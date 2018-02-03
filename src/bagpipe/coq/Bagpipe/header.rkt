#lang racket

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction-racket.rkt")
(require (except-in "network/network.rkt" current original path))
(require "config.rkt")
(require "bgpv-core.rkt")
(require "setup.rkt")

(require racket/place)
(require racket/place/distributed)
(require racket/serialize)

(provide bgpv bgpv-place incBgpvAll)

(define place-batch-size 8)
(define symbolic-batch-size 1)
(define parallel-batch-size 65536)

(define (coq-list-length l)
  (match l
    ((Nil) 0)
    ((Cons _ l*) (add1 (coq-list-length l*)))))

(define (coq-list-split-at n l)
  (if (rosette-eq? n 0)
    (cons '(Nil) l)
    (match l
      ((Nil) (cons '(Nil) l))
      ((Cons h l*) (begin
        (define split (coq-list-split-at (sub1 n) l*))
        (define lhs (car split))
        (define rhs (cdr split))
        (cons `(Cons ,h ,lhs) rhs))))))

(define (coq-list-chunks n l)
  (match l
    ((Nil) '(Nil))
    ((Cons _ __) (begin
     (define split (coq-list-split-at n l))      
     (define lhs (car split))
     (define rhs (cdr split))
     `(Cons ,lhs ,(coq-list-chunks n rhs))))))

(define (times count f) (for ([i (in-range count)]) (f)))

(define (forever f) (f) (forever f))

(define (coq-list->symbolic l)
  (match l ((Cons h l*)
  (match l* 
    ((Nil) h)
    ((Cons _ __)
      (@ symbolic-boolean (lambda (_) h) (lambda (_) (coq-list->symbolic l*)) void))))))

(define (bgpv-place ch)
  (define cpu (deserialize (place-channel-get ch)))
  (define node (deserialize (place-channel-get ch)))
  (write-string (string-append "# place started at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output)
  (define setup (deserialize (place-channel-get ch)))
  (define query (deserialize (place-channel-get ch)))
  (write-string (string-append "# place loaded setup at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output)
  (times place-batch-size (lambda ()
    (define routings (deserialize (place-channel-get ch)))
    (define res (@ bgpvCore~ setup query (coq-list->symbolic routings)))
    (place-channel-put ch (serialize (@ optionToSpace listSpace (@ listHead res))))))
  (write-string (string-append "# place done at " (~a node) " on cpu " (~a cpu) "\n"))
  (flush-output))

(define (cpus)
  (match-let ([(list out in pid err ctrl) (process "nproc")])
    (ctrl 'wait)
    (define res (read-line out))
    (close-output-port in)
    (close-input-port out)
    (close-input-port err)
    (stream->list (in-range (string->number res)))))

(define (nodes)
  (define evars (environment-variables-names (current-environment-variables)))
  (append* (list "localhost") (for/list ([evar evars])
    (define r (regexp-match #rx"^([^_]+)_NAME$" evar))
    (if r (list (string-downcase (bytes->string/utf-8 (second r)))) '()))))

(define distributed-bgpv-scheduler (lambdas (setup query routings)
  (define checks (coq-list-length routings))
  (write-string (string-append "total number of checks " (~a checks) "\n"))
  (flush-output)

  (define work-queue (make-channel))
  (define thd (current-thread))

  (define nodes* (nodes))
  (define cpus* (cpus))
  (write-string (string-append "nodes: " (~a nodes*) "\n"))
  (write-string (string-append "cpus: " (~a cpus*) "\n"))
  (flush-output)

  (define serializedSetup (serialize setup))
  (define serializedQuery (serialize query))
  
  ; start threads/nodes
  (for*/list ([node nodes*] [cpu cpus*])
    (thread (lambda ()
      (write-string (string-append "# node at " (~a node) " on cpu " (~a cpu) "\n"))
      (flush-output)
      (define nd (create-place-node node #:listen-port (+ 1234 cpu)))
      (forever (lambda ()
        (define ch (dynamic-place #:at nd (quote-module-path) 'bgpv-place))
        (place-channel-put ch (serialize cpu))
        (place-channel-put ch (serialize node))
        (place-channel-put ch serializedSetup)
        (place-channel-put ch serializedQuery)
        (times place-batch-size (lambda ()
          (define routings (channel-get work-queue))
          (place-channel-put ch (serialize routings))
          (define res (deserialize (place-channel-get ch)))
          (thread-send thd res))))))))

  ; provide work for threads
  (define count 0)
  (@ bind listSpace 
    (coq-list-chunks parallel-batch-size routings) (lambda (sub-routings)
      (define jobs (@ bind listSpace 
        (coq-list-chunks symbolic-batch-size sub-routings) (lambda (sub-sub-routings)
          (set! count (+ count symbolic-batch-size))
          (write-string (string-append "checking " (~a count) " of " (~a checks) " at " (~a (current-seconds)) "\n"))
          (flush-output)
          (channel-put work-queue sub-sub-routings)
          (@ single listSpace count))))

      (write-string (string-append "collecting " (~a (coq-list-length jobs)) " results\n"))
      (flush-output)

      ; collect results
      (@ bind listSpace jobs (lambda (_) (thread-receive)))))))

