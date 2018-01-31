#lang racket

(require "../util/util.rkt")
(require "../network/network.rkt")

(provide compare-policies)

; based on denote.rkt but non-rosette for the purposes of being easily run
; during the "translation phase" of incrementalization

; rosette is baked into the dict lookups so we must define versions that
; use ordinary equality
; (contrast with dict-lookup, record-data, record-field in denote.rkt)

; the layout of a dict is `((key value) (key* value*) ...)
(define (dict-lookup' key dict)
  (second (findf [lambda (entry) (equal? key (first entry))] dict)))

; the layout of a record is `(name data)
(define (record-data' name record)
  (if (equal? (first record) name)
    (second record)
    #f))

(define (record-field' name field record)
  (dict-lookup' field (record-data' name record)))

; see as-lookup-router and as-lookup-neighbor in denote.rkt

(define (as-find-router as ip)
  (findf [lambda (r)
     (equal? ip (to-ipv4 (record-field' 'Router '_routerIP r)))
  ] (record-field' 'Config 'routers as)))

(define (as-find-neighbor r ip)
  (findf [lambda (n)
    (equal? ip (to-ipv4 (record-field' 'Neighbor 'neighborIP n)))
  ] (record-field' 'Router '_neighbors r)))

; see denote-policy
(define (find-policy-stmts kind as r n)
  (define r* (as-find-router as r))
  (define n* (as-find-neighbor r* n))
  (define policy (record-field' 'Neighbor kind n*))
  (record-data' 'Inlined policy))

; checks if two routers in different ASes have exactly the
; same configuration (for incrementalization)
(define (compare-policies kind as1 r1 n1 as2 r2 n2)
  (define stmts1 (find-policy-stmts kind as1 r1 n1))
  (define stmts2 (find-policy-stmts kind as2 r2 n2))
  (equal? stmts1 stmts2))
