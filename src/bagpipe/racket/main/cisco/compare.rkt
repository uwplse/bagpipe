#lang racket

(require "../util/util.rkt")
(require "../network/network.rkt")

(require "denote.rkt")

(provide compare-import-policies compare-export-policies)

; based on denote.rkt but non-rosette for the purposes of being easily run
; during the "translation phase" of incrementalization

; rosette is baked into the dict lookups so we must define versions that
; use ordinary equality
; (contrast with dict-lookup, record-data, record-field in denote.rkt)

; the layout of a dict is `((key value) (key* value*) ...)
(define (dict-lookup* key dict)
  (second (findf [lambda (entry) (equal? key (first entry))] dict)))

; the layout of a record is `(name data)
(define (record-data* name record)
  (if (equal? (first record) name)
    (second record)
    #f))

(define (record-field* name field record)
  (dict-lookup* field (record-data* name record)))

; see as-lookup-router and as-lookup-neighbor in denote.rkt

(define (as-find-router as ip)
  (findf [lambda (r)
     (equal? ip (to-ipv4 (record-field* 'Router '_routerIP r)))
  ] (record-field* 'Config 'routers as)))

(define (as-find-neighbor r ip)
  (findf [lambda (n)
    (equal? ip (to-ipv4 (record-field* 'Neighbor 'neighborIP n)))
  ] (record-field* 'Router '_neighbors r)))

; see denote-policy
(define (find-policy-stmts kind as r n)
  (define r* (as-find-router as r))
  (define n* (as-find-neighbor r* n))
  (define policy (record-field* 'Neighbor kind n*))
  (record-data* 'Inlined policy))

; checks if two routers in different ASes have exactly the
; same configuration (for incrementalization)
(define (compare-import-policies as1 r1 i1 as2 r2 i2)
  (define import1 (find-policy-stmts '_importPolicy as1 r1 i1))
  (define import2 (find-policy-stmts '_importPolicy as2 r2 i2))
  (equal? import1 import2))

(define (compare-export-policies as1 r1 o1 as2 r2 o2)
  (define export1 (find-policy-stmts '_exportPolicy as1 r1 o1))
  (define export2 (find-policy-stmts '_exportPolicy as2 r2 o2))
  (equal? export1 export2))
