#lang racket

(require "../util/util.rkt")
(require "../network/network.rkt")
(require "environment.rkt")
(require "parser.rkt")
(require "translate.rkt")
(require "denote.rkt")
(require "config.rkt")

(provide compare-import-policies compare-export-policies)

; for the "translation phase" of incrementalization; does not use rosette-eq
; because we'd prefer to avoid any searching while subtracting spaces

; compare as-routers-lookup and router-neighbors-lookup in config.rkt
(define (as-find-routers as ip) (findf [lambda (r) (equal? ip (router-ip r))] (as-routers as)))
(define (router-find-neighbors r ip) (findf [lambda (n) (equal? ip (neighbor-ip n))] (router-neighbors r)))

; just checking for direct equality (based on as-denote-import and as-denote-export in juniper.rkt)

(define (compare-import-policies as1 r1 i1 as2 r2 i2)
  (define r1* (as-find-routers as1 r1))
  (define r2* (as-find-routers as2 r2))
  (define policies1 (neighbor-import (router-find-neighbors r1* i1)))
  (define policies2 (neighbor-import (router-find-neighbors r2* i2)))
  (equal? policies1 policies2))

(define (compare-export-policies as1 r1 o1 as2 r2 o2)
  (define r1* (as-find-routers as1 r1))
  (define r2* (as-find-routers as2 r2))
  (define policies1 (neighbor-export (router-find-neighbors r1* o1)))
  (define policies2 (neighbor-export (router-find-neighbors r2* o2)))
  (equal? policies1 policies2))
