#lang racket

(require "../network/network.rkt")
(require "environment.rkt")
(require "parser.rkt")
(require "compare.rkt")
(require "translate.rkt")
(require "denote.rkt")
(require "config.rkt")

(provide as-from-configs as-denote-import as-denote-export
         as-internal-routers as-router-external-neighbors as-environment
	 as-compare-policies)

; represents ases as AS defined in config.rkt
; represents routers as ip addresses

(define (as-from-configs configs)
  (load-as configs))

(define (as-denote-import as r i a)
  (define r* (as-routers-lookup as r))
  (define policies (neighbor-import (router-neighbors-lookup r* i)))
  (denote-policies policies a))

(define (as-denote-export as r o a)
  (define r* (as-routers-lookup as r))
  (define policies (neighbor-export (router-neighbors-lookup r* o)))
  (denote-policies policies a))

(define (as-environment as)
  (as->environment as))

(define (as-internal-routers as)
  (map router-ip (as-routers as)))

(define (as-router-external-neighbors as r)
  (define r* (as-routers-lookup as r))
  (define res (map neighbor-ip (filter neighbor-external? (router-neighbors r*))))
  res)

(define (as-compare-policies as1 r1 n1 as2 r2 n2) (compare-policies as1 r1 n2 as2 r2 n2))