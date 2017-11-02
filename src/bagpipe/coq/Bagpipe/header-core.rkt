#lang s-exp rosette

(require racket/format)

(current-bitwidth 10)

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction-rosette.rkt")
(require (except-in "network/network.rkt" current original path))
(require "config.rkt")
(require "setup.rkt")

(provide bgpvCore~)
