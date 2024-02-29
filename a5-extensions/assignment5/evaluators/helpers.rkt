#lang plai-typed

(require "../parseltongue-lang/typed-lang.rkt")

(define (d msg a)
  (begin
    (display msg)
    (display ":")
    (display a)
    (display "\n")))

(define id (lambda (_) _))

