#lang plai-typed

(require "../parseltongue-lang/typed-lang.rkt"
         "exn-typed-desugar.rkt"
         "exn-typed-interp.rkt"
         "helpers.rkt")

(define (evaluate [exprP : ExprP]) : ValueC
  (begin
    (d "EVALUATE: ***" exprP)
    (interp (desugar exprP))))

(define pretty-printer pretty-value)



