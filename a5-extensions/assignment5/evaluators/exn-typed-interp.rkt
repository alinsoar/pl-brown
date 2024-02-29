#lang plai-typed

(require "../parseltongue-lang/typed-lang.rkt"
         "helpers.rkt")

(define (extend-env sym loc old-env)
  (cons (bind sym loc) old-env))
(define (override-store loc value old-store)
  (cons (cell loc value) old-store))

;; raise-user-error raises errors that don't have any prefix on them
(require (typed-in racket/base (raise-user-error : (string -> ValueC))))

(define get-new-location
  (let ([loc 1000])
    (lambda ()
      (let ((k loc))
        (begin
          (set! loc (add1 loc))
          k)))))
(define get-n-locations
  (lambda (n)
    (if (= n 0)
        empty
        (cons (get-new-location)
              (get-n-locations (sub1 n))))))

(define (exception-handler e)
  : AnswerC
  (begin
    (d "EXCEPTION-HANDLER: ***" e)
    (VA (StrV "stop") empty empty)))

(define (fetch [loc : Location] [sto : Store] )
  (cond
   [(empty? sto)
    ;;  ``unknown-location`` error will never happen, as the store is
    ;;  updated for each operation, and never loses non-garbaged locations
    (error 'fetch "point never reached")]
   [(= loc (cell-location (first sto)))
    (cell-value (first sto))]
   [else
    (fetch loc (rest sto))]))

(define (lookup [for : symbol]
                [env : Env]
                [sto : Store]
                k
                exn)
  (cond
   [(empty? env)
    (exn (ExceptionA
          (ObjectV
           (list
            (fieldV "message"
                    (StrV "unknown location"))
            (fieldV "type" (StrV "PSL"))))
          sto
          env))]
   [(symbol=? for (bind-name (first env)))
    (k (bind-value (first env)))]
   [else (lookup for (rest env) sto k exn)]))

(define (check-equality v1 v2)
  (type-case ValueC v1
    [NumV (n1)
          (type-case ValueC v2
            [NumV (n2)
                  (if (= n1 n2)
                      (TrueV)
                      (FalseV))]
            [else (FalseV)])]
    [StrV (s1)
          (type-case ValueC v2
            [StrV (s2)
                  (if (string=? s1 s2)
                      (TrueV)
                      (FalseV))]
            [else (FalseV)])]
    [TrueV ()
           (type-case ValueC v2
             [TrueV () (TrueV)]
             [else (FalseV)])]
    [FalseV ()
            (type-case ValueC v2
              [FalseV () (TrueV)]
              [else (FalseV)])]
    [else (error 'a "TO COMPLETE")]))

(define (interp-app-arglist [syms          : (listof symbol)]
                            [new-locations : (listof Location)]
                            [args          : (listof ExprC)]
                            [answer        : AnswerC]
                            upper-env
                            exn
                            co)
  ;; evaluate the list of arguments used by function application.
  ;; 
  ;; will build a new environment extending env-closure, binding the
  ;; parameters to new memory locations, and also update the store.
  (ANSWER-CASE
   answer (val sto env)
   (if (empty? args)
       (co answer)
       (interp-env
        (first args)
        upper-env
        sto
        (lambda (q)
          (ANSWER-CASE
           q (v s e)
           (interp-app-arglist
            (rest syms)
            (rest new-locations)
            (rest args)
            (ValueA
             (UndefinedV)
             (override-store (first new-locations) v s)
             (extend-env (first syms)
                         (first new-locations)
                         env))
            upper-env
            exn
            co)
           [else (error 'r "r")]))
        exn
        "APP/ARGS"))
   [else (error 's "s")]))

(define-syntax (VA s)
  (syntax-case s ()
    [(VA v s e)
     #'(ValueA v s e)]))
(define-syntax (ANSWER-CASE s)
  (syntax-case s ()
    [(_ expr (v s e) body1
        body2)
     #'(type-case AnswerC expr
         [ValueA (v s e)
                 body1]
         body2)]))
(define-syntax (DEBUG-INTERP s)
  (syntax-case s ()
    [(_ 0)
     (with-syntax ([exprC  (datum->syntax s 'exprC)]
                   [env    (datum->syntax s 'env)]
                   [store  (datum->syntax s 'store)]
                   [d-code (datum->syntax s 'debug-code)])
       #'(begin
           (d "==========INTERP-ENV"
              (string-append "***"
                             (string-append d-code
                                            "***")))       
           (d "  ~~~" exprC)
           (d "  ~~~" env)
           (d "  ~~~" store)))]
    [(_ F) #''ignore]
    [(_ ...)
     (with-syntax ([exprC  (datum->syntax s 'exprC)]
                   [env    (datum->syntax s 'env)]
                   [store  (datum->syntax s 'store)]
                   [d-code (datum->syntax s 'debug-code)])
       #'(d "==========INTERP-ENV"
            (string-append "***"
                           (string-append d-code
                                          "***"))))]))

(define (interp (exprC : ExprC))
  : ValueC
  (begin
    (d "INTERP:  ***" exprC)
    (d "@" "---------------------------------------- START COMPUTATION")
    (let ((result (interp-env exprC
                              empty
                              empty
                              (lambda (x) x)
                              exception-handler
                              "MAIN")))
      (begin
        (d "@" "---------------------------------------- END COMPUTATION")
        '(d "=======>: ***" result)
        (type-case AnswerC result
          [ExceptionA (exn-val store env)
                      (raise-user-error "1:No interpreter here yet")]
          [ValueA (val store e2)
                  val
                  ;; (raise-user-error "2:No interpreter here yet")
                  ])))))
(define (interp-env [exprC : ExprC]
                    [env : Env]
                    [store : Store]
                    k
                    exn
                    [debug-code : string])
  : AnswerC
  (begin
    (DEBUG-INTERP F)
    (type-case ExprC exprC
      [NumC (n)
            (k (VA (NumV n) store env))]
      [TrueC ()
             (k (VA (TrueV) store env))]
      [UndefinedC ()
                  (k (VA (UndefinedV) store env))]
      [FalseC ()
              (k (VA (FalseV) store env))]
      [StrC (s)
            (k (VA (StrV s) store env))]
      [IdC (sym)
           (lookup sym
                   env
                   store
                   (lambda (loc)
                     (let ((value (fetch loc store )))
                       (k (VA value store env))))
                   exn)]
      [LetC (id bind-val body)
            (interp-env
             bind-val
             env
             store
             (lambda (e)
               (ANSWER-CASE
                e (val0 sto0 env0)
                (let ((loc (get-new-location)))
                  (interp-env
                   body
                   (extend-env id loc env0)
                   (override-store loc val0 sto0)
                   k
                   exn
                   "LET/BODY"))
                [else (error 'interp "TODO")]))
             exn
             "LET/VAL")]
      [Prim1C (op arg)
              (case op
                ['print
                 (interp-env
                  arg
                  env
                  store
                  (lambda (m)
                    (ANSWER-CASE
                     m (v _ __)
                     (begin
                       (display (pretty-value v))
                       m)
                     [else (error 'ww "ee")]))
                  exn
                  "PRINT")]
                ['tagof
                 (interp-env
                  arg
                  env
                  store
                  (lambda (aval)
                    (ANSWER-CASE
                     aval (v s e)
                     (let ((t (type-case ValueC v
                                [UndefinedV ()       "undefined"]
                                [ObjectV (_)         "object"]
                                [ClosureV (_ __ ___) "function"]
                                [NumV (_)            "number"]
                                [StrV (_)            "string"]
                                [TrueV ()            "boolean"]
                                [FalseV ()           "boolean"])))
                       (k (VA (StrV t) s e)))
                     [else [error 'a1 "b1"]]))
                  exn
                  "TAGOF")])]
      [Prim2C (op arg1 arg2)
              (case op
                ['==
                 (interp-env
                  arg1
                  env
                  store
                  (lambda (val1)
                    (ANSWER-CASE
                     val1 (v1 s1 e1)
                     (interp-env
                      arg2 e1 s1
                      (lambda (val2)
                        (ANSWER-CASE
                         val2 (v2 s2 e2)
                         (k (VA (check-equality v1 v2)
                                s2 e2))
                         [else (error 'b "b")]))
                      exn
                      "==/2")
                     [else (error 'a "a")]))
                  exn
                  "==/1")]
                ['num+
                 (interp-env
                  arg1
                  env
                  store
                  (lambda (val1)
                    (ANSWER-CASE
                     val1 (v1 sto1 _)
                     (type-case ValueC v1
                       [NumV (n1)
                             (interp-env
                              arg2
                              env
                              sto1
                              (lambda (val2)
                                (ANSWER-CASE
                                 val2 (v2 sto2 _)
                                 (type-case ValueC v2
                                   [NumV (n2)
                                         (k (VA
                                             (NumV (+ n1 n2))
                                             sto2 env))]
                                   [else
                                    (exn
                                     (ExceptionA
                                      (ObjectV
                                       (list
                                        (fieldV "message"
                                                (StrV "Bad args to +"))
                                        (fieldV "type" (StrV "PSL"))))
                                      sto2
                                      env))])
                                 [else (error 'a "a")]))
                              exn
                              "+/2")]
                       [else (error '+ "e")])
                     [else (error 'a "a")]))
                  exn
                  "+/1")])]
      [IfC (c then-branch else-branch)
           (interp-env
            c
            env
            store
            (lambda (vc)
              (ANSWER-CASE
               vc (v s1 e1)
               (type-case ValueC v
                 [TrueV ()
                        (interp-env
                         then-branch
                         env
                         store
                         k
                         exn
                         "IF-THEN-ELSE/THEN")]
                 [else (interp-env
                        else-branch
                        env
                        store
                        k
                        exn
                        "IF-THEN-ELSE/ELSE")])
               [else (error 'interp "TODO2")]))
            exn
            "IF-THEN-ELSE/COND")]
      [TryCatchC (body param catch)
                 (interp-env
                  body
                  env
                  store
                  k
                  (lambda (e)
                    (let ([loc (get-new-location)])
                      (ANSWER-CASE
                       e (val sto e2)
                       (interp-env catch
                                   (extend-env param loc e2)
                                   (override-store loc val sto)
                                   k
                                   exn
                                   "CATCH")
                       [else [error 'a "b"]])))
                  "TRY-CATCH")]
      [ErrorC (e)
              (interp-env
               e
               env
               store
               exn
               exn
               "ERROR")]
      [SeqC (e1 e2)
            (interp-env
             e1
             env
             store
             (lambda (val1)
               (ANSWER-CASE
                val1 (v1 sto1 env1)
                (interp-env
                 e2
                 env1
                 sto1
                 k
                 exn
                 "SEQ/2")
                [else (error 'a "a")]))
             exn
             "SEQ/1")]
      [Set!C (id val)
             (interp-env
              val
              env
              store
              (lambda (v0)
                (ANSWER-CASE
                 v0 (v s e)
                 (lookup id
                         e
                         s
                         (lambda (where)
                           (k (VA
                               (StrV "ok") ; v
                               (override-store where v s)
                               env)))
                         exn)
                 [else (error 'a "p")]))
              exn
              "SET!/VAL")]
      [FuncC (args body)
             (k (VA (ClosureV args body env)
                    store env))]
      [AppC (func args)
            (interp-env
             func
             env
             store
             (lambda (fv)
               (ANSWER-CASE
                fv (fun0 s0 _)
                (type-case ValueC fun0
                  [ClosureV (params body env-clos)
                            (interp-app-arglist
                             params
                             (get-n-locations (length params))
                             args
                             (VA (UndefinedV) s0 env-clos)
                             env
                             exn
                             (lambda (arg-values)
                               (interp-env
                                body
                                (ValueA-env arg-values)
                                (ValueA-store arg-values)
                                (lambda (o)
                                  (ANSWER-CASE
                                   o (v1 s1 _)
                                   (k (VA v1 s1 env))
                                   [else (error 'q "e")]))
                                exn
                                "APP/CLOSURE")))]
                  [else (error 'app "not a fun")])
                [else (error 'app "?")]))
             exn
             "APP/F")]
      [else
       (error 'interp "0:No interpreter here yet either")])))


