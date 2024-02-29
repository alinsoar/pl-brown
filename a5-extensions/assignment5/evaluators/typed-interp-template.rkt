#lang plai-typed

(require "typed-lang2.rkt")

(define (debug m a): void
  (begin
    (display m)
    (display "==> ")
    (map (lambda (x)
           (begin (display x)
                  (display " ")))
         a)
    (display "\n")))

(define-type Cell [cell (location : Location) (value : ValueC)])
(define-type-alias Store (listof Cell))

(define-type Result [v*s (value : ValueC) (store : Store)])
(define-type FV-helper [fv (value : (listof FieldV)) (store : Store)])
(define-type ArgV-helper [av (value : (listof ValueC)) (store : Store)])

(define new-loc
  (let ([loc 1000])
    (lambda ()
      (begin (set! loc (add1 loc))
             loc))))
(define (interp-app-arguments args env store interp-args)
  (if (empty? args)
      (av interp-args store)
      (type-case Result (interp-full (first args) env store)
        [v*s (v-a s-a)
             (interp-app-arguments
              (rest args) env s-a
              (append interp-args (list v-a)))])))

(define (make-new-env args locs new-env)
  (if (empty? args)
      new-env
      (make-new-env (rest args) (rest locs)
                    (cons (bind (first args) (first locs))
                          new-env))))

(define (check-uniq-field fieldname fields): boolean
  (cond [(empty? fields)
         true]
        [(string=? fieldname (fieldC-name (first fields)))
         false]
        [else (check-uniq-field fieldname (rest fields))]))
(define (check-object-fields fields)
  (if (empty? fields)
      true
      (and
       (check-uniq-field (fieldC-name (first fields))
                         (rest fields))
       (check-object-fields (rest fields)))))
(define (interp-obj-fields env store fields interp-fields-value)
  (if (empty? fields)
      (fv interp-fields-value store)
      (let ((f (first fields)))
        (type-case Result (interp-full (fieldC-value f) env store)
          (v*s (v-f s-f)
               (interp-obj-fields
                env
                s-f
                (rest fields)
                (cons (fieldV (fieldC-name f) v-f)
                      interp-fields-value)))))))
(define (lookup-field (fields : (listof FieldV)) (f : string))
  (if (empty? fields)
      (interp-error (string-append "Field not found: " f))
      (type-case FieldV (first fields)
        [fieldV (name val)
                (if (string=? name f)
                    val
                    (lookup-field (rest fields) f))])))
(define (duplicate-fields (fields : (listof FieldV))
                          (fieldname : string)
                          (new-value : ValueC))
  (cond [(and (empty? fields) (string=? fieldname ""))
         empty]
        [(empty? fields)
         (list (fieldV fieldname new-value))]
        [else
         (type-case FieldV (first fields)
           [fieldV (name val)
                   (if (string=? name fieldname)
                       (cons (fieldV name new-value)
                             (duplicate-fields (rest fields) "" (FalseV)))
                       (cons (first fields)
                             (duplicate-fields (rest fields) fieldname new-value)))])]))

(define override-store cons)
(define extend-env cons)

(define (reduce combine init elems)
  (if (empty? elems)
      init
      (combine (first elems)
               (reduce combine
                       init
                       (rest elems)))))

(define (zipY s b)
  (if (and (empty? s) (empty? b))
      empty
      (cons (cell (first s) (first b))
            (zipY (rest s) (rest b)))))

(define (make-error err-msg v1 v2)
  (interp-error
   (string-append
    err-msg
    (string-append
     (pretty-value v1)
     (string-append
      "\n"
      (pretty-value v2))))))

(define (check-identical-exprC (e1 : ExprC) (e2 : ExprC))
  ;; todo
  true)

(define (check-identical-env env1 env2 store)
  (cond [(empty? env1)
         true]
        [else
         (type-case Binding (first env1)
           (bind (name value)
                 (and
                  ;; either the name is bound to the same memory location,
                  ;; or the value of the symbols are Equal.
                  (or (= (lookup name env1) (lookup name env2))
                      (type-case ValueC (check-equality (fetch (lookup name env1) store)
                                                        (fetch (lookup name env2) store)
                                                        store)
                        [TrueV () true]
                        [else false]))
                  (check-identical-env (rest env1) env2 store))))]))

(define (check-identical-arguments (args1 : (listof symbol))
                                   (args2 : (listof symbol))) : boolean
  (cond [(and (empty? args1) (empty? args2))
         true]
        [(or (empty? args1) (empty? args2))
         false]
        [else (and (eq? (first args1) (first args2))
                   (check-identical-arguments (rest args1) (rest args2)))]))
(define (check-identical-objects (fields1 : (listof FieldV))
                                 (fields2 : (listof FieldV))
                                 store)
  (cond [(and (empty? fields1) (empty? fields2))
         true]
        [(or (empty? fields1) (empty? fields2))
         false]
        [else
         (type-case FieldV (first fields1)
           (fieldV (name1 value1)
                   (type-case FieldV (first fields2)
                     (fieldV (name2 value2)
                             (and (string=? name1 name2)
                                  (type-case ValueC (check-equality value1 value2 store)
                                    [TrueV () true]
                                    [else false])
                                  (check-identical-objects
                                   (rest fields1)
                                   (rest fields2)
                                   store))))))]))
(define (check-equality v-arg1 v-arg2 store) : ValueC
  (type-case ValueC v-arg1
    [NumV (n1)
          (type-case ValueC v-arg2
            [NumV (n2)
                  (if (= n1 n2)
                      (TrueV)
                      (FalseV))]
            [else (FalseV)])]
    [StrV (s1)
          (type-case ValueC v-arg2
            [StrV (s2)
                  (if (string=? s1 s2)
                      (TrueV)
                      (FalseV))]
            [else (FalseV)])]
    [TrueV ()
           (type-case ValueC v-arg2
             [TrueV () (TrueV)]
             [else (FalseV)])]
    [FalseV ()
            (type-case ValueC v-arg2
              [FalseV () (TrueV)]
              [else (FalseV)])]
    [ObjectV (fields1)
             (type-case ValueC v-arg2
               [ObjectV (fields2)
                        (if (check-identical-objects fields1 fields2 store)
                            (TrueV)
                            (FalseV))]
               [else (FalseV)])]
    [ClosureV (args1 body1 env1)
              (type-case ValueC v-arg2
                [ClosureV (args2 body2 env2)
                          (if (and (check-identical-arguments args1 args2)
                                   (check-identical-exprC body1 body2)
                                   (check-identical-env env1 env2 store))
                              (TrueV)
                              (FalseV))]
                [else (FalseV)])]))

(define (interp [exprC : ExprC]) : ValueC
  (type-case Result (interp-full exprC empty empty)
    [v*s (value store) value]))
(define (lookup [for : symbol] [env : Env]): Location
  (cond [(empty? env) (error 'Unbound\ identifier (symbol->string for))]
        [(symbol=? for (bind-name (first env)))
         (bind-value (first env))]
        [else (lookup for (rest env))]))
(define (fetch [loc : Location] [sto : Store]): ValueC
  (cond [(empty? sto) (error (s-exp->symbol (number->s-exp loc))
                             "location not found")]
        [(= loc (cell-location (first sto)))
         (cell-value (first sto))]
        [else (fetch loc (rest sto))]))
(define (interp-full [exprC : ExprC] [env : Env] [store : Store]) : Result
  (type-case ExprC exprC
    [NumC (n) (v*s (NumV n) store)]
    [StrC (s) (v*s (StrV s) store)]
    [TrueC () (v*s (TrueV) store)]
    [FalseC () (v*s (FalseV) store)]
    [SeqC (b1 b2) (type-case Result (interp-full b1 env store)
                    [v*s (v-b1 s-b1)
                         (interp-full b2 env s-b1)])]
    [IfC (c t e) (type-case Result (interp-full c env store)
                   [v*s (v-c s-c)
                        (type-case ValueC v-c
                          [FalseV () (interp-full e env s-c)]
                          [else (interp-full t env s-c)])])]
    [Prim1C (op arg)
            (case op
              ['print (type-case Result (interp-full arg env store)
                        [v*s (v-val s-val)
                             (begin (display (pretty-value v-val))
                                    (v*s v-val s-val))])]
              ['tagof (type-case Result (interp-full arg env store)
                        [v*s (v-val s-val)
                             (v*s (StrV (type-case ValueC v-val
                                          [ObjectV (_) "object"]
                                          [ClosureV (_ __ ___) "function"]
                                          [NumV (_) "number"]
                                          [StrV (_) "string"]
                                          [TrueV () "boolean"]
                                          [FalseV () "boolean"]))
                                  s-val)])])]
    [Prim2C (op arg1 arg2)
            (case op
              ['string+ (type-case Result (interp-full arg1 env store)
                          [v*s (v-arg1 s-arg1)
                               (type-case ValueC v-arg1
                                 [StrV (s1)
                                       (type-case Result (interp-full arg2 env s-arg1)
                                         [v*s (v-arg2 s-arg2)
                                              (type-case ValueC v-arg2
                                                [StrV (s2)
                                                      (v*s (StrV (string-append s1 s2))
                                                           s-arg2)]
                                                [else (interp-error "bad str+")])])]
                                 [else (interp-error "bad str+")])])]
              ['num+ (type-case Result (interp-full arg1 env store)
                       [v*s (v-arg1 s-arg1)
                            (type-case ValueC v-arg1
                              [NumV (n1)
                                    (type-case Result (interp-full arg2 env s-arg1)
                                      [v*s (v-arg2 s-arg2)
                                           (type-case ValueC v-arg2
                                             [NumV (n2)
                                                   (v*s (NumV (+ n1 n2))
                                                        s-arg2)]
                                             [else (make-error "Bad arguments for +:\n"
                                                               v-arg1
                                                               v-arg2)])])]
                              [else (make-error "Bad arguments for +:\n"
                                                v-arg1
                                                (v*s-value
                                                 (interp-full arg2 env s-arg1)))])])]
              ['num- (type-case Result (interp-full arg1 env store)
                       [v*s (v-arg1 s-arg1)
                            (type-case ValueC v-arg1
                              [NumV (n1)
                                    (type-case Result (interp-full arg2 env s-arg1)
                                      [v*s (v-arg2 s-arg2)
                                           (type-case ValueC v-arg2
                                             [NumV (n2)
                                                   (v*s (NumV (- n1 n2))
                                                        s-arg2)]
                                             [else (make-error
                                                    "Bad arguments for -:\n"
                                                    v-arg1
                                                    v-arg2)])])]
                              [else (make-error "Bad arguments for -:\n"
                                                v-arg1
                                                (v*s-value
                                                 (interp-full arg2 env s-arg1)))])])]
              ['< (type-case Result (interp-full arg1 env store)
                    [v*s (v-arg1 s-arg1)
                         (type-case ValueC v-arg1
                           [NumV (n1)
                                 (type-case Result (interp-full arg2 env s-arg1)
                                   [v*s (v-arg2 s-arg2)
                                        (type-case ValueC v-arg2
                                          [NumV (n2)
                                                (v*s (if (< n1 n2) (TrueV) (FalseV))
                                                     s-arg2)]
                                          [else (make-error "Bad arguments for <:\n"
                                                            v-arg1
                                                            v-arg2)])])]
                           [else (interp-error (make-error
                                                "Bad arguments for <:\n"
                                                v-arg1
                                                (v*s-value
                                                 (interp-full arg2 env s-arg1))))])])]
              ['> (type-case Result (interp-full arg1 env store)
                    [v*s (v-arg1 s-arg1)
                         (type-case ValueC v-arg1
                           [NumV (n1)
                                 (type-case Result (interp-full arg2 env s-arg1)
                                   [v*s (v-arg2 s-arg2)
                                        (type-case ValueC v-arg2
                                          [NumV (n2)
                                                (v*s (if (> n1 n2) (TrueV) (FalseV))
                                                     s-arg2)]
                                          [else (make-error
                                                 "Bad arguments for >:\n"
                                                 v-arg1 v-arg2)])])]
                           [else (make-error
                                  "Bad arguments for >:\n"
                                  v-arg1
                                  (v*s-value
                                   (interp-full arg2 env s-arg1)))])])]
              ['==
               (type-case Result (interp-full arg1 env store)
                 [v*s (v-arg1 s-arg1)
                      (type-case Result (interp-full arg2 env s-arg1)
                        [v*s (v-arg2 s-arg2)
                             (v*s
                              (check-equality v-arg1 v-arg2 store)
                              s-arg2)])])])]
    [IdC (sym) (v*s (fetch (lookup sym env) store) store)]
    [FuncC (args body) (v*s (ClosureV args body env) store)]
    [AppC (func args)
          (type-case Result (interp-full func env store)
            [v*s (v-func s-func)
                 (type-case ValueC v-func
                   [ClosureV (X-args X-body X-env)
                             (let ((args-interp (interp-app-arguments args env s-func empty)))
                               (if (= (length args) (length X-args))
                                   (let ((new-locations (map (lambda (_) (new-loc)) args)))
                                     (let ((new-env
                                            (make-new-env X-args new-locations X-env))
                                           (new-store
                                            (reduce override-store
                                                    (av-store args-interp)
                                                    (zipY new-locations
                                                          (av-value args-interp)))))
                                       (interp-full X-body new-env new-store)))
                                   (interp-error "Application failed with arity mismatch")))]
                   [else (interp-error
                          (string-append "Applied a non-function: "
                                         (pretty-value v-func)))])])]
    [LetC (id bind-val body)
          (let ([where (new-loc)])
            (type-case Result (interp-full bind-val env store)
              [v*s (v-bind s-bind)
                   (interp-full body
                                (extend-env (bind id where) env)
                                (override-store (cell where v-bind)
                                                s-bind))]))]
    [Set!C (id val) (type-case Result (interp-full val env store)
                      [v*s (v-val s-val)
                           (let ([where (lookup id env)])
                             (v*s v-val
                                  (override-store (cell where v-val)
                                                  s-val)))])]
    [ErrorC (e) (type-case Result (interp-full e env store)
                  [v*s (v-val s-val)
                       (type-case ValueC v-val
                         [StrV (s) (interp-error s)]
                         [else (interp-error "unknown")])])]
    [ObjectC (fields)
             (if (check-object-fields fields)
                 (let ((fds (interp-obj-fields env store fields empty)))
                   (v*s (ObjectV (fv-value fds))
                        (fv-store fds)))
                 (interp-error "Multiply-defined fields"))]
    [GetFieldC (obj field)
               (type-case Result (interp-full obj env store)
                 (v*s (v-o s-o)
                      (type-case ValueC v-o
                        [ObjectV (o-fields)
                                 (type-case Result (interp-full field env s-o)
                                   (v*s (v-f s-f)
                                        (type-case ValueC v-f
                                          [StrV (fieldname)
                                                (v*s (lookup-field o-fields fieldname)
                                                     s-f)]
                                          [else (interp-error
                                                 (string-append
                                                  "Non-string in field lookup: "
                                                  (pretty-value v-f)))])))]
                        (else (interp-error (string-append "Non-object in field lookup: "
                                                           (pretty-value v-o)))))))]
    [SetFieldC (obj field new-value)
               ;; EVALUATE OBJECT
               (type-case Result
                 (interp-full obj env store)
                 (v*s (v-o s-o)
                      (type-case ValueC v-o
                        [ObjectV (o-fields)
                                 ;; EVALUATE FIELD
                                 (type-case Result
                                   (interp-full field env s-o)
                                   (v*s (v-f s-f)
                                        (type-case ValueC v-f
                                          [StrV (fieldname)
                                                ;; EVALUATE NEW-VALUE
                                                (type-case Result
                                                  (interp-full new-value env s-f)
                                                  [v*s (v-newvalue s-newvalue)
                                                       ;; MAKE NEW MODIFIED OBJECT
                                                       (v*s
                                                        (ObjectV
                                                         (duplicate-fields
                                                          o-fields
                                                          fieldname
                                                          v-newvalue))
                                                        s-newvalue)])]
                                          [else (interp-error
                                                 (string-append
                                                  "Non-string in field update: "
                                                  (pretty-value v-f)))])))]
                        (else (interp-error (string-append "Non-object in field update: "
                                                           (pretty-value v-o)))))))]))


