#lang plai

;;; CFWAE (conditionals, functions, with, and arithmetic expressions)

(define-type Binding
  [binding (name symbol?) (named-expr CFWAE?)])

(define-type CFWAE
  [num (n number?)]
  [binop (op procedure?) (lhs CFWAE?) (rhs CFWAE?)]
  [with (lob (listof Binding?)) (body CFWAE?)]
  [id (name symbol?)]
  [if0 (c CFWAE?) (t CFWAE?) (e CFWAE?)]
  [fun (args (listof symbol?)) (body CFWAE?)]
  [app (f CFWAE?) (args (listof CFWAE?))])

(define-type Env
  [mtEnv]
  ;; we really don't need an enclosing environment in case of pure
  ;; substitution, but let us still keep it there.
  [anEnv (name symbol?) (value CFWAE-Value?) (env Env?)])

(define-type CFWAE-Value
  [numV (n number?)]
  [closureV (params (listof symbol?))
            (body CFWAE?)
            (env Env?)])

;;; ---------------------------------------- PARSER
(define (parse-number sexp)
  (and (number? sexp)
       (num sexp)))

(define (parse-identifier sexp)
  (and (symbol? sexp)
       (or (not (member sexp
                        '(+ - * / with if0 fun)))
           (error "invalid identifier"))
       (id sexp)))

(define (parse-binop op left right)
  (case op
    [(+) (binop + (parse left) (parse right))]
    [(-) (binop - (parse left) (parse right))]
    [(*) (binop * (parse left) (parse right))]
    [(/) (binop / (parse left) (parse right))]
    [else (error "non-supported operator")]))

(define (zip-vars-bindings vars bind)
    (cond [(or (empty? vars) (empty? bind))
           empty]
          [else
           (cons (binding (first vars) (first bind))
                 (zip-vars-bindings (rest vars) (rest bind)))]))

(define (parse-with lob body)
  "with ((a x) (b y)) will be interpreted as with (a x) with (b y)"
  
  (define (list-of-bindings lob)
    (let ((vars (map first lob))
          (bindings (map (lambda (b) (parse (second b)))
                         lob)))
      (and (parse-check-uniq-symbols vars)
           (zip-vars-bindings vars bindings))))
  (with (list-of-bindings lob) (parse body)))

(define (parse-check-uniq-symbols lop)
  (cond [(empty? lop) true]
        [(not (symbol? (first lop)))
         (error "fun/with parameters must be symbol")]
        [(member (first lop) (rest lop))
         (error "fun/with parameters must not be duplicated")]
        [else (parse-check-uniq-symbols (rest lop))]))

(define (parse-function args body)
  (and (parse-check-uniq-symbols args)
       (fun args (parse body))))

(define (parse-conditional cond then else)
  (if0 (parse cond) (parse then) (parse else)))

(define (parse-application fun args)
  (and (or (symbol? fun)
           (pair? fun)
           (error "function application is either a symbol or an application"))
       (app (parse fun) (map parse args))))

;;; parse : expression -> CFWAE
;;; This procedure parses an expression into a CFWAE
(define (parse sexp)
  ;; (debug "$$" sexp)
  (define (check-number-params params expected)
    (or (= (length params) expected)
        (error "bad number of arguments" params)))
  (cond [(empty? sexp) (error "a program block cannot be empty")]
        [(number? sexp) (parse-number sexp)]
        [(symbol? sexp) (parse-identifier sexp)]
        [(pair? sexp)
         (case (first sexp)
           [(+ - * /)
            (check-number-params (rest sexp) 2)
            (parse-binop (first sexp) (second sexp) (third sexp))]
           [(with)
            (check-number-params (rest sexp) 2)
            (parse-with (second sexp) (third sexp))]
           [(fun)
            (check-number-params (rest sexp) 2)
            (parse-function (second sexp) (third sexp))]
           [(if0)
            (check-number-params (rest sexp) 3)
            (parse-conditional (second sexp) (third sexp) (fourth sexp))]
           [else (parse-application (first sexp) (rest sexp))])]
        ))

;;; ---------------------------------------- INTERPRETER USING SUBSTITUTION
(define make-fresh-variable
  (let ((counter 1000))
    (lambda (sym)
      (set! counter (add1 counter))
      (string->symbol
       (string-append (symbol->string sym)
                      ":"
                      (number->string (sub1 counter)))))))

(define (substitution what for where)
  "replaces FOR => WHAT in expression WHERE"
  (type-case CFWAE where
             [num (n) where]
             [id (s) (if (eq? s for)
                         what
                         where)]
             [binop (op l r) (binop op
                                    (substitution what for l)
                                    (substitution what for r))]
             [if0 (c t e) (if0 (substitution what for c)
                               (substitution what for t)
                               (substitution what for e))]
             [app (f args) (app (substitution what for f)
                                (map (lambda (x) (substitution what for x))
                                     args))]
             [fun (args body)
                  (let ((fresh (make-new-arguments args body)))
                    (fun (car fresh)
                         (substitution what for (cdr fresh))))]
             [with (lob body)
                   (let ((params (map binding-name lob))
                         (args (map (lambda (x) (substitution what
                                                         for
                                                         (binding-named-expr x)))
                                    lob)))
                     (with
                      (zip-vars-bindings params args)
                      (substitution what for body)))]))

(define (make-new-arguments a body)
  (cond [(empty? a) (cons empty body)]
        [else (let ((new-var (make-fresh-variable (first a))))
                (let ((res (make-new-arguments
                            (rest a)
                            (substitution (id new-var) (first a) body))))
                  (cons (cons new-var (car res))
                        (cdr res))))]))

(define (interp-with lob body)
  (let ((params (map (lambda (x) (binding-name x)) lob))
        (args (map (lambda (x) (interp (binding-named-expr x))) lob)))
    (interp-apply (interp-function params body)
                  args)))

(define (interp-function args body)
  (let ((fresh-args (make-new-arguments args body)))
    (closureV (car fresh-args) (cdr fresh-args) (mtEnv))))

(define (interp-apply f args)
  (define (subst-params replacement-vals params body)
    (cond [(and (empty? replacement-vals) (empty? params))
           body]
          [(or (empty? replacement-vals) (empty? params))
           (error "arity mismatch" f args)]
          [else
           (let ((val (first replacement-vals)))
             (let ((rep (type-case CFWAE-Value val
                                   [numV (n) (num n)]
                                   [closureV (p b e) (fun p b)])))
               (subst-params (rest replacement-vals)
                             (rest params)
                             (substitution rep
                                          (first params)
                                          body))))]))
  (and (or (closureV? f)
           (error "only the functions can be applied"))
       (let ((params (closureV-params f))
             (body (closureV-body f)))
         (interp (subst-params args params body)))))

;;; interp : CFWAE -> CFWAE-Value
;;; This procedure evaluates a CFWAE expression, producing a CFWAE-Value.
(define (interp expr)
  ;; (debug "........" expr)
  (type-case CFWAE expr
             [num (n) (numV n)]
             [binop (op l r)
                    (let ((lv (interp l)) (rv (interp r)))
                      (or (and (numV? lv)
                               (numV? rv)
                               (let ((lv (numV-n lv))
                                     (rv (numV-n rv)))
                                 (and (eq? op /)
                                      (or (not (= rv 0))
                                          (error "division by 0")))
                                 (numV (op lv rv))))
                          (error "canot apply arith operator on non-numbers")))]
             [if0 (c t e) (let ((c (interp c)))
                    (type-case CFWAE-Value c
                               [numV (n) (if (= 0 (numV-n c))
                                             (interp t)
                                             (interp e))]
                               [closureV (_ __ ___) (interp e)]))]
             [id (i) (error "found free variable" expr)]
             [with (lob body) (interp-with lob body)]
             [fun (a b) (interp-function a b)]
             [app (f a) (interp-apply (interp f) (map interp a))]))

;;; ---------------------------------------- DEBUG
(define (debug m . s)
  (display m)
  (display " ")
  (map (lambda (x)
         (display x)
         (display " "))
       s)
  (newline))

;;; ---------------------------------------- TESTS

(test/exn
 (parse '(parse (("sym" 1)) 5))
 "function application is either a symbol or an application")

(make-fresh-variable 'x)
(make-fresh-variable 'x)
(make-fresh-variable 'y)
(make-fresh-variable 'x)

(interp
 (parse '{with {{x 2}
                {y 3}}
          {with {{z {+ x y}}}
           {+ x z}}}))

(test/exn
 (parse '{with {{x 2}
                {x 3}}
          {+ x 2}})
 "fun/with parameters must not be duplicated")

(interp
 (parse '{with {{x 1}} 5}))

(test/exn
 (interp (parse '(with ((x (/ 1 0))) 5)))
 "division by 0")

(interp (parse '(if0 (- 2 1) 1 2)))
(interp (parse '(if0 (- 1 1) 1 2)))

(interp
 (parse
  '(fun (x)
    (proc (fun (arg)
               ((x x) arg))))))

(interp
 (parse
  '((fun (f)
         (fun (x)
              (f 10)))
    (fun (y) (+ x y)))))

(interp
 (parse
  '((fun (s) (s s))
    (fun (f) f))))

(interp
 (parse
  '((fun (self n) (self self n))
    (fun (self n) (if0 n 0 (+ n (self self (- n 1)))))
    10)))

(interp
 (parse
  '(with ((x (/ 1 2)) (y 111)) 5)))

(interp
 (parse
  '(with ((x 5))
    (with ((x 6)
           (y x))
          y))))

(interp
 (parse
  '((fun (x)
         ((fun (y)
               y)
          x))
    11)))

(interp
 (parse
  '(with ((x 5))
    (with ((x 7)
           (y x))
          y))))

(interp
 (parse
  '((fun (x)
         ((fun (x) (+ x x))
          (+ x 1)))
    5)))



"........................................."





