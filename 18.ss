; Assignment 17
; Zane Geiger & Philip Ross

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

(define (map-dot proc x)
  (if (pair? x)
    (cons (proc (car x))
         (map-dot proc (cdr x)))
    (proc x)))

(define (andmap-dot proc x)
  (if (pair? x)
    (and (proc (car x))
         (andmap-dot proc (cdr x)))
    (proc x)))

(define (split-dot x)
  (list
    (let first ([x x])
      (if (pair? x)
        (cons (car x)
              (first (cdr x)))
        '()))
    (let second ([x x])
      (if (pair? x)
        (second (cdr x))
        x))))


(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
    (vars (lambda (x)
            (and ((list-of symbol?) (car x))
                 (scheme-value? (cdr x)))))
    (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
    (ids (list-of symbol?))
    (bodies (list-of expression?))
    (env environment?)]
  [closure-list
    (id symbol?)
    (bodies (list-of expression?))
    (env environment?)]
  [closure-dot
    (ids (lambda (x) (andmap-dot symbol? x)))
    (bodies (list-of expression?))
    (env environment?)])
	 
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+

(define-datatype expression expression?
	[var-exp (id symbol?)]
	[lit-exp (value
		(lambda (x)
                  #t
		)
	)]
	[lambda-exp
		(ids (lambda (x) 
			(or 
				(symbol? x)
                                (andmap-dot symbol? x)
				(andmap symbol? x)
			)
		))
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[let-exp
		(vars (lambda (x) 
			(and 
				(list? x)
					(andmap (lambda (y)
						(and 
							(eq? 2 (length y))
							(expression? (car y))
							(expression? (cadr y))
						)
					)
				x
				)
			)
		))
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[letrec-exp
		(vars (lambda (x) 
			(and 
				(list? x)
					(andmap (lambda (y)
						(and 
							(eq? 2 (length y))
							(expression? (car y))
							(expression? (cadr y))
						)
					)
				x
				)
			)
		))
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[let*-exp
		(vars (lambda (x) 
			(and 
				(list? x)
					(andmap (lambda (y)
						(and 
							(eq? 2 (length y))
							(expression? (car y))
							(expression? (cadr y))
						)
					)
				x
				)
			)
		))
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[named-let-exp
		(name symbol?)
		(vars (lambda (x) 
			(and 
				(list? x)
					(andmap (lambda (y)
						(and 
							(eq? 2 (length y))
							(expression? (car y))
							(expression? (cadr y))
						)
					)
				x
				)
			)
		))
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[app-exp
		(rator expression?)
		(rands (lambda (x) 
			(andmap expression? x))
		)
	]
	[if-exp
		(condition expression?)
		(if-true expression?)
		(if-false expression?)
	]
	[if-exp-void
		(condition expression?)
		(if-true expression?)
	]
	[set-exp
		(id expression?)
		(value expression?)
	]
	[and-exp 
		(bodies 
			(lambda (x) (andmap expression? x))
		)
	]
	[or-exp 
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
	[while-exp
		(condition expression?)
		(bodies (lambda (x) 
			(andmap expression? x))
		)
	]
    [cond-exp
      (bodies (lambda (x)
                (andmap (lambda (y)
                          (and (expression? (car y))
                               (expression? (cadr y)))) x)))]
    [case-exp
      (condition expression?)
      (bodies (lambda (x)
                (andmap (lambda (y)
                          (and (or (expression? (car y)) (andmap expression? (car y)))
                               (andmap expression? (cadr y))))
                        x)))]
    [begin-exp
      (bodies (lambda (x)
                 (andmap expression? x)))]
    [case-lambda-exp
      (cases (lambda (x)
               (andmap (lambda (y)
                         (and (andmap expression? (car y)) (andmap expression? (cadr y))))
               x)))]
    [define-exp
      (id symbol?)
      (value expression?)]
)

(define (parse-exp datum)
	(cond
		[(symbol? datum) (var-exp datum)]
		[(number? datum) (lit-exp datum)]
		[(string? datum) (lit-exp datum)]
		[(vector? datum) (lit-exp datum)]
		[(boolean? datum) (lit-exp datum)]
		[(pair? datum)
			(cond
				[(not (list? datum)) 
					(eopl:error 'parse-exp "application ~s is not a proper list" datum)
				]
				[(eqv? 'lambda (car datum))
					(if (< 2 (length datum))
						(lambda-exp 
							(cond 
								[(list? (cadr datum))
									(if (andmap symbol? (cadr datum))
										(cadr datum)
										(eopl:error 'parse-exp "lambda arguments must only be symbols, arguments were ~s" (cadr datum))
									)
								]
                                                                [(pair? (cadr datum))
                                                                 (if (andmap-dot symbol? (cadr datum))
                                                                   (cadr datum)
                                                                   (eopl:error 'parse-exp "lambda arguments must only be symbols, arguments were ~s" (cadr datum)))]
								[(symbol? (cadr datum))
									(cadr datum)
								]
								[else
									(eopl:error 'parse-exp "first argument of lambda must be an argument name or list of argument names")
								]
							)
							(map parse-exp (cddr datum))
						)
						(eopl:error 'parse-exp "lambda statement must contain a list of argument names and at least one expression")
					)
				]
                                [(eqv? 'quote (car datum))
                                 (lit-exp (cadr datum))]
				[(and (eqv? 'let (car datum)) (symbol? (cadr datum)))
					(if (< 3 (length datum))
						(if 
							(and 
								(symbol? (cadr datum))
								(list? (caddr datum))
								(andmap (lambda (y)
									(and 
										(list? y)
										(eq? 2 (length y))
										(symbol? (car y))
										(expression? (parse-exp (cadr y)))
									))
									(caddr datum)
								)
							)
							(named-let-exp
								(cadr datum)
								(map (lambda (x) 
									(map parse-exp x)
									)
									(caddr datum)
								)
								(map parse-exp (cdddr datum))
							)
							(eopl:error 'parse-exp "first argument of named let must be a name and the second argument must be a list of argument name / value pairs")
						)
						(eopl:error 'parse-exp "named let statement must contain a name, a list of argument / value pairs and at least one expression")
					)
				]
				[(eqv? 'let (car datum))
					(if (< 2 (length datum))
						(if 
							(and 
								(list? (cadr datum))
								(andmap (lambda (y)
									(and 
										(list? y)
										(eq? 2 (length y))
										(symbol? (car y))
										(expression? (parse-exp (cadr y)))
									))
									(cadr datum)
								)
							)
							(let-exp 
								(map (lambda (x) 
									(map parse-exp x)
									)
									(cadr datum)
								)
								(map parse-exp (cddr datum))
							)
							(eopl:error 'parse-exp "first argument of let must be a list of argument name / value pairs")
						)
						(eopl:error 'parse-exp "let statement must contain a list of argument / value pairs and at least one expression")
					)
				]
				[(eqv? 'letrec (car datum))
					(if (< 2 (length datum))
						(if 
							(and 
								(list? (cadr datum))
								(andmap (lambda (y)
									(and 
										(list? y)
										(eq? 2 (length y))
										(symbol? (car y))
										(expression? (parse-exp (cadr y)))
									))
									(cadr datum)
								)
							)
							(letrec-exp 
								(map (lambda (x) 
									(map parse-exp x)
									)
									(cadr datum)
								)
								(map parse-exp (cddr datum))
							)
							(eopl:error 'parse-exp "first argument of letrec must be a list of argument name / value pairs")
						)
						(eopl:error 'parse-exp "letrec statement must contain a list of argument / value pairs and at least one expression")
					)
				]
				[(eqv? 'let* (car datum))
					(if (< 2 (length datum))
						(if 
							(and 
								(list? (cadr datum))
								(andmap (lambda (y)
									(and 
										(list? y)
										(eq? 2 (length y))
										(symbol? (car y))
										(expression? (parse-exp (cadr y)))
									))
									(cadr datum)
								)
							)
							(let*-exp 
								(map (lambda (x) 
									(map parse-exp x)
									)
									(cadr datum)
								)
								(map parse-exp (cddr datum))
							)
							(eopl:error 'parse-exp "first argument of let* must be a list of argument name / value pairs")
						)
						(eopl:error 'parse-exp "let* statement must contain a list of argument / value pairs and at least one expression")
					)
				]				
				[(eqv? 'if (car datum))
					(cond
						[(eq? (length datum) 3)
							(apply if-exp-void (map parse-exp (cdr datum)))
						]
						[(eq? (length datum) 4)
							(apply if-exp (map parse-exp (cdr datum)))
						] 
						[else
							(eopl:error 'parse-exp "if statement must contain a condition and one or two expressions")
						]
					)
				]
				[(eqv? 'set! (car datum))
					(if (eq? (length datum) 3)
						(if (symbol? (cadr datum))
							(set-exp (parse-exp (cadr datum)) (parse-exp (caddr datum)))
							(eopl:error 'parse-exp "first argument of set! must be a variable name")
						)
						(eopl:error 'parse-exp "set! must take a variable name and an expression")
					)
				]
				[(eqv? 'and (car datum))
					(and-exp (map parse-exp (cdr datum)))
				]
				[(eqv? 'or (car datum))
					(or-exp (map parse-exp (cdr datum)))
				]
				[(eqv? 'while (car datum))
					(while-exp (parse-exp (cadr datum)) (map parse-exp (cddr datum)))
				]
                [(eqv? 'cond (car datum))
                 (if (> (length datum) 1)
                   (cond-exp 
                     (map (lambda (x)
                            (if (= (length x) 2)
                              (map parse-exp x)
                              (eopl:error 'parse-exp "cond conditions must take a condition and an expression")))
                          (cdr datum)))
                   (eopl:error 'parse-exp "cond must have at least one condition"))]
                [(eqv? 'case (car datum))
                   (if (> (length datum) 2)
                     (case-exp
                       (parse-exp (cadr datum))
                       (map (lambda (x)
                              (if (>= (length x) 2)
                                (list (lit-exp (car x)) (map parse-exp (cdr x)))
                                (eopl:error 'parse-exp "case conditions must take a value and an expression")))
                            (cddr datum)))
                     (eopl:error 'parse-exp "case must have a value and at least one condition"))]
                [(eqv? 'begin (car datum))
                 (begin-exp (map parse-exp (cdr datum)))]
                [(eqv? 'case-lambda (car datum))
                 (if (null? (cdr datum))
                   (eopl:error 'parse-exp "case-lambda must have at least one case")
                   (if (ormap (lambda (x) (not (>= (length x) 2))) (cdr datum))
                     (eopl:error 'parse-exp "case-lambda cases must have a list of parameters and a body")
                     (case-lambda-exp (map (lambda (body)
                                             (list (map parse-exp (car body)) (map parse-exp (cdr body))))
                                           (cdr datum)))))]
                [(eqv? 'define (car datum))
                 (if (not (= (length datum) 3))
                   (eopl:error 'parse-exp "define must have an id and a value")
                   (define-exp (cadr datum) (parse-exp (caddr datum))))]
				[else 
					(app-exp 
						(parse-exp (car datum))
						(map parse-exp (cdr datum))
					)
				]
			)
		]
		[else 
			(eopl:error 'parse-exp "bad expression: ~s" datum)
		]
	)
)


(define unparse-exp
	(lambda (exp)
		(cases expression exp
			[var-exp (id) id]
			[lit-exp (value) value]
			[app-exp (rator rands)
				(cons (unparse-exp rator) (map unparse-exp rands))
			]
			[set-exp (id value)
				(list 'set! (unparse-exp id) (unparse-exp value))
			]
			[if-exp (condition if-true if-false)
				(list 'if (unparse-exp condition) (unparse-exp if-true) (unparse-exp if-false))
			]
			[if-exp-void (condition if-true)
				(list 'if (unparse-exp condition) (unparse-exp if-true))
			]
			[lambda-exp (ids bodies)
				(if (or (null? ids) (expression? (car ids)))
					(cons 'lambda (cons (map unparse-exp ids) (map unparse-exp bodies)))
					(cons 'lambda (cons (unparse-exp ids) (map unparse-exp bodies)))
				)
			]
			[let-exp (vars bodies)
				(cons 'let 
					(cons 
						(map (lambda (x) 
								(list (unparse-exp (car x)) (unparse-exp (cadr x)))
							)
							vars
						)
						(map unparse-exp bodies)))
			]
			[letrec-exp (vars bodies)
				(cons 'letrec
					(cons 
						(map (lambda (x) 
								(list (unparse-exp (car x)) (unparse-exp (cadr x)))
							)
							vars
						)
						(map unparse-exp bodies)))
			]
			[let*-exp (vars bodies)
				(cons 'let* 
					(cons 
						(map (lambda (x) 
								(list (unparse-exp (car x)) (unparse-exp (cadr x)))
							)
							vars
						)
						(map unparse-exp bodies)))
			]
			[named-let-exp (name vars bodies)
				(cons 'let 
					(cons 
						name
						(cons 
							(map (lambda (x) 
									(list (unparse-exp (car x)) (unparse-exp (cadr x)))
								)
								vars
							)
							(map unparse-exp bodies)
						)
					)
				)
			]
			[and-exp (bodies)
				(cons 'and bodies)
			]
			[or-exp (bodies)
				(cons 'or bodies)
			]
			[while-exp (condition bodies)
				(list 'while condition (map unparse-exp bodies))
			]
		)
	)
)



;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record (cons syms vals) env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (apply-k fail (void)))
      (extended-env-record (vars env)
	(let ((pos (list-find-position sym (car vars))))
      	  (if (number? pos)
	      (apply-k succeed (vector-ref (cdr vars) pos))
	      (apply-env env sym succeed fail)))))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+


(define syntax-expand
	(lambda (exp)
	    (cases expression exp
			[var-exp (id) exp]
			[lit-exp (value) exp]
			[app-exp (rator rands) (app-exp (syntax-expand rator) (map syntax-expand rands))]
			[lambda-exp (ids bodies) (lambda-exp ids (map syntax-expand bodies))]
			[let-exp (vars bodies)
				(app-exp (lambda-exp (map cadar vars) (map syntax-expand bodies)) (map syntax-expand (map cadr vars)))
			]
			[letrec-exp (vars bodies)
                                (letrec-exp (map list (map car vars) (map syntax-expand (map cadr vars))) (map syntax-expand bodies))
			]
			[let*-exp (vars bodies)
		        (if (null? vars)
		          	(syntax-expand (let-exp vars (map syntax-expand bodies)))
		          	(syntax-expand (let-exp (list (car vars)) (list (syntax-expand (let*-exp (cdr vars) bodies)))))) 
			]
			[named-let-exp (name vars bodies)
				(syntax-expand (letrec-exp
                                                 (list (list
                                                         (var-exp name)
                                                         (lambda-exp (map cadar vars)
                                                                     (map syntax-expand bodies))))
                                                 (list (app-exp
                                                         (var-exp name)
                                                         (map syntax-expand (map cadr vars))))))
			]
			[if-exp (condition if-true if-false) (if-exp (syntax-expand condition) (syntax-expand if-true) (syntax-expand if-false))]
			[if-exp-void (condition if-true) (if-exp-void (syntax-expand condition) (syntax-expand if-true))]
			[set-exp (id value) (set-exp id (syntax-expand value))]
			[or-exp (bodies)
				(if (null? bodies)
					(lit-exp #f)
					(if (null? (cdr bodies))
						(syntax-expand (car bodies))
                                                (syntax-expand (let-exp (list (list (var-exp 'if-exp-result) (syntax-expand (car bodies))))
                                                                        (list (if-exp (var-exp 'if-exp-result) (var-exp 'if-exp-result) (syntax-expand (or-exp (cdr bodies)))))))
					)
				)
			]
			[and-exp (bodies)
				(if (null? bodies)
					(lit-exp #t)
					(if (null? (cdr bodies))
						(syntax-expand (car bodies))
						(syntax-expand (if-exp (syntax-expand (car bodies)) (syntax-expand (and-exp (cdr bodies))) (syntax-expand (car bodies))))
					)
				)
			]
			[while-exp (condition bodies)
                                   (while-exp (syntax-expand condition) (map syntax-expand bodies))
			; (display (map syntax-expand bodies))
			; (newline)
			; 	(list 'named-let-exp 'recurse '() (if-exp-void (syntax-expand condition) (begin-exp (map syntax-expand bodies))))
			]
            [cond-exp (bodies)
                      (if (null? (cdr bodies))
                        (syntax-expand (if-exp-void (if (eqv? 'else (cadaar bodies))
                                                      (lit-exp #t)
                                                      (syntax-expand (caar bodies)))
                                                    (syntax-expand (cadar bodies))))
                        (syntax-expand (if-exp (syntax-expand (caar bodies))
                                               (syntax-expand (cadar bodies))
                                               (syntax-expand (cond-exp (cdr bodies))))))]
            [case-exp (condition bodies)
                      (if (null? (cdr bodies))
                        (syntax-expand (if-exp-void (if (eqv? 'else (cadaar bodies))
                                                      (lit-exp #t)
                                                      (app-exp (var-exp (if (list? (caar bodies)) 'member 'eqv?)) (list (syntax-expand condition) (caar bodies))))
                                                    (syntax-expand (begin-exp (cadar bodies)))))
                        (syntax-expand (if-exp
                                         (app-exp (var-exp (if (list? (caar bodies)) 'member 'eqv?)) (list (syntax-expand condition) (caar bodies)))
                                         (syntax-expand (begin-exp (cadar bodies)))
                                         (syntax-expand (case-exp condition (cdr bodies))))))]
            [begin-exp (bodies)
                       (if (null? bodies)
                         (lit-exp (void))
                         (app-exp (lambda-exp '() (map syntax-expand bodies)) '()))]
            [case-lambda-exp (bodies)
                             (lambda-exp 'args (list
                                                 (syntax-expand (case-exp (app-exp (var-exp 'length) (list (var-exp 'args)))
                                                                          (map (lambda (body)
                                                                                 (list (lit-exp (list (length (car body))))
                                                                                       (let helper ([args (car body)])
                                                                                         (if (null? args)
                                                                                           (cadr body)
                                                                                           (list (let-exp (list (list (car args) (app-exp (var-exp 'car) (list (var-exp 'args))))
                                                                                                          (list (var-exp 'args) (app-exp (var-exp 'cdr) (list (var-exp 'args)))))
                                                                                                    (helper (cdr args))))))))
                                                                               bodies)))))]
            [define-exp (id value)
                        (define-exp id (syntax-expand value))]
                                    
		)
	)
)

;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+

(define-datatype continuation continuation?
                 [test-k (then-exp expression?)
                         (else-exp expression?)
                         (env environment?)
                         (k continuation?)]
                 [test-k-void (then-exp expression?)
                              (env environment?)
                              (k continuation?)]
                 [rator-k (rands (list-of expression?))
                          (env environment?)
                          (k continuation?)]
                 [rands-k (proc-value scheme-value?)
                          (k continuation?)]
                 [while-k (exp expression?)
                          (bodies (list-of expression?))
                          (env environment?)
                          (k continuation?)]
                 [eval-k (exp expression?)
                         (env environment?)
                         (k continuation?)]
                 [apply-global-env-k (env environment?)
                              (id symbol?)
                              (success continuation?)]
                 [no-var-k (id symbol?)]
                 [letrec-k (bodies (list-of expression?))
                           (k continuation?)]
                 [set-k (vars pair?)
                        (pos number?)
                        (k continuation?)]
                 [define-k (vars pair?)
                           (k continuation?)]
                 [bodies-k (bodies (list-of expression?))
                           (env environment?)
                           (k continuation?)]
                 [helper-k (proc procedure?)
                           (args list?)]
                 [map-helper-k (proc proc-val?)
                               (l list?)
                               (k continuation?)]
                 [cons-k (l list?)
                           (k continuation?)]
                 [extend-env-k (new-vals box?)
                               (pos number?)
                               (vals list?)
                               (proc procedure?)]
                 [identity-k])

; Temporary. Will switch to datatype representation once eval-exp and friends are converted to cps style.
(define (apply-k k val)
  (cases continuation k
         [test-k (then-exp else-exp env k)
                 (if val
                   (eval-exp then-exp env k)
                   (eval-exp else-exp env k))]
         [test-k-void (then-exp env k)
                      (if val
                        (eval-exp then-exp env k)
                        (apply-k k (void)))]
         [rator-k (rands env k)
                  (eval-rands rands env (rands-k val k))]
         [rands-k (proc-value k)
                  (apply-proc proc-value val k)]
         [while-k (exp bodies env k)
                  (if val
                    (eval-bodies bodies env (eval-k exp env k))
                    (apply-k k (void)))]
         [eval-k (exp env k)
                 (eval-exp exp env k)]
         [apply-global-env-k (env id success)
                      (apply-env env id success (no-var-k id))]
         [no-var-k (id)
                   (eopl:error 'apply-env "variable not found in environment: ~s" id)]
         [letrec-k (bodies k)
                   (eval-bodies bodies val k)]
         [set-k (vars pos k)
                (apply-k k (vector-set! (cdr vars) pos val))]
         [define-k (vars k)
                   (apply-k k (set-cdr! vars (vector-append (cdr vars) val)))]
         [bodies-k (bodies env k)
                   (eval-bodies bodies env k)]
         [helper-k (proc args)
                   (apply proc args)]
         [map-helper-k (proc l k)
                       (if (null? l)
                         (apply-k k (reverse val))
                         (apply-proc proc (list (car l))
                                     (cons-k val (map-helper-k proc (cdr l) k))))]
         [cons-k (l k)
                   (apply-k k (cons val l))]
         [extend-env-k (new-vals pos vals proc)
                       (vector-set! (unbox new-vals) pos val)
                       (proc (+ pos 1) (cdr vals))]
         [identity-k ()
           val]))

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env (identity-k))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env k)
    (cases expression exp
      [lit-exp (datum) (apply-k k datum)]
      [var-exp (id)
               (apply-env env id k
                          (apply-global-env-k global-env id k))]
      [letrec-exp (vars bodies)
                  (extend-env-recursively vars env
                                          (letrec-k bodies k))]
      [lambda-exp (ids bodies)
                  (cond
                    [(list? ids)
                     (apply-k k (closure ids bodies env))]
                    [(pair? ids)
                     (apply-k k (closure-dot ids bodies env))]
                    [(symbol? ids)
                     (apply-k k (closure-list ids bodies env))])]
      [app-exp (rator rands)
               (eval-exp rator env
                         (rator-k rands env k))]
      [if-exp (condition if-true if-false)
              (eval-exp condition env
                        (test-k if-true if-false env k))]
      [if-exp-void (condition if-true)
                   (eval-exp condition env
                             (test-k-void if-true env k))]
      [while-exp (condition bodies)
                 (eval-exp condition env 
                           (while-k exp bodies env k))]
      [set-exp (id value)
               (let helper ([recur-env env])
                 (cases environment recur-env
                        [empty-env-record ()
                                          (eopl:error 'eval-exp "No environment found!")]
                        [extended-env-record (vars next-env)
                                             (let ([i (list-find-position (cadr id) (car vars))])
                                               (cond [i
                                                       (eval-exp value env
                                                                 (set-k vars i k))]
                                                     [(eqv? next-env (empty-env))
                                                      (set-car! vars (append (car vars) (list (cadr id))))
                                                      (eval-exp value env (define-k vars k))]
                                                     [else
                                                       (helper next-env)]))]))]
      [define-exp (id value)
                  (cases environment env
                         [empty-env-record ()
                                           (eopl:error 'eval-exp "No environment found!")]
                         [extended-env-record (vars next-env)
                                              (let ([i (list-find-position id (car vars))])
                                                (cond [i
                                                        (eval-exp value env (set-k vars i k))]
                                                      [else
                                                        (set-car! vars (append (car vars) (list id)))
                                                        (eval-exp value env (define-k vars k))]))])]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define (vector-append v . args)
    (apply vector (append (vector->list v) args)))

(define (map-k proc-k l k)
  (let helper ([l l] [acc '()])
    (if (null? l)
      (apply-k k (reverse acc))
      (proc-k (car l) (lambda (r)
                        (helper (cdr l) (cons r acc)))))))

(define (reset-global-env)
  (set! init-env (extend-env (list) (vector) (empty-env))))

(define (extend-env-recursively vals env k)
  (let* ([syms (map car vals)]
        [new-vals (make-vector (length syms))]
        [new-env (extended-env-record (cons (map cadr syms) new-vals) env)])
    (let helper ([i 0] [vals vals])
      (if (null? vals)
        (apply-k k new-env)
        (eval-exp (cadr (car vals)) new-env
                  (extend-env-k (box new-vals) i vals helper))))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env k)
    (apply-k k (map (lambda (x) (eval-exp x env (identity-k))) rands))))

(define (eval-bodies bodies env k)
  (if (null? (cdr bodies))
    (eval-exp (car bodies) env k)
    (eval-exp (car bodies) env (bodies-k (cdr bodies) env k))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args k)]
			; You will add other cases
      [closure (ids bodies env)
               (eval-bodies bodies (extend-env ids (apply vector args) env) k)]
      [closure-list (id bodies env)
                    (eval-bodies bodies (extend-env (list id) (vector args) env) k)]
      [closure-dot (ids bodies env)
                  (eval-bodies bodies (extend-env
                    (let helper ([ids ids])
                      (if (pair? ids)
                        (cons (car ids)
                              (helper (cdr ids)))
                        (list ids)))
                    (apply vector (let helper ([ids ids] [args args])
                                    (if (pair? ids)
                                      (cons (car args)
                                            (helper (cdr ids) (cdr args)))
                                      (list args))))
                    env) k)]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / zero? not add1 sub1 cons = < > >= <= list car cdr null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline cadr caar cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr apply map eqv? quotient set-car! member append list-tail))

(define global-env       ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (apply vector (map prim-proc      
          *prim-proc-names*))
     (empty-env)))

(define init-env (extend-env (list) (vector) (empty-env)))

(define (arg-number proc args expected)
  (if (= (length args) expected)
    #t
    (eopl:error 'apply-prim-proc "Procedure ~s takes ~s arguments, but was given ~s" proc expected args)))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args k)
    (case prim-proc
      [(+) (apply-k k (apply + args))]
      [(-) (apply-k k (apply - args))]
      [(*) (apply-k k (apply * args))]
      [(/) (apply-k k (apply / args))]
      [(zero?) (apply-k k (if (arg-number zero? args 1)
             (zero? (1st args))))]
      [(not) (apply-k k (if (arg-number not args 1)
             (not (1st args))))]
      [(add1) (apply-k k (if (arg-number add1 args 1) 
                (+ (1st args) 1)))]
      [(sub1) (apply-k k (if (arg-number sub1 args 1)
                (- (1st args) 1)))]
      [(cons) (apply-k k (if (arg-number cons args 2)
                (cons (1st args) (2nd args))))]
      [(=) (apply-k k (if (arg-number = args 2)
             (= (1st args) (2nd args))))]
      [(<) (apply-k k (if (arg-number < args 2)
             (< (1st args) (2nd args))))]
      [(>) (apply-k k (if (arg-number > args 2)
             (> (1st args) (2nd args))))]
      [(>=) (apply-k k (if (arg-number >= args 2)
             (>= (1st args) (2nd args))))]
      [(<=) (apply-k k (if (arg-number <= args 2)
             (<= (1st args) (2nd args))))]
      [(list) (apply-k k (apply list args))]
      [(car) (apply-k k (if (arg-number car args 1)
             (car (1st args))))]
      [(cdr) (apply-k k (if (arg-number cdr args 1)
             (cdr (1st args))))]
      [(null?) (apply-k k (if (arg-number null? args 1)
             (null?(1st args))))]
      [(assq) (apply-k k (if (arg-number assq args 2)
             (assq (1st args) (2nd args))))]
      [(eq?) (apply-k k (if (arg-number eq? args 2)
             (eq? (1st args) (2nd args))))]
      [(equal?) (apply-k k (if (arg-number equal? args 2)
             (equal? (1st args) (2nd args))))]
      [(atom?) (apply-k k (if (arg-number atom? args 1)
             (atom? (1st args))))]
      [(length) (apply-k k (if (arg-number length args 1)
             (length (1st args))))]
      [(list->vector) (apply-k k (if (arg-number list->vector args 1)
             (list->vector (1st args))))]
      [(list?) (apply-k k (if (arg-number list? args 1)
             (list? (1st args))))]
      [(pair?) (apply-k k (if (arg-number pair? args 1)
             (pair? (1st args))))]
      [(procedure?) (apply-k k (if (arg-number procedure? args 1)
             (proc-val? (car args))))]
      [(vector->list) (apply-k k (if (arg-number vector->list args 1)
             (vector->list (1st args))))]
      [(vector) (apply-k k (apply vector args))]
      [(make-vector) (apply-k k (if (arg-number make-vector args 2)
             (make-vector (1st args) (2nd args))))]
      [(vector-ref) (apply-k k (if (arg-number vector-ref args 2)
             (vector-ref (1st args) (2nd args))))]
      [(vector?) (apply-k k (if (arg-number vector? args 1)
             (vector? (1st args))))]
      [(number?) (apply-k k (if (arg-number number? args 1)
             (number? (1st args))))]
      [(symbol?) (apply-k k (if (arg-number symbol? args 1)
             (symbol? (1st args))))]
      [(set-car!) (apply-k k (if (arg-number set-car! args 2)
             (set-car! (1st args) (2nd args))))]
      [(set-cdr!) (apply-k k (if (arg-number set-cdr! args 2)
             (set-cdr! (1st args) (2nd args))))]
      [(vector-set!) (apply-k k (if (arg-number vector-set! args 3)
             (vector-set! (1st args) (2nd args) (3rd args))))]
      [(display) (apply-k k (if (arg-number display args 1)
             (display (1st args))))]
      [(newline) (apply-k k (if (arg-number newline args 0)
             (newline)))]
      [(cadr) (apply-k k (if (arg-number cadr args 1)
             (cadr (1st args))))]
      [(caar) (apply-k k (if (arg-number caar args 1)
             (caar (1st args))))]
      [(cdar) (apply-k k (if (arg-number cdar args 1)
             (cdar (1st args))))]
      [(cddr) (apply-k k (if (arg-number cddr args 1)
             (cddr (1st args))))]
      [(caadr) (apply-k k (if (arg-number caadr args 1)
             (caadr (1st args))))]
      [(caaar) (apply-k k (if (arg-number caaar args 1)
             (caaar (1st args))))]
      [(cadar) (apply-k k (if (arg-number cadar args 1)
             (cadar (1st args))))]
      [(caddr) (apply-k k (if (arg-number caddr args 1)
             (caddr (1st args))))]
      [(cdadr) (apply-k k (if (arg-number cdadr args 1)
             (cdadr (1st args))))]
      [(cdaar) (apply-k k (if (arg-number cdaar args 1)
             (cdaar (1st args))))]
      [(cddar) (apply-k k (if (arg-number cddar args 1)
             (cddar (1st args))))]
      [(cdddr) (apply-k k (if (arg-number cdddr args 1)
             (cdddr (1st args))))]
      [(apply)
             (apply-proc (car args) (cadr args) k)]
      [(map) (if (arg-number map args 2)
               (apply-k (map-helper-k (car args) (cadr args) k) '()))]
      [(eqv?) (apply-k k (if (arg-number eqv? args 2)
                (eqv? (1st args) (2nd args))))]
      [(quotient) (apply-k k (if (arg-number quotient args 2)
                    (quotient (1st args) (2nd args))))]
      [(set-car!) (apply-k k (if (arg-number set-car! args 2)
                    (set-car! (1st args) (2nd args))))]
      [(member) (apply-k k (if (arg-number member args 2)
                    (member (1st args) (2nd args))))]
      [(append)
       (apply-k k (apply append args))]
      [(list-tail) (apply-k k (if (arg-number list-tail args 2)
                     (list-tail (1st args) (2nd args))))]
      [else (eopl:error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))
