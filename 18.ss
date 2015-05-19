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
  (lambda (sym los k)
    (list-index (lambda (xsym) (eqv? sym xsym)) los k)))

(define list-index
  (lambda (pred ls k)
    (cond
     ((null? ls) (apply-k k #f))
     ((pred (car ls)) (apply-k k 0))
     (else (list-index pred (cdr ls) (lambda (list-index-r)
	     (if (number? list-index-r)
		 (apply-k k (+ 1 list-index-r))
		 (apply-k k #f))))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (vars env)
                           (list-find-position sym (car vars) (lambda (pos)
      	  (if (number? pos)
	      (apply-k succeed (vector-ref (cdr vars) pos))
	      (apply-env env sym succeed fail))))))))








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
		          	(let-exp vars (map syntax-expand bodies))
		          	(let-exp (list (car vars)) (list (syntax-expand (let*-exp (cdr vars) bodies))))) 
			]
			[named-let-exp (name vars bodies)
				(letrec-exp
                                  (list (list
                                          (var-exp name)
                                          (lambda-exp (map cadar vars)
                                                      (map syntax-expand bodies))))
                                  (list (app-exp
                                          (var-exp name)
                                          (map syntax-expand (map cadr vars)))))
			]
			[if-exp (condition if-true if-false) (if-exp (syntax-expand condition) (syntax-expand if-true) (syntax-expand if-false))]
			[if-exp-void (condition if-true) (if-exp-void (syntax-expand condition) (syntax-expand if-true))]
			[set-exp (id value) (set-exp id (syntax-expand value))]
			[or-exp (bodies)
				(if (null? bodies)
					(lit-exp #f)
					(if (null? (cdr bodies))
						(syntax-expand (car bodies))
                                                (let-exp (list (list (var-exp 'if-exp-result) (syntax-expand (car bodies))))
                                                         (list (if-exp (var-exp 'if-exp-result) (var-exp 'if-exp-result) (syntax-expand (or-exp (cdr bodies))))))
					)
				)
			]
			[and-exp (bodies)
				(if (null? bodies)
					(lit-exp #t)
					(if (null? (cdr bodies))
						(syntax-expand (car bodies))
						(if-exp (syntax-expand (car bodies)) (syntax-expand (and-exp (cdr bodies))) (syntax-expand (car bodies)))
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
                        (if-exp-void (if (eqv? 'else (cadaar bodies))
                                       (lit-exp #t)
                                       (syntax-expand (caar bodies)))
                                     (syntax-expand (cadar bodies)))
                        (if-exp (syntax-expand (caar bodies))
                                (syntax-expand (cadar bodies))
                                (syntax-expand (cond-exp (cdr bodies)))))]
            [case-exp (condition bodies)
                      (if (null? (cdr bodies))
                        (if-exp-void (if (eqv? 'else (cadaar bodies))
                                       (lit-exp #t)
                                       (app-exp (var-exp (if (list? (caar bodies)) 'member 'eqv?)) (list (syntax-expand condition) (caar bodies))))
                                       (syntax-expand (begin-exp (cadar bodies))))
                        (if-exp
                          (app-exp (var-exp (if (list? (caar bodies)) 'member 'eqv?)) (list (syntax-expand condition) (caar bodies)))
                          (syntax-expand (begin-exp (cadar bodies)))
                          (syntax-expand (case-exp condition (cdr bodies)))))]
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


; Temporary. Will switch to datatype representation once eval-exp and friends are converted to cps style.
(define (apply-k k . args)
  (apply k args))

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env (lambda (x) x))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env k)
    (cases expression exp
      [lit-exp (datum) (apply-k k datum)]
      [var-exp (id)
               (apply-env env id; look up its value.
      	   k ; procedure to call if id is in the environment 
           (lambda () (apply-env global-env id
                      k
                      (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
                                             "variable not found in environment: ~s"
                                             id)))))] 
      [letrec-exp (vars bodies)
                  (extend-env-recursively vars env (lambda (env)
                                                     (eval-bodies bodies env k)))]
      [let-exp (vars bodies)
               (eval-rands (map cadr vars) env (lambda (rands)
                                                 (eval-bodies bodies (extend-env (map cadar vars) (apply vector rands) env k))))]
      [lambda-exp (ids bodies)
                  (cond
                    [(list? ids)
                     (apply-k k (closure ids bodies env))]
                    [(pair? ids)
                     (apply-k k (closure-dot ids bodies env))]
                    [(symbol? ids)
                     (apply-k k (closure-list ids bodies env))])]
      [app-exp (rator rands)
               (eval-exp rator env (lambda (proc-value)
                                     (eval-rands rands env (lambda (args)
                                                             (apply-proc proc-value args k)))))]
      [if-exp (condition if-true if-false)
              (eval-exp condition env (lambda (val)
                                        (if val
                                          (eval-exp if-true env k)
                                          (eval-exp if-false env k))))]
      [if-exp-void (condition if-true)
                   (eval-exp condition env (lambda (val)
                                             (if val
                                               (eval-exp if-true env k)
                                               (apply-k k (void)))))]
      [while-exp (condition bodies)
                 (eval-exp condition env (lambda (val)
                                           (if val
                                             (eval-bodies bodies env (lambda (result)
                                                                       (eval-exp exp env k)))
                                             (apply-k k (void)))))]
      [set-exp (id value)
               (let helper ([recur-env env])
                 (cases environment recur-env
                        [empty-env-record ()
                                          (eopl:error 'eval-exp "No environment found!")]
                        [extended-env-record (vars next-env)
                                             (list-find-position (cadr id) (car vars) (lambda (pos)
                                               (cond [pos
                                                       (eval-exp value env (lambda (val)
                                                                             (apply-k k (vector-set! (cdr vars) pos val))))]
                                                     [(eqv? next-env (empty-env))
                                                      (set-car! vars (append (car vars) (list (cadr id))))
                                                      (eval-exp value env (lambda (val)
                                                                            (vector-append (cdr vars) val (lambda (vec)
                                                                                                            (apply-k k (set-cdr! vars vec))))))]
                                                     [else
                                                       (helper next-env)])))]))]
      [define-exp (id value)
                  (cases environment env
                         [empty-env-record ()
                                           (eopl:error 'eval-exp "No environment found!")]
                         [extended-env-record (vars next-env)
                                              (list-find-position id (car vars) (lambda (pos)
                                                (cond [pos
                                                        (apply-k k (vector-set! (cdr vars) pos (eval-exp value env)))]
                                                      [else
                                                        (set-car! vars (append (car vars) (list id)))
                                                        (eval-exp value env (lambda (val)
                                                                              (vector-append (cdr vars) (lambda (vec)
                                                                                                              (apply-k k (set-cdr! vars vec)))
                                                                                             val)))])))])]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define (vector-append v k . args)
    (apply-k k (apply vector (append (vector->list v) args))))

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
        (eval-exp (cadr (car vals)) new-env (lambda (val)
                                              (vector-set! new-vals i val)
                                              (helper (+ i 1) (cdr vals))))))))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env k)
    (map-k (lambda (x k) (eval-exp x env k)) rands k)))

(define (eval-bodies bodies env k)
  (if (null? (cdr bodies))
    (eval-exp (car bodies) env k)
    (eval-exp (car bodies) env (lambda (val)
                                 (eval-bodies (cdr bodies) env k)))))

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

(define (arg-number proc args expected k)
  (if (= (length args) expected)
    (apply-k k)
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
      [(zero?) (arg-number zero? args 1 
                           (lambda () (apply-k k 
                                               (zero? (1st args)))))]
      [(not) (arg-number not args 1 
                         (lambda () (apply-k k 
                                             (not (1st args)))))]
      [(add1) (arg-number add1 args 1
                          (lambda () (apply-k k 
                                              (+ (1st args) 1))))]
      [(sub1) (arg-number sub1 args 1 
                          (lambda () (apply-k k 
                                              (- (1st args) 1))))]
      [(cons) (arg-number cons args 2 
                          (lambda () (apply-k k 
                                              (cons (1st args) (2nd args)))))]
      [(=) (arg-number = args 2 
                       (lambda () (apply-k k 
                                           (= (1st args) (2nd args)))))]
      [(<) (arg-number < args 2 
                       (lambda () (apply-k k 
                                           (< (1st args) (2nd args)))))]
      [(>) (arg-number > args 2 
                       (lambda () (apply-k k 
                                           (> (1st args) (2nd args)))))]
      [(>=) (arg-number >= args 2 
                        (lambda () (apply-k k 
                                            (>= (1st args) (2nd args)))))]
      [(<=) (arg-number <= args 2 
                        (lambda () (apply-k k 
                                            (<= (1st args) (2nd args)))))]
      [(list) (apply-k k (apply list args))]
      [(car) (arg-number car args 1 
                         (lambda () (apply-k k 
                                             (car (1st args)))))]
      [(cdr) (arg-number cdr args 1 
                         (lambda () (apply-k k 
                                             (cdr (1st args)))))]
      [(null?) (arg-number null? args 1 
                           (lambda () (apply-k k 
                                               (null?(1st args)))))]
      [(assq) (arg-number assq args 2 
                          (lambda () (apply-k k 
                                              (assq (1st args) (2nd args)))))]
      [(eq?) (arg-number eq? args 2 
                         (lambda () (apply-k k 
                                             (eq? (1st args) (2nd args)))))]
      [(equal?) (arg-number equal? args 2 
                            (lambda () (apply-k k 
                                                (equal? (1st args) (2nd args)))))]
      [(atom?) (arg-number atom? args 1 
                           (lambda () (apply-k k 
                                               (atom? (1st args)))))]
      [(length) (arg-number length args 1 
                            (lambda () (apply-k k 
                                                (length (1st args)))))]
      [(list->vector) (arg-number list->vector args 1 
                                  (lambda () (apply-k k 
                                                      (list->vector (1st args)))))]
      [(list?) (arg-number list? args 1 
                           (lambda () (apply-k k 
                                               (list? (1st args)))))]
      [(pair?) (arg-number pair? args 1 
                           (lambda () (apply-k k 
                                               (pair? (1st args)))))]
      [(procedure?) (arg-number procedure? args 1 
                                (lambda () (apply-k k 
                                                    (proc-val? (car args)))))]
      [(vector->list) (arg-number vector->list args 1 
                                  (lambda () (apply-k k 
                                                      (vector->list (1st args)))))]
      [(vector) (apply-k k (apply vector args))]
      [(make-vector) (arg-number make-vector args 2 
                                 (lambda () (apply-k k 
                                                     (make-vector (1st args) (2nd args)))))]
      [(vector-ref) (arg-number vector-ref args 2 
                                (lambda () (apply-k k 
                                                    (vector-ref (1st args) (2nd args)))))]
      [(vector?) (arg-number vector? args 1 
                             (lambda () (apply-k k 
                                                 (vector? (1st args)))))]
      [(number?) (arg-number number? args 1 
                             (lambda () (apply-k k 
                                                 (number? (1st args)))))]
      [(symbol?) (arg-number symbol? args 1 
                             (lambda () (apply-k k 
                                                 (symbol? (1st args)))))]
      [(set-car!) (arg-number set-car! args 2 
                              (lambda () (apply-k k 
                                                  (set-car! (1st args) (2nd args)))))]
      [(set-cdr!) (arg-number set-cdr! args 2 
                              (lambda () (apply-k k 
                                                  (set-cdr! (1st args) (2nd args)))))]
      [(vector-set!) (arg-number vector-set! args 3 
                                 (lambda () (apply-k k 
                                                     (vector-set! (1st args) (2nd args) (3rd args)))))]
      [(display) (arg-number display args 1 
                             (lambda () (apply-k k 
                                                 (display (1st args)))))]
      [(newline) (arg-number newline args 0 
                             (lambda () (apply-k k 
                                                 (newline))))]
      [(cadr) (arg-number cadr args 1 
                          (lambda () (apply-k k 
                                              (cadr (1st args)))))]
      [(caar) (arg-number caar args 1 
                          (lambda () (apply-k k 
                                              (caar (1st args)))))]
      [(cdar) (arg-number cdar args 1 
                          (lambda () (apply-k k 
                                              (cdar (1st args)))))]
      [(cddr) (arg-number cddr args 1 
                          (lambda () (apply-k k 
                                              (cddr (1st args)))))]
      [(caadr) (arg-number caadr args 1 
                           (lambda () (apply-k k 
                                               (caadr (1st args)))))]
      [(caaar) (arg-number caaar args 1 
                           (lambda () (apply-k k 
                                               (caaar (1st args)))))]
      [(cadar) (arg-number cadar args 1 
                           (lambda () (apply-k k 
                                               (cadar (1st args)))))]
      [(caddr) (arg-number caddr args 1 
                           (lambda () (apply-k k 
                                               (caddr (1st args)))))]
      [(cdadr) (arg-number cdadr args 1 
                           (lambda () (apply-k k 
                                               (cdadr (1st args)))))]
      [(cdaar) (arg-number cdaar args 1 
                           (lambda () (apply-k k 
                                               (cdaar (1st args)))))]
      [(cddar) (arg-number cddar args 1 
                           (lambda () (apply-k k 
                                               (cddar (1st args)))))]
      [(cdddr) (arg-number cdddr args 1 
                           (lambda () (apply-k k 
                                               (cdddr (1st args)))))]
      [(apply)
       (apply-proc (car args) (cadr args) k)]
      [(map) (arg-number map args 2 
                         (lambda () (apply-k k 
                                             (let helper ([proc (car args)] [args (cadr args)] [acc '()])
                                               (if (null? args)
                                                 (reverse acc)
                                                 (apply-proc proc (list (car args)) (lambda (val)
                                                                                      (helper proc (cdr args) (cons val acc)))))))))]
      [(eqv?) (arg-number eqv? args 2 
                          (lambda () (apply-k k 
                                              (eqv? (1st args) (2nd args)))))]
      [(quotient) (arg-number quotient args 2 
                              (lambda () (apply-k k 
                                                  (quotient (1st args) (2nd args)))))]
      [(set-car!) (arg-number set-car! args 2 
                              (lambda () (apply-k k 
                                                  (set-car! (1st args) (2nd args)))))]
      [(member) (arg-number member args 2 
                            (lambda () (apply-k k 
                                                (member (1st args) (2nd args)))))]
      [(append)
       (apply-k k (apply append args))]
      [(list-tail) (arg-number list-tail args 2 
                               (lambda () (apply-k k 
                                                   (list-tail (1st args) (2nd args)))))]
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
