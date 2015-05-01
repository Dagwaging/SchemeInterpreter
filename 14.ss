; Assignment 13
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
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
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
                          (and (expression? (car y))
                               (expression? (cadr y)))) x)))]
    [begin-exp
      (bodies (lambda (x)
                 (andmap expression? x)))]
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
                              (if (= (length x) 2)
                                (map parse-exp x)
                                (eopl:error 'parse-exp "case conditions must take a value and an expression")))
                            (cddr datum)))
                     (eopl:error 'parse-exp "case must have a value and at least one condition"))]
                [(eqv? 'begin (car datum))
                 (begin-exp (map parse-exp (cdr datum)))]
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
				; TODO
                                (letrec-exp (map syntax-expand vars) (map syntax-expand bodies))
			]
			[let*-exp (vars bodies)
		        (if (null? vars)
		          	(let-exp vars (map syntax-expand bodies))
		          	(let-exp (list (car vars)) (list (syntax-expand (let*-exp (cdr vars) bodies))))) 
			]
			[named-let-exp (name vars bodies)
				; TODO
				(named-let-exp name (syntax-expand vars) (map syntax-expand bodies))
			]
			[if-exp (condition if-true if-false) (if-exp (syntax-expand condition) (syntax-expand if-true) (syntax-expand if-false))]
			[if-exp-void (condition if-true) (if-exp-void (syntax-expand condition) (syntax-expand if-true))]
			[set-exp (id value) (set-exp id (syntax-expand value))]
			[or-exp (bodies)
				(if (null? bodies)
					(lit-exp #f)
					(if (null? (cdr bodies))
						(syntax-expand (car bodies))
						(if-exp (syntax-expand (car bodies)) (syntax-expand (car bodies)) (syntax-expand (or-exp (cdr bodies))))
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
                                       (app-exp (var-exp (if (list? (caar bodies))
                                                           'member
                                                           'eqv?))
                                                (list (syntax-expand condition) (syntax-expand (caar bodies)))))
                                     (syntax-expand (cadar bodies)))
                        (if-exp (app-exp (var-exp (if (list? (caar bodies))
                                                           'member
                                                           'eqv?))
                                                (list (syntax-expand condition) (syntax-expand (caar bodies))))
                                (syntax-expand (cadar bodies))
                                (syntax-expand (case-exp condition (cdr bodies)))))]
            [begin-exp (bodies)
                       (if (null? bodies)
                         (lit-exp (void))
                         (app-exp (lambda-exp '() (map syntax-expand bodies)) '()))]
                                    
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
    (extended-env-record syms vals env)))

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
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env env sym succeed fail)))))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
		          "variable not found in environment: ~s"
			   id)))] 
      [let-exp (vars bodies)
               (let ([new-env (extend-env (map cadar vars) (eval-rands (map cadr vars) env) env)])
                     (eval-bodies bodies new-env))]
      [lambda-exp (ids bodies)
                  (cond
                    [(list? ids)
                     (closure ids bodies env)]
                    [(pair? ids)
                     (closure-dot ids bodies env)]
                    [(symbol? ids)
                     (closure-list ids bodies env)])]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [if-exp (condition if-true if-false)
              (if (eval-exp condition env)
                (eval-exp if-true env)
                (eval-exp if-false env))]
      [if-exp-void (condition if-true)
              (if (eval-exp condition env)
                (eval-exp if-true env))]
      [while-exp (condition bodies)
      	(if (eval-exp condition env) 
      		(begin 
      			(eval-bodies bodies env) 
      			(eval-exp exp env)
      		)
      	)
      ]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

(define (eval-bodies bodies env)
  (if (null? (cdr bodies))
             (eval-exp (car bodies) env)
             (begin
               (eval-exp (car bodies) env)
               (eval-bodies (cdr bodies) env))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [closure (ids bodies env)
                  (let ([new-env (extend-env ids args env)])
                    (eval-bodies bodies new-env))]
      [closure-list (id bodies env)
                  (let ([new-env (extend-env (list id) (list args) env)])
                    (eval-bodies bodies new-env))]
      [closure-dot (ids bodies env)
                  (let ([new-env (extend-env
                                   (let helper ([ids ids])
                                     (if (pair? ids)
                                       (cons (car ids)
                                             (helper (cdr ids)))
                                       (list ids)))
                                   (let helper ([ids ids] [args args])
                                     (if (pair? ids)
                                       (cons (car args)
                                             (helper (cdr ids) (cdr args)))
                                       (list args))) env)])
                    (eval-bodies bodies new-env))]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define *prim-proc-names* '(+ - * / zero? not add1 sub1 cons = < > >= <= list car cdr null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline cadr caar cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr apply map eqv? quotient))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))

(define (arg-number proc args expected)
  (if (= (length args) expected)
    #t
    (eopl:error 'apply-prim-proc "Procedure ~s takes ~s arguments, but was given ~s" proc expected args)))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(zero?) (if (arg-number zero? args 1)
             (zero? (1st args)))]
      [(not) (if (arg-number not args 1)
             (not (1st args)))]
      [(add1) (if (arg-number add1 args 1) 
                (+ (1st args) 1))]
      [(sub1) (if (arg-number sub1 args 1)
                (- (1st args) 1))]
      [(cons) (if (arg-number cons args 2)
                (cons (1st args) (2nd args)))]
      [(=) (if (arg-number = args 2)
             (= (1st args) (2nd args)))]
      [(<) (if (arg-number < args 2)
             (< (1st args) (2nd args)))]
      [(>) (if (arg-number > args 2)
             (> (1st args) (2nd args)))]
      [(>=) (if (arg-number >= args 2)
             (>= (1st args) (2nd args)))]
      [(<=) (if (arg-number <= args 2)
             (<= (1st args) (2nd args)))]
      [(list) (apply list args)]
      [(car) (if (arg-number car args 1)
             (car (1st args)))]
      [(cdr) (if (arg-number cdr args 1)
             (cdr (1st args)))]
      [(null?) (if (arg-number null? args 1)
             (null?(1st args)))]
      [(assq) (if (arg-number assq args 2)
             (assq (1st args) (2nd args)))]
      [(eq?) (if (arg-number eq? args 2)
             (eq? (1st args) (2nd args)))]
      [(equal?) (if (arg-number equal? args 2)
             (equal? (1st args) (2nd args)))]
      [(atom?) (if (arg-number atom? args 1)
             (atom? (1st args)))]
      [(length) (if (arg-number length args 1)
             (length (1st args)))]
      [(list->vector) (if (arg-number list->vector args 1)
             (list->vector (1st args)))]
      [(list?) (if (arg-number list? args 1)
             (list? (1st args)))]
      [(pair?) (if (arg-number pair? args 1)
             (pair? (1st args)))]
      [(procedure?) (if (arg-number procedure? args 1)
             (proc-val? (car args)))]
      [(vector->list) (if (arg-number vector->list args 1)
             (vector->list (1st args)))]
      [(vector) (apply vector args)]
      [(make-vector) (if (arg-number make-vector args 2)
             (make-vector (1st args) (2nd args)))]
      [(vector-ref) (if (arg-number vector-ref args 2)
             (vector-ref (1st args) (2nd args)))]
      [(vector?) (if (arg-number vector? args 1)
             (vector? (1st args)))]
      [(number?) (if (arg-number number? args 1)
             (number? (1st args)))]
      [(symbol?) (if (arg-number symbol? args 1)
             (symbol? (1st args)))]
      [(set-car!) (if (arg-number set-car! args 2)
             (set-car! (1st args) (2nd args)))]
      [(set-cdr!) (if (arg-number set-cdr! args 2)
             (set-cdr! (1st args) (2nd args)))]
      [(vector-set!) (if (arg-number vector-set! args 3)
             (vector-set! (1st args) (2nd args) (3rd args)))]
      [(display) (if (arg-number display args 1)
             (display (1st args)))]
      [(newline) (if (arg-number newline args 0)
             (newline))]
      [(cadr) (if (arg-number cadr args 1)
             (cadr (1st args)))]
      [(caar) (if (arg-number caar args 1)
             (caar (1st args)))]
      [(cdar) (if (arg-number cdar args 1)
             (cdar (1st args)))]
      [(cddr) (if (arg-number cddr args 1)
             (cddr (1st args)))]
      [(caadr) (if (arg-number caadr args 1)
             (caadr (1st args)))]
      [(caaar) (if (arg-number caaar args 1)
             (caaar (1st args)))]
      [(cadar) (if (arg-number cadar args 1)
             (cadar (1st args)))]
      [(caddr) (if (arg-number caddr args 1)
             (caddr (1st args)))]
      [(cdadr) (if (arg-number cdadr args 1)
             (cdadr (1st args)))]
      [(cdaar) (if (arg-number cdaar args 1)
             (cdaar (1st args)))]
      [(cddar) (if (arg-number cddar args 1)
             (cddar (1st args)))]
      [(cdddr) (if (arg-number cdddr args 1)
             (cdddr (1st args)))]
      [(apply)
             (apply-proc (car args) (cadr args))]
      [(map) (if (arg-number map args 2)
               (let helper ([proc (car args)] [args (cadr args)] [acc '()])
                 (if (null? args)
                   (reverse acc)
                   (helper proc (cdr args)
                           (cons (apply-proc proc (list (car args)))
                                 acc)))))]
      [(eqv?) (if (arg-number eqv? args 2)
                (eqv? (1st args) (2nd args)))]
      [(quotient) (if (arg-number quotient args 2)
                    (quotient (1st args) (2nd args)))]
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
