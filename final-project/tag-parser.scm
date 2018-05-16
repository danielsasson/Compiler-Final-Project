(load "project/qq.scm")

(define *reserved-words*
	'(and begin cond define do else if lambda let let* letrec or quasiquote unquote unquote-splicing quote set!))

(define parse
	(lambda (expr)
		(cond 
			((const-expr? expr)
				`(const ,expr))

			((quote-case? expr)
				`(const ,@(cdr expr)))

			((variable-expr? expr)
				`(var ,expr))

			((full-if-expr? expr)
				(let ((test (cadr expr))
					  (dit (caddr expr))
					  (dif (cadddr expr)))
					`(if3 ,(parse test) ,(parse dit) ,(parse dif))))
  		
			((short-if-expr? expr)
				(let ((test (cadr expr))
					  (dit (caddr expr)))
					`(if3 ,(parse test) ,(parse dit)  (const ,(void)))))

			((applic-expr? expr)
				`(applic ,(parse (car expr)) ,(map parse (cdr expr))))

			((or-exp? expr)
				(if (equal? (length expr) 1)
					`(const ,#f)							;or no has arguments
					(if (equal? (length expr) 2)
						(parse (cadr expr))
						`(or ,(map parse (cdr expr))))))		;otherwise

			((ass-expr? expr)
				`(set ,@(map parse (cdr expr)))) 

			((regular-lambda? expr)
				(let ((args (cadr expr))
					  (body (cddr expr)))					
					`(lambda-simple ,args ,(parse `(begin ,@body)))))

			((optional-lambda? expr)
				(let ((args (opt-lambda-args (cadr expr) '()))
					  (lastOptionalArg (opt-lambda-last-arg (cadr expr)))
					  (body (cddr expr)))
					`(lambda-opt ,args ,lastOptionalArg ,(parse `(begin ,@body)))))			

			((variadic-lambda-expr? expr)
				(let ((args (cadr expr))
					  (body (cddr expr)))
					`(lambda-opt () ,args ,(parse `(begin ,@body)))))	

			((regular-define? expr)
				(let ((var (cadr expr))
					  (xpr (caddr expr)))
					`(define ,(parse var) ,(parse xpr))))

			((MIT-properArgs-define? expr)				;expr-form --> (define (v1 v2 .. nN) e1 e2 .. eM)
				(let ((var (if (null? (cadr expr)) '() (caadr expr)))
					  (lambdaArgs (cdadr expr))
					  (exprns (cddr expr)))
					`(define ,(parse var) ,(parse `(lambda ,lambdaArgs ,@exprns)))))		

			((MIT-imProperArgs-define? expr)
				(let ((var (if (null? (cadr expr)) '() (caadr expr)))
					  (args (opt-lambda-args (cdadr expr) '()))
					  (lastOptionalArg (opt-lambda-last-arg (cdadr expr)))
					  (exprns (cddr expr)))
					`(define ,(parse var) (lambda-opt ,args ,lastOptionalArg ,(parse `(begin ,@exprns))))))

			((seq-expr? expr)	
				(if (> (length (cdr expr)) 1)
					`(seq ,(map parse (flat-begin-expr (cdr expr))))
					(if (equal? (length (cdr expr)) 1)
						`,(parse (cadr expr))
						`(const ,(void)
						))))


	
			((let-expr? expr)
				(let* ((bnds (cadr expr))
					   (xprns (cddr expr))
					   (vars (fold-right cons '() (map car bnds)))
					   (values (fold-right cons '() (map cadr bnds))))
						`,(parse `((lambda ,vars ,@xprns) ,@values))))

			((letStar-expr? expr)
				(let* ((bnds (cadr expr))
					   (xprns (cddr expr))
					   (vars (fold-right cons '() (map car bnds)))
					   (values (fold-right cons '() (map cadr bnds))))
						(if (null? bnds)
								`,(parse `(let () ,@xprns))
								`,(parse `,(fold-right 
									(lambda(curr acc)
										(if (equal? xprns acc)
											`(let ,(list curr) ,@acc)
											`(let ,(list curr) ,acc))
									)		
									xprns
									bnds 
								)))))
	
			((letRec-expr? expr)
				(let* ((bnds (cadr expr))
					   (xprns (cddr expr))
					   (vars (fold-right cons '() (map car bnds)))
					   (values (fold-right cons '() (map cadr bnds))))
						
					`,(parse `(let
								,(map
									 (lambda (var) (list var #f))
									 vars)
								,@(map
									 (lambda (bnd) `(set! ,(car bnd) ,(cadr bnd)))
									 bnds)
								(let () ,@xprns)
								))))


			((and-expr? expr)
				(let ((last (car (reverse expr))))
						(if (equal? (length expr) 1)
							`(const ,#t)							;or no has arguments
							(if (equal? (length expr) 2)
								`,(parse (cadr expr))
								`,(parse `,(fold-right 
												(lambda (curr acc) `(if ,curr ,acc #f))
												last
												(reverse(cdr (reverse (cdr expr))))))))
				)
			)

			((cond-expr? expr)
				(let ((preds (map car (cdr expr)))
					  (xprns (map cdr (cdr expr)))
					  (last (car (reverse expr))))
					`,(parse 
						(if (equal? 'else (caar (reverse expr)))	;checking if there is and 'else' condition
							`,(fold-right 
								(lambda (curr acc) `(if ,(car curr) (begin ,@(cdr curr)) ,acc))
								 `(begin ,@(cdar (reverse expr)))
								(cdr (reverse (cdr (reverse expr)))))	;list of all conditions without the 'else' condition		
							`,(fold-right 
								(lambda (curr acc) `(if ,(car curr) (begin ,@(cdr curr)) ,acc))
								`(if ,(car last) (begin ,@(cdr last)))
								(cdr (reverse (cdr (reverse expr)))))
						)
					)
				)
			)


			((quasiquote-expr? expr)
				`,(parse (expand-qq (cadr expr)))) 


  		)
  	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-expr?
	(lambda (expr)
		(or 
			(null? expr)
			(vector? expr)
			(boolean? expr)
			(char? expr)
			(number? expr)
			(integer? expr)
			(string? expr))
	)
)

(define quote-case?
	(lambda (expr)
		(and (list? expr)
			 (not (null? expr))
			 (equal? (car expr) 'quote))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define consist-reserve?
	(lambda (expr)
		(if (list? (member expr *reserved-words*))
				#t
				#f)
	)
)

(define variable-expr?
	(lambda(expr)
		(if (not (consist-reserve? expr))
				(if (symbol? expr)
					#t 						;not consist & symbol
					#f 						;ot a symbol
				)
			#f 								;is consist
		)
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define full-if-expr?
	(lambda (expr)
		(and
				(list? expr)
				(not (null? expr))
				(equal? (car expr) 'if)
				(equal? (length expr) 4))
	)
)

(define short-if-expr?
	(lambda (expr)
		(and
				(list? expr)
				(not (null? expr))
				(equal? (car expr) 'if)
				(equal? (length expr) 3))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define applic-expr?
	(lambda (expr)
		(and
				(list? expr)
				(not (null? expr))
				(not (consist-reserve? (car expr))))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define or-exp?
	(lambda (expr)
		(and
				(list? expr)
				(not (null? expr))
				(equal? (car expr) 'or))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ass-expr?
	(lambda(expr)
		(and
				(list? expr)
				;(equal? (length expr) 3)
				(equal? (car expr) 'set!))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define regular-lambda?   			;TO CHECK - should be seq'
	(lambda (expr)
		(and
				(list? expr)
				(equal? (car expr) 'lambda)			
				(list? (cadr expr))) 				;checks (v1 v2.. vN) form - parameters should apeears in a list struct
	)
)

(define optional-lambda?
	(lambda (expr)
		(and
				(list? expr)
				;(> (length expr) 2)
				(equal? (car expr) 'lambda)											
				(pair? (cadr expr))) 				;checks (v1 v2.. vN . v) form
	)
)

(define opt-lambda-args
	(lambda (lst acc)
		(if (not (pair? lst)) 
			'()
			(if (and (pair? lst) (pair? (cdr lst))) 
        	(opt-lambda-args (cdr lst) (append acc (list (car lst))))
        	(append acc (list (car lst))))
        )
    )
)

(define opt-lambda-last-arg
	(lambda (lst)
		(if (pair? lst)
			(opt-lambda-last-arg (cdr lst))
			lst
		)
	)
)

(define variadic-lambda-expr?
	(lambda (expr)
		(and
				(list? expr)
				(equal? (car expr) 'lambda)			
				(not (list? (cadr expr)))
				(> (length expr) 2))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define regular-define?
	(lambda (expr)
		(and
				(list? expr)
				(equal? (length expr) 3)
				(equal? (car expr) 'define)
				(not (list? (cadr expr)))
				(not (pair? (cadr expr))))
	)
)

(define MIT-properArgs-define?
	(lambda (expr)
		(and
				(list? expr)
				(> (length expr) 2)
				(equal? (car expr) 'define)
				(list? (cadr expr))
				(> (length (cadr expr)) 0))			;function name must appear
	)
)

(define MIT-imProperArgs-define?
	(lambda (expr)
		(and
				(list? expr)
				(> (length expr) 2)
				(equal? (car expr) 'define)
				(pair? (cadr expr)))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define seq-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'begin))
	)
)


(define flat-begin-expr
	(lambda (expr)
		(fold-right
			(lambda (curr acc) 
				(if (and (not (null? curr)) (list? curr))
					(if (equal? (car curr) 'begin)
						(flat-begin-expr (append (cdr curr) acc))
						(cons curr acc))
					(cons curr acc))
				)
			'()
			expr
		)
	)
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define let-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'let))
	)	
)

(define letStar-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'let*))
	)
)


(define letRec-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'letrec))
	)	
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define and-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'and))
	)	
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cond-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'cond))
	)	
)

(define quasiquote-expr?
	(lambda (expr)
		(and
			(list? expr)
			(not (null? expr))
			(equal? (car expr) 'quasiquote))
	)	
)





