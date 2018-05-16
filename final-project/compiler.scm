;(load "sexpr-parser.scm") 
;(load "tag-parser.scm")
;(load "semantic-analyzer.scm")

(define AST-additional 
	(lambda (AST)
		(append (string->list (string-append fvar-list fvar-fold-left fvar-bin-append fvar-append fvar-map)) AST)))

(define fvar-list (string-append
							"(define list "
									"(lambda x x))\n"))

(define fvar-fold-left (string-append
							"(define fold-left "
									"(lambda (func init lst) (if (null? lst)" 
																"init" 
																"(fold-left func (func init (car lst)) (cdr lst)))))\n"))

(define fvar-bin-append (string-append
							"(define bin-append (lambda (lst1 lst2) (if (null? lst1) "
																		"lst2 "
																		"(cons (car lst1) (bin-append (cdr lst1) lst2)))))\n"))
(define fvar-append (string-append
						"(define append "
							"(lambda x (fold-left bin-append '() x)))\n"))

(define fvar-map (string-append
						"(define map "
							"(lambda (func lst) "
									"(if (null? lst) "
									"lst "
									"(cons (func (car lst)) (map func (cdr lst))))))\n"))
;(define map (lambda (func lst) (if (null? lst) lst (cons (func (car lst)) (map func (cdr lst))))))

;################# PREDICATEs #################

(define is-const-expr?
	(lambda (pe)
		(and
			(list? pe)
			(eq? (car pe) 'const))))

(define is-fvar-expr?
	(lambda (pe)
		(and
			(list? pe)
			(eq? (car pe) 'fvar))))

(define is-void?
	(lambda (pe)
		(eq? pe (void))
		))


(define (containing-list? lst)
  (ormap (lambda (subList) (list? subList)) lst))

(define (is-containing? lst1 lst2)
  (if (list? lst2)
        (if (member lst1 lst2)
        	#t
        	(ormap (lambda (subList) (is-containing? lst1 subList)) lst2))
		#f))


;################# HELPERs #################

(define (vector-length expr)
  (length (vector->list expr)))

(define (string-length expr)
   (length (string->list expr)))

(define (symbol-length expr)
   (length (string->list (symbol->string expr))))

(define (count-list-elements lst)
  (if (null-or-not-list? lst)
  	  1
      (apply + (map count-list-elements lst))))


;####LABEL-COUNTERS####

(define global-label-counter 0)
(define if3-label-counter 0)
(define or-label-counter 0)
(define applic-label-counter 0)
(define lambda-label-counter 0)
(define gcd-label-counter 0)

(define if3-label-plusplus
	(lambda ()
		(begin (set! if3-label-counter (+ if3-label-counter 1)))
				(- if3-label-counter 1)))		; return value

(define global-label-plusplus
	(lambda ()
		(begin (set! global-label-counter (+ global-label-counter 1)))
				(- global-label-counter 1)))		; return value

(define or-label-plusplus
	(lambda ()
		(begin (set! or-label-counter (+ or-label-counter 1)))
				(- or-label-counter 1)))		; return value


(define applic-label-plusplus
	(lambda ()
		(begin (set! applic-label-counter (+ applic-label-counter 1)))
				(- applic-label-counter 1)))	; return value


(define lambda-label-plusplus
	(lambda ()
		(begin (set! lambda-label-counter (+ lambda-label-counter 1)))
				(- lambda-label-counter 1)))	; return value

(define gcd-label-plusplus
	(lambda ()
		(begin (set! gcd-label-counter (+ gcd-label-counter 1)))
				(- gcd-label-counter 1)))	; return value


;####CONST-TABLE####

(define <globalSymbols> (list))

(define (remove-dups lst)
  (if (null? lst)
       '()
        (if (member (car lst) (cdr lst))
         	(remove-dups (cdr lst))
     		(cons (car lst) (remove-dups (cdr lst))))))

(define depth-const-exprs
	(lambda (expr)
	  (cond ((or (char? expr) (integer? expr) (is-void? expr) (null? expr) (boolean? expr)) `(,expr))
	        ((list? expr) 		`(,expr ,@(depth-const-exprs (car expr)) ,@(depth-const-exprs (cdr expr))))
	        ((string? expr) 	`(,expr ,@(apply append (map depth-const-exprs (string->list expr)))))
	        ((vector? expr) 	`(,expr ,@(apply append (map depth-const-exprs (vector->list expr)))))
	        ((symbol? expr) 	`(,expr ,@(depth-const-exprs (symbol->string expr))))
	        ((pair? expr) 		`(,expr ,@(depth-const-exprs (car expr)) ,@(depth-const-exprs (cdr expr))))
	        ((rational? expr) 	`(,expr ,@(depth-const-exprs (numerator expr)) ,@(depth-const-exprs (denominator expr))))
	        (else 				(display 'ERROR-->func:depth-const-exprs)))))

(define sort-by-func
	(lambda (exp1 exp2)
		(cond   ((and (number? exp1) (number? exp2)) (if (< exp1 exp2) #t #f))
		        ((and (char? exp1) (char? exp2)) (if (< (char->integer exp1) (char->integer exp2)) #t #f))
		        ((and (list? exp1) (list? exp2)) (cond ((is-containing? exp1 exp2) #t)
		                                               ((is-containing? exp2 exp1) #f)
		                                               ((and (containing-list? exp1) (not (containing-list? exp2))) #f)
		                                               ((and (containing-list? exp2) (not (containing-list? exp1))) #t)
		                                               ((< (count-list-elements exp1) (count-list-elements exp2)) #t)
		                                               ((> (count-list-elements exp1) (count-list-elements exp2)) #f)
		                                               (else #t)))
		        ((and (string? exp1) (string? exp2)) (if (< (string-length exp1) (string-length exp2)) #t #f))
		        ((and (symbol? exp1) (symbol? exp2)) (if (< (symbol-length exp1) (symbol-length exp2)) #t #f))

		        ((number? exp1) #t)
		        ((number? exp2) #f)
		        ((char? exp1) #t)
		        ((char? exp2) #f)
		        ((string? exp1) #t)
		        ((string? exp2) #f)
		        ((symbol? exp1) #t)
		        ((symbol? exp2) #f)
		        ((list? exp1) #t)
		        ((list? exp2) #f)
		        (else #t))))




(define find-const-index
	(lambda (const pre-asm-table)
		(if (eq? pre-asm-table (list)) 
				"ERROR - func:find-const-index"
				(let ((currConst (cadar pre-asm-table))
					  (currIndex (caar pre-asm-table)))
		    		(if (equal? const currConst) 
		    			currIndex
		          		(find-const-index const (cdr pre-asm-table)))))))
		          
		   

(define build-const-lst
	(lambda (str-AST)
		(letrec ((constList '())
				 (default-constList (list '() (void) #t #f))
				 (const-lookup (lambda (pe)
				 					(if (null-or-not-list? pe)
				 						'()
				 						(if (is-const-expr? pe)
				 							(set! constList (append constList (depth-const-exprs (cadr pe))))
				 							(map const-lookup pe))))))			;not a const expr---> lookup inside by recursion
			(begin 
				(const-lookup str-AST)
				(set! constList (filter 
									(lambda (element)
											(not (member element default-constList)))
									(remove-dups constList)))
									;constList))
				(append 
					default-constList 
					(sort 
						sort-by-func
						constList))))))

(define memConstLocation 0)

(define memLocationPlusNum
	(lambda (num)
		(set! memConstLocation (+ memConstLocation num))))


(define build-pre-asm-const-table
	(lambda (constList pre-const-table)
		(if (eq? constList (list))
			(reverse pre-const-table)
			(cond ((eq? (car constList) (list)) 	(begin (memLocationPlusNum 1) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 1) ,(car constList) (T_NIL)) pre-const-table))))
		      	  ((eq? (car constList) (void)) 	(begin (memLocationPlusNum 1) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 1) ,(car constList) (T_VOID)) pre-const-table))))
		          ((eq? (car constList) #t) 		(begin (memLocationPlusNum 2) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 2) ,(car constList) (T_BOOL 1)) pre-const-table))))    
		          ((eq? (car constList) #f) 		(begin (memLocationPlusNum 2) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 2) ,(car constList) (T_BOOL 0)) pre-const-table))))  
		          ((integer? (car constList)) 		(begin (memLocationPlusNum 3) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 3) ,(car constList) ,`(T_INTEGER ,(car constList))) pre-const-table))))  
		          ((char? (car constList)) 			(begin (memLocationPlusNum 2) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 2) ,(car constList) ,`(T_CHAR  ,(char->integer (car constList)))) pre-const-table))))  
		          ((pair? (car constList)) 			(begin (memLocationPlusNum 3) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 3) ,(car constList) ,`(T_PAIR ,(find-const-index (caar constList) pre-const-table) ,(find-const-index (cdar constList) pre-const-table))) pre-const-table))))  
		          ((vector? (car constList)) 		(begin (memLocationPlusNum (+ 2 (vector-length (car constList)))) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation (+ 2 (vector-length (car constList)))) ,(car constList) ,`(T_VECTOR ,(vector-length (car constList)) ,@(map (lambda (x) (find-const-index x pre-const-table)) (reverse (vector->list (car constList)))))) pre-const-table))))  
		          ((string? (car constList)) 		(begin (memLocationPlusNum (+ 2 (string-length (car constList)))) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation (+ 2 (string-length (car constList)))) ,(car constList) ,`(T_STRING ,(string-length (car constList)) ,@(map (lambda (x) (char->integer x)) (reverse (string->list (car constList)))))) pre-const-table))))
		          ((symbol? (car constList)) 		(begin (memLocationPlusNum 2) (set! <globalSymbols> (cons (- memConstLocation 2) <globalSymbols>)) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 2) ,(car constList) ,`(T_SYMBOL ,(find-const-index (symbol->string (car constList)) pre-const-table))) pre-const-table))))
		          ((rational? (car constList)) 		(begin (memLocationPlusNum 3) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 3) ,(car constList) ,`(T_FRACTION ,(find-const-index (numerator (car constList)) pre-const-table) ,(find-const-index (denominator (car constList)) pre-const-table))) pre-const-table))))					;FRACTION NUM CASE
		      ))))

;((symbol? (car constList)) 		(begin (memLocationPlusNum 2) (set! <globalSymbols> (cons (find-const-index (symbol->string (car constList)) pre-const-table) <globalSymbols>)) (build-pre-asm-const-table (cdr constList) (cons `(,(- memConstLocation 2) ,(car constList) ,`(T_SYMBOL ,(find-const-index (symbol->string (car constList)) pre-const-table))) pre-const-table))))

(define myVecStringAppend
	(lambda (lst constList final)
		(if (null? lst)
			(if (not (equal? final ""))
				(remove-last-char (remove-last-char final)))				;; delete the last --> ', '
			(myVecStringAppend (cdr lst) constList (string-append final (find-label-by-value (car lst) constList) ", ")))))

(define remove-last-char
	(lambda (str)
		(list->string (reverse (cdr (reverse (string->list str)))))))




(define	build-asm-const-data 
	(lambda (pre-asm-table)						;pre-asm-table = constList
		(if (null-or-not-list? pre-asm-table)
			"" 
	        (letrec ((handle-single-const (lambda (constTriplet)				;	constTriplet = (address value [type etc.])
							        		(let* ((address (car constTriplet))
							        			   (value (cadr constTriplet))
							        			   (type (caaddr constTriplet)))
						                        (cond ((eq? type 'T_NIL) 		(string-append "\nconst_NIL:\n\tdq SOB_NIL\n"))
						                              ((eq? type 'T_VOID) 		(string-append "\nconst_VOID:\n\tdq SOB_VOID\n"))
						                              ((eq? type 'T_BOOL) 		(string-append "\nconst_BOOL_" (if (equal? value #f) "FALSE:\n\tdq SOB_FALSE\n" "TRUE:\n\tdq SOB_TRUE\n")))
						                              ((eq? type 'T_CHAR) 		(string-append "\nconst_char_" (number->string address) ":\n\tdq MAKE_LITERAL(T_CHAR, " (number->string (char->integer value)) ")\n"))
						                              ((eq? type 'T_INTEGER)	(string-append "\nconst_number_" (if (< value 0) (string-append "neg_" (number->string (- value))) (number->string value)) ":\n\tdq MAKE_LITERAL(T_INTEGER, " (number->string value) ")\n"))
						                              ((eq? type 'T_PAIR) 		(string-append "\nconst_PAIR_byAdrs" (number->string address) ":\n\tdq MAKE_LITERAL_PAIR(" (find-label-by-value (car value) pre-asm-table) ", " (find-label-by-value (cdr value) pre-asm-table) ")\n"))
						                              ((eq? type 'T_STRING) 	(string-append "\nconst_string_" (number->string address) ":\n\tMAKE_LITERAL_STRING \"" value "\"\n"))			;TOCHECK
						                              ((eq? type 'T_SYMBOL) 	(string-append "\nconst_symbol_" (number->string address) ":\n\tdq MAKE_LITERAL_SYMBOL(" (find-label-by-value (symbol->string value) pre-asm-table) ")\n"))
						                              ((eq? type 'T_FRACTION) 	(string-append "\nconst_fraction" (if (< value 0) (string-append "neg" (number->string (- (numerator value)))) (number->string  (numerator value)))  "_" (number->string (denominator value)) ":\n\tdq MAKE_LITERAL_FRACTION(" (find-label-by-value (numerator value) pre-asm-table) ", " (find-label-by-value (denominator value) pre-asm-table) ")\n"))
						                              ((eq? type 'T_VECTOR) 	(string-append "\nconst_vector_byadrs" (number->string address) ":\n\tMAKE_LITERAL_VECTOR " (if (equal? value '#()) "" (myVecStringAppend (vector->list value) pre-asm-table "")) "\n"))
						                              (else 'ERROR-func:build-asm-const-data ))))))
	        	(apply string-append (map handle-single-const pre-asm-table))))))
;(number->string (/ (numerator value) (gcd (cadr (caddr constTriplet)) (caddr (caddr constTriplet))))) "_" (number->string (/ (denominator value) (gcd (cadr (caddr constTriplet)) (caddr (caddr constTriplet)))))
;(remove-last-char (remove-last-char (foo2 (foo value) "")))
(define	find-label-by-value
	(lambda (value constList)					;	constTriplet = (address value [type etc.])
		(if (null-or-not-list? constList)
			'ERROR--->func:find-label-by-value	
    		(let* ((constTriplet (car constList))
    			   (address (car constTriplet))
    			   (valueConst (cadr constTriplet))
    			   (type (caaddr constTriplet)))
                (if (equal? value valueConst)
                	(cond ((eq? type 'T_NIL) 	"const_NIL")
                          ((eq? type 'T_VOID) 	"const_VOID")
                          ((eq? type 'T_BOOL) 	(string-append "const_BOOL_" (if (equal? value #f) "FALSE" "TRUE")))
                          ((eq? type 'T_CHAR) 	(string-append "const_char_" (number->string address)))
                          ((eq? type 'T_INTEGER)(string-append "const_number_" (if (< value 0) (string-append "neg_" (number->string (- value))) (number->string value))))
                          ((eq? type 'T_PAIR) 	(string-append "const_PAIR_byAdrs" (number->string address)))
                          ((eq? type 'T_STRING) (string-append "const_string_" (number->string address)))		;TOCHECK
                          ((eq? type 'T_SYMBOL) (string-append "const_symbol_" (number->string address)))
                          ((eq? type 'T_FRACTION) (string-append "const_fraction" (if (< value 0) (string-append "neg" (number->string (- (numerator value)))) (number->string  (numerator value)))  "_" (number->string (denominator value))))
                          ((eq? type 'T_VECTOR) (string-append "const_vector_byadrs" (number->string address)))
                          (else 'ERROR-func:find-label-by-value))
                	(find-label-by-value value (cdr constList)))))))
					
                          

(define build-const-lst
	(lambda (str-AST)
		(letrec ((constList '())
				 (default-constList (list '() (void) #t #f))
				 (const-lookup (lambda (pe)
				 					(if (null-or-not-list? pe)
				 						'()
				 						(if (is-const-expr? pe)
				 							(set! constList (append constList (depth-const-exprs (cadr pe))))
				 							(map const-lookup pe))))))			;not a const expr---> lookup inside by recursion
			(begin 
				(const-lookup str-AST)
				(set! constList (filter 
									(lambda (element)
											(not (member element default-constList)))
									(remove-dups constList)))
									;constList))
				(append 
					default-constList 
					(sort 
						sort-by-func
						constList))))))



;####<---SYMBOL-TABLE--->####

(define headSymbolTable "const_NIL")

(define symbol-data-asm
	(lambda (reverse_globalSymbolList prevLAbel constList final) 		
		(if (null-or-not-list? reverse_globalSymbolList)
			final
			(let ((currSymbolAddres (car reverse_globalSymbolList)))
				(if (null-or-not-list? (cdr reverse_globalSymbolList))
					(set! headSymbolTable (string-append "const_symbol_PAIR" (number->string currSymbolAddres))))
				(symbol-data-asm (cdr reverse_globalSymbolList) (string-append "const_symbol_PAIR" (number->string currSymbolAddres)) constList (string-append final "\nconst_symbol_PAIR" (number->string currSymbolAddres) ":\n\tdq MAKE_LITERAL_PAIR("(find-string-label-by-symbol-address currSymbolAddres constList constList) ", " prevLAbel")\n"))))))

(define allocate-space-to-symbol-table-head
	(lambda (asm-constable)
		(string-append "\nhead_of_symbol_list:\n\t dq SOB_UNDEFINED\n" asm-constable)))

;####<---FVAR--->####

(define find-string-label-by-symbol-address 	;address = memlocation
	(lambda (symbolAddres constList originalConstList)
		(if (null-or-not-list? constList)
			"ERROR:find-string-label-by-symbol-address"
			(let* ((constTriplet (car constList))
				   (address (car constTriplet))
				   (value (cadr constTriplet))
				   (type (caaddr constTriplet)))
				(if (equal? symbolAddres address)
					(find-label-by-value (symbol->string value) originalConstList)
					(find-string-label-by-symbol-address symbolAddres (cdr constList) originalConstList))))))

(define memFvarLocation 0)

(define memFvarLocationPlusPlus
	(lambda ()
		(set! memFvarLocation (+ memFvarLocation 1))))


(define build-fvar-table
	(lambda (str-AST)
		(letrec (;(fvarList '())
				 (fvarList '(append apply < = > + / * - boolean? car cdr char->integer char? cons denominator eq? integer? integer->char list make-string make-vector map not null? number? numerator pair? procedure? rational? remainder set-car! set-cdr! string-length string-ref string-set! string->symbol string? symbol? symbol->string vector vector-length vector-ref vector-set! vector? zero?))
				
				(fvar-lookup (lambda (pe)
								(if (or (null-or-not-list? pe) (is-const-expr? pe))
									'()
									(if (is-fvar-expr? pe)
										(set! fvarList (append fvarList (list (cadr pe))))
										(map fvar-lookup pe))))))
			(begin (fvar-lookup str-AST) (remove-dups fvarList)))))


(define build-pre-asm-fvar-table
	(lambda (fvarList pre-fvar-table)
		(if (eq? fvarList (list))
			(reverse pre-fvar-table)
			(begin (memFvarLocationPlusPlus) (build-pre-asm-fvar-table (cdr fvarList) (cons `(,(- memFvarLocation 1) ,(car fvarList)) pre-fvar-table))))))


(define build-asm-fvar-data
	(lambda (pre-fvar-table)
		(if (null-or-not-list? pre-fvar-table)
			"" 
	        (letrec ((handle-single-fvar (lambda (fvarPair)				
							        		(let* ((address (car fvarPair))
							        			   (value (cadr fvarPair)))
												(string-append "\nfvar" (number->string address) ":\n\tdq SOB_UNDEFINED\n")))))
	        	(apply string-append (map handle-single-fvar pre-fvar-table))))))

		         

(define find-fvar-index-by-name
	(lambda (fvarName fvarList)
		(if (eq? fvarList (list))
			"ERROR - func:find-fvar-index-by-name"
			(let* ((currFvarElement (car fvarList))
				  (currIndexFvar   (car currFvarElement))
				  (currNameFvar    (cadr currFvarElement)))
				(if (equal? fvarName currNameFvar)
					currIndexFvar
					(find-fvar-index-by-name fvarName (cdr fvarList)))))))


;####<---END-FVAR--->####




;#################################################
;############# OUR LIBRARY FUNCTIONS #############
;#################################################

(define fvar-boolean-pred
	(lambda (fvarList constList)
		(let ((bool-body-label "bool_predicate_func")
			  (bool-end-body-label "end_boolean_pred")
			  (is-bool-label "isBollean")
			  (bool-make-clousure "make_boolean_pred_closure"))
		(string-append 
			"\t jmp " bool-make-clousure "\n"

			bool-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"
			"\tmov rax, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov rax, [rax]\n"				;value og args[0]
			"\tTYPE rax\n"
			"\tcmp rax, T_BOOL\n"
			"\tje " is-bool-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " bool-end-body-label "\n"
			is-bool-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			bool-end-body-label ":\n"
			"\tpop rbp\n"
			"\tret\n"

			bool-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " bool-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'boolean? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-char-pred
	(lambda (fvarList constList)
		(let ((char-body-label "char_predicate_func")
			  (char-end-body-label "end_char_pred")
			  (is-char-label "isChar")
			  (char-make-clousure "make_char_pred_closure"))
		(string-append 
			"\t jmp " char-make-clousure "\n"

			char-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10
			
			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_CHAR\n"
			"\tje " is-char-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " char-end-body-label "\n"
			is-char-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			char-end-body-label ":\n"

			"\tpop r10\n"

			"\tpop rbp\n"
			"\tret\n"

			char-make-clousure ":\n"
			;"\tmov rcx, [rbp + 2*8]\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " char-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'char? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-integer-pred
	(lambda (fvarList constList)
		(let ((integer-body-label "integer_predicate_func")
			  (integer-end-body-label "end_integer_pred")
			  (is-integer-label "isInteger")
			  (integer-make-clousure "make_integer_pred_closure"))
		(string-append 
			"\t jmp " integer-make-clousure "\n"

			integer-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_INTEGER\n"
			"\tje " is-integer-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " integer-end-body-label "\n"
			is-integer-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			integer-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			integer-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " integer-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'integer? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-number-pred
	(lambda (fvarList constList)
		(let ((number-body-label "number_predicate_func")
			  (number-end-body-label "end_number_pred")
			  (is-number-label "isNumber")
			  (number-make-clousure "make_number_pred_closure"))
		(string-append 
			"\t jmp " number-make-clousure "\n"

			number-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_INTEGER\n"
			"\tje " is-number-label "\n"

			"\tcmp r10, T_FRACTION\n"
			"\tje " is-number-label "\n"

			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " number-end-body-label "\n"

			is-number-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"

			number-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			number-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " number-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'number? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-rational-pred
	(lambda (fvarList constList)
		(let ((rational-body-label "rational_predicate_func")
			  (rational-end-body-label "end_rational_pred")
			  (is-rational-label "isRational")
			  (rational-make-clousure "make_rational_pred_closure"))
		(string-append 
			"\t jmp " rational-make-clousure "\n"

			rational-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_FRACTION\n"
			"\tje " is-rational-label "\n"

			"\tcmp r10, T_INTEGER\n"
			"\tje " is-rational-label "\n"


			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " rational-end-body-label "\n"
			is-rational-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			rational-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			rational-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " rational-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'rational? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-string-pred
	(lambda (fvarList constList)
		(let ((string-body-label "string_predicate_func")
			  (string-end-body-label "end_string_pred")
			  (is-string-label "isString")
			  (string-make-clousure "make_string_pred_closure"))
		(string-append 
			"\t jmp " string-make-clousure "\n"

			string-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			;"L7:\tmov r10, [r10]\n"				;value og args[0]
			"\tmov r10, [r10]\n"
			"\tTYPE r10\n"
			"\tcmp r10, T_STRING\n"
			"\tje " is-string-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " string-end-body-label "\n"
			is-string-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			string-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			string-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " string-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'string? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-pair-pred
	(lambda (fvarList constList)
		(let ((pair-body-label "pair_predicate_func")
			  (pair-end-body-label "end_pair_pred")
			  (is-pair-label "isPair")
			  (pair-make-clousure "make_pair_pred_closure"))
		(string-append 
			"\tjmp " pair-make-clousure "\n"

			pair-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_PAIR\n"
			"\tje " is-pair-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " pair-end-body-label "\n"
			is-pair-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			pair-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			pair-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " pair-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'pair? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-null-pred
	(lambda (fvarList constList)
		(let ((null-body-label "null_predicate_func")
			  (null-end-body-label "end_null_pred")
			  (is-null-label "isNull")
			  (null-make-clousure "make_null_pred_closure"))
		(string-append 
			"\tjmp " null-make-clousure "\n"

			null-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, SOB_NIL\n"
			"\tje " is-null-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " null-end-body-label "\n"
			is-null-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			null-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			null-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " null-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'null? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-procedure-pred
	(lambda (fvarList constList)
		(let ((procedure-body-label "procedure_predicate_func")
			  (procedure-end-body-label "end_procedure_pred")
			  (is-procedure-label "isProcedure")
			  (procedure-make-clousure "make_procedure_pred_closure"))
		(string-append 
			"\tjmp " procedure-make-clousure "\n"

			procedure-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_CLOSURE\n"
			"\tje " is-procedure-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " procedure-end-body-label "\n"
			is-procedure-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			procedure-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			procedure-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " procedure-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'procedure? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-vector-pred
	(lambda (fvarList constList)
		(let ((vector-body-label "vector_predicate_func")
			  (vector-end-body-label "end_vector_pred")
			  (is-vector-label "isVector")
			  (vector-make-clousure "make_vector_pred_closure"))
		(string-append 
			"\tjmp " vector-make-clousure "\n"

			vector-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [r10]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_VECTOR\n"
			"\tje " is-vector-label "\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " vector-end-body-label "\n"
			is-vector-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"
			vector-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			vector-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " vector-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'vector? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-car-func
	(lambda (fvarList constList)
		(let ((car-body-label "car_func")
			  (car-make-clousure "make_car_closure"))
		(string-append 
			"\tjmp " car-make-clousure "\n"

			car-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"
			"\tmov rax, [rbp + 4 * 8]\n"			;points to args[0], value to "car"
			"\tmov rax, [rax]\n"				;value og args[0]
			"\tDATA_UPPER rax\n"
			"\tadd rax, start_of_data\n"
			"\tpop rbp\n"
			"\tret\n"

			car-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " car-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'car fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-cdr-func
	(lambda (fvarList constList)
		(let ((cdr-body-label "cdr_func")
			  (cdr-make-clousure "make_cdr_closure"))
		(string-append 
			"\tjmp " cdr-make-clousure "\n"

			cdr-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tmov rax, [rbp + 4 * 8]\n"			;points to args[0], value to "car"
			"\tmov rax, [rax]\n"				;value og args[0]
			"\tDATA_LOWER rax\n"
			"\tadd rax, start_of_data\n"

			"\tpop rbp\n"
			"\tret\n"

			cdr-make-clousure ":\n"
			;"\tmov rcx, [rbp + 2*8]\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " cdr-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'cdr fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-not-func
	(lambda (fvarList constList)
		(let ((not-body-label "not_predicate_func")
			  (not-end-body-label "end_not_pred")
			  (is-not-false-label "not_is_not_Fasle")
			  (not-make-clousure "make_not_pred_closure"))
		(string-append 
			"\tjmp " not-make-clousure "\n"

			not-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov rax, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov rax, [rax]\n"				;value og args[0]
			"\tmov r10, rax\n"
			"\tcmp r10, [const_BOOL_FALSE]\n"
			"\tjne " is-not-false-label "\n"

			"\tmov rax, " (find-label-by-value #t constList) "\n"
			"\tjmp " not-end-body-label "\n"

			is-not-false-label ":\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			not-end-body-label ":\n"

			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			not-make-clousure ":\n"
			;"\tmov rcx, [rbp + 2*8]\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " not-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'not fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-zero-pred
	(lambda (fvarList constList)
		(let ((zero-body-label "zero_predicate_func")
			  (zero-end-body-label "end_zero_pred")
			  (is-zero-label "zero_isZero")
			  (zero-make-clousure "make_zero_pred_closure"))
		(string-append 
			"\tjmp " zero-make-clousure "\n"

			zero-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10
			"\tpush rbx\n"						;BU rbx

			"\tmov rbx, [rbp + 4 * 8]\n"		;points to args[0], valuve to check
			"\tmov r10, [rbx]\n"				;value og args[0]
			"\tTYPE r10\n"
			"\tcmp r10, T_INTEGER\n"
			"\tjne incorrect_input\n"

			"\tmov r10, [rbx]\n"
			"\tDATA r10\n"
			"\tcmp r10, 0\n"
			"\tje " is-zero-label "\n"

			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\tjmp " zero-end-body-label "\n"

			is-zero-label ":\n"
			"\tmov rax, " (find-label-by-value #t constList) "\n"

			zero-end-body-label ":\n"

			"\tpop rbx\n"						;BU rbx
			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			zero-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " zero-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'zero? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-numerator
	(lambda (fvarList constList)
		(let ((numerator-body-label "numerator_func")
			  (numerator-end-body-label "end_numerator_body")
			  (numerator-is-integer-label "numerator_is_int")
			  (numerator-make-clousure "numerator_make_closure"))
		(string-append 
			"\tjmp " numerator-make-clousure "\n"

			numerator-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10

			"\tmov r10, [rbp + 4 * 8]\n"			;points to args[0], valuve to check
			"\tmov r10, [r10]\n"					;value og args[0]

			"\tmov r11, r10\n"
			"\tTYPE r11\n"
			"\tcmp r11, T_INTEGER\n"
			"\tje " numerator-is-integer-label "\n"

			"\tNUMERATOR r10\n"
			"\tmov rax, r10\n"
			"\tjmp " numerator-end-body-label "\n"

			numerator-is-integer-label ":\n"
				"\tmov rax, qword [rbp + 4*8]\n"

			numerator-end-body-label ":\n"

			"\tl13:pop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			numerator-make-clousure ":\n"
			;"\tmov rcx, [rbp + 2*8]\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " numerator-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'numerator fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-denominator
	(lambda (fvarList constList)
		(let ((denominator-body-label "denominator_func")
			  (end-is-integer-label "end_denominator_is_integer")
			  (is-integer-label "denominator_is_integer")
			  (denominator-make-clousure "denominator_make_closure"))
		(string-append 
			"\tjmp " denominator-make-clousure "\n"

			denominator-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"

			"\tmov rax, [rbp + 4 * 8]\n"			;points to args[0], valuve to check
			"\tmov rax, [rax]\n"					;value og args[0]
			

			"\tmov rbx, rax\n"
			"\tTYPE rbx\n"
			"\tcmp rbx, T_INTEGER\n"
			"\tje " is-integer-label "\n"


			"\tDENOMINATOR rax\n"

			"\tjmp " end-is-integer-label "\n"

			is-integer-label ":\n"

			"\tmymalloc 1\n"
			"\tmov qword [rax], MAKE_LITERAL(T_INTEGER, 1)\n"

			end-is-integer-label ":\n"

			"\tpop rbx\n"

			"\tpop rbp\n"
			"\tret\n"

			denominator-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " denominator-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'denominator fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-eq-pred
	(lambda (fvarList constList)
		(let ((eq-body-label "eq_body_func")
			  (eq-end-body "eq_end_body_func")
			  (doesnt-eq "arentEquals")
			  (eq-make-clousure "make_eq_closure"))
		(string-append 
			"\tjmp " eq-make-clousure "\n"

			eq-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10

			"\tmov rax, [rbp + 4*8]\n"		;args[0]
			"\tmov rbx, [rbp + 5*8]\n"		;args[1]

			"\tcmp rax, rbx\n"
			"\tjne " doesnt-eq "\n"

			"\tmov rax, " (find-label-by-value #t constList) " \n"
			"\tjmp " eq-end-body "\n"
			
			doesnt-eq ":\n"
			"\tmov rax, " (find-label-by-value #f constList) "\n"
			"\t\n"
			 eq-end-body ":\n"

			"\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			eq-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " eq-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'eq? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-cons
	(lambda (fvarList constList)
		(let ((cons-body-label "cons_body_func")
			  (cons-end-body "cons_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (cons-make-clousure "make_cons_closure"))
		(string-append 
			"\tjmp " cons-make-clousure "\n"

			cons-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10
			"\tpush rcx\n"						;BU r10

		    "mov rbx, qword [rbp + 4*8]\n";     rdx holds first argument
		    "mov rcx, qword [rbp + 5*8]\n";     r8 holds second argument
		    
		    ;create new pair

		    "mymalloc 1\n"

		    "\tMAKE_MALLOC_LITERAL_PAIR rax, rbx, rcx\n"
		   
			"\t\n"
			 cons-end-body ":\n"

			 "\tpop rcx\n"						;BU r10
			 "\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			cons-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " cons-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'cons fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-char-to-int
	(lambda (fvarList constList)
		(let ((char-to-int-body-label "char_to_int_body_func")
			  (char-to-int-end-body "char_to_int_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (char-to-int-make-clousure "make_char_to_int_closure"))
		(string-append 
			"\tjmp " char-to-int-make-clousure "\n"

			char-to-int-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10

		    "\tmov rax, qword [rbp + 3*8]\n";     rdx holds first argument
		    "\tcmp rax, 1\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, rax\n"

		    "\tmov rbx, [rax]\n"
		    
		    "\tmov rbx, [rax]\n"
		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_CHAR\n"
		    "\tjne incorrect_input\n"

		    "\tmov rbx, [rax]\n"

		    "\tDATA rbx\n"
		    "\tshl rbx, TYPE_BITS\n"
		    "\tor rbx, T_INTEGER\n"
		    
		    "\tmymalloc 1\n"
		    "\tmov [rax], rbx \n"
		   

			 char-to-int-end-body ":\n"

			"\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			char-to-int-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " char-to-int-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'char->integer fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-int-to-char
	(lambda (fvarList constList)
		(let ((int-to-char-body-label "int_to_char_body_func")
			  (int-to-char-end-body "int_to_char_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (int-to-char-make-clousure "make_int_to_char_closure"))
		(string-append 
			"\tjmp " int-to-char-make-clousure "\n"

			int-to-char-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10

		    "\tmov rax, qword [rbp + 3*8]\n";     rdx holds first argument
		    "\tcmp rax, 1\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, rax\n"

		    "\tmov rbx, [rax]\n"
		    
		    "\tmov rbx, [rax]\n"
		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_INTEGER\n"
		    "\tjne incorrect_input\n"

		    "\tmov rbx, [rax]\n"

		    ;MAKE_LITERAL(T_INTEGER, len)
		    "\tDATA rbx\n"
		    "\tshl rbx, TYPE_BITS\n"
		    "\tor rbx, T_CHAR\n"

		    "\tmymalloc 1\n"
		    "\tmov [rax], rbx \n"
		   

			 int-to-char-end-body ":\n"

			 "\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			int-to-char-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " int-to-char-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'integer->char fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-string-length
	(lambda (fvarList constList)
		(let ((string-length-body-label "string_length_body_func")
			  (string-length-end-body "string_length_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (string-length-make-clousure "make_string_length_closure"))
		(string-append 
			"\tjmp " string-length-make-clousure "\n"

			string-length-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"							;BU rbx

		    "\tmov rax, qword [rbp + 3*8]\n";     rdx holds first argument
		    "\tcmp rax, 1\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, rax\n"

		    "\tmov rbx, [rax]\n"
		    
		    "\tmov rbx, [rax]\n"
		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_STRING\n"
		    "\tjne incorrect_input\n"

		    "\tmov rbx, [rax]\n"

		    "\tSTRING_LENGTH rbx\n"
		    "\t\n"
		    ;((lit << TYPE_BITS) | type)
		    "\tshl rbx, TYPE_BITS\n"
		    "\tadd rbx, T_INTEGER\n"
		    "\tmymalloc 1\n"
		    ;"\tmov rcx, MAKE_LITERAL(T_INTEGER, rbx)\n"
		    "\tmov qword [rax], rbx\n"
		   

			 string-length-end-body ":\n"

			 "\tpop rbx\n"

			"\tpop rbp\n"
			"\tret\n"

			string-length-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " string-length-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'string-length fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-vector-length
	(lambda (fvarList constList)
		(let ((vector-length-body-label "vector_length_body_func")
			  (vector-length-end-body "vector_length_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (vector-length-make-clousure "make_vector_length_closure"))
		(string-append 
			"\tjmp " vector-length-make-clousure "\n"

			vector-length-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"							;BU rbx


		    "\tmov rax, qword [rbp + 4*8]\n"
		    
		    "\tmov rbx, [rax]\n"
		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_VECTOR\n"
		    "\tjne incorrect_input\n"


		    "\tmov rbx, [rax]\n"

		    "\tVECTOR_LENGTH rbx\n"


		    "\tshl rbx, TYPE_BITS\n"
		    "\tadd rbx, T_INTEGER\n"
		    "\tmymalloc 1\n"
		    ;"\tmov rcx, MAKE_LITERAL(T_INTEGER, rbx)\n"
		    "\tmov qword [rax], rbx\n"
		   

			 vector-length-end-body ":\n"

			 "\tpop rbx\n"

			"\tpop rbp\n"
			"\tret\n"

			vector-length-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " vector-length-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'vector-length fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-string-ref
	(lambda (fvarList constList)
		(let ((string-ref-body-label "string_ref_body_func")
			  (string-ref-make-clousure "make_string_ref_closure"))
		(string-append 
			"\tjmp " string-ref-make-clousure "\n"

			string-ref-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"				;BU
			"\tpush rcx\n"				;BU
			"\tpush r10\n"				;BU

			"\tmov rax, qword [rbp + 3*8]\n";     
		    "\tcmp rax, 2\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_STRING\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 5*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_INTEGER\n"
		    "\tjne incorrect_input\n"

		   	"\tmov rbx, qword [rbp + 4*8]\n"
		   	"\tmov rcx, qword [rbp + 5*8]\n"
		   	"\tmov rbx, [rbx]\n"
		   	"\tmov rcx, [rcx]\n"
		   	"\tDATA rcx\n"
		   	"\tmov r10,0\n"
		   	

		   	"\tSTRING_REF r10B, rbx, rcx\n"


		    "\tshl r10, TYPE_BITS\n"
		    "\tor r10, T_CHAR\n"

		    "\tmymalloc 1\n"
		    "\tmov [rax], r10\n"

		    "\tpop r10\n"				;BU
			"\tpop rcx\n"				;BU
			"\tpop rbx\n"				;BU

			"\tpop rbp\n"
			"\tret\n"

			string-ref-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " string-ref-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'string-ref fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-vector-ref
	(lambda (fvarList constList)
		(let ((vector-ref-body-label "vector_ref_body_func")
			  (vector-ref-make-clousure "make_vector_ref_closure"))
		(string-append 
			"\tjmp " vector-ref-make-clousure "\n"

			vector-ref-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"				;BU
			"\tpush rcx\n"				;BU
			"\tpush r10\n"				;BU

			"\tmov rax, qword [rbp + 3*8]\n";     
		    "\tcmp rax, 2\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_VECTOR\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 5*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_INTEGER\n"
		    "\tjne incorrect_input\n"

		   	"\tmov rbx, qword [rbp + 4*8]\n"
		   	"\tmov rcx, qword [rbp + 5*8]\n"
		   	"\tmov rbx, [rbx]\n"
		   	"\tmov rcx, [rcx]\n"
		   	"\tDATA rcx\n"
		   	"\tmov r10,0\n"
		   	

		   	"\tVECTOR_REF r10, rbx, rcx\n"


		    "\tmymalloc 1\n"
		    "\tmov [rax], r10\n"

		    "\tpop r10\n"				;BU
			"\tpop rcx\n"				;BU
			"\tpop rbx\n"				;BU

			"\tpop rbp\n"
			"\tret\n"

			vector-ref-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " vector-ref-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'vector-ref fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-small-than
	(lambda (fvarList constList)
		(let ((small-than-body-label "small_than_func")
			  (small-than-end-loop-label "small_than_end_loop")
			  (small-than-loop-label "small_than_loop")
			  (small-than-make-clousure "make_small_than_pred_closure")
			  (small-than-equals-type "small_than_eq_types")
			  (small-than-two-int "small_than_two_int")
			  (small-than-one-frac "small_than_one_frac")
			  (small-than-one-frac2 "small_than_one_frac2")
			  (small-than-two-frac "small_than_two_frac"))
		(string-append 
			"\tjmp " plus-make-clousure "\n"

			small-than-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush r10\n"						;BU r10
			"\tpush rbx\n"						;BU r10
			"\tpush rcx\n"						;BU r10
			"\tpush rdx\n"						;BU r10
			"\tpush rdi\n"						;BU r10

			"\tmov r10, [rbp + 3* 8]\n"		;arg_count
			"\tcmp r10, 2\n"
			"\tjl  incorrect_input\n"

			"\tmov rbx, [rbp + 4*8]\n"			;first arg
			"\tTYPE rbx\n"
			"\tmov rcx, [rbp + 5*8]\n"			;second arg
			"\tTYPE rcx\n"
			"\tcmp rbx, rcx\n"
			"\tje " small-than-equals-type "\n"	

			;one frac & one int
			"\tmov rbx, [rbp + 4*8]\n"			;first arg
			"\tTYPE rbx\n"
			"\tcmp rbx, T_FRACTION\n"			


			"\tmov rbx, [rbp + 4*8]\n"			;rbx = INT
			"\tmov rcx, [rbp + 5*8]\n"			;rcx = frac
			"\tjmp " small-than-one-frac2 "\n"

			small-than-one-frac ":\n"


			small-than-equals-type ":\n"				
			
			"\tmov rbx, rcx\n"				;acc, at first cotains first arg
			"\tmov rdx, rbp\n"	
			"\tadd rdx, 32\n"				;offset to get args

			small-than-loop-label ":\n"
			"\tcmp rdi, r10\n"
			"\tjge " plus-end-loop-label "\n"

			"\tmov rcx, [rdx + rdi*8]\n"
			"\tmov rcx, [rcx]\n"
			"\tDATA rcx\n"
			"\tadd rbx, rcx\n"
			"\tinc rdi\n"
			"\tjmp " small-than-loop-label "\n"



			small-than-end-loop-label ":\n"
			
			"\tshl rbx, TYPE_BITS\n"
			"\tor rbx, T_INTEGER\n"
			

			"\tmymalloc 1\n"
			"\tmov [rax], rbx\n"

			"\tpop rdi\n"						;BU r10
			"\tpop rdx\n"						;BU r10
			"\tpop rcx\n"						;BU r10
			"\tpop rbx\n"						;BU r10
			"\tpop r10\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			small-than-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " small-than-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '< fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-remainder
	(lambda (fvarList constList)
		(let ((remainder-body-label "remainder_body_func")
			  (remainder-end-body-label "remainder_end_body_func")
			  (remainder-make-clousure "make_remainder_closure")
			  (remainder-sec-arg-is-zero "remainder_sec_arg_zero"))
		(string-append 
			"\tjmp " remainder-make-clousure "\n"

			remainder-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"				;BU
			"\tpush rcx\n"				;BU
			"\tpush r10\n"				;BU

			"\tmov rax, qword [rbp + 3*8]\n";     
		    "\tcmp rax, 2\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 4*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_INTEGER\n"
		    "\tjne incorrect_input\n"

		    "\tmov rax, qword [rbp + 5*8]\n"
		    "\tmov rbx, [rax]\n"

		    "\tTYPE rbx\n"
		    "\tcmp rbx, T_INTEGER\n"
		    "\tjne incorrect_input\n"

		   	"\tmov rax, qword [rbp + 4*8]\n"
		   	"\tmov rbx, qword [rbp + 5*8]\n"
		   	"\tmov rax, [rax]\n"				;first arg
		   	"\tmov rbx, [rbx]\n"				;second arg



		   	;"\tsmov rdx, 0\n"
		   	;"\tDATA rax\n"
		   	;"\tcmp rax, 0\n"
		   	;"\tje " remainder-end-body-label "\n"

		   	"\tDATA rax\n"
		   	"\tDATA rbx\n"
		   	"\tmov rdx, 0\n"
		   	"\tCQO\n"
		   	"\tidiv rbx\n"

		   	;"\tmov rax, rdx\n"
		   	"\tshl rdx, TYPE_BITS\n"
		   	"\tor rdx, T_INTEGER\n"
		   	"\tjmp " remainder-end-body-label "\n"
		   	
		   	;"\tbackup_registers\n"



		    remainder-end-body-label ":\n"

		    "\tmymalloc 1\n"
		    "\tmov [rax], rdx\n"
		    "\t\n"

		    "\tpop r10\n"				;BU
			"\tpop rcx\n"				;BU
			"\tpop rbx\n"				;BU

			"\tpop rbp\n"
			"\tret\n"

			remainder-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " remainder-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'remainder fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-plus
	(lambda (fvarList constList)
		(let ((plus-body-label "plus_body_func")
			  (plus-loop-label "plus_loop_label")
			  (plus-end-loop-label "plus_end_loop_label")
			  (plus-two-fractions "plus_two_fractions")
			  (plus-make-clousure "make_plus_closure")
			  (plus-the-arg-is-not-frac "plus_arg_is_not_frac")
			  (plus-the-arg-is-frac "plus_arg_is_frac")
			  (plus-ret-int "plus_int_ret")
			  (plus-exit "plus_exit")
			  (plus-numinator-is-neg "plus_numi_is_neg")
			  (plus-denominator-is-neg "plus_denomi_is_neg")
			  (plus-start-gcd "plus_start_gcd")
			  (plus-end-gcd "plus_end_gcd")
			  (plus-no-args "plus_no_args")
			  )
		(string-append 
			"\tjmp " plus-make-clousure "\n"

			plus-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tbackup_registers\n"

			"\tmov rdi, qword [rbp + 3*8]\n";     
		    "\tcmp rdi, 0\n"
		    "\tjl incorrect_input\n"

		    "\tmov rdi, qword [rbp + 3*8]\n";     
		    "\tcmp rdi, 0\n"
		    "\tje " plus-no-args "\n"

		    "\tmov r10, 0\n"			;init numenator
		    "\tmov r11, 1\n"			;init denumintor

		    plus-loop-label ":\n"
		    	"\tcmp rdi, 0\n"
		    	"\tje " plus-end-loop-label "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " plus-the-arg-is-frac "\n"


		    	;MAKE FRACTION AND SEND TO PLUS
		    	plus-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " plus-two-fractions "\n"


		    	plus-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!
		    	;"\tmov rsi, r14\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	;"\tmov rsi, r15\n"
		    	

		    plus-two-fractions ":\n"

		    	"\tmov rax, r15\n"
		    	"\tmul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r11\n"
		    	"\tmul r14\n"					;r14 contains common left numinator
		    	"\tmov r14, rax\n"

		    	"\tmov rax, r15\n"
		    	"\tmul r11\n"					;r11 contains common denominator
		    	"\tmov r11, rax\n"

		    	"\tadd r10, r14\n"
		    	;HERE-> r10 contain numinator, r11 contain denominator AFTER PLUS!


		    	"\tdec rdi\n"
		    	"\tjmp " plus-loop-label "\n"


		    plus-no-args ":\n"
		    	"\tmov r10, 0\n"
		    	"\tmov r11, 1\n"
		    	"\tjmp " plus-end-gcd "\n"


		    plus-end-loop-label ":\n"	
		    	;r10 contains numnerator
		    	;r11 contains demomirator

		    	"\tmov r14, r10\n"			;now r14,15 are helpers to check negatives valuse for r10,11
		    	"\tmov r15, r11\n"
		    	"\tmov r13, 0\n"				;r13=0-> both positives, r13=1->first is neg, r13=2 both negatives

		    	"\tcmp r14, 0\n"
				"\tjl " plus-numinator-is-neg "\n"

				"\tcmp r15, 0\n"
				"\tjl " plus-denominator-is-neg "\n"
			
				"\tjmp " plus-start-gcd "\n"

				plus-numinator-is-neg ":\n"
					"\tneg r14\n"
					"\tor r13, 1\n"
					"\tcmp r15, 0\n"
					"\tjge " plus-start-gcd "\n"

				plus-denominator-is-neg ":\n"
					"\tneg r15\n"
					"\tor r13, 2\n"


			plus-start-gcd ":\n"

				"\tmov r10, r14\n"		;abs r10
				"\tmov r11, r15\n"		;abs r11

		    	"\tGCD r10,r11\n"			;result in rax

		    	"\tmov rbx, rdi\n"		;BU- rbx = gcd
		    	"\tmov rax, r11\n"
		    	"\tCQO\n"

		    	"\tdiv rbx\n"
		    	"\tmov r11, rax\n"

		    	"\tCQO\n"

		    	"\tmov rax, r10\n"
		    	"\tdiv rbx\n"

		    	"\tmov r10, rax\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " plus-end-gcd "\n"

		    	"\tcmp r13,3\n"
		    	"\tje " plus-end-gcd  "\n"

		    	;one of them(denimo, nomi) is neg
		    	"\tneg r10\n"

		    	plus-end-gcd ":\n"
			    	"\tcmp r11, 1\n"
			    	"\tje " plus-ret-int "\n"


		   		"\tmymalloc 1\n"
		   		"\tmov rbx, rax\n"
		   		"\tshl r10, TYPE_BITS\n"
		   		"\tor r10, T_INTEGER\n"
		   		"\tmov [rbx], r10\n"

		   		"\tmymalloc 1\n"
		   		"\tmov rcx, rax\n"
		   		"\tshl r11, TYPE_BITS\n"
		   		"\tor r11, T_INTEGER\n"
		   		"\tmov [rcx], r11\n"

		   		"\tmymalloc 1\n"
		   		"\tMAKE_MALLOC_LITERAL_FRACTION rax, rbx, rcx\n"

		   		"\tjmp " plus-exit "\n"

		   		plus-ret-int ":\n"

		   			"\tmymalloc 1\n"
		   			"\tshl r10, TYPE_BITS\n"
		   			"\tor r10, T_INTEGER\n"
		   			"\tmov [rax], r10\n"

		   		plus-exit ":\n"

		   		"\trestore_registers\n"

			"\tpop rbp\n"
			"\tret\n"

			plus-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " plus-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '+ fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-minus
	(lambda (fvarList constList)
		(let ((minus-body-label "minus_body_func")
			  (minus-loop-label "minus_loop_label")
			  (minus-end-loop-label "minus_end_loop_label")
			  (minus-two-fractions "minus_two_fractions")
			  (minus-make-clousure "make_minus_closure")
			  (minus-the-arg-is-not-frac "minus_arg_is_not_frac")
			  (minus-the-arg-is-frac "minus_arg_is_frac")
			  (minus-ret-int "minus_int_ret")
			  (minus-exit "minus_exit")
			  (minus-end-gcd "minus_end_gcd")
			  (minus-numinator-is-neg "minus_numi_is_neg")
			  (minus-denominator-is-neg "minus_denomi_is_neg")
			  (minus-start-gcd "minus_start_gcding")
			  (minus-first-arg-is-fraction "minus_last_arg_is_fraction")
			  (minus-first-arg-is-zero "minus_last_arg_is_zero")
			  (minus-before-loop "minus_before_loop")
			  ;(div-upSide-single-number "div_upSide")
			  (minus-single-first-arg-is-fraction "minus_single_arg_is_frac")
			  (minus-upSide-single-number "minus_single_arg_only")
			  )
		(string-append 
			"\tjmp " minus-make-clousure "\n"

			minus-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tbackup_registers\n"

			"\tmov rsi, qword [rbp + 3*8]\n";     

		    ;************************
		    "\tcmp rsi, 1\n"			;should be upside
		    "\tje " minus-upSide-single-number "\n"
		    ;************************

		    "\tmov rdi, 1\n"
		    ;at-least two args
		    "\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    "\tmov r13, [r12]\n"							;r13 = curr arg
		    "\tTYPE r13\n"
		    "\tcmp r13, T_FRACTION\n"
		    "\tje " minus-first-arg-is-fraction "\n"

		    ;first is int
			    "\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
			    "\tmov r13, [r12]\n"							;r13 = curr arg
			    "\tDATA r13\n"
			    
			    "\tcmp r13, 0\n"
			    "\tje " minus-first-arg-is-zero "\n"

			    "\tmov r10, r13\n"
			    "\tmov r11, 1\n"
			    "\tjmp " minus-before-loop "\n"

			    minus-first-arg-is-zero ":\n"
			    	"\tmov r10, 0\n"			;init numenator
		    		"\tmov r11, 1\n"			;init denumintor
		    		"\tjmp " minus-end-gcd "\n"


		    minus-first-arg-is-fraction ":\n"
		    	"\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		 		"\tcmp r14, 0\n"
		 		"\tje " minus-first-arg-is-zero "\n"

		    	"\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!

		    	"\tmov r10, r14\n"
		    	"\tmov r11, r15\n"
		    	"\tjmp " minus-before-loop "\n"

		    minus-upSide-single-number ":\n"
		    	"\tmov r12, qword [rbp + 4*8]\n"		;r12 = point to first arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		   	 	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " minus-single-first-arg-is-fraction "\n"

		    	;single-first-arg is int
		    	"\tmov r12, qword [rbp + 4*8]\n"		;r12 = point to first arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tDATA r13\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " minus-first-arg-is-zero "\n"

		    	"\tmov r10, r13\n"
		    	"\tneg r10\n"
		    	"\tmov r11, 1\n"
		    	"\tjmp " minus-end-gcd "\n"
		    	"\t\n"

		    	minus-single-first-arg-is-fraction ":\n"

		    		"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
			    	"\tmov r14, [r12]\n"					;r13 = curr arg
			    	"\tDATA_UPPER r14\n"
			    	"\tadd r14, start_of_data\n"
			    	"\tmov r14, [r14]\n"
			    	"\tDATA r14\n"							;r14 contain numenator!!

			    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
			    	"\tmov r15, [r12]\n"					;r13 = curr arg
			    	"\tDATA_LOWER r15\n"
			    	"\tadd r15, start_of_data\n"
			    	"\tmov r15, [r15]\n"
			    	"\tDATA r15\n"							;r15 contain dinumenator!

			    	"\tcmp r14, 0\n"
			    	"\tje " minus-first-arg-is-zero "\n"

			    	"\tmov r10, r14\n"
			    	"\tneg r10\n"
			    	"\tmov r11, r15\n"

			    	"\tjmp " minus-end-loop-label "\n"
			    	"\t\n"

		  minus-before-loop ":\n"
		  	"\tinc rdi\n"

		    minus-loop-label ":\n"
		    	"\tcmp rdi, rsi\n"
		    	"\tjg " minus-end-loop-label "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " minus-the-arg-is-frac "\n"


		    	;MAKE FRACTION AND SEND TO PLUS
		    	minus-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " minus-two-fractions "\n"


		    	minus-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!


		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	
		    	
		    minus-two-fractions ":\n"


		    	"\tmov rax, r15\n"
		    	"\timul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r11\n"
		    	"\timul r14\n"					;r10 contains common right numinator
		    	"\tmov r14, rax\n"

		    	"\tmov rax, r15\n"
		    	"\timul r11\n"					;r14 contains common left numinator
		    	"\tmov r11, rax\n"

		    	"\tsub r10, r14\n"

		    	"\tinc rdi\n"
		    	"\tjmp " minus-loop-label "\n"



		    minus-end-loop-label ":\n"	
		    	;r10 contains numnerator
		    	;r11 contains demomirator

		    	"\tcmp r10, 1\n"
		    	"\tje " minus-end-gcd "\n"

		    	"\tmov r14, r10\n"				;now r14,15 are helpers to check negatives valuse for r10,11
		    	"\tmov r15, r11\n"
		    	"\tmov r13, 0\n"				;r13=0-> both positives, r13=1->first is neg, r13=2 both negatives

		    	"\tcmp r14, 0\n"
				"\tjl " minus-numinator-is-neg "\n"

				"\tcmp r15, 0\n"
				"\tjl " minus-denominator-is-neg "\n"
			
				"\tjmp " minus-start-gcd "\n"

				minus-numinator-is-neg ":\n"
					"\tneg r14\n"
					"\tor r13, 1\n"
					"\tl25:cmp r15, 0\n"
					"\tjge " minus-start-gcd "\n"

				minus-denominator-is-neg ":\n"
					"\tneg r15\n"
					"\tor r13, 2\n"


				minus-start-gcd ":\n"

				"\tmov r10, r14\n"		;abs r10
				"\tmov r11, r15\n"		;abs r11

		    	"\tGCD r10,r11\n"			;result in rax



		    	"\tmov rbx, rdi\n"		;BU- rbx = gcd
		    	"\tCQO\n"

		    	"\tmov rax, r11\n"
		    	"\tidiv rbx\n"
		    	"\tmov r11, rax\n"

		    	"\tCQO\n"
		    	"\tmov rax, r10\n"
		    	"\tidiv rbx\n"

		    	"\tmov r10, rax\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " minus-end-gcd "\n"

		    	"\tcmp r13,3\n"
		    	"\tje " minus-end-gcd  "\n"

		    	;one of them(denimo, nomi) is neg
		    	"\tneg r10\n"

		    	minus-end-gcd ":\n"
			    	"\tcmp r11, 1\n"
			    	"\tje " minus-ret-int "\n"


		   		"\tmymalloc 1\n"
		   		"\tmov rbx, rax\n"
		   		"\tshl r10, TYPE_BITS\n"
		   		"\tor r10, T_INTEGER\n"
		   		"\tmov [rbx], r10\n"

		   		"\tmymalloc 1\n"
		   		"\tmov rcx, rax\n"
		   		"\tshl r11, TYPE_BITS\n"
		   		"\tor r11, T_INTEGER\n"
		   		"\tmov [rcx], r11\n"

		   		"\tmymalloc 1\n"
		   		"\tMAKE_MALLOC_LITERAL_FRACTION rax, rbx, rcx\n"

		   		"\tjmp " minus-exit "\n"

		   		minus-ret-int ":\n"

		   			"\tmymalloc 1\n"
		   			"\tshl r10, TYPE_BITS\n"
		   			"\tor r10, T_INTEGER\n"
		   			"\tmov [rax], r10\n"

		   		minus-exit ":\n"

		   		"\trestore_registers\n"

			"\tpop rbp\n"
			"\tret\n"

			minus-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " minus-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '- fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-multiply
	(lambda (fvarList constList)
		(let ((multiply-body-label "multiply_body_func")
			  (multiply-loop-label "multiply_loop_label")
			  (multiply-end-loop-label "multiply_end_loop_label")
			  (multiply-two-fractions "multiply_two_fractions")
			  (multiply-make-clousure "make_multiply_closure")
			  (multiply-the-arg-is-not-frac "multiply_arg_is_not_frac")
			  (multiply-the-arg-is-frac "multiply_arg_is_frac")
			  (multiply-ret-int "multiply_int_ret")
			  (multiply-exit "multiply_exit")
			  (multiply-end-gcd "multiply_end_gcd")
			  (multiplpy-numinator-is-neg "multiplpy_numi_is_neg")
			  (multiplpy-denominator-is-neg "multiplpy_denomi_is_neg")
			  (multiplpy-start-gcd "multiplpy_start_gcding")
			  (mul-no-args "mul_no_args"))
		(string-append 
			"\tjmp " multiply-make-clousure "\n"

			multiply-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tbackup_registers\n"

			"\tmov rdi, qword [rbp + 3*8]\n";     
		    "\tcmp rdi, 0\n"
		    "\tjl incorrect_input\n"

		    "\tmov rdi, qword [rbp + 3*8]\n";     
		    "\tcmp rdi, 0\n"
		    "\tje " mul-no-args "\n"

		    "\tmov r10, 1\n"			;init numenator
		    "\tmov r11, 1\n"			;init denumintor

		    multiply-loop-label ":\n"
		    	"\tcmp rdi, 0\n"
		    	"\tje " multiply-end-loop-label "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " multiply-the-arg-is-frac "\n"


		    	;MAKE FRACTION AND SEND TO PLUS
		    	multiply-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " multiply-two-fractions "\n"


		    	multiply-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!
		    	;"\tmov rsi, r14\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	
		    	;"\tmov rsi, r15\n"
		    	

		    multiply-two-fractions ":\n"

		    	"\tmov rax, r14\n"
		    	"\tmul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"
		    	;"\tmov rsi, r10\n"

		    	"\tmov rax, r15\n"
		    	"\tmul r11\n"					;r14 contains common left numinator
		    	"\tmov r11, rax\n"


		    	"\tdec rdi\n"
		    	"\tjmp " multiply-loop-label "\n"

		    mul-no-args ":\n"
		    	"\tmov r10, 1\n"
		    	"\tmov r11, 1\n"
		    	"\tjmp " multiply-end-gcd "\n"

		    multiply-end-loop-label ":\n"	
		    	;r10 contains numnerator
		    	;r11 contains demomirator

		    	"\tmov r14, r10\n"			;now r14,15 are helpers to check negatives valuse for r10,11
		    	"\tmov r15, r11\n"
		    	"\tmov r13, 0\n"				;r13=0-> both positives, r13=1->first is neg, r13=2 both negatives

		    	"\tcmp r14, 0\n"
				"\tjl " multiplpy-numinator-is-neg "\n"

				"\tcmp r15, 0\n"
				"\tjl " multiplpy-denominator-is-neg "\n"
			
				"\tjmp " multiplpy-start-gcd "\n"

				multiplpy-numinator-is-neg ":\n"
					"\tneg r14\n"
					"\tor r13, 1\n"
					"\tcmp r15, 0\n"
					"\tjge " multiplpy-start-gcd "\n"

				multiplpy-denominator-is-neg ":\n"
					"\tneg r15\n"
					"\tor r13, 2\n"


				multiplpy-start-gcd ":\n"

				"\tmov r10, r14\n"		;abs r10
				"\tmov r11, r15\n"		;abs r11

		    	"\tGCD r10,r11\n"			;result in rax

		    	"\tmov rbx, rdi\n"		;BU- rbx = gcd
		    	"\tCQO\n"

		    	"\tmov rax, r11\n"
		    	"\tdiv rbx\n"
		    	"\tmov r11, rax\n"

		    	"\tCQO\n"

		    	"\tmov rax, r10\n"
		    	"\tdiv rbx\n"

		    	"\tmov r10, rax\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " multiply-end-gcd "\n"

		    	"\tcmp r13,3\n"
		    	"\tje " multiply-end-gcd  "\n"

		    	;one of them(denimo, nomi) is neg
		    	"\tneg r10\n"

		    	multiply-end-gcd ":\n"
			    	"\tcmp r11, 1\n"
			    	"\tje " multiply-ret-int "\n"


		   		"\tmymalloc 1\n"
		   		"\tmov rbx, rax\n"
		   		"\tshl r10, TYPE_BITS\n"
		   		"\tor r10, T_INTEGER\n"
		   		"\tmov [rbx], r10\n"

		   		"\tmymalloc 1\n"
		   		"\tmov rcx, rax\n"
		   		"\tshl r11, TYPE_BITS\n"
		   		"\tor r11, T_INTEGER\n"
		   		"\tmov [rcx], r11\n"

		   		"\tmymalloc 1\n"
		   		"\tMAKE_MALLOC_LITERAL_FRACTION rax, rbx, rcx\n"

		   		"\tjmp " multiply-exit "\n"

		   		multiply-ret-int ":\n"

		   			"\tmymalloc 1\n"
		   			"\tshl r10, TYPE_BITS\n"
		   			"\tor r10, T_INTEGER\n"
		   			"\tmov [rax], r10\n"

		   		multiply-exit ":\n"

		   		"\trestore_registers\n"

			"\tpop rbp\n"
			"\tret\n"

			multiply-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " multiply-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '* fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-div
	(lambda (fvarList constList)
		(let ((div-body-label "div_body_func")
			  (div-loop-label "div_loop_label")
			  (div-end-loop-label "div_end_loop_label")
			  (div-two-fractions "div_two_fractions")
			  (div-make-clousure "make_div_closure")
			  (div-the-arg-is-not-frac "div_arg_is_not_frac")
			  (div-the-arg-is-frac "div_arg_is_frac")
			  (div-ret-int "div_int_ret")
			  (div-exit "div_exit")
			  (div-end-gcd "div_end_gcd")
			  (div-numinator-is-neg "div_numi_is_neg")
			  (div-denominator-is-neg "div_denomi_is_neg")
			  (div-start-gcd "div_start_gcding")
			  (div-first-arg-is-fraction "div_last_arg_is_fraction")
			  (div-first-arg-is-zero "div_last_arg_is_zero")
			  (div-before-loop "div_before_loop")
			  ;(div-upSide-single-number "div_upSide")
			  (div-single-first-arg-is-fraction "div_single_arg_is_frac")
			  (div-upSide-single-number "div_single_arg_only")
			  (div-is-not-neg "div_is_not_neg")
			  )
		(string-append 
			"\tjmp " div-make-clousure "\n"

			div-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tbackup_registers\n"

			"\tmov rsi, qword [rbp + 3*8]\n";     

		    ;************************
		    "\tcmp rsi, 1\n"			;should be upside
		    "\tje " div-upSide-single-number "\n"
		    ;************************

		    "\tmov rdi, 1\n"
		    ;at-least two args
		    "\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    "\tmov r13, [r12]\n"							;r13 = curr arg
		    "\tTYPE r13\n"
		    "\tcmp r13, T_FRACTION\n"
		    "\tje " div-first-arg-is-fraction "\n"

		    ;first is int
			    "\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
			    "\tmov r13, [r12]\n"							;r13 = curr arg
			    "\tDATA r13\n"
			    
			    "\tcmp r13, 0\n"
			    "\tje " div-first-arg-is-zero "\n"

			    "\tmov r10, r13\n"
			    "\tmov r11, 1\n"
			    "\tjmp " div-before-loop "\n"

			    div-first-arg-is-zero ":\n"
			    	"\tmov r10, 0\n"			;init numenator
		    		"\tmov r11, 1\n"			;init denumintor
		    		"\tjmp " div-end-gcd "\n"


		    div-first-arg-is-fraction ":\n"
		    	"\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		 		"\tcmp r14, 0\n"
		 		"\tje " div-first-arg-is-zero "\n"

		    	"\tmov r12, qword [rbp + (3 + rdi) * 8]\n"		;r12 = point to first arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!

		    	"\tmov r10, r14\n"
		    	"\tmov r11, r15\n"
		    	"\tjmp " div-before-loop "\n"

		    div-upSide-single-number ":\n"
		    	"\tmov r12, qword [rbp + 4*8]\n"		;r12 = point to first arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		   	 	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " div-single-first-arg-is-fraction "\n"

		    	;single-first-arg is int
		    	"\tmov r12, qword [rbp + 4*8]\n"		;r12 = point to first arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tDATA r13\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " div-first-arg-is-zero "\n"

		    	"\tmov r11, r13\n"
		    	"\tmov r10, 1\n"
		    	"\tjmp " div-end-loop-label "\n"
		    	"\t\n"

		    	div-single-first-arg-is-fraction ":\n"

		    		"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
			    	"\tmov r14, [r12]\n"					;r13 = curr arg
			    	"\tDATA_UPPER r14\n"
			    	"\tadd r14, start_of_data\n"
			    	"\tmov r14, [r14]\n"
			    	"\tDATA r14\n"							;r14 contain numenator!!

			    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
			    	"\tmov r15, [r12]\n"					;r13 = curr arg
			    	"\tDATA_LOWER r15\n"
			    	"\tadd r15, start_of_data\n"
			    	"\tmov r15, [r15]\n"
			    	"\tDATA r15\n"							;r15 contain dinumenator!

			    	"\tcmp r14, 0\n"
			    	"\tje " div-first-arg-is-zero "\n"

			    	"\tmov r10, r15\n"
			    	"\tmov r11, r14\n"

			    	"\tjmp " div-end-loop-label "\n"
			    	"\t\n"

		  div-before-loop ":\n"
		  	"\tinc rdi\n"

		    div-loop-label ":\n"
		    	"\tcmp rdi, rsi\n"
		    	"\tjg " div-end-loop-label "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " div-the-arg-is-frac "\n"


		    	;MAKE FRACTION AND SEND TO PLUS
		    	div-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " div-two-fractions "\n"


		    	div-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!


		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	
		    	
		    div-two-fractions ":\n"

		    	"\txchg r14,r15\n"						;KEFEL BA OFHI!

		    	"\tmov rax, r14\n"
		    	"\timul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r15\n"
		    	"\timul r11\n"					;r14 contains common left numinator
		    	"\tmov r11, rax\n"


		    	"\tinc rdi\n"
		    	"\tjmp " div-loop-label "\n"



		    div-end-loop-label ":\n"	
		    	;r10 contains numnerator
		    	;r11 contains demomirator



		    	"\tmov r14, r10\n"				;now r14,15 are helpers to check negatives valuse for r10,11
		    	"\tmov r15, r11\n"
		    	"\tmov r13, 0\n"				;r13=0-> both positives, r13=1->first is neg, r13=2 both negatives

		    	"\tcmp r14, 0\n"
				"\tjl " div-numinator-is-neg "\n"

				"\tcmp r15, 0\n"
				"\tjl " div-denominator-is-neg "\n"
			
				"\tjmp " div-start-gcd "\n"

				div-numinator-is-neg ":\n"
					"\tneg r14\n"
					"\tor r13, 1\n"
					"\tcmp r15, 0\n"
					"\tjge " div-start-gcd "\n"

				div-denominator-is-neg ":\n"
					"\tneg r15\n"
					"\tor r13, 2\n"

				"\tmov r10, r14\n"		;abs r10
				"\tmov r11, r15\n"		;abs r11

				"\tcmp r10, 1\n"
		    	"\tje check_neg1\n"	


				div-start-gcd ":\n"

				"\tmov r10, r14\n"		;abs r10
				"\tmov r11, r15\n"		;abs r11

		    	"\tGCD r10,r11\n"			;result in rax

		    	"\tmov rbx, rdi\n"		;BU- rbx = gcd


		    	"\tmov rax, r11\n"
		    	"\tmov rdx, 0\n"
		    	"\tCQO\n"
		    	"\tidiv rbx\n"
		    	"\tmov r11, rax\n"

		    	"\tmov rax, r10\n"
		    	"\tmov rdx, 0\n"
		    	"\tCQO\n"
		    	"\tidiv rbx\n"

		    	"\tmov r10, rax\n"

		    	"check_neg1:\n"

		    	"\tcmp r13, 0\n"
		    	"\tje " div-end-gcd "\n"

		    	"\tcmp r13,3\n"
		    	"\tje " div-end-gcd  "\n"

		    	;one of them(denimo, nomi) is neg
		    	"\tneg r10\n"



		    	div-end-gcd ":\n"
			    	"\tcmp r11, 1\n"
			    	"\tje " div-ret-int "\n"



		   		"\tmymalloc 1\n"
		   		"\tmov rbx, rax\n"
		   		"\tshl r10, TYPE_BITS\n"
		   		"\tor r10, T_INTEGER\n"
		   		"\tmov [rbx], r10\n"

		   		"\tmymalloc 1\n"
		   		"\tmov rcx, rax\n"
		   		"\tshl r11, TYPE_BITS\n"
		   		"\tor r11, T_INTEGER\n"
		   		"\tmov [rcx], r11\n"

		   		"\tmymalloc 1\n"
		   		"\tMAKE_MALLOC_LITERAL_FRACTION rax, rbx, rcx\n"

		   		"\tjmp " div-exit "\n"

		   		div-ret-int ":\n"

		   			"\tmymalloc 1\n"
		   			"\tshl r10, TYPE_BITS\n"
		   			"\tor r10, T_INTEGER\n"
		   			"\tmov [rax], r10\n"

		   		div-exit ":\n"

		   		"\trestore_registers\n"

			"\tpop rbp\n"
			"\tret\n"

			div-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " div-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '/ fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-small-than
	(lambda (fvarList constList)
		(let ((small-than-body-label "small_than_body_func")
			  (small-than-loop-label "small_than_loop_label")
			  (small-than-end-loop-label "small_than_end_loop_label")
			  (small-than-two-fractions "small_than_two_fractions")
			  (small-than-make-clousure "make_small_than_closure")
			  (small-than-the-arg-is-not-frac "small_than_arg_is_not_frac")
			  (small-than-the-arg-is-frac "small_than_arg_is_frac")
			  (small-than-ret-int "small_than_int_ret")
			  (small-than-exit "small_than_exit")
			  (small-than-numinator-is-neg "small_than_numi_is_neg")
			  (small-than-denominator-is-neg "small_than_denomi_is_neg")
			  (small-than-start-gcd "small_than_start_gcd")
			  (small-than-end-gcd "small_than_end_gcd")
			  (small-than-ret-true "small_than_ret_true")
			  (small-than-ret-false "small_than_ret_false")
			  (small-than-first-arg-is-frac "small_than_first_arg_is_frac")
			  (small-than-first-arg-handled "small_than_first_arg_handled"))
		(string-append 
			"\tjmp " small-than-make-clousure "\n"

			small-than-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


			"\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 0\n"
		    "\tjle incorrect_input\n"

		    "\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 1\n"
		    "\tje " small-than-ret-true "\n"


		    "\tmov r12, qword [rbp + 32]\n"			;r12 = first arg
		    "\tmov r13, [r12]\n"					;r13 = curr arg
		    "\tTYPE r13\n"
		    "\tcmp r13, T_FRACTION\n"
		    "\tje " small-than-first-arg-is-frac "\n"

		    ;FIRST ARG IS INT
	    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    "\tmov r12, [r12]\n"
		    "\tDATA r12\n"
		    "\tmov r14, r12\n"
		    "\tmov r15, 1\n"
		    "\tjmp " small-than-first-arg-handled "\n"


		    small-than-first-arg-is-frac ":\n"
		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	

		    small-than-first-arg-handled ":\n"

		    	"\tmov r10, r14\n"			;init numenator
		    	"\tmov r11, r15\n"			;init denumintor
		    	"\tmov rdi,2\n"

		    small-than-loop-label ":\n"
		    	"\tcmp rdi, rsi\n"
		    	"\tjg " small-than-ret-true "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " small-than-the-arg-is-frac "\n"


		    	;MAKE INT TO FRACTION AND SEND TO PLUS
		    	small-than-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " small-than-two-fractions "\n"


		    	small-than-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	

		    small-than-two-fractions ":\n"

		    	"\tmov r8, r14\n"				;BU
		    	"\tmov r9, r15\n"				;BU

		    	"\tmov rax, r15\n"
		    	"\tmul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r11\n"
		    	"\tmul r14\n"					;r14 contains common left numinator
		    	"\tmov r14, rax\n"

		    	"\tcmp r10, r14\n"
		    	"\tjge " small-than-ret-false "\n"

		    	"\tmov r10, r8\n"
		    	"\tmov r11, r9\n"


		    	"\tinc rdi\n"
		    	"\tjmp " small-than-loop-label "\n"


		    small-than-ret-true ":\n"
		    	"\tmov rax, " (find-label-by-value #t constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " small-than-exit "\n"

		    small-than-ret-false ":\n"
		    	"\tmov rax, " (find-label-by-value #f constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " small-than-exit "\n"


		   		small-than-exit ":\n"

			"\tpop rbp\n"
			"\tret\n"

			small-than-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " small-than-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '< fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-greater-than
	(lambda (fvarList constList)
		(let ((greater-than-body-label "greater_than_body_func")
			  (greater-than-loop-label "greater_than_loop_label")
			  (greater-than-end-loop-label "greater_than_end_loop_label")
			  (greater-than-two-fractions "greater_than_two_fractions")
			  (greater-than-make-clousure "make_greater_than_closure")
			  (greater-than-the-arg-is-not-frac "greater_than_arg_is_not_frac")
			  (greater-than-the-arg-is-frac "greater_than_arg_is_frac")
			  (greater-than-ret-int "greater_than_int_ret")
			  (greater-than-exit "greater_than_exit")
			  (greater-than-numinator-is-neg "greater_than_numi_is_neg")
			  (greater-than-denominator-is-neg "greater_than_denomi_is_neg")
			  ;(greater-than-start-gcd "small_thagreaterrt_gcd")
			  (greater-than-end-gcd "greater_than_end_gcd")
			  (greater-than-ret-true "greater_than_ret_true")
			  (greater-than-ret-false "greater_than_ret_false")
			  (greater-than-first-arg-is-frac "greater_than_first_arg_is_frac")
			  (greater-than-first-arg-handled "greater_than_first_arg_handled"))
		(string-append 
			"\tjmp " greater-than-make-clousure "\n"

			greater-than-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


			"\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 0\n"
		    "\tjle incorrect_input\n"

		    "\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 1\n"
		    "\tje " greater-than-ret-true "\n"


		    "\tmov r12, qword [rbp + 32]\n"			;r12 = first arg
		    "\tmov r13, [r12]\n"					;r13 = curr arg
		    "\tTYPE r13\n"
		    "\tcmp r13, T_FRACTION\n"
		    "\tje " greater-than-first-arg-is-frac "\n"

		    ;FIRST ARG IS INT
	    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    "\tmov r12, [r12]\n"
		    "\tDATA r12\n"
		    "\tmov r14, r12\n"
		    "\tmov r15, 1\n"
		    "\tjmp " greater-than-first-arg-handled "\n"


		    greater-than-first-arg-is-frac ":\n"
		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	

		    greater-than-first-arg-handled ":\n"

		    	"\tmov r10, r14\n"			;init numenator
		    	"\tmov r11, r15\n"			;init denumintor
		    	"\tmov rdi,2\n"

		    greater-than-loop-label ":\n"
		    	"\tcmp rdi, rsi\n"
		    	"\tjg " greater-than-ret-true "\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " greater-than-the-arg-is-frac "\n"


		    	;MAKE INT TO FRACTION AND SEND TO PLUS
		    	greater-than-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " greater-than-two-fractions "\n"


		    	greater-than-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 24 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!

		    	

		    greater-than-two-fractions ":\n"

		    	"\tmov r8, r14\n"				;BU
		    	"\tmov r9, r15\n"				;BU

		    	"\tmov rax, r15\n"
		    	"\tmul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r11\n"
		    	"\tmul r14\n"					;r14 contains common left numinator
		    	"\tmov r14, rax\n"

		    	"\tcmp r10, r14\n"
		    	"\tjle " greater-than-ret-false "\n"

		    	"\tmov r10, r8\n"
		    	"\tmov r11, r9\n"


		    	"\tinc rdi\n"
		    	"\tjmp " greater-than-loop-label "\n"


		    greater-than-ret-true ":\n"
		    	"\tmov rax, " (find-label-by-value #t constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " greater-than-exit "\n"

		    greater-than-ret-false ":\n"
		    	"\tmov rax, " (find-label-by-value #f constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " greater-than-exit "\n"


		   		greater-than-exit ":\n"

			"\tpop rbp\n"
			"\tret\n"

			greater-than-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " greater-than-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '> fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-equal-to
	(lambda (fvarList constList)
		(let ((equal-to-body-label "equal_than_body_func")
			  (equal-to-loop-label "equal_than_loop_label")
			  (equal-to-end-loop-label "equal_than_end_loop_label")
			  (equal-to-two-fractions "equal_than_two_fractions")
			  (equal-to-make-clousure "make_equal_than_closure")
			  (equal-to-the-arg-is-not-frac "equal_than_arg_is_not_frac")
			  (equal-to-the-arg-is-frac "equal_than_arg_is_frac")
			  (equal-to-ret-int "equal_than_int_ret")
			  (equal-to-exit "equal_than_exit")
			  (equal-to-numinator-is-neg "equal_than_numi_is_neg")
			  (equal-to-denominator-is-neg "equal_than_denomi_is_neg")
			  ;(greater-than-start-gcd "small_thagreaterrt_gcd")
			  (equal-to-end-gcd "equal_than_end_gcd")
			  (equal-to-ret-true "equal_than_ret_true")
			  (equal-to-ret-false "equal_than_ret_false")
			  (equal-to-first-arg-is-frac "equal_than_first_arg_is_frac")
			  (equal-to-first-arg-handled "equal_than_first_arg_handled"))
		(string-append 
			"\tjmp " equal-to-make-clousure "\n"

			equal-to-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		   "\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 0\n"
		    "\tjle incorrect_input\n"

		    "\tmov rsi, qword [rbp + 3*8]\n";     
		    "\tcmp rsi, 1\n"
		    "\tje " equal-to-ret-true "\n"


		    "\tmov r12, qword [rbp + 32]\n"			;r12 = first arg
		    "\tmov r13, [r12]\n"					;r13 = curr arg
		    "\tTYPE r13\n"
		    "\tcmp r13, T_FRACTION\n"
		    "\tje " equal-to-first-arg-is-frac "\n"

		    ;FIRST ARG IS INT
	    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    "\tmov r12, [r12]\n"
		    "\tDATA r12\n"
		    "\tmov r14, r12\n"
		    "\tmov r15, 1\n"
		    "\tjmp " equal-to-first-arg-handled "\n"


		    equal-to-first-arg-is-frac ":\n"
		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 32]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	

		    equal-to-first-arg-handled ":\n"

		    	"\tmov r10, r14\n"			;init numenator
		    	"\tmov r11, r15\n"			;init denumintor
		    	"\tmov rdi,1\n"

		    equal-to-loop-label ":\n"
		    	"\tcmp rdi, rsi\n"
		    	"\tje " equal-to-ret-true "\n"

		    	"\tmov r12, qword [rbp + 32 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r13, [r12]\n"					;r13 = curr arg
		    	"\tTYPE r13\n"
		    	"\tcmp r13, T_FRACTION\n"
		    	"\tje " equal-to-the-arg-is-frac "\n"


		    	;MAKE INT TO FRACTION AND SEND TO PLUS
		    	equal-to-the-arg-is-not-frac ":\n"
			    	"\tmov r12, qword [rbp + 32 + rdi*8]\n"	;r12 = point to curr arg
			    	"\tmov r12, [r12]\n"
			    	"\tDATA r12\n"
			    	"\tmov r14, r12\n"
			    	"\tmov r15, 1\n"
			    	"\tjmp " equal-to-two-fractions "\n"


		    	equal-to-the-arg-is-frac ":\n"

		    	"\tmov r12, qword [rbp + 32 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r14, [r12]\n"					;r13 = curr arg
		    	"\tDATA_UPPER r14\n"
		    	"\tadd r14, start_of_data\n"
		    	"\tmov r14, [r14]\n"
		    	"\tDATA r14\n"							;r14 contain numenator!!

		    	"\tmov r12, qword [rbp + 32 + rdi*8]\n"	;r12 = point to curr arg
		    	"\tmov r15, [r12]\n"					;r13 = curr arg
		    	"\tDATA_LOWER r15\n"
		    	"\tadd r15, start_of_data\n"
		    	"\tmov r15, [r15]\n"
		    	"\tDATA r15\n"							;r15 contain dinumenator!!
		    	;"\tmov rsi, r15\n"
		    	

		    equal-to-two-fractions ":\n"

		    	"\tmov r8, r14\n"				;BU
		    	"\tmov r9, r15\n"				;BU

		    	"\tmov rax, r15\n"
		    	"\tmul r10\n"					;r10 contains common right numinator
		    	"\tmov r10, rax\n"

		    	"\tmov rax, r11\n"
		    	"\tmul r14\n"					;r14 contains common left numinator
		    	"\tmov r14, rax\n"

		    	"\tcmp r10, r14\n"
		    	"\tjne " equal-to-ret-false "\n"

		    	"\tmov r10, r8\n"
		    	"\tmov r11, r9\n"


		    	"\tinc rdi\n"
		    	"\tjmp " equal-to-loop-label "\n"


		    equal-to-ret-true ":\n"
		    	"\tmov rax, " (find-label-by-value #t constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " equal-to-exit "\n"

		    equal-to-ret-false ":\n"
		    	"\tmov rax, " (find-label-by-value #f constList) "\n"
		    	;"\tmov r11, 1\n"
		    	"\tjmp " equal-to-exit "\n"


		   		equal-to-exit ":\n"

			"\tpop rbp\n"
			"\tret\n"

			equal-to-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " equal-to-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name '= fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-symbol-to-string
	(lambda (fvarList constList)
		(let ((symbol-to-string-body-label "symbol_to_string_body_func")
			  (symbol-to-string-end-body "symbol_to_string_end_body_func")
			  ;(doesnt-cons "arentEquals")
			  (symbol-to-string-make-clousure "make_symbol_to_string_closure"))
		(string-append 
			"\tjmp " symbol-to-string-make-clousure "\n"

			symbol-to-string-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10

		    "\tmov rbx, qword [rbp + 4*8]\n";     rdx holds first argument
		    "\tmov rbx, [rbx]\n"
		    "\tDATA rbx\n"
		    "\tadd rbx, start_of_data\n"
		    
		   
			 symbol-to-string-end-body ":\n"
			"\tmov rax, rbx\n"

			 "\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			symbol-to-string-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " symbol-to-string-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'symbol->string fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-symbol-pred
	(lambda (fvarList constList)
		(let ((symbol-pred-body-label "symbol_pred_body_func")
			  (symbol-pred-end-body "symbol_pred_end_body_func")
			  (isnt-symbol "symbol_isnt_symbol")
			  (symbol-pred-make-clousure "make_symbol_pred_closure"))
		(string-append 
			"\tjmp " symbol-pred-make-clousure "\n"

			symbol-pred-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tpush rbx\n"						;BU r10

		    "\tmov rbx, qword [rbp + 4*8]\n";     rdx holds first argument
		    "\tmov rbx, [rbx]\n"
		    "\tTYPE rbx\n"
		    
		    "\tcmp rbx, T_SYMBOL\n"
		    "\tjne " isnt-symbol "\n"

		    "\tmov rax, " (find-label-by-value #t constList) "\n"
		    "\tjmp " symbol-pred-end-body "\n"


		    isnt-symbol ":\n"
		    	 "\tmov rax, " (find-label-by-value #f constList) "\n"

		   
			 symbol-pred-end-body ":\n"
			
			 "\tpop rbx\n"						;BU r10

			"\tpop rbp\n"
			"\tret\n"

			symbol-pred-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " symbol-pred-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'symbol? fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-string-to-symbol
	(lambda (fvarList constList)
		(let ((string-to-symbol-body-label "string_to_symbol_body_func")
			  (string-to-symbol-end-body "string_to_symbol_end_body_func")
			  (string-to-symbol-found-string "string_to_symbol_found_string")
			  (string-to-symbol-not-found-string "string_to_symbol_not_found_string")
			  (string-to-symbol-make-clousure "make_string_to_symbol_closure")
			  (string-to-symbol-looking-in-symbol-table "string_to_looking_in_table"))
		(string-append 
			"\tjmp " string-to-symbol-make-clousure "\n"

			string-to-symbol-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"

			"\tbackup_registers\n"

		    "\tmov r10, qword [rbp + 4*8]\n";      	;r10 = string label (address)
		    "\tl30:mov rbx, [r10]\n" 					;rbx holds string

		    
			"\tmov rcx, [head_of_symbol_list]\n"	;first pair label

		    string-to-symbol-looking-in-symbol-table ":\n"

		    	"\tcmp rcx, const_NIL\n"
			    "\tje " string-to-symbol-not-found-string "\n"

			    "\tmov rcx, [rcx]\n" 					;actual pair
			    "\tmov rdx, rcx\n"					;rdx contain lable to first arg [pair\nil]
			    "\tCAR rdx\n" 						;***SEG HERE IF APPLY TWICE THIS FUNC - PROBABLY WERE WE UPDATE THE LINKED LIST

			    "\tcmp rdx, rbx\n"
			    "\tje " string-to-symbol-found-string "\n"

			    "\tmov rdx, rcx\n"

			    "\tDATA_LOWER rdx\n"
			    "\tadd rdx, start_of_data\n"

			    "\tmov rcx, rdx\n"
			    "\tjmp " string-to-symbol-looking-in-symbol-table "\n"
			    "\t\n"

		    
		   string-to-symbol-found-string ":\n"

		   "\tmov rdi, const_BOOL_TRUE\n"
		   "\tmov rbx, qword [rbp + 4*8]\n";
		   "\tmov r9, rbx\n"
		   ;"\tDATA r9\n"

		   "loop_on_constList:\n"
		   	   "\tmov rcx, [rdi]\n"
		   	   "\tTYPE rcx\n"

		   	   "\tcmp rcx, T_VECTOR\n"
		   	   "\tje type_is_vector\n"

		   	   "\tcmp rcx, T_STRING\n"
		   	   "\tje type_is_string\n"

		   	   "\tadd rdi, 8\n"
		   	   "\tjmp look_up\n"


		   	   "type_is_vector:\n"
		   	   		"\tadd rdi, 16\n"
		   	   		"\tjmp look_up\n"

		   	   	"type_is_string:\n"
		   	   		"\tadd rdi, 9\n"
		   	   		"\tjmp look_up\n"


		   	   "look_up:\n"
			   	   
				   "\tmov rcx, [rdi]\n"
				   "\tmov rdx, rcx\n"
				   "\tTYPE rdx\n"
				   "\tcmp rdx, T_SYMBOL\n"
				   "\tjne loop_on_constList\n"

				   "\tmov rcx, [rdi]\n"
				   "\tmov rdx, rcx\n"
				   "\tDATA rdx\n"
				   "\tl1:add rdx, start_of_data\n"
				  
				   "\tcmp rdx, r9\n"
				   "\tjne loop_on_constList\n"

				   "\tl2:mov rax, rdi\n"
				   "\tjmp " string-to-symbol-end-body "\n"



		   "\tmov rbx, qword [rbp + 4*8]\n";
		   "\tmov r9, rbx\n"
		   "mymalloc 1\n"
		   "\tMAKE_LITERAL_SYMBOL_RUNTIME rax, r9\n"

		    "\tjmp " string-to-symbol-end-body "\n"


		    string-to-symbol-not-found-string ":\n"

		    	"\tmymalloc 1\n"								;malloc for new symbol
		    	"\tmov r9, r10\n"
		    	"\tMAKE_LITERAL_SYMBOL_RUNTIME rax, r9\n" 		;rax label of new symbol
		    	"\tmov rbx, rax\n"
		    	
		    	"\tmov rcx, qword [head_of_symbol_list]\n"


		    	"\tmymalloc 1\n"		
		    	"\tMAKE_MALLOC_LITERAL_PAIR rax, r10, rcx\n"


		    	"\tmov qword [head_of_symbol_list], rax\n"
		    	
		    	"\tmov rax, rbx\n"

		   
			 string-to-symbol-end-body ":\n"
			
			 "\trestore_registers\n"

			"\tpop rbp\n"
			"\tret\n"

			string-to-symbol-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " string-to-symbol-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'string->symbol fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-make-string
	(lambda (fvarList constList)
		(let ((make-string-body-label "make_string_body_func")
			  (make-string-end-body "make_string_end_body_func")
			  (make-string-loop "make_string_loop")
			  (make-string-end-loop "make_string_end_loop")
			  (make-string-make-clousure "make_make_string_closure")
			  (make-string-two-args "make_string_two_args")
			  (make-string-init-string "make_string_init_string"))
		(string-append 
			"\tjmp " make-string-make-clousure "\n"

			make-string-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		    "\tmov rbx, qword [rbp + 4*8]\n"     
		    "\tmov rbx, [rbx]\n"
		    "\tDATA rbx\n"							;rbx = string len

		    "\tmov rdx, qword [rbp + 3*8]\n";     
		    "\tcmp rdx, 1\n"
		    "\tjg " make-string-two-args "\n"


		    ;ONLY ONE ARG
		    "\tmov rcx, 0\n"
		    "\tjmp " make-string-init-string "\n"

		    make-string-two-args ":\n"

			    "\tmov rcx, qword [rbp + 5*8]\n";     
			    "\tmov rcx, [rcx]\n"
			    "\tDATA rcx\n"							;rcx = char to string rbx times
		    



		    make-string-init-string ":\n"

			    "\tmymalloc2 rbx\n"						;init new string
			    ;"\tmov rcx, 0\n"						;*********
			    "\tmov rdi, 0\n"


		    ;create new string
		    make-string-loop ":\n"
			    "\tcmp rdi, rbx\n"
			    ;"\tje " make-string-end-loop "\n"
			    "\tje make_string_end_2\n"
			    "\tmov byte [rax + rdi], cl\n"			;rcx low byte
			    "\tinc rdi\n"
			    "\tjmp " make-string-loop "\n"



			"make_string_end_2:"   
			
			"\tmov rdi, const_BOOL_TRUE\n"
		
				;rbx = len of new string
			   ;[rax] contains string
			   "make_string_loop_on_constList:\n"
		   			
		   			"\tl22:cmp rdi, fvar0\n"
					"\tjge " make-string-end-loop "\n"

			   	   "\tmov rcx, [rdi]\n"
			   	   "\tTYPE rcx\n"

			   	   "\tcmp rcx, T_VECTOR\n"
			   	   "\tje make_string_type_is_vector\n"

			   	   "\tcmp rcx, T_STRING\n"
			   	   "\tje make_string_type_is_string\n"

			   	   "\tadd rdi, 8\n"
			   	   "\tjmp make_string_look_up\n"


			   	   "make_string_type_is_vector:\n"
			   	   		"\tadd rdi, 16\n"
			   	   		"\tjmp make_string_look_up\n"

			   	   	"make_string_type_is_string:\n"
			   	   		"\tadd rdi, 9\n"
			   	   		;"\tjmp make_string_look_up\n"


			   	   "make_string_look_up:\n"
				   	   
					   "\tmov rcx, [rdi]\n"
					   "\tmov rdx, rcx\n"
					   "\tTYPE rdx\n"
					   "\tcmp rdx, T_STRING\n"
					   "\tjne make_string_loop_on_constList\n"

					   ;checking length strings
					   "\tmov rcx, [rdi]\n"
					   "\tmov rdx, rcx\n"
					   "\tDATA_UPPER rdx\n"
					   "\tcmp rdx, rbx\n"
					   "\tjne make_string_loop_on_constList\n"


					   "\tmov rcx, [rdi]\n"
					   "\tmov rdx, rcx\n"
					   "\tDATA_LOWER rdx\n"
					   "\tadd rdx, start_of_data\n"
					  
					   "mov r15, 0\n"
					   "mov r15B, [rax]\n"
					   "\tl20:mov r8, 0\n"
					   ;"\tdec r8\n"

					   "make_string_loop2:\n"

					   		"\tcmp r8, rbx\n"
					   		"\tje make_string_end_loop_found_string\n"

					   		"\tmov r9, 0\n"
					   		"\tor r9B, byte [rax]\n"
					   		"\tcmp byte r9B, [rdx + r8]\n"
					   		"\tjne " make-string-end-loop "\n"

					   		"\tl21:inc r8\n"
					   		"\tjmp make_string_loop2\n"


					   "make_string_end_loop_found_string:\n"

						   ;"\tl11:cmp rdx, r9\n"
						   ;"\tjne make_string_loop_on_constList\n"

						   "\tmov rax, rdi\n"
						   "\tjmp " make-string-end-body "\n"









			make-string-end-loop ":\n"

				"\tmov rcx, rax\n"				;BU pointer to new string
				"\tsub rcx, start_of_data\n"
				"\tmymalloc 1\n"
				"\tmov qword [rax], rbx\n"
				"\tshl qword [rax], 30\n"
				"\tor  qword [rax],rcx\n"
				"\tshl qword [rax], TYPE_BITS\n"
				"\tor qword [rax], T_STRING\n"
				;"\tmov rax, qword [rax]\n"

			 make-string-end-body ":\n"


			"\tpop rbp\n"
			"\tret\n"

			make-string-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " make-string-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'make-string fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-make-vector
	(lambda (fvarList constList)
		(let ((make-vector-body-label "make_make_vector_body_func")
			  (make-vector-end-body "make_make_vector_end_body_func")
			  (make-vector-loop "make_make_vector_loop")
			  (make-vector-end-loop "make_make_vector_end_loop")
			  (make-vector-make-clousure "make_make_vector_closure")
			  (make-vector-two-args "make_make_vector_two_args")
			  (make-vector-init-vector "make_make_make_vector_init_string"))
		(string-append 
			"\tjmp " make-vector-make-clousure "\n"

			make-vector-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		    "\tmov rbx, qword [rbp + 4*8]\n"     
		    "\tmov rbx, [rbx]\n"
		    "\tDATA rbx\n"							;rbx = vector len

		    "\tmov rdx, qword [rbp + 3*8]\n";     
		    "\tcmp rdx, 1\n"
		    "\tjg " make-vector-two-args "\n"


		    ;****ONLY ONE ARG****
		    "\tmymalloc 1\n"
		    "\tmov rcx, rax\n"
		    "\tmov qword [rcx], 0\n"
		    "\tor qword [rcx], T_INTEGER\n"
		    "\tjmp " make-vector-init-vector "\n"



		    make-vector-two-args ":\n"

			    "\tmov rcx, qword [rbp + 5*8]\n";     
			    
		    
		    make-vector-init-vector ":\n"

			    "\tmymalloc rbx\n"			;allocate (vector-len) address
			    "\tmov rdi, 0\n" 			;init index loop

		    ;create new string
		    make-vector-loop ":\n"
			    "\tcmp rdi, rbx\n"
			    "\tje " make-vector-end-loop "\n"
			    "\tmov [rax + rdi * 8], rcx\n"		
			    "\tinc rdi\n"
			    "\tjmp " make-vector-loop "\n"



			make-vector-end-loop ":\n"

				"\tmov rcx, rax\n"				;BU pointer to new string
				"\tsub rcx, start_of_data\n"
				"\tmymalloc 1\n"
				"\tmov qword [rax], rbx\n"
				"\tshl qword [rax], 30\n"
				"\tor  qword [rax],rcx\n"
				"\tshl qword [rax], TYPE_BITS\n"
				"\tor qword [rax], T_VECTOR\n"
				;"\tmov rax, qword [rax]\n"

			 make-vector-end-body ":\n"


			"\tpop rbp\n"
			"\tret\n"

			make-vector-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " make-vector-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'make-vector fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-vector-set
	(lambda (fvarList constList)
		(let ((vector-set-body-label "make_vector_set_body_func")
			  (vector-set-end-body "make_vector_set_end_body_func")
			  (vector-set-make-clousure "make_make_vector_set_closure")
			  (vector-set-two-args "make_vector_set_two_args")
			  (vector-set-init-vector "make_vector_set_init_string"))
		(string-append 
			"\tjmp " vector-set-make-clousure "\n"

			vector-set-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		    "\tmov rbx, qword [rbp + 4*8]\n"     	
		    "\tmov rbx, [rbx]\n"					;rbx = addres vector
		    "\tDATA_LOWER rbx\n"
		    "\tadd rbx, start_of_data\n"					;					

		    "\tmov rcx, qword [rbp + 5*8]\n";     	
		    "\tmov rcx, [rcx]\n"
		    "\tDATA rcx\n"							;rcx = pos to set (index)


		    "\tmov rdx, qword [rbp + 6*8]\n";     	;rdx = address of value to set

		    "\tmov [rbx + rcx*8], rdx\n"
		    "\tmov rax, " (find-label-by-value (void) constList) "\n"


			"\tpop rbp\n"
			"\tret\n"

			vector-set-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " vector-set-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'vector-set! fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-vector
	(lambda (fvarList constList)
		(let ((vector-body-label "vector_body_func")
			  (vector-end-body "vector_end_body_func")
			  (vector-make-clousure "vector_closure")
			  (vector-loop "vector_loop")
			  (vector-end-loop "vector_end_loop")
			  (vector-init-vector "vector_init_string"))
		(string-append 
			"\tjmp " vector-make-clousure "\n"

			vector-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		    "\tmov rbx, qword [rbp + 3*8]\n"     	;rbx = length vector
		    ;"\tmov rbx, [rbx]\n"					
		    ;"\tDATA rbx\n"

		    "\tmov rdi, 0\n"
		    "\tmymalloc rbx\n"

		    vector-loop ":\n"
			    "\tcmp rdi, rbx\n"
			    "\tje " vector-end-body "\n"
			    "\tmov rcx, [rbp + 32 +rdi*8]\n"	;arg[rdi]
			    ;"\tmov rcx, [rcx]\n"
			    ;"\tDATA rcx\n"
			    
			    "\tmov qword [rax + rdi*8], rcx\n"
			    "\tinc rdi\n"
			    "\tjmp " vector-loop "\n"


			vector-end-loop ":\n"


		    ;"\tadd rbx, start_of_data\n"					;					

		   

		    vector-end-body ":\n"

		    	"\tsub rax, start_of_data\n"
		    	"\tmov rcx, rax\n"

		    	"\tmymalloc 1\n"
		    	"\tmov qword [rax], rbx\n"
		    	"\tshl qword [rax], 30\n"
		    	"\tor qword [rax], rcx\n"
		    	"\tshl qword [rax], 4\n"
		    	"\tor qword [rax], T_VECTOR\n"


			"\tpop rbp\n"
			"\tret\n"

			vector-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " vector-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'vector fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-string-set
	(lambda (fvarList constList)
		(let ((string-set-body-label "make_string_set_body_func")
			  (string-set-end-body "make_string_set_end_body_func")
			  (string-set-make-clousure "make_make_string_set_closure")
			  (string-set-two-args "make_string_set_two_args")
			  (string-set-init-string "make_string_set_init_string"))
		(string-append 
			"\tjmp " string-set-make-clousure "\n"

			string-set-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		    "\tmov rbx, qword [rbp + 4*8]\n"     	
		    "\tmov rbx, [rbx]\n"					
		    "\tDATA_LOWER rbx\n"
		    "\tadd rbx, start_of_data\n"					;					

		    "\tmov rcx, qword [rbp + 5*8]\n";     	
		    "\tmov rcx, [rcx]\n"
		    "\tDATA rcx\n"							;rcx = pos to set (index)


		    "\tmov rdx, qword [rbp + 6*8]\n";     	;rdx = address of value to set
		    "\tmov rdx, [rdx]\n"
		    "\tDATA rdx\n"
		    "\t\n"

		    "\tmov [rbx + rcx], dl\n"
		    "\t\n"
		    "\tmov rax, " (find-label-by-value (void) constList) "\n"


			"\tpop rbp\n"
			"\tret\n"

			string-set-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " string-set-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'string-set! fvarList)) "], rax\n"
			"\t\n"
		))))

(define fvar-apply
	(lambda (fvarList constList)
		(let ((apply-body-label "make_apply_body_func")
			  (apply-end-body "make_apply_end_body_func")
			  (apply-make-clousure "make_make_apply_closure")
			  (apply-args-length-loop "apply_args_length_loop")
			  (apply-args-length-end-loop "apply_args_length_end_loop")
			  (apply-init-string "make_apply_init_string")
			  (apply-fix-stack-loop "apply_fix_stack_loop")
			  (apply-fix-stack-end-loop "apply_fix_stack_end_loop"))
		(string-append 
			"\tjmp " apply-make-clousure "\n"

			apply-body-label ":\n"
			"\tpush rbp\n"
			"\tmov rbp, rsp\n"


		   	"\tl0:mov rax, [rbp + 4*8]\n"			
	        "\tmov rax, qword [rax]\n"			;rax = func
	        "\tmov r12, qword [rbp]\n" 			;r10 =  old rbp
	        "\tmov r11,qword [rbp + 1*8]\n" 	;r11 =  return address
	        "\tmov r10, rbp\n"
	        "\tadd r10, 6*8\n" 			    	;r10 = point after lst arg
	        
	         
	        "\tmov rbx, [rbp + 5*8]\n"			
	        "\tmov rbx, qword [rbx]\n" 			;rbx = list of args

	        "\tmov rcx, rbx\n" 					;rcx = arg[i]
	        ;"\tmov rbx\n"
	        "\tTYPE rcx\n"

	        ;*******************
	        ;*******************

	        "\tmov rdi, 0\n"  					;counter args len

		    apply-args-length-loop ":\n"
			    "\tcmp rcx, T_NIL\n"
			    "\tje " apply-args-length-end-loop "\n"
			    "\tinc rdi\n"
			    "\tCDR rbx\n"
			    "\tmov rcx, rbx\n"
			    "\tTYPE rcx\n"
			    "\tjmp " apply-args-length-loop "\n"

			apply-args-length-end-loop ":\n"

	        "\tshl rdi, 3\n"
	        "\tsub r10, rdi\n" 		;r10 point to last args position in stack 
	        "\tshr rdi, 3\n"
	        
	        "\tmov rsi, 0\n"	 		;index to fix the stack
	        "\tmov rbx, [rbp + 5*8]\n"			 
	        "\tmov rbx, qword [rbx]\n" 	;rbx point to lst

	        apply-fix-stack-loop ":\n"

		        "\tcmp rsi, rdi\n"
		        "\tje " apply-fix-stack-end-loop "\n"
		        "\tmov rcx, rbx\n"
		        "\tDATA_UPPER rcx\n"
				"\tadd rcx, start_of_data\n"    
		        "\tmov qword [r10 + 8 * rsi], rcx\n"
		        "\tCDR rbx\n"
		        "\tinc rsi\n"
		        "\tjmp " apply-fix-stack-loop "\n"
	        
	        apply-fix-stack-end-loop ":\n"


	        "\tsub r10, 8\n" 					;r10 point to last arg after fix stack
	        "\tmov qword [r10], rdi\n"			;push arg length

	        "\tsub r10, 8\n"
	        "\tmov rbx, rax\n"
	        "\tCLOSURE_ENV rbx\n"
	        "\tmov qword [r10], rbx\n" 			;push env

	        "\tsub r10, 8\n"
	        "\tmov qword [r10], r11\n"			;push return address
	        "\tmov rsp, r10\n"	        
	        "mov rbp, r12\n" 					;restore old rbp
	        "mov rbx, rax\n" 
	        ;"TYPE rbx\n"
	        
	        ;"cmp rbx, T_CLOSURE\n"
	        ;"jne apply_finish\n"
	        "CLOSURE_CODE rax\n"
	        "jmp rax\n"
	        "apply_finish:\n"





			"\tpop rbp\n"
			"\tret\n"

			apply-make-clousure ":\n"
			"\tmymalloc 2\n"
			"\tMAKE_LITERAL_CLOSURE rax, 0, " apply-body-label "\n"
			"\tmov qword [fvar" (number->string (find-fvar-index-by-name 'apply fvarList)) "], rax\n"
			"\t\n"
		))))

;####<---CODE-GENERATOR--->####

(define find-const-address
	(lambda (constValue constList)
		(if (null-or-not-list? constList)
			(list '"ERROR--->func:find-const-addrs")
			(let ((currConstValue (cadar constList))
				  (currConstAdrress (caar constList)))
				(if (equal? currConstValue constValue)
					currConstAdrress
	          		(find-const-address constValue (cdr constList)))))))

(define code-gen-const
	(lambda (pe constList)
  		(string-append
  				"\tmov rax, "
  				(find-label-by-value (cadr pe) constList)
  				;"[const (number->string (find-const-address (cadr pe) constList))"
  				"\n")))

(define code-gen-if3
	(lambda (pe depth constList fvarList)
		(let*  ((test-case (cadr pe))
				(then-case (caddr pe))
				(else-case (cadddr pe))
				(label-counter-string (number->string (if3-label-plusplus)))
				(else-case-label (string-append "if3_" label-counter-string "_else"))
				(end-of-if3-label (string-append "if3_" label-counter-string "_end")))

			(string-append
				(code-gen test-case depth constList fvarList)	;test case answer goes into RAX
				"\tcmp rax, " (find-label-by-value #f constList) "\n"						;and then compared to false value
				"\tje " else-case-label "\n"
				(code-gen then-case depth constList fvarList)
				"\tjmp " end-of-if3-label "\n"
				"\n" else-case-label ":\n"
				(code-gen else-case depth constList fvarList)
				"\n" end-of-if3-label ":\n\n"
			)
		)
	))

(define code-gen-seq 
	(lambda (args depth constList fvarList)
    	(if (null-or-not-list? args)
    		""
        	(let ((currArg (code-gen (car args) depth constList fvarList)))
        		(string-append currArg (code-gen-seq (cdr args) depth constList fvarList))))))

(define code-gen-or
	(lambda (args depth constList fvarList)
		(letrec ((genCodedArgs (map (lambda (sub-pe)
										(code-gen sub-pe depth constList fvarList))
								args))
           		 (exitOrLabel (string-append "or_" (number->string (or-label-plusplus)) "_exit:"))
		         (sub-or-gen (lambda (genCodedArgs)
		                     (if (null-or-not-list? (cdr genCodedArgs))					
		                      	 (string-append (car genCodedArgs) "\n" exitOrLabel "\n\n")		;last or's element
		                         (string-append (car genCodedArgs)
		                                        "\tcmp rax, " (find-label-by-value #f constList) "\n"
		                                        "\tjne " (remove-last-char exitOrLabel) "\n"
		                                        (sub-or-gen (cdr genCodedArgs))))))) 

  
    		(sub-or-gen genCodedArgs))))

(define code-gen-def
	(lambda (pe depth constList fvarList)
    	(string-append
      				  (code-gen (caddr pe) depth constList fvarList)
      				  ;"\tmov rbx, [rax]\n"
				      "\tmov [fvar" (number->string (find-const-address (cadr (cadr pe)) fvarList))"], rax\n"			;put code-gen(body's define) at right place by fvarList
				      "\tmov rax, " (find-label-by-value (void) constList) "\n")))

(define code-gen-fvar
	(lambda (pe depth constList fvarList)
		(let ((fvar-label (string-append "fvar" (number->string (find-const-address (cadr pe) fvarList)))))
			(string-append
				"\tmov rax, qword [" fvar-label "]\n\n"
			)
		)
	))

(define code-gen-pvar
	(lambda (pe depth constList fvarList)
		(let ((minor (number->string (caddr pe))))
			(string-append
				"\tmov rbx, 4\n"				;to skip stack pointer to pvars location
				"\tadd rbx, " minor	"\n"		;to skip stack pointer to the exact pvar location by his minor
				"\tmov rax, qword [rbp + rbx * 8]\n\n" 
			)
		)
	))

(define code-gen-bvar
	(lambda (pe depth constList fvarList)
		(let ((major (number->string (caddr pe)))
			  (minor (number->string (cadddr pe))))
			(string-append
				"\tmov rax, qword [rbp + 2 * 8]\n"				;to skip stack pointer to bvars location
				"\tmov rbx, " major	"\n"						;to skip stack pointer to the bvar location by his major
				"\tmov rax, qword [rax + rbx * 8]\n" 
				"\tmov rbx, " minor	"\n"						;to skip stack pointer to the exact bvar location by his minor
				"\tmov rax, qword [rax + rbx * 8]\n\n" 
			)
		)
	))

(define code-gen-set
	(lambda (pe depth constList fvarList)
		(let ((varType (caadr pe)))
			(cond ((eq? varType 'fvar) (code-gen-set-fvar pe depth constList fvarList))
				  ((eq? varType 'pvar) (code-gen-set-pvar pe depth constList fvarList))
				  ((eq? varType 'bvar) (code-gen-set-bvar pe depth constList fvarList))
				  (else (display 'ERROR-->func:code-gen-set)))
		)
	))

(define code-gen-set-fvar
	(lambda (pe depth constList fvarList)
		(let* ((fvar (cadr pe))
			   (fvar-label (string-append "fvar" (number->string (find-const-address (cadr fvar) fvarList))))
			   (value (caddr pe)))
			(string-append
				(code-gen value depth constList fvarList)		;computes the value and puts it in rax
				"\tmov qword [" fvar-label "], rax\n" 			;put the computed value that rax stores into the bvar address in the env
				"\tmov rax, SOB_VOID\n\n"						;void is returned	
			)
		)
	))


(define code-gen-set-pvar
	(lambda (pe depth constList fvarList)
		(let* ((pvar (cadr pe))
			   (value (caddr pe))
			   (minor (number->string (caddr pvar))))
			(string-append
				(code-gen value depth constList fvarList)		;computes the value and puts it in rax
				"\tmov rbx, 4\n"								;to skip stack pointer to pvars location
				"\tadd rbx, " minor	"\n"						;to skip stack pointer to the exact pvar location by his minor
				"\tmov qword [rbp + rbx * 8], rax\n" 			;put the computed value that rax stores into the bvar address in the env
				"\tmov rax, SOB_VOID\n\n"						;void is returned	
			)
		)
	))

(define code-gen-set-bvar
	(lambda (pe depth constList fvarList)
		(let* ((bvar (cadr pe))
			   (value (caddr pe))
			   (major (number->string (caddr bvar)))
			   (minor (number->string (cadddr bvar))))
			(string-append
				(code-gen value depth constList fvarList)		;computes the value and puts it in rax
				"\tmov rbx, qword [rbp + 2 * 8]\n"				;to skip stack pointer to env location
				"\tmov rcx, " major	"\n"						;to skip stack pointer to the bvar location by his major
				"\tmov rbx, qword [rbx + rcx * 8]\n" 			
				"\tmov rcx, " minor	"\n"						;to skip stack pointer to the exact bvar location by his minor
				"\tmov qword [rbx + rcx * 8], rax\n" 			;put the computed value that rax stores into the bvar address in the env
				"\tmov rax, SOB_VOID\n\n"						;void is returned	
			)
		)
	))



(define code-gen-box
	(lambda (pe depth constList fvarList)
		(let ((box (cadr pe)))
			(string-append
				(code-gen box depth constList fvarList)			;computes the box and puts it in rax
				"\tmov rbx, rax\n"								;save rax value in rbx for now
				"\tmymalloc 1\n"								;call mymalloc with the value 8=rdi
				"\tmov qword [rax], rbx\n\n"					;put rbx value in the allocated memory pointed by rax 
			)
		)
	)
)


(define code-gen-box-get
	(lambda (pe depth constList fvarList)
		(let ((var (cadr pe)))
			(string-append
				(code-gen var depth constList fvarList)			;computes the var and puts it in rax
				"\tmov rax, [rax]\n\n"							;dereference rax
			)
		)
	)
)


(define code-gen-box-set
	(lambda (pe depth constList fvarList)
		(let ((box (cadr pe))
			  (value (caddr pe))
			  (label-number (number->string (global-label-plusplus))))
			(string-append
				"mov rax, 10\n"
				"L_BREAK_0" label-number ":\n"
				(code-gen value depth constList fvarList)		;computes the value and puts it in rax
				"L_BREAK_1" label-number ":\n"
				"\tmov rbx, rax\n"								;save rax value in rbx for now
				"L_BREAK_2" label-number ":\n"
				(code-gen box depth constList fvarList)			;computes the box and puts it in rax
				"L_BREAK_3" label-number ":\n"
				"\tmov [rax], rbx\n"							;put rbx (the value) content in the adress of the box that is in rax
				"L_BREAK_4" label-number ":\n"
				"\tmov rax, SOB_VOID\n\n"						;void is returned	
			)
		)
	))



(define code-gen-lambda-simple
	(lambda (pe depth constList fvarList)			;[pe = lambda-simple params body]
		(let* ((closure-number (lambda-label-plusplus))
			   (arg-loop-label 	   (string-append "closure_simple_params_loop_" (number->string closure-number)))
			   (arg-loop-end-label (string-append "closure_simple_params_loop_end_" (number->string closure-number)))
			   (env-loop-label 	   (string-append "closure_simple_env_loop_" (number->string closure-number)))
			   (env-loop-end-label (string-append "closure_simple_env_loop_end_" (number->string closure-number)))
			   (body-label 		   (string-append "closure_simple_body_" (number->string closure-number)))
			   (end-closure-label  (string-append "closure_simple_end_" (number->string closure-number)))
			   ;(display "\n")
			   ;(display (number->string depth))
			   ;(display "\n")
			   );(arg-count (number->string (length (cadr pe)))))
			(string-append
					"\tmymalloc 1\n"	
					"\tmov rbx, rax\n" 						; if no upper lambdas, no need for more envs

					"\tmymalloc 2\n"									;rax=malloc(8bytes)
					"\tmov rdi, rax\n"						; backup rax

					(if (> depth 0)
						  (string-append	

							"\tmymalloc " (number->string (+ depth 1)) "\n"		;rbx=malloc(8bytes*(m+1))
							"\tmov rbx, rax\n" 									;rbx=new env
							
							"\tmov r9, [rbp + 3 * 8]\n"
							"\tmymalloc r9\n"						;rcx=malloc(8bytes*(n))
							"\tmov rcx, rax\n" 									;rcx=params list

							"\tmov rax, rdi\n"						; restore rax

					;params_loop:
							"\tmov rdx, [rbp + 3 * 8]\n"						;parameter count (arg_count)
							"\tmov rdi, 0\n"									;parameter index

							"\n" arg-loop-label ":\n"
							
							"\tcmp rdi, rdx\n"
							"\tjge " arg-loop-end-label "\n"


							"\tmov r13, rdi\n"									;parameter index
							"\tadd r13, 4\n"									;to skip the 4 elements in the top of the stack
							"\tmov r14, qword [rbp + r13 * 8]\n"				;fetching parameter i value
							"\tmov qword [rcx + rdi * 8], r14\n"				;copying the value of the parameter to the list pointed by rcx

							"\tinc rdi\n"

							"\tjmp " arg-loop-label "\n"

							"\n" arg-loop-end-label ":\n"
					;params_loop-end:

							
							"\tmov [rbx], rcx\n"								;updating first env to be the current
							"\tmov r13, 0\n"									;r13=i=0
							"\tmov r14, 1\n"									;r14j=1

					;env_loop:
							"\n" env-loop-label ":\n"
							
							"\tcmp r13, " (number->string depth) "\n"
							"\tjge " env-loop-end-label "\n"

							"\tmov rdx, qword [rbp + 2 * 8]\n"					;rdx=old env
							"\tmov rdi, qword [rdx + r13 * 8]\n"				;rdi=current env
							"\tmov qword [rbx + r14 * 8], rdi\n"				;updating current env to be the one in rdi
							"\tinc r13\n"										;i++
							"\tinc r14\n"										;j++

							"\tjmp " env-loop-label "\n"
							"\n\n" env-loop-end-label ":\n\n"
					;env_loop_end:
							)
						  
							"")

					"\tmov rcx, " body-label "\n"
					"\tMAKE_LITERAL_CLOSURE rax, rbx, rcx\n"
					;"\tl2:mov rax, qword [rax]\n"
					"\tjmp " end-closure-label "\n"


					"\n\n" body-label ":\n"

					"\tpush rbp\n"
					"\tmov rbp, rsp\n"
					
					(code-gen (caddr pe) (+ depth 1) constList fvarList)
					
					"\tleave\n"
					"\tret\n"

					"\n\n" end-closure-label ":\n\n"))))


(define code-gen-lambda-opt
	(lambda (pe depth constList fvarList)			;[pe = lambda-opt params rest body] ;;;;;;; in lambda-opt sum of args is (length paramas)+1 ,+1 present list of optinals params
		(let* ((closure-number (lambda-label-plusplus))
			   (arg-loop-label 	   (string-append "closure_opt_arg_loop_" (number->string closure-number)))
			   (arg-loop-end-label (string-append "closure_opt_arg_loop_end_" (number->string closure-number)))
			   (env-loop-label 	   (string-append "closure_opt_env_loop_" (number->string closure-number)))
			   (env-loop-end-label (string-append "closure_opt_env_loop_end_" (number->string closure-number)))
			   (body-label 		   (string-append "closure_opt_body_" (number->string closure-number)))
			   (end-closure-label  (string-append "closure_opt_end_" (number->string closure-number)))
			   (arg-count 		   (number->string (length (cadr pe))))
			   (fix-stack-label	   (string-append "closure_opt_fix_stack_loop_" (number->string closure-number)))
			   (fix-stack-label-end (string-append "closure_opt_fix_stack_loop_end_" (number->string closure-number))))
				   ;(arg-count (number->string (length (cadr pe)))))
			(string-append
					"\tmymalloc 1\n"	
					"\tmov rbx, rax\n" 						; if no upper lambdas, no need for more envs

					"\tmymalloc 2\n"									;rax=malloc(8bytes)
					"\tmov rdi, rax\n"						; backup rax

					(if (> depth 0)
						  (string-append	

							"\tmymalloc " (number->string (+ depth 1)) "\n"		;rbx=malloc(8bytes*(m+1))
							"\tmov rbx, rax\n" 									;rbx=new env
							
							"\tmov r9, [rbp + 3 * 8]\n"
							"\tmymalloc r9\n"						;rcx=malloc(8bytes*(n))
							"\tmov rcx, rax\n" 									;rcx=params list

							"\tmov rax, rdi\n"						; restore rax

					;arg_loop:
							"\tmov rdx, " arg-count "\n"			;parameter count (arg_count)
							"\tmov rdi, 0\n"					;parameter index

							"\n" arg-loop-label ":\n"
							
							"\tcmp rdi, rdx\n"
							"\tjge " arg-loop-end-label "\n"


							"\tmov r13, rdi\n"					;parameter index
							"\tadd r13, 4\n"					;to skip the 4 elements in the top of the stack
							"\tmov r14, qword [rbp + r13 * 8]\n"	;fetching parameter i value
							"\tmov qword [rcx + rdi * 8], r14\n"	;copying the value of the parameter to the list pointed by rcx

							"\tinc rdi\n"

							"\tjmp " arg-loop-label "\n"
							"\n" arg-loop-end-label ":\n"
					;arg_loop-end:

							
							"\tmov [rbx], rcx\n"				;updating first env to be the current
							"\tmov r13, 0\n"					;i=0
							"\tmov r14, 1\n"					;j=1

					;env_loop:
							"\n" env-loop-label ":\n"
							
							"\tcmp r13, " (number->string depth) "\n"
							"\tjge " env-loop-end-label "\n"

							"\tmov rdx, qword [rbp + 2 * 8]\n"			;rdx=env
							"\tmov rdi, qword [rdx + r13 * 8]\n"		;rdi=current env
							"\tmov qword [rbx + r14 * 8], rdi\n"		;updating current env to be the one in rdi
							"\tinc r13\n"						;i++
							"\tinc r14\n"						;j++

							"\tjmp " env-loop-label "\n"
							"\n\n" env-loop-end-label ":\n\n"
					;env_loop_end:

						)
					  		"")


					"\tmov rcx, " body-label "\n"
					"\tMAKE_LITERAL_CLOSURE rax, rbx, rcx\n"
					;"\tmov rax, qword [rax]\n"
					"\tjmp " end-closure-label "\n"


					"\n\n" body-label ":\n"

					"\tpush rbp\n"
					"\tmov rbp, rsp\n"

					;;;;;TO-CHECK ->>> should we add a continue conditional?
					;"\tcmp qword [rbp + 3 * 8]," arg-count "\n"
     				;"\tjl lambda_opt_wrong_args\n"


     				;build a list of rest params
					"\tmov rbx, " (find-label-by-value '() constList) "\n"							;rbx = NIL - end of list

					"\tmov rdi, qword [rbp +3*8]\n" 	;rdi = n+m ->>> i, cur arg
					"\tmov rdx, " (number->string (string->number arg-count)) "\n"			;rdx = n
					"\n" fix-stack-label ":\n"

					"\tcmp rdi, rdx\n"
					"\tjle " fix-stack-label-end "\n"

					"\tmymalloc 1\n"				;malloc for next opt-arg
					"\tmov rcx, rax\n"				;save the malloc poiter in rcx 

					"\tmov r11, rbp\n"				
					"\tadd r11, 4*8\n"				;r11 point to first arg in stack (offset)
					
					"\tmov r10, rdi\n"				;r10 is helper for point of arg[i]
					"\tdec r10\n"
					"\tshl r10, 3\n"				;now offset+r10 = address of curr arg				
					"\tadd r11, r10\n"				;rdx = address of arg[i]
					"\tmov r11, qword [r11]\n"		;rdx = value of arg[i]

					"\tMAKE_MALLOC_LITERAL_PAIR rax, r11, rbx\n"				;rax = target, rbx = cdr, rcx = car
					"\tmov rbx, rax\n"										;rbx ponints to the new pair as cdr for the new allocate in next iteration
					
					"\tdec rdi\n"					;at-least 1 arg
					"\tjmp " fix-stack-label "\n"

					"\n" fix-stack-label-end ":\n"
					"\tmov qword [rbp+4*8+rdx*8], rbx\n"	;add the list in stack after const params (not optinals)
					;"\tmov qword [rbp + 3*8], " (number->string (+ 1 (string->number arg-count))) "\n"


					(code-gen (cadddr pe) (+ depth 1) constList fvarList)
					
					"\tleave\n"
					;"\tpop rbp\n"
					"\tret\n"

					"\n\n" end-closure-label ":\n\n"))))


(define code-gen-applic
	(lambda (pe depth constList fvarList)
		(let* ((proc (cadr pe))
			   (params (caddr pe))
			   (params-n (length params))
			   (applic-label-num (number->string (applic-label-plusplus)))
			   (applic-pop-loop-label (string-append "applic_pop_loop_" applic-label-num))
			   (applic-pop-loop-end-label (string-append "applic_pop_loop_end_" applic-label-num))
			  )
			(string-append
				"\tpush " (find-label-by-value (void) constList) "\n"							;pushing VOID to the stack
				(apply string-append
					(map 
						(lambda (param)
							(string-append 	
								(code-gen param depth constList fvarList)		
								"\tpush rax\n"))			;pushing each parameter to the stack
						(reverse params)))
				
				"\tmov r10, " (number->string params-n) "\n"		
				"\tpush r10\n"								;pushing n - number of params into the stack

				(code-gen proc depth constList fvarList)	;generating procedure code and returning it into rax

				;"\tmov r10, rax\n"
				;"\tTYPE r10\n"								;leaves only the TYPE field in r10

				;"\tcmp r10, T_CLOSURE\n"
				;"\tjne applic_no_closure\n"					;if no closure, then exit
				"\tmov rax, [rax]\n"

				"\tmov r10, rax\n"
				"\tCLOSURE_ENV r10\n"						;leaves only the CLOSURE_ENV field in r10
				"\tpush r10\n"								;pushing the CLOSURE_ENV field into the stack

				"\tmov r10, rax\n"
				"\tCLOSURE_CODE r10\n"						;leaves only the CLOSURE_CODE field in r10
				"\tcall r10\n"								;starting the closure code



				"\tmov r10, [rsp + 1*8]\n"		;[rbp + 3*8]
 				"\tadd r10, 2\n"
 
 				"\n" applic-pop-loop-label ":\n"
 				"\tcmp r10, 0\n"
 				"\tje " applic-pop-loop-end-label "\n"
 				"\tpop r9\n"								;popping 1 param every time
 				"\tdec r10\n"
 				"\tjmp " applic-pop-loop-label "\n"

 				"\n" applic-pop-loop-end-label ":\n"
 				"\tpop r8\n"								;popping NIL

			))))



(define code-gen-tc-applic
    (lambda (pe depth constList fvarList)
        (let* ((proc (cadr pe))
         	  (params (caddr pe))
			  (params-n (length params))
			  (applic-label-num (number->string (applic-label-plusplus)))
         	  (tc-applic-exit-label (string-append "tc_applic_exit_" applic-label-num))
         	  (tc-applic-loop-end-label (string-append "for_copy_args_lbl" applic-label-num))
         	  (tc-applic-loop-start-label (string-append "tc_applic_start_loop_" applic-label-num)))
        (string-append
             	"\tpush " (find-label-by-value (void) constList) "\n"							;pushing VOID to the stack
             	;
				(apply string-append
					(map 
						(lambda (param)
							(string-append 	
								(code-gen param depth constList fvarList)		
								"\tpush rax\n"))			;pushing each parameter to the stack
						(reverse params)))
				
				"\tmov r10, " (number->string params-n) "\n"		
				"\tpush r10\n"								;pushing n - number of params into the stack

				(code-gen proc depth constList fvarList)	;generating procedure code and returning it into rax

				;"\tmov r10, rax\n"
				;"\tTYPE r10\n"								;leaves only the TYPE field in r10

				;"\tcmp r10, T_CLOSURE\n"
				;"\tjne applic_no_closure\n"					;if no closure, then exit
				
				"\tmov rax, [rax]\n"

				"\tmov r10, rax\n"
				"\tCLOSURE_ENV r10\n"						;leaves only the CLOSURE_ENV field in r10
				"\tpush r10\n"								;pushing the CLOSURE_ENV field into the stack
			
				"\tmov rbx, [rbp + 1 * 8]\n"
				"\tpush rbx\n"	

				"\tmov rbx, rbp\n"					;old rbp
				"\tmov rbp, [rbx]\n"

				
				"\tmov r11, rsp\n"					;point to end of the stack

				"\tmov r15, 5\n"			; 5 = old rbp + ret + env + arg-count + void
				"\tadd r15, [rbx + 3 * 8]\n"		;n+5

				"\tmov rdi, " (number->string (+ 4 params-n)) "\n"   ; m elements + ret + env + arg-count + void
			
				 "\n" tc-applic-loop-start-label ":\n"

					"\tcmp rdi, 0\n"
					"\tje "tc-applic-loop-end-label "\n"


					"\tmov r12, rdi\n"
					"\tdec r12\n"
					"\tsal r12, 3\n"

					"\tmov r10, [r11 + r12]\n"
					

					"\tdec r15\n"
					"\tmov r12, r15\n"
					"\tsal r12, 3\n"

					"\tmov [rbx + r12], r10\n"


					"\tdec rdi\n"
					"\tjmp " tc-applic-loop-start-label "\n"


				 "\n" tc-applic-loop-end-label":\n"
			
					"\tmov r12, r15\n"				
					"\tsal r12, 3\n"
					"\tlea rsp, [rbx + r12]\n"
					
		            "\tCLOSURE_CODE rax\n"

		            "\tjmp rax\n"

	        
	             "\n" tc-applic-exit-label":\n"
	            
))))


#|

(define code-gen-tc-applic
    (lambda (pe depth constList fvarList)
        (let* ((proc (cadr pe))
         	  (params (caddr pe))
			  (params-n (length params))
			  (applic-label-num (number->string (applic-label-plusplus)))
         	  (exit_lbl (string-append "exit_app_lbl" applic-label-num))
         	  (for_copy_args (string-append "for_copy_args_lbl" applic-label-num))
         	  (end_of_copy_args (string-append "end_of_copy_args_lbl" applic-label-num))
         	  (tc-applic-pop-loop-end-label (string-append "tc_applic_end_loop" applic-label-num)))
        (string-append
            	"\tpush " (find-label-by-value (void) constList) "\n"							;pushing VOID to the stack
				(apply string-append
					(map 
						(lambda (param)
							(string-append 	
								(code-gen param depth constList fvarList)		
								"\tpush rax\n"))			;pushing each parameter to the stack
						(reverse params)))
				
				"\tmov r10, " (number->string params-n) "\n"		
				"\tpush r10\n"								;pushing n - number of params into the stack

				(code-gen proc depth constList fvarList)	;generating procedure code and returning it into rax

				;"\tmov r10, rax\n"
				;"\tTYPE r10\n"								;leaves only the TYPE field in r10

				;"\tcmp r10, T_CLOSURE\n"
				;"\tjne applic_no_closure\n"					;if no closure, then exit
				"\tmov rax, [rax]\n"

				"\tmov r10, rax\n"
				"\tCLOSURE_ENV r10\n"						;leaves only the CLOSURE_ENV field in r10
				"\tpush r10\n"								;pushing the CLOSURE_ENV field into the stack
			
				"push ret_addr\n" ;save return address


				"mov r8, rbp\n"					;old rbp
				"mov rbp, qword[r8]\n"
				"mov r11,rsp\n"					;point to end of the stack

				"mov r14,24\n"
				"mov r15,4\n"
				"add r15,qword[r8+r14]\n"		;n+4
				"dec r15\n"

				;copy arguments into rbp
				"mov rdi, "(number->string (+ 2 (length params))) "\n" ;m+3	BECAUSE NUL?? +3!
				for_copy_args":\n"
				"mov r12, rdi\n"
				"shl r12, 3\n"

				"mov r10,qword[r11+r12]\n"
				"mov r12,r15\n"
				"shl r12, 3\n"
				"mov qword[r8+r12],r10\n"

				"cmp rdi, 0\n"
				"je "end_of_copy_args"\n"
				"dec rdi\n"
				"dec r15\n"

				"jmp "for_copy_args"\n"
				end_of_copy_args":\n"

				"mov r12,r15\n"				;r15 = n-m (+1 ?)
				"shl r12, 3\n"
				"lea rsp,[r8+r12]\n"

	            "CLOSURE_CODE rax\n"
	            "jmp rax\n"

	            exit_lbl":\n"
	            
	            "add rsp, " (number->string (* 8 (+ 3 (length params))) ) "\n"							;popping NIL
))))

(define code-gen-lambda-simple
	(lambda (pe depth constList fvarList)			;[pe = lambda-simple params body]
		(let* ((closure-number (lambda-label-plusplus))
			   (arg-loop-label 	   (string-append "closure_simple_params_loop_" (number->string closure-number)))
			   (arg-loop-end-label (string-append "closure_simple_params_loop_end_" (number->string closure-number)))
			   (env-loop-label 	   (string-append "closure_simple_env_loop_" (number->string closure-number)))
			   (env-loop-end-label (string-append "closure_simple_env_loop_end_" (number->string closure-number)))
			   (body-label 		   (string-append "closure_simple_body_" (number->string closure-number)))
			   (end-closure-label  (string-append "closure_simple_end_" (number->string closure-number)))
			   (arg-count (number->string (length (cadr pe)))))
			(string-append
					"\tmymalloc " (number->string (+ depth 1)) "\n"		;rbx=malloc(8bytes*(m+1))
					"\tmov rbx, rax\n" 									;rbx=new env
					
					"\tmymalloc " arg-count "\n"						;rcx=malloc(8bytes*(n))
					"\tmov rcx, rax\n" 									;rcx=params list
					
					"\tmymalloc 2\n"									;rax=malloc(8bytes)
					

			;params_loop:
					"\tmov rdx, " arg-count "\n"						;parameter count (arg_count)
					"\tmov rdi, 0\n"									;parameter index

					"\n" arg-loop-label ":\n"
					
					"\tcmp rdi, rdx\n"
					"\tjge " arg-loop-end-label "\n"


					"\tmov r13, rdi\n"									;parameter index
					"\tadd r13, 4\n"									;to skip the 4 elements in the top of the stack
					"\tmov r14, qword [rbp + r13 * 8]\n"				;fetching parameter i value
					"\tmov qword [rcx + rdi * 8], r14\n"				;copying the value of the parameter to the list pointed by rcx

					"\tinc rdi\n"

					"\tjmp " arg-loop-label "\n"

					"\n" arg-loop-end-label ":\n"
			;params_loop-end:

					
					"\tmov [rbx], rcx\n"								;updating first env to be the current
					"\tmov r13, 0\n"									;r13=i=0
					"\tmov r14, 1\n"									;r14j=1

			;env_loop:
					"\n" env-loop-label ":\n"
					
					"\tcmp r13, " (number->string depth) "\n"
					"\tjge " env-loop-end-label "\n"

					"\tmov rdx, qword [rbp + 2 * 8]\n"					;rdx=old env
					"\tmov rdi, qword [rdx + r13 * 8]\n"				;rdi=current env
					"\tmov qword [rbx + r14 * 8], rdi\n"				;updating current env to be the one in rdi
					"\tinc r13\n"										;i++
					"\tinc r14\n"										;j++

					"\tjmp " env-loop-label "\n"
					"\n\n" env-loop-end-label ":\n\n"
			;env_loop_end:

					"\tmov rcx, " body-label "\n"
					"\tMAKE_LITERAL_CLOSURE rax, rbx, rcx\n"
					;"\tl2:mov rax, qword [rax]\n"
					"\tjmp " end-closure-label "\n"


					"\n\n" body-label ":\n"

					"\tpush rbp\n"
					"\tmov rbp, rsp\n"
					
					(code-gen (caddr pe) (+ depth 1) constList fvarList)
					
					"\tleave\n"
					"\tret\n"

					"\n\n" end-closure-label ":\n\n"))))


(define code-gen-lambda-opt
	(lambda (pe depth constList fvarList)			;[pe = lambda-opt params rest body] ;;;;;;; in lambda-opt sum of args is (length paramas)+1 ,+1 present list of optinals params
		(let* ((closure-number (lambda-label-plusplus))
			   (arg-loop-label 	   (string-append "closure_opt_arg_loop_" (number->string closure-number)))
			   (arg-loop-end-label (string-append "closure_opt_arg_loop_end_" (number->string closure-number)))
			   (env-loop-label 	   (string-append "closure_opt_env_loop_" (number->string closure-number)))
			   (env-loop-end-label (string-append "closure_opt_env_loop_end_" (number->string closure-number)))
			   (body-label 		   (string-append "closure_opt_body_" (number->string closure-number)))
			   (end-closure-label  (string-append "closure_opt_end_" (number->string closure-number)))
			   (arg-count 		   (number->string (length (cadr pe))))
			   (fix-stack-label	   (string-append "closure_opt_fix_stack_loop_" (number->string closure-number)))
			   (fix-stack-label-end (string-append "closure_opt_fix_stack_loop_end_" (number->string closure-number))))
			(string-append
					"\tmymalloc " (number->string (+ depth 1)) "\n"		;rbx=malloc(8bytes*(m+1)) --> env
					"\tmov rbx, rax\n" 									;rbx=malloc(8bytes*(m+1)) --> env
					
					"\tmymalloc " arg-count "\n"							;rcx=malloc(8bytes*(n))
					"\tmov rcx, rax\n" 									;rcx=malloc(8bytes*(n))
					
					"\tmymalloc 2\n"									;rax=malloc(8bytes)
					

			;arg_loop:
					"\tmov rdx, " arg-count "\n"			;parameter count (arg_count)
					"\tmov rdi, 0\n"					;parameter index

					"\n" arg-loop-label ":\n"
					
					"\tcmp rdi, rdx\n"
					"\tjge " arg-loop-end-label "\n"


					"\tmov r13, rdi\n"					;parameter index
					"\tadd r13, 4\n"					;to skip the 4 elements in the top of the stack
					"\tmov r14, qword [rbp + r13 * 8]\n"	;fetching parameter i value
					"\tmov qword [rcx + rdi * 8], r14\n"	;copying the value of the parameter to the list pointed by rcx

					"\tinc rdi\n"

					"\tjmp " arg-loop-label "\n"
					"\n" arg-loop-end-label ":\n"
			;arg_loop-end:

					
					"\tmov [rbx], rcx\n"				;updating first env to be the current
					"\tmov r13, 0\n"					;i=0
					"\tmov r14, 1\n"					;j=1

			;env_loop:
					"\n" env-loop-label ":\n"
					
					"\tcmp r13, " (number->string depth) "\n"
					"\tjge " env-loop-end-label "\n"

					"\tmov rdx, qword [rbp + 2 * 8]\n"			;rdx=env
					"\tmov rdi, qword [rdx + r13 * 8]\n"		;rdi=current env
					"\tmov qword [rbx + r14 * 8], rdi\n"		;updating current env to be the one in rdi
					"\tinc r13\n"						;i++
					"\tinc r14\n"						;j++

					"\tjmp " env-loop-label "\n"
					"\n\n" env-loop-end-label ":\n\n"
			;env_loop_end:

					"\tmov rcx, " body-label "\n"
					"\tMAKE_LITERAL_CLOSURE rax, rbx, rcx\n"
					;"\tmov rax, qword [rax]\n"
					"\tjmp " end-closure-label "\n"


					"\n\n" body-label ":\n"

					"\tpush rbp\n"
					"\tmov rbp, rsp\n"

					;;;;;TO-CHECK ->>> should we add a continue conditional?
					;"\tcmp qword [rbp + 3 * 8]," arg-count "\n"
     				;"\tjl lambda_opt_wrong_args\n"


     				;build a list of rest params
					"\tmov rbx, " (find-label-by-value '() constList) "\n"							;rbx = NIL - end of list

					"\tmov rdi, qword [rbp +3*8]\n" 	;rdi = n+m ->>> i, cur arg
					"\tmov rdx, " (number->string (string->number arg-count)) "\n"			;rdx = n
					"\n" fix-stack-label ":\n"

					"\tcmp rdi, rdx\n"
					"\tjle " fix-stack-label-end "\n"

					"\tmymalloc 1\n"				;malloc for next opt-arg
					"\tmov rcx, rax\n"				;save the malloc poiter in rcx 

					"\tmov r11, rbp\n"				
					"\tadd r11, 4*8\n"				;r11 point to first arg in stack (offset)
					
					"\tmov r10, rdi\n"				;r10 is helper for point of arg[i]
					"\tdec r10\n"
					"\tshl r10, 3\n"				;now offset+r10 = address of curr arg				
					"\tadd r11, r10\n"				;rdx = address of arg[i]
					"\tmov r11, qword [r11]\n"		;rdx = value of arg[i]

					"\tMAKE_MALLOC_LITERAL_PAIR rax, r11, rbx\n"				;rax = target, rbx = cdr, rcx = car
					"\tmov rbx, rax\n"										;rbx ponints to the new pair as cdr for the new allocate in next iteration
					
					"\tdec rdi\n"					;at-least 1 arg
					"\tjmp " fix-stack-label "\n"

					"\n" fix-stack-label-end ":\n"
					"\tmov qword [rbp+4*8+rdx*8], rbx\n"	;add the list in stack after const params (not optinals)
					"\tmov qword [rbp + 3*8], " (number->string (+ 1 (string->number arg-count))) "\n"


					(code-gen (cadddr pe) (+ depth 1) constList fvarList)
					
					"\tleave\n"
					;"\tpop rbp\n"
					"\tret\n"

					"\n\n" end-closure-label ":\n\n"))))

(define code-gen-tc-applic2
  (lambda (pe depth constList fvarList)
    (let* ((applic-label-num (number->string (applic-label-plusplus)))
			   (tc-applic-frame-loop-label (string-append "tc_applic_frame_loop_" applic-label-num))
			   (tc-applic-frame-loop-end-label (string-append "tc_applic_frame_loop_end_" applic-label-num))
		)
      (string-append
        "\n;;;;;;;; START TC-APPLIC\n"
        (apply string-append
      "push SOB_NIL\n"
    (map
      (lambda (x)
        (string-append
    (code-gen x depth constList fvarList)
    "push rax\n"))
      (reverse (caddr pe))))
      "mov rcx, "(number->string (+ 1 (length (caddr pe))))
      "\npush rcx\n"
      (code-gen (cadr pe) depth constList fvarList)
      "
      mov rcx,rax
      TYPE rcx
      cmp rcx,T_CLOSURE
      jne applic_no_closure
      mov rbx,rax
      CLOSURE_ENV rbx
      push rbx
      
      mov r8,rbp



      mov r10, qword [rbp+8*3]
      
      shl r10,3
      add r10,3*8
      add r10,r8
      
      push qword [rbp+8]
      mov rbp,qword [rbp]


      mov r9,qword [rsp+2*8]
      add r9,3
      mov rsi,0
      

       " 
       tc-applic-frame-loop-label 
       ":\n
       cmp rsi,r9
       je " tc-applic-frame-loop-end-label "\n
       
       mov rcx,r8

       shl rsi,3
       sub rcx, rsi
       sub rcx,8
       mov rcx,qword [rcx]

       mov rdx,r10
       sub rdx,rsi
       mov qword [rdx],rcx
       shr rsi,3

       inc rsi

       jmp "tc-applic-frame-loop-label "\n
        " tc-applic-frame-loop-end-label ":\n
        sub rsi,1
  shl rsi,3
  sub r10,rsi
  mov rsp,r10
          CLOSURE_CODE rax
          jmp rax "
         "\n ;;;;;;;; END TC-APPLIC   \n"  

))))

(define code-gen-tc-applic
	(lambda (pe depth constList fvarList)
		(let* ((proc (cadr pe))
			   (params (caddr pe))
			   (params-n (length params))
			   (applic-label-num (number->string (applic-label-plusplus)))
			   (tc-applic-frame-loop-label (string-append "tc_applic_frame_loop_" applic-label-num))
			   (tc-applic-frame-loop-end-label (string-append "tc_applic_frame_loop_end_" applic-label-num))
			  )
			(string-append
				"\tpush SOB_NIL\n"							;pushing VOID to the stack
				(apply string-append
					(map 
						(lambda (param)
							(string-append 	
								(code-gen param depth constList fvarList)		
								"\tpush rax\n"))			;pushing each parameter to the stack
						(reverse params)))
				
				"\tmov r10, " (number->string (+ 1 params-n)) "\n"		;;; to params-n or params-n + 1
				"\tpush r10\n"						;;; to params-n or params-n + 1			;pushing n - number of params into the stack

				(code-gen proc depth constList fvarList)	;generating procedure code and returning it into rax

				"\tmov r10, rax\n"
				"\tTYPE r10\n"								;leaves only the TYPE field in r10

				"\tcmp r10, T_CLOSURE\n"
				"\tjne applic_no_closure\n"					;if no closure, then exit

				"\tmov r10, rax\n"
				"\tCLOSURE_ENV r10\n"						;leaves only the CLOSURE_ENV field in r10
				"\tpush r10\n"								;pushing the CLOSURE_ENV field into the stack


				"\tmov rbx, rbp\n"

				
				"\tmov r10, qword [rbp + 3 * 8]\n"			;arg_count
			
				"\tshl r10, 3\n"
				"\tadd r10, 3 * 8\n"
				"\tadd r10, rbx\n"

			;	"\tadd r10, 3\n"

				"\tpush qword [rbp + 8]\n"
				"\tmov rbp, qword [rbp]\n"
			;	

				"\tmov r11, qword [rsp + 2 * 8]\n"
				"\tadd r11, 3\n"


				"\tmov rdi, 0\n"
				
				"\n" tc-applic-frame-loop-label ":\n"
				
				"\tcmp rdi, r11\n"
				"\tje " tc-applic-frame-loop-end-label "\n"

				"\tmov rdx, rbx\n"		;rdx=past rbp
				
				"\tshl rdi, 3\n"
				"\tsub rdx, rdi\n"
				"\tsub rdx, 8\n"
				"\tmov rdx, qword [rdx]\n"
				
				"\tmov r12, r10\n"
				"\tsub r12, rdi\n"
				"\tmov qword [r12], rdx\n"
				"\tshl rdi, 3\n"

				"\tinc rdi\n"

				"\tjmp " tc-applic-frame-loop-label "\n"

				"\n" tc-applic-frame-loop-end-label ":\n"

				"\tdec rdi\n"			;to cancel the last "inc rdi"
				"\tshl rdi, 3\n"
				"\tsub r10, rdi\n"
				
				"\tmov rsp, r10\n"
				
				"\tCLOSURE_CODE rax\n"
				"\tjmp rax\n"			;jumping to closure code, and not coming back !!!
			)
		)
	))
					
|#

(define code-gen
	(lambda (pe depth constList fvarList)
		(string-append
			"backup_registers\n\n"
			(code-gen-helper pe depth constList fvarList)
			"restore_registers\n\n"
			)))


(define code-gen-helper
	(lambda (pe depth constList fvarList)
		(let ((type (car pe)))
			(cond ((eq? type 'const) (code-gen-const pe constList))
	          	  ((eq? type 'if3) 	 (code-gen-if3 pe depth constList fvarList))
	          	  ((eq? type 'seq) (code-gen-seq  (cadr pe) depth constList fvarList))
	          	  ((eq? type 'or) (code-gen-or (cadr pe) depth constList fvarList))
	          	  ((eq? type 'pvar) (code-gen-pvar pe depth constList fvarList))
	          	  ((eq? type 'bvar) (code-gen-bvar pe depth constList fvarList))
	              ((eq? type 'define) (code-gen-def pe depth constList fvarList))
	              ((eq? type 'fvar) (code-gen-fvar pe depth constList fvarList))
	          	  ((eq? type 'set) (code-gen-set pe depth constList fvarList))
	          	  ((eq? type 'box) (code-gen-box pe depth constList fvarList))
	          	  ((eq? type 'box-set) (code-gen-box-set pe depth constList fvarList))
	          	  ((eq? type 'box-get) (code-gen-box-get pe depth constList fvarList))
	          	  ((eq? type 'lambda-simple) (code-gen-lambda-simple pe depth constList fvarList))
	          	  ((eq? type 'lambda-opt) (code-gen-lambda-opt pe depth constList fvarList))
				  ((eq? type 'applic) (code-gen-applic pe depth constList fvarList))
	          	  ((eq? type 'tc-applic) (code-gen-tc-applic pe depth constList fvarList))

	          (else 'error)))))


;####<---CODE-GENERATOR--->####



(define write-to-file 
	(lambda (outputFile str)
		(let ((outputPort (open-output-file outputFile)))
				(begin (display str outputPort)
					   (close-output-port outputPort)))))


;#########################################




(define file->list
	(lambda (in-file)
		(let ((in-port (open-input-file in-file)))
			(letrec ((run
					(lambda ()
						(let ((ch (read-char in-port)))
							(if (eof-object? ch)
								(begin
									(close-input-port in-port)
									'())
								(cons ch (run)))))))
			(run)))))



(define pipeline
	(lambda (s)
		((star <sexpr>) s
			(lambda (m r)
				(map (lambda (e)
					(annotate-tc
						(pe->lex-pe
							(box-set
								(remove-applic-lambda-nil
									(parse e))))))
					m))
				(lambda (f) 'fail))))


(define prologue
	(let ()
	(string-append
		"\n"
		"%define param(offset) qword [rbp + offset]\n"
		"\n"
		"struc scmframe\n"
		".old_rbp: resq 1\n"
		".ret_addr: resq 1\n"
		".env: resq 1\n"
		".arg_count: resq 1\n"
		".A0: resq 1\n"
		".A1: resq 1\n"
		".A2: resq 1\n"
		".A3: resq 1\n"
		".A4: resq 1\n"
		".A5: resq 1\n"
		"endstruc\n"
		"\n"
		"%define old_rbp param(scmframe.old_rbp)\n"
		"%define ret_addr param(scmframe.ret_addr)\n"
		"%define env param(scmframe.env)\n"
		"%define arg_count param(scmframe.arg_count)\n"
		"%define A0 param(scmframe.A0)\n"
		"%define A1 param(scmframe.A1)\n"
		"%define A2 param(scmframe.A2)\n"
		"%define A3 param(scmframe.A3)\n"
		"%define A4 param(scmframe.A4)\n"
		"%define A5 param(scmframe.A5)\n"
		"%define An(n) qword [rbp + 8 * (n + 4)]\n"
		"\n"
		"%macro mymalloc 1\n"				;mymalloc 3 --> allocate 3 addresses of 64bit each
		    "push rbx\n"
		    "push rcx\n"
		    "push rdx\n"
		    "push rdi\n"
		    "push rsi\n"
		    "push r8\n"
		    "push r9\n"
		    "push r10\n"
		    "push r11\n"
		    "push r12\n"
		    "push r13\n"
		    "push r14\n"
		    "push r15\n"
		    "mov rbx, %1\n"
		    "sal rbx, 3\n"
		    "mov rdi,rbx\n"
		    "call malloc\n"
		    "pop r15\n"
		    "pop r14\n"
		    "pop r13\n"
		    "pop r12\n"
		    "pop r11\n"
		    "pop r10\n"
		    "pop r9\n"
		    "pop r8\n"
		    "pop rsi\n"
		    "pop rdi\n"
		    "pop rdx\n"
		    "pop rcx\n"
		    "pop rbx\n"
		"%endmacro\n"

		"%macro mymalloc2 1\n"				;mymalloc 1 --> allocate 1 byte
		    "push rbx\n"
		    "push rcx\n"
		    "push rdx\n"
		    "push rdi\n"
		    "push rsi\n"
		    "push r8\n"
		    "push r9\n"
		    "push r10\n"
		    "push r11\n"
		    "push r12\n"
		    "push r13\n"
		    "push r14\n"
		    "push r15\n"
		    ;"mov rbx, %1\n"
		    ;"sal rbx, 3\n"
		    "mov rdi,%1\n"
		    "call malloc\n"
		    "pop r15\n"
		    "pop r14\n"
		    "pop r13\n"
		    "pop r12\n"
		    "pop r11\n"
		    "pop r10\n"
		    "pop r9\n"
		    "pop r8\n"
		    "pop rsi\n"
		    "pop rdi\n"
		    "pop rdx\n"
		    "pop rcx\n"
		    "pop rbx\n"
		"%endmacro\n"

		"%macro backup_registers 0\n"				;mymalloc 3 --> allocate 3 addresses of 64bit each
		    "push rbx\n"
		    "push rcx\n"
		    "push rdx\n"
		    "push rdi\n"
		    "push rsi\n"
		    "push r8\n"
		    "push r9\n"
		    "push r10\n"
		    "push r11\n"
		    "push r12\n"
		    "push r13\n"
		    "push r14\n"
		    "push r15\n"
		"%endmacro\n"

	"%macro restore_registers 0\n"				;mymalloc 3 --> allocate 3 addresses of 64bit each
		    "pop r15\n"
		    "pop r14\n"
		    "pop r13\n"
		    "pop r12\n"
		    "pop r11\n"
		    "pop r10\n"
		    "pop r9\n"
		    "pop r8\n"
		    "pop rsi\n"
		    "pop rdi\n"
		    "pop rdx\n"
		    "pop rcx\n"
		    "pop rbx\n"
		"%endmacro\n"

		;GCD USE RAX, RBX, RDX and return result in RDI
		;first = arg one  ,  second = arg two ,  result in rdi
		"%macro GCD 2\n"
	
			"push rax\n"
			"push rbx\n"
			"push rdx\n"

			"mov rdx, 0\n"
			"mov rax, %1\n" ; first
			"mov rbx, %2\n" ; second
			;"iabs rax\n"
			;"iabs rbx\n"
			"cmp rax, rbx\n"
			"jge .loop\n"
			"xchg rax, rbx\n"
			
		".loop:\n"
			"cmp rbx, 0\n"
			"je .done\n"
			"mov rdx, 0\n"
			"div rbx\n"
			"mov rax, rbx\n"
			"mov rbx, rdx\n"
			"jmp .loop\n"

		".done:\n"
			"mov rdi, rax\n"
			
			"pop rdx\n"
			"pop rbx\n"
			"pop rcx\n"
		"%endmacro\n"


		"\n"
		"\n"
		"%define T_UNDEFINED 0\n"
		"%define T_VOID 1\n"
		"%define T_NIL 2\n"
		"%define T_INTEGER 3\n"
		"%define T_FRACTION 4\n"
		"%define T_BOOL 5\n"
		"%define T_CHAR 6\n"
		"%define T_STRING 7\n"
		"%define T_SYMBOL 8\n"
		"%define T_CLOSURE 9\n"
		"%define T_PAIR 10\n"
		"%define T_VECTOR 11\n"
		"\n"
		"%define CHAR_NUL 0\n"
		"%define CHAR_TAB 9\n"
		"%define CHAR_NEWLINE 10\n"
		"%define CHAR_PAGE 12\n"
		"%define CHAR_RETURN 13\n"
		"%define CHAR_SPACE 32\n"
		"\n"
		"%define TYPE_BITS 4\n"
		"%define WORD_SIZE 64\n"
		"\n"
		"%define MAKE_LITERAL(type, lit) ((lit << TYPE_BITS) | type)\n"
		"\n"
		"\n"
		"%define MAKE_LITERAL_FRACTION(numerator_label, denominator_label) (((((numerator_label - start_of_data) << ((WORD_SIZE - TYPE_BITS) >> 1)) | (denominator_label - start_of_data)) << TYPE_BITS) | T_FRACTION)\n"
		"\n"
		"%macro NUMERATOR 1\n"
		    "DATA_UPPER %1\n"
		    "add %1, start_of_data\n"
		"%endmacro\n"
		"\n"
		"%macro DENOMINATOR 1\n"
		    "DATA_LOWER %1\n"
		    "add %1, start_of_data\n"
		"%endmacro\n"
		"\n"
		"\n"

		"\n"
		"%macro TYPE 1\n"
			"and %1, ((1 << TYPE_BITS) - 1) \n"
		"%endmacro\n"
		"\n"
		"%macro DATA 1\n"
			"sar %1, TYPE_BITS\n"
		"%endmacro\n"
		"\n"
		"%macro DATA_UPPER 1\n"
			"sar %1, (((WORD_SIZE - TYPE_BITS) >> 1) + TYPE_BITS)\n"
		"%endmacro\n"
		"\n"
		"%macro DATA_LOWER 1\n"
			"sal %1, ((WORD_SIZE - TYPE_BITS) >> 1)\n"
			"DATA_UPPER %1\n"
		"%endmacro\n"
		"\n"
		"%define MAKE_LITERAL_PAIR(car, cdr) (((((car - start_of_data) << ((WORD_SIZE - TYPE_BITS) >> 1)) | (cdr - start_of_data)) << TYPE_BITS) | T_PAIR)\n"
		"\n"
		"%macro CAR 1\n"
			"DATA_UPPER %1\n"
			"add %1, start_of_data\n"
			"mov %1, qword [%1]\n"
		"%endmacro\n"
		"\n"
		"%macro CDR 1\n"
			"DATA_LOWER %1\n"
			"add %1, start_of_data\n"
			"mov %1, qword [%1]\n"
		"%endmacro\n"
		"\n"
		";;; MAKE_LITERAL_CLOSURE target, env, code\n"
		"%macro MAKE_LITERAL_CLOSURE 3\n"
			"push rax\n"
			"push rbx\n"
			"mov rax, %1\n"
			"mov qword [rax], %2\n"
			"sub qword [rax], start_of_data\n"
			"shl qword [rax], ((WORD_SIZE - TYPE_BITS) >> 1)\n"
			"lea rbx, [rax + 8]\n"

			"sub rbx, start_of_data\n"

			"or qword [rax], rbx\n"
			"shl qword [rax], TYPE_BITS\n"
			"or qword [rax], T_CLOSURE\n"
			"mov qword [rax + 8], %3\n"
			"pop rbx\n"
			"pop rax\n"
		"%endmacro\n"

		"\n"

		";;; MAKE_MALLOC_LITERAL_FRACTION target-address, car-address, cdr-address\n"
		"%macro MAKE_MALLOC_LITERAL_FRACTION 3\n"
			"push rax\n" 
			"push rbx\n"
			"mov rax, %1\n" 
			"mov qword [rax], %2\n"
			"sub qword [rax], start_of_data\n"
			"shl qword [rax], ((WORD_SIZE - TYPE_BITS) >> 1)\n"
			"mov rbx, %3\n"
			"sub rbx, start_of_data\n"
			"or qword [rax], rbx\n"
			"shl qword [rax], TYPE_BITS\n"
			"or qword [rax], T_FRACTION\n"
			"pop rbx\n"
			"pop rax\n"
		"%endmacro\n"
		"\n"

		"\n";string_target = label string of synbol
		"%define MAKE_LITERAL_SYMBOL(string_target) (((string_target - start_of_data) << TYPE_BITS ) | T_SYMBOL)\n"

		;first = target, second= string label
		"%macro MAKE_LITERAL_SYMBOL_RUNTIME 2 \n"
				"sub %2, start_of_data\n"
				"shl %2, TYPE_BITS\n"
				"or %2, T_SYMBOL\n"
				"mov [%1], %2\n"
		"%endmacro\n"

		"\n"
		";;; MAKE_MALLOC_LITERAL_PAIR target-address, car-address, cdr-address\n"
		"%macro MAKE_MALLOC_LITERAL_PAIR 3\n"
			"push rax\n" 
			"push rbx\n"
			"mov rax, %1\n" 
			"mov qword [rax], %2\n"
			"sub qword [rax], start_of_data\n"
			"shl qword [rax], ((WORD_SIZE - TYPE_BITS) >> 1)\n"
			"mov rbx, %3\n"
			"sub rbx, start_of_data\n"
			"or qword [rax], rbx\n"
			"shl qword [rax], TYPE_BITS\n"
			"or qword [rax], T_PAIR\n"
			"pop rbx\n"
			"pop rax\n"
		"%endmacro\n"
		"\n"
		

		"\n"
		"%macro CLOSURE_ENV 1\n"
			"DATA_UPPER %1\n"
			"add %1, start_of_data\n"
		"%endmacro\n"
		"\n"
		"%macro CLOSURE_CODE 1\n"
			"DATA_LOWER %1\n"
			"add %1, start_of_data\n"
			"mov %1, qword [%1]\n"
		"%endmacro\n"
		"\n"
		"%macro MAKE_LITERAL_STRING 1+\n"
			"dq (((((%%LstrEnd - %%Lstr) << ((WORD_SIZE - TYPE_BITS) >> 1)) | (%%Lstr - start_of_data)) << TYPE_BITS) | T_STRING)\n"
			"%%Lstr:\n"
			"db %1\n"
			"%%LstrEnd:\n"
		"%endmacro\n"
		"\n"
		"%macro STRING_LENGTH 1\n"
			"DATA_UPPER %1\n"
		"%endmacro\n"
		"\n"
		"%macro STRING_ELEMENTS 1\n"
			"DATA_LOWER %1\n"
			"add %1, start_of_data\n"
		"%endmacro\n"
		"\n"
		";;; STRING_REF dest, src, index\n"
		";;; dest cannot be RAX! (fix this!)\n"
		"%macro STRING_REF 3\n"
			"push rax\n"
			"mov rax, %2\n"
			"STRING_ELEMENTS rax\n"
			"add rax, %3\n"
			"mov %1, byte [rax]\n"
			"pop rax\n"
		"%endmacro\n"
		"\n"
		"%macro MAKE_LITERAL_VECTOR 1+\n"
			"dq ((((((%%VecEnd - %%Vec) >> 3) << ((WORD_SIZE - TYPE_BITS) >> 1)) | (%%Vec - start_of_data)) << TYPE_BITS) | T_VECTOR)\n"
			"%%Vec:\n"
			"dq %1\n"
			"%%VecEnd:\n"
		"%endmacro\n"
		"\n"

		"%macro MAKE_LITERAL_VECTOR 0\n"
		"dq MAKE_LITERAL(T_VECTOR,0)\n"
		"%endmacro\n"

		"\n"
		"%macro VECTOR_LENGTH 1\n"
			"DATA_UPPER %1\n"
		"%endmacro\n"
		"\n"
		"%macro VECTOR_ELEMENTS 1\n"
			"DATA_LOWER %1\n"
			"add %1, start_of_data\n"
		"%endmacro\n"
		"\n"
		";;; VECTOR_REF dest, src, index\n"
		";;; dest cannot be RAX! (fix this!)\n"
		"%macro VECTOR_REF 3\n"
			"mov %1, %2\n"
			"VECTOR_ELEMENTS %1\n"
			"lea %1, [%1 + %3*8]\n"
			"mov %1, qword [%1]\n"
			"mov %1, qword [%1]\n"
		"%endmacro\n"
		"\n"
		"%define SOB_UNDEFINED MAKE_LITERAL(T_UNDEFINED, 0)\n"
		"%define SOB_VOID MAKE_LITERAL(T_VOID, 0)\n"
		"%define SOB_FALSE MAKE_LITERAL(T_BOOL, 0)\n"
		"%define SOB_TRUE MAKE_LITERAL(T_BOOL, 1)\n"
		"%define SOB_NIL MAKE_LITERAL(T_NIL, 0)\n"
		"\n"
		"\n"
		"\n"

		"section .data\n\n"

		"start_of_data:\n\n"
	)))

(define epilog 
	(let ()
		(string-append
			"\n"
			"write_sob_undefined:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .undefined\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".undefined:\n"
				"db \"#<undefined>\", 0\n"
			"\n"
			"write_sob_integer:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rsi, qword [rbp + 8 + 1*8]\n"
				"sar rsi, TYPE_BITS\n"
				"mov rdi, .int_format_string\n"
				"mov rax, 0\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".int_format_string:\n"
				"db \"%ld\", 0\n"
			"\n"
			"write_sob_char:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rsi, qword [rbp + 8 + 1*8]\n"
				"DATA rsi\n"
			"\n"
				"cmp rsi, CHAR_NUL\n"
				"je .Lnul\n"
			"\n"
				"cmp rsi, CHAR_TAB\n"
				"je .Ltab\n"
			"\n"
				"cmp rsi, CHAR_NEWLINE\n"
				"je .Lnewline\n"
			"\n"
				"cmp rsi, CHAR_PAGE\n"
				"je .Lpage\n"
			"\n"
				"cmp rsi, CHAR_RETURN\n"
				"je .Lreturn\n"
			"\n"
				"cmp rsi, CHAR_SPACE\n"
				"je .Lspace\n"
				"jg .Lregular\n"
			"\n"
				"mov rdi, .special\n"
				"jmp .done	\n"
			"\n"
			".Lnul:\n"
				"mov rdi, .nul\n"
				"jmp .done\n"
			"\n"
			".Ltab:\n"
				"mov rdi, .tab\n"
				"jmp .done\n"
			"\n"
			".Lnewline:\n"
				"mov rdi, .newline\n"
				"jmp .done\n"
			"\n"
			".Lpage:\n"
				"mov rdi, .page\n"
				"jmp .done\n"
			"\n"
			".Lreturn:\n"
				"mov rdi, .return\n"
				"jmp .done\n"
			"\n"
			".Lspace:\n"
				"mov rdi, .space\n"
				"jmp .done\n"
			"\n"
			".Lregular:\n"
				"mov rdi, .regular\n"
				"jmp .done\n"
			"\n"
			".done:\n"
				"mov rax, 0\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".space:\n"
				"db \"#\\space\", 0\n"
			".newline:\n"
				"db \"#\\newline\", 0\n"
			".return:\n"
				"db \"#\\return\", 0\n"
			".tab:\n"
				"db \"#\\tab\", 0\n"
			".page:\n"
				"db \"#\\page\", 0\n"
			".nul:\n"
				"db \"#\\nul\", 0\n"
			".special:\n"
				"db \"#\\x%02x\", 0\n"
			".regular:\n"
				"db \"#\\%c\", 0\n"
			"\n"
			"write_sob_void:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .void\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".void:\n"
				"db \"#<void>\", 0\n"
			"	\n"
			"write_sob_bool:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				"cmp rax, SOB_FALSE\n"
				"je .sobFalse\n"
			"	\n"
				"mov rdi, .true\n"
				"jmp .continue\n"
			"\n"
			".sobFalse:\n"
				"mov rdi, .false\n"
			"\n"
			".continue:\n"
				"mov rax, 0\n"
				"call printf	\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data			\n"
			".false:\n"
				"db \"#f\", 0\n"
			".true:\n"
				"db \"#t\", 0\n"
			"\n"
			"write_sob_nil:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .nil\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".nil:\n"
				"db \"()\", 0\n"
			"\n"
			"write_sob_string:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .double_quote\n"
				"call printf\n"
			"\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				"mov rcx, rax\n"
				"STRING_LENGTH rcx\n"
				"STRING_ELEMENTS rax\n"
			"\n"
			".loop:\n"
				"cmp rcx, 0\n"
				"je .done\n"
				"mov bl, byte [rax]\n"
				"and rbx, 0xff\n"
			"\n"
				"cmp rbx, CHAR_TAB\n"
				"je .ch_tab\n"
				"cmp rbx, CHAR_NEWLINE\n"
				"je .ch_newline\n"
				"cmp rbx, CHAR_PAGE\n"
				"je .ch_page\n"
				"cmp rbx, CHAR_RETURN\n"
				"je .ch_return\n"
				"cmp rbx, CHAR_SPACE\n"
				"jl .ch_hex\n"
			"	\n"
				"mov rdi, .fs_simple_char\n"
				"mov rsi, rbx\n"
				"jmp .printf\n"
			"	\n"
			".ch_hex:\n"
				"mov rdi, .fs_hex_char\n"
				"mov rsi, rbx\n"
				"jmp .printf\n"
			"	\n"
			".ch_tab:\n"
				"mov rdi, .fs_tab\n"
				"mov rsi, rbx\n"
				"jmp .printf\n"
			"	\n"
			".ch_page:\n"
				"mov rdi, .fs_page\n"
				"mov rsi, rbx\n"
				"jmp .printf\n"
			"	\n"
			".ch_return:\n"
				"mov rdi, .fs_return\n"
				"mov rsi, rbx\n"
				"jmp .printf\n"
			"\n"
			".ch_newline:\n"
				"mov rdi, .fs_newline\n"
				"mov rsi, rbx\n"
			"\n"
			".printf:\n"
				"push rax\n"
				"push rcx\n"
				"mov rax, 0\n"
				"call printf\n"
				"pop rcx\n"
				"pop rax\n"
			"\n"
				"dec rcx\n"
				"inc rax\n"
				"jmp .loop\n"
			"\n"
			".done:\n"
				"mov rax, 0\n"
				"mov rdi, .double_quote\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"section .data\n"
			".double_quote:\n"
				"db '\"', 0\n"
			".fs_simple_char:\n"
				"db \"%c\", 0\n"
			".fs_hex_char:\n"
				"db \"\\x%02x;\", 0	\n"
			".fs_tab:\n"
				"db \"\\t\", 0\n"
			".fs_page:\n"
				"db \"\\f\", 0\n"
			".fs_return:\n"
				"db \"\\r\", 0\n"
			".fs_newline:\n"
				"db \"\\n\", 0\n"
			"\n"
			"write_sob_pair:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .open_paren\n"
				"call printf\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				"CAR rax\n"
				"push rax\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				"CDR rax\n"
				"push rax\n"
				"call write_sob_pair_on_cdr\n"
				"add rsp, 1*8\n"
				"mov rdi, .close_paren\n"
				"mov rax, 0\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".open_paren:\n"
				"db \"(\", 0\n"
			".close_paren:\n"
				"db \")\", 0\n"
			"\n"
			"write_sob_pair_on_cdr:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rbx, qword [rbp + 8 + 1*8]\n"
				"mov rax, rbx\n"
				"TYPE rbx\n"
				"cmp rbx, T_NIL\n"
				"je .done\n"
				"cmp rbx, T_PAIR\n"
				"je .cdrIsPair\n"
				"push rax\n"
				"mov rax, 0\n"
				"mov rdi, .dot\n"
				"call printf\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"jmp .done\n"
			"\n"
			".cdrIsPair:\n"
				"mov rbx, rax\n"
				"CDR rbx\n"
				"push rbx\n"
				"CAR rax\n"
				"push rax\n"
				"mov rax, 0\n"
				"mov rdi, .space\n"
				"call printf\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"call write_sob_pair_on_cdr\n"
				"add rsp, 1*8\n"
			"\n"
			".done:\n"
				"leave\n"
				"ret\n"
			"\n"
			"section .data\n"
			".space:\n"
				"db \" \", 0\n"
			".dot:\n"
				"db \" . \", 0\n"
			"\n"
			"write_sob_vector:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, 0\n"
				"mov rdi, .fs_open_vector\n"
				"call printf\n"
			"\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				"mov rcx, rax\n"
				"VECTOR_LENGTH rcx\n"
				"cmp rcx, 0\n"
				"je .done\n"
				"VECTOR_ELEMENTS rax\n"
			"\n"
				"push rcx\n"
				"push rax\n"
				"mov rax, qword [rax]\n"
				"push qword [rax]\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"pop rax\n"
				"pop rcx\n"
				"dec rcx\n"
				"add rax, 8\n"
			"\n"
			".loop:\n"
				"cmp rcx, 0\n"
				"je .done\n"
			"\n"
				"push rcx\n"
				"push rax\n"
				"mov rax, 0\n"
				"mov rdi, .fs_space\n"
				"call printf\n"
			"	\n"
				"pop rax\n"
				"push rax\n"
				"mov rax, qword [rax]\n"
				"push qword [rax]\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"pop rax\n"
				"pop rcx\n"
				"dec rcx\n"
				"add rax, 8\n"
				"jmp .loop\n"
			"\n"
			".done:\n"
				"mov rax, 0\n"
				"mov rdi, .fs_close_vector\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"
			"section	.data\n"
			".fs_open_vector:\n"
				"db \"#(\", 0\n"
			".fs_close_vector:\n"
				"db \")\", 0\n"
			".fs_space:\n"
				"db \" \", 0\n"
			"\n"
			

			"write_sob_symbol:\n"
				"push rbp\n"
				"mov rbp, rsp\n"

				"mov rax, qword [rbp + 8 + 1*8]\n"
				"DATA rax\n"
				"add rax, start_of_data\n"
				"mov rax, qword [rax]\n"

				"mov rcx, rax\n"
				"STRING_LENGTH rcx\n"
				"STRING_ELEMENTS rax\n"

			".loop:\n"
				"cmp rcx, 0\n"
				"je .done\n"
				"mov bl, byte [rax]\n"
				"and rbx, 0xff\n"

				"mov rdi, .simple_char\n"
				"mov rsi, rbx\n"

				"push rax\n"
				"push rcx\n"
				"mov rax, 0\n"
				"call printf\n"
				"pop rcx\n"
				"pop rax\n"

				"dec rcx\n"
				"inc rax\n"
				"jmp .loop\n"
			".done:\n"
				"leave\n"
				"ret\n"

			"section .data\n"
				".simple_char:\n"
					"db \"%c\", 0\n"

			"write_sob_fraction:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rax, qword [rbp + 8 + 1*8]\n"
				;"mov rax, [rax]\n"
			    "CAR rax\n"
			    ;"mov rdi, .int_format_string2\n"
			    "push rax\n"
			    "call write_sob\n"
			    "add rsp, 1*8\n"

			    "mov rax, 0\n"
			    "mov rdi, .slash\n"
			    "call printf\n"

			    "mov rax, qword [rbp + 8 + 1*8]\n"
				"CDR rax\n"
				"push rax\n"
			    "call write_sob\n"
			    "add rsp, 1*8\n"
			"\n"
				"leave\n"
				"ret\n"
			"\n"

			"section .data\n"
			".slash:\n"
				"\tdb \"/\", 0\n"


			"\n"
			"write_sob_closure:\n"
				"push rbp\n"
				"mov rbp, rsp\n"
			"\n"
				"mov rsi, qword [rbp + 8 + 1*8]\n"
				"mov rdx, rsi\n"
				"CLOSURE_ENV rsi\n"
				"CLOSURE_CODE rdx\n"
				"mov rdi, .closure\n"
				"mov rax, 0\n"
				"call printf\n"
			"\n"
				"leave\n"
				"ret\n"
			"section .data\n"
			".closure:\n"
				"db \"#<closure [env:%p, code:%p]>\", 0\n"
			"\n"
			"write_sob:\n"
				"mov rax, qword [rsp + 1*8]\n"
				"TYPE rax\n"
				"jmp qword [.jmp_table + rax * 8]\n"
			"\n"
			"section .data\n"
			".jmp_table:\n"
				"dq write_sob_undefined, write_sob_void, write_sob_nil\n"
				"dq write_sob_integer, write_sob_fraction, write_sob_bool\n"
				"dq write_sob_char, write_sob_string, write_sob_symbol\n"
				"dq write_sob_closure, write_sob_pair, write_sob_vector\n"
			"\n"
			"section .text\n"
			"write_sob_if_not_void:\n"
				"mov rax, qword [rsp + 1*8]\n"
				"cmp rax, SOB_VOID\n"
				"je .continue\n"
			"\n"
				"push rax\n"
				"call write_sob\n"
				"add rsp, 1*8\n"
				"mov rax, 0\n"
				"mov rdi, .newline\n"
				"call printf\n"
			"	\n"
			".continue:\n"
				"ret\n"
			"section .data\n"
			".newline:\n"
				"db CHAR_NEWLINE, 0\n"
			"	\n\n\n\n"
		)))



(define compile-scheme-file
	(lambda (inputFile outputFile)
		(let ()
			(set! memConstLocation 0)
			(set! memFvarLocation 0)
			(set! headSymbolTable "const_NIL")
			(let* ((str-AST (pipeline (AST-additional (file->list inputFile))))
				   (constList (build-pre-asm-const-table (build-const-lst str-AST) '()))
				   (constTable (build-asm-const-data constList))
				   (fvarList (build-pre-asm-fvar-table (build-fvar-table str-AST) '()))
				   (fvarTable (build-asm-fvar-data fvarList))
				   (symbolList (symbol-data-asm (reverse (remove-dups <globalSymbols>)) "const_NIL" constList "")))
				;fvarList
				;(find-fvar-index-by-name 'a fvarList)
;#|				
				(display "\n")
				(display (pipeline (file->list inputFile)))
				(display "\n")
				;(display headSymbolTable)
			;(display constList)
				(display "\n")
				(display "\n")
				;(set! symbolList )

				(write-to-file outputFile (string-append
														
														prologue
														(allocate-space-to-symbol-table-head constTable)
														symbolList
														fvarTable
														"\n\n\nsection .bss\n\n"
														"extern exit, printf, scanf, malloc\n"
														"global main, write_sob, write_sob_if_not_void\n\n"
														"section .text\n"
														"\n\nmain:\n"
														;str-AST
														;(code-gen str-AST 0 constList)
														(fvar-string-pred fvarList constList)
														(fvar-char-pred fvarList constList)
														(fvar-integer-pred fvarList constList)
														;(fvar-symbol-pred fvarList)
														(fvar-pair-pred fvarList constList)
														(fvar-null-pred fvarList constList)
														(fvar-procedure-pred fvarList constList)
														(fvar-vector-pred fvarList constList)
														(fvar-car-func fvarList constList)
														(fvar-cdr-func fvarList constList)
														(fvar-not-func fvarList constList)
														(fvar-boolean-pred fvarList constList)
														(fvar-zero-pred fvarList constList)
														(fvar-rational-pred fvarList constList)
														(fvar-number-pred fvarList constList)
														(fvar-numerator fvarList constList)
														(fvar-eq-pred fvarList constList)
														(fvar-cons fvarList constList)

														;those fvar functions USE malloc
														(fvar-denominator fvarList constList)
														(fvar-char-to-int fvarList constList)
														(fvar-int-to-char fvarList constList)
														(fvar-string-length fvarList constList)
														(fvar-string-ref fvarList constList)
														(fvar-vector-ref fvarList constList)
														(fvar-vector-length fvarList constList)
														(fvar-remainder fvarList constList)
														(fvar-plus fvarList constList)
														(fvar-minus fvarList constList)
														(fvar-multiply fvarList constList)
														(fvar-small-than fvarList constList)
														(fvar-greater-than fvarList constList)
														(fvar-div fvarList constList)
														(fvar-equal-to fvarList constList)
														(fvar-make-string fvarList constList)
														(fvar-make-vector fvarList constList)
														(fvar-vector-set fvarList constList)
														(fvar-vector fvarList constList)
														(fvar-string-set fvarList constList)
														(fvar-apply fvarList constList)
														(fvar-symbol-to-string fvarList constList)
														(fvar-symbol-pred fvarList constList)
														(fvar-string-to-symbol fvarList constList)


														"\tmov r10, " headSymbolTable "\n"
														"\tmov qword [head_of_symbol_list], r10\n"

														(apply string-append 
																			(map 
																				(lambda (pe) (string-append 
																									(code-gen pe 0 constList fvarList) 
																									"\n\tpush qword [rax]\n"
																									"\tcall write_sob_if_not_void\n"
																									"\tadd rsp, 1*8\n\n"))
																				 str-AST))
														
														"\nret\n\n"			; ret of main function

														"\napplic_no_closure: \n"
														"lambda_opt_wrong_args: \n"
														"incorrect_input:\n"
														"\tcall exit\n\n"

														epilog))  	;|#
				))))




#|

((0 append) (1 apply) (2 <) (3 =) (4 >) (5 +) (6 /) (7 *)
 (8 -) (9 boolean?) (10 car) (11 cdr) (12 char->integer)
 (13 char?) (14 cons) (15 denominator) (16 eq?) (17 integer?)
 (18 integer->char) (19 list) (20 make-string)
 (21 make-vector) (22 map) (23 not) (24 null?) (25 number?)
 (26 numerator) (27 pair?) (28 procedure?) (29 rational?)
 (30 remainder) (31 set-car!) (32 set-cdr!)
 (33 string-length) (34 string-ref) (35 string-set!)
 (36 string->symbol) (37 string?) (38 symbol?)
 (39 symbol->string) (40 vector) (41 vector-length)
 (42 vector-ref) (43 vector-set!) (44 vector?) (45 zero?)


((1 apply)

0	append			done
1								21	make-vector			done				41  vector-length 	done
2	<				done		22	map					done				42	vector-ref 		done
3	=				done		23	not 				done				43	vector-set!		done
4	>				done		24	null?				done 				44	vector?			done
5	+				done		25	number?				done 				45	zero?			done
6	/				done		26  numerator 			done
7	*				done		27	pair?				done
8	-				done		28	procedure?			done
9   boolean? 		done		29	rational?			done
10	car 			done		30  remainder 			done
11	cdr				done		31	no needed
V12	char->integer 	done		32	no needed
13	char? 			done		33	string-length 		done
14	cons			done		34	string-ref 			done
V15	denominator 	done		35  string-set!			done
16	eq?				done		36  string->symbol 		done
17	integer?		done		37	string?	 			done
V18	integer->char	done		38  symbol?				done
19	list			done		39  symbol->string 		done
20	make-string		done		40	vector 				done

---->build in comile time empty vector
|#