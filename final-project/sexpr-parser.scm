(load "project/pc.scm")



(define <boolean> (disj (pack (word-ci "#t") (lambda (_) #t))
			   		 (pack (word-ci "#f") (lambda (_) #f))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Char ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define <char-prefix> (word "#\\"))


(define <VisibleSimpleChar>
	(const
		(lambda (ch)
			(char<? #\space ch))))


(define <WhiteSpace>
	(const
		(lambda (ch)
			(char>=? #\space ch))))


(define ^<NamedChar>
  (lambda (str ch)
    (new 
    	(*parser (word-ci str))
	 	(*pack (lambda (_) ch))
	 done)))


(define <NamedChar>
  (new
   (*parser (^<NamedChar> "lambda" (integer->char 955)))
   (*parser (^<NamedChar> "newline" #\newline)) 
   (*parser (^<NamedChar> "nul" #\nul))
   (*parser (^<NamedChar> "page" #\page))
   (*parser (^<NamedChar> "return" #\return))
   (*parser (^<NamedChar> "space" #\space))
   (*parser (^<NamedChar> "tab" #\tab))
   (*disj 7)


   done))

(define <HexChar>
	(new
		(*parser (range #\0 #\9))
		(*parser (range #\a #\f))
		(*parser (range #\A #\F))
		(*pack (lambda (first) (integer->char (+ (char->integer first) 32))))
		
		(*disj 3)
	done))

(define <HexUnicodeChar>
	(new
		(*parser (char-ci #\x))
		(*parser <HexChar>) *plus
		(*caten 2)
		(*pack-with (lambda (first rest)
							(integer->char (string->number (list->string rest) 16))))
	done))


(define <Char>
	(new
		(*parser <char-prefix>)
	  	(*parser <HexUnicodeChar>)
	  	(*parser <NamedChar>)
	  	(*parser <VisibleSimpleChar>)
	  	(*disj 3)
	  	(*caten 2)
	  	(*pack-with (lambda (first second)
								second))
	 done))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Comments ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <end-of-line-or-input>
	(new 
		(*parser <end-of-input>)
		(*parser (char #\newline))
    	(*disj 2)
    done))

(define <CommentChars>
	(new
		(*parser <any-char>)
   		(*parser <end-of-line-or-input>)
    	*diff
    	*star
    done))

(define <ExpressionComment>
	(new
   		(*parser (word "#;"))
   		
   		(*delayed (lambda () <InfixExpression>))
   		(*delayed (lambda () <sexpr>))
   		(*disj 2)
    	
    	(*caten 2)
    	(*pack-with (lambda (first second)
								`(,first ,second)))
   	done))

(define <LineComment>
  	(new
   		(*parser (char #\;))
  		(*parser <CommentChars>) 
    	(*parser <end-of-line-or-input>)
    	(*caten 3)
   	done))

(define <CharsToIgnore>
	(new
		(*parser <WhiteSpace>)
   		(*parser <ExpressionComment>)
   		(*parser <LineComment>)
    	(*disj 3)

    	*star
    done))

(define ^<StripedParser> 
	(lambda (parser)
		(new
			(*parser <CharsToIgnore>)
			(*parser parser)
			(*parser <CharsToIgnore>)
			(*caten 3)
			(*pack-with (lambda (first second third)
								second))
		done)
		)
	)





;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Numbers ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <Plus-Minus> (disj (char #\+) (char #\-) ))

(define <Natural>
	(new
		
		(*parser (char #\0)) *star
		(*parser (range #\1 #\9))
		(*parser (range #\0 #\9)) *star
		(*caten 3)

		(*pack-with (lambda (first second third)
								(string->number (list->string `(,second ,@third)))))

		(*parser (char #\0))
		(*pack (lambda(_) 0))

		(*disj 2)
	done))

(define <Integer>
	(new
		(*parser <Plus-Minus>)  *maybe
		(*parser <Natural>)
		(*caten 2)
		(*pack-with (lambda (first rest)
						 	(if (equal? #t (car first))
						 		(if (char=? #\- (cadr first))
						 			(- rest)
						 			rest)
						 		rest)))

	done))

(define <Fraction>
	(new
		(*parser <Integer>)
		(*parser (char #\/))
		(*parser <Natural>)
		(*caten 3)
		(*pack-with (lambda (first second third)
								 (/ first third)))
	done))


(define <Number>
	(new
		(*parser <Fraction>)
		(*parser <Integer>) 
		(*disj 2)

		;(*parser <Symbol>)
		;*not-followed-by
		;(*disj 2)
	done))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; String ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <StringHexChar>
  (new
   		(*parser (word "\\x"))
   		(*parser <HexChar>) *star
   		(*parser (char #\;))
   		(*caten 3)
   		(*pack-with (lambda (first second third)
   								 (integer->char (string->number (list->string `(,@second)) 16))))
  done))


(define ^<meta-char>
  (lambda (str ch)
    (new 
    	(*parser (word str))
	 	(*pack (lambda (_) ch))
	 done)))


(define <StringMetaChar>
  (new (*parser (^<meta-char> "\\\\" #\\))
       (*parser (^<meta-char> "\\\"" #\"))
       (*parser (^<meta-char> "\\n" #\newline))
       (*parser (^<meta-char> "\\r" #\return))
       (*parser (^<meta-char> "\\t" #\tab))
       (*parser (^<meta-char> "\\f" #\page))

       (*disj 6)
       done))


(define <StringLiteralChar>
	(new
		(*parser <any-char>)
		
		(*parser (char #\"))
		(*parser (char #\\))
		(*disj 2)
		*diff

		;(*pack (lambda (c) (list c)))
	done))


(define <StringChar>
	(new
		(*parser <StringLiteralChar>)
		(*parser <StringMetaChar>) 
		(*parser <StringHexChar>)
		(*disj 3)
	done)
	)

(define <String>
	(new
		(*parser (char #\"))
		(*parser <StringChar>) 	*star
		;(*parser (char #\")) *diff *star
		(*parser (char #\"))
		(*caten 3)
		(*pack-with (lambda (first second third)
								(list->string `(,@second))))
	done))

;(define <StringMetaChar>
;	(new
;		(*parser (word "\\\\"))
;		(*parser (word "\\\""))
;		(*parser (word "\\t"))
;		(*parser (word "\\f"))
;		(*parser (word "\\n"))
;		(*parser (word "\\r"))
;		(*disj 6)
;	
;		(*pack-with (lambda (first second)
;							(list->string (cons first (cons second '())))))
;	done))

;(load "sexpr-parser.scm")
;(test-string <StringHexChar> "aa")



;define <StringHexChar>
	;(new
		;(*parser (word "\\x"))
	;	(*parser <HexChar>) *star
	;	(*caten 2)
	
		;(*pack-with (lambda (first rest)
		;					(list (integer->char (string->number (list->string rest) 16)))))
	;done))













;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Symbols ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <SymbolChar>
	(new
		(*parser (range #\0 #\9))
		
		(*parser (range #\A #\Z))
		(*pack (lambda (first) (integer->char (+ (char->integer first) 32))))
		
		(*parser (range #\a #\z))
		(*parser (range #\< #\?))	; #\< #\= #\> #\?
		(*parser (char #\/))
		(*parser (char #\+))
		(*parser (char #\-))
		(*parser (char #\_))
		(*parser (char #\*))
		(*parser (char #\^))
		(*parser (char #\$))
		(*parser (char #\!))

		(*disj 12)

		
		done))

(define <Symbol>
	(new
		(*parser <SymbolChar>) *plus
		(*pack (lambda (first)
						;(map char->string first)))
						(string->symbol (list->string first))))
	done))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Lists ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <ProperList>
	(new
		(*parser (char #\())
		(*delayed (lambda () <sexpr>)) *star
		(*parser (char #\)))

		(*caten 3)

		(*pack-with (lambda (first second third)
								second))
	done))


(define <ImproperList>
	(new
		(*parser (char #\())
		(*delayed (lambda () <sexpr>)) *plus
		(*parser (char #\.))
		(*delayed (lambda () <sexpr>))
		(*parser (char #\)))

		(*caten 5)

		(*pack-with (lambda (first second third fourth fifth)
								`(,@second ,@fourth)))
	done))


(define <Vector>
	(new
		(*parser (char #\#))
		(*parser (char #\())
		(*delayed (lambda () <sexpr>)) *star
		(*parser (char #\)))

		(*caten 4)

		(*pack-with (lambda (first second third fourth)
								(list->vector third)))
	done))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Quotes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <Quoted>
	(new
		(*parser (char #\'))
		(*delayed (lambda () <sexpr>)) 

		(*caten 2)

		(*pack-with (lambda (first second)
								(list 'quote second)))
	done))

(define <QuasiQuoted>

	(new
		(*parser (char #\`))
		(*delayed (lambda () <sexpr>)) 

		(*caten 2)

		(*pack-with (lambda (first second)
								(list 'quasiquote second)))
	done))

(define <Unquoted>
	(^<StripedParser>
		(new
			(*parser (char #\,))
			(*delayed (lambda () <sexpr>)) 

			(*caten 2)

			(*pack-with (lambda (first second)
									(list 'unquote second)))
		done)))

(define <UnquoteAndSpliced>
	(^<StripedParser>
		(new
			(*parser (word ",@"))
			(*delayed (lambda () <sexpr>)) 

			(*caten 2)
			(*pack-with (lambda (first second)
									(list 'unquote-splicing second)))
		done)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; CBName ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define <CBNameSyntax1>
	(new
		(*parser (char #\@))
		(*delayed (lambda () <sexpr>)) 

		(*caten 2)
		(*pack-with (lambda (first second)
								(list 'cbname second)))
	done))


(define <CBNameSyntax2>
	(new
		(*parser (char #\{))
		(*delayed (lambda () <sexpr>)) 
		(*parser (char #\}))

		(*caten 3)
		(*pack-with (lambda (first second third)
								(list 'cbname second)))
	done))

(define <CBName>
	(new
		(*parser <CBNameSyntax1>)
		(*parser <CBNameSyntax2>)
		(*disj 2)
	done)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Infix ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define <Mul-Div> (disj (char #\*) (char #\/) ))
(define <Pow> (disj (char #\^) (word "**")))
(define <Neg> (char #\-))

(define <InfixSymbol>
	(new
		;(*parser <SymbolChar>)
		
		(*parser (range #\0 #\9))
		
		(*parser (range #\A #\Z))
		(*pack (lambda (first) (integer->char (+ (char->integer first) 32))))
		
		(*parser (range #\a #\z))
		(*parser (range #\< #\?))	; #\< #\= #\> #\?
		;(*parser (char #\/))
		;(*parser (char #\+))
		;(*parser (char #\-))
		(*parser (char #\_))
		;(*parser (char #\*))
		;(*parser (char #\^))
		(*parser (char #\$))
		(*parser (char #\!))


		;(*parser <Plus-Minus>)
		;(*parser <Mul-Div>)
		;(*parser <Pow>)
		(*disj 7)
		
		;*diff
		*plus

		(*pack (lambda (first) (string->symbol (string-downcase (list->string first)))))
	done))


(define <InfixPrefixExtensionPrefix>
  	(new
   		(*parser (word "##"))
   		(*parser (word "#%"))
   		(*disj 2)
   	done))


(define <InfixSexprEscape>
	(^<StripedParser>
		(new
			(*parser <InfixPrefixExtensionPrefix>)
			(*delayed (lambda () <sexpr>))
			(*caten 2)
			(*pack-with (lambda (first second)
									second))
		done)))


(define <InfixHaltParser>
  	(^<StripedParser>
  		(new


   			(*parser <Number>)
   			;(*parser <InfixSymbol>)

   			;(*parser <Plus-Minus>)
			;(*parser <Mul-Div>)
			;(*parser <Pow>)
			;(*disj 3)
   			;*diff
   			
   			;*not-followed-by
   			
   			;(*parser <InfixSymbol>)

   			(*parser <InfixSymbol>)
   			(*parser <InfixSexprEscape>)
   			(*disj 3)
   		done)))




(define InfixArithmetic_Pack-With 
	(lambda (first rest) 
		(fold-left 
			(lambda (acc curr)	; curr := a list of 2 arguments, an arithmetic operation (+, -, \, * etc.) and a Number terminal \ expression.
				`(,(string->symbol(string (car curr))) ,acc ,@(cdr curr))) 
			first 
			rest
		)
	)
)


(define InfixPow_Pack-With
	(lambda (first rest)
		(let* (
			(wholeList (cons first rest))
			(lastElement (car (reverse wholeList)))
			(lastElementChoppedList (reverse (cdr (reverse wholeList)))))

			(fold-right
				(lambda (acc curr)
					`(expt ,acc ,curr))
				lastElement	
				lastElementChoppedList
			)
		)
	)
)



(define <InfixParen>
	(^<StripedParser>
		(new
			
			(*parser (char #\())
			(*delayed (lambda () <InfixExpression>))
			(*parser (char #\)))
			(*caten 3)
			(*pack-with (lambda (first second third)
						second))

			(*parser <InfixHaltParser>)

			(*disj 2)
		done)))




(define <InfixArgList>
	(^<StripedParser>
		(new
			(*delayed (lambda () <InfixExpression>))

			(*parser (char #\,))
			(*delayed (lambda () <InfixExpression>))
			(*caten 2)
			(*pack-with (lambda (first second)
						second))
			*star

			(*caten 2)
			(*pack-with (lambda (first rest)
								`(,first ,@rest)))

			(*parser <epsilon>)
			(*disj 2)
		done)))



(define <InfixFuncall>
	(^<StripedParser>
		(new
			(*parser <InfixParen>)
			
			(*parser (char #\())
			(*parser <InfixArgList>)
			(*parser (char #\)))			
			(*caten 3)

			(*pack-with (lambda (first second third)
						second))
			*star

			(*caten 2)
			(*pack-with (lambda (first rest)
							(fold-left
								(lambda (acc curr)
									`(,acc ,@curr))
								first	
								rest)))
		done)))


(define <InfixArrayGet>
	(^<StripedParser>
		(new
			(*parser <InfixFuncall>)
			
			(*parser (char #\[))
			(*delayed (lambda () <InfixExpression>))
			(*parser (char #\]))			
			(*caten 3)

			(*pack-with (lambda (first second third)
						second))
			*star

			(*caten 2)
			(*pack-with (lambda (first rest)
							(fold-left
								(lambda (acc curr)
									`(vector-ref ,acc ,curr))
								first	
								rest)))
		done)))


(define <InfixNeg>
	(^<StripedParser>
		(new
			(*parser <InfixArrayGet>)
			
			(*parser <Neg>)
			(*parser <InfixArrayGet>)
			(*caten 2)
			(*pack-with (lambda (first second)
						`(- ,second)))

			(*disj 2)
		done)))


(define <InfixPow>
	(^<StripedParser>
		(new
			(*parser <InfixNeg>)
			
			(*parser <Pow>)
			(*parser <InfixNeg>)
			(*caten 2) 
			(*pack-with (lambda (first second)
						second))
			*star

			(*caten 2)
			(*pack-with InfixPow_Pack-With)
		done)))


(define <InfixMul&Div>
	(^<StripedParser>
		(new
			(*parser <InfixPow>)

			(*parser <Mul-Div>)
			(*parser <InfixPow>)
			(*caten 2) *star

			(*caten 2)
			(*pack-with InfixArithmetic_Pack-With)
		done)))


(define <InfixAdd&Sub>
	(^<StripedParser>
		(new
			(*parser <InfixMul&Div>)

			(*parser <Plus-Minus>)
			(*parser <InfixMul&Div>)
			(*caten 2) *star

			(*caten 2)
			(*pack-with InfixArithmetic_Pack-With)
		done)))



(define <InfixExpression> <InfixAdd&Sub>)		; TO CHECK -> STRIPED PARSER
;	(new
;   		(*parser <InfixAdd>)
;		(*parser <InfixNeg>)   		
;		(*parser <InfixSub>)
;		(*parser <InfixMul>)
;		(*parser <InfixDiv>)
;		(*parser <InfixPow>)
;		(*parser <InfixArrayGet>)
;		(*parser <InfixFuncall>)
;		(*parser <InfixParen>)
;		(*parser <InfixSexprEscape>)
;		(*parser <InfixSymbol>)
;		(*parser <Number>)
;
;		(*disj 12)
 ;  	done))

(define <InfixExtention>
	(^<StripedParser>
		(new
			(*parser <InfixPrefixExtensionPrefix>)
			(*delayed (lambda () <InfixExpression>))
			(*caten 2)

			(*pack-with (lambda (first second)
									second))

		done)))

(define <sexpr>
  ;; fill in the s-expression parser details here
	(^<StripedParser>
	  (new 
	  	(*parser <boolean>)
	  	(*parser <Char>)

	  	(*parser <Number>)
	  	(*parser <Symbol>)
	  	*not-followed-by

		(*parser <String>)
		(*parser <Symbol>)
		(*parser <ProperList>)
		(*parser <ImproperList>)
		(*parser <Vector>)
		(*parser <Quoted>)
		(*parser <QuasiQuoted>)
		(*parser <Unquoted>)
		(*parser <UnquoteAndSpliced>)
		(*parser <CBName>)
		(*parser <InfixExtention>)
	  	(*disj 14)
	done)
	)
  )







 ; 	(*parser (range #\1 #\9))
;	(*parser (range #\0 #\9)) *star
;	(*caten 2)
;	
;	(*parser (char #\0))
;	(*parser (range #\0 #\9))
;	*not-followed-by
;	(*disj 2)

;(load "sexpr-parser.scm")
;(test-string <sexpr> "")

