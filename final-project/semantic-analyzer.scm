;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    Assignment 3    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;             
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define is-empty-list?
  (lambda (lst) 
    (if (eq? lst (list)) 
        #t
        #f)))

(define null-or-not-list?
  (lambda (pe) 
    (or (null? pe) (not (list? pe)))  
  )
)

(define (is-lambda? pe)  
  (or (eq? (car pe) 'lambda-simple)
      (eq? (car pe) 'lambda-opt)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Question 2     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;             


(define remove-applic-lambda-nil  
   (lambda (pe)
    (if (or (atom? pe)
          (eq? (car pe) 'var)
          (eq? (car pe) 'const)) 
        pe
        (remove-redundant-applic (map remove-applic-lambda-nil pe)))))

(define remove-redundant-applic 
  (lambda (pe)
    (if (cut-applic? pe)        
      (car (cddadr pe))
      pe)))

(define cut-applic?
  (lambda (pe)
    (if (eq? 'applic (car pe))              ;checks if first element is "applic"
      (if (eq? 'lambda-simple (caadr pe))   ;checks first element = 'lambda-simple / 'lambda-opt
        (if (null? (caddr pe))              
          (if (is-empty-list? (cadadr pe))        ;checks params list is null / no params
            #t
            #f)
          #f)
        #f)
      #f)))
                  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Question 3     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;             


(define lambda-bound-occ?
    (lambda (pe param)
    (cond ((null-or-not-list? pe) #f)
      ((equal? pe `(var ,param)) #t)
      ((and (eq? (car pe) 'set) (eq? (cadadr pe) param)) #t)
      ((and (is-lambda? pe)
            (member param (if (eq? 'lambda-simple (car pe)) 
                              (cadr pe)
                              (list (caadr pe) (caddr pe)))                                ;lambda opt
            )) #f) 
      (else (or (lambda-bound-occ? (cdr pe) param) (lambda-bound-occ? (car pe) param))))
  )
)


(define bound-occ?
    (lambda (pe var)
  (cond ((null-or-not-list? pe) #f)
        ((is-lambda? pe)
           (lambda-bound-occ? pe var))
        (else (or (bound-occ? (car pe) var) (bound-occ? (cdr pe) var))))))

   
(define set-occ? (lambda (pe box-param)
    (if (null-or-not-list? pe)
      #f
      (cond
        ((and (eq? (car pe) 'set) (eq? (cadadr pe) box-param)) #t)
        ((and (eq? 'lambda-simple (car pe))   
              (member box-param 
                      (cadr pe))
              ) 
                 #f
        )
        ((and (eq? 'lambda-opt (car pe))   
            (member box-param 
                  (if (not (list? (cadr pe)))
                    (list (cadr pe))            ;lambda-var
                    (list))                      ;lambda-opt
             ))
         #f
        )
        (else (or (set-occ? (car pe) box-param) (set-occ? (cdr pe) box-param)))
      )
  )
))


(define get-occ?
  (lambda (pe box-param)
    (if (null-or-not-list? pe)
      #f
      (cond

        ((and (list? pe) (equal? pe `(var ,box-param))) #t)   
        
        ((and (eq? (car pe) 'lambda-simple)
              (not (member box-param (cadr pe))))
          (get-occ? (caddr pe) box-param))

           ((and (eq? 'lambda-opt (car pe))   
              (not (member box-param 
                      (append (cadr pe) (list (cddr pe)))))
              ) 
          (get-occ? (caddr pe) box-param)
         )
         ((and (eq? 'set (car pe)) (eq? box-param (cadadr pe)))
          (get-occ? (cddr pe) box-param)
         )
         (else (or (get-occ? (car pe) box-param) 
          (get-occ? (cdr pe) box-param))))
      )
    )
  )

(define add-params-box-sets
 (lambda (box-params)
    (if (and (not (null? box-params)) (list? box-params))
      (let ((curr-box-param (car box-params)))
        (if (not (null? (cdr box-params)))
          `((set ,curr-box-param (box ,curr-box-param)) ,@(add-params-box-sets (cdr box-params)))
          `((set ,curr-box-param (box ,curr-box-param)))
        )
      )
    )
  )

)


(define add-single-box-to-body
  (lambda (box-param body)
    (if (or (null-or-not-list? body)
            (and  (is-lambda? body) 
                  (member (cadr box-param) 
                           (if (eq? (car body) 'lambda-simple)   
                               (cadr body)                                  ; lambda-simple
                                (if (is-empty-list? (cadr body)) 
                                     (list (caddr body))                    ; "lambda-var":=lambda-opt
                                     #f)
                            )
                   )                    
              )
        )
        body
        (if (and (eq? 'set (car body) ) (equal? box-param (cadr body)))
                `(box-set ,box-param ,@(add-single-box-to-body box-param (cddr body)))
                (if (equal? box-param body) 
                    `(box-get ,box-param)
                    (cons (add-single-box-to-body box-param (car body)) (add-single-box-to-body box-param (cdr body))))))))




(define add-boxes-to-body
  (lambda (box-params body) 
    (if (null? box-params)
      body
      (let ((first-param (car box-params))
            (rest-of-params (cdr box-params)))
          (add-boxes-to-body rest-of-params (add-single-box-to-body first-param body))       
      )
    )
  )
)

(define fetch-box-params 
  (lambda (pe body)
    (let* ((params (if (eq? (car pe) 'lambda-simple)   
                       (cadr pe)                                  ; lambda-simple
                        (if (not (is-empty-list? (cadr pe))) 
                          (append (cadr pe) (list (caddr pe)))    ; lambda-opt
                          (list (caddr pe)))))                    ; "lambda-var":=lambda-opt
            (filtered-params (filter
                                  (lambda (param)
                                     (if (and (bound-occ? body param) (get-occ? body param) (set-occ? body param))
                                        #t
                                        #f))
                                  params))
        )
      (map 
        (lambda (param) `(var ,param))
        filtered-params
        ))
  )
)

(define lambdaBoxing
  (lambda (pe)
    (let* ((lambda-type (car pe))
           (lambda-simple? (if (eq? lambda-type 'lambda-simple)  ;lambda-simple? is a boolean flag
                      #t
                      #f))
           (all-params (if lambda-simple?
                       (cadr pe)
                       (list (cadr pe) (caddr pe))))
          (body (if lambda-simple?
                     (caddr pe)     ;lambda-simple
                     (cadddr pe))) ;lambda-opt , "lambda-var"
           (box-params (fetch-box-params pe body)))
          (if (null? box-params)
                ;;;; <dit>
                (if lambda-simple?
                    `(,lambda-type ,all-params ,(box-set body))           ;lambda-simple form
                    `(,lambda-type ,(cadr pe) ,(caddr pe) ,(box-set body))  ;lambda-opt form
                )
                ;;;; <dif>
                (if lambda-simple?
                  ;;;; lambda-simple
                  (if (eq? 'seq (car body))
                    `(,lambda-type ,all-params (seq (,@(add-params-box-sets box-params) ,@(add-boxes-to-body box-params (box-set (cadr body))))))
                    `(,lambda-type ,all-params (seq (,@(add-params-box-sets box-params) ,(add-boxes-to-body box-params (box-set body)))))
                  )
                  ;;;; lambda-opt
                  (if (eq? 'seq (car body))
                    `(,lambda-type ,(cadr pe) ,(caddr pe) (seq (,@(add-params-box-sets box-params) ,@(add-boxes-to-body box-params (box-set (cadr body))))))
                    `(,lambda-type ,(cadr pe) ,(caddr pe) (seq (,@(add-params-box-sets box-params) ,(add-boxes-to-body box-params (box-set body)))))
                  )
                )
              )

)))


(define box-it
  (lambda (pe)
    (let* ((lambda-type (car pe))
        (lambda-simple? (if (eq? lambda-type 'lambda-simple)  ;lambda-simple? is a boolean flag
                      #t
                      #f))
        (all-params (if lambda-simple?
                (cadr pe)                   ;lambda-simple form
                 (list (cadr pe) (caddr pe))))        ;lambda-opt form
        (body (if lambda-simple?
                 (caddr pe)                   ;lambda-simple form
                 (cadddr pe)))                ;lambda-opt form
        (box-params (fetch-box-params all-params body)))
      
      (if (null? box-params)
        ;;;; <dit>
        (if lambda-simple?
            `(,lambda-type ,all-params ,(box-set body))           ;lambda-simple form
            `(,lambda-type ,(cadr pe) ,(caddr pe) ,(box-set body))  ;lambda-opt form
        )
        ;;;; <dif>
        (if lambda-simple?
          ;;;; lambda-simple
          (if (eq? 'seq (car body))
            `(,lambda-type ,all-params (seq (,@(add-params-box-sets box-params) ,@(add-boxes-to-body box-params (box-set (cadr body))))))
            `(,lambda-type ,all-params (seq (,@(add-params-box-sets box-params) ,(add-boxes-to-body box-params (box-set body)))))
          )
          ;;;; lambda-opt
          (if (eq? 'seq (car body))
            `(,lambda-type ,(cadr pe) ,(caddr pe) (seq (,@(add-params-box-sets box-params) ,@(add-boxes-to-body box-params (box-set (cadr body))))))
            `(,lambda-type ,(cadr pe) ,(caddr pe) (seq (,@(add-params-box-sets box-params) ,(add-boxes-to-body box-params (box-set body)))))
          )
        )
      )
    )
  )
)




(define box-set
  (lambda (pe)
    (if (null-or-not-list? pe)
        pe
        (if (is-lambda? pe)
            (lambdaBoxing pe)
            (cons 
                (if (not (list? (car pe)))
                    (car pe)
                    (box-set (car pe)))              ;aint lambda-form  --> take it has is
                (box-set (cdr pe))))
    )
))
                
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Question 4     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;             


(define calc-minor  
  (lambda (var params acc)
    (if (is-empty-list? params)
        -1
        (if (equal? (car params) var) 
            acc
            (calc-minor var (cdr params) (+ acc 1))
            )
        )
    )
  )
  

(define is-member-of?
  (lambda (var params)
    (not (not (member var params)))))


(define bvar-fvar  
  (lambda (var params acc)
    (if (is-empty-list? params)
        `(fvar ,var)
        (if (is-member-of? var (car params))
            `(bvar ,var ,acc ,(calc-minor var (car params) 0))
            (bvar-fvar var (cdr params) (+ acc 1))
        )
    )
  )
)

(define fetch-lambda-params
    (lambda (pe)
      (if (eq? 'lambda-simple (car pe))
            (cadr pe)
            (if (eq? 'lambda-opt (car pe))
                (append (cadr pe) (list (caddr pe)))   ; params + rest united
            )
    )
  )
)


(define calc-var                              ;Checks which kind of var (fvar, pvar, bvar)
  (lambda (pe params box-params)
    (if (or (is-empty-list? pe) (atom? pe))
        pe                                    
        (if (equal? 'var (car pe))
            (if (is-member-of? (cadr pe) params) 
                    `(pvar ,(cadr pe) ,(calc-minor (cadr pe) params 0))
                    (bvar-fvar (cadr pe) box-params 0)
            ) 
            (if (eq? 'lambda-opt (car pe))     ; lambda-opt form
                (list (car pe) (cadr pe) (caddr pe) (car (map (lambda (param) (calc-var param (fetch-lambda-params pe) (cons params box-params))) (cdddr pe))))
                (if (eq? 'lambda-simple (car pe))
                    (list (car pe) (cadr pe)  (car (map (lambda (param) (calc-var param (fetch-lambda-params pe) (cons params box-params))) (cddr pe))))
                    (map (lambda (y) (calc-var y params box-params)) pe)
                 )
              )
        )
    )
  )
)
 
    
(define pe->lex-pe
  (lambda (pe)
    (calc-var pe '() '())))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;     Question 5     ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;             


(define annotate-tc
  (lambda (pe) 
    (annotate-tc-func pe #f)))


(define cut-last-element
  (lambda (pe) 
    (reverse (cdr (reverse pe)))))


(define last-element
  (lambda (pe) 
    (car (reverse pe))))
  

(define annotate-tc-func
  (lambda (pe tail-pos?)
    (if (or (atom? pe)
               (is-empty-list? pe)
               (not (list? pe)))
            pe
            (let ((frst (car pe)))          
              (cond ((or (eq? frst 'const)
                         (eq? frst 'fvar)
                         (eq? frst 'box-get)
                         (eq? frst 'pvar)
                         (eq? frst 'bvar)) 
                       pe)
    
                    ((eq? frst 'applic) 
                        (if tail-pos? 
                            `(tc-applic ,(annotate-tc-func (cadr pe) #f) ,@(map annotate-tc-func (cddr pe) (make-list (length (cddr pe) ) #f)))
                            `(applic  ,(annotate-tc-func (cadr pe) #f) ,@(map annotate-tc-func (cddr pe) (make-list (length (cddr pe) ) #f)))))

                     ((eq? frst 'seq) 
                        `(seq  ,`(,@(map (lambda (se) (annotate-tc-func se #f)) (cut-last-element (cadr pe)))  ,(annotate-tc-func (last-element (cadr pe)) tail-pos?))))
                     
                    ((eq? frst 'or) 
                        `(or (,@(map (lambda (oe) (annotate-tc-func oe #f)) (cut-last-element (car (cdr pe))))  ,(annotate-tc-func (last-element (cadr pe)) tail-pos?))))

                    ((eq? frst 'if3)
                        `(if3 ,(annotate-tc-func (cadr pe) #f) ,(annotate-tc-func (car (cddr pe)) tail-pos?) ,(annotate-tc-func (cadddr pe) tail-pos?)))

                    ((eq? frst 'define)
                        `(define ,(cadr pe) ,(annotate-tc-func (caddr pe) #f)))
                  
                    ((eq? frst 'lambda-opt) 
                        `(lambda-opt ,(cadr pe) ,(caddr pe) ,(annotate-tc-func (cadddr pe) #t)))

                    ((eq? frst 'lambda-simple) 
                        `(lambda-simple ,(cadr pe) ,(annotate-tc-func (caddr pe) #t)))
                    
                    ((or (equal? frst 'set)
                         (equal? frst 'box-set)) 
                      `(,frst ,(cadr pe)  ,(annotate-tc-func (caddr pe) #f)))

                  (else (cons (annotate-tc-func (car pe) tail-pos?) (annotate-tc-func (cdr pe) tail-pos?))))))
    ))