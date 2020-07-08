#lang racket

;; Caccia Anthony

(define (true? x)
  (not (eq? x #f)))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (self-evaluating? exp)
  (or (number? exp) (string? exp)))

(define (variable? exp)
  (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp)
  (cadr exp))

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment-variable exp)
  (cadr exp))

(define (assignment-value exp)
  (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (lambda? exp)
  (tagged-list? exp 'lambda))

(define (lambda-parameters exp)
  (cadr exp))

(define (lambda-body exp)
  (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp)
  (tagged-list? exp 'if))

(define (if-predicate exp)
  (cadr exp))

(define (if-consequent exp)
  (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (begin? exp)
  (tagged-list? exp 'begin))

(define (begin-actions exp)
  (cdr exp))

(define (last-exp? seq)
  (null? (cdr seq)))

(define (first-exp seq)
  (car seq))

(define (rest-exps seq)
  (cdr seq))

(define (application? exp)
  (pair? exp))

(define (operator exp)
  (car exp))

(define (operands exp)
  (cdr exp))

(define (no-operands? ops)
  (null? ops))

(define (first-operand ops)
  (car ops))

(define (rest-operands ops)
  (cdr ops))

(define (enclosing-environment env)
  (cdr env))

(define (first-frame env)
  (car env))

(define the-empty-environment
  '())

(define (make-frame)
  (mcons '() '()))

(define (frame-variables frame)
  (mcar frame))

(define (frame-values frame)
  (mcdr frame))

(define (add-binding-to-frame! var val frame)
  (set-mcar! frame (mcons var (mcar frame)))
  (set-mcdr! frame (mcons val (mcdr frame))))

(define (extend-environment vars vals base-env)
  (define frame (make-frame))
  (define (extend-loop vars vals)
    (if (null? vars)
        (if (null? vals)
            (cons frame base-env)
            (error "Too many arguments supplied"))
        (if (null? vals)
            (error "Too few arguments supplied")
            (begin
              (add-binding-to-frame! (car vars) (car vals) frame)
              (extend-loop (cdr vars) (cdr vals))))))
    (extend-loop vars vals))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (mcar vars))
             (mcar vals))
            (else (scan (mcdr vars) (mcdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (mcar vars))
             (set-mcar! vals val))
            (else (scan (mcdr vars) (mcdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (mcar vars))
             (set-mcar! vals val))
            (else (scan (mcdr vars) (mcdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))

(define (procedure-parameters p)
  (cadr p))

(define (procedure-body p)
  (caddr p))

(define (procedure-environment p)
  (cadddr p))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc)
  (cadr proc))

(define (make-continuation cont)
  (list 'continuation cont))

(define (continuation? c)
  (tagged-list? c 'continuation))

(define (continuation-continuation p)
  (cadr p))

(define (call-cc-prim cont args)
  (let ((proc (car args)))
    (apply-c proc (list (make-continuation cont)) cont)))

(define (dispatch? exp)
  ;; does the expression begin by dispatch ?
  (tagged-list? exp 'dispatch))

(define (dispatch-args exp)
  ;; getting all args of dispatcher
  (cdr exp))

(define (dispatch->lambda exp)
  ;; converting dispatch to lambda expression, example:
  ;; (dispatch f g) => lambda (m) (if (eq? m 'f) f (if eq? m 'g) g (error ...))))
  (define (dispatch-exp->if exp)
  (if (null? exp)
      '(error "Unknown request")
      (let ((first (car exp))
            (rest (cdr exp)))
        (make-if (list 'eq? 'm (list 'quote first))
                 first
                 (dispatch-exp->if rest)))))
  (let ((if-expr (dispatch-exp->if (dispatch-args exp))))
    (make-lambda '(m) (list if-expr))))

(define (send? exp)
  ;; does the expression begin by dispatch ?
  (tagged-list? exp 'send))

(define (send-dispatcher exp)
  ;; get dispatcher from send command
  (cadr exp))

(define (send-name exp)
  ;; get name from send command
  (caddr exp))

(define (send->app exp)
  ;; change a (send d n) to (d 'n)
  (let ((disp (send-dispatcher exp))
        (name (send-name exp)))
    (list disp (list 'quote name))))

(define (invoke? exp)
  ;; does the expression begin by invoke ?
  (tagged-list? exp 'invoke))

(define (invoke-dispatcher exp)
  ;; get dispatcher from invoke command
  (cadr exp))

(define (invoke-name exp)
  ;; get name from invoke command
  (caddr exp))

(define (invoke-args exp)
  ;; get remaining args from invoke command
  (cdddr exp))

(define (invoke->app exp)
  ;; change a (invoke d n a1 a2 ...) to ((d 'n) a1 a2 ...)
  (let ((disp (invoke-dispatcher exp))
        (name (invoke-name exp))
        (args (invoke-args exp)))
    (append (list (list disp (list 'quote name))) args)))
  
(define (evaluate exp env cont)
  (cond ((self-evaluating? exp) (cont exp))
        ((variable? exp) (eval-variable exp env cont))
        ((quoted? exp) (eval-quoted exp cont))
        ((assignment? exp) (eval-assignment exp env cont))
        ((definition? exp) (eval-definition exp env cont))
        ((if? exp) (eval-if exp env cont))
        ((lambda? exp) (eval-lambda exp env cont))
        ((begin? exp) (eval-begin exp env cont))
        ((dispatch? exp) (eval-lambda (dispatch->lambda exp) env cont)) ;; syntactic sugar
        ((send? exp) (eval-application (send->app exp) env cont))       ;; 
        ((invoke? exp) (eval-application (invoke->app exp) env cont))   ;;
        ((application? exp) (eval-application exp env cont))
        (else (error "Unknown expression type -- EVAL" exp))))

(define (eval-variable exp env cont)
  (let ((value (lookup-variable-value exp env)))
    (cont value)))

(define (eval-quoted exp cont)
  (let ((text (text-of-quotation exp)))
    (cont text)))

(define (eval-lambda exp env cont)
  (cont (make-procedure (lambda-parameters exp)
                        (lambda-body exp)
                        env)))

(define (eval-assignment exp env cont)
  (evaluate (assignment-value exp) env
            (lambda (value)
              (set-variable-value! (assignment-variable exp)
                                   value
                                   env)
              (cont 'ok))))

(define (eval-definition exp env cont)
  (evaluate (definition-value exp) env
            (lambda (value)
              (define-variable! (definition-variable exp)
                value
                env)
              (cont 'ok))))

(define (eval-if exp env cont)
  (evaluate (if-predicate exp) env
            (lambda (value)
              (if (true? value)
                  (evaluate (if-consequent exp) env cont)
                  (evaluate (if-alternative exp) env cont)))))

(define (eval-begin exp env cont)
  (eval-sequence (begin-actions exp) env cont))

(define (eval-sequence exps env cont)
  (if (last-exp? exps)
      (evaluate (first-exp exps) env cont)
      (evaluate (first-exp exps) env
                (lambda (ignored)
                  (eval-sequence (rest-exps exps) env cont))))) 

(define (eval-application exp env cont)
  (evaluate (operator exp) env
            (lambda (procedure)
              (eval-operands (operands exp) env
                                   (lambda (arguments)
                                     (apply-c procedure arguments cont))))))

(define (eval-operands exps env cont)
  (define (exp-loop exps arguments)
    (if (no-operands? exps)
        (cont (reverse arguments))
        (evaluate (first-exp exps) env
                  (lambda (value)
                    (exp-loop (rest-exps exps) (cons value arguments))))))
  (exp-loop exps '()))

(define (apply-c procedure arguments cont)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments cont))
        ((compound-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (extend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure))
           cont))
        ((continuation? procedure)
         ((continuation-continuation procedure) (car arguments)))
        (else
         (error
          "Unknown procedure type -- APPLY" procedure))))

(define (apply-primitive-procedure proc args cont)
  (cont ((primitive-implementation proc) cont args)))

(define (prim/cc prim)
    (lambda (cont args)
      (apply prim args)))

(define primitive-procedures
  (list (list '+ (prim/cc +))
        (list '- (prim/cc -))
        (list '* (prim/cc *))
        (list '< (prim/cc <))
        (list '> (prim/cc >))
        (list '<= (prim/cc <=))
        (list '>= (prim/cc >=))
        (list 'car (prim/cc car))
        (list 'cdr (prim/cc cdr))
        (list 'cons (prim/cc cons))
        (list 'null? (prim/cc null?))
        (list 'eq? (prim/cc eq?))      ;; needed for the lambda reconstruction in dispatch
        (list 'call/cc call-cc-prim)
        ))

(define (primitive-procedure-names)
  (map car
       primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")
(define (driver-loop value)
  (announce-output output-prompt)
  (user-print value)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (evaluate input the-global-environment driver-loop)))

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))

(define (announce-output string)
  (newline) (display string) (newline))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

(define the-global-environment (setup-environment))
(driver-loop "CPS Evaluator 0.9")
