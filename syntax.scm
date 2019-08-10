;;; File: syntax.scm
;;;
;;; This file contains procedures that are taken from the Chapter 4
;;; interpreter.  They are used in two contexts:
;;;
;;; It is loaded by
;;;
;;;   eceval-support.scm to provide implementations of additional
;;;   machine-primitive operators in the register machines of Chapter
;;;   5.
;;;
;;;   compiler.scm to support syntax analysis in the compiler itself.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;;      Representing expressions
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Numbers, strings, and booleans are all represented as themselves.
;;; (Not characters though; they don't seem to work out as well
;;; because of an interaction with read and display.)

(define (self-evaluating? exp)
  (or (number? exp)
      (string? exp)
      (boolean? exp)
      ))

;;; variables -- represented as symbols

(define (variable? exp) (symbol? exp))

;;; quote -- represented as (quote <text-of-quotation>)

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

;;; assignment -- represented as (set! <var> <value>)

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

;;; definitions -- represented as
;;;    (define <var> <value>)
;;;  or
;;;    (define (<var> <parameter_1> <parameter_2> ... <parameter_n>) <body>)
;;;
;;; The second form is immediately turned into the equivalent lambda
;;; expression.

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

;;; lambda expressions -- represented as (lambda ...)
;;;
;;; That is, any list starting with lambda.  The list must have at
;;; least one other element, or an error will be generated.

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

;;; conditionals -- (if <predicate> <consequent> <alternative>?)

(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

;;;**following needed only to implement COND as derived expression,
;;; not needed by eceval machine in text.  But used by compiler

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

;;; sequences -- (begin <list of expressions>)

(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))

;;; procedure applications -- any compound expression that is not one
;;; of the above expression types.

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

;;; Derived expressions -- the only one we include initially is cond,
;;; which is a special form that is syntactically transformed into a
;;; nest of if expressions.

(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))

(define (cond-first-clause exp) (car exp))
(define (cond-rest-clauses exp) (cdr exp))
(define (cond-last-clause? clauses) (null? (cdr clauses)))
(define (cond-no-actions? exp) (null? exp))
(define (cond-null? exp) (null? exp))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                          ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF"
                       clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))
;; end of Cond support

;;; Derive application from let expression

(define (let? exp) (tagged-list? exp 'let))
(define (bindings exp) (cadr exp))
(define (body exp) (cddr exp))
(define (first-binding bindings) (car bindings))
(define (rest-bindings bindings) (cdr bindings))
(define (no-more-bindings? bindings) (null? bindings))
(define (formal binding) (car binding))
(define (arg binding) (cadr binding))

(define (let->appl exp)
  (analyze-let (bindings exp)
               (lambda (formals args)
                 (cons (append `(lambda ,formals) (body exp))
                       args))))

(define (analyze-let exps receive)
  (if (no-more-bindings? exps)
      (receive '() '())
      (analyze-let
       (rest-bindings exps)
       (lambda (formals args)
         (let ((binding (first-binding exps)))
           (let ((variable (formal binding))
                 (init (arg binding)))
             (if (memq variable formals)
                 (error "Name duplicated in formals: " variable)
                 (receive (cons variable formals) (cons init args)))))))))
;; end of let support

;;; Derive if expression from or expression

(define (or? exp) (tagged-list? exp 'or))
(define (tests exp) (cdr exp))
(define (first-test tests) (car tests))
(define (rest-tests tests) (cdr tests))
(define (no-more-tests? tests) (null? tests))

(define (or->if exp)
  (analyze-or (tests exp)))

(define (analyze-or tests)
  (if (no-more-tests? tests)
      '#f
      (make-if (first-test tests)
               (first-test tests)
               (analyze-or (rest-tests tests)))))
;; end of or support

;;; support for apply procedure

(define (apply? exp) (tagged-list? exp 'apply))
;; end of apply support

;;; support for map procedure

(define (map? exp) (tagged-list? exp 'map))
;; end of map support
