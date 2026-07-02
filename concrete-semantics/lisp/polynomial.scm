
#|

Define a function eval :: exp ⇒ int ⇒ int such that eval e x evaluates e at
the value x.
A polynomial can be represented as a list of coefficients, starting with the
constant. For example, [4, 2, − 1, 3] represents the polynomial 4+2x−x^2+3*x^3
*)

fun eval :: "exp ⇒ int ⇒ int" where
"eval Var x = x" |
"eval (Const i) x = i" |
"eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)" |
"eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)" 

value "eval Var 3" 
value "eval (Const 5) 3"
value "eval (Add Var Var) 3"

(*
Define a function evalp :: int list ⇒ int ⇒ int that evaluates a polynomial at
the given value. 
*)
fun evalph :: "int list ⇒ int ⇒ int ⇒ int" where
"evalph [] x n = 0" |
"evalph (h # t) x n = 0"

fun evalp :: "int list ⇒ int ⇒ int" where
"evalp [] x = 0" |
"evalp (h # t) x = 0" 
|#

;; (use-modules (ice-9 match))

;; eval reserved word - use meval
(define (meval expr x)
  (cond
    ((eq? expr 'var) x)
    ((and (pair? expr) (eq? (car expr) 'add))
     (let ((e1 (car (cdr expr)))
	   (e2 (car (cdr (cdr expr)))))
       (+ (meval e1 x) (meval e2 x))))
    ((and (pair? expr) (eq? (car expr) 'mult))
     (let ((e1 (car (cdr expr)))
	   (e2 (car (cdr (cdr expr)))))
       (* (meval e1 x) (meval e2 x))))))


(meval 'var 3) ;; 3
(meval '(add var var) 3) ;; 3 + 3
(meval '(add (mult var var) var) 5) ;; 5*5 + 5


;; given a list - translate into polynomial expression

(define (mlist3 x pow)
  (cond
    ((< pow 1) `(const ,x))
    (else `(mult (const ,x) (pow var ,pow)))))

(define (mlist2 xs pow)
  (cond
    ((null? xs) '())
    (else (let ((x (car xs))
		(tt (cdr xs)))
	 (cond
	  ((null? tt) (mlist3 x pow))
	  (else `(add ,(mlist3 x pow) ,(mlist2 tt (+ pow 1)))))))))
    
(define (mlist xs)
  (mlist2 xs 0))

(mlist '(0))
(mlist '(1))
(mlist '(1 1))
(mlist '(1 2 3))

;; pre_order on tree xs -- cps 
(define (coeffs expr)
  (cond
    ((null? expr) '())
    ((eq? expr 'var) '())
    ((eq? (car expr) 'const) (let ((i (car (cdr expr)))) (list i)))
    ((eq? (car expr) 'add) (append (coeffs (car (cdr expr)))
				   (coeffs (car (cdr (cdr expr))))))
    ((eq? (car expr) 'mult) (append (coeffs (car (cdr expr)))
				    (coeffs (car (cdr (cdr expr))))))
    ((eq? (car expr) 'pow) '())))
     
(coeffs 'var)
(coeffs '(const 3))
(coeffs '(add var var))
(coeffs '(add (const 3) (mult (const 4) (pow var 1))))
(coeffs (mlist '(0)))
(coeffs (mlist '(1)))
(coeffs (mlist '(1 1)))
(coeffs (mlist '(1 2 3)))




    
					   
