

;; eval reserved word - use meval
(define (meval expr x)
  (cond
    ((eq? expr 'var) x)
    ((and (pair? expr) (eq? (car expr) 'const))
     (let ((e1 (car (cdr expr))))
       e1))
    ((and (pair? expr) (eq? (car expr) 'add))
     (let ((e1 (car (cdr expr)))
	   (e2 (car (cdr (cdr expr)))))
       (+ (meval e1 x) (meval e2 x))))
    ((and (pair? expr) (eq? (car expr) 'mult))
     (let ((e1 (car (cdr expr)))
	   (e2 (car (cdr (cdr expr)))))
       (* (meval e1 x) (meval e2 x))))))


(meval 'var 3) ;; 3
(meval '(const 4) 3) ;; 3
(meval '(add var var) 3) ;; 3 + 3
(meval '(add (mult var var) var) 5) ;; 5*5 + 5


#|
 how do you determine what coefficients of a random expression actually are ?

  Var      -> this our 'x'  (1 1)
  Const a  -> 
  Add a b  -> 
  Mult a b ->     

  2*x^2+4*x^2+3*x^2
  ((2 2)(4 2)(3 2)) 

  (+ (* 2 (* x x))
     (+ (* 4 (* x x))
        (* 3 (* x x))))


(0 3) 3x
(2)   2
(2 3) => 2 + 3x 


(comb '(0 3) '(2))
(fan3-mult 2 '(0 1 0 2) '(0 0))

;;(fan-mult '(5) '(2 3))

|#

(define (comb xs ys)
  (cond 
   ((null? xs) ys)
   ((null? ys) xs)
   (else (let ((x (car xs))
	       (y (car ys)))
	   (cons (+ x y) (comb (cdr xs) (cdr ys)))))))

(define (fan3-mult x ys aa)
  (append aa (map (lambda (y) (* x y)) ys)))

;; for each x in xs do x*each ys - add to zs , aa are units tens hundred thousands etc..
(define (fan2-mult xs ys zs aa)
  (cond
   ((null? xs) zs)
   (else (let ((x (car xs))
	       (xt (cdr xs)))
	   (fan2-mult xt ys (comb (fan3-mult x ys aa) zs) (cons 0 aa))))))

(define (fan-mult xs ys) 
  (fan2-mult xs ys '() '()))

;; three polynomial tests -- all pass
(fan-mult '(3) '(2 4)) ;; (6 12)
(fan-mult '(0 1) '(5 -1)) ;; (0 5 -1) 
(fan-mult '(1 2) '(3 4)) ;; (3 10 8)



;; expr -> 
(define (seval expr)
  (cond
    ((equal? expr 'var) '(0 1))
    ((and (pair? expr) (equal? (car expr) 'const))
     (let ((e1 (car (cdr expr))))
       `(,e1)))
    ((and (pair? expr) (equal? (car expr) 'add))
     (let ((e1 (seval (car (cdr expr))))
	   (e2 (seval (car (cdr (cdr expr))))))
       (comb e1 e2)))
    ((and (pair? expr) (equal? (car expr) 'mult))
     (let ((e1 (seval (car (cdr expr))))
	   (e2 (seval (car (cdr (cdr expr))))))
       (fan-mult e1 e2)))))

;; a rename
(define coeffs seval)

(coeffs 'var)
(coeffs '(const 3))
(coeffs '(add var (const 3)))
(coeffs '(add (const 4) var))
(coeffs '(add (const 4) (const 2)))
(coeffs '(add var (add var (const 3))))
(coeffs '(add var (add var (add var (const 3)))))
(coeffs '(mult var (const 2)))
(coeffs '(add var (add (const 3) (mult var (const 2)))))
(coeffs '(mult (add var (add (const 3) (mult var (const 2)))) (const 4)))
             ;; (* (+ x (+ 3 (* x 2))) 4)  (12 12)

(define (evalp3 x n z)
  (cond
   ((= n 0) x)
   (else (* x (expt z n)))))

(define (evalp2 xs n z)
  (cond
   ((null? xs) 0)
   (else (let ((x (car xs))
	       (xt (cdr xs)))
	   (+ (evalp3 x n z) (evalp2 xt (+ n 1) z))))))

(define (evalp xs z) (evalp2 xs 0 z))

(evalp '(4 2 -1 3) 3) ;;82













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




    
					   
