(load "primitives-raw.lsp")

;; Environments

(defrel lookupo (y ρ o)
  (conde
   ((fresh (d)
	   (== ρ `((,y ,o) . ,d))))
   ((fresh (x v d)
	   (== ρ `((,x ,v) . ,d))
	   (lookupo y d o)))))

(defrel extend-env (ρ y v o)
  (== o `((,y ,v) . ,ρ)))

;; The Interpreter with helpers

;; let actually has the semantics of let*
;; for proposed expressions. This is OK for now.
(defrel do-let (es ρ new-ρ)
  (conde
   ((== es '()) (== ρ new-ρ))
   ((fresh (x a d v rho)
	   (== es `((,x ,a) . ,d))
	   (value-of a ρ v)
	   (extend-env ρ x v rho)
	   (do-let es rho new-ρ)))))

(defun expr-for-value-of ()
  '(conde
    ;; environment lookup
    ((lookupo expr ρ o))
    ;; constants
    ((booleanpo expr) (== o expr))
    ((varpo expr) (== o expr))
    ((numberpo expr) (== o expr))
    ((fresh (a d res1 res2)
	    (== expr `(cons ,a ,d))
	    (conso res1 res2 o)
	    (value-of a ρ res1)
	    (value-of d ρ res2)))
    ;; Arithmetic
    ((fresh (n m n-res m-res)
	    (== expr `(+ ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-pluso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(- ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-minuso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(* ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-timeso n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(exp ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-expo n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(< ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-o-fn n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(<= ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-equal-o-fn n-res m-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(> ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-o-fn m-res n-res o)))
    ((fresh (n m n-res m-res)
	    (== expr `(<= ,n ,m))
	    (value-of n ρ n-res)
	    (value-of m ρ m-res)
	    (do-less-than-equal-o-fn m-res n-res o)))
    ;; list stuff
    ((fresh (pr res)
	    (== expr `(car ,pr))
	    (caro res o)
	    (value-of pr ρ res)))
    ((fresh (pr res)
	    (== expr `(cdr ,pr))
	    (cdro res o)
	    (value-of pr ρ res)))
    ((fresh (l1 l2 res1 res2)
	    (== expr `(append ,l1 ,l2))
	    (value-of l1 ρ res1)
	    (value-of l2 ρ res2)
	    (appendo res1 res2 o)))
    ((fresh (l1 res1)
	    (== expr `(reverse ,l1))
	    (value-of l1 ρ res1)
	    (reverso res1 o)))
    ((fresh (es b new-ρ)
	    (== expr `(let ,es ,b))
	    (do-let es ρ new-ρ)
	    (value-of b new-ρ o)))))


(defun expr-for-has-arity ()
  '(conde
    ((== form 'car) (== n 1))
    ((== form 'cdr) (== n 1))
    ((== form 'reverse) (== n 1))
    ((== form 'append) (== n 2))
    ((== form 'let) (== n 2))
    ((== form 'cons) (== n 2))
    ((== form '*) (== n 2))
    ((== form '+) (== n 2))
    ((== form '-) (== n 2))
    ((== form 'exp) (== n 2))
    ((== form '<) (== n 2))
    ((== form '>) (== n 2))
    ((== form '<=) (== n 2))
    ((== form '>=) (== n 2))
    ((succeed))))

(defun all-lines ()
  '(var
    boolean symbol number cons
    + - * exp < <= > >=
    car cdr append reverse
    let))

(defmacro reset-interp ()
  `(progn
     (defrel value-of (expr ρ o)
       ,(expr-for-value-of))
     (defrel has-arity (form n)
       ,(expr-for-has-arity))
     (defun all-lines ()
       ,(all-lines))))

(reset-interp)

;;;;;;;;;;

;; Constraints on expressions

(defrel contains-form (form e)
  (conde
   ((== form e))
   ((fresh (op e1)
	   (== e `(,op ,e1))
	   (conde
	    ((has-arity form 1) (== op form))
	    ((contains-form form e1)))))
   ((fresh (op e1 e2)
	   (== e `(,op ,e1 ,e2))
	   (conde
	    ((has-arity form 2) (== op form)) 
	    ((contains-form form e1))
	    ((contains-form form e2)))))
   ((fresh (op e1 e2 e3)
	   (== e `(,op ,e1 ,e2 ,e3))
	   (conde
	    ((has-arity form 3) (== op form))
	    ((contains-form form e1))
	    ((contains-form form e2))
	    ((contains-form form e3)))))
   ((fresh (op e1 e2 e3 e4)
	   (== e `(,op ,e1 ,e2 ,e3 ,4))
	   (conde
	    ((has-arity form 4) (== op form))
	    ((contains-form form e1))
	    ((contains-form form e2))
	    ((contains-form form e3))
	    ((contains-form form e4)))))))

#|
(defrel contains-form (form e)
  (conde
   ((== form e))
   ((fresh (op e1)
	   (== e `(,op ,e1))
	   (conde
	    ( (== op form))
	    ((contains-form form e1)))))
   ((fresh (op e1 e2)
	   (== e `(,op ,e1 ,e2))
	   (conde
	    ( (== op form)) 
	    ((contains-form form e1))
	    ((contains-form form e2)))))
   ((fresh (op e1 e2 e3)
	   (== e `(,op ,e1 ,e2 ,e3))
	   (conde
	    ( (== op form))
	    ((contains-form form e1))
	    ((contains-form form e2))
	    ((contains-form form e3)))))
   ((fresh (op e1 e2 e3 e4)
	   (== e `(,op ,e1 ,e2 ,e3 ,4))
	   (conde
	    ( (== op form))
	    ((contains-form form e1))
	    ((contains-form form e2))
	    ((contains-form form e3))
	    ((contains-form form e4)))))))|#

(defrel contains-forms (fms e)
  (conde
   ((== '() fms))
   ((fresh (a d)
	   (== fms `(,a . ,d))
	   (contains-form a e)
	   (contains-forms d e)))))

(defrel passes-tests (e2 tests results)
     (conde
      ((== tests '()))
      ((fresh (a d v r1 rs)
	      (== tests `(,a . ,d))
	      (== results `(,r1 . ,rs))
	      (value-of e2 a r1)
	      (passes-tests e2 d rs)))))

#|
(defrel find-equivalent (forms e tests results)
  (passes-tests e tests results)
  (contains-forms forms e))
(defrel find-equivalent (forms e tests results)
  (contains-forms forms e)
  (passes-tests e tests results))
|#

(defrel find-equivalent (forms e tests results)
  (conde
   ((passes-tests e tests results)
    (contains-forms forms e))
   ((contains-forms forms e)
    (passes-tests e tests results))))
