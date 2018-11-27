(in-package "ACL2S")
;(load "primitives-raw.lsp")
;(load "helpers-raw.lsp")
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

(defrel do-cond (es ρ o)
  (conde
   ((== es '()) (== o nil))
   ((fresh (tst c rst b)
	   (== es `((,tst ,c) . ,rst))
	   (value-of tst ρ b)
	   (conde
	    ((== b nil) (do-cond rst ρ o))
	    ((non-nilo b) (value-of c ρ o)))))))

;; the wrapper function accepting either lists or strings, as in ACL2S
(defrel reverso (x o)
  (conde
   ((ls-reverso x o))
   ((str-revo x o))))

(defun new-clause (num-args vars pmatch recursive-calls final)
  (cond
   ((= num-args 0)
    `((fresh ,vars
	     (== expr ,pmatch)
	     ,@recursive-calls
	     (,@final o))))
   (t (let ((subexpr (next-var))
	    (subres (next-var)))
	(let ((new-vars `(,@vars ,subexpr ,subres))
	      (new-pmatch `(,@pmatch ,subexpr))
	      (new-rec-calls
	       `(,@recursive-calls (value-of ,subexpr ρ ,subres)))
	      (new-final `(,@final ,subres)))
	  (new-clause
	   (- num-args 1) new-vars new-pmatch new-rec-calls new-final))))))

(defun make-init-value-of-clause (e)
  (let* ((name (car e))
	 (arity (if (cadr e) (cadr e) 2))
	 (rel-name (if (cadr e) (caddr e) (car (cdddr e)))))
    (new-clause arity nil `(list ',name) nil (list rel-name))))

(defun expr-for-value-of ()
  `(conde
    ;; environment lookup
    ((lookupo expr ρ o))
    ;; constants
    ((booleanpo expr) (== o expr))
    ((varpo expr) (== o expr))
    ((numberpo expr) (== o expr))
    ((stringpo expr) (== o expr))
    ((charpo expr) (== o expr))
    ;; cons, car, cdr are hard-coded since they are non-recursive, meaning
    ;; that doing the helper function first is better
    ((fresh (a d res1 res2)
	    (== expr `(cons ,a ,d))
	    (conso res1 res2 o)
	    (value-of a ρ res1)
	    (value-of d ρ res2)))
    ((fresh (pr res) (== expr `(car ,pr))
	    (caro res o) (value-of pr ρ res)))
    ((fresh (pr res) (== expr `(cdr ,pr))
	    (cdro res o) (value-of pr ρ res)))
    ;; More complex build-ins (let, if, cond)
    ((fresh (es b new-ρ)
	    (== expr `(let ,es ,b))
	    (do-let es ρ new-ρ)
	    (value-of b new-ρ o)))
    ((fresh (tst c a b)
	    (== expr `(if ,tst ,c ,a))
	    (value-of tst ρ b)
	    (conde
	     ((== b nil) (value-of a ρ o))
	     ((non-nilo b) (value-of c ρ o)))))
    ((fresh (es)
	    (== expr `(cond . ,es))
	    (do-cond es ρ o)))
    ;; everything else -- standard recursion & completion
    . ,(mapcar #'make-init-value-of-clause lemma-built-ins)))

(defun all-forms ()
  (append 
   '(var boolean symbol number string char cons car cdr let if cond)
   (mapcar #'car lemma-built-ins)))

(defun make-init-has-arity-clause (pr)
  (let ((name (car pr))
	(arity (cadr pr)))
    `((== form ',name) (== n ,arity))))

(defun expr-for-has-arity ()
  `(conde
    ((== form 'cons) (== n 2))
    ((== form 'car) (== n 1))
    ((== form 'cdr) (== n 1))
    ((== form 'if) (== n 3))
    ((== form 'let) (== n 2))
    ((== form 'varp) (== n 1))
    ((== form 'conspp) (== n 1))
    ((== form 'booleanp) (== n 1))
    ((== form 'symbolp) (== n 1))
    ((== form 'stringp) (== n 1))
    ((== form 'charp) (== n 1))
    ((== form 'cond))
    ,@(mapcar #'make-init-has-arity-clause lemma-built-ins)
    ((succeed))))

(defmacro reset-interp ()
  `(progn
     (defrel value-of (expr ρ o)
       ,(expr-for-value-of))
     (defrel has-arity (form n)
       ,(expr-for-has-arity))
     (defun all-forms ()
       ',(all-forms))))

(reset-interp)

;; Constraints on expressions

#|
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
|#



#|
Attempt to encode Herbrand levels

(defrel one-contains-form (form es n)
  (fresh (a d)
    (== es `(,a . ,d))
    (conde
     ((contains-form form a n))
     ((one-contains-form form d n)))))

(defrel contains-form (form e n)
  (conde
   ((== form e))
   ((has-arity form 1)
    (fresh (e1) (== e `(,form ,e1))))
   ((has-arity form 2)
    (fresh (e1 e2) (== e `(,form ,e1 ,e2))))
   ((has-arity form 3)
    (fresh (e1 e2 e3) (== e `(,form ,e1 ,e2 ,e3))))
   ((fresh (op es)
      (== e `(,op . ,es))
      (conde
       ((== op form))
       ((fresh (n-1)
	  (pluso '(1) n-1 n)
	  (one-contains-form form es n-1))))))))

(defrel contains-forms (fms e n)
  (conde
   ((== '() fms))
   ((fresh (a d)
	   (== fms `(,a . ,d))
	   (contains-form a e n)
	   (contains-forms d e n)))))

(defrel passes-tests (e2 tests results)
     (conde
      ((== tests '()))
      ((fresh (a d v r1 rs)
	      (== tests `(,a . ,d))
	      (== results `(,r1 . ,rs))
	      (value-of e2 a r1)
	      (passes-tests e2 d rs)))))

(defrel find-equivalent (n forms e tests results)
  (conde
   ((contains-forms forms e n)
    (passes-tests e tests results))
   ((fresh (n+1)
      (pluso '(1) n n+1)
      (find-equivalent n+1 forms e tests results)))))
|#

(defrel one-contains-form (form es)
  (fresh (a d)
    (== es `(,a . ,d))
    (conde
     ((contains-form form a))
     ((one-contains-form form d)))))

(defrel contains-form (form e)
  (conde
   ((== form e))
   ((has-arity form 1)
    (fresh (e1) (== e `(,form ,e1))))
   ((has-arity form 2)
    (fresh (e1 e2) (== e `(,form ,e1 ,e2))))
   ((has-arity form 3)
    (fresh (e1 e2 e3) (== e `(,form ,e1 ,e2 ,e3))))
   ((fresh (op es)
      (== e `(,op . ,es))
      (conde
       ((== op form))
       ((one-contains-form form es)))))))

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

(defrel find-equivalent (forms e tests results)
  (conde
   ;((passes-tests e tests results))
   ((contains-forms forms e)
    (passes-tests e tests results)))
  (contains-forms forms e))
#|

|#


