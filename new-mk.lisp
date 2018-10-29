;; Functions I'm defining instead of using built-ins, because lisp gets picky
(defun lookup (e s)
  (cond
   ((empty? s) nil)
   ((equal e (caar s)) (car s))
   (t (lookup e (cdr s)))))

(defun member (x ls)
  (cond
   ((empty ls) nil)
   ((equal x (car ls)) t)
   (t (member x (cdr ls)))))

(defun mymap (f ls)
  (cond
   ((endp ls) nil)
   (t (cons (apply f (list (car ls)))
	    (mymap f (cdr ls))))))
;;;;;;;;;;;;;;;;

(defconst *empty-c*
  '(() () () () () () ()))

(defconst *eigen-tag*
  '(VECTOR eigen-tag))

(defun c->B  (c) (car c))
(defun c->E (c) (cadr c))
(defun c->S (c) (caddr c))
(defun c->D (c) (cadddr c))
(defun c->Y (c) (cadddr (cdr c)))
(defun c->N (c) (cadddr (cddr c)))
(defun c->T (c) (cadddr (cdddr c)))

(defmacro lambdaf@ (ls e) `(lambda () ,e))

(defmcaro lambdag1@ (ls e)
  `(lambda ,ls ,e))

(defmacro lambdag2@ (ls e)
  `(lambda (c)
     (let ((B (c->B c)) (E (c->E c)) (S (c->S c)))
       ,e)))

(defmacro lambda3@ (ls e)
  `(lambda (c)
     (let ((B (c->B c)) (E (c->E c)) (S (c->S c)) (D (c->D c))
	   (Y (c->Y c)) (N (c->N c)) (T (c->T c)))
         ,e)))

(defmacro inc (e) `(lambdaf@ () ,e))

(defun rhs (pr) (cdr pr))
(defun lhs (pr) (car pr))


;;;;;;;;;;;;;;

(defun eigen-var ()
  `(VECTOR ,*eigen-tag*))

(defun eigenp (x)
  (and (consp x)
       (equal (car x) 'VECTOR)
       (equal (cadr x) *eigen-tag*)))

(defun lvar (e)
  `(VECTOR ,e))

(defun lvarp (x)
  (and (consp x)
       (equal (car x) 'VECTOR)
       (not (equal (cadr x) *eigen-tag*))))


;;;;;;;;;;;;;;;



(defun walk (v s)
  (let ((a (and (lvarp v) (lookup v s))))
    (cond
     ((consp a) (walk (rhs a) s))
     (t v))))


(defun prefix-S (S+ S)
  (cond
   ((equal S+ S) '())
   (else (cons (car S+)
	       (prefix-S (cdr S+) S)))))


(defun unify (u v s)
  (let ((u (walk u s))
	(v (walk v s)))
    (cond
     ((equal u v) s)
     ((lvarp u) (ext-s-check u v s))
     ((lvarp v) (ext-s-check v u s))
     ((and (consp u) (consp v))
      (let ((s (unify (car u) (car v) s)))
	(and s (unify (cdr u) (cdr v) s))))
     ((or (eigenp u) (eigenp v)) nil)
     ((equal? u v) s)
     (else nil))))


(defun occurs-check (x v s)
  (let ((v (walk v s)))
    (cond
     ((lvarp v) (equal v x))
     ((consp v) 
      (or 
       (occurs-check x (car v) s)
       (occurs-check x (cdr v) s)))
     (else nil))))

(define eigen-occurs-check (e* x s)
  (let ((x (walk x s)))
    (cond
     ((lvarp x) nil)
     ((eigenp x) (member x e*))
     ((consp x) 
      (or 
       (eigen-occurs-check e* (car x) s)
       (eigen-occurs-check e* (cdr x) s)))
     (else nil))))

;;;;;;;;;;;;;;;;;;;;;

(defconst *empty-f* (lambdaf@ () (mzero)))

(defun ext-s-check (x v s)
  (cond
   ((occurs-check x v s) nil)
   (else (cons `(,x . ,v) s))))

(defun unify* (S+ S)
  (unify (mymap lhs S+) (mymap rhs S+) S))

#|
(defmacro get-e0 (ls) `(cadar ,ls))
(defmacro get-e1 (ls) `(cadr (cadr ,ls)))
(defmacro get-e2 (ls) `(cadr (caddr ,ls)))
(defmacro get-e3 (ls) `(cadr (cadddr ,ls)))

(defmacro case-inf (e &rest ls)
  `(let ((c-inf ,e))
     (cond
      ((not c-inf) (get-e0 ,ls))
      ((and (consp c-inf)
	    (or (not (cdr c-inf))
		(consp (cdr c-inf))))
       e2)
      ((consp c-inf)
       (let ((c (car c-inf))
	     (f (cdr c-inf)))
	 e3))
      (t (let ((f c-inf))
	   (get-e1 ,ls))))))
|#

(define mzero () nil)

(define unit (c) c)

(define choice (c f) (cons c f))


(defmacro eigen (xs &rest gs)
  `(lambdag2@
    (let (()))))

(defmacro bind* (e &rest gs)
  `(cond
    ((endp ,gs) e)
    (t (bind* (bind ,e ,(car gs)) . ,(cdr gs)))))

(defun bind (c-inf g)
  (cond
   ((not c-inf) (mzero))
   ((not (consp c-inf))
    (inc (bind (c-inf) g)))
   ((not (and (consp c-inf)
	      (not (equal (cdr c-inf) nil))
	      (not (consp (cdr c-inf)))))
    (g c-inf))
   (t (let ((c (car c-inf))
	    (f (cdr c-inf)))
	(mplus (g c) (lambdaf@ () (bind (f) g)))))))



(defmacro fresh-help (xs gs)
  `(cond
    ((endp ',xs) (bind*))
    ((consp ',xs)
     (call/fresh (gensym)
		 (lambda (,(car xs))
		   (fresh-help ,(cdr xs) ,gs))))))


(defmacro fresh-help (xs gs B E S D Y N T)
  (cond
   ((endp xs) `(make-bind gs B E S D Y NT ))))

(defmacro fresh (xs &rest gs)
  `(lambdag3@
    (lambda ()
      )))














(defun lvar (e) (list 'lvar e))

(defun lvarp (e)
  (and (consp e)
       (equal (car e) 'lvar)
       (consp (cdr e))
       (symbolp (cadr e))))

;; Substitutions
(defun substp (s)
  (cond
   ((equal s '(SUBST))
    (and (consp (car s))
	 (lvarp (caar s))
	 (substp (cdr s))))))

(defun empty? (s)
  (equal s '(SUBST)))

(defun lookup (e s)
  (cond
   ((empty? s) nil)
   ((equal e (caar s)) (car s))
   (t (lookup e (cdr s)))))

(defun walk (v s)
  (let ((a (and (lvarp v) (lookup v s))))
    (cond
     ((consp a) (walk (cadr a) s))
     (t v))))

(defun ext-s (x v s)
  (cons `(,x ,v) s))


(defun unify (u v s)
  (let ((u (walk u s))
	(v (walk v s)))
    (cond
     ((equal u v) s)
     ((lvarp u) (ext-s u v s))
     ((lvarp v) (ext-s v u s))
     ((and (consp u) (consp v))
      (let ((s (unify (car u) (car v) s)))
	(and s
	     (unify (cdr u) (cdr v) s))))
     (t nil))))

(defun walk* (v s)
  (let ((v (walk v s)))
    (cond
     ((lvarp v) v)
     ((consp v)
      (cons
       (walk* (car v) s)
       (walk* (cdr v) s)))
     (t v))))

(defun get-name (n)
  (cond
   ((equal n 0) "0")
   ((equal n 1) "1")
   ((equal n 2) "2")
   ((equal n 3) "3")
   ((equal n 4) "4")
   ((equal n 5) "5")
   ((equal n 6) "6")
   ((equal n 7) "7")
   ((equal n 8) "8")
   ((equal n 9) "9")
   (t (concatenate 'string
		   (get-name (floor n 10))
		   (get-name (mod n 10))))))

(defun reify-sym (n)
  (intern (concatenate 'string "_" (get-name n))))

(defun reify-s (v r)
  (let ((v (walk v r)))
    (cond
     ((lvarp v)
      (let ((n (length r)))
	(let ((rn (reify-sym (- n 1))))
	  (cons `(,v ,rn) r))))
     ((consp v)
      (let ((r (reify-s (car v) r)))
	(reify-s (cdr v) r)))
     (t r))))

(defun reify (v)
  (lambda (s)
    (let ((v (walk* v s)))
      (let ((r (reify-s v '(SUBST))))
	(walk* v r)))))

(defun == (u v)
  (lambda (s)
    (let ((s (unify u v s)))
      (if s `(,s) '()))))

(defun succeed ()
  (lambda (s)
    `(,s)))

(defun fail ()
  (lambda (s)
    '()))

(defun append-inf (s-inf t-inf)
  (cond
   ((equal nil s-inf) t-inf)
   ((consp s-inf)
    (cons (car s-inf)
	  (append-inf (cdr s-inf) t-inf)))
   (t (lambda ()
	   (append-inf t-inf (apply s-inf ()))))))

(defun disj2 (g1 g2)
  (lambda (s)
    (append-inf (apply g1 (list s))
		(apply g2 (list s)))))

(defun take-inf (n s-inf)
  (cond
   ((and n (equal n 0)) '())
   ((equal s-inf nil) '())
   ((consp s-inf)
    (cons (car s-inf)
	  (take-inf (and n (- n 1))
		    (cdr s-inf))))
   (t (take-inf n (apply s-inf ())))))

(defun conj2 (g1 g2)
  (lambda (s)
    (append-map-inf g2 (apply g1 (list s)))))

(defun append-map-inf (g s-inf)
  (cond
   ((equal s-inf '()) '())
   ((consp s-inf)
    (append-inf (apply g (list (car s-inf)))
		(append-map-inf g (cdr s-inf))))
   (t (lambda ()
	(append-map-inf g (apply s-inf ()))))))

(defun call/fresh (name f)
  (apply f (list (lvar name))))

(defun run-goal (n g)
  (take-inf n (apply g (list '(SUBST)))))


(defmacro disj (gs)
  `(cond
    ((endp ',gs) (fail))
    ((equal (length ',gs) 1) ,(car gs))
    ((consp ',gs)
     (disj2 ,(car gs)
	    (disj ,(cdr gs))))))

(defmacro conj (gs)
  `(cond
    ((endp ',gs) (succeed))
    ((equal (length ',gs) 1) ,(car gs))
    ((consp ',gs)
     (conj2 ,(car gs)
	    (conj ,(cdr gs))))))

(defmacro conde-help (gs)
  `(cond
    ((endp ',gs) (fail))
    ((equal (length ',gs) 1) (conj ,(car gs)))
    (t
     (disj2 (conj ,(car gs))
	    (conde-help ,(cdr gs))))))

(defmacro conde (&rest gs)
  `(conde-help ,gs))

(defmacro fresh-help (xs gs)
  `(cond
    ((endp ',xs) (conj ,gs))
    ((consp ',xs)
     (call/fresh (gensym)
		 (lambda (,(car xs))
		   (fresh-help ,(cdr xs) ,gs))))))

(defmacro fresh (xs &rest gs)
  `(fresh-help ,xs ,gs))

(defmacro defrel (name xs &rest gs)
  `(defun ,name ,xs
     (lambda (s)
       (lambda ()
	 (apply (conj ,gs) (list s))))))

(defmacro run* (q &rest gs)
  `(run nil ,q . ,gs))

(defmacro run-more (n xs gs)
  (let ((q (gensym)))
    `(let ((q-var (lvar ',q)))
       (mymap (reify q-var)
	      (run-goal ,n
			(fresh ,xs
			       (== q-var (list . ,xs))
			       . ,gs))))))

(defmacro run (n xs &rest gs)
  `(cond
    ((symbolp ',xs)
     (let ((q (lvar ',xs)))
       (mymap (reify q)
	       (run-goal ,n (conj ,gs)))))
    (t (run-more ,n ,xs ,gs))))
