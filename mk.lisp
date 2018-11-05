(defun mymap (f ls)
  (cond
   ((endp ls) nil)
   (t (cons (apply f (list (car ls)))
	    (mymap f (cdr ls))))))

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

;; code for condi = conde-include


(defrel foo (e o)
  (conde
   ((== e '()) (== o 1))))





#|
Users can specify lines to use in two ways:
-- giving specific forms to include/exclude
-- assigning groups of lines, and suggesting to include/exclude groups
|#

(defun disj* (gs)
  (cond
   ((endp gs) (fail))
   ((equal (length gs) 1) (apply (car gs) ()))
   ((consp gs)
    (disj2 (apply (car gs) ())
	   (disj* (cdr gs))))))

(defun conj* (gs)
  (cond
   ((endp gs) (succeed))
   ((equal (length gs) 1) (apply (car gs) ()))
   ((consp gs)
    (conj2 (apply (car gs) ())
	   (conj* (cdr gs))))))


;; separates the include statements into 3 types:
;; the list of lines that are to be included
;; the list of groups whose lines should be included
;; the list of expression forms to be included

#|
(defun exprs-symbols (lls)
  (reduce #'append (mapcar #'expr-symbols lls)
	  :initial-value nil
	  :from-end t))

(defun expr-symbols (ls)
  (cond
   ((symbolp ls) '(vars))
   ((equal (car ls) 'INTERNAL-NUMBER) '(numbers))
   ((equal (car ls) 'INTERNAL-SYMBOL) '(symbols))
   ((equal (car ls) 'INTERNAL-CONS) '(pairs))
   (t (cons (car ls) (exprs-symbols (cdr ls))))))

(defmacro thunk-all (gs)
  `(cond
    ((endp ',gs) nil)
    (t (cons (lambda () (conj ,(cdar gs)))
	    (thunk-all ,(cdr gs))))))


(defmacro run-condi (keep gs)
  `(condi-help ,keep ,gs))

(defmacro condi-help (keep gs)
  `(cond
   ((endp ',gs) (fail))
   (t (if (member ,(caar gs) ,keep)
	  (disj2 (conj ,(cdar gs))
		 (run-condi ,keep ,(cdr gs)))
	(run-condi ,keep ,(cdr gs))))))

(defun select-lns (keepers all ths)
  (cond
   ((endp ths) nil)
   ((member (car all) keepers)
    (cons (car ths) (select-lns keepers (cdr all) (cdr ths))))
   (t (select-lns keepers (cdr all) (cdr ths)))))

;; gather lines from groups (gather-groups -> gg)
(defun gg (gs)
  (reduce #'append
	  (mapcar #'(lambda (e) (apply e ())) gs)
	  :initial-value nil))


(defmacro call-condi-help (i g)
  `(condi-help ,(eval i) ,g))

(defmacro condi (all-gps includes &rest gs)
  `(let* ((all-lns (mapcar #'car ',gs))
	  (inc-gps (split-incs all-lns ',all-gps ',includes nil nil nil))
	  (inc-lns (append (car inc-gps)
			   (gg (cadr inc-gps))
			   (exprs-symbols (caddr inc-gps)))))
     (call-condi-help inc-lns ,gs)))
#|
(defrel foo (e o)
  (condi
   nil
   (line2)
   (line1 (== o 2))
   (line2 (== o 1))))
|#

(defun gp1 () '(line2))


(run 1 q )
|#
