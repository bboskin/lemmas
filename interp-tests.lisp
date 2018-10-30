(load "~/lemmas/interp-acl2.lisp")
(load "~/lemmas/mk.lisp")
(load "~/lemmas/frontend.lisp")

;; tests to just the interpreter
(read-back (run* q (value-of '(cons t nil) '() q)))
(read-back (run* q (value-of (clean-expr '(cons 4 (cons 'e (cons 2 nil)))) '() q)))
(read-back (run* q (value-of (clean-expr '(append '(4 e 3) '(1 e 2))) '() q)))
(read-back (run* q (value-of (clean-expr '(reverse '(a 5 b))) '() q)))

;; tests using suggest-lemma, but only built-in functions,
;; to test cleaners and interpreter running backwards

(suggest-lemma (append a (append b c))
	       (append a b c)
	       (((a (3))
		 (b (e r f))
		 (c (5 w)))))

(suggest-lemma (reverse (append a b))
	       (append (reverse b) a)
	       (((a (e 3 f))
		 (b (4 3)))))

(suggest-lemma (cons a (reverse b))
	       (reverse append)
	       (((a 4)
		 (b (2 3)))))

(suggest-lemma (reverse (reverse b))
	       (b)
	       (((b (e 3)))))

(suggest-lemma (reverse (reverse (reverse b)))
	       (b)
	       (((b (e 3)))))



;; tests using build-in-functions

(defun2 rev-acc (ls acc)
  (cond
   ((endp ls) acc)
   (t (rev-acc (cdr ls) (cons (car ls) acc)))))

(suggest-lemma (rev-acc ls acc)
	       (append reverse ls)
	       (((ls (t nil 3))
		 (acc (nil t)))))

(defun2 revt (ls)
  (rev-acc ls nil))

(suggest-lemma (rev-acc ls acc)
	       ((reverse ls) acc)
	       (((ls (a r r))
		 (acc (e)))))

(suggest-lemma (revt (append a b))
	       (append (revt a) (revt b))
	       (((a (3 e))
		 (b (t 4)))))

(defun2 in (x ls)
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defun2 tlp (x)
  (cond
   ((equal x nil) t)
   ((consp x) (tlp (cdr x)))
   (t nil)))

(defun2 remdups (ls)
  (cond
   ((endp ls) nil)
   ((in (car ls) (cdr ls))
    (remdups (cdr ls)))
   (t (cons (car ls) (remdups (cdr ls))))))

(defun2 remdupst (ls acc)
  (cond
   ((endp ls) acc)
   ((in (car ls) acc)
    (remdupst (cdr ls) acc))
   (t (remdupst (cdr ls) (cons (car ls) acc)))))

;; takes a good 15 secs or so
(suggest-lemma (remdupst ls acc)
	       (remdups ls acc)
	       (((ls (r r))
		 (acc ()))))

(suggest-lemma (remdupst ls acc)
	       ((rev-acc ls acc))
	       (((ls (a r r))
		 (acc (e)))
		((ls (a a r))
		 (acc (e)))))

;; takes 5ish seconds
(suggest-lemma (remdupst ls acc)
	       (remdups append (reverse ls) acc)
	       (((ls (a r r))
		 (acc (e)))))

(suggest-lemma (remdupst ls acc)
	       (remdups append reverse acc ls)
	       (((ls (a r r))
		 (acc (e)))))

(suggest-lemma (remdupst ls acc)
	       (remdups append revt acc ls)
	       (((ls (a r r))
		 (acc (e)))))
