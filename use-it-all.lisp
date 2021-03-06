:q

(load "interp.lisp")


#|
An expression of the form:
(defun2 name (x ...)
  body)

does three things:
1 -- defines name as a normal Lisp function

2 -- defines a relational counterpart of the function
   (defrel name-rel (x ... o) body'),
   where name-rel is literally name + 'rel', 
   and body' is body, having been compiled to miniKanren

3 -- adds a clause to handle expressions of the form (name x ...).
   [(name x ...) ρ out] =
    (fresh (x-res ...)
      V[x ρ x-res]
      ...
      (name-rel x-res ... out))
   giving them the meaning
|#


;; a classic example
(defun2 rev-acc (ls acc)
  (cond
   ((endp ls) acc)
   (t (rev-acc (cdr ls) (cons (car ls) acc)))))

(run* q (rev-acc-rel '(1 2 3) nil q))

(run 1 q (rev-acc-rel q nil '(3 2 1)))


; the '2800 homework' lemma we want
(suggest-lemma (rev-acc ls acc)
	       ((reverse ls))
	       (((ls (t nil nil))
		 (acc (nil t)))))

; now we can reason about our new reverse!
(defun2 revt (ls)
  (rev-acc ls nil))

(run 1 q (revt-rel q '(1 2 3)))

(run 7 q (revt-rel q q))


;; here's a first attempt, but our test suite wasn't good enough
(suggest-lemma (revt (append a b))
	       (append revt a b)
	       (((a (nil))
		 (b (t)))))


;; here's a second attempt, but we didn't get what we wanted
(suggest-lemma (revt (append a b))
	       (revt a b)
	       (((a (nil))
		 (b (t)))))

;; some more help
(suggest-lemma (revt (append a b))
	       ((revt b) a)
	       (((a (nil))
		 (b (t)))))

; finally 
(suggest-lemma (revt (append a b))
	       ((revt b) (revt a))
	       (((a (nil))
		 (b (t)))))

;;;;;;;;;
;; another classic example
(suggest-lemma (append (append a b) c)
	       (append a append b c)
	       (((a (t nil))
		 (b (nil t))
		 (c (t nil t)))))

;; faster when we give it some help
(suggest-lemma (append (append a b) c)
	       (a (append b c))
	       (((a (t nil))
		 (b (nil t))
		 (c (t nil t)))))


;; We all recognize these definitions...
(defun2 in (x ls)
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(run* q (in-rel q '(1 2 3 4 5) t))

(run 6 q (in-rel 2 q t))

(defun2 tlp (x)
  (cond
   ((equal x nil) t)
   ((consp x) (tlp (cdr x)))
   (t nil)))

(run 6 q
     (tlp-rel q t)
     (in-rel 2 q t))

(defun2 remdups (ls)
  (cond
   ((endp ls) nil)
   ((in (car ls) (cdr ls))
    (remdups (cdr ls)))
   (t (cons (car ls) (remdups (cdr ls))))))

(run 5 q (remdups-rel q '(1 2 3)))

(defun2 remdupst (ls acc)
  (cond
   ((endp ls) acc)
   ((in (car ls) acc)
    (remdupst (cdr ls) acc))
   (t (remdupst (cdr ls) (cons (car ls) acc)))))

(run 5 (q r) (remdupst-rel q r '(1 2 3)))

;; are our test cases good enough?
(suggest-lemma (remdupst ls acc)
	       (remdups ls acc)
	       (((ls (r r))
		 (acc ()))))

;; still not good enough?
(suggest-lemma (remdupst ls acc)
	       (remdups ls acc)
	       (((ls (a r r))
		 (acc (e)))))

;; sanity check – that actually was what we wanted
(suggest-lemma (rev-acc ls acc)
	       ((reverse ls) acc)
	       (((ls (a r r))
		 (acc (e)))))

;; tell it what we want to see
(suggest-lemma (remdupst ls acc)
	       (remdups append (reverse ls) acc)
	       (((ls (a r r))
		 (acc (e)))))

;; this also works
(suggest-lemma (remdupst ls acc)
	       (remdups append reverse acc ls)
	       (((ls (a r r))
		 (acc (e)))))

;; whichever reverse we prefer
(suggest-lemma (remdupst ls acc)
	       (remdups append revt acc ls)
	       (((ls (a r r))
		 (acc (e)))))
