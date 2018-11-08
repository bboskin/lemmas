(include-book "itest-cgen")
(include-book "itest-ithm")

(acl2s-defaults :set sampling-method :be)
:q

(load "suggest-lemma.lisp")

(suggest-lemma (reverse (append a b))
	       :required-expressions a b reverse
	       :with reverse append
	       :hyps (true-listp a) (true-listp b))
#|
(IMPLIES (AND (TRUE-LISTP A) (TRUE-LISTP B))
	 (EQUAL (REVERSE (APPEND A B))
		(APPEND (REVERSE B) A)))
|#
(defunc2 rev-acc (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract t
  (cond
   ((endp ls) acc)
   (t (rev-acc (cdr ls) (cons (car ls) acc)))))

(suggest-lemma (rev-acc ls acc)
	       :required-expressions ls acc
	       :with append reverse
	       :hyps (true-listp ls) (true-listp acc))

(suggest-lemma (rev-acc ls acc)
	       :required-expressions ls reverse
	       :with reverse append
	       :hyps (true-listp ls) (true-listp acc))

(suggest-lemma (rev-acc ls acc)
	       :required-expressions reverse ls
	       :with reverse append
	       :hyps (true-listp ls) (true-listp acc))

(suggest-lemma (rev-acc ls acc)
	       :required-expressions (reverse ls)
	       :with reverse append
	       :hyps (true-listp ls) (true-listp acc))

(defunc2 in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defunc2 tlp (x)
  :input-contract t
  :output-contract (booleanp (tlp x))
  (cond
   ((equal x nil) t)
   ((consp x) (tlp (cdr x)))
   (t nil)))

(defunc2 remdups (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp ls)
  (cond
   ((endp ls) nil)
   ((in (car ls) (cdr ls))
    (remdups (cdr ls)))
   (t (cons (car ls) (remdups (cdr ls))))))

(defunc2 remdupst (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (true-listp (remdupst ls acc))
  (cond
   ((endp ls) acc)
   ((in (car ls) acc)
    (remdupst (cdr ls) acc))
   (t (remdupst (cdr ls) (cons (car ls) acc)))))

(suggest-lemma (remdupst ls acc)
	       :required-expressions remdups ls
	       :with append reverse remdups
	       :hyps (true-listp ls) (true-listp acc))

(time (suggest-lemma (remdupst ls acc)
		     :required-expressions remdups ls
		     :with append rev-acc
		     :hyps (true-listp ls) (true-listp acc)))

(time (suggest-lemma (rev-acc ls acc)
		     :required-expressions acc reverse ls
		     :with append
		     :hyps (true-listp ls) (true-listp acc)))

(time (suggest-lemma (remdupst ls acc)
		     :required-expressions (remdups (append (reverse ls) acc))
		     :hyps (true-listp ls) (true-listp acc)))

;; this one sometimes takes a long time... to look into
(time (suggest-lemma (remdupst ls acc)
		     :required-expressions remdups append reverse acc ls
		     :hyps (true-listp ls) (true-listp acc)))

(time (suggest-lemma (remdupst ls acc)
		     :required-expressions append reverse acc
		     :with remdups
		     :hyps (true-listp ls) (true-listp acc)))
