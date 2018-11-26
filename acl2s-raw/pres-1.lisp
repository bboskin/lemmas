(defttag t)
(include-book "lemma-synth" :uncertified-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;
;;Example 1: The exam lemma
;;;;;;;;;;;;;;;;;;;;;;;;;

(defunc2 in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (first ls)) t)
   (t (in x (rest ls)))))

(defunc2 nodups (ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (nodups ls))
  (cond
   ((endp ls) t)
   ((in (first ls) (rest ls)) nil)
   (t (nodups (rest ls)))))

(defunc2 remdups (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp (remdups ls))
  (cond
   ((endp ls) nil)
   ((in (first ls) (rest ls))
    (remdups (rest ls)))
   (t (cons (first ls) (remdups (rest ls))))))

(defunc2 remdupst (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (true-listp (remdupst ls acc))
  (cond
   ((endp ls) acc)
   ((in (car ls) acc)
    (remdupst (cdr ls) acc))
   (t (remdupst (cdr ls) (cons (car ls) acc)))))

(defgroup exam-fns in nodups append reverse remdups remdupst cons)

(suggest-lemma (remdupst ls acc)
	       :required-expressions remdups append reverse
	       :with exam-fns
	       :hyps (nodups acc))

;; This is the lemma we want, but we need to do some work first
#|
(defthm remdupst-remdups
  (IMPLIES (AND (TRUE-LISTP LS)
		(TRUE-LISTP ACC)
		(NODUPS ACC))
	   (EQUAL (REMDUPST LS ACC)
		  (REMDUPS (APPEND (REVERSE LS) ACC)))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Creating a small library

;; Lemma 1
(suggest-lemma (remdups x)
	       :with exam-fns
	       :hyps (true-listp x) (nodups x))

(defthm remdups-id
  (IMPLIES (AND (TRUE-LISTP X)
		(TRUE-LISTP X)
		(NODUPS X))
	   (EQUAL (REMDUPS X) X)))

;; Lemma 2
(suggest-lemma (in b (append x (cons a y)))
	       :required-expressions (append x y)
	       :with exam-fns
	       :complete-hyps nil
	       :hyps (true-listp x) (true-listp y) (in a y))

(defthm foo
  (IMPLIES (AND (TRUE-LISTP X)
              (TRUE-LISTP Y)
              (IN A Y))
         (EQUAL (IN B (APPEND X (CONS A Y)))
                (IN B (APPEND X Y)))))

;; Lemma 3
(suggest-lemma (remdups (append x (cons a y)))
	       :required-expressions (append x y)
	       :with exam-fns
	       :complete-hyps nil
	       :hyps (true-listp x) (true-listp y) (in a y))

(defthm remdups-app-in-cons
  (IMPLIES (AND (TRUE-LISTP X)
		(TRUE-LISTP Y)
		(IN A Y))
	   (EQUAL (REMDUPS (APPEND X (CONS A Y)))
		  (REMDUPS (APPEND X Y)))))

;; The final theorem
(defthm remdupst-lemma
  (IMPLIES (AND (TRUE-LISTP LS)
		(TRUE-LISTP ACC)
		(NODUPS ACC))
	   (EQUAL (REMDUPST LS ACC)
		  (REMDUPS (APPEND (REVERSE LS) ACC)))))
