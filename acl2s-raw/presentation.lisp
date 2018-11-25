(defttag t)
(include-book "top" :uncertified-okp t)


;; Show this to Pete
(thm (IMPLIES (AND (TRUE-LISTP ACL2S::X)
		   (OR (TRUE-LISTP (BINARY-APPEND ACL2S::X ACL2S::Y))
		       (STRINGP (BINARY-APPEND ACL2S::X ACL2S::Y))))
	      (EQUAL (REVERSE (APPEND ACL2S::X ACL2S::Y))
		     (REVERSE (APPEND ACL2S::X ACL2S::Y)))))

(test? (IMPLIES (AND (TRUE-LISTP ACL2S::X)
		     (OR (TRUE-LISTP (BINARY-APPEND ACL2S::X ACL2S::Y))
			 (STRINGP (BINARY-APPEND ACL2S::X ACL2S::Y))))
		(EQUAL (REVERSE (APPEND ACL2S::X ACL2S::Y))
		       (REVERSE (APPEND ACL2S::X ACL2S::Y)))))

(IMPLIES (AND (TRUE-LISTP ACL2S::X)
	      (OR (TRUE-LISTP (BINARY-APPEND ACL2S::X ACL2S::Y))
		  (STRINGP (BINARY-APPEND ACL2S::X ACL2S::Y))))
	 (EQUAL (REVERSE (APPEND ACL2S::X ACL2S::Y))
		(REVERSE (APPEND ACL2S::X ACL2S::Y))))

(suggest-lemma (reverse (append x y))
	       :with reverse append)

;;;;;;;;;;;;;;;;;;;;;;;;;
;;Example 1: The exam lemma
;;;;;;;;;;;;;;;;;;;;;;;;;

(defunc2 in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defunc2 nodups (ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (nodups ls))
  (cond
   ((endp ls) t)
   ((in (car ls) (cdr ls)) nil)
   (t (nodups (cdr ls)))))

(defunc2 remdups (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp (remdups ls))
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
	       :required-expressions remdups append reverse
	       :hyps (nodups acc))
#|
(IMPLIES (AND (TRUE-LISTP ACL2S::LS)
	      (TRUE-LISTP ACL2S::ACC)
	      (ACL2S::NODUPS ACL2S::ACC))
	 (EQUAL (ACL2S::REMDUPST ACL2S::LS ACL2S::ACC)
		(ACL2S::REMDUPS (APPEND (REVERSE ACL2S::LS) ACL2S::ACC))))
|#

(defthm remdupst-lemma
  (IMPLIES (AND (TRUE-LISTP LS)
              (TRUE-LISTP ACC)
              (NODUPS ACC))
         (EQUAL (REMDUPST LS ACC)
                (REMDUPS (APPEND (REVERSE LS) ACC)))))

(suggest-lemma (append (reverse ls) acc)
	       :required-expressions append (reverse (cdr ls)) cons acc
	       :with car
	       :hyps (consp ls))

;; TODO -> finish off proof when we can see how I did it on exam
(defthm append-revv
  (IMPLIES (AND (TRUE-LISTP (REVERSE LS))
		(OR (TRUE-LISTP LS) (STRINGP LS))
		(CONSP LS))
	   (EQUAL (APPEND (REVERSE LS) ACC)
		  (APPEND (REVERSE (CDR LS))
			  (CONS (CAR LS) ACC)))))

;; eventually
(defthm remdupst-lemma
  (IMPLIES (AND (TRUE-LISTP LS)
              (TRUE-LISTP ACC)
              (NODUPS ACC))
         (EQUAL (REMDUPST LS ACC)
                (REMDUPS (APPEND (REVERSE LS) ACC)))))

(suggest-lemma (remdupst ls acc)
	       :required-expressions remdupst (cdr ls) acc
	       :hyps (consp ls) (in (car ls) acc))

(suggest-lemma (remdupst ls acc)
	       :required-expressions remdupst (cdr ls) (cons (car ls) acc)
	       :hyps (consp ls) (not (in (car ls) acc)))



(defunc2 remdups-fast (ls)
  :input-contract (true-listp ls)
  :output-contract (true-listp (remdups-fast ls))
  (remdupst ls nil))

(suggest-lemma (in x ls)
	       :required-expressions (remdups-fast ls) x
	       :with in)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Questions from homework 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata flat-input
  (oneof (cons flat-input flat-input) integer boolean character))

(defunc2 flatten (x)
  :input-contract (flat-inputp x)
  :output-contract (true-listp (flatten x))
  (cond ((not (consp x)) (cons x nil))
        (t (append (flatten (car x)) (flatten (cdr x))))))

(defunc2 mc-flatten-acc (x a)
  :input-contract (and (flat-inputp x) (true-listp a))
  :output-contract (true-listp (mc-flatten-acc x a))
  (cond ((not (consp x)) (cons x a))
        (t (mc-flatten-acc (car x)
                           (mc-flatten-acc (cdr x) a)))))

(suggest-lemma (mc-flatten-acc a l)
	       :with flatten append)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Quicksort and Insertion sort
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata2 loi (listof integer))

(defunc2 orderedp (ls)
  :input-contract (loip ls)
  :output-contract (booleanp (orderedp ls))
  (cond
   ((endp ls) t)
   ((endp (cdr ls)) t)
   ((<= (car ls) (car (cdr ls)))
    (orderedp (cdr ls)))
   (t nil)))

(defunc2 my-remove (x ls)
  :input-contract (loip ls)
  :output-contract (loip (my-remove x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) (cdr ls))
   (t (cons (car ls) (my-remove x (cdr ls))))))

(defunc2 perm (l1 l2)
  :input-contract (and (loip l1) (loip l2))
  :output-contract (booleanp (perm l1 l2))
  (cond
   ((endp l1) (endp l2))
   ((in (car l1) l2)
    (perm (cdr l1) (my-remove (car l1) l2)))
   (t nil)))

;; TODO -> add 'list' macro to compiler/interpreter (and cadr, etc.?)

(defunc2 insert (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (insert x ls))
  (cond
   ((endp ls) (cons x nil))
   ((<= x (car ls)) (cons x ls))
   (t (cons (car ls) (insert x (cdr ls))))))

(defunc2 isort (ls)
  :input-contract (loip ls)
  :output-contract (loip (isort ls))
  (cond
   ((endp ls) nil)
   (t (insert (car ls) (isort (cdr ls))))))

(defgroup sorting-fns orderedp perm insert isort boolean)

(suggest-lemma (isort ls1)
	       :hyps (loip ls2) (orderedp ls2) (perm ls1 ls2))

;; At first this doesn't go through

(defthm isort-ordered
  (IMPLIES (AND (LOIP LS)
		(LOIP (ISORT LS)))
	   (EQUAL (ORDEREDP (ISORT LS)) T)))

(suggest-lemma (orderedp (insert x ls))
	       :with sorting-fns)

(defthm insert-ordered
  (IMPLIES (AND (INTEGERP X)
		(LOIP (INSERT X LS))
		(LOIP LS))
	   (EQUAL (ORDEREDP (INSERT X LS))
		  (ORDEREDP LS))))

;; but now it does!
(defthm isort-ordered
  (IMPLIES (AND (LOIP LS)
		(LOIP (ISORT LS)))
	   (EQUAL (ORDEREDP (ISORT LS)) T)))


(suggest-lemma (perm ls (isort ls))
	       :with sorting-fns)

(suggest-lemma t
	       :required-expressions (cons x ls) (insert x ls)
	       :hyps (and (loip ls) (integerp x))
	       :with sorting-fns)


;;;;;;;;;;;;;;;;;
;; Now, quicksort

;; CCL has a weird bug that makes me define this
(defunc2 my-lte (a b)
  :input-contract (and (integerp a) (integerp b))
  :output-contract (booleanp (my-lte a b))
  (<= a b))

(defunc2 less (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (less x ls))
  (cond
   ((endp ls) nil)
   ((my-lte (car ls) x)
    (cons (car ls) (less x (cdr ls))))	  
   (t (less x (cdr ls)))))

(add-to-group sorting-fns my-lte less)

(defunc2 notless (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (notless x ls))
  (cond
   ((endp ls) nil)
   ((not (my-lte (car ls) x))
    (cons (car ls) (notless x (cdr ls))))	  
   (t (notless x (cdr ls)))))

(add-to-group sorting-fns my-lte notless)

(defunc2 qsort (ls)
  :input-contract (loip ls)
  :output-contract (loip (qsort ls))
  (cond
   ((endp ls) nil)
   (t (append (qsort (less (car ls) (cdr ls)))
	      (cons (car ls)
		    (qsort (notless (car ls) (cdr ls))))))))

;; first key qsort-isort lemma
(suggest-lemma (isort (less x ls))
	       :required-expressions (isort ls) x
	       :with less)

;; second key qsort-isort lemma
(suggest-lemma (isort (notless x ls))
	       :required-expressions (isort ls)
	       :with notless)

;; final key qsort-isort lemma
(suggest-lemma (append (isort (less (car x) (cdr x)))
		       (cons (car x)
			     (isort (notless (car x) (cdr x)))))
	       :required-expressions (car x) (cdr x)
	       :with insert isort
	       :hyps (consp x))

;; alternate versions

(suggest-lemma (insert x ls)
	       :required-expressions (less x ls) (notless x ls) 
	       :with append cons
	       :hyps (orderedp ls))
