(defttag t)
(include-book "top" :uncertified-okp t)

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
  (oneof (cons flat-input flat-input) rational boolean character string))

(defunc2 flatten (x)
  :input-contract t ;(flat-inputp x)
  :output-contract (true-listp (flatten x))
  (cond ((atom x) (cons x nil))
        (t (append (flatten (car x)) (flatten (cdr x))))))

(defunc2 mc-flatten-acc (x a)
  :input-contract (true-listp a)
  :output-contract (true-listp (mc-flatten-acc x a))
  (cond ((atom x) (cons x a))
        (t (mc-flatten-acc (car x)
                           (mc-flatten-acc (cdr x) a)))))

(suggest-lemma (mc-flatten-acc a l)
	       :with flatten append
	       :hyps (flat-inputp a))

;; Doesn't go through, we'd need to provide an induction scheme

(defthm flatten-acc-flatten
  (IMPLIES (AND (TRUE-LISTP L) (FLAT-INPUTP A))
	   (EQUAL (MC-FLATTEN-ACC A L)
		  (APPEND (FLATTEN A) L))))

;;

(defunc2 gopher-meas (x)
  :input-contract t
  :output-contract (natp (gopher-meas x))
  (cond
   ((atom x) 0)
   ((atom (car x)) 0)
   (t (+ 1 (gopher-meas (car x))))))

(defthm lg-dec
  (implies (and (consp e)
		(consp (car e)))
	   (< (gopher-meas (cons (caar e)
				 (cons (cdar e) (cdr e))))
	      (gopher-meas e))))

(set-termination-method :measure)
(defunc2 gopher (x)
  :input-contract t
  :output-contract t
  (declare (xargs :measure (gopher-meas x)))
  (if (or (atom x)
          (atom (car x)))
      x
    (gopher (cons (caar x) (cons (cdar x) (cdr x))))))

(suggest-lemma (flatten (gopher x))
	       :with flatten gopher
	       :hyps (flat-inputp x))

(defthm flatten-gopher
  (IMPLIES (AND (FLAT-INPUTP (GOPHER X))
		(FLAT-INPUTP X))
         (EQUAL (FLATTEN (GOPHER X))
                (FLATTEN X))))

;;;;

(defunc2 count-all (x)
  :input-contract t
  :output-contract (natp (count-all x))
  (cond ((atom x) 1)
        ((consp x)
	 (+ 1 (count-all (car x))
	    (count-all (cdr x))))))

(defgroup flatten-like flatten gopher count-all)

;; Theorems needed for the termination argument
(suggest-lemma (count-all (gopher x))
	       :with flatten-like)

(defthm gopher-count-all-eq
  (EQUAL (COUNT-ALL (GOPHER X))
	 (COUNT-ALL X)))

(suggest-lemma t
	       :required-expressions (gopher x)
	       :with flatten-like car atom
	       :hyps (not (atom x)))

(defthm gopher-first-atom
  (IMPLIES (NOT (ATOM X))
	   (ATOM (CAR (GOPHER X)))))

(suggest-lemma (count-all x)
	       :with flatten-like + - number
	       :hyps (atom x))

(defthm count-all-atom
  (IMPLIES (ATOM X)
	   (EQUAL (COUNT-ALL X) 1)))


;; This one surprised me
(suggest-lemma (count-all (cdr (gopher x)))
	       :required-expressions (gopher x)
	       :with flatten-like - number
	       :hyps (not (atom x))
	       :complete-hyps nil)

(defthm gopher-rest-count-all
  (IMPLIES (NOT (ATOM X))
	   (EQUAL (COUNT-ALL (CDR (GOPHER X)))
		  (- (COUNT-ALL (GOPHER X)) 2))))

(defthm gopher-rest-count-all-less
  (<= (count-all (cdr (gopher x))) (count-all (gopher x))))


(defthm gopher-rest-count-all-less
  (<= (count-all (cdr (gopher x)))
      (count-all (gopher x))))

(suggest-lemma t
	       :required-expressions (gopher x)
	       :with flatten-like listp
	       :hyps (listp x))

(defthm goph-list
  (IMPLIES (LISTP X) (LISTP (GOPHER X))))

(defunc samefringe-measure (x y)
  :input-contract t
  :output-contract (natp (samefringe-measure x y))
  (cond ((or (atom x) (atom y)) 0)
        ((not (equal (car (gopher x)) (car (gopher y)))) 0)
        (t (+ 1 (count-all (cdr (gopher x))) (count-all (cdr (gopher y)))))))

(set-termination-method :measure)

(defunc2 samefringe (x y)
  :input-contract t
  :output-contract (booleanp (samefringe x y))
  (declare (xargs :measure (samefringe-measure x y)))
  (if (or (atom x) (atom y))
      (equal x y)
    (and (equal (car (gopher x))
                (car (gopher y)))
         (samefringe (cdr (gopher x))
                     (cdr (gopher y))))))

(defunc2 first* (e)
  :input-contract t
  :output-contract (atom (first* e))
  (cond
   ((atom e) e)
   ((atom (car e)) (car e))
   (t (first* (car e)))))

(defgroup group
  gopher flatten first* samefringe)

(suggest-lemma (first* e)
	       :required-expressions (gopher e)	       
	       :with group)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Question from 2800 Homework 10
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunc2 zip-list (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (zip-list x y))
  (if (or (endp x) (endp y))
    nil
    (cons (list (first x) (first y))
          (zip-list (rest x) (rest y)))))

(defunc2 zip-list-t (x y acc)
  :input-contract (and (true-listp x) (true-listp y) (true-listp acc))
  :output-contract (true-listp (zip-list-t x y acc))
  (if (or (endp x) (endp y))
    (rev* acc)
    (zip-list-t (rest x) (rest y) (cons (list (first x) (first y)) acc))))

(defunc2 zip-list* (x y)
  :input-contract (and (true-listp x) (true-listp y))
  :output-contract (true-listp (zip-list* x y))
  (zip-list-t x y nil))

(suggest-lemma (zip-list-t x y acc)
	       :required-expressions (zip-list x y)
	       :with reverse append zip-list)

(defthm zip-list-t-zip-list
 (IMPLIES (AND (TRUE-LISTP X)
	       (TRUE-LISTP Y)
	       (TRUE-LISTP ACC))
	  (EQUAL (ZIP-LIST-T X Y ACC)
		 (APPEND (REVERSE ACC) (ZIP-LIST X Y)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Quicksort and Insertion sort
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata2 loi (listof integer))

(defunc2 orderedp (ls)
  :input-contract (loip ls)
  :output-contract (booleanp (orderedp ls))
  (cond
   ((endp ls) t)
   ((endp (rest ls)) t)
   ((<= (first ls) (second ls))
    (orderedp (rest ls)))
   (t nil)))

(defunc2 del (x ls)
  :input-contract (loip ls)
  :output-contract (loip (del x ls))
  (cond
   ((endp ls) nil)
   ((equal x (first ls)) (rest ls))
   (t (cons (first ls) (del x (rest ls))))))

(defunc2 perm (l1 l2)
  :input-contract (and (loip l1) (loip l2))
  :output-contract (booleanp (perm l1 l2))
  (cond
   ((endp l1) (endp l2))
   ((in (first l1) l2)
    (perm (rest l1) (del (first l1) l2)))
   (t nil)))

(defunc2 insert (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (insert x ls))
  (cond
   ((endp ls) (list x))
   ((<= x (first ls)) (cons x ls))
   (t (cons (first ls) (insert x (rest ls))))))

(defunc2 isort (ls)
  :input-contract (loip ls)
  :output-contract (loip (isort ls))
  (cond
   ((endp ls) nil)
   (t (insert (first ls) (isort (rest ls))))))

(defgroup sorting-fns orderedp perm insert isort boolean)

(suggest-lemma (isort ls1)
	       :with sorting-fns
	       :hyps (loip ls2) (orderedp ls2) (perm ls1 ls2))

;; This doesn't go through

(thm (IMPLIES (AND (LOIP LS1)
		   (LOIP LS2)
		   (ORDEREDP LS2)
		   (PERM LS1 LS2))
	      (EQUAL (ISORT LS1) LS2)))


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

(defthm perm-cons
  (IMPLIES (AND (LOIP LS) (INTEGERP X))
         (PERM (CONS X LS) (INSERT X LS))))

(defthm isort-perm
  (IMPLIES (AND (LOIP LS) (LOIP (ISORT LS)))
	   (PERM LS (ISORT LS))))

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
