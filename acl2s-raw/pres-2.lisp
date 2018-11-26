(defttag t)
(include-book "lemma-synth" :uncertified-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Quicksort and Insertion sort
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defdata2 loi (listof integer))

(defunc2 in (x ls)
  :input-contract (and (loip ls) (integerp x))
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (first ls)) t)
   (t (in x (rest ls)))))

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

(defgroup sorting-fns orderedp perm insert isort)

;; Some interesting properties that we can find,
;; which don't immediately go through

(suggest-lemma t
	       :required-expressions isort
	       :with sorting-fns
	       :hyps (loip x))

(suggest-lemma t
	       :required-expressions isort
	       :with sorting-fns
	       :exclude orderedp
	       :hyps (loip x))

(suggest-lemma (isort ls1)
	       :with sorting-fns
	       :hyps (loip ls2) (orderedp ls2) (perm ls1 ls2))

;; Let's prove the first one!
(suggest-lemma t
	       :required-expressions insert
	       :with sorting-fns
	       :hyps (loip x) (integerp a) (orderedp x))

(defthm insert-ordered
  (IMPLIES (AND (LOIP X)
		(INTEGERP A)
		(ORDEREDP X))
	   (ORDEREDP (INSERT A X))))

(defthm isort-ordered
  (IMPLIES (LOIP X)
	   (ORDEREDP (ISORT X))))

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

(defunc2 notless (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (notless x ls))
  (cond
   ((endp ls) nil)
   ((not (my-lte (car ls) x))
    (cons (car ls) (notless x (cdr ls))))	  
   (t (notless x (cdr ls)))))

(add-to-group sorting-fns my-lte less notless)

(defunc2 qsort (ls)
  :input-contract (loip ls)
  :output-contract (loip (qsort ls))
  (cond
   ((endp ls) nil)
   (t (append (qsort (less (car ls) (cdr ls)))
	      (cons (car ls)
		    (qsort (notless (car ls) (cdr ls))))))))

;;;;;;;;;;;;;;;
;; first key qsort-isort lemma

;; helper 1
(suggest-lemma (less a (insert b ls))
	       :required-expressions less
	       :with sorting-fns
	       :complete-hyps nil
	       :hyps (integerp a) (integerp b) (> b a) (loip ls) (orderedp ls))

(defthm insert-less-drop
  (IMPLIES (AND (INTEGERP A)
		(INTEGERP B)
		(> B A)
		(LOIP LS)
		(ORDEREDP LS))
	   (EQUAL (LESS A (INSERT B LS))
		  (LESS A LS))))

;; helper 2
(suggest-lemma (less a (insert b ls))
	       :required-expressions (insert b (less a ls))
	       :with sorting-fns
	       :complete-hyps nil
	       :hyps (integerp a) (integerp b) (<= b a) (loip ls) (orderedp ls))

(defthm insert-less-keep
     (IMPLIES (AND (INTEGERP A)
              (INTEGERP B)
              (<= B A)
              (LOIP LS)
              (ORDEREDP LS))
         (EQUAL (LESS A (INSERT B LS))
                (INSERT B (LESS A LS)))))

;; Lemma 1
(suggest-lemma (isort (less x ls))
	       :required-expressions (isort ls) x
	       :with less
	       :complete-hyps nil
	       :hyps (loip ls) (integerp x))

(defthm less-isort-comp
  (IMPLIES (AND (LOIP LS) (INTEGERP X))
         (EQUAL (ISORT (LESS X LS))
                (LESS X (ISORT LS)))))

;;;;;;;;;;;;;;;;;;
;; second key qsort-isort lemma
(suggest-lemma (isort (notless x ls))
	       :required-expressions (isort ls)
	       :with notless)

;; helper 1
(suggest-lemma (notless a (insert b ls))
	       :required-expressions notless
	       :with sorting-fns
	       :complete-hyps nil
	       :hyps (integerp a) (integerp b) (<= b a) (loip ls) (orderedp ls))

(defthm insert-notless-drop
  (IMPLIES (AND (INTEGERP A)
              (INTEGERP B)
              (<= B A)
              (LOIP LS)
              (ORDEREDP LS))
         (EQUAL (NOTLESS A (INSERT B LS))
                (NOTLESS A LS))))

;; helper 2
(suggest-lemma (notless a (insert b ls))
	       :required-expressions (insert b (notless a ls))
	       :with sorting-fns
	       :complete-hyps nil
	       :hyps (integerp a) (integerp b) (> b a) (loip ls) (orderedp ls))

(defthm insert-notless-keep
  (IMPLIES (AND (INTEGERP A)
		(INTEGERP B)
		(> B A)
		(LOIP LS)
		(ORDEREDP LS))
	   (EQUAL (NOTLESS A (INSERT B LS))
		  (INSERT B (NOTLESS A LS)))))


;; Lemma 2
(suggest-lemma (isort (notless x ls))
	       :required-expressions (isort ls) x
	       :with notless
	       :complete-hyps nil
	       :hyps (loip ls) (integerp x))

(defthm notless-isort-comp
  (IMPLIES (AND (LOIP LS) (INTEGERP X))
         (EQUAL (ISORT (NOTLESS X LS))
                (NOTLESS X (ISORT LS)))))




(defunc2 get-before (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (get-before x ls))
  (cond
   ((endp ls) nil)
   ((> (car ls) x) nil)
   (t (cons (car ls) (get-before x (cdr ls))))))

(defunc2 get-after (x ls)
  :input-contract (and (integerp x) (loip ls))
  :output-contract (loip (get-after x ls))
  (cond
   ((endp ls) nil)
   ((> (car ls) x) ls)
   (t (get-after x (cdr ls)))))

(add-to-group sorting-fns get-before get-after)

(suggest-lemma (less a x)
	       :required-expressions (get-before a x)
	       :with sorting-fns
	       :exclude less
	       :hyps (orderedp x))

(defthm before-less
  (IMPLIES (AND (INTEGERP A) (LOIP X) (ORDEREDP X))
         (EQUAL (LESS A X) (GET-BEFORE A X))))


(suggest-lemma (notless a x)
	       :required-expressions (get-after a x)
	       :with sorting-fns
	       :exclude notless
	       :hyps (orderedp x))

(defthm after-notless
  (IMPLIES (AND (INTEGERP A) (LOIP X) (ORDEREDP X))
         (EQUAL (NOTLESS A X) (GET-AFTER A X))))

;; final key qsort-isort lemma
(suggest-lemma (insert x ls)
	       :required-expressions (less x ls) (notless x ls) 
	       :with append cons
	       :hyps (orderedp ls))

(defthm qsort-step
  (IMPLIES (AND (INTEGERP X)
              (LOIP LS)
              (ORDEREDP LS))
         (EQUAL (INSERT X LS)
                (APPEND (LESS X LS)
                        (CONS X (NOTLESS X LS))))))

(suggest-lemma (qsort x)
	       :with sorting-fns)

(defthm qsort-isort
  (IMPLIES (LOIP X)
         (EQUAL (QSORT X) (ISORT X))))
