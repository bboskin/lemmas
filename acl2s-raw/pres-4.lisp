(defttag t)
(include-book "lemma-synth" :uncertified-okp t)

(defdata2 loi (listof integer))

(defunc2 sum-ls (l)
  :input-contract (loip l)
  :output-contract (integerp (sum-ls l))
  (cond
   ((endp l) 0)
   (t (+ (car l) (sum-ls (cdr l))))))

(defunc2 bad-sum (l)
  :input-contract (loip l)
  :output-contract (integerp (bad-sum l))
  (cond
   ((endp l) 11)
   (t (+ (car l) (bad-sum (cdr l))))))


;; A few options...
(suggest-lemma (bad-sum l)
	       :required-expressions sum-ls
	       :with all-forms)

(thm (IMPLIES (LOIP L)
	      (EQUAL (BAD-SUM L)
		     (SUM-LS (CONS 11 L)))))

(suggest-lemma (bad-sum l)
	       :required-expressions + sum-ls
	       :with all-forms)

(thm (IMPLIES (LOIP L)
	      (EQUAL (BAD-SUM L)
		     (+ (SUM-LS L) 11))))



(defunc2 strange (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (symbolp (strange ls acc))
  (cond
   ((atom ls) 'terminated)
   ((consp ls)
    (strange (cdr ls) (append (list (first ls)) (reverse acc))))))

(suggest-lemma (strange ls acc)
	       :with all-forms)

(thm
 (IMPLIES (AND (TRUE-LISTP LS) (TRUE-LISTP ACC))
         (EQUAL (STRANGE LS ACC) 'TERMINATED)))

(defunc2 what- (l s1 s2)
  :input-contract (and (true-listp l) (stringp s1) (stringp s2))
  :output-contract (stringp (what- l s1 s2))
  (cond
   ((endp l) (string-append s1 s2))
   ((endp (cdr l)) (what- (cdr l) s2 (string-append s1 "s")))
   (t (what- (cdr l) s2 s1))))

(defunc2 what (l)
  :input-contract (true-listp l)
  :output-contract (stringp (what l))
  (what- (list* 'goodluck! (append l l)) "L2" "AC"))

(suggest-lemma (what l)
	       :with all-forms)


;; This one isn't directly a theorem
(test? (IMPLIES (TRUE-LISTP L)
		(EQUAL (WHAT L) "ACL2s")))
