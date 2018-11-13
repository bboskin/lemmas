(defttag t)

(include-book "top" :uncertified-okp t)

;;; more tests, focusing on the newly-added strings and chars


(defunc2 str-app-eta (s1 s2)
  :input-contract (and (stringp s1) (stringp s2))
  :output-contract (stringp (str-app-eta s1 s2))
  (string-append s1 s2))

(suggest-lemma (str-app-eta s1 s2)
	       :with string-append)

(defdata los (listof string))
(defdata lon (listof nat))


(defunc2 map-len (ls)
  :input-contract (losp ls)
  :output-contract (lonp (map-len ls))
  (cond
   ((endp ls) nil)
   (t (cons (length (car ls))
	    (map-len (cdr ls))))))

(suggest-lemma (append (map-len l1) (map-len l2))
	       :required-expressions (append l1 l2)
	       :with map-len)

;; testing recognizers

(suggest-lemma (consp e) :with consp)

(suggest-lemma (characterp e) :with characterp)
(suggest-lemma (stringp e) :with stringp)

(suggest-lemma (symbolp e) :with symbolp)
(suggest-lemma (booleanp e) :with booleanp)

;; the semantics of varp isn't quite what I expected,
;; this is what it's defined as under the hood
(suggest-lemma (varp e) :with varp
	       :hyps (or (varp e) (booleanp e) (not (symbolp e))))

(suggest-lemma (rationalp e) :with rationalp)
(suggest-lemma (integerp e) :with integerp)
(suggest-lemma (natp e) :with natp)
(suggest-lemma (negp e) :with negp)
(suggest-lemma (posp e) :with posp)
(suggest-lemma (zerop e) :with zerop)
(suggest-lemma (endp e) :with endp)


(defunc2 convert-to-number (e)
  :input-contract t
  :output-contract (integerp (convert-to-number e))
  (cond
   ((booleanp e) 1)
   ((symbolp e) -1)
   ((integerp e) e)
   ((rationalp e) (+ (numerator e) (denominator e)))
   ((stringp e) (length e))
   ((characterp e) 0)
   ((consp e) (+ (convert-to-number (car e))
		 (convert-to-number (cdr e))))
   (t 0)))


(defgroup conv-forms
  number
  length
  numerator denominator +
  car cdr)

(defunc2 d-eta (n)
  :input-contract (rationalp n)
  :output-contract (integerp (d-eta n))
  (denominator n))

(suggest-lemma (d-eta n)
	       :with conv-forms)

(suggest-lemma (numerator e)
	       :with conv-forms)

(suggest-lemma (convert-to-number e)
	       :required-expressions (numerator e)
	       :with conv-forms
	       :hyps (rationalp e) (not (integerp e)))

(suggest-lemma (convert-to-number e)
	       :with conv-forms
	       :hyps (stringp e))

(suggest-lemma (convert-to-number e)
	       :with conv-forms
	       :hyps (not (booleanp e)) (symbolp e))

(suggest-lemma (convert-to-number e)
	       :with conv-forms
	       :hyps (characterp e))
