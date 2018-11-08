(in-package "ACL2")

(defttag t)
(include-book "top" :uncertified-okp t)

(defgroup list-ops append reverse)

(add-to-group list-ops cons)

(defunc2 eta-cons (a b)
  :input-contract (true-listp b)
  :output-contract (true-listp (eta-cons a b))
  (cons a b))


(suggest-lemma a
	       :required-expressions a
	       :hyps (true-listp a))

(suggest-lemma (eta-cons a b)
	       :required-expressions (cons a b)
	       :hyps (true-listp b) (natp a))

(defunc2 reverse-acc (ls acc)
  :input-contract (and (true-listp ls) (true-listp acc))
  :output-contract (true-listp (reverse-acc ls acc))
  (cond
   ((endp ls) acc)
   (t (reverse-acc (cdr ls) (cons (car ls) acc)))))

(suggest-lemma (reverse-acc ls acc)
	       :required-expressions reverse ls
	       :with append
	       :hyps (true-listp ls) (true-listp acc))
