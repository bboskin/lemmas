(in-package "ACL2S")
(defttag t)

(include-book "itest-cgen")
(include-book "itest-ithm")

(acl2::define defgroup-inner ((name symbolp) (args true-listp))
  :returns (nil)
  (declare (ignore name args))
  (acl2::raise "Wrong version of defgroup-inner is being called"))

(acl2::define add-to-group-inner ((name symbolp) (args true-listp))
  :returns (nil)
  (declare (ignore name args))
  (acl2::raise "Wrong version of add-to-group-inner is being called"))

(acl2::define suggest-lemma-inner (form (args true-listp))
  :returns (nil)
  (declare (ignore form args))
  (acl2::raise "Wrong version of suggest-lemma-inner is being called"))

(acl2::define gen-rel-inner ((name symbolp) (vars true-listp)
		       body state)
  :returns (mv a b state)
  (declare (ignore name vars body)
	   (xargs :stobjs state))
  (mv nil (acl2::raise "Wrong version of gen-rel-inner is being called") state))


(acl2::define get-tests ((form true-listp))
  :returns (nil)
  (declare (ignore form))
  (acl2::raise "wrong"))

(acl2::define get-final (form from to)
  :returns (nil)
  (declare (ignore form form to))
  (acl2::raise "wrong"))

(acl2::include-raw "to-acl2-raw.lsp" :do-not-compile t)
(acl2::include-raw "helpers-raw.lsp" :do-not-compile t)

(acl2::include-raw "mk-raw.lsp" :do-not-compile t)
(acl2::include-raw "numbers-raw.lsp" :do-not-compile t)
(acl2::include-raw "primitives-raw.lsp" :do-not-compile t)

(acl2::include-raw "compile-raw.lsp" :do-not-compile t)
(acl2::include-raw "interp-raw.lsp" :do-not-compile t)

(acl2::include-raw "suggest-lemma-raw.lsp" :do-not-compile t)
(acl2::include-raw "defunc2-raw.lsp" :do-not-compile t)

(defmacro suggest-lemma (form &rest args)
  `(suggest-lemma-inner ',form ',args))

(defmacro defunc2 (name vars ic-ig ic oc-ig oc body)
  (declare (ignore ic-ig oc-ig))
  `(progn!
    (gen-rel-inner ',name ',vars ',body state)
    (defunc ,name ,vars
      :input-contract ,ic
      :output-contract ,oc
      ,body)))

(defmacro defgroup (name &rest args)
 `(defgroup-inner ',name ',args))

(defmacro add-to-group (name &rest args)
  `(add-to-group-inner ',name ',args))
