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

(acl2::define defunc2- ((name symbolp) (vars true-listp)
		       body state)
  :returns (mv a b state)
  (declare (ignore name vars body)
	   (xargs :stobjs state))
  (mv nil (acl2::raise "Wrong version of defunc2- is being called") state))

(acl2::define defdata2- ((exprs true-listp))
  :returns (nil)
  (declare (ignore exprs))
  (acl2::raise "Wrong version of defdata2- is being called"))

(acl2::include-raw "to-acl2-raw.lsp" :do-not-compile t)
(acl2::include-raw "helpers-raw.lsp" :do-not-compile t)

(acl2::include-raw "mk-raw.lsp" :do-not-compile t)
(acl2::include-raw "numbers-raw.lsp" :do-not-compile t)
(acl2::include-raw "primitives-raw.lsp" :do-not-compile t)

(acl2::include-raw "compile-raw.lsp" :do-not-compile t)
(acl2::include-raw "interp-raw.lsp" :do-not-compile t)
(acl2::include-raw "compile-defdata-raw.lsp" :do-not-compile t)

(acl2::include-raw "suggest-lemma-raw.lsp" :do-not-compile t)
(acl2::include-raw "defunc2-raw.lsp" :do-not-compile t)
(acl2::include-raw "compile-defdata-raw.lsp" :do-not-compile t)

(defmacro suggest-lemma (form &rest args)
  `(suggest-lemma-inner ',form ',args))

(defmacro defunc2 (name vars ic-ig ic oc-ig oc &rest body)
  (declare (ignore ic-ig oc-ig))
  `(progn!
    (defunc2- ',name ',vars (car (reverse ',body)) state)
    (defunc ,name ,vars
      :input-contract ,ic
      :output-contract ,oc
      . ,body)))

(defmacro defdata2 (&rest exprs)
  `(progn!
    (defdata2- ',exprs)
    (defdata . ,exprs)))

(defmacro defgroup (name &rest args)
 `(defgroup-inner ',name ',args))

(defmacro add-to-group (name &rest args)
  `(add-to-group-inner ',name ',args))



;;;; Setting bounds on rational numbers

;(defdata-attach rational :enumerator by-hand-rational-enum)

