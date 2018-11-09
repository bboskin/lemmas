(defun acl2s-last-result ()
  (let ((state *the-live-state*))
    (@ result)))

(defun acl2s-query (q)
  (let ((state *the-live-state*))
    (ld `((mv-let
           (erp val state)
           (trans-eval ',q 'acl2s-query state t)
           (assign result (list erp (cdr val))))))
    (acl2s-last-result)))

(defun acl2s-event (e)
  (let ((state *the-live-state*))
    (ld `((mv-let
           (erp val state)
           ,e
           (assign result (list erp val)))))
    (acl2s-last-result)))
