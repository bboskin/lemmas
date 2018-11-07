(defun generate-tests (hyps)
  (let ((vs (group hyps)))))

(defunc in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal (car ls) x) t)
   (t (in x (cdr ls)))))

(defunc no-dups (e)
  :input-contract (true-listp e)
  :output-contract (booleanp (no-dups e))
  (cond
   ((endp e) t)
   ((in (car e) (cdr e)) nil)
   (t (no-dups (cdr e)))))


(test? (implies (and (true-listp e) (not (no-dups e))) nil))
