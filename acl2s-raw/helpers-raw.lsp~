(in-package "ACL2")

; Creating new variable names
(defun next-index () 0)
(defun next-var ()
  (let ((i (next-index)))
    (progn
      (defun next-index () (+ 1 i))
      (intern (concatenate 'string
			   "fresh-var"
			   (get-name i))))))

(defun get-name (n)
  (cond
   ((equal n 0) "0")
   ((equal n 1) "1")
   ((equal n 2) "2")
   ((equal n 3) "3")
   ((equal n 4) "4")
   ((equal n 5) "5")
   ((equal n 6) "6")
   ((equal n 7) "7")
   ((equal n 8) "8")
   ((equal n 9) "9")
   (t (concatenate 'string
		   (get-name (floor n 10))
		   (get-name (mod n 10))))))

;; The name of a miniKanrenized function
(defun get-rel-name (name)
  (intern
   (concatenate 'string (string name) "-REL")))
