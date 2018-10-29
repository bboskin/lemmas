(load "~/lemmas/interp-acl2.lisp")

;; Some tests about append

(defun2 snoc (x ls)
  (cond
   ((endp ls) (cons x nil))
   ((consp ls)
    (cons (car ls)
	  (snoc x (cdr ls))))))

(defun2 append2 (l1 l2)
  (cond
   ((endp l2) l1)
   ((consp l2)
    (append2 (snoc (car l2) l1) (cdr l2)))))

(suggest-lemma (append2 l1 l2)
	       (append)
	       (((l1 nil)
		 (l2 nil))
		((l1 (t))
		 (l2 nil))
		((l1 (t))
		 (l2 (t)))))


(defun2 rev-acc (ls acc)
  (cond
   ((endp ls) acc)
   (t (rev-acc (cdr ls) (cons (car ls) acc)))))


(suggest-lemma (rev-acc ls1 ls2)
	       ((reverse ls1))
	       (((ls1 nil)
		 (ls2 nil))
		((ls1 (t))
		 (ls2 nil))
		((ls1 (t))
		 (ls2 (t nil t)))))

(suggest-lemma (append x (append y z))
	       ((append x y))
	       (((x (t))
		 (y (t nil))
		 (z (nil t)))))


(suggest-lemma (reverse (append x y))
	     			((reverse x) (reverse y))
	       (((x (a b c))
		 (y (b c)))))



(suggest-lemma (append x y)
	       (append-acc)
	       (((x (1 1 2))
		 (y 5))))
