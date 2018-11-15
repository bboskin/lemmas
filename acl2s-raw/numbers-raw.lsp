(in-package "ACL2S")

;(load "mk-raw.lsp")
#|A Library for little-endian binary numbers for miniKanren.
  My implementation differs from the typical version, because
  they have a tag at the front. This will make reading numbers 
  back to decimal easier, because numbers will be easily detectable from
lists of numerals or fresh variables.


Edit:

In addition, I add support for integers and rational numbers.

In addition to a tag at the front, each miniKanren number has 
a sign (0 means positive, 1 means negative).
Rational numbers have, instead of a sign tag, the tag 'RATIONAL, and follow
this form:

`(INTERNAL-NUMBER RATIONAL ,numerator ,denominator)
|#

(defun div2 (n)
  (cond
   ((evenp n) (/ n 2))
   (t (/ (- n 1) 2))))

(defun build-num-in (n)
  (cond
   ((zerop n) '())
   ((oddp n) (cons 1 (build-num-in (div2 (- n 1)))))
   (t (cons 0 (build-num-in (div2 n))))))


(defun read-back-inner (n)
  (cond
   ((endp n) 0)
   (t (let ((v (if (or (equal (car n) 1)
		       (equal (car n) 0))
		   (car n)
		 (random 2))))
	(+ v (* 2 (read-back-inner (cdr n))))))))


(defrel zeroo (n)
  (== '() n))

(defrel poso (n)
  (fresh (b r)
	 (== `(,b . ,r) n)
	 (conde
	  ((== b 0))
	  ((== b 1)))))

(defrel >1o (n)
  (fresh (a ad dd)
	 (== `(,a ,ad . ,dd) n)))

(defrel full-addero (b x y r c)
  (conde
   ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
   ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
   ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
   ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
   ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
   ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
   ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
   ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))


(defrel addero (d n m r)
  (conde
   ((== 0 d) (== '() m) (== n r))
   ((== 0 d) (== '() n) (== m r)
    (poso m))
   ((== 1 d) (== '() m)
    (addero 0 n '(1) r))
   ((== 1 d) (== '() n) (poso m)
    (addero 0 '(1) m r))
   ((== '(1) n) (== '(1) m)
    (fresh (a c)
           (== `(,a ,c) r)
           (full-addero d 1 1 a c)))
   ((== '(1) n) (gen-addero d n m r))
   ((== '(1) m) (>1o n) (>1o r)
    (addero d '(1) n r))
   ((>1o n) (gen-addero d n m r))))

(defrel gen-addero (d n m r)
  (fresh (a b c e x y z)
         (== `(,a . ,x) n)
         (== `(,b . ,y) m) (poso y)
         (== `(,c . ,z) r) (poso z)
         (full-addero d a b c e)
         (addero e x y z)))

(defrel pluso (n m k)
  (addero 0 n m k))

(defrel minuso (n m k)
  (pluso m k n))

(defrel *o (n m p)
  (conde
   ((== '() n) (== '() p))
   ((poso n) (== '() m) (== '() p))
   ((== '(1) n) (poso m) (== m p))
   ((>1o n) (== '(1) m) (== n p))
   ((fresh (x z)
           (== `(0 . ,x) n) (poso x)
           (== `(0 . ,z) p) (poso z)
           (>1o m)
           (*o x m z)))
   ((fresh (x y)
           (== `(1 . ,x) n) (poso x)
           (== `(0 . ,y) m) (poso y)
           (*o m n p)))
   ((fresh (x y)
           (== `(1 . ,x) n) (poso x)
           (== `(1 . ,y) m) (poso y)
           (odd-*o x n m p)))))

(defrel odd-*o (x n m p)
  (fresh (q)
         (bound-*o q p n m)
         (*o x m q)
         (pluso `(0 . ,q) m p)))

(defrel bound-*o (q p n m)
  (conde
   ((== '() q) (poso p))
   ((fresh (a0 a1 a2 a3 x y z)
           (== `(,a0 . ,x) q)
           (== `(,a1 . ,y) p)
           (conde
            ((== '() n)
             (== `(,a2 . ,z) m)
             (bound-*o x y z '()))
            ((== `(,a3 . ,z) n) 
             (bound-*o x y z m)))))))

(defrel =lo (n m)
  (conde
   ((== '() n) (== '() m))
   ((== '(1) n) (== '(1) m))
   ((fresh (a x b y)
           (== `(,a . ,x) n) (poso x)
           (== `(,b . ,y) m) (poso y)
           (=lo x y)))))

(defrel <lo (n m)
  (conde
   ((== '() n) (poso m))
   ((== '(1) n) (>1o m))
   ((fresh (a x b y)
           (== `(,a . ,x) n) (poso x)
           (== `(,b . ,y) m) (poso y)
           (<lo x y)))))

(defrel <=lo (n m)
  (conde
   ((=lo n m))
   ((<lo n m))))

(defrel >lo (n m)
  (<lo m n)) 

(defrel <o (n m)
  (conde
   ((<lo n m))
   ((=lo n m)
    (fresh (x)
           (poso x)
           (pluso n x m)))))

(defrel <=o (n m)
  (conde
   ((== n m))
   ((<o n m))))

(defrel /o (n m q r)
  (conde
   ((== r n) (== '() q) (<o n m))
   ((== '(1) q) (=lo n m) (pluso r m n)
    (<o r m))
   ((<lo m n)
    (<o r m)
    (poso q)
    (fresh (nh nl qh ql qlm qlmr rr rh)
           (splito n r nl nh)
           (splito q r ql qh)
           (conde
            ((== '() nh)
             (== '() qh)
             (minuso nl r qlm)
             (*o ql m qlm))
            ((poso nh)
             (*o ql m qlm)
             (pluso qlm r qlmr)
             (minuso qlmr nl rr)
             (splito rr r '() rh)
             (/o nh m qh rh)))))))

(defrel splito (n r l h)
  (conde
   ((== '() n) (== '() h) (== '() l))
   ((fresh (b n^)
           (== `(0 ,b . ,n^) n)
           (== '() r)
           (== `(,b . ,n^) h)
           (== '() l)))
   ((fresh (n^)
           (==  `(1 . ,n^) n)
           (== '() r)
           (== n^ h)
           (== '(1) l)))
   ((fresh (b n^ a r^)
           (== `(0 ,b . ,n^) n)
           (== `(,a . ,r^) r)
           (== '() l)
           (splito `(,b . ,n^) r^ '() h)))
   ((fresh (n^ a r^)
           (== `(1 . ,n^) n)
           (== `(,a . ,r^) r)
           (== '(1) l)
           (splito n^ r^ '() h)))
   ((fresh (b n^ a r^ l^)
           (== `(,b . ,n^) n)
           (== `(,a . ,r^) r)
           (== `(,b . ,l^) l)
           (poso l^)
           (splito n^ r^ l^ h)))))

(defrel logo (n b q r)
  (conde
   ((== '(1) n) (poso b) (== '() q) (== '() r))
   ((== '() q) (<o n b) (pluso r '(1) n))
   ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
   ((== '(1) b) (poso q) (pluso r '(1) n))
   ((== '() b) (poso q) (== r n))
   ((== '(0 1) b)
    (fresh (a ad dd)
           (poso dd)
           (== `(,a ,ad . ,dd) n)
           (exp2 n '() q)
           (fresh (s)
                  (splito n dd r s))))
   ((fresh (a ad add ddd)
           (conde
            ((== '(1 1) b))
            ((== `(,a ,ad ,add . ,ddd) b))))
    (<lo b n)
    (fresh (bw1 bw nw nw1 ql1 ql s)
           (exp2 b '() bw1)
           (pluso bw1 '(1) bw)
           (<lo q n)
           (fresh (q1 bwq1)
                  (pluso q '(1) q1)
                  (*o bw q1 bwq1)
                  (<o nw1 bwq1))
           (exp2 n '() nw1)
           (pluso nw1 '(1) nw)
           (/o nw bw ql1 s)
           (pluso ql '(1) ql1)
           (<=lo ql q)
           (fresh (bql qh s qdh qd)
                  (repeated-mul b ql bql)
                  (/o nw bw1 qh s)
                  (pluso ql qdh qh)
                  (pluso ql qd q)
                  (<=o qd qdh)
                  (fresh (bqd bq1 bq)
                         (repeated-mul b qd bqd)
                         (*o bql bqd bq)
                         (*o b bq bq1)
                         (pluso bq r n)
                         (<o n bq1)))))))

(defrel exp2 (n b q)
  (conde
   ((== '(1) n) (== '() q))
   ((>1o n) (== '(1) q)
    (fresh (s)
           (splito n b s '(1))))
   ((fresh (q1 b2)
           (== `(0 . ,q1) q)
           (poso q1)
           (<lo b n)
           (appendo b `(1 . ,b) b2)
           (exp2 n b2 q1)))
   ((fresh (q1 nh b2 s)
           (== `(1 . ,q1) q)
           (poso q1)
           (poso nh)
           (splito n b s nh)
           (appendo b `(1 . ,b) b2)
           (exp2 nh b2 q1)))))

(defrel repeated-mul (n q nq)
  (conde
   ((poso n) (== '() q) (== '(1) nq))
   ((== '(1) q) (== n nq))
   ((>1o q)
    (fresh (q1 nq1)
           (pluso q1 '(1) q)
           (repeated-mul n q1 nq1)
           (*o nq1 n nq)))))

(defrel expo (b q n)
  (logo n b q '()))


;;; User forms

;; new versions
(defun build-num (n)
  (cond
   ((natp n) (list* 'INTERNAL-NUMBER '(0) (build-num-in n)))
   ((integerp n) (list* 'INTERNAL-NUMBER '(1) (build-num-in (abs n))))
   ((rationalp n) (list 'INTERNAL-NUMBER '(RATIONAL)
	     (build-num (acl2s::numerator n))
	     (build-num (acl2s::denominator n))))))

(defun read-back-num (n)
  (if (and (consp n) (equal (car n) 'INTERNAL-NUMBER))
      (cond
       ((equal (cadr n) '(0))
	(read-back-inner (cddr n)))
       ((equal (cadr n) '(1))
	(* -1 (read-back-inner (cddr n))))
       ((equal (cadr n) '(RATIONAL))
	(let ((numerator (read-back-num (caddr n)))
	      (denominator (read-back-num (cadddr n))))
	  (if (zerop denominator) 0 (/ numerator denominator)))))
    n))
