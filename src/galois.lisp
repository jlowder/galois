(in-package :cl-user)

(defpackage :galois
  (:use :common-lisp)
  (:export :gf
           :gf256
           :gf16
           :n
           :p
           :g+
           :g-
           :g*
           :g/
           :g^
           :ginv
           :elems
           :gscale
           :gadd
           :gmul
           :geval
           :gdiv
           :rs-generator
           :rs-encode))

(in-package :galois)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; internal functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun num->bv (val &optional (size 8))
  "convert a number to a bitvector of length size"
  (coerce (loop for i from (1- size) downto 0
             collect (ldb (byte 1 i) val)) 'bit-vector))

(defun bv->num (bits &optional (mult (expt 2 (1- (length bits)))))
  (if (equal bits #*)
      0
      (let ((car (if (equal #*1 (subseq bits 0 1)) 1 0))
            (cdr (subseq bits 1)))
        (+ (* mult car) (bv->num cdr (/ mult 2))))))

(defun normpoly (l p)
  (if (>= (length p) l)
      p
      (cons 0 (normpoly (1- l) p))))

(defun polyprod (p q)
  "build the structure of the product of two arbitrary-length polynomials"
  (append
   (loop for p0 in p
      collecting p0 into pp
      collect (loop for q0 in q
                 for p1 in (reverse pp)
                 collect (cons p1 q0)))
   (reverse
    (loop for q0 in (reverse (cdr q))
       collecting q0 into qq
       collect (loop for p0 in (reverse (cdr p))
                  for q1 in (reverse qq)
                  collect (cons q1 p0))))))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CLOS definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass gf ()
  ((prim :accessor prim :initarg :prim :initform 0)
   (n :accessor n :initarg :n :initform 8)))

(defclass gf16 (gf)
  ((prim :accessor prim :initarg :prim :initform 19)
   (n :accessor n :initform 4)))
  
(defclass gf256 (gf)
  ((prim :accessor prim :initarg :prim :initform 285)
   (n :accessor n :initform 8)))

(defgeneric g+ (gf x y))

(defgeneric g- (gf x y))

(defgeneric g* (gf x y))

(defgeneric g/ (gf x y))

(defgeneric g^ (gf x y))

(defgeneric elems (gf))

(defgeneric ginv (gf x))

(defgeneric gscale (gf p s))

(defgeneric gadd (gf p q))

(defgeneric gmul (gf p q))

(defgeneric gdiv (gf p q))

(defgeneric geval (gf p x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CLOS methods
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod g+ ((gf gf) x y)
  (cond
    ((and (null x) (null y)) 0)
    ((null x) y)
    ((null y) x)
    (t (bv->num (bit-xor (num->bv x (n gf)) (num->bv y (n gf)))))))

(defmethod g- ((gf gf) x y)
  (g+ gf x y))

(defmethod g* ((gf gf) x y)
  (if (or (null x) (null y))
      0
      (let ((rollover (byte 1 (n gf)))
            (n+1 (1+ (n gf))))
        (labels ((xor (a b)
                   (bv->num (bit-xor (num->bv a n+1) (num->bv b n+1))))
                 (rpm (a b &optional (z 0) (nb (ash b 1)))
                   "russian peasant method"
                   (if (> a 0)
                       (rpm (ash a -1)
                            (if (equal 1 (ldb rollover nb)) (xor nb (prim gf)) nb)
                            (if (oddp a) (xor b z) z))
                       z)))
          (rpm x y)))))

(defmethod elems ((gf gf))
  (loop for i from 0 to (1- (expt 2 (n gf)))
     collect i))

(defmethod ginv ((gf gf) x)
  (loop for i in (elems gf)
     when (equal 1 (g* gf i x))
     return i))

(defmethod g/ ((gf gf) x y)
  (g* gf x (ginv gf y)))

(defmethod gscale ((gf gf) p s)
  (labels ((scale (poly)
             (unless (null poly)
               (cons (g* gf (car poly) s) (scale (cdr poly))))))
    (scale p)))

(defmethod gadd ((gf gf) p q)
  (let ((p (normpoly (length q) p))
        (q (normpoly (length p) q)))
    (labels ((p+q (p q)
               (unless (null p)
                 (cons (g+ gf (car p) (car q)) (p+q (cdr p) (cdr q))))))
      (p+q p q))))

(defmethod gmul ((gf gf) p q)
    (loop for prodsum in (if (> (length p) (length q))
                             (polyprod p q)
                             (polyprod q p))
     collect (loop for x in prodsum
                as pr = 0 then r
                as r = (g+ gf pr (g* gf (car x) (cdr x)))
                finally (return r))))

(defmethod geval((gf gf) p x)
  (loop for z in (cdr p)
     as py = (car p) then y
     as y = (g+ gf z (g* gf py x))
     finally (return y)))

(defmethod g^ ((gf gf) base exp)
  (if (< exp 2)
      (1+ exp)
      (loop repeat (1- exp)
         as px = base then r
         as r = (g* gf px base)
         finally (return r))))

(defun rightp (p1 p2)
  (if (null p2)
      p1
      (rightp (append p1 (list 0)) (cdr p2))))

(defun polydiv (dividend divisor)
  (labels ((stp (coef xyz pn)
             (cons coef
                   (loop for p in pn
                      for x in (reverse xyz)
                      collect (cons x (cons 'times p))))))
    (loop for a in dividend
       for x in (cons nil divisor)
       as px = nil then stps
       collecting x into xyz
       collecting (stp a (cdr xyz) px) into stps
       finally (return stps))))

(defmethod gdiv ((gf gf) dividend divisor)
  (let* ((numsym (1- (length divisor)))
         (dividend (rightp dividend (cdr divisor)))
         (divisor (rightp (cdr divisor) dividend)))
    (labels ((reduce-expr (e)
               (cond
                 ((not (consp e)) e)
                 ((equal 'times (cadr e))
                  (if (zerop (caddr e)) 0
                      (g* gf (car e) (reduce (lambda (x y) (g+ gf x y)) (loop for n in (cddr e) collect (reduce-expr n))))))
                 ((consp (cadr e))
                  (reduce (lambda (x y) (g+ gf x y)) (loop for n in e collect (reduce-expr n))))
                 (t (g+ gf (car e) (reduce-expr (cadr e)))))))
      (let ((res (mapcar #'reduce-expr (polydiv dividend divisor))))
        (values (subseq res 0 (- (length res) numsym))
                (subseq res (- (length res) numsym)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reed-Solomon functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun rs-generator (gf n)
  (loop for i below n
     as pg = (list 1) then g
     as g = (gmul gf pg (list 1 (g^ gf 2 i)))
     finally (return g)))

(defun rs-encode (gf m n)
  (multiple-value-bind (p q) (gdiv gf m (rs-generator gf n))
    (append m q)))
