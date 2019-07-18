(in-package "ACL2")

(include-book "Defs")

(defun find-pyth1 (a a^2 b n)

; Search starting with b > a such that a^2 + b^2 = (n - a - b)^2.

  (declare (xargs :mode :program))
  (let ((c (- n (+ a b))))
    (if (<= c b)
        nil ; failure
      (if (equal (+ a^2 (* b b))
                 (* c c))
          b ; success
        (find-pyth1 a a^2 (1+ b) n)))))

; Note that there is no point in calling find-pyth1 if
; n - (a + b) <= b, i.e., 2b >= (n - a).  But I'm not using that here.

(defun find-pyth2 (a n) ; e.g., n is 1000
  (declare (xargs :mode :program))
  (if (>= (* 2 a) n) ; could do better
      nil
    (let ((b (find-pyth1 a (* a a) (1+ a) n)))
      (if b
          (list a b (- n (+ a b)))
        (find-pyth2 (1+ a) n)))))

(defun find-pyth (n) ; e.g., n is 1000
  (declare (xargs :mode :program))
  (find-pyth2 1 n))

(defconst *pyth-answer*
  (find-pyth 1000))

(defun-sk lemma-formalization ()
  (exists (a b c) (pythagoreantriple a b c)))

(defthm lemma
  (lemma-formalization)
  :hints (("Goal" :use ((:instance lemma-formalization-suff
                                   (a (nth 0 *pyth-answer*))
                                   (b (nth 1 *pyth-answer*))
                                   (c (nth 2 *pyth-answer*)))))))
