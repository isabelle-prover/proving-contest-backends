(in-package "ACL2")

(defun pythagoreantriple (a b c)
  (and (natp a) (natp b) (natp c)
       (< a b)
       (< b c)
       (equal (+ (* a a) (* b b))
              (* c c))))


