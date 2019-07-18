(in-package "ACL2")

; The following is not necessary in this example, since the book has no
; events.
(include-book "Defs")

(defun rev (x)
  (if (consp x)
      (append (rev (cdr x))
              (list (car x)))
    nil))

(defthm rev-append
  (equal (rev (append x y))
         (append (rev y) (rev x))))

(defthm triple-rev-is-rev
  (equal (rev (rev (rev x)))
         (rev x)))

(defun dotprod (x y)
  (if (consp x)
      (+ (* (car x) (car y)) (dotprod (cdr x) (cdr y)))
    0))

(defthm dotprod-test
  (equal (dotprod '(1 2 3 4) '(1 10 100 1000))
         4321))

(skip-proofs
(defthm dotprod-rev-rev
  (implies (equal (len x) (len y))
           (equal (dotprod (rev x) (rev y))
                  (dotprod x y))))
)
