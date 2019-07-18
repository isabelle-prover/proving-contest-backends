; The four lines just below are boilerplate, that is, the same for every
; problem.

(in-package "ACL2")
(include-book "solution")
(set-enforce-redundancy t)
(include-book "definitions")

; The events below represent the theorems to be proved, and are copied from
; template.lisp.

(defthm triple-rev-is-rev
  (equal (rev (rev (rev x)))
         (rev x)))

(defthm dotprod-test
  (equal (dotprod '(1 2 3 4) '(1 10 100 1000))
         4321))

(defthm dotprod-rev-rev
  (implies (equal (len x) (len y))
           (equal (dotprod (rev x) (rev y))
                  (dotprod x y))))
