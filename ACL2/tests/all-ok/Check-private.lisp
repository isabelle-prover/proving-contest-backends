; The three lines just below are boilerplate, that is, the same for every
; problem.

(in-package "ACL2")
(include-book "../system/ok-or-skipped-doublets")
(include-book "Submission")
(set-enforce-redundancy t)
(include-book "Defs")

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

(thm (equal (rev nil)
            nil))

(thm (equal (rev '(a))
            '(a)))

(thm (equal (rev '(a b c d))
            '(d c b a)))

(thm (equal (dotprod nil nil)
            0))

(thm (equal (dotprod '(3 4) '(5 6))
            39))

(print-ok-or-skipped-doublets triple-rev-is-rev
                              dotprod-test
                              dotprod-rev-rev)
