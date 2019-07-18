; The three lines just below are boilerplate, that is, the same for every
; problem.

(in-package "ACL2")
(include-book "../system/ok-or-skipped-doublets")
(include-book "check-public")

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
