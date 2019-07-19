(in-package "ACL2")

; The following is not necessary in this example, since the book has no
; events.
(include-book "Defs")

; Define rev to reverse its list argument:
; (defun rev (x) ...)

(defthm triple-rev-is-rev
  (equal (rev (rev (rev x)))
         (rev x)))

; Define dotprod so that it takes the dot product of two lists of equal length.
; For example:

(defthm dotprod-test
  (equal (dotprod '(1 2 3 4) '(1 10 100 1000))
         4321))

; Now prove this:

(defthm dotprod-rev-rev
  (implies (equal (len x) (len y))
           (equal (dotprod (rev x) (rev y))
                  (dotprod x y))))
