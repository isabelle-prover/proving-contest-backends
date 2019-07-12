; The four lines just below are boilerplate, that is, the same for every
; problem.

(in-package "ACL2")
(include-book "solution")
(set-enforce-redundancy t)
(include-book "definitions")

; The events below represent the theorem to be proved, and are copied from
; template.lisp.

(defun-sk lemma-formalization ()
  (exists (a b c) (pythagoreantriple a b c)))

(defthm lemma
  (lemma-formalization))
