; The three lines just below are boilerplate, that is, the same for every
; problem.

(in-package "ACL2")
(include-book "../system/ok-or-skipped-doublets")
(include-book "Submission")
(set-enforce-redundancy t)
(include-book "Defs")

; The events below represent the theorem to be proved, and are copied from
; template.lisp.

(defun-sk lemma-formalization ()
  (exists (a b c) (pythagoreantriple a b c)))

(defthm lemma
  (lemma-formalization))

; In this trivial example, we don't add any private checks.

(print-ok-or-skipped-doublets lemma)
