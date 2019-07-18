(in-package "ACL2")

(include-book "definitions")

; Consider writing a program, find-pyth, to compute a suitable Pythagorean
; triple, then define a constant containing that triple, and finally give the
; lemma below a suitable :use hint based on that constant.

; (defconst *pyth-answer*
;   (find-pyth 1000))

(defun-sk lemma-formalization ()
  (exists (a b c) (pythagoreantriple a b c)))

(defthm lemma
  (lemma-formalization))
