(Check_refl "1 + 1 = f 0")
(Check_refl "1 + 1 = Submission.g 0")
(Check_refl "10 = 5 + 5")

(Check "Submission.toto" "forall n, n + 0 = n")

(Allow_axioms
  (Coq.Logic.FunctionalExtensionality.functional_extensionality_dep
   Coq.Logic.Classical_Prop.classic
  ))

(Check "Submission.hmm" "0 = 0")
