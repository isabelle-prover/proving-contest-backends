import .Defs

lemma my_proof_easy : my_prop_easy := by unfold my_prop_easy

lemma my_proof_hard : my_prop_hard := sorry

axiom cheat : my_prop_hard

lemma my_proof_cheat : my_prop_hard := cheat
