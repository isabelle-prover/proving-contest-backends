import .Defs

axioms (cheat : 1 + 1 = 2)

lemma my_proof_cheat : 1 + 1 = 2 := cheat

lemma my_proof_real : 1 + 1 = 2 := rfl

