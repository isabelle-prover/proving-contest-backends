import .defs

noncomputable lemma my_proof {α : Sort*} : nonempty α → α := classical.choice
