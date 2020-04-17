import .defs

lemma all_the_axioms :
  (∀ (p q: Prop), (p ↔ q) → p = q) ∧
  (Π {α : Sort}, nonempty α → α) ∧
  (∀ α {r : α → α → Prop} {a b : α}, r a b → quot.mk r a = quot.mk r b) :=
⟨@propext, @classical.choice, @quot.sound⟩
