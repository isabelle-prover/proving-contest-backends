import .submission

lemma main_lemma :
  (∀ (p q: Prop), (p ↔ q) → p = q) ∧
  (Π {α : Sort}, nonempty α → α) ∧
  (∀ α {r : α → α → Prop} {a b : α}, r a b → quot.mk r a = quot.mk r b) :=
all_the_axioms
