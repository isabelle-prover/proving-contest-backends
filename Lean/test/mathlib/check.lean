import .submission

lemma main : 1 + 1 = 2 := my_proof

lemma main2 {α β : Type*} (f : α → β) : ∀ (s : seq α), s.tail.map f = (s.map f).tail := from_lib f
