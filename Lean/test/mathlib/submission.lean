import .defs
import data.seq.seq
import tactic.norm_num

lemma my_proof : 1 + 1 = 2 := by norm_num

lemma from_lib {α β : Type*} (f : α → β) : ∀ (s : seq α), s.tail.map f = (s.map f).tail := seq.map_tail f
