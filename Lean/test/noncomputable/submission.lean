import .defs
import tactic.norm_num

noncomputable def my_int_of_nat : int_of_nat :=
begin
  assume n,
  have : nonempty ℤ := by simp,
  have i : ℤ := classical.choice this,
  exact (if i < 0 then i else -1)
end

lemma my_int_of_nat_correctness : correctness_prop my_int_of_nat :=
begin
  assume n,
  have : nonempty ℤ := by simp,
  let i : ℤ := classical.choice this,
  cases (classical.em (i < 0)) with h1 h2,
  { simp [my_int_of_nat, h1] },
  { simp [my_int_of_nat, h2] }
end
