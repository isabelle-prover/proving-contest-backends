def int_of_nat := ℕ → ℤ
notation `int_of_nat` := int_of_nat

def correctness_prop (f : int_of_nat) := ∀ (n : ℕ), f n < 0
notation `correctness_prop` := correctness_prop
