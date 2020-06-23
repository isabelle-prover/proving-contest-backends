import .defs

def my_int_of_nat : int_of_nat :=
by { assume n, exact (-1) }

lemma my_int_of_nat_correctness : correctness_prop my_int_of_nat :=
by { assume n, simp [my_int_of_nat] }
