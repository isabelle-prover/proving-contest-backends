Require Import Defs.

Definition g (n : nat) := S (S (S n)).

Lemma toto : forall k, k + 0 = k.
Proof.
  induction k; auto.
Qed.

Require Import Classical.
Require Import FunctionalExtensionality.

Lemma hmm : 0 = 0.
  destruct (classic (0 = 0)). auto.
  pose proof (functional_extensionality (fun n => n+1) (fun n => S n)).
  (*apply cheat.*) auto.
Qed.
