Require Export Basics.

Theorem plus_n_O : forall n, n + O = n.
Proof.
  refine (fix Fn n :=
            match n with
            | O => eq_refl
            | S n' => _
            end).
  cbn. rewrite (Fn n'). exact eq_refl.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  refine (fix fn n :=
            match n with
            | O => eq_refl
            | S n' => _
            end).
  cbn. rewrite (fn n'). exact eq_refl.
Qed.

(* This is from DeepSpec *)
Theorem bogus_subtraction: ~ (forall k:nat, k > k - 3).
Proof.
  refine (fun H =>
            let g := H 0 in
            _).
  inversion g. 
Qed.

(* Worth looking Library 
https://coq.inria.fr/library/Coq.omega.PreOmega.html *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  refine (fix Fn n :=
            match n with
            | O => eq_refl
            | S n' => _
            end).
  cbn. apply Fn.
Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  refine (fix Fn n :=
            match n with
            | O => fun m => _
            | S n' => fun m => _
            end);
    cbn; try (rewrite (Fn n' m)); exact eq_refl.
Qed.

Require Import Psatz.
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  refine (fun n m => _). lia.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros; lia. Show Proof. (* lia is good enough to discharge these proofs *)
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  refine (fix Fn n :=
            match n with
            | O => eq_refl
            | S n' => _
            end).
  cbn. f_equal. rewrite <- plus_n_Sm.
  rewrite (Fn n'). exact eq_refl.
Qed.


Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  refine (fix Fn n :=
            match n with
            | O => eq_refl
            | S n' => _
            end).
  cbn.
  refine (match n' with
          | O => _
          | S n'' => _
          end).
  cbn. exact eq_refl.
  apply Fn.
Qed.

