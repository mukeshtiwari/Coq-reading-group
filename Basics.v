Require Import Psatz.

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

(* 
What is difference between 
Proof. 
Proof using. 
and other constructs 
 *)

Example test_next_weekday :
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. 
  refine (eq_refl).
Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb1: (orb true false) = true.
Proof. refine eq_refl. Qed.

Example test_orb2: (orb false false) = false.
Proof. refine eq_refl. Qed.

Example test_orb3: (orb false true) = true.
Proof. refine eq_refl. Qed. 

Example test_orb4: (orb true true) = true.
Proof. refine eq_refl. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof.  refine eq_refl. Qed.

Definition nandb (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => false
  | _, _ => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. refine eq_refl. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. refine eq_refl. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. refine eq_refl. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. refine eq_refl. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. refine eq_refl. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. refine eq_refl. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. refine eq_refl. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. refine eq_refl. Qed.

Check true.
Check (negb true).
Check negb.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Inductive color : Type :=
| black : color
| white : color
| primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | _ => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Module Natplayground.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Natplayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. exact eq_refl. Qed.

Example test_oddb2: oddb 4 = false.
Proof. exact eq_refl. Qed.

Module Natplayground2.

  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof. exact eq_refl. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End Natplayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. exact eq_refl. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. exact eq_refl.  Qed.

Inductive fact : nat -> nat -> Type :=
| base : fact 0 1
| step n m : fact n m -> fact (S n) (mult m (S n)).

Example fact_compute : fact 5 120.
Proof. apply step with (n := 4) (m := 24).
       apply step with (n := 3) (m := 6).
       apply step with (n := 2) (m := 2).
       apply step with (n := 1) (m := 1).
       apply step with (n := 0) (m := 1).
       apply base.
Qed.

Lemma fact_correctness : forall n m,
    fact n m -> m = factorial n.
Proof.  
  induction n.
  + cbn; intros m H; inversion H; try auto.
  + cbn; intros m H; inversion H; subst; try auto.
    pose proof (IHn _ H1). rewrite H0.
    assert (forall a, a * S n = a + a * n).
    intros. lia.  rewrite H2 with (a := factorial n).
    f_equal. lia. 
Qed.

Lemma fact_relation : forall n m,
    m = factorial n -> fact n m.
Proof.
  induction n.
  + cbn; intros; subst; try constructor.
  + cbn; intros.
    assert (Hm : m = mult (factorial n) (S n)). lia.
    rewrite Hm; eapply step; apply IHn; auto.
Defined. 

Lemma compute_fact_rel :
  forall n, fact n (factorial n).
Proof.
  intros.
  pose proof (fact_relation n (factorial n) eq_refl); assumption.
Defined.

(* Inspect the internal details of this proof. Looks interesting *)
Eval compute in (compute_fact_rel 5).


Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.
Check ((0 + 1) + 1).


