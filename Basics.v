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


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
        | O => true
        | S m' => false
        end
  | S n' => match m with
           | O => false
           | S m' => beq_nat n' m'
           end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
           | O => false
           | S m' => leb n' m'
           end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. exact eq_refl. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. exact eq_refl. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. exact eq_refl. Qed.


Definition blt_nat (n m : nat) : bool :=
  negb (leb m n).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. exact eq_refl. Qed. 

Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. exact eq_refl. Qed.

Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. exact eq_refl. Qed.

Theorem plus_O_n : forall n, O + n = n.
Proof.
  refine (fun n => eq_refl).
Qed.

Theorem plus_1_n : forall n, 1 + n = S n.
Proof.
  refine (fun n => eq_refl).
Qed.

Theorem mult_0_1 : forall n, O * n = O.
Proof.
  refine (fun n => eq_refl).
Qed.

Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  refine (fun n m H => eq_ind_r (fun n0 => n0 + n0 = m + m) eq_refl H).
Qed.

Check (@eq_ind_r nat O (fun n => n = O) eq_refl O eq_refl).
(* Learn more about eq_ind_r, 
eq_ind_r :
forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, y = x -> P y
Arguments A, x, y are implicit. 
If you want to supply all the arguments then use @eq_ind_r *)

Check (fun n m => @eq_ind_r _ _ (fun N => N = n + S m)  (plus_n_Sm n m) _  (plus_Sn_m n m)).

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
  refine (fun n m o Hnm Hmo => eq_ind_r (fun n0 => n0 + m = m + o)
                                     (eq_ind_r (fun m0 => m0 + m0 = m0 + o) eq_refl Hmo) Hnm).
Qed.

Theorem mult_O_plus : forall n m : nat,
    (O + n) * m = n * m.
Proof.
  refine (fun n m => eq_refl).
Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
  refine (fun n m H => eq_ind_r (fun m0 => m0 * (1 + n) = m0 * m0) eq_refl H).
Qed.

Theorem plus_1_neq_O :
  forall (n : nat), beq_nat (n + 1) O = false.
Proof.
  refine (fix Fn n :=
            match n with
            | O => eq_refl
            | S n' => eq_refl
            end).
Qed.

Theorem negb_involutive : forall b,
    negb (negb b) = b.
Proof.
  refine (fun b => match b with
                | true => eq_refl
                | false => eq_refl
                end).
Qed.

Theorem and_commutative :
  forall a b, andb a b = andb b a.
Proof.
  refine (fun a b =>
            match a, b with
            | true, true => eq_refl
            | false, false => eq_refl
            | false, true => eq_refl
            | true, false => eq_refl
            end).
Qed.

(* plus as relation *)

Inductive plus_rel : nat -> nat -> nat -> Type :=
| pbase m : plus_rel O m m
| pstep n m r : plus_rel n m r -> plus_rel (S n) m (S r).

(* Define a division function n / k *)
Definition div (n k : nat) := 1.

Inductive log (b : nat) :  nat -> nat -> Type :=
| lbase : log b 1 0
| lstep n k : b <= n -> log b n k -> log b (div n b) (S k).

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  refine (fun f Hf =>
            fix Fn b :=
            match b with
            | true => _
            | false => _
            end);
    [repeat rewrite (Hf true) | repeat rewrite (Hf false)]; exact eq_refl.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  refine (fun f Hf =>
            fix Fn b :=
            match b with
            | true => _
            | false => _
            end). 
  rewrite (Hf true); cbn; rewrite (Hf false); cbn; exact eq_refl.
  rewrite (Hf false); cbn; rewrite (Hf true); cbn; exact eq_refl. 
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof.
  refine (fun b c =>
            match b, c with
            | true, true => fun H => eq_refl
            | true, false => fun H => _
            | false, true => fun H => _
            | false, false => fun H => eq_refl
            end); inversion H.
Qed.

(* influenced by coq binary *)
Inductive bin : Type :=
| xZ : bin (* Zero *)
| xD : bin -> bin (* Twice *)
| xT : bin -> bin. (*Twice plus one *)


(* 
 0 => xZ
 1 => xT xZ (2 * 0 + 1)
 2 => xD (xT xZ)  (2 * 1)
 3 => xT (xT xZ) (2 * 1 + 1)
 4 => xD (xD (xT xZ)) *)

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | xZ => O
  | xD p => 2 * bin_to_nat p
  | xT p => 1 + 2 * bin_to_nat p
  end.

Eval compute in (bin_to_nat (xD (xD (xT xZ)))).

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n) => even n
  end.

Fixpoint div2 (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n) => S (div2 n)
  end.

Eval compute in div2 12.

Require Import FunInd.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2t2le : forall n, div2 n <= n.
Proof.
  intros n.
  functional induction (div2 n); try lia.
Qed.

  
Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

