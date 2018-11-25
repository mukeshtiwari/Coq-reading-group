Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Psatz. 
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus e1 e2 => aeval e1 + aeval e2
    | AMinus e1 e2 => aeval e1 - aeval e2
    | AMult e1 e2 => aeval e1 * aeval e2
    end.


  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => leb (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n =>
           ANum n
    | APlus (ANum 0) e2 =>
            optimize_0plus e2
    | APlus e1 e2 =>
            APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
             AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
            AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
  cbn. auto. Qed.


  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    induction a;
      try (cbn; rewrite IHa1; rewrite IHa2; auto).
    + auto.
    + cbn. destruct a1;
             try (rewrite <- IHa1; rewrite <- IHa2; auto).
      ++ destruct n; try auto.
  Qed.

  
  

  Module aevalR_first_try.

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum n : aevalR (ANum n) n
    | E_APlus e1 e2 n1 n2 :
        aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat) : 
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

    Notation "e '\\' n"
      := (aevalR e n)
           (at level 50, left associativity)
         : type_scope.
    
  End aevalR_first_try.

  Reserved Notation "e '\\' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n : (ANum n) \\ n
  | E_APlus e1 e2 n1 n2 :
      e1 \\ n1 -> e2 \\ n2 ->  (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) : 
      e1 \\ n1 -> e2 \\ n2 -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      e1 \\ n1 -> e2 \\ n2 -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

  Theorem aeval_iff_aevalR : forall a n,
      (a \\ n) <-> aeval a = n.
  Proof.
    split. 
    + revert n.
      induction a; cbn; intros; inversion H; subst; clear H; try auto.
    + revert n. induction a; cbn; intros; subst; constructor;
                  try (eapply IHa1); try (eapply IHa2); auto.
  Qed.

  Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq a1 a2 n1 n2 : aevalR a1 n1 -> aevalR a2 n2 -> bevalR (BEq a1 a2) (n1 =? n2)
  | E_BLe a1 a2 n1 n2 : aevalR a1 n1 -> aevalR a2 n2 -> bevalR (BLe a1 a2) (n1 <=? n2)
  | E_BNot b1 v1 : bevalR b1 v1 -> bevalR (BNot b1) (negb v1)
  | E_BAnd b1 b2 v1 v2 : bevalR b1 v1 -> bevalR b2 v2 -> bevalR (BAnd b1 b2) (andb v1 v2).


  

  Lemma beval_iff_bevalR : forall b bv,
      bevalR b bv <-> beval b = bv.
  Proof.
    split.
    + intros H. induction H; cbn; try auto.
      pose proof (aeval_iff_aevalR a1 n1).
      pose proof (aeval_iff_aevalR a2 n2).
      apply H1 in H. apply H2 in H0; subst; auto.

      pose proof (aeval_iff_aevalR a1 n1).
      pose proof (aeval_iff_aevalR a2 n2).
      apply H1 in H. apply H2 in H0; subst; auto.

      subst. auto.
      subst; auto.


    + generalize dependent bv.
      induction b; cbn; intros; subst.
      eapply E_BTrue.
      eapply E_BFalse.
      eapply E_BEq; eapply  aeval_iff_aevalR; auto.
      eapply E_BLe; eapply  aeval_iff_aevalR; auto.
      eapply E_BNot; eapply IHb; auto.
      eapply E_BAnd; [eapply IHb1 | eapply IHb2]; auto.
  Qed.

  Module aevalR_division.

    Inductive aexp : Type :=
    | ANum : nat -> aexp
    | APlus : aexp -> aexp -> aexp
    | AMinus : aexp -> aexp -> aexp
    | AMult : aexp -> aexp -> aexp
    | ADiv : aexp -> aexp -> aexp.

    
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum n : (ANum n) \\ n
    | E_APlus e1 e2 n1 n2 :
        e1 \\ n1 -> e2 \\ n2 ->  (APlus e1 e2) \\ (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat) : 
        e1 \\ n1 -> e2 \\ n2 -> (AMinus e1 e2) \\ (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat) :
        e1 \\ n1 -> e2 \\ n2 -> (AMult e1 e2) \\ (n1 * n2)
    | E_ADiv e1 e2 n1 n2 n3 :
        e1 \\ n1 -> e2 \\ n2 -> (n2 > 0) ->
        (mult n1 n2 = n3) -> (ADiv e1 e2) \\ n3
    where "e '\\' n" := (aevalR e n) : type_scope.

  End aevalR_division.
  Module aevalR_extended.

    Inductive aexp : Type :=
    | AAny : aexp
    | ANum : nat -> aexp
    | APlus : aexp -> aexp -> aexp
    | AMinus : aexp -> aexp -> aexp
    | AMult : aexp -> aexp -> aexp.

    Reserved Notation "e '\\' n" (at level 50, left associativity).

    Inductive aevalR : aexp -> nat -> Prop :=
    | E_AAny n : AAny \\ n
    | E_ANum n : (ANum n) \\ n
    | E_APlus e1 e2 n1 n2 :
        e1 \\ n1 -> e2 \\ n2 ->  (APlus e1 e2) \\ (n1 + n2)
    | E_AMinus (e1 e2: aexp) (n1 n2: nat) : 
        e1 \\ n1 -> e2 \\ n2 -> (AMinus e1 e2) \\ (n1 - n2)
    | E_AMult (e1 e2: aexp) (n1 n2: nat) :
        e1 \\ n1 -> e2 \\ n2 -> (AMult e1 e2) \\ (n1 * n2)
    where "e '\\' n" := (aevalR e n) : type_scope.

  End aevalR_extended.

End AExp.

Module AState.
  Definition state := total_map nat.

  Print total_map.
  
  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Definition W : string := "W".
  Definition X : string := "X".
  Definition Y : string := "Y".
  Definition Z : string := "Z".

  
  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


  Coercion AId : string >-> aexp.
  Coercion ANum : nat >-> aexp.
  Definition bool_to_bexp (b: bool) : bexp :=
    if b then BTrue else BFalse.
  Coercion bool_to_bexp : bool >-> bexp.
  Bind Scope aexp_scope with aexp.
  Infix "+" := APlus : aexp_scope.
  Infix "-" := AMinus : aexp_scope.
  Infix "*" := AMult : aexp_scope.
  Bind Scope bexp_scope with bexp.
  Infix "<=" := BLe : bexp_scope.
  Infix "=" := BEq : bexp_scope.
  Infix "&&" := BAnd : bexp_scope.
  Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

  Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n => n
    | AId x => st x
    | APlus e1 e2 => aeval st e1 + aeval st e2
    | AMinus e1 e2 => aeval st e1 - aeval st e2
    | AMult e1 e2 => aeval st e1 * aeval st e2
    end.

    Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
    end.

    Notation "{ a --> x }" :=
      (t_update { --> 0 } a x) (at level 0).
    Notation "{ a --> x ; b --> y }" :=
      (t_update ({ a --> x }) b y) (at level 0).
    Notation "{ a --> x ; b --> y ; c --> z }" :=
      (t_update ({ a --> x ; b --> y }) c z) (at level 0).
    Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" :=
      (t_update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
    Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
      (t_update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
    Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
      (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).
    Example aexp1 :
      aeval { X --> 5 } (3 + (X * 2))
      = 13.
    cbn. auto.
  Qed.

  Example bexp1 :
    beval { X --> 5 } (true && !(X <= 4))
    = true.
  cbn. auto. Qed.


  Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

  Bind Scope com_scope with com.
  Notation "'SKIP'" :=
    CSkip : com_scope.
  Notation "x '::=' a" :=
    (CAss x a) (at level 60) : com_scope.
  Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity) : com_scope.
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity) : com_scope.
  Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

  Open Scope com_scope.

  Definition fact_in_coq : com :=
    Z ::= X;;
    Y ::= 1;;
    WHILE ! (Z = 0) DO
         Y ::= Y * Z;;
         Z ::= Z - 1
    END.

  Definition plus2 : com :=
    X ::= X + 2.
  Definition XtimesYinZ : com :=
    Z ::= X * Y.
  Definition subtract_slowly_body : com :=
    Z ::= Z - 1 ;;
    X ::= X - 1.


  Definition subtract_slowly : com :=
  WHILE ! (X = 0) DO
    subtract_slowly_body
    END.

  Definition subtract_3_from_5_slowly : com :=
    X ::= 3 ;;
    Z ::= 5 ;;
    subtract_slowly.

  Definition loop : com :=
  WHILE true DO
    SKIP
  END.

  Check t_update. 
 Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        st & { x --> (aeval st a1) }
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st (* bogus *)
  end.

 Reserved Notation "c1 '/' st '\\' st'"
          (at level 40, st at level 39).
 Inductive ceval : com -> state -> state -> Prop :=
 | E_Skip st : SKIP / st \\ st
 | E_Ass st a1 n x :
     aeval st a1 = n -> (x ::= a1) / st \\ st & {x --> n}
 | E_Seq c1 c2 st st' st'' :
     c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
 | E_IfTrue st st' b c1 c2 :
     beval st b = true ->
     c1 / st \\ st' ->
     (IFB b THEN c1 ELSE c2 FI) / st \\ st'
 | E_IfFalse st st' b c1 c2 :
     beval st b = false ->
     c2 / st \\ st' -> 
     (IFB b THEN c1 ELSE c2 FI) / st \\ st'
 | E_WhileFalse b st c :
     beval st b = false ->
     (WHILE b DO c END) / st \\ st
 | E_WhileTrue b st st' st'' c :
     beval st b = true ->
     c / st \\ st' ->
     (WHILE b DO c END) / st' \\ st'' ->
     (WHILE b DO c END) / st \\ st''
                    
 where "c1 '/' st '\\' st'" := (ceval c1 st st').


 Example ceval_example1:
   (X ::= 2;;
     IFB X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI)
   / { --> 0 } \\ { X --> 2 ; Z --> 4 }.
 Proof.
   apply E_Seq with { X --> 2 }.
   - apply E_Ass; auto.
   - apply E_IfFalse; auto.
     apply E_Ass; auto.
 Qed.


 Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { --> 0 } \\
  { X --> 0 ; Y --> 1 ; Z --> 2 }.
 Proof.
   eapply E_Seq. eapply E_Ass. cbn. instantiate (1 := 0). auto.
   eapply E_Seq; eapply E_Ass. cbn. auto.
   cbn. auto.
 Qed.


 Definition pup_to_n : com :=
   Y ::= 0;;
   WHILE ! (X = 0) DO
      Y ::= Y + X;;
      X ::= X - 1
   END.                   


 Theorem pup_to_2_ceval :
   pup_to_n / { X --> 2 }
            \\ { X --> 2 ; Y --> 0 ; Y --> 2 ; X --> 1 ; Y --> 3 ; X --> 0 }.
 Proof.
   unfold pup_to_n.
   eapply E_Seq. eapply E_Ass. cbn. instantiate (1 := 0). auto.
   eapply E_WhileTrue; auto.
   eapply E_Seq; eapply E_Ass; cbn. instantiate (1 := 2). auto.
   instantiate (1 := 1). auto.
   eapply E_WhileTrue; auto.
   eapply E_Seq; eapply E_Ass. cbn. instantiate (1 := 3); auto.
   cbn. instantiate (1 := 0); auto.
   eapply E_WhileFalse; cbn; auto.
 Qed.



 Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1 ->
     c / st \\ st2 ->
     st1 = st2.
   (* proof by induction on c *)
 Proof.
   intros  c st st1 st2 E1 E2.
   generalize dependent st2.
   induction E1; intros st2 E2; inversion E2; subst; clear E2.
   + auto.
   + auto.
   + pose proof (IHE1_1 _ H1). subst. 
     pose proof (IHE1_2 _ H4). auto.
   + pose proof (IHE1 _ H6). auto.
   + rewrite H in H5. inversion H5.
   + rewrite H in H5. inversion H5.
   + pose proof (IHE1 _ H6). auto.
   + auto.
   + rewrite H in H2.  inversion H2.
   + rewrite H in H4.  inversion H4.
   + assert (st' = st'0). pose proof (IHE1_1 _ H3). auto.
     subst st'. pose proof (IHE1_2 _ H6). auto.
 Qed.
 
      
End AState.
