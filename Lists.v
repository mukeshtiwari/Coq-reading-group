Require Export Induction.
Module Natlist.

  Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

  Check (pair 3 5).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair x _ => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair _ y => y
    end.


  Notation "( x , y )" := (pair x y).

  Compute (fst (3,5)).

  Definition fst' (p : natprod) : nat :=
    match p with
    | (x, y) => x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x, y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

  Theorem surjective_pairing' : forall (n m : nat),
      (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    refine (fun n m => eq_refl).
  Qed.

  Theorem surjective_pairing : forall (p : natprod),
      p = (fst p, snd p).
  Proof.
    refine (fun p => match p with
                  | (x, y) => eq_refl
                  end).
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    refine (fun p => match p with
                  | (x, y) => eq_refl
                  end).
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
      fst (swap_pair p) = snd p.
  Proof.
    refine (fun p => match p with
                  | (x, y) => eq_refl
                  end).
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" := (cons x l)
                         (at level 60, right associativity).

  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Definition mylist1 := 1 :: (2 :: (3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := [1;2;3].

  Notation "x + y" := (plus x y)
                        (at level 50, left associativity).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => []
    | S count' => n :: repeat n count'
    end.


  Fixpoint length (l : natlist) : nat :=
    match l with
    | [] => O
    | _ :: tl => S (length tl)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | h :: tl => h :: app tl l2
    end.

  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).
  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | [] => default
    | h :: _ => h
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | [] => []
    | h :: t => t
    end.

  Example test_hd1: hd 0 [1;2;3] = 1.
  Proof. reflexivity. Qed.
  Example test_hd2: hd 0 [] = 0.
  Proof. reflexivity. Qed.
  Example test_tl: tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.


  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | [] => []
    | h :: t => if beq_nat h 0 then nonzeros t else h :: nonzeros t
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof.
    exact eq_refl.
  Qed.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | [] => []
    | h :: t => if evenb h then oddmembers t else h :: oddmembers t
    end.

  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. 
    exact eq_refl.
  Qed.

  Definition countoddmembers (l : natlist) : nat :=
    length (oddmembers l). 

  Example test_countoddmembers1:
    countoddmembers [1;0;3;1;4;5] = 4.
  exact eq_refl.
  Qed.

  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  exact eq_refl.
  Qed.

  Example test_countoddmembers3:
    countoddmembers nil = 0.
  exact eq_refl.
  Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | h1 :: t1 => match l2 with
               | [] => h1 :: t1
               | h2 :: t2 => h1 :: h2 :: alternate t1 t2
                 end
    end.

  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  exact eq_refl. Qed.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  cbn. exact eq_refl. Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  exact eq_refl. Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  exact eq_refl. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | [] => 0
    | h :: t => if beq_nat v h then S (count v t) else count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  cbn. exact eq_refl.  Qed.
  
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  exact eq_refl. Qed.

  Definition sum := app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  exact eq_refl. Qed.

  Definition add (v : nat) (s : bag) : bag := cons v s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  exact eq_refl. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  exact eq_refl. Qed. 

  Definition member (v:nat) (s:bag) : bool :=
    negb (beq_nat (count v s) 0).

  Example test_member1: member 1 [1;4;1] = true.
  exact eq_refl. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  exact eq_refl. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | [] => []
    | h :: t => if beq_nat h v then t else h :: remove_one v t
    end.

  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  exact eq_refl. Qed. 

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  exact eq_refl. Qed.
  
  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  exact eq_refl. Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  exact eq_refl. Qed.

  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
    | [] => []
    | h :: t => if beq_nat v h then remove_all v t else h :: remove_all v t
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  exact eq_refl. Qed.
  
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  exact eq_refl. Qed.
  
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  exact eq_refl. Qed.
  
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  exact eq_refl. Qed.

  Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | [] => true
    | h :: t => if member h s2 then subset t (remove_one h s2) else false
    end.
  
    

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  exact eq_refl. Qed.

  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  exact eq_refl. Qed.

  Theorem nil_app : forall l:natlist,
      [] ++ l = l.
    refine (fun l => eq_refl).
  Qed.

  Theorem tl_length_pred : forall l : natlist,
      pred (length l) = length (tl l).
  Proof.
    refine (fun l => match l with
                  | [] => eq_refl
                  | h :: t => eq_refl
                  end).
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    refine (fix Fn l1 :=
              match l1 as l1' return (forall l2 l3,  (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3) with
              | [] => fun l2 l3 => eq_refl
              | h :: t => _ (* some more lemma *)
              end).
    cbn; intros l2 l3; f_equal; apply Fn.
  Qed.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = length l1 + length l2.
  Proof.
    refine (fix Fn l1 :=
              match l1 as l1' return
                    l1 = l1' ->  forall l2, length (l1' ++ l2) = length l1' + length l2 with
              | [] => fun H l2 => eq_refl
              | h :: t => fun H l2 => _
              end eq_refl).
    cbn; f_equal; apply Fn.
  Qed.
   
  Theorem rev_length : forall l : natlist,
      length (rev l) = length l.
  Proof.
    refine (fix Fn l :=
              match l as l' return l = l' ->  length (rev l') = length l' with
              | [] => fun H => eq_refl
              | h :: t => _
              end eq_refl).
    cbn; intro H. (* Now we need a way to discharge 
                     length (rev t ++ [h]) = S (length t) => S (length (rev t)) = S (length t) *)
    rewrite app_length, plus_comm; cbn; f_equal; apply Fn.
  Qed.

  Inductive subsetrel : natlist -> natlist -> Type :=
  | emptylist l : subsetrel [] l
  | firstcons x l1 l2 : subsetrel l1 l2 -> subsetrel (x :: l1) (x :: l2)
  | secondcons x l1 l2 : subsetrel l1 l2 -> subsetrel l1 (x :: l2)
  | thirdcons x y l : subsetrel (x :: y :: l) (y :: x :: l).

  Example subset_rel1 : forall l, subsetrel [] l.
  refine (fun l => match l with
                | [] => emptylist []
                | h :: t => emptylist (h :: t)
                end).
  Qed.

  Theorem subset_connect : forall l1 l2, subset l1 l2 = true -> subsetrel l1 l2.
  Proof.
    induction l1.
    + cbn; intros l2 H.
      apply emptylist.
    + cbn; intros l2 H.
      remember (member n l2) as Hm.
      destruct Hm as [H1 | H1].
      (* At this point  true = member n l2 asserts that In n l2 -> l2 = l3 ++ [n] ++ l4
         But my subset relation is not good enough to capture it :( *)
  Admitted.


  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    refine (fix Fn l :=
              match l with
              | [] => eq_refl
              | h :: t => _
              end).
    cbn. rewrite Fn. exact eq_refl.  Show Proof.
  Qed.

  Theorem rev_app_distr: forall l1 l2 : natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    refine (fix Fn l1 :=
              match l1 as l1' return l1 = l1' -> forall l2, rev (l1' ++ l2) = rev l2 ++ rev l1' with
              | [] => fun H l2 => _
              | h :: t => fun H l2 => _
              end eq_refl).
    cbn. rewrite app_nil_r. exact eq_refl.
    cbn. rewrite Fn, app_assoc. exact eq_refl. 
  Qed.

  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    refine (fix Fn l :=
              match l with
              | [] => eq_refl
              | h :: t => _
              end).
    cbn. rewrite rev_app_distr; cbn; f_equal; rewrite Fn; exact eq_refl.
  Qed.

  Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    repeat rewrite app_assoc; exact eq_refl.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
      nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    refine (fix Fn l1 :=
              match l1 with
              | [] => _
              | h :: t => _
              end).
    + cbn; intro l2; exact eq_refl.
    + cbn; intro l2. destruct (beq_nat h 0); try auto.
      cbn; f_equal. rewrite Fn. auto.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | h1 :: t1, h2 :: t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
    end.

  Example test_beq_natlist1 :
    (beq_natlist nil nil = true).
  cbn. auto. Qed.


  Example test_beq_natlist2 :
    beq_natlist [1;2;3] [1;2;3] = true.
  auto. Qed.

  Example test_beq_natlist3 :
    beq_natlist [1;2;3] [1;2;4] = false.
  auto. Qed.

  Theorem beq_natlist_refl : forall l:natlist,
      true = beq_natlist l l.
  Proof.
    refine (fix Fn l :=
              match l with
              | [] => eq_refl
              | h :: t => _
              end).
    cbn. remember (beq_nat h h) as Hb. destruct Hb as [Hb | Hb].
    apply Fn. assert (beq_nat h h = true). induction h.  inversion HeqHb.
    cbn in *. auto. rewrite <- HeqHb in H. inversion H.
  Qed.

  Theorem count_member_nonzero : forall (s : bag),
      leb 1 (count 1 (1 :: s)) = true.
  Proof.
    cbn. refine (fun H => eq_refl).
  Qed.

  Theorem ble_n_Sn : forall n,
      leb n (S n) = true.
  Proof.
    refine (fix Fn n :=
              match n with
              | O => eq_refl
              | S n' => _
              end).
    cbn. apply Fn.
  Qed.

  Theorem remove_does_not_increase_count: forall (s : bag),
      leb (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    refine (fix Fn s :=
              match s with
              | [] =>  eq_refl
              | h :: t => _
              end).
    cbn. destruct h; cbn. rewrite ble_n_Sn; auto.
    apply Fn.
  Qed.

  Theorem rev_injective :
    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2. 
  Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H. rewrite rev_involutive.
    auto.
  Qed.

  Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
    match l with
    | nil => 42 (* arbitrary! *)
    | a :: l' => match beq_nat n O with
                | true => a
                | false => nth_bad l' (pred n)
                end
    end.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.


  Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => match beq_nat n O with
                | true => Some a
                | false => nth_error l' (pred n)
                end
    end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  auto. Qed.
  
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  auto. Qed.
  
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  auto. Qed.

  Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => if beq_nat n O then Some a
                else nth_error' l' (pred n)
    end.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
    end.


  Definition hd_error (l : natlist) : natoption :=
    match l with
    | [] => None
    | h :: t => Some h
    end.
    
 
  Example test_hd_error1 : hd_error [] = None.
  auto. Qed.
  
  Example test_hd_error2 : hd_error [1] = Some 1.
  auto. Qed.
  
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  auto. Qed.


  Theorem option_elim_hd : forall (l:natlist) (default:nat),
      hd default l = option_elim default (hd_error l).
  Proof.
    refine (fix Fn l :=
              match l with
              | [] => _
              | h :: t => _
              end).
    + cbn; intro default; try auto.
    + cbn; intro default; try auto.
  Qed.

End Natlist.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id (x1 x2 : id) : bool :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intro x. destruct x; cbn.
  induction n; try auto.
Qed.

Module PartialMap.
  Export Natlist.

  Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map.

  Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record x1 n1 d1 => if beq_id x x1 then Some n1 else find x d1
    end.

  Theorem update_eq :
    forall (d : partial_map) (x : id) (v: nat),
      find x (update d x v) = Some v.
  Proof.
    unfold update; cbn. intros d x v. rewrite <- beq_id_refl.
    auto.
  Qed.

  Theorem update_neq :
    forall (d : partial_map) (x y : id) (o: nat),
      beq_id x y = false ->  find x (update d y o) = find x d.
  Proof.
    cbn. intros d x y o H. rewrite H. auto.
  Qed.

End PartialMap.

