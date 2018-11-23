Require Export Lists.


Inductive boollist : Type :=
| bool_nil : boollist
| bool_con : bool -> boollist -> boollist.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (n : nat) : list X :=
  match n with
  | O => @nil X
  | S n' => cons X x (repeat X x n')
  end.


Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

  Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat ->  mumble
  | c : mumble.

  Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

  Check (d _ (b a 5)).
  Check (d mumble (b a 5)).
  Check (d bool (b a 5)).
  Check (e bool true).
  Check (e mumble (b c 0)).

End MumbleGrumble.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x n.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).


Inductive list' {X:Type} : Type :=
| nil' : list'
| cons' : X -> list' -> list'.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).


Theorem app_nil_r : forall  (X : Type) (l : list X),
    l ++ [] = l.
Proof.
  refine (fun X => fix F l :=
            match l with
            | [] => _
            | h :: t => _
            end).
  + exact eq_refl.
  + cbn. rewrite F. exact eq_refl.
Qed.

  
Theorem app_assoc : forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  refine (fun  A =>
            fix F l :=
            match l with
            | [] => fun m n => _
            | h :: t => fun m n => _
            end).
  + cbn. exact eq_refl.
  + cbn. rewrite F. exact eq_refl.
Qed.

              
  
Lemma app_length : forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  refine (fun X =>
            fix F l1 :=
            match l1 with
            | [] => fun l2 => _
            | h :: t => fun l2 => _
            end).
  + cbn. exact eq_refl.
  + cbn. rewrite F.  exact eq_refl.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  refine (fun X =>
            fix F l1 :=
            match l1 with
            | [] => fun l2 => _
            | h :: t => fun l2 => _
            end).
  + cbn. rewrite app_nil_r. exact eq_refl.
  + cbn. rewrite F. rewrite app_assoc. exact eq_refl.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | h1 :: t1, h2 :: t2 => (h1, h2) :: combine t1 t2
  end.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (h1, h2) :: rest =>
    let (l1, l2) := split rest in
    (h1 :: l1, h2 :: l2)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  cbn. exact eq_refl.
Qed.

Module OptionPlayground.

  Inductive option (X : Type) : Type :=
  | Some : X -> option X
  | None : option X.

  Arguments Some {X} _.
  Arguments None {X}.
End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | h :: t => if beq_nat n O then Some h else nth_error t (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.


Definition doit3times {X : Type} (f : X -> X) (x : X) : X :=
  f (f (f x)).

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    let ret_val := filter f t in
    if f h then h :: ret_val else ret_val
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.
Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.
Example test_filter2:
  filter length_is_1
         [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.


Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (blt_nat 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
compute. exact eq_refl.
Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
compute. exact eq_refl. Qed.

Definition partition {X : Type} (f : X -> bool) (l : list X) : list X * list X :=
  (filter f l, filter (fun x => negb (f x)) l).


Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
auto. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
auto. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => f h :: map f t
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  refine (fun X Y f =>
            fix F l1 :=
            match l1 with
            | [] => fun l2 => eq_refl
            | h :: t => fun l2 => _
            end).
  + cbn. rewrite F. exact eq_refl.
Qed.

  
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  refine (fun X Y f =>
            fix F l :=
            match l with
            | [] => _
            | h :: t => _
            end).
  + cbn. exact eq_refl.
  + cbn. rewrite  (map_app X Y f (rev t) [h]). 
    cbn. rewrite F. exact eq_refl. 
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
cbn. exact eq_refl.
Qed.

Definition option_map {X Y : Type} (f : X -> Y) (x : option X) : option Y :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.


Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | [] => b
  | h :: t =>
    let rev_val := fold f t b in
    f h rev_val
  end.


Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
cbn. exact eq_refl. Qed.

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  refine (fun X =>
            fix F l :=
            match l with
            | [] => _
            | h :: t => _
            end).
  + cbn. exact eq_refl.
  + cbn. unfold fold_length in F. rewrite F. exact eq_refl.
Qed.


Definition fold_map {X Y : Type} (f : X -> Y) (l: list X) : list Y :=
  fold (fun x acc => cons (f x) acc) l [].

Lemma fold_map_correct :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    fold_map f l = map f l.
Proof.
  intros X Y f.
  induction l.
  + auto.
  + cbn. f_equal.
    unfold fold_map in IHl. auto.
Qed.

Module Church.

  Definition nat : Type := forall (X : Type), (X -> X) -> X -> X.

  Definition one : nat :=
    fun (X : Type) (f : X -> X) (x : X) =>
      f x.

  Definition two : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (f x).

  Definition zero : nat :=
    fun (X : Type) (f : X -> X) (x : X) => x.

 
  Definition succ (n : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

  Example succ_1 : succ zero = one.
  Proof. unfold succ, one, zero. exact eq_refl.
  Qed.

  Definition plus (n m : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) =>
      m X f (n X f x).

  Example plus_1 : plus zero one = one.
  Proof.
    unfold plus, zero, one.
    exact eq_refl.
  Qed.
  Definition three : nat := @doit3times.
  
  Example plus_2 : plus two three = plus three two.
  Proof. unfold plus, two, three, one, zero, doit3times.
         exact eq_refl.
  Qed.

  (* This is challenging problem. Don't look for solution *)
  Definition mult (n m : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) =>
     m X f (plus n zero X f x).

  Example mult_1 : mult one one = one.
  Proof. unfold mult, one, one, plus, zero.
  Admitted.

End Church.

