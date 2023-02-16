Inductive bool: Type :=
    | true
    | false.

Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1: bool) (b2: bool) : bool := 
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1: bool) (b2: bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb2: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Practice 1: 1 星, standard (nandb)*)
Definition nandb (b1:bool) (b2:bool) : bool :=
    match (b1, b2) with
    | (true, true) => false
    | (_, _) => true
    end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Practice 2: 1 星, standard (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    b1 && b2 && b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground.
    Inductive nat: Type :=
        | O
        | S (n: nat).
    
    Definition pred (n: nat) : nat :=
        match n with
        | O => O
        | S n' => n'
        end.
End NatPlayground.

(* Practice 3: 1 星, standard (factorial) *)
Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S n' => (mult n (factorial n'))
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
            | O => true
            | S m' => false
            end
    | S n' => match m with
            | O => false
            | S m' => eqb n' m'
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

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(* Practice 4: 1 星, standard (ltb) *)
Definition ltb (n m : nat) : bool := (n <=? m) && (negb (n =? m)).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Practice 5: 1 星, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o H1 H2.
    rewrite -> H1.
    rewrite <- H2.
    reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
    n = m ->
    n + n = m + m.
Proof.
    (* 将两个量词移到上下文中： *)
    intros n m.
    (* 将前提移到上下文中： *)
    intros H.
    (* 用前提改写目标： *)
    rewrite -> H.
    reflexivity. Qed.

Theorem mult_n_0_m_0 : forall n m : nat,
    (n * 0) + (m * 0) = 0.
Proof.
    intros n m.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.

(* Practice 6: 2 星, standard (mult_n_1) *)
Theorem mult_n_1 : forall n : nat,
    n * 1 = n.
Proof.
    intros n.               (* n * 1 = n *)
    rewrite <- mult_n_Sm.   (* n * m + n = n * S m *)
    rewrite <- mult_n_O.    (* 0 = n * 0 *)
    rewrite -> plus_O_n.    (* 0 + n = n *)
    reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
    intros n. destruct n as [| n'] eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b eqn:E.
    - reflexivity.
    - reflexivity. 
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
        + reflexivity.
        + reflexivity.
    - destruct c eqn:Ec.
        + reflexivity.
        + reflexivity.
Qed.

Theorem andb3_exchange : forall b c d, 
    andb (andb b c) d = andb (andb b d) c.
Proof.
    intros b c d. destruct b eqn:Eb.
    - destruct c eqn:Ec.
        { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
        { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
    - destruct c eqn:Ec.
        { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
        { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
Qed.

(* Practice 7: 2 星, standard (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros [] [].
    - simpl. reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
    - simpl. intros H. rewrite <- H. reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
Qed.

(* Practice 8: 1 星, standard (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
    intros n.
    destruct n as [| n'] eqn:E.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* Practice 9: 1 星, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
    forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros f H b.
    rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

(* Practice 10: 1 星, standard (negation_fn_applied_twice) *)
Theorem negation_fn_applied_twice :
    forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros f H b.
    rewrite -> H.
    rewrite -> H.
    destruct b.
    - reflexivity.
    - reflexivity.
Qed.



