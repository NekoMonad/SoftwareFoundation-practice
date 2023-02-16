From LF Require Export Basics.

Theorem plus_n_0: forall n : nat, n = n + 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag: forall n,
    n - n = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Practice1: 2 星, standard, recommended (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed. 
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
      rewrite <- plus_Sn_m. 
      simpl. 
      rewrite <- IHn'. 
      reflexivity.
Qed. 
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. rewrite <- plus_n_0. reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite -> IHn'. reflexivity.
Qed. 
Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* Practice2: 2 星, standard (double_plus) *)
Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus : forall n, double n = n + n .
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* Practice3: 2 星, standard, optional (evenb_S) *)
Fixpoint evenb (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Lemma negb_double_apply: forall b : bool, negb (negb b) = b.
Proof.
    intros b. destruct b.
    + reflexivity.
    + reflexivity.
Qed.
Theorem evenb_S : forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - rewrite -> IHn'. simpl.
      rewrite -> negb_double_apply.
      reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
    intros n m.
    assert (H: 0 + n = n). { reflexivity. }
    rewrite -> H.
    reflexivity. 
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H: n + m = m + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H. reflexivity. 
Qed.

(* Practice4: 3 星, standard, recommended (mult_comm) *)
Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite -> plus_assoc. rewrite -> plus_assoc.
    assert (H: n + m = m + n). 
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. rewrite <- mult_n_O. reflexivity.
    - simpl. 
      rewrite -> IHn'. 
      rewrite <- mult_n_Sm.
      rewrite -> plus_comm.
      reflexivity.
Qed.

(* Practice5: 3 星, standard, optional (more_exercises) *)
Check leb.
Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.
Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
    intros n.
    reflexivity.
Qed.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
    intros b. rewrite -> andb_commutative. reflexivity.
Qed.
Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
    intros n m p H.
    induction p as [| p' IHp'].
    - simpl. rewrite -> H. reflexivity.
    - simpl. rewrite -> IHp'. reflexivity.
Qed.
Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
    intros n.
    reflexivity.
Qed.
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
    intros n.
    simpl. rewrite <- plus_n_0. reflexivity.
Qed.
Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
    intros b c.
    destruct b.
    destruct c.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p.
    induction n.
    - reflexivity.
    - simpl. rewrite -> IHn. rewrite -> plus_assoc. reflexivity.
Qed. 
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. 
      rewrite -> IHn'. 
      rewrite -> mult_plus_distr_r.
      reflexivity.
Qed.
