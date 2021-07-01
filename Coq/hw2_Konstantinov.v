Require List Bool Arith.
Require Import Omega. 
(** 5 *)
Module Exc5.

(* Consider the following innocently looking polymorphic constant function: *)
Definition const {A B : Type} : A -> B -> A := fun a _ => a.

Check const.
Check @const.
Check @const nat bool.
Check @const nat bool 5 true.

Check const 5 true.
Compute @const nat bool 5 false.
Compute @const nat bool 5 true.
Compute const 5 nat.

(* If two constants agree in value, those values must be the same, right? *)
Axiom const_eq : forall (A B : Type) (x y : A),
  @const _ B x = const y -> x = y.

(* Yet this is unprovable. To show this fact, infer a contradiction from
  const_eq and the well-reputed extensionality axiom, which is provably
  consistent with the 'basic' Coq axioms. *)

Axiom functional_extensionality : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Theorem absurd : False.
Proof. 
assert ( H := const_eq nat False 0 1).
discriminate H. apply functional_extensionality.
intro x. destruct x. 
Qed.


End Exc5.

(** 6 *)
Module Exc6.
 

(* Prove the following 'strong' (or 'order') induction principle for nat. *)
Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, k < m -> P k) -> P m) ->
    forall n, P n.
Proof. 
intros H n. apply H.
assert (G: forall k y, y < k -> P y).
 - intros k. induction k.
    + intros y B. inversion B.
    + intros y B. apply H. intros z C. apply IHk. omega.
 - apply G.
Qed.

End Exc6.

(** 7 *)
Module Exc7.

(* The canonical repersentation of naturals with two constructors O and S
  is in no way space effective. A binary notation would be much better in
  this respect. Consider the following inductive definition for 'binaries'
  and prove the following lemmas.  *)

(* You may import any arithmetical lemma you need from a suitable library. *)

Inductive bin : Set :=
(* zero *)
  | Z : bin
(* double a number *)
  | db : bin -> bin
(* double then increment *)
  | dbi : bin -> bin.

(** 7a *)

Fixpoint incr (b: bin) : bin :=
  match b with
    | Z =>  dbi Z
    | db x => dbi x
    | dbi x => db (incr x)
  end.

Print nat.
Compute 2 * 3.
Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | Z => O
    | db x => 2 * (bin_to_nat x)
    | dbi x => S (2 * (bin_to_nat x))
  end.

Lemma bin_to_nat_preserves_zero :
  bin_to_nat Z = 0.
Proof. reflexivity. Qed.

Import Arith.
(*Search nat.*) 
Lemma bin_to_nat_preserves_incr (b : bin) :
 bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
 induction b.
- simpl; reflexivity.
- simpl; reflexivity.
- simpl; rewrite IHb. 
  (*Search _ (S (_ + _ )).*) rewrite plus_n_Sm. rewrite plus_Sn_m. reflexivity.
Qed.

(** 7b *)

Fixpoint nat_to_bin (n : nat) : bin :=
 match n with
  | O => Z
  | S x => incr (nat_to_bin x)
 end. 

Example test19 : nat_to_bin 19 =  dbi (dbi (db (db (dbi Z)))).
Proof. auto. Qed.

Theorem left_inverse n : bin_to_nat (nat_to_bin n) = n.
Proof. induction n.
- simpl; reflexivity.
- simpl; rewrite bin_to_nat_preserves_incr. rewrite IHn. reflexivity.
Qed.

(** 7c *)

Compute nat_to_bin 2. (*39 = 100111*)
Compute bin_to_nat (dbi (db Z)).
Compute nat_to_bin 1. (*dbi Z*)

(* Is bin_to_nat injective? *)
Example not_right_inverse : exists b,   (* b = 0010*)
  nat_to_bin (bin_to_nat b) <> b.
Proof. exists (db Z). simpl. discriminate. Qed.
(* pose or set - for introduction constant*)

(* But there is a bypass for this problem: normalization of a binary. *)
(* Все сломать может только db Z *)
Fixpoint normalize (b : bin) : bin :=
 match b with
  | Z => Z
  | db x => match normalize x with
             | Z => Z
             | db y => db (db y)
             | dbi y => db (dbi y)
            end
  | dbi x => dbi (normalize x)
 end.

Compute normalize (db (db (dbi Z))).

Lemma normalized_is_normal b : normalize (normalize b) = normalize b.
Proof. 
induction b.
- reflexivity.
- simpl. remember (normalize b) as H. destruct H.
   * assumption.
   * replace (normalize (db (db H))) with ( match normalize (db H) with
                                             | Z => Z 
                                             | db x => db (db x) 
                                             | dbi x => db (dbi x) 
                                            end) .
     ** rewrite IHb. reflexivity.
     ** auto. 
   * simpl. rewrite <- IHb. reflexivity.
- simpl; rewrite IHb; reflexivity.
Qed.

Example test : nat_to_bin (bin_to_nat (dbi (db (dbi (db (db Z)))))) =
    normalize (dbi (db (dbi (db Z)))).
Proof. auto. Qed.

(** 7d *)

Theorem help1 b : normalize (incr b) = incr (normalize b).
Proof.
  induction b.
  - auto.
  - simpl. remember (normalize b) as H. destruct H; auto.
  - simpl. rewrite IHb. remember (normalize b) as H. destruct H; auto.
Qed.

Theorem help2 n : nat_to_bin(n + n) = normalize(db (nat_to_bin n)).
Proof.
  induction n.
  - auto.
  - replace (nat_to_bin (S n + S n)) with (incr (incr (nat_to_bin (n + n)))).
    * rewrite IHn. do 2 rewrite <- help1. auto.
    * simpl. rewrite <- plus_n_Sm. auto.
Qed.

Theorem right_inverse_for_normal b : nat_to_bin (bin_to_nat b) =
    normalize b.
Proof. induction b.
  - reflexivity.
  - simpl. rewrite plus_0_r.
    rewrite help2. simpl. rewrite IHb. rewrite normalized_is_normal. auto.
  - simpl. rewrite plus_0_r. rewrite help2. rewrite IHb. simpl. rewrite normalized_is_normal.
    remember (normalize b) as H. induction H; auto.
Qed.

End Exc7.

(** 8 *)
Module Exc8.

Import List.
Import ListNotations.
Import Arith.
Import Bool.

Inductive sorted : list nat -> Prop := 
| sorted_nil:
    sorted []
| sorted_1: forall x,
    sorted [x]
| sorted_cons: forall x y l,
   x <= y -> sorted (y::l) -> sorted (x::y::l).

Fixpoint sorted_b (l : list nat) : bool :=
  match l with
  | [] => true
  | x::t => match t with 
            | [] => true
            | (y::_) => (x <=? y) && sorted_b t
            end
  end.

Compute sorted_b [1;2;3].
Compute sorted_b [1;3;2].
Compute sorted [3;1;2].
(** 8a *)

(* Prove that these two definitions of a sorted list
   reflect each  other. *)

Lemma sorted_b_sorted (l : list nat) : 
  sorted l <-> sorted_b l = true.
Proof. 
induction l.
- simpl; split.
   + intros; constructor.
   + intros; constructor.
- split; intros.
   + induction H; auto.
     * assert (Leb := leb_correct). specialize Leb with x y. apply Leb in H.
      replace (sorted_b (x :: y :: l0) = true) 
                  with ((x <=? y) && sorted_b (y :: l0) = true).
         ** (*Search (_ && _).*) apply andb_true_iff. auto.
         ** simpl; auto.
   + destruct IHl. induction l.
     * constructor.
     * constructor.
         ** cbn in H. apply andb_prop in H. destruct H. apply leb_complete. auto.
         ** apply H1. cbn in H. apply andb_prop in H. destruct H. simpl. auto.
  Qed.

Theorem sorted_b_spec (l : list nat) :
  reflect (sorted l) (sorted_b l).
Proof.
(*Search reflect.*) apply iff_reflect; apply sorted_b_sorted.
Qed.

(** 8b *)

Definition sorted' (al: list nat) :=
 forall i j, i < j < length al -> nth i al 0 <= nth j al 0.

Compute nth 0 [1;2;3] 2020.
Compute nth 1 [1;2;3] 2020.
Compute nth 2 [1;2;3] 2020.
Compute nth 3 [1;2;3] 2020.
Search _ nth.

(* Prove that this 'universal' definition for sortedness is
   equivalent to the inductive one. *)

Lemma sorted_b_sorted': forall l, sorted l -> sorted' l.
Proof. 
intros l H. induction H; unfold sorted'; intros.
- simpl in H. inversion H as [H1 H2]. inversion H2. (*apply Nat.lt_eq_cases; right. *)
- simpl in H. inversion H as [H1 H2]. inversion H2.
  + rewrite H3 in H1; inversion H1.
  + inversion H3.
- simpl in H1. unfold sorted' in IHsorted. specialize IHsorted with i j. 
 change [x :: y :: l] with ([x]++[y :: l]). 
  

 apply sorted_b_sorted in H0. 
Admitted.

Lemma sorted'_b_sorted: forall l, sorted' l -> sorted l.
Proof. intros. induction l.
- constructor.
- apply sorted_b_sorted.
 apply sorted_b_sorted.
Admitted.

Theorem sorted'_sorted (l : list nat) :
  sorted l <-> sorted' l.
Proof. 
split; try apply sorted_b_sorted'; try apply sorted'_b_sorted.
Qed.


End Exc8.