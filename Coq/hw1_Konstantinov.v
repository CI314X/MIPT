(* HW1 *)
Require List.

(** 1 *)
Module Exc1.
(* Define a function zip that satsifies the following tests. *)
Import List.
Import ListNotations.

(*Compute [(1,3)] ++ [(2,4)]. *)

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1 with
    |nil => nil
    |x :: xs => match l2 with
                  |nil => nil
                  |y :: ys => [(x, y)] ++ zip xs ys
                end
  end.

Compute zip [1; 2; 3] [3; 4]. 

Example exm1 : zip [1; 2; 3] [3; 4] = [(1,3); (2,4)].
Proof. reflexivity.
Qed.

Example exm2 : zip [1; 2] [true; false; true] = [(1,true); (2,false)].
Proof. reflexivity. 
Qed.

Example exm4 : @zip nat _ [] [3; 4; 5] = [].
Proof. reflexivity.
Qed.


End Exc1.

(** 2 *)
Module Exc2.
(* Devise proof terms of the following types. THEN construct such terms
   via tactics. *)

(** 2a *)

Definition t1' (A B C : Prop) : (A -> B) -> (B -> C) -> (A -> C) :=
fun x y z => y (x z).


Lemma t1 (A B C : Prop) : (A -> B) -> (B -> C) -> (A -> C).
Proof. 
intros x y z.
apply y. apply x. assumption.
Qed.

(** 2b *)

Definition t2' (A B C : Prop) : (C -> ~A \/ ~B)  -> (A /\ B -> ~C) :=
 fun H1 H2 C => match H2 with conj H2A H2B =>
                  match (H1 C) with
                   | or_introl notA => notA H2A
                   | or_intror notB => notB H2B
                  end
               end.


Lemma t2 (A B C : Prop) : (C -> ~A \/ ~B)  -> (A /\ B -> ~C).
Proof. (**tauto. *) 
intros x y z. destruct x.  
- exact z.
- destruct y; contradiction.
- destruct y; contradiction.
Qed.

(**apply not_all_ex_not in x. *)
(** 2c *)

Check ex_intro.
Check or_introl.
Definition t3' (X : Type) (P Q : X -> Prop) : (exists x, P x \/ Q x) ->
  (exists x, P x) \/ exists x, Q x :=
   fun H => match H with
              | ex_intro _ y (or_introl HP) => or_introl (ex_intro _ y HP)
              | ex_intro _ y (or_intror HQ) => or_intror (ex_intro _ y HQ)
            end.

Lemma t3 (X : Type) (P Q : X -> Prop) : (exists x, P x \/ Q x) ->
  (exists x, P x) \/ exists x, Q x.
Proof. 
intro H. destruct H as [y H1]. destruct H1. 
- left; exists y; assumption.
- right; exists y; assumption.
Qed.


End Exc2.

(** 3 *)
Module Exc3.
(* Prove the following lemmas. Use the axioms as needed. *)

Axiom tnd : forall A : Prop, ~A \/ A.

Variable NotEmpty : Type.
Axiom not_empty : exists x : NotEmpty, True.


Lemma dneg_tnd : forall a : Prop, (~a \/ a) -> ~~a -> a.
Proof.
intros a H1 H2. destruct H1 as [H1 | H1];
[ destruct H2 | idtac ]; assumption.
Qed.
Lemma dneg : forall a : Prop, ~~a -> a.
Proof.
intro. apply dneg_tnd. apply tnd.
Qed.
Theorem deMorgan (A B: Prop): ~(A/\B) -> ~A\/~B.
Proof.
  intro H; apply dneg; intro H2; apply H; split.
  - apply dneg; intro HA; apply H2; left; assumption.
  - apply dneg; intro HB; apply H2; right; assumption.
Qed.
Lemma contra : forall a b : Prop, (a -> b) -> (~b -> ~a).
Proof.
intros a b H1 H2 H3; destruct H2; apply H1; exact H3.
Qed.
Lemma imp_def : forall a b : Prop, (a -> b) <-> (~a \/ b).
Proof.
intros a b. split; intro H.
- assert (Htnd := tnd a); destruct Htnd as [Hn | Hp].
  + left. assumption.
  + right. apply H. assumption.
- intro Ha; destruct H; [destruct H | idtac]; assumption.
Qed.

(** 3a *)
Lemma t1 (A B C : Prop) : (A /\ B -> ~C) -> (C -> ~A \/ ~B).
Proof.
 intros H1. 
 apply imp_def. apply imp_def in H1. destruct H1.
  - apply deMorgan in H; right; assumption.
  - left; assumption.
Qed.


Lemma neg_ex_all_neg (T : Type) (P: T -> Prop) :
  ~(exists n : T, P n) -> (forall n : T, ~P n).
Proof.
 intros HnE n H; destruct HnE;
 exists n; assumption.
Qed.


(** 3b *)
Lemma t2 (P Q : NotEmpty -> Prop) :
 ((exists x, ~Q x) -> exists x, ~P x) -> (forall x, P x) -> exists x, Q x.
Proof. intros H1 H2.  apply imp_def in H1. destruct H1. 
- clear H2. 
  assert (Hn := neg_ex_all_neg _ (fun x : NotEmpty => ~ Q x ) H). simpl in Hn. clear H.  
  assert ( Hex := not_empty). destruct Hex as [y _]. 
  specialize Hn with y.  apply dneg in Hn. exists y. assumption.
- destruct H as [x H3]. exists x. specialize H2 with x. contradiction.
Qed.

Lemma and_assoc : forall a b c : Prop,
    a /\ b <-> b /\ a.
Proof. split;
intros H.
- destruct H as [Ha Hb].
do 2 try split; assumption.
- destruct H as [Ha Hb].
do 2 try split; assumption.
Qed.
 
(** 3c *)
Lemma t3 (R : NotEmpty -> NotEmpty -> Prop) :
  (forall x, exists y, R x y) -> (forall x y z, R x y /\ R x z -> y = z) ->
    (forall x y z, R x y /\ R y z -> R x z) -> exists x, R x x.
Proof. 
intros H1 H2 H3. assert ( Hex := not_empty). destruct Hex as [x _].
assert (H1n : forall y : NotEmpty, exists z : NotEmpty, R y z).
- assumption.
- specialize H1 with x; destruct H1 as [y Rxy].
  specialize H1n with y; destruct H1n as [z Ryz].
  specialize H2 with x y z; specialize H3 with x y z. 
  assert (H4 := conj Rxy Ryz); apply H3 in H4.
  assert (H5 := conj Rxy H4); apply H2 in H5. 
  destruct H5; exists y; assumption.
Qed.

End Exc3.


(** 4 *)
Module Exc4.
(* State and prove that there is no term of the type kva *)

Inductive kva : Set :=
  | kva0 : kva -> kva
  | kva1 : kva -> kva -> kva.

Check kva.
Check kva_rect.
Check kva_ind.
Check kva_rec.

Lemma kva_not_exist0 (kvak : kva) : (exists x : kva, False).
Proof.
apply kva_ind.
* intros. auto.
* intros. auto.
* auto.
Qed.


Lemma kva_not_exist1 (kvak : kva) (P : kva -> Prop) : (exists k : kva, P k) -> False.
Proof.
apply kva_ind.
- intros. auto.
- intros. auto.
- assumption.
Qed.


End Exc4.
































