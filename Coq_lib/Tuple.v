(** * The type constructors of homogeneous tuples *)

Require Import Spreadable.

(** ** The tuples type constructors family *)
Fixpoint Tuple (n : nat) (A : Type) : Type :=
 match n with
  | 0   => A
  | S p => A * Tuple p A
 end.

(** ** Tuple n is spread-able for any n *)
Fixpoint tuple_map (n : nat) : Map (Tuple n) :=
 match n with
  | 0   => fun A B f t => f t
  | S p => fun A B f t => (f (fst t), tuple_map p _ _ f (snd t))
 end.

Lemma tuple_cmp_map (n : nat) : MapComposition (tuple_map n).
Proof.
unfold MapComposition. induction n; intros A B C f g x.
 + simpl in *. reflexivity.
 + simpl in *. destruct x.
   simpl. rewrite IHn with A B C f g t. reflexivity.
Defined.

Lemma tuple_cng_map (n : nat) : MapCongruence (tuple_map n).
Proof.
unfold MapCongruence. induction n; intros A B f g x H.
 + simpl in *. apply H.
 + simpl in *. rewrite H. erewrite IHn.
   reflexivity. assumption.
Defined.

Definition tuple_mapable n : MapAble (Tuple n) :=
  mkMap (Tuple n) (tuple_map n) (tuple_cng_map n) (tuple_cmp_map n).

Fixpoint tuple_foldr (n : nat) : Fold (Tuple n) :=
 match n with
  | 0   => fun A B f b t => f b t
  | S p => fun A B f b t => f (tuple_foldr p _ _ f b (snd t)) (fst t)
 end.

Fixpoint tuple_foldl (n : nat) : Fold (Tuple n) :=
 match n with
  | 0   => fun A B f b t => f b t
  | S p => fun A B f b t => tuple_foldl p _ _ f (f b (fst t)) (snd t)
 end.

Definition tuple_foldable n : FoldAble (Tuple n) :=
  mkFold (Tuple n) (tuple_foldr n) (tuple_foldl n).

Fixpoint tuple_any (n : nat) : TransPred (Tuple n) :=
 match n with
  | 0   => fun A P t => P t
  | S p => fun A P t => (P (fst t)) \/ (tuple_any _ _ P (snd t))
 end.

Lemma tuple_dec_any (n : nat) : TransDec (tuple_any n).
Proof.
unfold TransDec. induction n.
 + simpl in *. intros A P Hdec. unfold Dec in *. assumption.
 + intros A P Hdec x. simpl in *. unfold Dec in *.
   specialize (IHn A P Hdec). destruct x.
   destruct (Hdec a).
    * tauto.
    * destruct (IHn t).
      - tauto.
      - right. intro Hfalse. destruct Hfalse;tauto.
Defined.

Fixpoint tuple_all (n : nat) : TransPred (Tuple n) :=
 match n with
  | 0   => fun A P t => P t
  | S p => fun A P t => (P (fst t)) /\ (tuple_all _ _ P (snd t))
 end.

Lemma tuple_dec_all (n : nat) : TransDec (tuple_all n).
Proof.
unfold TransDec. induction n.
 + simpl in *. intros A P Hdec. unfold Dec in *. assumption.
 + intros A P Hdec x. simpl in *. unfold Dec in *.
   specialize (IHn A P Hdec). destruct x.
   destruct (Hdec a).
   * destruct (IHn t).
      - tauto.
      - right. intro Hfalse. tauto.
   * destruct (IHn t).
      - tauto.
      - right. intro Hfalse. destruct Hfalse. tauto.
Defined.

Definition tuple_any_all_able n : AnyAllAble (Tuple n) :=
  mkAnyAll (Tuple n) (tuple_any n) (tuple_dec_any n)
      (tuple_all n) (tuple_dec_all n).

Lemma tuple_dec_eq (n : nat) : DecEq (Tuple n).
Proof.
unfold DecEq. induction n; intros.
 + exact X.
 + unfold Decidable in *. destruct x ; destruct y. decide equality.
Defined.

Definition tuple_eqable (n : nat) : EqAble (Tuple n) :=
  mkEq (Tuple n) (tuple_dec_eq n).

Definition tuple_spreadable (n : nat) : SpreadAble (Tuple n) :=
 mkSpread (Tuple n)
          (tuple_foldable n)
          (tuple_mapable n)
          (tuple_any_all_able n)
          (tuple_eqable n) 
          (* _ _ _ (tuple_map_spec n)*).

Eval compute in (mkSpread (Tuple 2)).

Definition in_tuples n : forall A, A -> Tuple n A -> Prop
 := fun A x => tuple_any n A (fun y => x = y ) .

Lemma in_tuples_S n : forall A x a t,
 in_tuples (S n) _ x (a, t) <-> x = a \/ in_tuples n A x t.
Proof.
intros; simpl; split ; auto.
Qed.

Lemma tuple_in_map  (n : nat) : forall (A B : Type) (f : A -> B) l (x : A),
in_tuples n _ x l -> in_tuples n _ (f x) (tuple_map n _ _ f l).
Proof.
induction n ; intros.
+ simpl in *. congruence.
+ destruct l ; simpl in *. 
  apply in_tuples_S in H. apply in_tuples_S. destruct H.
  -  subst; tauto.
  - right ; auto.
Qed.

(** ** The size of a Tuple can be retrieved, and is equal to S n *)
Definition tuplesSize (n : nat) {A : Type} (T : Tuple n A) : nat :=
  size _ (tuple_foldable n) A T.
(*
Lemma sizen_equiv_sucn : forall {n} {A : Type} {t : Tuple n A},
tuplesSize n t = S n.
Proof.
  unfold tuplesSize ; simpl; intros;
    induction n. simpl. auto. simpl.
Defined.
**)
(* Version Catherine, oupss *)
Definition size_C {A : Type}  (n : nat): Tuple n A -> nat :=
(foldr _ (tuple_foldable n)) A _ (fun x => fun _ => x + 1) 0.

Require Import Lia.

Lemma size_is_sucn : forall A n (p : Tuple n A) ,
size_C _ p =  n+1 .
Proof.
unfold size_C, tuple_foldr ; simpl; intros; induction n; simpl; auto.
destruct p ; simpl.
rewrite IHn. lia.
Qed.

Print tuple_foldr.

(** ** The membership in a Tuple *)
Definition tuplesIn_prop (n : nat) (A : Type) (x : A)
  (T : Tuple n A) : Prop :=
  in_prop _ (tuple_any_all_able n) A x T.

(** ** Examples of tuples *)
Definition example0 : Tuple 0 nat := 3.
Definition example3 : Tuple 2 nat := (3, (2, 9)).

(** ** Examples of function calls over tuples *)

Definition example0Map :=
(map _ (tuple_mapable _)) _ _ (fun x => x + 3) example0.

Eval compute in example0Map.
(* = 6 : Tuples 0 nat *)
     
Eval compute in ((map _ (tuple_mapable _)) _ _ (fun x => x + 3) example3).
(* = (6, (5, 12)) : Tuples 2 nat *)

Eval compute in 
((foldr _ (tuple_foldable _)) _ _ (fun x => fun y => x + y) 0 example0).
(* = 3 : nat *)
 
Eval compute in 
((foldr _ (tuple_foldable _)) _ _ (fun x => fun y => x + y) 0 example3).
(* = 14 : nat *)
 
Eval compute in
(size_C _ example0).
(* = 1 : nat *)

Eval compute in 
(size_C _ example3).
(* = 3 : nat *)
 
(** ** Examples of predications over tuples *)

Lemma example0Any : 
(any _ (tuple_any_all_able _ )) _ (fun x => x > 2) example0.
Proof. compute. auto. Qed.

Lemma example3Any : 
(any _ (tuple_any_all_able _ )) _ (fun x => x > 7) example3.
Proof. compute. auto. Qed.

Lemma example0All : 
(all _ (tuple_any_all_able _ )) _ (fun x => x > 2) example0.
Proof. compute. auto. Qed.

Lemma example3All : 
(all _ (tuple_any_all_able _ )) _ (fun x => x < 11) example3.
Proof. compute. lia. Qed.



Definition size_regular F (f : FoldAble F) {A : Type} : (F A) -> nat :=
foldr F f A _ (fun x => fun _ => x + 1) 0.

Eval compute in (size_regular (Tuple 2) (tuple_foldable _ )) example3.
(* = 3 : nat *)

From QuickChick Require Import QuickChick Tactics.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

 
Fixpoint tuple_gensized (n : nat) : Gensized (Tuple n) :=
 match n with
  | 0   => fun A g size => do! v <- g size ; returnGen v
  | S p => fun A g size => 
         do! v <- g size ; 
         do! t <- tuple_gensized p _ g size; 
         returnGen (v,t)
         end.


Definition example0Gensized := tuple_gensized 0 nat arbitrarySized 10.

Sample example0Gensized. 

Definition example3Gensized := tuple_gensized 3 nat arbitrarySized 10.

Sample example3Gensized.
