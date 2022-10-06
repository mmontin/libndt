(** * The family of type constructors for n-ary perfectly balanced trees *)

Require Import LNDT.
Require Import Spreadable.
Require Import Tuple.
Require Import Lia.

Definition PerfectTree n : TT := LNDT (Tuple n).

Definition pt_spreadable n : SpreadAble (PerfectTree n) := 
  lndt_spreadable (tuple_spreadable n).

Definition pt_map         n := map         _ (map_able _ (pt_spreadable n)).
Definition pt_cng_map     n := map_congru  _ (map_able _ (pt_spreadable n)).
Definition pt_cmp_map     n := map_compo   _ (map_able _ (pt_spreadable n)).
Definition pt_foldr       n := foldr       _ (fold_able _ (pt_spreadable n)).
Definition pt_foldl       n := foldl       _ (fold_able _ (pt_spreadable n)).
Definition pt_size        n := size        _ (fold_able _ (pt_spreadable n)).
Definition pt_flatten     n := flatten     _ (fold_able _ (pt_spreadable n)).
(* Definition pt_show       n := show        _ (fold_able _ (pt_spreadable n)). *)
Definition pt_any         n := any         _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_any     n := dec_any     _ (any_all_able _ (pt_spreadable n)).
Definition pt_all         n := all         _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_all     n := dec_all     _ (any_all_able _ (pt_spreadable n)).
Definition pt_in_prop     n := in_prop     _ (any_all_able _ (pt_spreadable n)).
Definition pt_empty       n := empty       _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_in_prop n := dec_in_prop _ (any_all_able _ (pt_spreadable n)).
Definition pt_dec_eq      n := dec_eq      _ (eq_able _ (pt_spreadable n)).

From QuickChick Require Import QuickChick Tactics.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

Open Scope string.

Definition STuple : forall n, Printable (Tuple n). 
unfold Printable. induction n ;  intros; simpl.
+ exact X.
+ specialize (IHn A X).
exact showPair.
Defined.

Instance showLNDT_Tuplen {n : nat} {A : Type} `(sh : Show A) : Show (LNDT (Tuple n) A) :=
{|
  show  := @lndt_print (Tuple n) (STuple n) A sh
|}.


Close Scope string.
           
Definition tuple_n_gensized n := lndt_gen_sized (tuple_gensized n) nat arbitrarySized.

Sample (tuple_n_gensized 1 10).
Sample (tuple_n_gensized 2 10).
Sample (tuple_n_gensized 3 10).
