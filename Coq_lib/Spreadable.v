(** * Elements that can be spread for a certain TT F to LNDT F *)

Require Import Nat Coq.Lists.List.

(** ** Type Transformers *)
Definition TT := Type -> Type.

(** ** Mapable type constructors *)
Definition Map (F : TT) : Type :=
  forall A B  : Type, (A -> B) -> (F A -> F B).

(** ** Properties of Mapables : congruence and composition *)
Definition MapCongruence {F : TT} (map : Map F) : Type :=
  forall (A B : Type) (f : A -> B) (g : A -> B) (x : F A),
    (forall x, f x = g x) -> map A B f x = map A B g x.

Definition MapComposition {F : TT} (map : Map F) : Type :=
  forall (A B C : Type) (f : A -> B) (g : B -> C) x,
  map A C (fun x => g (f x)) x = map B C g ((map A B f) x).

Record MapAble (F : TT) : Type := mkMap
  { map        : Map F
  ; map_congru : MapCongruence  map
  ; map_compo  : MapComposition map }.

(** ** Foldable type constructors *)
Definition Fold (F : TT) : Type :=
  forall (A B : Type), (B -> A -> B) -> B -> F A -> B.

Definition flip {A B C : Type} f (a : A) (b : B) : C := f b a.

Record FoldAble (F : Type -> Type) : Type := mkFold
  { foldr   : Fold F ;
    foldl   : Fold F ;
    size    : forall (A : Type), F A -> nat
      := fun A => foldl _ _ (fun x y => succ x) 0 ;
    flatten : forall (A : Type), F A -> list A
      := fun A => foldl _ _ (flip cons) nil
    (* TODO show *)
  }.

(** ** A transformation of predicate over a type constructor
       (used later for Any and All) *)
Definition TransPred (F : TT) : Type :=
  forall (A : Type), (A -> Prop) -> ((F A) -> Prop).

(** ** The preservation of decidability through TransPred *)
(* TODO Je n'ai pas trouvé "Dec" dans la bibliothèque standard. *)
Definition Dec (A:Type) (P:A -> Prop) :=
  forall (x:A), {P x} + {~ (P x)}.

Definition TransDec {F : TT} (TransPF : TransPred F) : Type :=
  forall (A : Type) (P : A -> Prop), Dec A P -> Dec (F A) (TransPF _ P).

(* TODO Correct ? *)
Definition Decidable {A B : Type} (f : A -> B -> Prop) : Type :=
  forall (x:A) (y:B), {f x y} + {~(f x y)}.

Record AnyAllAble (F : TT) : Type := mkAnyAll
  { any     : TransPred F ;
    dec_any : TransDec any ;
    all     : TransPred F ;
    dec_all : TransDec all ;

    in_prop : forall (A : Type), A -> F A -> Prop
      := fun A x => any A (fun y => x = y ) ;
    empty : forall (A : Type), F A -> Prop
      := fun _ l => forall x, ~ in_prop _ x l ;
    dec_in_prop : forall (A : Type),
      Decidable eq -> Decidable (in_prop A)
      := fun A dec_equiv x y => dec_any A _ (dec_equiv x) y
  }.

(** ** Type constructors that preserve decidability of equality *)
Definition DecEq (F : TT) : Type := forall (A: Type),
  @Decidable A A eq ->
  @Decidable (F A) (F A) eq.

Record EqAble (F : TT) : Type := mkEq
  { dec_eq : DecEq F }.

(** ** All spread-able properties in a single record *)
Record SpreadAble (F : TT) : Type := mkSpread
  { fold_able    : FoldAble F ;
    map_able     : MapAble F ;
    any_all_able : AnyAllAble F ;
    eq_able      : EqAble F ;
  }.
  
  (** For random generation and property based testing*)

From QuickChick Require Import QuickChick Tactics.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

Definition Gensized (F : TT)  : Type := forall ( A : Type ), (nat -> G A) ->  nat -> G (F A).

Open Scope string.

Definition Printable (F : TT) := forall ( A : Type ), `(Show A)  ->  `(Show (F A)) .

Close Scope string.
