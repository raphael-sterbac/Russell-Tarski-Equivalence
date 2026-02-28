From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Require Import Stdlib.Program.Equality.
Require Import PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Arith.

Set Primitive Projections.

Definition lvl := nat.

Inductive ty : Type :=
    | Prod : ty -> ty -> ty
    | Decode : lvl -> term -> ty
    | U : lvl -> ty
with term : Type :=
    | var_term : nat -> term
    | Lambda : ty -> ty -> term -> term
    | App : ty -> ty -> term -> term -> term
    | cProd : lvl -> term -> term -> term
    | cU : lvl -> lvl -> term
    | cLift : lvl -> lvl -> term -> term.

Inductive russ_term : Type :=
    | r_var_term : nat -> russ_term
    | r_Prod : russ_term -> russ_term -> russ_term
    | r_U : lvl -> russ_term
    | r_Lambda : russ_term -> russ_term -> russ_term -> russ_term
    | r_App : russ_term -> russ_term -> russ_term -> russ_term -> russ_term.


(* ----- Substitutions ----- *)
Axiom subst_ty : term -> ty -> ty.
Axiom weak_ty : ty -> ty.

Axiom subst_term : term -> term -> term.
Axiom weak_term : term -> term.

Axiom r_subst_term : russ_term -> russ_term -> russ_term.
Axiom r_weak_term : russ_term -> russ_term.

(* ----- Contexts ----- *)

Definition ctx := list ty.

Notation "'ε'" := (@nil ty).
Notation " Γ ,, A " := (@cons ty A Γ) (at level 20, A at next level).


(* ----- Shortands for products and sum types ----- *)

Inductive prod (A B : Type) : Type := | pair : A -> B -> prod A B.

Notation "x × y" := (prod x y) (at level 80, right associativity).

Inductive sigT {A : Type} (P : A -> Type) : Type :=
| existT (projT1 : A) (projT2 : P projT1) : sigT P.

Definition projT1 {A P} (x : @sigT A P) : A := let '(existT _ a _) := x in a.
Definition projT2 {A P} (x : @sigT A P) : P (projT1 x) := let '(existT _ _ p) := x in p.

Inductive sum (A : Type) (B : Type) : Type :=
| inj1 (a : A) : sum A B | inj2 (b:B) : sum A B.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
(at level 200, x binder, right associativity,
format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
: type_scope.
