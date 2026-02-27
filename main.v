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

(* ----- Rules ----- *)

Reserved Notation "[ |- Γ ]"  (at level 0, Γ at level 50).
Reserved Notation "[ Γ |- t : A ]" (at level 0, Γ, t, A at level 50).
Reserved Notation "[ Γ |- A = B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |- t = u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |- A ]"  (at level 0, Γ, A at level 50).

Inductive WfContextDecl : ctx -> Type :=
    | connil : [ |- ε ]
    | concons {Γ A} : 
        [ |- Γ ] -> 
        [ Γ |- A ] -> 
        [ |-  Γ ,, A]
(* Type well-formation *)
with WfTypeDecl  : ctx -> ty -> Type :=
    | wfTypeU {Γ n} : 
        [ |- Γ ] -> 
        [ Γ |- U n ] 
    | wfTypeProd {Γ} {A B} : 
        [ Γ |- A ] -> 
        [Γ ,, A |- B ] -> 
        [ Γ |- Prod A B ]
    | wfTypeDecode {Γ}  {a n} :
        [Γ |- a : U n] ->
        [Γ |- Decode n a]
(** **** Typing *)
with TypingDecl : ctx -> term -> ty -> Type :=
     | wfVar0 {Γ} {A} :
        [ Γ |- A ] ->
        [ Γ,, A|- var_term 0 : (weak_ty A) ]
    | wfVarN {Γ} {n A B} :
        [Γ |- A] ->
        [Γ |- var_term n : B] ->
        [Γ ,, A |- (var_term (n+1)) : (weak_ty B)]
    
    (* | weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | wfTermcProd {Γ} {a b l} :
        [Γ |- a : U l] ->
        [Γ |- Decode l a] ->
        [Γ ,, Decode l a |- b : U l] ->
        [Γ |- cProd l a b : U l]
    | wfTermcUniv {Γ} (l : lvl) (m:lvl) :
        [   |- Γ] ->
        (m<l) ->
        [Γ |- cU m l : U l] 
    | wfTermcLift {Γ} {l m a} :
        [Γ |- a : U m] ->
        (m<l) ->
        [Γ |- cLift m l a : U l]
    | wfTermLambda {Γ} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, A |- t : B ] -> 
        [ Γ |- Lambda A B t : Prod A B]
    | wfTermApp {Γ} {f a A B} :
        [ Γ |- f : Prod A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- App A B f a : subst_ty a B ]
    | wfTermConv {Γ} {t A B} :
        [ Γ |- t : A ] -> 
        [ Γ |- A = B ] -> 
        [ Γ |- t : B ]
(* Conversion of types *)
with ConvTypeDecl : ctx -> ty -> ty  -> Type :=  
    | TypePiCong {Γ} {A B C D} :
        [ Γ |- A] ->
        [ Γ |- A = B] ->
        [ Γ ,, A |- C = D] ->
        [ Γ |- Prod A C = Prod B D]
    | TypeDecodeCong {Γ n a b} :
        [Γ |- a = b : U n] ->
        [Γ |- Decode n a = Decode n b]
    | TypeDecodeConv {Γ} (n: lvl) (m:lvl) :
        [  |- Γ ] ->
        (n< m) ->
        [Γ |- U n = Decode m (cU n m)]
    | TypeDecodeLiftConv {Γ} (n: lvl) (m:lvl) (u:term) :
        [Γ |- u: U m] ->
        (m < n) ->
        [Γ |- Decode m u = Decode n (cLift m n u)]
    | TypeDecodeProdConv {Γ a b n}:
        [Γ |- a: U n] ->
        [Γ,, Decode n a |- b :U n ] ->
        [Γ |- Decode n (cProd n a b) = Prod (Decode n a) (Decode n b)]
    | TypeRefl {Γ} {A} : 
        [ Γ |- A ] ->
        [ Γ |- A = A]
    | TypeTrans {Γ} {A B C} :
        [ Γ |- A = B] ->
        [ Γ |- B = C] ->
        [ Γ |- A = C]
    | TypeSym {Γ} {A B} :
        [ Γ |- A = B ] ->
        [ Γ |- B = A ]
(* Conversion of terms *)
with ConvTermDecl : ctx -> term -> term -> ty -> Type :=
    | TermBRed {Γ} {a t A B} :
            [ Γ |- A ] ->
            [ Γ ,, A |- t : B ] ->
            [ Γ |- a : A ] ->
            [ Γ |- App A B (Lambda A B t) a = (subst_term a t) : subst_ty a B ]
    | TermPiCong {Γ} {A B C D n} :
        [ Γ |- A : U n] ->
        [ Γ |- A = B : U n ] ->
        [ Γ ,, Decode n A |- C = D : U n ] ->
        [ Γ |- cProd n A C = cProd n B D : U n ]
    | TermAppCong {Γ} {a b f g A B A' B'} :
        [ Γ |- A = A'] ->
        [ Γ,,A |- B = B'] ->
        [ Γ |- f = g : Prod A B ] ->
        [ Γ |- a = b : A ] ->
        [ Γ |- App A B f a = App A' B' g b : subst_ty a B ]
    | TermLambdaCong {Γ} {t u A A' B' B} :
        [ Γ |- A ] ->
        [ Γ |- A = A' ] ->
        [ Γ,,A |- B = B' ] ->
        [ Γ,, A |- t = u : B ] ->
        [ Γ |- Lambda A B t = Lambda A' B' u : Prod A B ]
    | TermLiftingProdConv {Γ a b n p}:
        [Γ |- a: U p] ->
        [Γ,, Decode p a |- b : U p ] ->
        (p < n) ->
        [Γ |- cLift p n (cProd p a b) = cProd n (cLift p n a) (cLift p n b) : U n]
    | TermLiftingUnivConv {Γ p n m}:
        [   |- Γ] ->
        m < n ->
        n < p ->
        [Γ |- cLift n p (cU m n) =  cU m p : U p]
    | TermLiftingCumul {Γ a n l p}:
        [Γ |- a : U n] ->
        (n < p) ->
        (p < l) ->
        [Γ |- cLift p l (cLift n p a) = cLift n l a : U l]
    | TermLiftingCong {Γ a b n p}:
        [Γ |- a = b: U n] ->
        (n < p) ->
        [Γ |- cLift n p a = cLift n p b : U p]
    | TermFunEta {Γ} {f A B} :
        [ Γ |- f : Prod A B ] ->
        [ Γ |- Lambda A B (App (weak_ty A) (weak_ty B) (weak_term f) (var_term 0)) = f : Prod A B ]
    | TermRefl {Γ} {t A} :
        [ Γ |- t : A ] -> 
        [ Γ |- t = t : A ]
    | TermConv {Γ} {t t' A B} :
        [ Γ |- t = t': A ] ->
        [ Γ |- A = B ] ->
        [ Γ |- t = t': B ]
    | TermSym {Γ} {t t' A} :
        [ Γ |- t = t' : A ] ->
        [ Γ |- t' = t : A ]
    | TermTrans {Γ} {t t' t'' A} :
        [ Γ |- t = t' : A ] ->
        [ Γ |- t' = t'' : A ] ->
        [ Γ |- t = t'' : A ]
    
where "[ Γ |- T ]" := (WfTypeDecl Γ T)
and   "[ Γ |- t : T ]" := (TypingDecl Γ t T)
and   "[ Γ |- A = B ]" := (ConvTypeDecl Γ A B)
and   "[ Γ |- t = t' : T ]" := (ConvTermDecl Γ t t' T)
and   "[ |- Γ ]" := (WfContextDecl Γ).

(* ----- Russel Universes ----- *)

Definition russ_ctx := list russ_term.

Notation "'εr'" := (@nil russ_term).
Notation " Γ ,,r A " := (@cons russ_term A Γ) (at level 20, A at next level). 

Reserved Notation "[ |-r Γ ]"  (at level 0, Γ at level 50).
Reserved Notation "[ Γ |-r t : A ]" (at level 0, Γ, t, A at level 50).
Reserved Notation "[ Γ |-r A = B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-r t = u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-r A ]"  (at level 0, Γ, A at level 50).

Inductive Russ_WfContextDecl : russ_ctx -> Type :=
    | r_connil : [ |-r εr ]
    | r_concons {Γ A} : 
        [ |-r Γ ] -> 
        [ Γ |-r A ] -> 
        [ |-r Γ ,,r A]
(* Type well-formation *)
with Russ_WfTypeDecl  : russ_ctx -> russ_term -> Type :=
    | r_wfTypeU {Γ n} : 
        [ |-r Γ ] -> 
        [ Γ |-r r_U n ] 
    | r_wfTypeUniv {Γ n} {a} :
        [ Γ |-r a : r_U n]
        -> [ Γ |-r a ] 
(** **** Typing *)
with Russ_TypingDecl : russ_ctx -> russ_term -> russ_term -> Type :=
    | r_wfVar0 {Γ} {A} :
        [ Γ |-r A ] ->
        [ Γ,,r A |-r r_var_term 0 : (r_weak_term A) ]
    | r_wfVarN {Γ} {n A B} :
        [Γ |-r A] ->
        [Γ |-r r_var_term n : B] ->
        [Γ ,,r A |-r (r_var_term (n+1)) : (r_weak_term B)]

    (* | r_weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | r_wfTermLambda {Γ} {A B t} :
        [ Γ |-r A ] ->        
        [ Γ ,,r A |-r t : B ] -> 
        [ Γ |-r r_Lambda A B t : r_Prod A B]
    | r_wfTermApp {Γ} {f a A B} :
        [ Γ |-r f : r_Prod A B ] -> 
        [ Γ |-r a : A ] -> 
        [ Γ |-r r_App A B f a : r_subst_term a B ]
    | r_wfTermConv {Γ} {t A B} :
        [ Γ |-r t : A ] -> 
        [ Γ |-r A = B ] -> 
        [ Γ |-r t : B ]
    | r_wfTermProd {Γ n} {A B} : 
        [ Γ |-r A : r_U n] -> 
        [Γ ,,r A |-r B : r_U n] -> 
        [ Γ |-r r_Prod A B : r_U n]
    | r_wfTermUniv {Γ n m} :
        [ |-r Γ ] -> 
        (n<m) ->
        [ Γ |-r r_U n : r_U m ] 
    | r_wfTermCumul {Γ A n m}:
        (n < m) ->
        [Γ |-r A : r_U n] ->
        [Γ |-r A : r_U m]
(* Conversion of types *)
with Russ_ConvTypeDecl : russ_ctx -> russ_term -> russ_term  -> Type :=  
    | r_TypePiCong {Γ} {A B C D} :
        [ Γ |-r A] ->
        [ Γ |-r A = B] ->
        [ Γ ,,r A |-r C = D] ->
        [ Γ |-r r_Prod A C = r_Prod B D]
    | r_TypeRefl {Γ} {A} : 
        [ Γ |-r A ] ->
        [ Γ |-r A = A]
    | r_TypeSym {Γ} {A B} :
        [ Γ |-r A = B] ->
        [ Γ |-r B = A]
    | r_TypeTrans {Γ} {A B C} :
        [ Γ |-r A = B] ->
        [ Γ |-r B = C] ->
        [ Γ |-r A = C]
    | r_TypeUnivConv {Γ} {A B n} :
        [ Γ |-r  A = B : r_U n] ->
        [Γ |-r A = B]
(* Conversion of terms *)
with Russ_ConvTermDecl : russ_ctx -> russ_term -> russ_term -> russ_term -> Type :=
    | r_TermBRed {Γ} {a t A B} :
            [ Γ |-r A ] ->
            [ Γ ,,r A |-r t : B ] ->
            [ Γ |-r a : A ] ->
            [ Γ |-r r_App A B (r_Lambda A B t) a = r_subst_term a t : r_subst_term a B ]
    | r_TermAppCong {Γ} {a b f g A B A' B'} :
        [ Γ |-r A = A'] ->
        [ Γ,,r A |-r B = B'] ->
        [ Γ |-r f = g : r_Prod A B ] ->
        [ Γ |-r a = b : A] ->
        [ Γ |-r r_App A B f a = r_App A' B' g b : r_subst_term a B ]
    | r_TermLambdaCong {Γ}  {t u A A' B' B} :
        [ Γ |-r A ] ->
        [ Γ |-r A = A' ] ->
        [ Γ,,r A |-r B = B' ] ->
        [ Γ,,r A |-r t = u : B ] ->
        [ Γ |-r r_Lambda A B t = r_Lambda A' B' u : r_Prod A B ]
    | r_TermPiCong {Γ} {A B C D n} :
        [ Γ |-r A : r_U n] ->
        [ Γ |-r A = B : r_U n] ->
        [ Γ ,,r A |-r C = D : r_U n] ->
        [ Γ |-r r_Prod A C = r_Prod B D : r_U n]
    | r_TermFunEta {Γ} {f A B} :
        [ Γ |-r f : r_Prod A B ] ->
        [ Γ |-r r_Lambda A B (r_App (r_weak_term A) (r_weak_term B) (r_weak_term f) (r_var_term 0)) = f : r_Prod A B ]
    | r_TermRefl {Γ} {t A} :
        [ Γ |-r t : A ] -> 
        [ Γ |-r t = t : A ]
    | r_ConvConv {Γ} {t t' A B} :
        [ Γ |-r t = t': A ] ->
        [ Γ |-r A = B ] ->
        [ Γ |-r t = t': B ]
    | r_TermSym {Γ} {t t' A} :
        [ Γ |-r t = t' : A ] ->
        [ Γ |-r t' = t : A ]
    | r_TermTrans {Γ} {t t' t'' A} :
        [ Γ |-r t = t' : A ] ->
        [ Γ |-r t' = t'' : A ] ->
        [ Γ |-r t = t'' : A ]
    | r_TermUnivCumul {Γ} {A B p n} :
        [ Γ |-r  A = B : r_U p ] ->
        p < n ->
        [ Γ |-r A = B : r_U n]
    
where "[ Γ |-r T ]" := (Russ_WfTypeDecl Γ T)
and   "[ Γ |-r t : T ]" := (Russ_TypingDecl Γ t T)
and   "[ Γ |-r A = B ]" := (Russ_ConvTypeDecl Γ A B)
and   "[ Γ |-r t = t' : T ]" := (Russ_ConvTermDecl Γ t t' T)
and   "[ |-r Γ ]" := (Russ_WfContextDecl Γ).


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


(* ----- Axioms ---- *)

Axiom substitution_lemma :
    forall {Γ A B a},
    [ Γ ,, A |- B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- subst_ty a B ].

Axiom substitution_lemma_term: forall {Γ A B a t},
    [ Γ ,, A |- t: B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- subst_term a t : subst_ty a B].

Axiom subst_cong: forall {Γ A B B' a a'},
    [ Γ ,, A |- B = B' ] ->
    [ Γ |- a = a' : A ] ->
    [ Γ |- subst_ty a B  = subst_ty a' B' ].

Axiom weak_lemma: forall {Γ A B},
    [ Γ |- A] ->
    [ Γ,,A |- weak_ty B ].

Axiom weak_cong: forall {Γ A B C},
    [Γ |- A = B] ->
    [Γ,, C |- weak_ty A = weak_ty B].

Axiom weak_term_lemma: forall {Γ a A B},
    [Γ |- a : A] ->
    [Γ,, B |- weak_term a : weak_ty A].

Axiom subst_var_0: forall {A},
    subst_ty (var_term 0) (weak_ty A) = A.

Axiom weak_ty_prod: forall {A B},
     Prod (weak_ty A) (weak_ty B) = weak_ty (Prod A B).

Axiom PiInj: forall {Γ A B A' B'},
    [Γ |- Prod A B = Prod A' B'] ->
    [Γ |- A = A'] × [Γ |- B = B'].

Axiom UInj: forall {Γ k l},
    [Γ |- U k = U l] ->
    k = l.

Axiom cohesion_prod_univ: forall {Γ t A B n},
    [Γ |- t : Prod A B] ->
    [Γ |- t : U n] ->
    False.

Axiom subject_red: forall {Γ a b A},
    [Γ |- a : A] ->
    [Γ |- a = b : A] ->
    [Γ |- b : A].

Axiom lift_same: forall {u Γ l},
    [Γ |- u : U l] ->
    [Γ |- u = cLift l l u : U l].
(*TODO :  Remplacer par une notation ? *)


(* ----- Essential lemmas -----*)


Lemma inv_wfcontext_wftype Γ A:
    [Γ |- A] -> [Γ |- A] × [ |- Γ]
with  inv_wfcontext_typing Γ a A:
    [Γ |- a: A] -> [Γ |- a: A] × [ |- Γ].
Proof.
    + intros.
        constructor.
        auto.
        induction H.
        ++ auto.
        ++ auto.
        ++ apply inv_wfcontext_typing in t. destruct t. auto.
    + intros. constructor. auto. induction H.
        all : try(auto).
        ++ constructor. apply inv_wfcontext_wftype in w; destruct w. auto. auto.
        ++ constructor. auto. auto.
        ++ inversion IHTypingDecl. auto.
Qed. 


Definition subst_context (A B : ty) (Γ : ctx) (Δ : ctx) : ctx :=
  Δ ++ (B :: Γ).

Lemma context_conversion_ctx :
  (forall Γ, [ |- Γ ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ |- subst_context A B Γ' Δ ])
with context_conversion_ty :
  (forall Γ T, [ Γ |- T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- T ])
with context_conversion_term :
  (forall Γ t T, [ Γ |- t : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- t : T ])
with context_conversion_ty_eq :
  (forall Γ T1 T2, [ Γ |- T1 = T2 ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- T1 = T2 ])
with context_conversion_term_eq :
  (forall Γ t1 t2 T, [ Γ |- t1 = t2 : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- t1 = t2 : T ])
with type_defeq_inv Γ A B:
    [Γ |- A = B] ->
    [Γ |- A = B] × [Γ |- A] × [Γ |- B]
with typing_defeq_inv Γ a b A:
    [Γ |- a = b : A] ->
    [Γ |- a = b : A] × [Γ |- a : A] × [Γ |- b : A]
with wftype_typing_inv Γ a A:
    [Γ |- a : A] ->
    [Γ |- a : A] × [Γ |- A]
with wftype_hypothesis_inv Γ A B:
    [Γ,,A |- B] ->
    [Γ |- A] × [Γ,,A |- B]
with typing_hypothesis_inv Γ A b B:
    [Γ,,A |- b: B] ->
    [ |- Γ ] × [Γ |- A] × [Γ,,A |- b: B]
with conv_hypothesis_wftype {Γ C}:
    forall  A B,
    [Γ,,A |- C] ->
    [Γ |- A = B] ->
    [Γ,,B |- C]
with conv_hypothesis_typing {Γ C}:
    forall  A B a,
    [Γ,,A |- a : C] ->
    [Γ |- A = B] ->
    [Γ,,B |- a : C]
with  conv_hypothesis_type_eq {Γ A B C1 C2}:
    [Γ,,A |- C1 = C2] ->
    [Γ |- A = B] ->
    [Γ,,B |- C1 = C2]
with conv_hypothesis_term_eq {Γ A B a b C}:
    [Γ,,A |- a = b : C] ->
    [Γ |- A = B] ->
    [Γ,,B |- a = b : C].
Proof.

(* 1. context_conversion_ctx *)
- intros Γ H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv.
    + (* Nil *) destruct Δ0; inversion Heq.
    + (* Cons *) destruct Δ0.
      * 
        simpl in Heq. injection Heq. intros HeqG HeqA. subst.
        simpl. apply concons.
        ** auto.
        ** 
           apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]].
           auto.
      * 
        simpl in Heq. injection Heq. intros. subst.
        simpl. apply concons.
        ** apply IHWfContextDecl with (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.
        ** apply context_conversion_ty with (Γ := (Δ0 ++ Γ'0,, A0)) (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.

(* 2. context_conversion_ty *)
  - intros Γ T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* U *) apply wfTypeU. eapply context_conversion_ctx; eauto.
    + (* Prod *) apply wfTypeProd.
      * eapply IHWfTypeDecl1; eauto.
      * eapply IHWfTypeDecl2 with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* Decode *) apply wfTypeDecode. eapply context_conversion_term; eauto.

  (* 3. context_conversion_term *)
  - intros Γ t T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* wfVar0 *)
      rename A into T_declared.
      destruct Δ0.
      * 
        simpl. injection Heq. intros. subst.
        eapply wfTermConv. instantiate (1 := weak_ty B0).
        ** apply wfVar0. apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
        **
           apply TypeSym. 
           apply weak_cong.
           exact Hconv.
      * 
        simpl. injection Heq. intros. subst.
        apply wfVar0.
        eapply context_conversion_ty; eauto.

    + (* wfVarN *)
        rename A into T_head.
        destruct Δ0.
        * 
            simpl. injection Heq. intros. subst.
            apply wfVarN.
            **
            apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
            ** 
            exact H.
            
        * 
            simpl. injection Heq. intros. subst.
            apply wfVarN.
            ** eapply context_conversion_ty; eauto.
            ** eapply IHTypingDecl with (Δ := Δ0); auto.

    + (* cProd *) apply wfTermcProd.
      * eapply IHTypingDecl1; eauto.
      * eauto.
      * eapply IHTypingDecl2 with (Δ := Δ0 ,, Decode l a); eauto. simpl. reflexivity.
    + (* cUniv *) apply wfTermcUniv; auto. eapply context_conversion_ctx; eauto.
    + (* cLift *) apply wfTermcLift; auto.
    + (* Lambda *) apply wfTermLambda.
      * eapply context_conversion_ty; eauto.
      * eapply IHTypingDecl with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* App *) eapply wfTermApp.
      * eapply IHTypingDecl1; eauto.
      * eapply IHTypingDecl2; eauto.
    + (* Conv *) eapply wfTermConv.
      * eapply IHTypingDecl; eauto.
      * eapply context_conversion_ty_eq; eauto.

  (* 4. context_conversion_ty_eq *)
  - intros Γ T1 T2 H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* PiCong *) apply TypePiCong.
      * eapply context_conversion_ty; eauto.
      * eapply IHConvTypeDecl1; eauto.
      * eapply IHConvTypeDecl2 with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* DecodeCong *) apply TypeDecodeCong. eapply context_conversion_term_eq; eauto.
    + (* DecodeConv *) apply TypeDecodeConv. eapply context_conversion_ctx; eauto. auto.
    + (* DecodeLift *) apply TypeDecodeLiftConv; auto. eapply context_conversion_term; eauto.
    + (* DecodeProd *) apply TypeDecodeProdConv.
       * eapply context_conversion_term; eauto.
       * eapply context_conversion_term with (Δ := Δ0 ,, Decode n a); eauto. simpl. reflexivity.
    + (* Refl *) apply TypeRefl. eapply context_conversion_ty; eauto.
    + (* Trans *) eapply TypeTrans; eauto.
    + (* Sym *) apply TypeSym; eauto.

  (* 5. context_conversion_term_eq *)
  - intros Γ t1 t2 T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* BRed *) eapply TermBRed.
      * eapply context_conversion_ty; eauto.
      * eapply context_conversion_term with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
      * eapply context_conversion_term; eauto.
    + (* PiCong *) apply TermPiCong.
      * eapply context_conversion_term; eauto.
      * specialize (IHConvTermDecl1 Γ'0 A0 B0 Δ0 eq_refl Hconv). auto. 
      * specialize (IHConvTermDecl2 Γ'0 A0 B0 (Δ0,, Decode n A) eq_refl Hconv). auto.
    + (* AppCong *) eapply TermAppCong.
    
      * eapply context_conversion_ty_eq; eauto.
      * eapply context_conversion_ty_eq with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
      * eapply IHConvTermDecl1; eauto.
      * eapply IHConvTermDecl2; eauto.
    + (* LambdaCong *) apply TermLambdaCong.
       * eapply context_conversion_ty; eauto.
       * eapply context_conversion_ty_eq; eauto.
       * eapply context_conversion_ty_eq with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
       * eapply IHConvTermDecl with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* LiftingProd *) apply TermLiftingProdConv; auto.
       * eapply context_conversion_term; eauto.
       * eapply context_conversion_term with (Δ := Δ0 ,, Decode p a); eauto. simpl. reflexivity.
    + (* LiftingUniv *) apply TermLiftingUnivConv; auto. eapply context_conversion_ctx; eauto.
    + (* LiftingCumul *) apply TermLiftingCumul; auto. eapply context_conversion_term; eauto.
    + (* LiftingCong *) apply TermLiftingCong; auto.
    + (* FunEta *) apply TermFunEta. eapply context_conversion_term; eauto.
    + (* Refl *) apply TermRefl. eapply context_conversion_term; eauto.
    + (* Conv *) eapply TermConv.
       * eapply IHConvTermDecl; eauto.
       * eapply context_conversion_ty_eq; eauto.
    + (* Sym *) apply TermSym; eauto.
    + (* Trans *) eapply TermTrans; eauto.

  (* 6. type_defeq_inv *)
  - intros. split.
    + auto.
    +
      *
        induction H.
        ** destruct IHConvTypeDecl1. destruct IHConvTypeDecl2. constructor. constructor. auto.
             auto. constructor. auto. apply conv_hypothesis_wftype with (A:=A). auto. auto.
        ** constructor. apply wfTypeDecode. apply typing_defeq_inv in c. destruct c as [_ [? ?]].
             auto. apply wfTypeDecode. apply typing_defeq_inv in c. destruct c as [_ [? ?]]. auto. 
        ** constructor. apply wfTypeU. eauto. apply wfTypeDecode. apply wfTermcUniv. auto. auto.
        ** constructor. apply wfTypeDecode. eauto. apply wfTypeDecode. eauto. apply wfTermcLift. auto. auto. 
        ** constructor. apply wfTypeDecode. apply wfTermcProd; auto. apply wfTypeDecode. auto. constructor.
             eapply typing_hypothesis_inv in t0. destruct t0 as [? []]. auto. apply wfTypeDecode in t0. auto.
        ** constructor. auto. auto.
        ** destruct IHConvTypeDecl1. destruct IHConvTypeDecl2. constructor. auto. auto.
        ** destruct IHConvTypeDecl. constructor. auto. auto.

  (* 7. typing_defeq_inv *)
  - intros. split.
    + auto.
    + split.
      * 
        induction H.
        ** apply wfTermApp. apply wfTermLambda; auto. auto.
        ** apply wfTermcProd. auto. apply wfTypeDecode. auto. auto.
        ** apply wfTermApp. auto. auto.
        ** apply wfTermLambda. auto. auto.
        ** apply wfTermcLift. apply wfTermcProd. auto. auto. apply typing_hypothesis_inv in t0.
             destruct t0 as [? []]. auto. auto. auto. 
        ** apply wfTermcLift. apply wfTermcUniv. auto. auto. auto.
        ** apply wfTermcLift. apply wfTermcLift. auto. auto. auto.
        ** apply wfTermcLift. auto. auto.
        ** apply wftype_typing_inv in t. destruct t. inversion w. apply wfTermLambda.
               *** auto. 
               *** eapply wfTermConv.
                    **** eapply wfTermApp.
                          ***** rewrite weak_ty_prod. apply weak_term_lemma. auto.
                          ***** apply wfVar0. auto. 
                    **** rewrite subst_var_0. apply TypeRefl. auto.
            
        ** auto.
        ** eapply wfTermConv. instantiate (1 := A). apply IHConvTermDecl. auto.
        ** eapply subject_red. instantiate (1:=t). auto. auto.
        ** apply IHConvTermDecl1.
      *
        induction H.
        ** (* BRed: subst_term a t *)
           eapply substitution_lemma_term. eauto. auto.
        ** (* PiCong *)
           apply wfTermcProd.
           *** auto.
           ***  apply wfTypeDecode. auto.
           ***  eapply conv_hypothesis_typing. instantiate (1:=Decode n A).
           auto. apply TypeDecodeCong. auto.
        ** (* AppCong *)
           eapply wfTermConv. instantiate (1 := subst_ty b B').
           *** apply type_defeq_inv in c. destruct c as [? []]. apply wfTermApp. eapply wfTermConv.
                instantiate (1:= Prod A B). auto. constructor. 
                auto. auto. auto. eapply wfTermConv. instantiate (1:= A). auto. auto.
           *** eapply subst_cong. instantiate (1:=A). auto. auto using TypeSym. auto using TermSym.
        ** (* LambdaCong *)
           eapply wfTermConv. instantiate (1:=Prod A' B'). apply wfTermLambda.
           *** apply type_defeq_inv in c. destruct c as [? []]. auto.
           *** eapply conv_hypothesis_typing. instantiate (1:=A). eapply wfTermConv. instantiate (1:= B). all: auto.
           *** apply TypePiCong. apply type_defeq_inv in c. destruct c as [? []]. auto. auto using TypeSym.
                eapply conv_hypothesis_type_eq. instantiate (1:= A). auto using TypeSym. auto.
        ** (* LiftingProd *)
           apply wfTermcProd.
           *** apply wfTermcLift. auto. auto.
           *** apply wfTypeDecode. apply wfTermcLift. auto. auto.
           *** constructor. eapply conv_hypothesis_typing. instantiate (1:= Decode p a). auto.
                eapply TypeDecodeLiftConv. all: auto.
        ** (* LiftingUniv *)
           apply wfTermcUniv. auto. lia.
        ** (* LiftingCumul *)
           apply wfTermcLift. auto. lia.
        ** (* LiftingCong *)
           apply wfTermcLift. auto. auto.
        ** (* FunEta *)
           auto.
        ** auto.
        ** eapply wfTermConv. instantiate (1:=A). auto. auto.
        ** eapply subject_red. instantiate (1:=t'). all: auto using TermSym.
        ** auto.

(* 8. wftype_typing_inv *)
  - intros. split.
    + exact H.
    + induction H.
      * (* wfVar0 *)
        apply weak_lemma. assumption.
      * (* wfVarN *)
        apply weak_lemma. assumption.
      * (* cProd *)
        apply wfTypeU. apply inv_wfcontext_wftype in IHTypingDecl1. destruct IHTypingDecl1. auto.
      * (* cUniv *)
        apply wfTypeU. assumption.
      * (* cLift *)
        apply wfTypeU. apply inv_wfcontext_wftype in IHTypingDecl. destruct IHTypingDecl. auto.
      * (* Lambda *)
        apply wfTypeProd.
        ** assumption.
        ** assumption.
      * (* App *)
        inversion IHTypingDecl1. subst.
        eapply substitution_lemma.
        ** exact H5. 
        ** exact H0.
      * (* Conv *)
        apply type_defeq_inv in c. destruct c as [_ [_ HwfB]].
        exact HwfB.

(* 9. wftype_hypothesis_inv *)
  - intros. 
    remember (Γ ,, A) as Γ' in H.
    dependent induction H; intros; subst; try discriminate.
    
    (* Cas Cons : *)
    + inversion w; subst. constructor; auto. constructor. auto.
    
    (* Cas Prod *)
    + 
      split.
      *
        eapply IHWfTypeDecl1; reflexivity.
      * 
        apply wfTypeProd.
        ** auto.
        ** assumption.

    (* Cas Decode *)
    + split.
      * 
        eapply typing_hypothesis_inv in t. destruct t as [? []]. auto.
      * apply wfTypeDecode. assumption. 

  (* 10. typing_hypothesis_inv *)
  - intros. split.
    + apply inv_wfcontext_typing in H. inversion H. inversion H1. auto.
    + split.
      * 
        inversion H; subst.
        ** (* wfVar0 *)  assumption.
        ** (* wfVarN *)  assumption.
        ** (* cProd *) apply inv_wfcontext_typing in H. inversion H. inversion H4. auto.
        ** (* cUniv *) inversion H0; subst; assumption.
        ** (* cLift *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Lambda *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* App *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Conv *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
      * 
        exact H.

  (* 11. conv_hypothesis_wftype *)
  - intros A B Hwf Hconv.
    eapply context_conversion_ty with (Δ := ε).
    + simpl. exact Hwf.
    + reflexivity.
    + exact Hconv.

  (* 12. conv_hypothesis_typing *)
  - intros A B a Htyp Hconv.
    eapply context_conversion_term with (Δ := ε).
    + simpl. exact Htyp.
    + reflexivity.
    + exact Hconv.

  (* 13. conv_hypothesis_type_eq *)
  - intros Heq Hconv.
    eapply context_conversion_ty_eq with (Δ := ε).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.

  (* 14. conv_hypothesis_term_eq *)
  - intros  Heq Hconv.
    eapply context_conversion_term_eq with (Δ := ε).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.
Admitted.  (* TODO : Decreasing argument *)



(* ----- Inversion Lemmas ----- *)
Lemma prod_ty_inv Γ A B :
  [Γ |- Prod A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  inversion Hty . subst .
  - easy.
Qed.

Lemma decode_ty_inv Γ k t:
    [Γ |- Decode k t] ->
    [Γ |- t: U k].
Proof.
    intros Hty.
    inversion Hty.
    easy.
Qed.

Lemma lambda_inv u :
    forall Γ A B C,
    [Γ |- Lambda A B u : C] ->
    [Γ |- C = Prod A B] × [Γ,,A |- u : B].
Proof.
    intros. dependent induction H. 
    - constructor. apply TypeRefl. apply wfTypeProd. auto. apply wftype_typing_inv in H. destruct H. auto. auto.
    - constructor. eapply TypeTrans. instantiate (1:=A0). auto using TypeSym. eapply IHTypingDecl. instantiate (1:=u). auto.
        eapply IHTypingDecl. auto.  
Qed.

Lemma code_univ_inv_bis Γ k l A:
    [Γ |- cU k l : A] ->
    [Γ |- A = U l] × (k < l).
Proof.
    intros. dependent induction H.
    - constructor. apply TypeRefl. constructor. auto. auto.
    - constructor. eapply TypeTrans. instantiate (1:= A). auto using TypeSym. eapply IHTypingDecl. instantiate (1:=k). auto. eapply IHTypingDecl. auto.   
Qed.

Lemma code_univ_inv Γ k l n:
    [Γ |- cU k l : U n] ->
    l = n.
Proof.
    intros.
    apply code_univ_inv_bis in H. destruct H. apply UInj in c. auto.
Qed.


Lemma lift_inv_plus Γ k l A u:
    [Γ |- cLift k l u : A] ->
    ∑ n, [Γ |- A = U n] × l = n × k < l × [Γ |- u : U k].
Proof.
    intros. dependent induction H.
    - eexists l. constructor. apply TypeRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto. constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl k l u eq_refl). destruct IHTypingDecl as [? [? [? []]]]. eexists l. constructor. eapply TypeTrans. instantiate (1:=A).
        auto using TypeSym. rewrite e. auto. constructor. auto. constructor. auto. auto.
Qed.

Lemma lift_inv Γ k l n u:
    [Γ |- cLift k l u : U n] ->
    l = n × k < l × [Γ |- u : U k].
Proof.
    intros.
    apply lift_inv_plus in H. destruct H as [? [? [? []]]]. apply UInj in c. constructor. rewrite e. auto. constructor. auto. auto.
Qed.

Lemma app_inv Γ A B C u1 u2:
    [Γ |- App A B u1 u2 : C] ->
    [Γ |- C = subst_ty u2 B] ×  [Γ |- A] × [Γ,,A |- B] × [Γ |- u1 : Prod A B] × [Γ |- u2 : A].
Proof.
    intros. dependent induction H.
    - apply wftype_typing_inv in H. destruct H. assert (wbis:=w). apply prod_ty_inv in wbis. destruct wbis.
        constructor. apply TypeRefl. eapply substitution_lemma. instantiate (1:=A). auto. auto.
        constructor. auto. constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl A B u1 u2 eq_refl). destruct IHTypingDecl as [? [? [? []]]]. 
        constructor. apply TypeSym in c. apply TypeTrans with (1:= c). auto.
        constructor. auto. constructor. auto. constructor. auto. auto.   
Qed.

 Fixpoint iter_weak (n : nat) (A : ty) : ty :=
  match n with
  | 0 => A
  | S m => weak_ty (iter_weak m A)
  end.

Lemma var_inv :
  forall Γ t T, [Γ |- t : T] ->
  forall n Δ Γ' A,
  t = var_term n ->
  Γ = Δ ++ (A :: Γ') ->
  length Δ = n ->
  [Γ |- T = iter_weak (S n) A].
Proof.
  intros Γ t T H. intros n0 Δ0 Γ'0 A0 HeqTerm HeqCtx Hlen. subst. dependent induction H.

  (* Cas wfVar0 : var 0 *)
  -
    destruct Δ0. simpl in x; try discriminate.
    simpl in x0. injection x0. intros; subst.
    simpl.
    apply TypeRefl. 
    apply weak_lemma. assumption.
    simpl in x. contradict x. auto.

  (* Cas wfVarN : var (n+1) *)
  - destruct Δ0.
        * simpl in x. contradict x. lia.
        * simpl in x. simpl in x0. inversion x0. simpl. 
        specialize (IHTypingDecl Δ0 Γ'0 A0). simpl in IHTypingDecl. rewrite H2 in IHTypingDecl. specialize (IHTypingDecl JMeq_refl).
        eapply weak_cong in IHTypingDecl. exact IHTypingDecl. simpl.  assert (n = length Δ0) by lia. rewrite H0. auto.

  (* Cas Conv : *)
  - 
    eapply TypeTrans.
    + apply TypeSym. exact c.
    + eapply IHTypingDecl; eauto.
Qed.

Lemma variable_zero_inv Γ A:
    [Γ |- var_term 0 : A] ->
    ∑ Γ' B, [Γ |- A = weak_ty B] × (Γ = Γ' ,, B) × [Γ' |- B].
Proof.
    intros H.
    
    assert (Hstruct: ∑ Γ' B, Γ = Γ' ,, B).
    {
      remember (var_term 0) as t.
      induction H; try discriminate.
      -  exists Γ, A. reflexivity.
      -  inversion Heqt. contradict Heqt. lia.
      -  apply IHTypingDecl. assumption.
    }
    
    destruct Hstruct as [Γ' [B HeqΓ]].
    
    exists Γ', B.
    
    split.
    
    - subst Γ.
      apply var_inv with (n:=0) (Δ:=ε) (Γ':=Γ') (A:=B) in H.
      + simpl in H. exact H.
      + reflexivity.
      + simpl. reflexivity.
      + reflexivity.

    - split.
      + exact HeqΓ.
      
      + subst Γ.
        apply inv_wfcontext_typing in H.
        destruct H as [_ HwfΓ].
        inversion HwfΓ; subst.
        exact H2.
Qed.

Lemma variable_non_zero_inv Γ A n :
    [Γ |- var_term (S n) : A] ->
    ∑ Γ' T_head B, 
      (Γ = Γ' ,, T_head) × 
      [Γ' |- var_term n : B] × 
      [Γ |- A = weak_ty B].
Proof.
    intros H.
    remember (var_term (S n)) as t.
    induction H; try discriminate.

    (* 2. Cas wfVarN : *)
    - injection Heqt. intro Heqn. subst.
      exists Γ, A, B.
      
      split.
      + 
        reflexivity.
      
      + split. 
        ++ 
            assert (n0 = n) by lia. rewrite H0 in H. exact H.
        ++
           apply TypeRefl.
           apply weak_lemma.
           exact w. 

    (* 3. Cas TermConv : *)
    -
      specialize (IHTypingDecl Heqt).
      destruct IHTypingDecl as [Γ' [T_head [B_origin [HeqΓ [Htyp HeqType]]]]].
      
      exists Γ', T_head, B_origin.
      split.
      + exact HeqΓ.
      + split.
        ++ exact Htyp.
        ++
           eapply TypeTrans.
           * apply TypeSym. exact c.
           * exact HeqType.
Qed.

Lemma var_ctx_inv Γ A0 A1 n :
    [Γ |- var_term n : A0] ->
    [Γ |- var_term n : A1] ->
    [Γ |- A0 = A1].
Proof.
  revert Γ A0 A1.
  induction n; intros Γ A0 A1 H1 H2.

  (* 1. Cas n = 0 *)
  - apply variable_zero_inv in H1.
    destruct H1 as [Γ1 [B1 [HeqA1 [HeqG1 Hwf1]]]].
    apply variable_zero_inv in H2.
    destruct H2 as [Γ2 [B2 [HeqA2 [HeqG2 Hwf2]]]].
    
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqB HeqCtx. subst.
    
    eapply TypeTrans.
    + exact HeqA1.
    + apply TypeSym. exact HeqA2.

  (* 2. Cas n = S n *)
  - apply variable_non_zero_inv in H1.
    destruct H1 as [Γ1 [T1 [B1 [HeqG1 [Hvar1 HeqA1]]]]].
    apply variable_non_zero_inv in H2.
    destruct H2 as [Γ2 [T2 [B2 [HeqG2 [Hvar2 HeqA2]]]]].
    
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqHead HeqTail. subst.
    
    assert (Hconv : [Γ1 |- B1 = B2]).
    { apply IHn; assumption. }
    
    eapply TypeTrans.
    + exact HeqA1. 
    + eapply TypeTrans.
      * 
        eapply weak_cong. exact Hconv. 
      * 
        apply TypeSym. exact HeqA2.
Qed.

Lemma code_prod_inv_plus Γ l A a b:
    [Γ |- cProd l a b : A] ->
    ∑ n, [Γ |- A = U n] × l = n × [Γ |- a : U l] × [Γ,,(Decode l a) |- b : U l].
Proof.
    intros. dependent induction H.
    - eexists l. constructor. apply TypeRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto.
        constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl l a b eq_refl). destruct IHTypingDecl as [? [? [? []]]]. eexists l. constructor.
        eapply TypeTrans. instantiate (1:= A). auto using TypeSym. rewrite e. auto. constructor. auto. constructor. auto. auto.
Qed.


Lemma code_prod_inv Γ l n a b:
    [Γ |- cProd l a b : U n] ->
    l = n × [Γ |- a : U l] × [Γ,,(Decode l a) |- b : U l].
Proof.
    intros. apply code_prod_inv_plus in H. destruct H as [? [? [? []]]]. apply UInj in c. constructor. rewrite c. auto.
    constructor. auto. auto.
Qed.


(* ----- Fonctions d'effacement ----*)
Fixpoint erase_term (t: term) : russ_term :=
    match t with
        | var_term n => r_var_term n 
        | Lambda A B b => r_Lambda (erase_ty A) (erase_ty B) (erase_term b)
        | App A B c a => r_App (erase_ty A) (erase_ty B) (erase_term c) (erase_term a)
        | cU n m => r_U n
        | cProd l a b => r_Prod (erase_term a) (erase_term b)
        | cLift n m t => (erase_term t)
    end
with erase_ty (A: ty): russ_term :=
    match A with
        | Prod A B => r_Prod (erase_ty A) (erase_ty B)
        | U n => r_U n
        | Decode n t => (erase_term t)
    end.

Fixpoint erase_context (Γ : ctx): russ_ctx := 
    match Γ with
    | nil => nil
    | cons a Γ' => cons (erase_ty a) (erase_context Γ')
    end.

Lemma product_wf_ty {Γ A B} : [Γ |-r A] -> [ Γ ,,r A |-r B ] -> [Γ |-r r_Prod A B].
Proof.
    intros. inversion H. inversion H0. symmetry in H3.
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermUniv.
            auto. lia. eapply r_wfTermUniv. constructor. auto. rewrite H3 in H. auto. lia. 
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermUniv.
            auto. lia. eapply r_wfTermCumul. instantiate (1:=n0). lia. symmetry in H3. rewrite H3 in H4. auto.
        inversion H0. eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermCumul.
            instantiate (1:=n). lia. auto. eapply r_wfTermUniv. auto. lia.
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermCumul.
            instantiate (1:=n). lia. auto. eapply r_wfTermCumul. instantiate (1:=n0). lia. auto.    
Qed.

(* ----- Erasure of substitutions lemma, as axioms ----- *)

Axiom defeq_erase_weak_ty: forall {A}, r_weak_term (erase_ty A) = erase_ty (weak_ty A).
Axiom defeq_erase_weak_term: forall {A}, r_weak_term (erase_term A) = erase_term (weak_term A).
Axiom defeq_erase_subst_ty: forall {a A}, r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A).
Axiom defeq_erase_subst_term: forall {a t}, r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t).
Axiom erase_weak_ty: forall {Γ A}, [Γ |-r r_weak_term (erase_ty A) = erase_ty (weak_ty A) ].
Axiom erase_subst_ty: forall {Γ a A}, [Γ |-r r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A) ].
Axiom erase_subst_term: forall {Γ a t B}, [Γ |-r r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t) : B].

Axiom defeq_weak_var: forall {n}, r_weak_term (r_var_term n) = r_var_term (n + 1). 


(* ----- Lemme de correction de l'effacement ----- *)

(* 1. On régénère les schémas proprement *)
Scheme wf_ctx_rect := Induction for WfContextDecl Sort Type
  with wf_ty_rect := Induction for WfTypeDecl Sort Type
  with typing_rect := Induction for TypingDecl Sort Type
  with conv_ty_rect := Induction for ConvTypeDecl Sort Type
  with conv_term_rect := Induction for ConvTermDecl Sort Type.

Combined Scheme mut_ind_erasure_rect from 
  wf_ctx_rect, wf_ty_rect, typing_rect, conv_ty_rect, conv_term_rect.

(* 2. Le Théorème *)
Theorem erasure_correction_mutual :
  (forall (Γ : ctx) (H : [ |- Γ ]), [ |-r erase_context Γ]) *
  ((forall (Γ : ctx) (A : ty) (H : [Γ |- A]), [(erase_context Γ) |-r (erase_ty A)]) *
  ((forall (Γ : ctx) (a : term) (A : ty) (H : [Γ |- a : A]), [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]) *
  ((forall (Γ : ctx) (A B : ty) (H : [Γ |- A = B]), [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]) *
  (forall (Γ : ctx) (a b : term) (A : ty) (H : [Γ |- a = b : A]), [(erase_context Γ) |-r (erase_term a) = (erase_term b) : (erase_ty A)])))).
Proof.
  apply mut_ind_erasure_rect.

  (* --- 1. WfContextDecl --- *)
  - simpl. constructor.
  - simpl. intros. apply r_concons; assumption.

  (* --- 2. WfTypeDecl--- *)
  - intros. simpl. constructor. assumption.
  - intros. simpl. apply product_wf_ty; assumption.
  - intros. simpl. eapply r_wfTypeUniv. simpl in H. exact H.

  (* --- 3. TypingDecl --- *)
  - intros. simpl. eapply r_wfTermConv. apply r_wfVar0. assumption. apply erase_weak_ty.
  - intros. simpl. eapply r_wfTermConv. eapply r_wfVarN. assumption. simpl in H0. exact H0. apply erase_weak_ty.
  - intros. simpl. constructor; assumption.
  - intros. simpl. constructor. assumption. assumption.
  - intros. simpl. apply r_wfTermCumul with (1:=l0). assumption.
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_wfTermConv. apply r_wfTermApp. assumption. assumption. apply erase_subst_ty.
  - intros. simpl. eapply r_wfTermConv. exact H. assumption.

  (* --- 4. ConvTypeDecl --- *)
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_TypeUnivConv. exact H.
  - intros. simpl. eapply r_TypeUnivConv. apply r_TermRefl. eapply r_wfTermUniv. assumption. exact l.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. simpl in H. exact H.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. eapply r_wfTermProd. simpl in H. exact H. simpl in H0. exact H0.
  - intros. simpl. apply r_TypeRefl. assumption.
  - intros. simpl. eapply r_TypeTrans; eauto.
  - intros. simpl. apply r_TypeSym. assumption.

  (* --- 5. ConvTermDecl --- *)
  - intros. simpl. eapply r_ConvConv. rewrite <- defeq_erase_subst_term. eapply r_TermBRed. auto. simpl in H0; auto. auto. apply erase_subst_ty.
  - intros. simpl. apply r_TermPiCong.  simpl in H; exact H.  simpl in H0; exact H0. simpl in H1; exact H1.
  - intros. simpl. eapply r_ConvConv. apply r_TermAppCong; assumption. apply erase_subst_ty.
  - intros. simpl. apply r_TermLambdaCong; assumption.
  - intros. simpl. eapply r_TermUnivCumul. instantiate (1:=p). apply r_TermRefl. apply r_wfTermProd. all: auto.
  - intros. simpl. apply r_TermRefl. apply r_wfTermUniv. auto. lia. 
  - intros. simpl. apply r_TermRefl. eapply r_wfTermCumul. exact l1. eapply r_wfTermCumul. exact l0. simpl in H. exact H.
  - intros. simpl. eapply r_TermUnivCumul. simpl in H. exact H. auto.
  - intros. simpl. 
    rewrite <- defeq_erase_weak_term.  
    rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty.
    apply r_TermFunEta. assumption.
  - intros. simpl. apply r_TermRefl. assumption.
  - intros. simpl. eapply r_ConvConv; eauto.
  - intros. simpl. apply r_TermSym; assumption.
  - intros. simpl. eapply r_TermTrans; eauto.
Qed.

(* 1. Formation du contexte *)
Definition ctx_formation_to_russ {Γ} (H : [ |- Γ ]) := 
  (fst erasure_correction_mutual) Γ H.

(* 2. Bonne formation du type  *)
Definition erasure_correction_wf_ty {Γ A} (H : [Γ |- A]) := 
  (fst (snd erasure_correction_mutual)) Γ A H.

(* 3. Typage  *)
Definition erasure_correction_typing {Γ a A} (H : [Γ |- a : A]) := 
  (fst (snd (snd erasure_correction_mutual))) Γ a A H.

(* 4. Conversion de type  *)
Definition erasure_correction_conversion {Γ A B} (H : [Γ |- A = B]) := 
  (fst (snd (snd (snd erasure_correction_mutual)))) Γ A B H.

(* 5. Conversion de terme *)
Definition erasure_correction_conv_typing {Γ a b A} (H : [Γ |- a = b : A]) := 
  (snd (snd (snd (snd erasure_correction_mutual)))) Γ a b A H.


(* ----- Lemmes utiles ----- *)


Lemma inf_right_max {k l}:
    l <= Nat.max k l.
Proof.
    lia.
Qed.

Lemma inf_left_max {k l}:
    k <= Nat.max k l.
Proof.
    lia.
Qed.

Lemma sup_max {k l n}:
    k < n ->
    l < n ->
    Nat.max k l < n.
Proof.
    intros. lia.
Qed.

Lemma sup_right_min {k l}:
    Nat.min k l <= l.
Proof.
    lia.
Qed.

Lemma sup_left_min {k l}:
    Nat.min k l <= k.
Proof.
    lia.
Qed.

Lemma inf_min {k l n}:
    n < k ->
    n < l ->
    n < Nat.min k l.
Proof.
    intros. lia.
Qed.

Lemma conv_lift_univ_min {Γ l l0 l1}:
    [ |- Γ] ->
    l < l0 ->
    l < l1 ->
    [Γ |- cLift (Nat.min l0 l1 ) l1 (cU l (Nat.min l0 l1)) = cU l l1 : U l1].
Proof.
    intros. destruct (lt_dec l0 l1) as [H_lt | H_ge].  
    - rewrite Nat.min_l. lia. apply TermLiftingUnivConv. all: auto.
    - rewrite Nat.min_r. lia. apply TermSym. apply lift_same. constructor. auto. auto.
Qed.

Lemma conv_lift_univ_min_comm {Γ l l0 l1}:
    [ |- Γ] ->
    l < l0 ->
    l < l1 ->
    [Γ |- cLift (Nat.min l1 l0 ) l1 (cU l (Nat.min l1 l0)) = cU l l1 : U l1].
Proof.
    intros. destruct (lt_dec l0 l1) as [H_lt | H_ge].  
    - rewrite Nat.min_r. lia. apply TermLiftingUnivConv. all: auto.
    - rewrite Nat.min_l. lia. apply TermSym. apply lift_same. constructor. auto. auto.
Qed.

Lemma conv_lift_cumul_max {Γ k l n0 u}:
    [Γ |- u : U l] ->
    n0 > k ->
    n0 > l ->
    [Γ |- cLift (Nat.max k l) n0 (cLift l (Nat.max k l) u) = cLift l n0 u : U n0].
Proof.
    intros. destruct (lt_dec l k) as [H_lt | H_ge].  
    - rewrite Nat.max_l. lia. apply TermLiftingCumul. auto. lia. auto.
    - rewrite Nat.max_r. lia. apply TermLiftingCong. apply TermSym. apply lift_same. auto. auto.
Qed.

Lemma conv_lift_cumul_max_comm {Γ k l n0 u}:
    [Γ |- u : U l] ->
    n0 > k ->
    n0 > l ->
    [Γ |- cLift (Nat.max l k) n0 (cLift l (Nat.max l k) u) = cLift l n0 u : U n0].
Proof.
     intros. destruct (lt_dec l k) as [H_lt | H_ge].  
    - rewrite Nat.max_r. lia. apply TermLiftingCumul. auto. lia. auto.
    - rewrite Nat.max_l. lia. apply TermLiftingCong. apply TermSym. apply lift_same. auto. auto.
Qed.

Lemma simplify_induction {Γ A0 A1 l0 l1 k v0 v1 u0 u1}:
    [Γ |- A0 = U l0] ->
    [Γ |- A1 = U l1] ->
    [Γ |- u0 = cLift k l0 v0 : A0] ->
    [Γ |- u1 = cLift k l1 v1 : A1] ->
    [Γ |- v0 = v1 : U k] ->
    [Γ |- A0 = A1] ->
    [Γ |- u0 = u1 : A0].
Proof.
    intros. apply TypeSym in H. apply TypeTrans with (1:=H) in H4. apply TypeSym in H0, H4. apply TypeTrans with (1:=H0) in H4. apply UInj in H4. subst.
    apply TypeSym in H. apply TypeTrans with (1:=H) in H0. apply TypeSym in H0. apply TermConv with (1:= H2) in H0.
    eapply TermLiftingCong in H3. eapply TermTrans. exact H1. eapply TermTrans. eapply TermConv. exact H3. auto using TypeSym. auto using TermSym.
    apply typing_defeq_inv in H0. destruct H0 as [? []]. apply lift_inv_plus in t0. destruct t0 as [? [? [? []]]]. auto. 
Qed.

Lemma simplify_induction_grouped {Γ A0 A1 u0 u1}:
    (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ) ->
    [Γ |- A0 = A1] ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. destruct H as [? [? [? [? [? [? [? [? []]]]]]]]]. constructor.
    apply simplify_induction with (1:=c) (2:=c0) (3:=c1) (4:=c2) (5:=c3) (6:=H0). auto.
Qed.

Lemma simplify_induction_bis {Γ A0 A1 u0 u1}:
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ) ->
    [Γ |- A0 = A1] ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. destruct H.
    - auto.
    - apply simplify_induction_grouped. auto. auto. 
Qed.

Lemma erase_decode_inv_univ t:
    forall Γ l n,
    [Γ |- Decode l t] ->
    r_U n = erase_term t ->
    [Γ |- U n = Decode l t].
Proof.
induction t.
    all: try (intros; simpl in H0; contradict H0; congruence).
    - intros. apply inv_wfcontext_wftype in H. destruct H.
        simpl in H0; apply decode_ty_inv in w. apply code_univ_inv_bis in w. destruct w. inversion H0. apply UInj in c. subst.
        apply TypeDecodeConv with (n := l) (m := l0) in w0. exact w0. auto.
    - intros. simpl in H0. apply decode_ty_inv in H. apply lift_inv in H. destruct H. rewrite e.
        eapply TypeTrans. instantiate (1 := Decode l t).
        + eapply IHt. apply wfTypeDecode. destruct p. auto. auto.
        + apply TypeDecodeLiftConv. destruct p. auto. destruct p. rewrite e in l2. auto.
Qed.

Lemma erase_decode_inv_prod t:
    forall Γ l A B,
    [Γ |- Decode l t] ->
    [Γ |- Prod A B] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    r_Prod (erase_ty A) (erase_ty B) = erase_term t ->
    [Γ |- Prod A B = Decode l t].
Proof.
induction t.
    all: try (intros; simpl in H3; contradict H3; congruence).
    - intros. eapply TypeTrans. instantiate (1:=Prod (Decode  l0 t1) (Decode l0 t2)).
        + inversion H0. simpl in H3. inversion H3. constructor. auto.
            ++ apply H1. auto. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. destruct p.
                constructor. rewrite e in t. auto. auto. 
            ++ apply H2. auto. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. destruct p.
                eapply conv_hypothesis_wftype. instantiate (1:= Decode l0 t1). constructor. rewrite e in t0. auto. apply TypeSym.
                apply H1. auto. constructor; auto. rewrite e in t. all: try(simpl; auto).
        + apply TypeSym. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. rewrite e. eapply TypeDecodeProdConv.
            destruct p. rewrite e in t. auto. destruct p. rewrite e in t0. auto.
    - intros. simpl in H0. apply decode_ty_inv in H. apply lift_inv in H. destruct H. rewrite e.
        eapply TypeTrans. instantiate (1 := Decode l t).
        + eapply IHt. apply wfTypeDecode. destruct p. auto. auto. auto. auto. auto.
        + apply TypeDecodeLiftConv. destruct p. auto. destruct p. rewrite e in l2. auto. 
Qed.

(* Lemme auxiliaire pour extraire la structure du contexte d'une variable *)
Lemma get_var_split Γ n A :
  [Γ |- var_term n : A] ->
  ∑ Δ Γ' T, Γ = Δ ++ (T :: Γ') × length Δ = n.
Proof.
  intros H. dependent induction H.
  - (* wfVar0 *)
    exists nil, Γ, A. simpl. split; auto. 
  - (* wfVarN *)
    specialize (IHTypingDecl n0 eq_refl).
    destruct IHTypingDecl as [Δ [Γ' [T [Hctx Hlen]]]].
    exists (A :: Δ), Γ', T.
    simpl. split.
    + rewrite Hctx. reflexivity.
    + rewrite Hlen. lia.
  - (* wfTermConv *)
    apply IHTypingDecl. auto.
Qed.

Lemma erase_var_inv {Γ t}:
    forall A A1 n,
    [Γ |- var_term n : A] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    r_var_term n = erase_term t ->
    ([Γ |- var_term n = t : A] × [Γ |- A = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- var_term n = cLift k l0 v0 : A]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
    induction t; intros A A1 n0 Hvar Ht Hinj Herase;
    try (simpl in Herase; discriminate).
    
    - (* Cas t = var_term *)
      simpl in Herase. injection Herase. intro Heq. subst.
      apply inl. split.
      + apply TermRefl. exact Hvar.
      + eapply var_ctx_inv; eauto.
      
    - (* Cas t = cLift k_t l_t t *)
      simpl in Herase. rename l into k_t. rename l0 into l_t.
      
      pose proof Ht as Ht_orig.
      apply lift_inv_plus in Ht. destruct Ht as [n1 [H_A1_Un1 [H_lt_n1 [H_kt_lt H_t_Ukt]]]].
      subst n1.
      
      specialize (IHt A (U k_t) n0 Hvar H_t_Ukt Hinj Herase).
      
      destruct IHt as [[Heq_var_t H_A_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A_Ul0 [H_Ukt_Ul1 [H_var_lift [H_t_lift H_v0_v1]]]]]]]]]].
      + 
        apply inr. eexists k_t, l_t, k_t, (var_term n0), t.
        repeat split; auto.
        * 
          eapply TermConv. instantiate (1:= U k_t).
          -- apply lift_same. eapply wfTermConv. exact Hvar. exact H_A_Ukt.
          -- apply TypeSym. exact H_A_Ukt.
        * (* cLift k_t l_t t = cLift k_t l_t t *)
          apply TermRefl. exact Ht_orig.
        * 
          eapply TermConv. exact Heq_var_t. exact H_A_Ukt.
          
      +
        apply UInj in H_Ukt_Ul1. subst l1'.
        apply inr. eexists l0', l_t, k_in, v0, v1.
        repeat split; auto.
        * 
          eapply TermConv. instantiate (1:= U l_t).
          eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
          -- apply TermLiftingCong. exact H_t_lift. exact H_kt_lt.
          -- apply TermLiftingCumul.
             ++ apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
             ++ apply typing_defeq_inv in H_t_lift. destruct H_t_lift as [_ [_ Hwf_t]]. apply lift_inv in Hwf_t. destruct Hwf_t as [_ [H_kin_kt _]]. exact H_kin_kt.
             ++ exact H_kt_lt.
          -- apply TypeSym. exact H_A1_Un1.
Qed.

Lemma erase_lambda_inv {Γ t}:
    forall A B A1 u,
    [Γ |- Lambda A B u : Prod A B] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    (forall Γ' u1 A1,
    [Γ' |- u : B] ->
    [Γ' |- u1 : A1] ->
    (erase_term u = erase_term u1) ->
    ([Γ' |- u = u1 : B] × [Γ' |- B = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- B = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- u = cLift k l0 v0 : B]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_Lambda (erase_ty A) (erase_ty B) (erase_term u) = erase_term t ->
    [Γ |- Lambda A B u = t : Prod A B ].
Proof.
    induction t.
        all: try(intros; simpl in H4; contradict H4; congruence).
        + intros. simpl in H4. inversion H4. apply lambda_inv in H; destruct H. apply type_defeq_inv in c; destruct c; destruct p.
        apply prod_ty_inv in w; destruct w. apply lambda_inv in H0; destruct H0. apply type_defeq_inv in c0; destruct c0; destruct p.
        apply prod_ty_inv in w3; destruct w3. apply H1 in H6. apply H2 in H7.
        apply TermLambdaCong. 
            all: auto using TypeSym.
            ++ assert (H:=H6). apply TypeSym in H6. apply conv_hypothesis_typing with (1:= t3) in H6. eapply H3 with (1:=t2) (2:= H6) in H8.
                destruct H8.
                +++ destruct p. auto.
                +++  destruct s as [? [? [? [? [? [? [? [? []]]]]]]]]. apply simplify_induction with (1:= c1) (2:= c2) (3:= c3) (4 := c4) (5:= c5) (6:= H7).
            ++ apply TypeSym in H6. apply conv_hypothesis_wftype with (1:= w4) in H6. auto.
        + intros. simpl in H4. eapply IHt in H4. all: auto. contradict H4; intros. apply subject_red in H4.
            apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]]. apply cohesion_prod_univ with (1:= H4) in t0.
            auto. apply typing_defeq_inv in H4. auto. instantiate (1:= U l). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]]. auto.     
Qed.

Lemma erase_app_inv {Γ t}:
    forall A B f a A0 A1,
    [Γ |- App A B f a : A0] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    (forall Γ' u1 A1',
    [Γ' |- f : Prod A B] ->
    [Γ' |- u1 : A1'] ->
    (erase_term f = erase_term u1) ->
    ([Γ' |- f = u1 : Prod A B] × [Γ' |- Prod A B = A1'])
    + (∑ l0 l1 k v0 v1, [Γ' |- Prod A B = U l0] 
        × [Γ' |- A1' = U l1]
        × [Γ' |- f = cLift k l0 v0 : Prod A B]
        × [Γ' |- u1 = cLift k l1 v1 : A1']
        × [Γ' |- v0 = v1 : U k] )) ->
    (forall Γ' u1 A1',
    [Γ' |- a : A] ->
    [Γ' |- u1 : A1'] ->
    (erase_term a = erase_term u1) ->
    ([Γ' |- a = u1 : A] × [Γ' |- A = A1']) 
    + (∑ l0 l1 k v0 v1, [Γ' |- A = U l0] 
        × [Γ' |- A1' = U l1]
        × [Γ' |- a = cLift k l0 v0 : A] 
        × [Γ' |- u1 = cLift k l1 v1 : A1']
        × [Γ' |- v0 = v1 : U k] )) ->
    r_App (erase_ty A) (erase_ty B) (erase_term f) (erase_term a) = erase_term t ->
    ([Γ |- App A B f a = t : A0 ] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- App A B f a = cLift k l0 v0 : A0]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
    induction t; intros A B f a A0 A1 H_App H_t Hinj_A Hinj_B H_f H_a Herase;
    try (simpl in Herase; discriminate).
    
    - (* Cas t = App t1 t2 t3 t4 *)
      simpl in Herase. injection Herase. intros Heq_a Heq_f Heq_B Heq_A.
      
      pose proof H_App as Happ_orig.
      (* On récupère Heq_A0_subst : [Γ |- A0 = subst_ty a B] *)
      apply app_inv in H_App. destruct H_App as [Heq_A0_subst [HwfA [HwfB [Htyp_f Htyp_a]]]].
      
      pose proof H_t as Ht_orig.
      apply app_inv in H_t. destruct H_t as [Heq_A1_subst [HwfA0_t [HwfB0_t [Htyp_f0 Htyp_a0]]]].
      
      assert (HeqA : [Γ |- A = t1]).
      { apply Hinj_A. exact HwfA. exact HwfA0_t. exact Heq_A. }
      
      assert (HeqB : [Γ,, A |- B = t2]). 
      { apply Hinj_B. 
        - exact HwfB. 
        - eapply conv_hypothesis_wftype. exact HwfB0_t. apply TypeSym. exact HeqA. 
        - exact Heq_B. }
      
      assert (Htyp_f0_conv : [Γ |- t3 : Prod A B]).
      { eapply wfTermConv. 
        - exact Htyp_f0. 
        - apply TypeSym. apply TypePiCong. 
          ++ exact HwfA. 
          ++ exact HeqA. 
          ++ exact HeqB. }
      
      specialize (H_f Γ t3 (Prod A B) Htyp_f Htyp_f0_conv Heq_f).
      destruct H_f as [[Heq_f_conv H_Prod_eq] | Right_f].
      
      + (* f is strict equality *)
        assert (Htyp_a0_conv : [Γ |- t4 : A]).
        { eapply wfTermConv. 
          - exact Htyp_a0. 
          - apply TypeSym. exact HeqA. }
        specialize (H_a Γ t4 A Htyp_a Htyp_a0_conv Heq_a).
        
        destruct H_a as [[Heq_a_conv H_A_eq] | Right_a].
        * (* a is strict equality *)
          apply inl. split.
          -- eapply TermConv. 
             ++ apply TermAppCong.
                ** exact HeqA.
                ** exact HeqB.
                ** exact Heq_f_conv.
                ** exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A0_subst.
          -- eapply TypeTrans. exact Heq_A0_subst.
             eapply TypeTrans. instantiate (1 := subst_ty t4 t2).
             ++ eapply subst_cong. exact HeqB. exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A1_subst.

        * (* a is a lift *)
          assert (Heq_a_conv : [Γ |- a = t4 : A]).
          { eapply simplify_induction_grouped. exact Right_a. apply TypeRefl. exact HwfA. }
          apply inl. split.
          -- eapply TermConv.
             ++ apply TermAppCong.
                ** exact HeqA.
                ** exact HeqB.
                ** exact Heq_f_conv.
                ** exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A0_subst.
          -- eapply TypeTrans. exact Heq_A0_subst.
             eapply TypeTrans. instantiate (1 := subst_ty t4 t2).
             ++ eapply subst_cong. exact HeqB. exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A1_subst.

      + (* f is a lift *)
        destruct Right_f as [l0' [l1' [k [v0 [v1 [Heq_Prod_U _]]]]]].
        exfalso. eapply cohesion_prod_univ. 
        ++ exact Htyp_f.
        ++ eapply wfTermConv. exact Htyp_f. exact Heq_Prod_U.
        
    - (* Cas t = cLift k_t l_t t_inner *)
      simpl in Herase. rename l into k_t. rename l0 into l_t.
      
      pose proof H_t as Ht_orig.
      apply lift_inv_plus in H_t. destruct H_t as [n1 [H_A1_Un1 [H_lt_n1 [H_kt_lt H_t_Ukt]]]].
      subst n1.
      
      (* L'appel récursif utilise directement A0 ! *)
      specialize (IHt A B f a A0 (U k_t) H_App H_t_Ukt Hinj_A Hinj_B H_f H_a Herase).
      
      destruct IHt as [[Heq_App_t H_A0_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A0_Ul0 [H_Ukt_Ul1 [H_App_lift [H_t_lift H_v0_v1]]]]]]]]]].
      + (* Cas Left: IHt a renvoyé l'égalité stricte App = t_inner *)
        apply inr. eexists k_t, l_t, k_t, (App A B f a), t.
        repeat split; auto.
        * (* App = cLift k_t k_t App *)
          eapply TermConv. instantiate (1:= U k_t).
        -- apply lift_same. eapply wfTermConv. exact H_App. exact H_A0_Ukt.
          -- apply TypeSym. exact H_A0_Ukt.
        * (* cLift k_t l_t t = cLift k_t l_t t *)
          apply TermRefl. exact Ht_orig.
        * (* App = t_inner : U k_t *)
          eapply TermConv. exact Heq_App_t. exact H_A0_Ukt.
          
      + (* Cas Right: App et t_inner sont déjà tous les deux des lifts profonds *)
        apply UInj in H_Ukt_Ul1. subst l1'.
        apply inr. eexists l0', l_t, k_in, v0, v1.
        repeat split; auto.
        * (* cLift k_t l_t t = cLift k_in l_t v1 *)
          eapply TermConv. instantiate (1:= U l_t).
          eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
          -- apply TermLiftingCong. exact H_t_lift. exact H_kt_lt.
          -- apply TermLiftingCumul.
             ++ apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
             ++ apply typing_defeq_inv in H_t_lift. destruct H_t_lift as [_ [_ Hwf_t]]. apply lift_inv in Hwf_t. destruct Hwf_t as [_ [H_kin_kt _]]. exact H_kin_kt.
             ++ exact H_kt_lt.
          -- apply TypeSym. exact H_A1_Un1.
Qed.


Lemma erase_cprod_inv {Γ t}:
    forall a b l A0 A1,
    [Γ |- cProd l a b : A0] ->
    [Γ |- t : A1] ->
    (* Hypothèses d'injectivité des types *)
    (forall C, [Γ |- A0] -> [Γ |- C] -> (erase_ty A0 = erase_ty C) -> [Γ |- A0 = C]) ->
    (* Hypothèse pour a *)
    (forall Γ' u1 A1,
    [Γ' |- a : U l] ->
    [Γ' |- u1 : A1] ->
    (erase_term a = erase_term u1) ->
    ([Γ' |- a = u1 : U l] × [Γ' |- U l = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- U l = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- a = cLift k l0 v0 : U l]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    (* Hypothèse pour b *)
    (forall Γ' u1 A1,
    [Γ' |- b : U l] -> 
    [Γ' |- u1 : A1] ->
    (erase_term b = erase_term u1) ->
    ([Γ' |- b = u1 : U l] × [Γ' |- U l = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- U l = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- b = cLift k l0 v0 : U l]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_Prod (erase_term a) (erase_term b) = erase_term t ->
    (* Conclusion *)
    ([Γ |- cProd l a b = t : A0 ] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- cProd l a b = cLift k l0 v0 : A0]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
  induction t; intros a b l_ A0 A1 Hprod Ht Hinj_ty Ha Hb Herase;
  
  try (simpl in Herase; discriminate).

  - (* Cas t = cProd l_t t1 t2 *)
    rename l into l_t.
    simpl in Herase. injection Herase. intros Heb Hea.
    
    apply code_prod_inv_plus in Hprod. destruct Hprod as [n_A0 [H_A0_Ul [H_l_nA0 [H_a_Ul H_b_Ul]]]]. subst n_A0.
    apply code_prod_inv_plus in Ht. destruct Ht as [n' [H_A1_Ult [H_lt_n' [H_t1_Ult H_t2_Ult]]]]. subst n'.

    specialize (Ha Γ t1 (U l_t) H_a_Ul H_t1_Ult Hea).

    assert (H_dec_eq : [Γ |- Decode l_ a = Decode l_t t1]).
    {
      destruct Ha as [[Heq_a H_Ul] | [l0' [l1' [ka [va [va' [H_Ul [H_Ult [H_a_lift [H_t1_lift H_va_eq]]]]]]]]]].
      - apply UInj in H_Ul. subst l_t.
        apply TypeDecodeCong. exact Heq_a.
      - apply UInj in H_Ul. subst l0'.
        apply UInj in H_Ult. subst l1'.
        
        eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
        { apply TypeDecodeCong. exact H_a_lift. }
        eapply TypeTrans. instantiate (1 := Decode ka va).
        { apply TypeSym. apply TypeDecodeLiftConv.
          - apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [Hwf_va _]]. exact Hwf_va.
          - apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ H_lift_a]].
            apply lift_inv in H_lift_a. destruct H_lift_a as [_ [H_ka_l _]]. exact H_ka_l. }
        eapply TypeTrans. instantiate (1 := Decode ka va').
        { apply TypeDecodeCong. exact H_va_eq. }
        eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
        { apply TypeDecodeLiftConv.
          - apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [_ Hwf_va']]. exact Hwf_va'.
          - apply typing_defeq_inv in H_t1_lift. destruct H_t1_lift as [_ [_ H_lift_t1]].
            apply lift_inv in H_lift_t1. destruct H_lift_t1 as [_ [H_ka_lt _]]. exact H_ka_lt. }
        { apply TypeSym. apply TypeDecodeCong. exact H_t1_lift. }
    }

    assert (Ht2_trans : [Γ ,, Decode l_ a |- t2 : U l_t]).
    { eapply conv_hypothesis_typing. exact H_t2_Ult. apply TypeSym. exact H_dec_eq. }

    specialize (Hb (Γ ,, Decode l_ a) t2 (U l_t) H_b_Ul Ht2_trans Heb).

    destruct Ha as [[Heq_a H_Ul_a] | [l0_a [l1_a [ka [va [va' [H_Ul_a [H_Ult_a [H_a_lift [H_t1_lift H_va_eq]]]]]]]]]].
    
    +
      apply UInj in H_Ul_a. subst l_t.
      destruct Hb as [[Heq_b H_Ul_b] | [l0_b [l1_b [kb [vb [vb' [H_Ul_b [H_Ult_b [H_b_lift [H_t2_lift H_vb_eq]]]]]]]]]].
      *
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.
      
      *
        apply UInj in H_Ul_b. subst l0_b. 
        apply UInj in H_Ult_b. subst l1_b. 
        assert (Heq_b : [Γ ,, Decode l_ a |- b = t2 : U l_]).
        { eapply TermTrans. exact H_b_lift. 
          eapply TermTrans. 2: { apply TermSym. exact H_t2_lift. }
          apply TermLiftingCong. exact H_vb_eq.
          apply typing_defeq_inv in H_b_lift. destruct H_b_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.

    +
      apply UInj in H_Ul_a. subst l0_a. 
      apply UInj in H_Ult_a. subst l1_a.
      
      destruct Hb as [[Heq_b H_Ul_b] | [l0_b [l1_b [kb [vb [vb' [H_Ul_b [H_Ult_b [H_b_lift [H_t2_lift H_vb_eq]]]]]]]]]].
      * 
        apply UInj in H_Ul_b. subst l_t.
        assert (Heq_a : [Γ |- a = t1 : U l_]).
        { eapply TermTrans. exact H_a_lift. 
          eapply TermTrans. 2: { apply TermSym. exact H_t1_lift. }
          apply TermLiftingCong. exact H_va_eq.
          apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.

      * (* Lifts *)
        apply UInj in H_Ul_b. subst l0_b. 
        apply UInj in H_Ult_b. subst l1_b.
        
        assert (H_va_U : [Γ |- va : U ka]).
        { apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [Hwf _]]. exact Hwf. }
        assert (H_vb_U : [Γ ,, Decode l_ a |- vb : U kb]).
        { apply typing_defeq_inv in H_vb_eq. destruct H_vb_eq as [_ [Hwf _]]. exact Hwf. }
        assert (H_ka_l : ka < l_).
        { apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        assert (H_kb_l : kb < l_).
        { apply typing_defeq_inv in H_b_lift. destruct H_b_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        
        assert (H_va'_U : [Γ |- va' : U ka]).
        { apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [_ Hwf]]. exact Hwf. }
        assert (H_vb'_U : [Γ ,, Decode l_ a |- vb' : U kb]).
        { apply typing_defeq_inv in H_vb_eq. destruct H_vb_eq as [_ [_ Hwf]]. exact Hwf. }
        assert (H_ka_lt : ka < l_t).
        { apply typing_defeq_inv in H_t1_lift. destruct H_t1_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        assert (H_kb_lt : kb < l_t).
        { apply typing_defeq_inv in H_t2_lift. destruct H_t2_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }

        destruct (lt_eq_lt_dec ka kb) as [[H_ka_lt_kb | H_ka_eq_kb] | H_kb_lt_ka].
        
        ++ (* Cas ka < kb *)
           apply inr. eexists l_, l_t, kb.
           eexists (cProd kb (cLift ka kb va) vb), (cProd kb (cLift ka kb va') vb').
           
           assert (H_dec_kb : [Γ |- Decode l_ a = Decode kb (cLift ka kb va)]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             eapply TypeTrans. instantiate (1 := Decode ka va).
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
             { apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_lt_kb. } 
           }
           
           assert (H_dec_kb' : [Γ |- Decode l_t t1 = Decode kb (cLift ka kb va')]).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             eapply TypeTrans. instantiate (1 := Decode ka va').
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
             { apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt_kb. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- (* cProd l_ a b = cLift kb l_ (cProd kb (cLift ka kb va) vb) *)
              eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. 
                 *** eapply TermTrans. exact H_a_lift. apply TermSym. eapply TermLiftingCumul. exact H_va_U. exact H_ka_lt_kb. exact H_kb_l.
                 *** exact H_b_lift.
              ** apply TermSym. apply TermLiftingProdConv.
                 *** apply wfTermcLift. exact H_va_U. exact H_ka_lt_kb.
                 *** eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_kb.
                 *** exact H_kb_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- (* t1 = cLift kb l_t (cProd kb (cLift ka kb va') vb') *)
              eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult.
                 *** eapply TermTrans. exact H_t1_lift. apply TermSym. eapply TermLiftingCumul. exact H_va'_U. exact H_ka_lt_kb. exact H_kb_lt.
                 *** eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
              ** apply TermSym. apply TermLiftingProdConv.
                 *** apply wfTermcLift. exact H_va'_U. exact H_ka_lt_kb.
                 *** eapply conv_hypothesis_typing. 2: { exact H_dec_kb'. }
                     eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 *** exact H_kb_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- (* v0 = v1 : U kb *)
              apply TermPiCong. 
              ** apply wfTermcLift. exact H_va_U. exact H_ka_lt_kb.
              ** apply TermLiftingCong. exact H_va_eq. exact H_ka_lt_kb.
              ** eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_kb.

        ++ (* Cas ka = kb *)
           subst kb. apply inr. eexists l_, l_t, ka.
           eexists (cProd ka va vb), (cProd ka va' vb').

           assert (H_dec_ka : [Γ |- Decode l_ a = Decode ka va]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
           }
           
           assert (H_dec_ka' : [Γ |- Decode l_t t1 = Decode ka va']).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- (* cProd l_ a b = cLift ka l_ (cProd ka va vb) *)
              eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. exact H_a_lift. exact H_b_lift.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va_U.
                 eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_ka.
                 exact H_ka_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- (* t1 = cLift ka l_t (cProd ka va' vb') *)
              eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult. exact H_t1_lift. 
                 eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va'_U.
                 eapply conv_hypothesis_typing. 2: { exact H_dec_ka'. }
                 eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 exact H_ka_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- (* v0 = v1 : U ka *)
              apply TermPiCong. exact H_va_U. exact H_va_eq.
              eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_ka.

        ++ (* Cas kb < ka *)
           apply inr. eexists l_, l_t, ka.
           eexists (cProd ka va (cLift kb ka vb)), (cProd ka va' (cLift kb ka vb')).

           assert (H_dec_ka : [Γ |- Decode l_ a = Decode ka va]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
           }
           
           assert (H_dec_ka' : [Γ |- Decode l_t t1 = Decode ka va']).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- (* cProd l_ a b = cLift ka l_ (cProd ka va (cLift kb ka vb)) *)
              eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. exact H_a_lift.
                 *** eapply TermTrans. exact H_b_lift. apply TermSym. eapply TermLiftingCumul. exact H_vb_U. exact H_kb_lt_ka. exact H_ka_l.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va_U.
                 apply wfTermcLift. eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_ka.
                 exact H_kb_lt_ka. exact H_ka_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- (* t1 = cLift ka l_t (cProd ka va' (cLift kb ka vb')) *)
              eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult. exact H_t1_lift.
                 *** eapply TermTrans. eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
                     apply TermSym. eapply TermLiftingCumul. eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                     exact H_kb_lt_ka. exact H_ka_lt.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va'_U.
                 apply wfTermcLift. eapply conv_hypothesis_typing. 2: { exact H_dec_ka'. }
                 eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 exact H_kb_lt_ka. exact H_ka_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- (* v0 = v1 : U ka *)
              apply TermPiCong. exact H_va_U. exact H_va_eq.
              apply TermLiftingCong. eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_ka.
              exact H_kb_lt_ka.

  - (* Cas t = cLift k_t l_t t *)
    rename l into k_t. rename l0 into l_t.
    simpl in Herase.
    
    pose proof Hprod as Hprod_orig.
    
    apply code_prod_inv_plus in Hprod. destruct Hprod as [n_A0 [H_A0_Ul [H_l_nA0 [H_a_Ul H_b_Ul]]]]. subst n_A0.
    apply lift_inv_plus in Ht. destruct Ht as [n' [H_A1_Un' [H_lt_n' [H_kt_lt H_t'_Ukt]]]]. subst n'.
    
    specialize (IHt a b l_ A0 (U k_t) Hprod_orig H_t'_Ukt Hinj_ty Ha Hb Herase).
    
    destruct IHt as [[Heq_cProd H_A0_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A0_Ul0 [H_Ukt_Ul1 [H_cProd_lift [H_t'_lift H_v0_v1]]]]]]]]]].
    +
      assert (H_U_eq : [Γ |- U l_ = U k_t]).
      { eapply TypeTrans. apply TypeSym. exact H_A0_Ul. exact H_A0_Ukt. }
      apply UInj in H_U_eq. subst k_t.
      
      apply inr. eexists l_, l_t, l_.
      eexists (cProd l_ a b). eexists t.
      repeat split; auto.
      * eapply TermConv. instantiate (1 := U l_).
        -- apply lift_same. eapply wfTermConv. exact Hprod_orig. exact H_A0_Ul.
        -- apply TypeSym. exact H_A0_Ul.
      * apply TermRefl. eapply wfTermConv. eapply wfTermcLift; eauto. auto using TypeSym.
      * eapply TermConv. exact Heq_cProd. exact H_A0_Ul.
      
    +
      assert (H_U_eq0 : [Γ |- U l_ = U l0']).
      { eapply TypeTrans. apply TypeSym. exact H_A0_Ul. exact H_A0_Ul0. }
      apply UInj in H_U_eq0. subst l0'.
      
      apply UInj in H_Ukt_Ul1. subst l1'.
      
      apply inr. eexists l_, l_t, k_in.
      eexists v0. eexists v1.
      
      repeat split; auto.
      
      assert (H_kin_kt : k_in < k_t).
      { apply typing_defeq_inv in H_t'_lift. destruct H_t'_lift as [_ [_ Hwf]].
        apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }

      eapply TermConv. instantiate (1:= U l_t).
      eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
      
      * apply TermLiftingCong. exact H_t'_lift. exact H_kt_lt.
      * apply TermLiftingCumul.
        -- apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
        -- exact H_kin_kt.
        -- exact H_kt_lt.
      * apply TypeSym. exact H_A1_Un'.
Qed.


Lemma erase_cuniv_inv
{Γ t}:
    forall k1 l1 k2 l2 A0 A1,
    [ Γ |- cU k1 l1 : A0 ] ->
    [ Γ |- cLift k2 l2 t : A1 ] ->
    r_U k1 = erase_term t ->
    (∑ k v0 v1,
        [Γ |- A0 = U l1] 
        × [Γ |- A1 = U l2]
        × [Γ |- cU k1 l1 = cLift k l1 v0 : A0]
        × [Γ |- cLift k2 l2 t = cLift k l2 v1 : A1]
        × [Γ |- v0 = v1 : U k] ). 
Proof.
    induction t.
    all: try(intros; simpl in H1; contradict H1; congruence).
    - intros. simpl in H1. inversion H1. rewrite H3 in H. set (K:= Nat.min (l0) (l1)).
    assert (H0bis:=H0). apply lift_inv_plus in H0bis. destruct H0bis as [? [? [? []]]].
    assert (tbis:=t). apply code_univ_inv_bis in tbis. destruct tbis. assert (Hbis :=H). apply code_univ_inv_bis in Hbis. destruct Hbis.
    apply UInj in c0.
    eexists K.  eexists (cU l K). eexists (cU l K). 
    constructor. auto. constructor. symmetry in e; rewrite e in c; auto. constructor.
    apply TermSym. eapply TermConv. instantiate (1:=U l1). apply conv_lift_univ_min. apply inv_wfcontext_typing in t. destruct t. all: auto using TypeSym. 
    constructor. eapply TermConv. instantiate (1:= U l2). rewrite c0. eapply TermTrans.
    instantiate (1:= cU l l2). apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    auto. rewrite c0 in l3. auto. apply TermSym. apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    apply inf_min. auto. auto. lia. rewrite e. auto using TypeSym. apply TermRefl. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
    apply inf_min. auto. auto.
    
    - intros. simpl in H1. assert (H0bis:=H0). apply lift_inv_plus in H0bis. destruct H0bis as [? [? [? []]]].
    assert (t0bis:=t0). apply lift_inv_plus in t0bis. destruct t0bis as [? [? [? []]]].
    apply UInj in c0. symmetry in e0. rewrite e0 in c0. rewrite c0 in l3.  apply TermLiftingCumul with (1:=t1) (2:= l4) in l3.
    apply typing_defeq_inv in l3. destruct l3 as [? []]. 
    eapply IHt with (1:= H) (2:= t3) in H1. destruct H1 as [? [? [? [? [? [? []]]]]]].
    eexists projT5. eexists projT6. eexists projT7.
    constructor. auto.
    constructor. rewrite e. auto.
    constructor. auto.
    constructor. eapply TermConv. instantiate (1:= U l2). eapply TermTrans. instantiate (1:= cLift l l2 t).
    rewrite c0. auto. auto. rewrite e. auto using TypeSym. auto.
Qed. 


(* -------- Lemme principal ------- *)

Lemma erase_inj_ty {Γ A B} : [Γ |- A] -> [Γ |- B] -> (erase_ty A = erase_ty B) -> [Γ |- A = B]
with erase_inj_term {u0}:
    forall Γ u1 A0 A1,
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ). 
Proof.

(* Types *)
induction 1. (* Induction on A *)
- intros;  destruct B. (* A = U n *)
    all: try (simpl in H0; contradict H0; congruence). (* Eliminate impossible cases *)
    + apply erase_decode_inv_univ. auto. simpl in H0. auto. 
    + simpl in H0. inversion H0. auto.

- intros; destruct B. (* A = Prod A1 A2 *)
    all: try (simpl in H2; contradict H2; congruence).
    + simpl in H2. inversion H2. apply TypePiCong. auto.
        ++ apply erase_inj_ty. auto. inversion H1. auto. auto.
        ++ apply erase_inj_ty. auto. inversion H1. eapply conv_hypothesis_wftype.
            instantiate (1:= B1). auto. apply erase_inj_ty. auto. auto. auto. auto.
    + simpl in H2. apply erase_decode_inv_prod. auto. constructor. all: try(auto).
    
- intros. destruct B. (* A = Decode n a *)
    + destruct a.
        all: try(simpl in H0; contradict H0; congruence).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
    + simpl in H0. apply decode_ty_inv in H. apply erase_inj_term with (1:=t) (2:=H) in H0.
        destruct H0.  destruct p. apply UInj in c0. rewrite c0. apply TypeDecodeCong. rewrite c0 in c. auto.
        destruct s; destruct projT4; destruct projT5; destruct projT6; destruct projT7; destruct projT8; destruct p as [ ? [ ? []] ].
        apply UInj in c; apply UInj in c0. symmetry in c; rewrite c in c1. symmetry in c0; rewrite c0 in c2. eapply TypeTrans. instantiate (1:= Decode n (cLift projT5 n projT6)).
            apply TypeDecodeCong. auto. eapply TypeTrans. instantiate (1:=Decode l (cLift projT5 l projT7)).
            eapply TypeTrans. instantiate (1:= Decode projT5 projT6). apply TypeSym; apply TypeDecodeLiftConv. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ eapply TypeTrans. instantiate (1:= Decode projT5 projT7). apply TypeDecodeCong. auto. apply TypeDecodeLiftConv.   
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ apply TypeDecodeCong. apply TermSym. auto. 

    + simpl in H0. apply TypeSym. apply erase_decode_inv_univ. apply wfTypeDecode. auto. auto.
    
(* Terms *)
- induction u0.

    (* u0 = var_term n *)
    + intros. destruct u1. apply erase_var_inv. all: auto.
    
    (* u0 = Lambda *)
    + intros. destruct u1.
        all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1. inversion H1. apply lambda_inv in H. destruct H. apply lambda_inv in H0. destruct H0.
            apply wftype_typing_inv in  t3; destruct t3. apply wftype_typing_inv in t4; destruct t4.
            apply wftype_hypothesis_inv in w; destruct w. apply wftype_hypothesis_inv in w0; destruct w0.  
            apply erase_inj_ty with (1:=w) (2:= w0) in H3. assert (H' := H3). apply conv_hypothesis_typing with (1:= t3) in H3.
            apply IHu0 with (1:=H3) (2:= t4) in H5. destruct H5.
            assert (H := H'). apply conv_hypothesis_wftype with (1:= w1) in H'. apply erase_inj_ty with (1:= H') (2:=w2) in H4. destruct p.
                +++ constructor. 
                    constructor. eapply TermConv. instantiate (1:=Prod t t0). eapply TermLambdaCong. auto. auto.
                    eapply conv_hypothesis_type_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply conv_hypothesis_term_eq. instantiate (1:= t1). auto. apply TypeSym; auto.
                    auto using TypeSym. apply TypeTrans with (1:= c). apply TypeSym. apply TypeTrans with (1:=c0).
                    constructor. auto. auto using TypeSym. auto using TypeSym.
                +++ destruct s as [? [? [? [? [? [ ? [? [ ? []]]]]]]]]. apply inl. 
                    assert (H := H'). apply conv_hypothesis_wftype with (1:= w1) in H'. apply erase_inj_ty with (1:= H') (2:=w2) in H4.
                    constructor. eapply TermConv. instantiate (1:=Prod t t0). eapply TermLambdaCong. auto. auto. 
                    eapply conv_hypothesis_type_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply TermTrans. instantiate (1:= cLift projT5 projT3 projT6). eapply conv_hypothesis_term_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply TermTrans. instantiate (1:= cLift projT5 projT4 projT7). eapply TermConv. instantiate (1:= U projT3).
                    apply TypeTrans with (1:=H4) in c2. apply TypeSym in c2. apply TypeTrans with (1:= c2) in c1. apply UInj in c1.
                    rewrite c1. apply TermLiftingCong. eapply conv_hypothesis_term_eq. instantiate (1:=t1). auto. auto using TypeSym.
                    apply typing_defeq_inv in c3. destruct c3 as [? []]. apply TypeSym in c2. eapply wfTermConv with (1:= t6) in c2. apply lift_inv in c2.
                    destruct c2 as [? []]. all: auto using TypeSym. eapply conv_hypothesis_type_eq. instantiate (1:= t1). all: auto using TypeSym.
                    eapply conv_hypothesis_term_eq. instantiate (1:= t1). apply TermSym. apply TermConv with (1:= c4). all: auto using TypeSym.
                    eapply TypeTrans. instantiate (1:= Prod t t0). auto. apply TypeSym. eapply TypeTrans. instantiate (1:= Prod t1 t2). auto.
                    apply TypePiCong. all: auto using TypeSym.
                    (* Utiliser simplify_induction pour simplifier la preuve ?*)

        ++ simpl in H1. assert (Hbis := H). apply lambda_inv in Hbis; destruct Hbis. apply wfTermConv with (1:=H) in c.
            apply inl. eapply erase_lambda_inv with (1:= c) (2:= H0) in H1.
            all: auto. constructor. assert (Hbis := H). apply lambda_inv in Hbis; destruct Hbis.
            eapply TermConv. instantiate (1:= Prod t t0). all : auto using TypeSym.
            apply subject_red in H1. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
            apply wfTermConv with (1:= Hbis) in c0. contradict H1. intros. apply cohesion_prod_univ with (1:= H1) (2:= c0). auto.

    (* u0 = App *)
    + intros. destruct u1. apply erase_app_inv. all:auto. 
    
    (* u0 = cProd *)
    + intros. destruct u1. apply erase_cprod_inv. all: auto.

    (* u0 = cU *)
    + intros. destruct u1. 
        all: try(simpl in H1; contradict H1; congruence).
        ++  simpl in H1. inversion H1. assert (Hbis:=H). apply code_univ_inv_bis in Hbis. destruct Hbis.
        assert (H0bis:=H0). apply code_univ_inv_bis in H0bis. destruct H0bis.
        apply inr. eexists l0. eexists l2. set (k:=(Nat.min l0 l2)). eexists k. eexists (cU l k). eexists (cU l k).
        constructor. auto. constructor. auto. constructor. apply TermSym. eapply TermConv. instantiate (1:= U l0).
        rewrite H3. apply conv_lift_univ_min_comm. apply inv_wfcontext_typing in H. destruct H. auto. auto. lia. auto using TypeSym.

        constructor.  apply TermSym. eapply TermConv. instantiate (1:= U l2).
        rewrite H3. apply conv_lift_univ_min. apply inv_wfcontext_typing in H. destruct H. auto. lia. lia. auto using TypeSym.
        apply TermRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto.
        apply inf_min. auto. rewrite H3; auto.

        ++ simpl in H1. apply inr. eexists l0; eexists l2. apply erase_cuniv_inv.
            auto. auto. auto.
    
    (* u0 = cLift *)
    + intros. assert (Hbis:= H). apply lift_inv_plus in Hbis. destruct Hbis as [? [? [? []]]].
        apply IHu0 with (1:=t) (2:=H0) in H1. destruct H1.
        ++ destruct p. symmetry in e. rewrite e in c. apply TypeSym in c1. apply inr.
            eexists l0. eexists l. eexists l. eexists u0. eexists u0.
            constructor; auto.
            constructor; auto.
            constructor. apply TermRefl. auto.
            constructor. eapply TermConv. instantiate (1:= U l). eapply TermTrans. instantiate (1:=u0).
            auto using TermSym. eapply lift_same. auto.  auto using TypeSym. apply TermRefl. auto.
     
        ++ destruct s as [? [? [? [? [? [? [? [? []]]]]]]]]. apply inr. apply UInj in c0. symmetry in e; rewrite e in c.
            eexists l0. eexists projT5. eexists projT6. eexists projT7. eexists projT8.
            constructor. auto.
            constructor. auto.
            constructor. assert (l1bis:=l1). apply TermLiftingCong with (1:= c2) in l1bis.
            eapply TermConv. instantiate (1:= U l0).
            eapply TermTrans. instantiate (1:= cLift l l0 (cLift projT6 projT4 projT7)). 
            auto. rewrite c0. apply TermLiftingCumul. apply typing_defeq_inv in c4. destruct c4 as [? []].
            auto. apply typing_defeq_inv in c2. destruct c2 as [? []]. apply lift_inv_plus in t1. destruct t1 as [? [? [? []]]].
            auto. rewrite c0 in l1. auto. auto using TypeSym.
            constructor. auto.
            auto.

Admitted. (* TODO : Decreasing argument *)

Lemma erase_inj_term_plus {u0}:
    forall Γ u1 A0 A1,
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    (erase_ty A0 = erase_ty A1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. apply erase_inj_term with (1:=H) (2:=H0) in H1. apply wftype_typing_inv in H, H0. destruct H, H0. apply erase_inj_ty with (1:= w) (2:=w0) in H2.
    destruct H1.
    - auto.
    - apply simplify_induction_grouped. auto. auto. 
Qed.

Theorem erase_inj_ctx_mutual :
  (forall Γ (H:[|- Γ]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> True) *
  ((forall Γ A (H:[Γ |- A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- A]) *
  ((forall Γ a A (H:[Γ |- a : A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- a : A]) *
  ((forall Γ A B (H:[Γ |- A = B]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- A = B]) *
  (forall Γ a b A (H:[Γ |- a = b : A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- a = b : A])))).
Proof.
  apply mut_ind_erasure_rect; intros.
  
  all: try match goal with H : erase_context _ = erase_context _ |- _ => rename H into Heq end.
  all: try match goal with H : [ |- _ ] |- _ => rename H into HwfG' end.

  (* --- Cas WfContextDecl --- *)
  - (* connil *) trivial.
  - (* concons *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    apply H with (1:=H3) (2:=HeqA).

  (* --- Cas WfTypeDecl --- *)
  - (* wfTypeU *) constructor; auto.
  - (* wfTypeProd *)
    apply wfTypeProd.
    + apply H; auto. 
    + apply H0.      
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
  - (* wfTypeDecode *) constructor. apply H; auto.

  (* --- Cas TypingDecl --- *)
  - (* wfVar0  *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    assert (Heq_types: [Γ' |- A = A']).
    { apply erase_inj_ty. apply H with (1:=H2); auto. auto. auto. }
    eapply wfTermConv.
    + apply wfVar0. exact H3.
    + apply TypeSym. apply weak_cong. exact Heq_types.

  - (* wfVarN *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    apply wfVarN.
    + exact H4.
    + apply H0; auto.

    - (* wfTermcProd *)
    apply wfTermcProd.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

    - econstructor. eauto. eauto.
    - econstructor. eauto. eauto.

  - (* wfTermLambda *)
    apply wfTermLambda.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.

    - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.
    assert (Heq' : erase_context (Γ,,A) = erase_context (Γ',,A)).
    {simpl. rewrite Heq. auto. }
    apply H1. econstructor. eauto. eauto. eauto.

  - econstructor. eauto.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.

  - (* TypeDecodeProdConv*)
    apply TypeDecodeProdConv.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

  - econstructor. eauto.
  - econstructor. eauto. eauto.
  - apply TypeSym. eauto.

  - (* TermBRed *)
    eapply TermBRed.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
    + apply H1; auto.

  (* --- Cas ConvTermDecl --- *)
  - (* TermPiCong *)
    apply TermPiCong.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

  - econstructor. eauto. apply H0. econstructor. eauto. eapply type_defeq_inv. apply TypeSym. eapply H.
    eauto. eauto. simpl. rewrite Heq. eauto. eauto. eauto.

  - (* TermLambdaCong *)
    apply TermLambdaCong.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
    + apply H2.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.

  - (* TermLiftingProdConv : Extension de contexte *)
    apply TermLiftingProdConv; auto.
    + apply H0; auto. constructor. auto. constructor. auto. simpl. rewrite Heq. auto.
  
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. apply TermSym. eauto. apply TypeRefl. apply H in HwfG'. apply typing_defeq_inv in HwfG'. destruct HwfG' as [? []].
    apply wftype_typing_inv in t1. destruct t1. eauto. eauto.
  - eapply TermTrans. eauto. eauto. 
Qed.

Lemma erase_inj_ctx_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall a A, [Γ |- a : A] -> [Γ' |- a : A]).
Proof.
  intros Γ' HwfG HwfG' Heq a A Htyp.
  eapply (fst (snd (snd erase_inj_ctx_mutual))).
  - exact Htyp.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_type {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A, [Γ |- A] -> [Γ' |- A]).
Proof.
  intros Γ' HwfG HwfG' Heq A Htyp.
  eapply (fst (snd erase_inj_ctx_mutual)).
  - exact Htyp.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_conv_ty {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A B, [Γ |- A = B] -> [Γ' |- A = B]).
Proof.
  intros Γ' HwfG HwfG' Heq A B Hconv.
  eapply (fst (snd (snd (snd erase_inj_ctx_mutual)))).
  - exact Hconv.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_conv_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall u v A, [Γ |- u = v : A ] -> [Γ' |- u = v : A ]).
Proof.
  intros Γ' HwfG HwfG' Heq u v A Hconv.
  eapply (snd (snd (snd (snd erase_inj_ctx_mutual)))).
  - exact Hconv.
  - exact HwfG'.
  - exact Heq.
Qed.


Lemma decode_prod_structure_from_erasure:
  forall t Γ l A B,
  [Γ |- t : U l] ->
  erase_term t = r_Prod A B ->
  ∑  A1 B1,
    [Γ |- Decode l t = Prod A1 B1] ×
    erase_ty A1 = A ×
    erase_ty B1 = B.
Proof.
  induction t; intros; simpl in H0; try discriminate.
  (* Cas cProd *)
  - injection H0; intros; subst.
    apply code_prod_inv in H. destruct H as [? [? ?]]. subst.
    eexists (Decode l0 t1), (Decode l0 t2).
    split.
    + apply TypeDecodeProdConv; auto.
    + simpl. split; auto.
  (* Cas cLift *)
  - apply lift_inv in H. destruct H as [? [? ?]]. subst.
    specialize (IHt _ _ _ _  t0 H0).
    destruct IHt as [A1 [B1 [Heq [HA HB]]]].
    exists A1, B1.
    split.
    + eapply TypeTrans. 
      2: exact Heq.
      apply TypeSym. apply TypeDecodeLiftConv; auto.
    + split; auto.
Qed.

(* ----- Principal théorème d'équivalence ----- *)
Theorem section_ctx {Γ} :
    [ |-r Γ] ->
    (∑ Γ1,
    [ |- Γ1] × (erase_context Γ1 = Γ))
with section_ty {Γ A} :
    [Γ |-r A] ->
    (∑ Γ1 A1,
    [Γ1 |- A1] × (erase_ty A1 = A) × (erase_context Γ1 = Γ))
with section_term {Γ u A} :
    [Γ |-r u : A] ->
    (∑ Γ1 u1 A1,
    [Γ1 |-  u1 : A1] × (erase_ty A1 = A) × (erase_term u1 = u) × (erase_context Γ1 = Γ))
with section_conv {Γ A B} :
    [Γ |-r A = B] ->
    (∑ Γ1 A1 B1,
    [Γ1 |- A1 = B1] × (erase_ty A1 = A) × (erase_ty B1 = B) × (erase_context Γ1 = Γ))
with section_conv_term {Γ u v A} :
    [Γ |-r u = v : A] ->
    (∑ Γ1 u1 v1 A1,
    [Γ1 |- u1 = v1 : A1] × (erase_ty A1 = A) × (erase_term u1 = u) × (erase_term v1 = v) × (erase_context Γ1 = Γ)).
Proof.
- intros. induction H.
    + eexists ε. constructor. constructor. simpl. auto.
    + destruct IHRuss_WfContextDecl as [? []]. apply section_ty in r. destruct r as [? [? [? []]]].
        eexists (projT4,,projT5). constructor. apply concons in w0. auto. apply inv_wfcontext_wftype in w0. destruct w0. auto.
        simpl. rewrite e1. rewrite e0. auto.

- intros. induction H.
    + apply section_ctx in r. destruct r as [? []]. eexists projT3. eexists (U n).
        constructor. constructor. auto.
        constructor. auto. auto.
    + apply section_term in r. destruct r as [? [? [? [? [? []]]]]]. eexists projT3. eexists (Decode n projT4).
        constructor. constructor. eapply wfTermConv. instantiate (1:=projT5). auto. eapply erase_inj_ty.
            apply wftype_typing_inv in t. destruct t. auto. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
            auto. 
        constructor. auto. auto.

- intros. induction H.

    (* Cas r_var0 *)
    + apply  section_ty in r. destruct r as [? [? [? []]]]. eexists (projT3,,projT4). eexists (var_term 0). eexists (weak_ty projT4).
        constructor. eapply wfVar0. auto.
        constructor. symmetry in e. rewrite e. rewrite defeq_erase_weak_ty. auto.
        constructor. auto. simpl. rewrite e0. rewrite e. auto.

      (* Cas r_VarN *)
    +  destruct IHRuss_TypingDecl as [? [? [? [? [? []]]]]]. apply section_ty in r. destruct r as [? [? [? []]]]. eexists (projT3,,projT7).
        eexists (weak_term projT4). eexists (weak_ty projT5).
        constructor. eapply weak_term_lemma. auto.
        constructor. rewrite <- defeq_erase_weak_ty. rewrite e. auto.
        constructor. rewrite <- defeq_erase_weak_term. rewrite e0. auto. 
        exact defeq_weak_var. simpl. rewrite e1. rewrite e2. auto. 

    + (* Cas r_Lambda *)
      destruct IHRuss_TypingDecl as [Γ_body [u_body [B_lifted [H_typing_body [H_erase_B [H_erase_u H_erase_ctx_body]]]]]].
      
      apply section_ty in r. destruct r as [Γ_A [A_lifted [H_wf_A [H_erase_A H_erase_ctx_A]]]].
      
      destruct Γ_body as [| A_body_head Γ_body_tail].
      * simpl in H_erase_ctx_body. discriminate.
      * simpl in H_erase_ctx_body. injection H_erase_ctx_body. intros H_eq_ctx H_eq_A.
      
      eexists Γ_A.
      eexists (Lambda A_lifted B_lifted u_body).
      eexists (Prod A_lifted B_lifted).
      
      repeat split.
      ** 
        apply wfTermLambda.
        -- exact H_wf_A.
        --
           eapply erase_inj_ctx_term.
           --- apply inv_wfcontext_typing in H_typing_body. destruct H_typing_body as [_ H_wf_source]. exact H_wf_source.
           --- apply concons. apply inv_wfcontext_wftype in H_wf_A. destruct H_wf_A as [_ H_wf_base]. exact H_wf_base. exact H_wf_A.
           --- simpl. rewrite H_erase_ctx_A H_erase_A.
               rewrite H_eq_ctx H_eq_A. reflexivity.
           --- exact H_typing_body.
           
      **
        simpl. rewrite H_erase_A H_erase_B. reflexivity.
      **
        simpl. rewrite H_erase_A H_erase_B H_erase_u. reflexivity.
      ** 
        exact H_erase_ctx_A.

    (* Cas r_App *)
    + destruct IHRuss_TypingDecl1 as [Γ_f [f_t [Prod_t [Hf_typ [H_er_Prod [H_er_f H_er_ctx_f]]]]]].
      destruct IHRuss_TypingDecl2 as [Γ_a [a_t [A_t [Ha_typ [H_er_A [H_er_a H_er_ctx_a]]]]]].

      assert (H_Bt_exists : ∑ B_t, [Γ_f ,, A_t |- B_t] × erase_ty B_t = B).
      {   assert (Hf_typbis := Hf_typ).
          apply wftype_typing_inv in Hf_typ. destruct Hf_typ as [_ Hwf_Prod_t].
          destruct Prod_t.
          - (* Cas Prod *)
            simpl in H_er_Prod. injection H_er_Prod. intros HeqB HeqA.
            apply prod_ty_inv in Hwf_Prod_t. destruct Hwf_Prod_t as [_ Hwf_B0].
            exists Prod_t2. split.
            + eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in Hwf_B0. destruct Hwf_B0. exact w0. apply concons.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto.
              apply wftype_typing_inv in Ha_typ. destruct Ha_typ.
              eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto. rewrite H_er_ctx_f. auto. auto.
              simpl. rewrite H_er_ctx_f. rewrite H_er_A. rewrite HeqA. auto. auto.
            + auto.
          - (* Cas Decode *)
            simpl in H_er_Prod. apply decode_ty_inv in Hwf_Prod_t.
            apply decode_prod_structure_from_erasure with (A:=A) (B:=B) in Hwf_Prod_t; auto.
            destruct Hwf_Prod_t as [A1 [B1 [Heq_Decode [HeqA HeqB]]]].
            apply type_defeq_inv in Heq_Decode. destruct Heq_Decode as [_ [_ Hwf_Prod]].
            apply prod_ty_inv in Hwf_Prod. destruct Hwf_Prod as [_ Hwf_B1].
            exists B1. split.
            + eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in Hwf_B1. destruct Hwf_B1. exact w0.
              apply concons. apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto.
              apply wftype_typing_inv in Ha_typ. destruct Ha_typ.
              eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto. rewrite H_er_ctx_f. auto. auto.
              simpl. rewrite H_er_ctx_f. rewrite H_er_A. rewrite HeqA. auto. auto.
            + auto.
          - (* Cas U *)
            simpl in H_er_Prod. discriminate.
      }
      destruct H_Bt_exists as [B_t [H_wf_B H_er_B]].

      eexists Γ_f.
      eexists (App A_t B_t f_t a_t).
      eexists (subst_ty a_t B_t).

      repeat split.
      -- apply wfTermApp.
         --- 
             eapply wfTermConv.
             ---- exact Hf_typ.
             ---- 
                  apply erase_inj_ty.
                  ----- apply wftype_typing_inv in Hf_typ. destruct Hf_typ; auto.
                  -----
                        apply wfTypeProd.
                        ------ apply wftype_typing_inv in Ha_typ. destruct Ha_typ; auto.
                               eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
                               apply inv_wfcontext_typing in Hf_typ. destruct Hf_typ. auto. rewrite H_er_ctx_f. auto. auto.
                        ------ exact H_wf_B.
                  ----- simpl. rewrite H_er_Prod. rewrite H_er_A H_er_B. reflexivity.
         --- eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Ha_typ. destruct Ha_typ. exact w.
             apply inv_wfcontext_typing in Hf_typ. destruct Hf_typ. auto. rewrite H_er_ctx_f. auto.
             auto.
      --
         rewrite <- defeq_erase_subst_ty. rewrite H_er_a H_er_B. reflexivity.
      -- 
         simpl. rewrite H_er_A H_er_B H_er_f H_er_a. reflexivity.
      -- exact H_er_ctx_f.

    + 
      destruct IHRuss_TypingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      apply section_conv in r. destruct r as [? [A2 [B1 [? [? []]]]]].
      eexists Γ1, u1, B1.
      split.
      * eapply wfTermConv.
        -- exact Htyp.
        -- eapply TypeTrans. instantiate (1:=A2).
           apply erase_inj_ty.
           --- apply wftype_typing_inv in Htyp. destruct Htyp. auto.
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_type. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
           --- rewrite HerA. auto. 
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_conv_ty. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
      * split. auto. split. auto. auto.

    (* Cas r_wfTermProd *)
    + destruct IHRuss_TypingDecl1 as [Γ1 [a1 [TA1 [Ha1 [HeTA1 [Hea1 HeG1]]]]]].
      destruct IHRuss_TypingDecl2 as [Γ2 [b1 [TB1 [Hb1 [HeTB1 [Heb1 HeG2]]]]]].
      eexists Γ1, (cProd n a1 b1), (U n).
      repeat split.
      * assert (HeqTA1 : [Γ1 |- TA1 = U n]). 
      {
        apply erase_inj_ty. apply wftype_typing_inv in Ha1. destruct Ha1. auto. constructor.
        apply inv_wfcontext_typing in Ha1. destruct Ha1. auto. auto.
      }
        apply wfTermConv with (1:= Ha1) in HeqTA1. constructor. auto. constructor. auto.
        assert (HeqTB1 : [Γ2 |- TB1 = U n]). 
      {
        apply erase_inj_ty. apply wftype_typing_inv in Hb1. destruct Hb1. auto. constructor.
        apply inv_wfcontext_typing in Hb1. destruct Hb1. auto. auto.
      }
      apply wfTermConv with (1:= Hb1) in HeqTB1. eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Hb1. destruct Hb1. exact w.
        constructor. apply inv_wfcontext_typing in Ha1. destruct Ha1. exact w. constructor. auto. rewrite HeG2. simpl. rewrite HeG1 Hea1. auto. auto.
      * simpl. rewrite Hea1. rewrite Heb1. reflexivity.
      * simpl. auto.

    (* Cas r_wfTermUniv *)
    + apply section_ctx in r. destruct r as [Γ1 [HwfG HeG]].
      eexists Γ1, (cU n m), (U m).
      repeat split.
      * apply wfTermcUniv; auto.
      * auto.

    (* Cas r_wfTermCumul *)
+ destruct IHRuss_TypingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      eexists Γ1, (cLift n m u1), (U m).
      repeat split.
      -- apply wfTermcLift; auto.
         eapply wfTermConv. exact Htyp. apply erase_inj_ty.
         --- apply wftype_typing_inv in Htyp; destruct Htyp; auto.
         --- apply wfTypeU. apply inv_wfcontext_typing in Htyp; destruct Htyp; auto.
         --- rewrite HerA. simpl. reflexivity.
      -- simpl. auto.
      -- simpl. auto.

- (* section_conv *)
  intros. induction H.

  (* Cas r_TypePiCong *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [HconvA [HeA [HeB HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [C1 [D1 [HconvC [HeC [HeD HeG2]]]]]].
    
    eexists Γ1, (Prod A1 C1), (Prod B1 D1).
    repeat split.
    * apply TypePiCong.
      -- (* A1 doit être bien formé *)
         apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
      -- (* A1 = B1 *)
         exact HconvA.
      -- (* C1 = D1 doit être valide dans Γ1,,A1. On l'a dans Γ2. *)
         (* On utilise erase_inj_ctx_conv_ty car les contextes s'effacent de la même manière *)
         eapply erase_inj_ctx_conv_ty.
         --- (* Γ2 est bien formé (venant de la preuve de C1=D1) *)
             apply type_defeq_inv in HconvC. destruct HconvC as [_ [HwfC _]]. apply inv_wfcontext_wftype in HwfC. destruct HwfC; exact w0.
         --- (* Γ1,,A1 est bien formé *)
             apply concons. 
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [_ HwfB1]]. apply inv_wfcontext_wftype in HwfB1. destruct HwfB1; auto.
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
         --- (* erase(Γ2) = Γ,,A = erase(Γ1,,A1) *)
             simpl. rewrite HeG2 HeG1 HeA. reflexivity.
         --- exact HconvC.
    * simpl. rewrite HeA HeC. reflexivity.
    * simpl. rewrite HeB HeD. reflexivity.
    * exact HeG1.

  (* Cas r_TypeRefl *)
  + apply section_ty in r. destruct r as [Γ1 [A1 [Hwf [HeA HeG]]]].
    eexists Γ1, A1, A1.
    repeat split; try auto.
    apply TypeRefl. exact Hwf.

  (* Cas r_TypeSym *)
  + destruct IHRuss_ConvTypeDecl as [Γ1 [A1 [B1 [Hconv [HeA [HeB HeG]]]]]].
    eexists Γ1, B1, A1.
    repeat split.
    * apply TypeSym. exact Hconv.
    * exact HeB.
    * exact HeA.
    * exact HeG.

    (* Cas r_TypeTrans *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [Hconv1 [HeA [HeB1 HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [B2 [C1 [Hconv2 [HeB2 [HeC HeG2]]]]]].
    
    eexists Γ1, A1, C1.
    repeat split; try auto.
    eapply TypeTrans.
    * exact Hconv1.
    * eapply TypeTrans. instantiate (1:=B2).
      -- apply erase_inj_ty.
         --- apply type_defeq_inv in Hconv1. destruct Hconv1 as [_ [_ HwfB1]]. exact HwfB1.
         --- apply type_defeq_inv in Hconv2. destruct Hconv2 as [_ [HwfB2 _]]. eapply erase_inj_ctx_type.
            instantiate (1:=Γ2 ). apply inv_wfcontext_wftype in HwfB2. destruct HwfB2. auto.
            apply type_defeq_inv in Hconv1. destruct Hconv1 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto.
            rewrite HeG1. auto. auto.
         --- rewrite HeB1 HeB2. reflexivity.
      -- eapply erase_inj_ctx_conv_ty.
            instantiate (1:=Γ2 ). apply type_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto.
            apply type_defeq_inv in Hconv1. destruct Hconv1 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto. rewrite HeG2. auto. auto. 

  (* Cas r_TypeUnivConv *)
  + apply section_conv_term in r.
    destruct r as [Γ1 [u1 [v1 [T1 [Hconv [HeqT [Hequ [Heqv HeqG]]]]]]]].
    
    eexists Γ1, (Decode n u1), (Decode n v1).
    repeat split.
    * apply TypeDecodeCong.
      eapply TermConv.
      -- exact Hconv.
      -- destruct T1; simpl in HeqT.
         ++ discriminate.
         ++ apply TypeSym.
            apply erase_decode_inv_univ with (t:=t).
            ** apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
               apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
               exact HwfT.
            ** symmetry. exact HeqT.
         ++ injection HeqT. intro. subst l.
            apply TypeRefl. apply wfTypeU.
            apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
            apply inv_wfcontext_typing in Hwf. destruct Hwf. exact w.
    * simpl. exact Hequ.
    * simpl. exact Heqv.
    * exact HeqG.

(* section_conv_term *)
- intros. induction H.

    + apply section_term in r0. destruct r0 as [Γ1 [t1 [B1 [Htyp_t [HeB [Het HeG1]]]]]].
    apply section_term in r1. destruct r1 as [Γ2 [a1 [A1 [Htyp_a [HeA [Hea HeG2]]]]]].
    
    
    eexists (Γ2), (App A1 B1 (Lambda A1 B1 t1) a1), (subst_term a1 t1), (subst_ty a1 B1).
    repeat split.
    * eapply TermBRed.
        -- apply wftype_typing_inv in Htyp_a. destruct Htyp_a. auto.
        --  eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Htyp_t. destruct Htyp_t. exact w.
            apply inv_wfcontext_typing in Htyp_a. destruct Htyp_a. constructor. auto. apply wftype_typing_inv in t0. destruct t0. auto.
            simpl. rewrite HeG2. rewrite HeA. auto. auto.
        -- exact Htyp_a.
    * rewrite <- defeq_erase_subst_ty. rewrite HeB Hea. reflexivity.
    * simpl. rewrite HeA HeB Het Hea. reflexivity.
    * rewrite <- defeq_erase_subst_term. rewrite Hea Het. reflexivity.
    * auto.
    

    (* Cas r_TermAppCong *)
    + apply section_conv in r. destruct r as [Γ1 [A1 [A'1 [HconvA [HeA [HeA' HeG1]]]]]].
    apply section_conv in r0. destruct r0 as [Γ2 [B1 [B'1 [HconvB [HeB [HeB' HeG2]]]]]].
    destruct IHRuss_ConvTermDecl1 as [Γ3 [f1 [g1 [Prod1 [Hconv_f [HeProd [Hef [Heg HeG3]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ4 [a1 [b1 [Ta1 [Hconv_a [HeTa [Hea [Heb HeG4]]]]]]]].

    eexists Γ1, (App A1 B1 f1 a1), (App A'1 B'1 g1 b1), (subst_ty a1 B1).
    repeat split.
    * apply TermAppCong.
        -- exact HconvA.
        -- 
        eapply erase_inj_ctx_conv_ty. apply type_defeq_inv in HconvB. destruct HconvB as [? []]. apply inv_wfcontext_wftype in w. destruct w.
        exact w1. apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto.
        simpl. rewrite HeG1. rewrite HeA. auto. auto.
        -- eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []]. apply inv_wfcontext_typing in t. destruct t.
        exact w. apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w0. destruct w0. auto. rewrite HeG3. auto.
        
        eapply TermConv. exact Hconv_f. apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfP]. exact HwfP.
        --- apply wfTypeProd. 
            apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0.  apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []].
            apply inv_wfcontext_typing in t. destruct t. auto. rewrite HeG3. auto. auto.
            apply type_defeq_inv in HconvB. destruct HconvB as [_ [HwfB _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfB. destruct HwfB. exact w0.  apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []].
            apply inv_wfcontext_typing in t. destruct t. constructor. auto. apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w1. auto.  rewrite HeG3. auto. auto. simpl. rewrite HeG3. rewrite HeA. auto. auto.
        --- simpl. rewrite HeProd. rewrite HeA HeB. reflexivity.
        -- 
        eapply TermConv. instantiate (1:=Ta1). eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_a. destruct Hconv_a as [? []].
        apply inv_wfcontext_typing in t. destruct t. exact w. apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0.
        rewrite HeG4. auto. auto. 
        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_a. destruct Hconv_a as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfT. destruct HwfT. exact w0. apply type_defeq_inv in HconvA. destruct HconvA as [? []].
        apply inv_wfcontext_wftype in w. destruct w.  auto. rewrite HeG4. auto. auto. 
        --- apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
        --- rewrite HeTa HeA. reflexivity.
    * rewrite <- defeq_erase_subst_ty. rewrite HeB Hea. reflexivity.
    * simpl. rewrite HeA HeB Hef Hea. reflexivity.
    * simpl. rewrite HeA' HeB' Heg Heb. reflexivity.
    * exact HeG1.

    (* Cas r_TermLambdaCong *)
    + apply section_conv in r0. destruct r0 as [Γ1 [A1 [A'1 [HconvA [HeA [HeA' HeG1]]]]]].
    apply section_conv in r1. destruct r1 as [Γ2 [B1 [B'1 [HconvB [HeB [HeB' HeG2]]]]]].
    destruct IHRuss_ConvTermDecl as [Γ3 [t1 [u1 [B_body [Hconv_t [HeBb [Het [Heu HeG3]]]]]]]].

    eexists Γ1, (Lambda A1 B1 t1), (Lambda A'1 B'1 u1), (Prod A1 B1).
    repeat split.
    * apply TermLambdaCong.
        -- apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
        -- exact HconvA.
        -- eapply erase_inj_ctx_conv_ty. apply type_defeq_inv in HconvB. destruct HconvB as [? []].
            apply inv_wfcontext_wftype in w. destruct w. exact w1.
            apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w.
            constructor. auto. auto. simpl. rewrite HeG1. rewrite HeA. auto. auto.
        -- eapply TermConv. instantiate (1:=B_body). eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_t.
        destruct Hconv_t as [? []]. apply inv_wfcontext_typing in t0. destruct t0. exact w. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 

        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfT. destruct HwfT. exact w0. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 
        --- apply type_defeq_inv in HconvB. destruct HconvB as [_ [HwfB _]]. 
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfB. destruct HwfB. exact w0. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 
        --- rewrite HeBb HeB. reflexivity.
    * simpl. rewrite HeA HeB. reflexivity.
    * simpl. rewrite HeA HeB Het. reflexivity.
    * simpl. rewrite HeA' HeB' Heu. reflexivity.
    * exact HeG1.

    (* Cas r_TermPiCong *)
    + destruct IHRuss_ConvTermDecl1 as [Γ1 [u1 [v1 [T1 [Hconv1 [HeqT1 [Hequ1 [Heqv1 HeqG1]]]]]]]].
      destruct IHRuss_ConvTermDecl2 as [Γ2 [u2 [v2 [T2 [Hconv2 [HeqT2 [Hequ2 [Heqv2 HeqG2]]]]]]]].

      eexists Γ1, (cProd n u1 u2), (cProd n v1 v2), (U n).
      repeat split.
      * apply TermPiCong.

        -- eapply wfTermConv.
           --- apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. exact Htyp.
           --- apply erase_inj_ty.
               ++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                 apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
               ++ apply wfTypeU. apply typing_defeq_inv in Hconv1. 
                 destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                 destruct Htyp. exact w.
               ++ rewrite HeqT1. simpl. reflexivity.

        -- eapply TermConv. exact Hconv1.
           apply erase_inj_ty.
           --- apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
               apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
           --- apply wfTypeU. apply typing_defeq_inv in Hconv1. 
               destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
               destruct Htyp. exact w.
           --- rewrite HeqT1. simpl. reflexivity.

        -- eapply erase_inj_ctx_conv_term.
           --- eapply concons.
               ++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                 apply inv_wfcontext_typing in Htyp. destruct Htyp. exact w.
               ++ eapply wfTypeDecode. eapply wfTermConv.
                 ** apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. exact Htyp.
                 ** apply erase_inj_ty.
                    +++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                        apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
                    +++ apply wfTypeU. apply typing_defeq_inv in Hconv1. 
                        destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                        destruct Htyp. exact w.
                    +++ rewrite HeqT1. simpl. reflexivity.
           --- apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Htyp _]]. 
               apply inv_wfcontext_typing in Htyp. destruct Htyp. constructor. eapply inv_wfcontext_typing.
               eapply typing_defeq_inv. exact Hconv1. constructor. eapply typing_defeq_inv. apply TermSym.
               eapply TermConv. exact Hconv1. apply erase_inj_ty. eapply wftype_typing_inv. eapply typing_defeq_inv.
               exact Hconv1. constructor. eapply inv_wfcontext_typing. eapply typing_defeq_inv. exact Hconv1. simpl. auto.
           --- simpl. rewrite HeqG1 Hequ1. rewrite <- HeqG2. reflexivity.
           --- eapply TermConv. eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []].
                apply inv_wfcontext_typing in t. destruct t. exact w. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t. destruct t. exact w. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t. apply erase_inj_ty. apply wftype_typing_inv in t. destruct t. auto. constructor. apply inv_wfcontext_typing in t.
                destruct t. auto. simpl. auto. simpl. rewrite HeqG1. rewrite Hequ1. auto. exact Hconv2.
               apply erase_inj_ty.
               ++ apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Htyp _]]. 
                 apply wftype_typing_inv in Htyp. destruct Htyp. apply wftype_typing_inv in t. destruct t. eapply erase_inj_ctx_type.
                 apply inv_wfcontext_typing in t. destruct t. exact w1. constructor.  apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t0. destruct t0. auto. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t0. apply erase_inj_ty. apply wftype_typing_inv in t0. destruct t0. auto. constructor. apply inv_wfcontext_typing in t0.
                destruct t0. auto. simpl. auto. simpl. rewrite HeqG1. rewrite Hequ1. auto. exact w0.
               ++ apply wfTypeU. apply typing_defeq_inv in Hconv2. 
                 destruct Hconv2 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                 destruct Htyp.  constructor.  apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t0. destruct t0. auto. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t0. apply erase_inj_ty. apply wftype_typing_inv in t0. destruct t0. auto. constructor. apply inv_wfcontext_typing in t0.
                destruct t0. auto. simpl. auto.
               ++ rewrite HeqT2. simpl. reflexivity.

      * simpl. subst. auto.
      * simpl. subst. auto.
      * simpl. subst. auto.

    (* Cas r_TermFunEta *)
    + apply section_term in r.
      destruct r as [Γ1 [f1 [Prod1 [Htyp_f [HeProd [Hef HeG1]]]]]].
      
      assert (∑ A1 B1, [Γ1 |- Prod1 = Prod A1 B1] × (erase_ty A1 = A) × (erase_ty B1 = B)).
      { 
          destruct Prod1; simpl in HeProd; try discriminate.
          - exists Prod1_1, Prod1_2.
            split; [| split]. 
            apply TypeRefl. apply wftype_typing_inv in Htyp_f. destruct Htyp_f; auto.
            injection HeProd; auto. injection HeProd; auto.
          - apply wftype_typing_inv in Htyp_f. destruct Htyp_f as [_ Hwf].
            apply decode_ty_inv in Hwf.
            apply decode_prod_structure_from_erasure with (A:=A) (B:=B) in Hwf; auto.
      }
      
      destruct H as [A1 [B1 [Hconv [HeA HeB]]]].

      eexists Γ1, (Lambda A1 B1 (App (weak_ty A1) (weak_ty B1) (weak_term f1) (var_term 0))), f1, (Prod A1 B1).
      repeat split.
      * apply TermFunEta. 
        eapply wfTermConv. exact Htyp_f. exact Hconv.
      * simpl. rewrite HeA HeB. reflexivity.
      * simpl. rewrite HeA HeB. rewrite <- defeq_erase_weak_term.
        rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty. 
        rewrite HeA HeB Hef. reflexivity.
      * exact Hef.
      * exact HeG1.


    (* Cas r_TermRefl *)
    + apply section_term in r. destruct r as [Γ1 [t1 [A1 [Htyp [HeA [Het HeG]]]]]].
    eexists Γ1, t1, t1, A1.
    repeat split; auto.
    apply TermRefl. exact Htyp.

    (* Cas r_ConvConv *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [t1 [t'1 [A1 [Hconv_t [HeA [Het [Het' HeG1]]]]]]]].
    apply section_conv in r. destruct r as [Γ2 [A2 [B1 [Hconv_A [HeA2 [HeB HeG2]]]]]].

    eexists Γ1, t1, t'1, B1.
    repeat split; auto.
    * eapply TermConv.
        -- exact Hconv_t.
        -- eapply TypeTrans.
        --- apply TypeSym. apply erase_inj_ty.
            ** apply type_defeq_inv in Hconv_A. destruct Hconv_A as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0. apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG2. auto. exact HwfA.
             ** apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfA1]. exact HwfA1.
            ** rewrite HeA2 HeA. reflexivity.
        --- eapply erase_inj_ctx_conv_ty.
            apply type_defeq_inv in Hconv_A. destruct Hconv_A as [? []]. apply inv_wfcontext_wftype in w. destruct w.
            exact w1. apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG2. auto. exact Hconv_A.

    (* Cas r_TermSym *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [A1 [Hconv [HeA [Heu [Hev HeG]]]]]]]].
    eexists Γ1, v1, u1, A1.
    repeat split; auto.
    apply TermSym. exact Hconv.

    (* Cas r_TermTrans *)
    + destruct IHRuss_ConvTermDecl1 as [Γ1 [t1 [t'1 [A1 [Hconv1 [HeA [Het [Het' HeG1]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ2 [t'2 [t''1 [A2 [Hconv2 [HeA2 [Het'2 [Het'' HeG2]]]]]]]].

    eexists Γ1, t1, t''1, A1.
    repeat split; auto.
    * eapply TermTrans.
        -- exact Hconv1.
        -- eapply TermTrans.
        --- apply erase_inj_term_plus with (u1 := t'2) (A1 := A2).
            ** apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [_ Hwf]]. exact Hwf.
            ** apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Hwf _]]. eapply erase_inj_ctx_term.
            apply inv_wfcontext_typing in Hwf. destruct Hwf. exact w. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG1. auto. auto.
            ** rewrite Het' Het'2. reflexivity.
            ** rewrite HeA HeA2. reflexivity.
        --- eapply erase_inj_ctx_conv_term.
            apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_typing in t0.
            destruct t0. exact w. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG1. auto. eapply TermConv. exact Hconv2.
            rewrite <- HeA in HeA2. apply erase_inj_ty. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []].
            apply wftype_typing_inv in t0. destruct t0. auto. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply wftype_typing_inv in t0. destruct t0. eapply erase_inj_ctx_type. apply inv_wfcontext_typing in t0. destruct t0.
            exact w0. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_typing in t3. destruct t3. auto.
            rewrite HeG1. auto. auto. auto. 

    (* Cas r_TermUnivCumul *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [Up [Hconv [HeUp [Heu [Hev HeG]]]]]]]].
    eexists Γ1, (cLift p n u1), (cLift p n v1), (U n).
    repeat split.
    * apply TermLiftingCong.
        -- eapply TermConv. exact Hconv.
        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT]. exact HwfT.
        --- apply wfTypeU. apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply inv_wfcontext_typing in Hwf. destruct Hwf; auto.
        --- rewrite HeUp. simpl. reflexivity.
        -- exact l.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
Qed.