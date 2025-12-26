Require Import Ast unscoped core.

Definition ctx := list ty.

Notation "'ε'" := (@nil ty).
Notation " Γ ,, A " := (@cons ty A Γ) (at level 20, A at next level).

Declare Scope asubst_scope.
Delimit Scope asubst_scope with asub.

Arguments funcomp {X Y Z}%_type_scope (g f)%_function_scope.

Notation "f >> g" := (funcomp g f) (at level 50) : function_scope.

Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : asubst_scope.

Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s ⟨ xi1 ⟩") : asubst_scope.
(* Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : function_scope. *)

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : asubst_scope.

Notation "s [ t ]⇑" := (subst_term (scons t (shift >> var_term)) s) (at level 7, left associativity, format "s '/' [ t ]⇑") : asubst_scope.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : asubst_scope.

Notation "↑" := (shift) : asubst_scope.

#[global] Open Scope asubst_scope.

Notation "'eta_expand' f" := (App f⟨↑⟩ (var_term 0)) (at level 40, only parsing).

#[global] Instance Ren1_subst {Y Z : Type} `{Ren1 (nat -> nat) Y Z} :
  (Ren1 (nat -> nat) (nat -> Y) (nat -> Z)) :=
  fun ρ σ i => (σ i)⟨ρ⟩.

Arguments ren1 {_ _ _}%_type_scope {Ren1} _ !_/.
(* Ideally, we'd like Ren_term to not be there, and ren_term to be directly the Ren1 instance… *)
Arguments Ren_term _ _ /.
Arguments Ren1_subst {_ _ _} _ _/.

Inductive in_ctx : ctx -> nat -> term -> Type :=
  | in_here (Γ : ctx) d : (in_ctx (Γ,,d) 0 (d⟨↑⟩))
  | in_there (Γ : ctx) d d' n : in_ctx Γ n d -> in_ctx (Γ,,d') (S n) (ren_term shift shift d).

Inductive WfContextDecl : context -> Type :=
    | connil : [ |- ε ]
    | concons {Γ A} : 
        [ |- Γ ] -> 
        [ Γ |- A ] -> 
        [ |-  Γ ,, A]
(** **** Type well-formation *)
with WfTypeDecl  : context -> ty -> Type :=
    | wfTypeU {Γ} : 
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
with TypingDecl : context -> term -> ty -> Type :=
    | wfVar {Γ} {n decl} :
        [   |- Γ ] ->
        in_ctx Γ n decl ->
        [ Γ |- var_term n : decl ]
    (* | weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | wfTermcProd {Γ} {a b n} :
        [Γ |- a : U n]
        -> [Γ |- Decode n a]
        -> [Γ ,, Decode n a |- b : U n]
        [ Γ |- cProd n a b : U n]
    | wfTermcUniv {Γ} {n m} :
        [   |- Γ] ->
        [Γ |- cU m n : U n] (*TODO : add m<n*)
    | wfTermcLift {Γ} {n m a} :
        [Γ |- a : U n] ->
        [Γ |- cLift m n a : U n] (*TODO : m<n*)
    | wfTermLambda {Γ} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, A |- t : B ] -> 
        [ Γ |- Lambda A B t : Prod A B]
    | wfTermApp {Γ} {f a A B} :
        [ Γ |- f : Prod A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- App (Prod A B) B f a : B[a..] ]
    | wfTermConv {Γ} {t A B} :
        [ Γ |- t : A ] -> 
        [ Γ |- A = B ] -> 
        [ Γ |- t : B ]
(** **** Conversion of types *)
with ConvTypeDecl : context -> ty -> ty  -> Type :=  
    | TypePiCong {Γ} {A B C D} :
        [ Γ |- A] ->
        [ Γ |- A = B] ->
        [ Γ ,, A |- C = D] ->
        [ Γ |- Prod A C = Prod B D]
    | TypeRefl {Γ} {A} : 
        [ Γ |- A ] ->
        [ Γ |- A = A]
    | TypeTrans {Γ} {A B C} :
        [ Γ |- A = B] ->
        [ Γ |- A = C] ->
        [ Γ |- B = C]
(** **** Conversion of terms *)
with ConvTermDecl : context -> term -> term -> term -> Type :=
    | TermBRed {Γ} {a t A B} :
            [ Γ |- A ] ->
            [ Γ ,, A |- t : B ] ->
            [ Γ |- a : A ] ->
            [ Γ |- tApp (tLambda A t) a = t[a..] : B[a..] ]
    | TermPiCong {Γ} {A B C D} :
        [ Γ |- A : U] ->
        [ Γ |- A = B : U ] ->
        [ Γ ,, A |- C = D : U ] ->
        [ Γ |- tProd A C = tProd B D : U ]
    | TermAppCong {Γ} {a b f g A B} :
        [ Γ |- f = g : tProd A B ] ->
        [ Γ |- a = b : A ] ->
        [ Γ |- tApp f a = tApp g b : B[a..] ]
    | TermLambdaCong {Γ} {t u A A' A'' B} :
        [ Γ |- A ] ->
        [ Γ |- A = A' ] ->
        [ Γ |- A = A'' ] ->
        [ Γ,, A |- t = u : B ] ->
        [ Γ |- tLambda A' t = tLambda A'' u : tProd A B ]
    | TermFunEta {Γ} {f A B} :
        [ Γ |- f : tProd A B ] ->
        [ Γ |- tLambda A (eta_expand f) = f : tProd A B ]
    | TermReflCong {Γ A A' x x'} :
      [Γ |- A = A'] ->
      [Γ |- x = x' : A] ->
      [Γ |- tRefl A x = tRefl A' x' : tId A x x]
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
    | TypeTrans {Γ} {A B C} :
        [Γ |- A = B] ->
        [Γ |- A = C] ->
        [Γ |- B = C]

    | TypeRefl {Γ} {A} :
        [Γ |- A] ->
        [Γ |- A = A]
    
where "[   |- Γ ]" := (WfContextDecl Γ)
and   "[ Γ |- T ]" := (WfTypeDecl Γ T)
and   "[ Γ |- t : T ]" := (TypingDecl Γ T t)
and   "[ Γ |- A = B ]" := (ConvTypeDecl Γ A B)
and   "[ Γ |- t = t' : T ]" := (ConvTermDecl Γ T t t').