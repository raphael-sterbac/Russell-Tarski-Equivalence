From Coq Require Import ssreflect.
From smpl Require Import Smpl.

Set Primitive Projections.

Definition lvl := nat.

Inductive ty : Type :=
| var_ty : nat -> ty
| Prod : ty -> ty -> ty
| Decode : lvl -> term -> ty
| U : lvl -> ty
| subst_ty : term -> ty -> ty
| weak_ty : ty -> ty
with term : Type :=
| var_term : nat -> term
| Lambda : ty -> ty -> term -> term
| App : ty -> ty -> term -> term -> term
| cProd : lvl -> term -> term -> term
| cU : lvl -> lvl -> term
| cLift : lvl -> lvl -> term -> term
| subst_term : term -> term -> term
| weak_term : term -> term.

Inductive russ_term : Type :=
| r_var_term : nat -> russ_term
| r_Prod : russ_term -> russ_term -> russ_term
| r_U : lvl -> russ_term
| r_Lambda : russ_term -> russ_term -> russ_term -> russ_term
| r_App : russ_term -> russ_term -> russ_term -> russ_term -> russ_term
| r_subst_term : russ_term -> russ_term -> russ_term
| r_weak_term : russ_term -> russ_term.

Definition ctx := list ty.

Notation "'ε'" := (@nil ty).
Notation " Γ ,, A " := (@cons ty A Γ) (at level 20, A at next level). 

Inductive in_ctx : ctx -> nat -> ty -> Type :=
| in_here (Γ : ctx) d : in_ctx (Γ,,d) 0 (weak_ty d)
| in_there (Γ : ctx) d d' n : in_ctx Γ n d -> in_ctx (Γ,,d') (S n) (weak_ty d).

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
    | wfVar {Γ} {n decl} :
        [   |- Γ ] ->
        in_ctx Γ n decl ->
        [ Γ |- var_term n : decl ]
    
(*     | wfVar0 {Γ} {A} :
        [ Γ |- A ] ->
        [ Γ,, A|- var_term 0 : (weak_ty A) ]
    | wfVarN {Γ} {n A B} :
        [Γ |- A] ->
        [Γ |- var_term n : B] ->
        [Γ ,, A |- (var_term (n+1)) : (weak_ty B)] *)
    
    
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
        [ Γ |- App (Prod A B) B f a : subst_ty a B ]
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
            [ Γ |- App (Prod A B) B (Lambda A B t) a = subst_term a t : subst_ty a B ]
    | TermPiCong {Γ} {A B C D n} :
        [ Γ |- A : U n] ->
        [ Γ |- A = B : U n ] ->
        [ Γ ,, Decode n A |- C = D : U n ] ->
        [ Γ |- cProd n A C = cProd n B D : U n ]
    | TermAppCong {Γ} {a b f g A B} :
        [ Γ |- f = g : Prod A B ] ->
        [ Γ |- a = b : A ] ->
        [ Γ |- App (Prod A B) B f a = App (Prod A B) B g b : subst_ty a B ]
    | TermLambdaCong {Γ} {t u A A' A'' B} :
        [ Γ |- A ] ->
        [ Γ |- A = A' ] ->
        [ Γ |- A = A'' ] ->
        [ Γ,, A |- t = u : B ] ->
        [ Γ |- Lambda A' B t = Lambda A'' B u : Prod A B ]
    | TermLiftingProdConv {Γ a b n p}:
        [Γ |- a: U n] ->
        [Γ,, Decode n a |- b :U n ] ->
        (n < p) ->
        [Γ |- cLift n p (cProd n a b) = cProd p (cLift n p a) (cLift n p b) : U n]
    | TermFunEta {Γ} {f A B} :
        [ Γ |- f : Prod A B ] ->
        [ Γ |- Lambda A B (App A B (weak_term f) (var_term 0)) = f : Prod A B ]
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

(* Russel Universes *)

Definition russ_ctx := list russ_term.

Notation "'εr'" := (@nil russ_term).
Notation " Γ ,,r A " := (@cons russ_term A Γ) (at level 20, A at next level). 

Inductive russ_in_ctx : russ_ctx -> nat -> russ_term -> Type :=
| r_in_here (Γ : russ_ctx) d : russ_in_ctx (Γ ,,r d) 0 (r_weak_term d)
| r_in_there (Γ : russ_ctx) d d' n : russ_in_ctx Γ n d -> russ_in_ctx (Γ ,,r d') (S n) (r_weak_term d).

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
with russ_termpingDecl : russ_ctx -> russ_term -> russ_term -> Type :=
    | r_wfVar {Γ} {n decl} :
        [   |-r Γ ] ->
        russ_in_ctx Γ n decl ->
        [ Γ |-r r_var_term n : decl ]
    (* | r_weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | r_wfTermLambda {Γ} {A B t} :
        [ Γ |-r A ] ->        
        [ Γ ,,r A |-r t : B ] -> 
        [ Γ |-r r_Lambda A B t : r_Prod A B]
    | r_wfTermApp {Γ} {f a A B} :
        [ Γ |-r f : r_Prod A B ] -> 
        [ Γ |-r a : A ] -> 
        [ Γ |-r r_App (r_Prod A B) B f a : r_subst_term a B ]
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
    | r_TermConv {Γ t A B} :
        [Γ |-r t : A] ->
        [Γ |-r A = B] ->
        [Γ |-r t: B] 
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
(* Conversion of terms *)
with Russ_ConvTermDecl : russ_ctx -> russ_term -> russ_term -> russ_term -> Type :=
    | r_TermBRed {Γ} {a t A B} :
            [ Γ |-r A ] ->
            [ Γ ,,r A |-r t : B ] ->
            [ Γ |-r a : A ] ->
            [ Γ |-r r_App (r_Prod A B) B (r_Lambda A B t) a = r_subst_term a t : r_subst_term a B ]
    | r_TermAppCong {Γ} {a b f g A B} :
        [ Γ |-r f = g : r_Prod A B ] ->
        [ Γ |-r a = b : A ] ->
        [ Γ |-r r_App (r_Prod A B) B f a = r_App (r_Prod A B) B g b : r_subst_term a B ]
    | r_TermLambdaCong {Γ} {t u A A' A'' B} :
        [ Γ |-r A ] ->
        [ Γ |-r A = A' ] ->
        [ Γ |-r A = A'' ] ->
        [ Γ ,,r A |-r t = u : B ] ->
        [ Γ |-r r_Lambda A' B t = r_Lambda A'' B u : r_Prod A B ]
    | r_TermFunEta {Γ} {f A B} :
        [ Γ |-r f : r_Prod A B ] ->
        [ Γ |-r r_Lambda A B (r_App A B (r_weak_term f) (r_var_term 0)) = f : r_Prod A B ]
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
    
where "[ Γ |-r T ]" := (Russ_WfTypeDecl Γ T)
and   "[ Γ |-r t : T ]" := (russ_termpingDecl Γ t T)
and   "[ Γ |-r A = B ]" := (Russ_ConvTypeDecl Γ A B)
and   "[ Γ |-r t = t' : T ]" := (Russ_ConvTermDecl Γ t t' T)
and   "[ |-r Γ ]" := (Russ_WfContextDecl Γ).


Inductive prod (A B : Type) : Type := | pair : A -> B -> prod A B.
Arguments pair {_ _} _ _.

Definition fst {A B} : prod A B -> A := fun '(pair a b) => a.
Definition snd {A B} : prod A B -> B := fun '(pair a b) => b.


Notation "( x , .. , y , z )" := (pair x .. (pair y z) ..) : core_scope.

Notation "x × y" := (prod x y) (at level 80, right associativity).

(* Generate induction principles for the mutually defined judgements *)

Scheme 
    Minimality for WfContextDecl Sort Type with
    Minimality for WfTypeDecl   Sort Type with
    Minimality for TypingDecl    Sort Type with
    Minimality for ConvTypeDecl  Sort Type with
    Minimality for ConvTermDecl  Sort Type.

Combined Scheme _WfDeclInduction from
    WfContextDecl_rect_nodep,
    WfTypeDecl_rect_nodep,
    TypingDecl_rect_nodep,
    ConvTypeDecl_rect_nodep,
    ConvTermDecl_rect_nodep.


Ltac polymorphise t :=
lazymatch t with
    | forall x : ?Hyp, @?T x => constr:(forall x : Hyp, ltac:(
        let T' := ltac:(eval hnf in (T x)) in let T'' := polymorphise T' in exact T''))
    | (?t1 * ?t2)%type => let t1' := polymorphise t1 in let t2' := polymorphise t2 in
        constr:(t1' × t2')
    | ?t' => t'
end.

Ltac remove_steps t :=
lazymatch t with
| _ -> ?T => remove_steps T
| forall x : ?Hyp, @?T x => constr:(fun  x : Hyp => ltac:(
    let T' := ltac:(eval hnf in (T x)) in let T'' := remove_steps T' in exact T''))
| ?t' => t'
end.

Definition _WfDeclInductionType :=
ltac:(let ind := fresh "ind" in
    pose (ind := _WfDeclInduction);
    let ind_ty := type of ind in
    exact ind_ty).

Definition WfDeclInductionType :=
ltac: (let ind := eval cbv delta [_WfDeclInductionType] zeta
    in _WfDeclInductionType in
    let ind' := polymorphise ind in
exact ind').

Lemma WfDeclInduction : WfDeclInductionType.
Proof.
intros PCon PTy PTm PTyEq PTmEq **.
pose proof (_WfDeclInduction PCon PTy PTm PTyEq PTmEq) as H.
destruct H as [?[?[? []]]].
all: try (assumption ; fail).
repeat (split;[assumption|]); assumption.
Qed.

Definition WfDeclInductionConcl :=
ltac:(
    let t := eval cbv delta [WfDeclInductionType] beta in WfDeclInductionType in
    let t' := remove_steps t in
    exact t').

Arguments WfDeclInductionConcl PCon PTy PTm PTyEq PTmEq : rename.

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

Notation "( x ; .. ; y ; z )" := (existT _ x .. (existT _ y z) ..) : core_scope.
Notation "x .π1" := (projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (projT2 _ _ x) (at level 3, format "x '.π2'").

Reserved Notation "[ × P1 & P2 ]" (at level 0).
Reserved Notation "[ × P1 , P2 & P3 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 ']' '/ '  &  P3 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 & P4 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  &  P4 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6  ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").
Reserved Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
"'[hv' [ × '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/'  P9 ']' '/ '  &  P10 ] ']'").

Variant and3 (P1 P2 P3 : Type) : Type := Times3 of P1 & P2 & P3.
Variant and4 (P1 P2 P3 P4 : Type) : Type := Times4 of P1 & P2 & P3 & P4.
Variant and5 (P1 P2 P3 P4 P5 : Type) : Type := Times5 of P1 & P2 & P3 & P4 & P5.
Variant and6 (P1 P2 P3 P4 P5 P6 : Type) : Type := Times6 of P1 & P2 & P3 & P4 & P5 & P6.
Variant and7 (P1 P2 P3 P4 P5 P6 P7 : Type) : Type := Times7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Variant and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Type) : Type := Times8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Variant and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Type) : Type := Times9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Variant and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Type) : Type := Times10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.

Notation "[ × P1 & P2 ]" := (prod P1 P2) (only parsing) : type_scope.
Notation "[ × P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ × P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ × P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.


Definition termGenData (Γ : ctx) (t : term) (T : ty): Type :=
  match t with
    | var_term n => ∑ decl, [× T = decl, WfContextDecl(Γ) & in_ctx Γ n decl]
    | Lambda A B t => ∑ A B, [× T = Prod A B, (WfTypeDecl Γ A) & (TypingDecl (Γ ,, A) t B)]
    | App A B f a => ∑ A B, [× T = subst_ty a B, (TypingDecl Γ f (Prod A B)) & (TypingDecl Γ a A)]
    | cProd l a b => [× T = U l, (TypingDecl Γ a (U l)) & (TypingDecl (Γ ,, (Decode l a)) b (U l))]
    | cU m n => [× T = U n, WfContextDecl(Γ) & (m < n)]
    | cLift m n a => [× T = U n, (TypingDecl Γ a (U m)) & (m < n)]
    | subst_term a b => unit (*TODO : mettre un vrai truc à la place ?*)
    | weak_term t => unit
  end.

Definition typeGenData (Γ : ctx) (T : ty): Type :=
    match T with
        | U n => unit
        | Decode n a => TypingDecl Γ a (U n)
        | Prod A B => [× WfTypeDecl Γ A & WfTypeDecl (Γ ,, A) B](*TODO*)
        | var_ty n => ∑ decl, [× T = decl, WfContextDecl(Γ) & in_ctx Γ n decl]
        | subst_ty a B => unit
        | weak_ty T => unit 
    end.

Ltac tea := try eassumption.
#[global] Ltac easy ::= solve [intuition eauto 3 with core crelations].

Ltac prod_splitter :=
  repeat match goal with
  | |- sigT _ => eexists
  | |- prod _ _ => split
  | |- and3 _ _ _ => split
  | |- and4 _ _ _ _ => split
  | |- and5 _ _ _ _ _ => split
  | |- _ /\ _ => split
  end.

Ltac prod_hyp_splitter :=
  repeat match goal with
    | H : ∑ _, _ |- _ => destruct H
    | H : [× _ & _] |- _ => destruct H
    | H : [× _, _ & _] |- _ => destruct H
    | H : [× _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _, _ & _] |- _ => destruct H
    | H : [× _, _, _, _, _, _, _, _ & _] |- _ => destruct H
  end.

Ltac by_prod_splitter :=
  solve [now prod_splitter].


Lemma _termGen {Γ t A} :
  [Γ |- t : A] ->
  ∑ A', (termGenData Γ t A') × ((A' = A) + [Γ |- A' = A]).
Proof.
  induction 1.
  all: try (eexists ; split ; [..|left ; reflexivity] ; cbn ; by_prod_splitter).
  + destruct IHTypingDecl1 as [? [? [-> | ]]]. destruct IHTypingDecl2 as [? [? [-> | ]]].
    * prod_splitter. cbn. eexists. eexists. prod_splitter. auto. exact H. exact H0. auto.
    * prod_splitter. cbn. eexists. eexists. prod_splitter. auto. exact H. exact H0. auto.
    * prod_splitter. cbn. eexists. eexists. prod_splitter. auto. exact H. exact H0. auto.
  +  destruct IHTypingDecl as [? [? [-> | ]]].
    * prod_splitter; tea; now right.
    * prod_splitter; tea; right. eapply TypeTrans. exact c0. exact c.
Qed.


(* ----- Admitted Lemmas ---- *)
Lemma substitution_lemma {Γ A B a} :
    [ Γ ,, A |- B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- subst_ty a B ].
Proof.
Admitted.

Lemma weak_cong {Γ A B} :
    [Γ |- A = B] ->
    [Γ |- weak_ty A = weak_ty B].
Proof.
Admitted.

Lemma PiInj Γ A B A' B': 
    [Γ |- Prod A B = Prod A' B'] ->
    [Γ |- A = A'] × [Γ |- B = B'].
Proof.
Admitted.  

Lemma UInj Γ k l:
    [Γ |- U k = U l] ->
    k = l.
Proof.
Admitted.

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

Lemma code_univ_inv Γ k l n:
    [Γ |- cU k l : U n] ->
    l = n.
Proof. Admitted.

Lemma lift_inv Γ k l n u:
    [Γ |- cLift k l u : U n] ->
    l = n × k < l × [Γ |- u : U k].
Proof. Admitted.

Lemma code_prod_inv Γ l n a b:
    [Γ |- cProd l a b : U n] ->
    l = n × [Γ |- a : U l] × [Γ,,(Decode l a) |- b : U l].
Proof. Admitted.

Lemma inv_wfcontext_wftype Γ A:
    [Γ |- A] -> [Γ |- A] × [ |- Γ].
Proof. Admitted.

Lemma inv_wfcontext_typing Γ a A:
    [Γ |- a: A] -> [Γ |- a: A] × [ |- Γ].
Proof. Admitted.

(* TODO : Preuve des lemmes d'inv

Supposer lemmes de cohesion ? Pi A B != U n par ex. Permet de se débarasser de la règle embêtante
dans les inversions (~ elim des coupures). *)


(* ----- Lemmes de modifications ----*)
Lemma conv_hypothesis_wftype {Γ A B C}:
    [Γ,,A |- C] ->
    [Γ |- A = B] ->
    [Γ,,B |- C].
Proof.
Admitted.

Lemma conv_hypothesis_typing {Γ a A B C}:
    [Γ,,A |- a: C] ->
    [Γ |- A = B] ->
    [Γ,,B |- a : C].
Proof.
Admitted.


(* ----- Fonctions d'effacement ----*)
Fixpoint erase_term (t: term) : russ_term :=
    match t with
        | var_term n => r_var_term n 
        | Lambda A B b => r_Lambda (erase_ty A) (erase_ty B) (erase_term b)
        | App A B c a => r_App (erase_ty A) (erase_ty B) (erase_term c) (erase_term a)
        | subst_term a b => r_subst_term (erase_term a) (erase_term b)
        | weak_term t => r_weak_term (erase_term t)
        | cU n m => r_U n
        | cProd l a b => r_Prod (erase_term a) (erase_term b)
        | cLift n m t => (erase_term t)
    end
with erase_ty (A: ty): russ_term :=
    match A with
        | Prod A B => r_Prod (erase_ty A) (erase_ty B)
        | U n => r_U n
        | var_ty n => r_var_term n
        | Decode n t => (erase_term t)
        | subst_ty t A => r_subst_term (erase_term t) (erase_ty A)
        | weak_ty A => r_weak_term (erase_ty A)
    end.

Fixpoint erase_context (Γ : ctx): russ_ctx := 
    match Γ with
    | nil => nil
    | cons a Γ' => cons (erase_ty a) (erase_context Γ')
    end.

Lemma product_wf_ty {Γ A B} : [Γ |-r A] -> [ Γ ,,r A |-r B ] -> [Γ |-r r_Prod A B].
Proof.
    (*TODO : utiliser les univers pour retrouver le type produit quand on a seulement les jugements de typage *)
Admitted.

(* ----- Lemme de correction de l'effacement ----- *)
Lemma erasure_correction_wf_ty {Γ A} : [Γ |- A] -> [(erase_context Γ) |-r (erase_ty A)]
with erasure_correction_typing {Γ a A} : [Γ |- a : A] -> [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]
with erasure_correction_conversion {Γ A B} : [Γ |- A = B] -> [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]
with ctx_formation_to_russ {Γ} : [ |- Γ ]  ->  [ |-r erase_context Γ]
with in_ctx_in_russ_ctx {Γ n decl} :  in_ctx Γ n decl -> russ_in_ctx (erase_context Γ) n (erase_ty decl).
Proof.
- induction 1.
    + simpl; constructor; apply ctx_formation_to_russ; exact w.
    + simpl; apply product_wf_ty; auto.
    + simpl; apply erasure_correction_typing in t; apply r_wfTypeUniv in t; exact t.
- induction 1.
    + simpl; constructor; apply ctx_formation_to_russ in w; auto.
    + simpl; simpl in IHTypingDecl1; simpl in IHTypingDecl2; constructor; auto.
    + simpl; constructor; auto.
    + simpl; simpl in IHTypingDecl. apply r_wfTermCumul with (1:=l0) in IHTypingDecl; auto.
    + simpl; simpl in IHTypingDecl; constructor; auto.
    + simpl; simpl in IHTypingDecl1; simpl in IHTypingDecl2; constructor; auto.
    + apply erasure_correction_conversion in c; apply r_TermConv with (1:=IHTypingDecl); exact c.
- induction 1.
    + simpl; constructor; auto.
    + simpl; apply TypeDecodeCong in c; apply erasure_correction_conversion in c; simpl in c; auto.
    + simpl; apply r_TypeRefl; constructor; apply ctx_formation_to_russ; auto.
    + simpl. constructor. apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. exact t.
    + simpl. constructor. apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. exact t. constructor.
        apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. auto. apply erasure_correction_typing in t0. simpl in t0.
        apply r_wfTypeUniv in t0. constructor. auto.
    + simpl; constructor; auto.
    + simpl. eapply r_TypeTrans. exact IHConvTypeDecl1. exact IHConvTypeDecl2.
    + simpl; constructor; auto.  
- induction 1.
    all: try (constructor; auto).
- induction 1.
    all: try (constructor; auto).
Admitted. (* TODO : Problème de decreasing argument avec le Qed. => Induction mutuelle !!*)


(* ----- Lemmes utiles ----- *)
Lemma erase_decode_inv_univ t:
    forall Γ l n,
    [Γ |- Decode l t] ->
    r_U n = erase_term t ->
    [Γ |- U n = Decode l t].
Proof.
induction t.
    all: try (intros; simpl in H0; contradict H0; congruence).
    - intros. apply inv_wfcontext_wftype in H. destruct H.
        simpl in H0; apply decode_ty_inv in w. apply code_univ_inv in w. rewrite w; inversion H0.
        apply TypeDecodeConv with (n := l) (m := l1) in w0. exact w0.
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


(* ----- Lemme principal ----*)
Lemma erase_inj_ty {Γ A B} : [Γ |- A] -> [Γ |- B] -> (erase_ty A = erase_ty B) -> [Γ |- A = B]
with erase_inj_term {Γ u0 u1 A0 A1 (* v0 v1 n0 n1 k *)} :
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
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
    + shelve. (*TODO : var_ty ? *)
    + destruct a.
        all: try(simpl in H0; contradict H0; congruence).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
    + simpl in H0. apply decode_ty_inv in H. apply erase_inj_term with (1:=t) (2:=H) in H0.
        destruct H0. apply UInj in c0. rewrite c0. apply TypeDecodeCong. rewrite c0 in c. auto.
        (* TODO : Modifier la preuve avec les deux cas de erase_inj_term *) 

    + simpl in H0. apply TypeSym. apply erase_decode_inv_univ. apply wfTypeDecode. auto. auto.
    + shelve. (* TODO : subst_ty ? *)
    + shelve. (*TODO : weak_ty ? *)

(* Terms *)
- induction u0.
    + intros; destruct u1. (* u0 = var_term n *)
        all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1; inversion H1. constructor. constructor. rewrite H3 in H. auto.
         inversion H. inversion H0.
            (*TODO : Remplacer avec les bonnes règles pour les variables *)
            +++ rewrite H3 in H6. inversion H11. inversion H6. symmetry in H16. rewrite H16 in H13.
                inversion H13. apply weak_cong. apply TypeRefl.