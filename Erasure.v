From Stdlib Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.
Require Import RussellTarskiEquivalence.Utils.

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

