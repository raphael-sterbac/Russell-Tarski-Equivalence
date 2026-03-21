From Stdlib Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.
Require Import RussellTarskiEquivalence.Utils.

(*  Erasure function *)
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

(* ----- Erasure of substitutions lemmas ----- *)

Scheme ty_rect_mut_erase := Induction for ty Sort Type
with term_rect_mut_erase := Induction for term Sort Type.

Combined Scheme mut_ind_ty_term_erase from ty_rect_mut_erase, term_rect_mut_erase.

Lemma defeq_erase_weak_mutual :
  (forall A, r_weak_term (erase_ty A) = erase_ty (weak_ty A)) *
  (forall t, r_weak_term (erase_term t) = erase_term (weak_term t)).
Proof.
  apply mut_ind_ty_term_erase; intros.
  
  - rewrite <- weak_ty_prod. simpl. 
    rewrite r_weak_term_Prod.
    rewrite H H0. auto.
  - rewrite weak_ty_Decode. simpl.
    rewrite H. auto.
  - rewrite weak_ty_U. simpl. 
    apply r_weak_term_U.
  

  - rewrite weak_term_var. simpl. 
    apply defeq_weak_var.
  - rewrite weak_term_Lambda. simpl.
    rewrite r_weak_term_Lambda.
    rewrite H H0 H1. auto.
  - rewrite weak_term_App. simpl.
    rewrite r_weak_term_App.
    rewrite H H0 H1 H2. auto.
  - rewrite weak_term_cProd. simpl.
    rewrite r_weak_term_Prod.
    rewrite H H0. auto.
  - rewrite weak_term_cU. simpl. 
    apply r_weak_term_U.
  - rewrite weak_term_cLift. simpl.
    apply H.
Qed.

Lemma defeq_erase_weak_ty : forall {A}, r_weak_term (erase_ty A) = erase_ty (weak_ty A).
Proof.
  intros A. apply (fst defeq_erase_weak_mutual).
Qed.

Lemma defeq_erase_weak_term : forall {t}, r_weak_term (erase_term t) = erase_term (weak_term t).
Proof.
  intros t. apply (snd defeq_erase_weak_mutual).
Qed.

Lemma defeq_erase_subst_mutual :
  (forall A a, r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A)) *
  (forall t a, r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t)).
Proof.
  apply mut_ind_ty_term_erase; intros.
  
  - rewrite subst_ty_Prod. simpl. 
    rewrite r_subst_term_Prod.
    rewrite H. 
    rewrite defeq_erase_weak_term. 
    rewrite H0. 
    reflexivity.
  - rewrite subst_ty_Decode. simpl.
    rewrite H. reflexivity.
  - rewrite subst_ty_U. simpl. 
    apply r_subst_term_U.
  
  - destruct n.
    + rewrite subst_term_var_0. simpl. 
      rewrite r_subst_term_var_0. reflexivity.
    + rewrite subst_term_var_S. simpl. 
      rewrite r_subst_term_var_S. reflexivity.
  - rewrite subst_term_Lambda. simpl.
    rewrite r_subst_term_Lambda.
    rewrite H.
    rewrite defeq_erase_weak_term.
    rewrite H0 H1.
    reflexivity.
  - rewrite subst_term_App. simpl.
    rewrite r_subst_term_App.
    rewrite H H1 H2.
    rewrite defeq_erase_weak_term.
    rewrite H0.
    reflexivity.
  - rewrite subst_term_cProd. simpl.
    rewrite r_subst_term_Prod.
    rewrite H.
    rewrite defeq_erase_weak_term.
    rewrite H0.
    reflexivity.
  - rewrite subst_term_cU. simpl. 
    apply r_subst_term_U.
  - rewrite subst_term_cLift. simpl.
    apply H.
Qed.

Lemma defeq_erase_subst_ty : forall {a A}, r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A).
Proof.
  intros a A. apply (fst defeq_erase_subst_mutual).
Qed.

Lemma defeq_erase_subst_term : forall {a t}, r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t).
Proof.
  intros a t. apply (snd defeq_erase_subst_mutual).
Qed.

(* Correction of erasure  *)

Scheme wf_ctx_rect := Induction for WfContextDecl Sort Type
  with wf_ty_rect := Induction for WfTypeDecl Sort Type
  with typing_rect := Induction for TypingDecl Sort Type
  with conv_ty_rect := Induction for ConvTypeDecl Sort Type
  with conv_term_rect := Induction for ConvTermDecl Sort Type.

Combined Scheme mut_ind_erasure_rect from 
  wf_ctx_rect, wf_ty_rect, typing_rect, conv_ty_rect, conv_term_rect.

Theorem erasure_correction_mutual :
  (forall (Γ : ctx) (H : [ |- Γ ]), [ |-r erase_context Γ]) *
  ((forall (Γ : ctx) (A : ty) (H : [Γ |- A]), [(erase_context Γ) |-r (erase_ty A)]) *
  ((forall (Γ : ctx) (a : term) (A : ty) (H : [Γ |- a : A]), [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]) *
  ((forall (Γ : ctx) (A B : ty) (H : [Γ |- A = B]), [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]) *
  (forall (Γ : ctx) (a b : term) (A : ty) (H : [Γ |- a = b : A]), [(erase_context Γ) |-r (erase_term a) = (erase_term b) : (erase_ty A)])))).
Proof.
  apply mut_ind_erasure_rect.

  (* WfContextDecl *)
  - simpl. constructor.
  - simpl. intros. apply r_concons; assumption.

  (* WfTypeDecl *)
  - intros. simpl. constructor. assumption.
  - intros. simpl. apply product_wf_ty; assumption.
  - intros. simpl. eapply r_wfTypeUniv. simpl in H. exact H.

  (* TypingDecl *)
  - intros. simpl. eapply r_wfTermConv. apply r_wfVar0. assumption. rewrite <- defeq_erase_weak_ty. apply r_TypeRefl.
    eapply r_weak_lemma. auto.
  - intros. simpl. eapply r_wfTermConv. eapply r_wfVarN. assumption. simpl in H0. exact H0. rewrite <- defeq_erase_weak_ty. apply r_TypeRefl.
    eapply r_weak_lemma. auto.
  - intros. simpl. constructor; assumption.
  - intros. simpl. constructor. assumption. assumption.
  - intros. simpl. destruct (Nat.eq_dec m l) as [H_eq | H_neq].
    + subst. auto.
    + assert (H_lt : m < l). lia. apply r_wfTermCumul with (1:=H_lt). assumption.  
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_wfTermConv. apply r_wfTermApp. assumption. assumption. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_wftype_typing_inv in H. destruct H.
    simpl in r0. apply r_prod_ty_inv in r0. destruct r0. exact r1. exact H0.
  - intros. simpl. eapply r_wfTermConv. exact H. assumption.

  (* -ConvTypeDecl*)
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_TypeUnivConv. exact H.
  - intros. simpl. eapply r_TypeUnivConv. apply r_TermRefl. eapply r_wfTermUniv. assumption. exact l.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. simpl in H. exact H.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. eapply r_wfTermProd. simpl in H. exact H. simpl in H0. exact H0.
  - intros. simpl. apply r_TypeRefl. assumption.
  - intros. simpl. eapply r_TypeTrans; eauto.
  - intros. simpl. apply r_TypeSym. assumption.

  (* ConvTermDecl *)
  - intros. simpl. eapply r_ConvConv. rewrite <- defeq_erase_subst_term. eapply r_TermBRed. auto. simpl in H0; auto. auto. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_wftype_typing_inv in H0. destruct H0. simpl in r0. exact r0. exact H1.
  - intros. simpl. apply r_TermPiCong.  simpl in H; exact H.  simpl in H0; exact H0. simpl in H1; exact H1.
  - intros. simpl. eapply r_ConvConv. apply r_TermAppCong; assumption. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_type_defeq_inv in H0. destruct H0 as [? []].
    simpl in r0. exact r0. apply r_typing_defeq_inv in H2. destruct H2 as [? []]. auto. 
  - intros. simpl. apply r_TermLambdaCong; assumption. 
  - intros. simpl. destruct (Nat.eq_dec p n) as [H_eq | H_neq].
    + subst. apply r_TermPiCong. auto. apply r_TermRefl. auto. apply r_TermRefl. auto.
    + assert (H_lt : p < n). lia. eapply r_TermUnivCumul. instantiate (1:=p). apply r_TermRefl. apply r_wfTermProd. all: auto.
  - intros. simpl. apply r_TermRefl. apply r_wfTermUniv. auto. lia. 
  - intros. simpl. apply r_TermRefl. destruct (Nat.eq_dec n l) as [H_eq | H_neq].
    + subst. auto.
    + assert (H_lt: n < l). lia. eapply r_wfTermCumul. exact H_lt. auto.
  - intros. simpl. destruct (Nat.eq_dec n p) as [H_eq | H_neq].
    + subst. auto. 
    + eapply r_TermUnivCumul. simpl in H. exact H. lia.
  - intros. simpl. apply r_TermRefl. auto.
  - intros. simpl. 
    rewrite <- defeq_erase_weak_term.  
    rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty.
    apply r_TermFunEta. assumption.
  - intros. simpl. apply r_TermRefl. assumption.
  - intros. simpl. eapply r_ConvConv; eauto.
  - intros. simpl. apply r_TermSym; assumption.
  - intros. simpl. eapply r_TermTrans; eauto.
Qed.

Definition ctx_formation_to_russ {Γ} (H : [ |- Γ ]) := 
  (fst erasure_correction_mutual) Γ H.

Definition erasure_correction_wf_ty {Γ A} (H : [Γ |- A]) := 
  (fst (snd erasure_correction_mutual)) Γ A H.

Definition erasure_correction_typing {Γ a A} (H : [Γ |- a : A]) := 
  (fst (snd (snd erasure_correction_mutual))) Γ a A H.

Definition erasure_correction_conversion {Γ A B} (H : [Γ |- A = B]) := 
  (fst (snd (snd (snd erasure_correction_mutual)))) Γ A B H.

Definition erasure_correction_conv_typing {Γ a b A} (H : [Γ |- a = b : A]) := 
  (snd (snd (snd (snd erasure_correction_mutual)))) Γ a b A H.

