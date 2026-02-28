From Stdlib Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.


(* --------- Axioms --------- *)

(* --- Subtitution and weakenings (Should be provable using AutoSubst) --- *)

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

Axiom defeq_weak_var: forall {n}, r_weak_term (r_var_term n) = r_var_term (n + 1). 

Axiom weak_ty_prod: forall {A B},
     Prod (weak_ty A) (weak_ty B) = weak_ty (Prod A B).



(* --- Normalisation Axioms ---*)

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


(* To make the notation simpler in erase_inj_term *)
Axiom lift_same: forall {u Γ l},
    [Γ |- u : U l] ->
    [Γ |- u = cLift l l u : U l].
(*TODO :  Remplacer par vraie notation ? *)


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
    
    (* Cons : *)
    + inversion w; subst. constructor; auto. constructor. auto.
    
    (* Prod *)
    + 
      split.
      *
        eapply IHWfTypeDecl1; reflexivity.
      * 
        apply wfTypeProd.
        ** auto.
        ** assumption.

    (* Decode *)
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
Qed.  (* TODO : Decreasing argument *)



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

  (* wfVar0 : var 0 *)
  -
    destruct Δ0. simpl in x; try discriminate.
    simpl in x0. injection x0. intros; subst.
    simpl.
    apply TypeRefl. 
    apply weak_lemma. assumption.
    simpl in x. contradict x. auto.

  (* wfVarN : var (n+1) *)
  - destruct Δ0.
        * simpl in x. contradict x. lia.
        * simpl in x. simpl in x0. inversion x0. simpl. 
        specialize (IHTypingDecl Δ0 Γ'0 A0). simpl in IHTypingDecl. rewrite H2 in IHTypingDecl. specialize (IHTypingDecl JMeq_refl).
        eapply weak_cong in IHTypingDecl. exact IHTypingDecl. simpl.  assert (n = length Δ0) by lia. rewrite H0. auto.

  (* Conv : *)
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

    (* 2. wfVarN : *)
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

    (* 3. TermConv : *)
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

  (* 1. n = 0 *)
  - apply variable_zero_inv in H1.
    destruct H1 as [Γ1 [B1 [HeqA1 [HeqG1 Hwf1]]]].
    apply variable_zero_inv in H2.
    destruct H2 as [Γ2 [B2 [HeqA2 [HeqG2 Hwf2]]]].
    
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqB HeqCtx. subst.
    
    eapply TypeTrans.
    + exact HeqA1.
    + apply TypeSym. exact HeqA2.

  (* 2. n = S n *)
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



(* ----- Lemmes utiles sur les niveaux ----- *)


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


(* Utilites using lift_same as a notation *)
(*TODO : supprimer et remplacer par une vraie notation ? *)
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