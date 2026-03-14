Fixpoint erase_inj_ty_fix (A : ty) {struct A} :
  forall Γ B, [Γ |- A] -> [Γ |- B] -> (erase_ty A = erase_ty B) -> [Γ |- A = B]
with erase_inj_term_fix (u0 : term) {struct u0} :
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
  (* ----- pour erase_inj_ty_fix ----- *)
  - destruct A as [A1 A2 | l a | n].
    + (* A = Prod A1 A2 *)
      intros Γ B H_A H_B Herase; destruct B; try (simpl in Herase; contradict Herase; congruence).
      * (* B = Prod *)
        simpl in Herase. injection Herase; intros Heq2 Heq1.
        apply TypePiCong.
        -- apply prod_ty_inv in H_A; destruct H_A. auto.
        -- eapply erase_inj_ty_fix. apply prod_ty_inv in H_A; destruct H_A; eauto. apply prod_ty_inv in H_B; destruct H_B; eauto. auto.
        -- eapply erase_inj_ty_fix. apply prod_ty_inv in H_A; destruct H_A; eauto.
           eapply conv_hypothesis_wftype. instantiate (1:=B1). apply prod_ty_inv in H_B; destruct H_B; eauto.
           eapply erase_inj_ty_fix. apply prod_ty_inv in H_B; destruct H_B; eauto. apply prod_ty_inv in H_A; destruct H_A; eauto.  auto.
           auto.
      * (* B = Decode *)
        simpl in Herase. apply erase_decode_inv_prod; auto.
    
    + (* A = Decode l a *)
      intros Γ B H_A H_B Herase; destruct B; try (simpl in Herase; contradict Herase; congruence).
      * (* B = Prod *)
        simpl in Herase. apply TypeSym. apply erase_decode_inv_prod; auto.
      * (* B = Decode l0 t *)
        simpl in Herase. apply decode_ty_inv in H_A. apply decode_ty_inv in H_B.
        assert (H_term := erase_inj_term_fix a Γ t _ _ H_A H_B Herase).
        destruct H_term as [[Heq Hty] | Hlift].
        -- apply UInj in Hty. subst l0. apply TypeDecodeCong. exact Heq.
        -- destruct Hlift as [l0' [l1' [k [v0 [v1 [HUl0 [HUl1 [Hlift_a [Hlift_t Heq_v]]]]]]]]].
           apply UInj in HUl0. apply UInj in HUl1. subst l0' l1'.
           eapply TypeTrans. instantiate (1:= Decode l (cLift k l v0)). apply TypeDecodeCong. exact Hlift_a.
           eapply TypeTrans. instantiate (1:= Decode k v0). apply TypeSym. apply TypeDecodeLiftConv.
           apply typing_defeq_inv in Heq_v; destruct Heq_v as [_ [Hwf _]]; exact Hwf.
           apply typing_defeq_inv in Hlift_a; destruct Hlift_a as [_ [_ Hwf]]; apply lift_inv in Hwf; destruct Hwf as [_ [Hlt _]]; exact Hlt.
           eapply TypeTrans. instantiate (1:= Decode k v1). apply TypeDecodeCong. exact Heq_v.
           eapply TypeTrans. instantiate (1:= Decode l0 (cLift k l0 v1)). apply TypeDecodeLiftConv.
           apply typing_defeq_inv in Heq_v; destruct Heq_v as [_ [_ Hwf]]; exact Hwf.
           apply typing_defeq_inv in Hlift_t; destruct Hlift_t as [_ [_ Hwf]]; apply lift_inv in Hwf; destruct Hwf as [_ [Hlt _]]; exact Hlt.
           apply TypeSym. apply TypeDecodeCong. exact Hlift_t.
      * (* B = U l0 *)
        simpl in Herase. apply TypeSym. apply erase_decode_inv_univ; auto.

    + (* A = U n *)
      intros Γ B H_A H_B Herase; destruct B; try (simpl in Herase; contradict Herase; congruence).
      * (* B = Decode *)
        simpl in Herase. apply erase_decode_inv_univ; auto.
      * (* B = U n0 *)
        simpl in Herase. injection Herase. intro. subst. apply TypeRefl. auto.

  (* ----- erase_inj_term_fix ----- *)
  - destruct u0; intros Γ u1 A0 A1 H_u0 H_u1 Herase.
    
    + (* u0 = var_term n *)
      destruct u1; try (simpl in Herase; contradict Herase; congruence).
      eapply erase_var_inv; eauto.
      eapply erase_var_inv; eauto.
      
    + (* u0 = Lambda A B u0 *)
      destruct u1; try(simpl in Herase; contradict Herase; congruence).
    * (* u1 = Lambda *)
        simpl in Herase. injection Herase; intros Heq_u Heq_B Heq_A.
        apply lambda_inv in H_u0. destruct H_u0 as [H_A0 H_u0].
        apply lambda_inv in H_u1. destruct H_u1 as [H_A1 H_u1].
        
        apply wftype_typing_inv in H_u0. destruct H_u0 as [H_u0 Hwf_B0].
        apply wftype_typing_inv in H_u1. destruct H_u1 as [H_u1 Hwf_B1].
        
        apply wftype_hypothesis_inv in Hwf_B0. destruct Hwf_B0 as [Hwf_A0 Hwf_B0].
        apply wftype_hypothesis_inv in Hwf_B1. destruct Hwf_B1 as [Hwf_A1 Hwf_B1].
        
        apply erase_inj_ty_fix with (1:=Hwf_A0) (2:= Hwf_A1) in Heq_A.
        assert (H_A_eq := Heq_A).
        assert (H_A_eq2 := Heq_A).
        
        apply conv_hypothesis_typing with (1:= H_u0) in Heq_A.
        apply erase_inj_term_fix with (1:=Heq_A) (2:= H_u1) in Heq_u.
        
        apply conv_hypothesis_wftype with (1:= Hwf_B0) in H_A_eq.
        apply erase_inj_ty_fix with (1:= H_A_eq) (2:=Hwf_B1) in Heq_B.
        
        destruct Heq_u as [[Heq_term H_B_eq] | Hlift].
        -- apply inl. split.
           ++ (* Preuve de Lambda = Lambda : A0 *)
              assert (Hu0_u1_t : [Γ,, t |- u0 = u1 : t0]).
              { eapply conv_hypothesis_term_eq. exact Heq_term. apply TypeSym. exact H_A_eq2. }
              assert (Heq_B_t : [Γ,, t |- t0 = t2]).
              { eapply conv_hypothesis_type_eq. exact Heq_B. apply TypeSym. exact H_A_eq2. }
              eapply TermConv. instantiate (1:=Prod t t0).
              ** apply TermLambdaCong.
                 --- exact Hwf_A0.
                 --- exact H_A_eq2.
                 --- exact Heq_B_t.
                 --- exact Hu0_u1_t.
              ** apply TypeSym. exact H_A0.
           ++ (* Preuve de A0 = A1 *)
              eapply TypeTrans. exact H_A0.
              eapply TypeTrans. 2: { apply TypeSym. exact H_A1. }
              assert (Heq_B_t : [Γ,, t |- t0 = t2]).
              { eapply conv_hypothesis_type_eq. exact Heq_B. apply TypeSym. exact H_A_eq2. }
              apply TypePiCong. exact Hwf_A0. exact H_A_eq2. exact Heq_B_t.

        -- destruct Hlift as [l0' [l1' [k [v0 [v1 [HUl0 [HUl1 [Hlift_u0 [Hlift_u1 Heq_v]]]]]]]]].
           apply inl. split.
           ++ (* Preuve de Lambda = Lambda : A0 avec Lifts *)
              (* 1. On prouve explicitement l0' = l1' en faisant le pont avec Heq_B *)
              assert (H_U_eq : [Γ,, t1 |- U l0' = U l1']).
              { eapply TypeTrans. apply TypeSym. exact HUl0.
                eapply TypeTrans. exact Heq_B. exact HUl1. }
              apply UInj in H_U_eq. subst l1'.

              (* 2. On rassemble l'égalité des termes dans le contexte t1 *)
              assert (Hu0_u1_t1 : [Γ,, t1 |- u0 = u1 : t0]).
              { eapply TermTrans. exact Hlift_u0.
                eapply TermTrans. 
                - eapply TermConv. instantiate (1:= U l0').
                  eapply TermLiftingCong. exact Heq_v.
                  apply typing_defeq_inv in Hlift_u1. destruct Hlift_u1 as [_ [_ Hwf_u1]].
                  apply lift_inv_plus in Hwf_u1. destruct Hwf_u1 as [? [Hlt [? []]]]. exact l.
                  auto using TypeSym.
                - apply TermSym. eapply TermConv. exact Hlift_u1. apply TypeSym. exact Heq_B. }

              (* 3. On ramène les égalités dans le contexte de base t *)
              assert (Hu0_u1_t : [Γ,, t |- u0 = u1 : t0]).
              { eapply conv_hypothesis_term_eq. exact Hu0_u1_t1. apply TypeSym. exact H_A_eq2. }
              assert (Heq_B_t : [Γ,, t |- t0 = t2]).
              { eapply conv_hypothesis_type_eq. exact Heq_B. apply TypeSym. exact H_A_eq2. }

              (* 4. Conclusion *)
              eapply TermConv. instantiate (1:=Prod t t0).
              ** apply TermLambdaCong.
                 --- exact Hwf_A0.
                 --- exact H_A_eq2.
                 --- exact Heq_B_t.
                 --- exact Hu0_u1_t.
              ** apply TypeSym. exact H_A0.
           ++ (* Preuve de A0 = A1 *)
              eapply TypeTrans. exact H_A0.
              eapply TypeTrans. 2: { apply TypeSym. exact H_A1. }
              assert (Heq_B_t : [Γ,, t |- t0 = t2]).
              { eapply conv_hypothesis_type_eq. exact Heq_B. apply TypeSym. exact H_A_eq2. }
              apply TypePiCong. exact Hwf_A0. exact H_A_eq2. exact Heq_B_t.
      * (* u1 = cLift *)
        simpl in Herase.
        assert (Hbis := H_u0). apply lambda_inv in Hbis; destruct Hbis. apply wfTermConv with (1:=H_u0) in c.
        apply inl.
        eapply erase_lambda_inv with (1:= c) (2:= H_u1) in Herase.
        all: auto. constructor. assert (Hbis := H_u0). apply lambda_inv in Hbis; destruct Hbis.
        eapply TermConv. instantiate (1:= Prod t t0). all : auto using TypeSym.
        apply subject_red in Herase.
        assert (Hbis := H_u1). apply lift_inv_plus in Hbis; destruct Hbis as [? [? [? []]]].
        apply wfTermConv with (1:= H_u1) in c0. contradict Herase. intros. apply cohesion_prod_univ with (1:= Herase) (2:= c0). auto.

    + (* u0 = App *)
      eapply erase_app_inv.
      * exact H_u0.
      * exact H_u1.
      * intros. eapply erase_inj_ty_fix; eauto.
      * intros. eapply erase_inj_ty_fix; eauto.
      * intros. eapply erase_inj_term_fix; eauto.
      * intros. eapply erase_inj_term_fix; eauto.
      * exact Herase.

    + (* u0 = cProd *)
      eapply erase_cprod_inv.
      * exact H_u0.
      * exact H_u1.
      * intros. eapply erase_inj_ty_fix; eauto.
      * intros. eapply erase_inj_term_fix; eauto.
      * intros. eapply erase_inj_term_fix; eauto.
      * exact Herase.

    + (* u0 = cU *)
      destruct u1; try(simpl in Herase; contradict Herase; congruence).
      * simpl in Herase. injection Herase; intro; subst.
        apply code_univ_inv_bis in H_u0; destruct H_u0.
        apply code_univ_inv_bis in H_u1; destruct H_u1.
        apply inr. eexists l0, l2. set (k:=(Nat.min l0 l2)). eexists k, (cU l1 k), (cU l1 k).
        constructor; auto. constructor; auto. constructor. apply TermSym. eapply TermConv.
        instantiate (1:= U l0). apply conv_lift_univ_min_comm. apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
        auto. auto. lia. auto using TypeSym.
        constructor. apply TermSym. eapply TermConv. instantiate (1:= U l2).
        apply conv_lift_univ_min. apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
        auto. lia. lia. auto using TypeSym.
        apply TermRefl. constructor. apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
        auto. apply inf_min. auto.  auto.
      * simpl in Herase. apply inr. eexists l0, l2. apply erase_cuniv_inv; eauto.

    + (* u0 = cLift *)
      assert (Hbis:= H_u0). apply lift_inv_plus in Hbis.
      destruct Hbis as [n1 [HeqA0 [Heql [Hlt Htypt]]]].
      apply erase_inj_term_fix with (1:=Htypt) (2:=H_u1) in Herase. destruct Herase as [[Heq Hty] | Hlift].
      * symmetry in Heql. rewrite Heql in HeqA0. apply TypeSym in Hty. apply inr.
        eexists l0, l, l, u0, u0.
        constructor; auto. constructor; auto. constructor. apply TermRefl. auto.
        constructor. eapply TermConv. instantiate (1:= U l).
        eapply TermTrans. instantiate (1:=u0).
        auto using TermSym. eapply lift_same. auto. auto using TypeSym. apply TermRefl. auto.
      * destruct Hlift as [l0' [l1' [k [v0 [v1 [HUl0 [HUl1 [Hlift_u0 [Hlift_u1 Heq_v]]]]]]]]].
        apply inr. 
        (* On extrait l'égalité l = l0' pour simplifier intégralement le contexte *)
        apply UInj in HUl0. symmetry in HUl0. subst l0'.
        
        symmetry in Heql. rewrite Heql in HeqA0.
        eexists l0, l1', k, v0, v1.
        
        (* On sépare les 5 buts proprement plutôt que d'utiliser 'repeat split; auto' *)
        split. { exact HeqA0. }
        split. { exact HUl1. }
        split.
        -- (* 3. Preuve de cLift l l0 u0 = cLift k l0 v0 : A0 *)
           eapply TermConv. instantiate (1:= U l0).
           eapply TermTrans. instantiate (1:= cLift l l0 (cLift k l v0)).
           ++ (* Étape A - Congruence : cLift l l0 u0 = cLift l l0 (cLift k l v0) *)
              apply TermLiftingCong. 
              ** exact Hlift_u0.
              ** exact Hlt.
           ++ (* Étape B - Cumulativité : cLift l l0 (cLift k l v0) = cLift k l0 v0 *)
              apply TermLiftingCumul.
              ** apply typing_defeq_inv in Heq_v. destruct Heq_v as [_ [Hwf _]]. exact Hwf.
              ** apply typing_defeq_inv in Hlift_u0. destruct Hlift_u0 as [_ [_ Hwf_lift]].
                 apply lift_inv in Hwf_lift. destruct Hwf_lift as [_ [Hkl _]]. exact Hkl.
              ** exact Hlt.
           ++ apply TypeSym. exact HeqA0.
        -- split.
           ++ exact Hlift_u1.
           ++ exact Heq_v.
Qed.




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
induction A. (* Induction on A *)
- intros; destruct B. (* A = Prod A1 A2 *)
    all: try (simpl in H1; contradict H1; congruence).
    + simpl in H1. inversion H1. apply TypePiCong. apply prod_ty_inv in H. destruct H. auto.
        ++ apply erase_inj_ty. apply prod_ty_inv in H,H0. destruct H,H0. auto. auto. inversion H0. auto. auto.
        ++ apply erase_inj_ty. apply prod_ty_inv in H,H0. destruct H,H0. auto. auto. inversion H0. eapply conv_hypothesis_wftype.
            instantiate (1:= B1). auto. apply erase_inj_ty. apply prod_ty_inv in H,H0. destruct H,H0. auto.
            apply prod_ty_inv in H,H0. destruct H,H0. auto. auto. auto.
    + simpl in H1. apply erase_decode_inv_prod. auto. constructor. all: try(auto). apply prod_ty_inv in H. destruct H. auto. apply prod_ty_inv in H. destruct H. auto.
    
- intros. destruct B. (* A = Decode n a *)
    + destruct t. 
        all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1. injection H1; intros Heq2 Heq1.
        
        (* 1. Inversion de Decode et cProd *)
        apply decode_ty_inv in H. 
        apply code_prod_inv in H. destruct H as [Heql [Ht1 Ht2]]. subst l0.
        
        (* 2. Inversion de Prod *)
        apply prod_ty_inv in H0. destruct H0 as [Hwf_B1 Hwf_B2].
        
        (* 3. Transitivité : Decode (cProd t1 t2) = Prod (Decode t1) (Decode t2) = Prod B1 B2 *)
        eapply TypeTrans.
        -- apply TypeDecodeProdConv; auto.
        -- apply TypePiCong.
           +++ (* Bonne formation du membre gauche *)
              apply wfTypeDecode; auto.
           +++ (* Egalité des domaines via IH *)
              eapply erase_inj_ty.
              ** apply wfTypeDecode; auto.
              ** exact Hwf_B1.
              ** simpl. exact Heq1.
           +++ (* Egalité des codomaines via IH avec conversion de contexte *)
              eapply erase_inj_ty.
              ** apply wfTypeDecode; auto.
              ** eapply conv_hypothesis_wftype.
                 --- exact Hwf_B2.
                 --- apply TypeSym. eapply erase_inj_ty.
                     ++++ apply wfTypeDecode; auto.
                     ++++ exact Hwf_B1.
                     ++++ simpl. exact Heq1.
              ** simpl. exact Heq2.

        ++ 
           simpl in H1.
           
           (* 1. Inversion de Decode et cLift *)
           apply decode_ty_inv in H. 
           apply lift_inv in H. destruct H as [Heql [Hlt Ht_inner]]. subst l.
           
           (* 2. Transitivité : Decode l1 (cLift l0 l1 t) = Decode l0 t = Prod B1 B2 *)
           eapply TypeTrans.
           ** apply TypeSym. apply TypeDecodeLiftConv.
              --- exact Ht_inner.
              --- exact Hlt.
           ** eapply erase_inj_ty.
              --- apply wfTypeDecode. exact Ht_inner.
              --- exact H0.
              --- simpl. exact H1.
    + simpl in H1. apply decode_ty_inv in H. apply decode_ty_inv in H0. apply erase_inj_term with (1:=H) (2:=H0) in H1.
        destruct H1.  destruct p. apply UInj in c0. rewrite c0. apply TypeDecodeCong. rewrite c0 in c. auto.
        destruct s as [? [? [projT5 [projT6 [projT7 [? [? [? []]]]]]]]].
        apply UInj in c; apply UInj in c0. symmetry in c; rewrite c in c1. symmetry in c0; rewrite c0 in c2. eapply TypeTrans. instantiate (1:= Decode l (cLift projT5 l projT6)).
            apply TypeDecodeCong. auto. eapply TypeTrans. instantiate (1:=Decode l0 (cLift projT5 l0 projT7)).
            eapply TypeTrans. instantiate (1:= Decode projT5 projT6). apply TypeSym; apply TypeDecodeLiftConv. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ eapply TypeTrans. instantiate (1:= Decode projT5 projT7). apply TypeDecodeCong. auto. apply TypeDecodeLiftConv.   
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ apply TypeDecodeCong. apply TermSym. auto. 

    + simpl in H0. apply TypeSym. apply erase_decode_inv_univ.  auto. auto.
    
- intros;  destruct B. (* A = U n *)
    all: try (simpl in H1; contradict H1; congruence). (* Eliminate impossible cases *)
    + apply erase_decode_inv_univ. auto. simpl in H0. auto. 
    + simpl in H0. inversion H0. auto.


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
                +++ destruct s as [projT3 [projT4 [projT5 [projT6 [projT7 [ ? [? [ ? []]]]]]]]]. apply inl. 
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
     
        ++ destruct s as [projT4 [projT5 [projT6 [projT7 [projT8 [? [? [? []]]]]]]]]. apply inr. apply UInj in c0. symmetry in e; rewrite e in c.
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

Qed.
