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