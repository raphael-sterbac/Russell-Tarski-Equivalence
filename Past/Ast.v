Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Definition lvl := nat.

Inductive ty : Type :=
  | var_ty : nat -> ty
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

Lemma congr_Prod {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : Prod s0 s1 = Prod t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Prod x s1) H0))
         (ap (fun x => Prod t0 x) H1)).
Qed.

Lemma congr_Decode {s0 : lvl} {s1 : term} {t0 : lvl} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : Decode s0 s1 = Decode t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Decode x s1) H0))
         (ap (fun x => Decode t0 x) H1)).
Qed.

Lemma congr_U {s0 : lvl} {t0 : lvl} (H0 : s0 = t0) : U s0 = U t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => U x) H0)).
Qed.

Lemma congr_Lambda {s0 : ty} {s1 : ty} {s2 : term} {t0 : ty} {t1 : ty}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  Lambda s0 s1 s2 = Lambda t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => Lambda x s1 s2) H0))
            (ap (fun x => Lambda t0 x s2) H1))
         (ap (fun x => Lambda t0 t1 x) H2)).
Qed.

Lemma congr_App {s0 : ty} {s1 : ty} {s2 : term} {s3 : term} {t0 : ty}
  {t1 : ty} {t2 : term} {t3 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : App s0 s1 s2 s3 = App t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => App x s1 s2 s3) H0))
               (ap (fun x => App t0 x s2 s3) H1))
            (ap (fun x => App t0 t1 x s3) H2))
         (ap (fun x => App t0 t1 t2 x) H3)).
Qed.

Lemma congr_cProd {s0 : lvl} {s1 : term} {s2 : term} {t0 : lvl} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cProd s0 s1 s2 = cProd t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cProd x s1 s2) H0))
            (ap (fun x => cProd t0 x s2) H1))
         (ap (fun x => cProd t0 t1 x) H2)).
Qed.

Lemma congr_cU {s0 : lvl} {s1 : lvl} {t0 : lvl} {t1 : lvl} (H0 : s0 = t0)
  (H1 : s1 = t1) : cU s0 s1 = cU t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cU x s1) H0))
         (ap (fun x => cU t0 x) H1)).
Qed.

Lemma congr_cLift {s0 : lvl} {s1 : lvl} {s2 : term} {t0 : lvl} {t1 : lvl}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cLift s0 s1 s2 = cLift t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cLift x s1 s2) H0))
            (ap (fun x => cLift t0 x s2) H1))
         (ap (fun x => cLift t0 t1 x) H2)).
Qed.

Lemma upRen_ty_ty (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_ty_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_term_ty (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_ty (xi_ty : nat -> nat) (xi_term : nat -> nat) (s : ty) {struct
 s} : ty :=
  match s with
  | var_ty s0 => var_ty (xi_ty s0)
  | Prod s0 s1 =>
      Prod (ren_ty xi_ty xi_term s0)
        (ren_ty (upRen_ty_ty xi_ty) (upRen_ty_term xi_term) s1)
  | Decode s0 s1 => Decode s0 (ren_term xi_ty xi_term s1)
  | U s0 => U s0
  end
with ren_term (xi_ty : nat -> nat) (xi_term : nat -> nat) (s : term) {struct
 s} : term :=
  match s with
  | var_term s0 => var_term (xi_term s0)
  | Lambda s0 s1 s2 =>
      Lambda (ren_ty xi_ty xi_term s0) (ren_ty xi_ty xi_term s1)
        (ren_term (upRen_ty_ty xi_ty) (upRen_ty_term xi_term) s2)
  | App s0 s1 s2 s3 =>
      App (ren_ty xi_ty xi_term s0) (ren_ty xi_ty xi_term s1)
        (ren_term xi_ty xi_term s2) (ren_term xi_ty xi_term s3)
  | cProd s0 s1 s2 =>
      cProd s0 (ren_term xi_ty xi_term s1)
        (ren_term (upRen_term_ty xi_ty) (upRen_term_term xi_term) s2)
  | cU s0 s1 => cU s0 s1
  | cLift s0 s1 s2 => cLift s0 s1 (ren_term xi_ty xi_term s2)
  end.

Lemma up_ty_ty (sigma : nat -> ty) : nat -> ty.
Proof.
exact (scons (var_ty var_zero) (funcomp (ren_ty shift id) sigma)).
Defined.

Lemma up_ty_term (sigma : nat -> term) : nat -> term.
Proof.
exact (funcomp (ren_term shift id) sigma).
Defined.

Lemma up_term_ty (sigma : nat -> ty) : nat -> ty.
Proof.
exact (funcomp (ren_ty id shift) sigma).
Defined.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var_term var_zero) (funcomp (ren_term id shift) sigma)).
Defined.

Fixpoint subst_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term) (s : ty)
{struct s} : ty :=
  match s with
  | var_ty s0 => sigma_ty s0
  | Prod s0 s1 =>
      Prod (subst_ty sigma_ty sigma_term s0)
        (subst_ty (up_ty_ty sigma_ty) (up_ty_term sigma_term) s1)
  | Decode s0 s1 => Decode s0 (subst_term sigma_ty sigma_term s1)
  | U s0 => U s0
  end
with subst_term (sigma_ty : nat -> ty) (sigma_term : nat -> term) (s : term)
{struct s} : term :=
  match s with
  | var_term s0 => sigma_term s0
  | Lambda s0 s1 s2 =>
      Lambda (subst_ty sigma_ty sigma_term s0)
        (subst_ty sigma_ty sigma_term s1)
        (subst_term (up_ty_ty sigma_ty) (up_ty_term sigma_term) s2)
  | App s0 s1 s2 s3 =>
      App (subst_ty sigma_ty sigma_term s0) (subst_ty sigma_ty sigma_term s1)
        (subst_term sigma_ty sigma_term s2)
        (subst_term sigma_ty sigma_term s3)
  | cProd s0 s1 s2 =>
      cProd s0 (subst_term sigma_ty sigma_term s1)
        (subst_term (up_term_ty sigma_ty) (up_term_term sigma_term) s2)
  | cU s0 s1 => cU s0 s1
  | cLift s0 s1 s2 => cLift s0 s1 (subst_term sigma_ty sigma_term s2)
  end.

Lemma upId_ty_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_ty_ty sigma x = var_ty x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma upId_ty_term (sigma : nat -> term)
  (Eq : forall x, sigma x = var_term x) :
  forall x, up_ty_term sigma x = var_term x.
Proof.
exact (fun n => ap (ren_term shift id) (Eq n)).
Qed.

Lemma upId_term_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_term_ty sigma x = var_ty x.
Proof.
exact (fun n => ap (ren_ty id shift) (Eq n)).
Qed.

Lemma upId_term_term (sigma : nat -> term)
  (Eq : forall x, sigma x = var_term x) :
  forall x, up_term_term sigma x = var_term x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_term : forall x, sigma_term x = var_term x) (s : ty) {struct s} :
subst_ty sigma_ty sigma_term s = s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod (idSubst_ty sigma_ty sigma_term Eq_ty Eq_term s0)
        (idSubst_ty (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (upId_ty_ty _ Eq_ty) (upId_ty_term _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (idSubst_term sigma_ty sigma_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with idSubst_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_term : forall x, sigma_term x = var_term x) (s : term) {struct s} :
subst_term sigma_ty sigma_term s = s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda (idSubst_ty sigma_ty sigma_term Eq_ty Eq_term s0)
        (idSubst_ty sigma_ty sigma_term Eq_ty Eq_term s1)
        (idSubst_term (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (upId_ty_ty _ Eq_ty) (upId_ty_term _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (idSubst_ty sigma_ty sigma_term Eq_ty Eq_term s0)
        (idSubst_ty sigma_ty sigma_term Eq_ty Eq_term s1)
        (idSubst_term sigma_ty sigma_term Eq_ty Eq_term s2)
        (idSubst_term sigma_ty sigma_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (idSubst_term sigma_ty sigma_term Eq_ty Eq_term s1)
        (idSubst_term (up_term_ty sigma_ty) (up_term_term sigma_term)
           (upId_term_ty _ Eq_ty) (upId_term_term _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_ty sigma_term Eq_ty Eq_term s2)
  end.

Lemma upExtRen_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Lemma upExtRen_ty_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_term xi x = upRen_ty_term zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_term_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_ty xi x = upRen_term_ty zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_term : forall x, xi_term x = zeta_term x) (s : ty) {struct s} :
ren_ty xi_ty xi_term s = ren_ty zeta_ty zeta_term s :=
  match s with
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
  | Prod s0 s1 =>
      congr_Prod (extRen_ty xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s0)
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_term _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (extRen_term xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with extRen_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_ty xi_term s = ren_term zeta_ty zeta_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (extRen_ty xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s0)
        (extRen_ty xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s1)
        (extRen_term (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_term _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (extRen_ty xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s0)
        (extRen_ty xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s1)
        (extRen_term xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s2)
        (extRen_term xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (extRen_term xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s1)
        (extRen_term (upRen_term_ty xi_ty) (upRen_term_term xi_term)
           (upRen_term_ty zeta_ty) (upRen_term_term zeta_term)
           (upExtRen_term_ty _ _ Eq_ty) (upExtRen_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (extRen_term xi_ty xi_term zeta_ty zeta_term Eq_ty Eq_term s2)
  end.

Lemma upExt_ty_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma upExt_ty_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_term sigma x = up_ty_term tau x.
Proof.
exact (fun n => ap (ren_term shift id) (Eq n)).
Qed.

Lemma upExt_term_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_ty sigma x = up_term_ty tau x.
Proof.
exact (fun n => ap (ren_ty id shift) (Eq n)).
Qed.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(tau_ty : nat -> ty) (tau_term : nat -> term)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_term : forall x, sigma_term x = tau_term x) (s : ty) {struct s} :
subst_ty sigma_ty sigma_term s = subst_ty tau_ty tau_term s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod
        (ext_ty sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s0)
        (ext_ty (up_ty_ty sigma_ty) (up_ty_term sigma_term) (up_ty_ty tau_ty)
           (up_ty_term tau_term) (upExt_ty_ty _ _ Eq_ty)
           (upExt_ty_term _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (ext_term sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with ext_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(tau_ty : nat -> ty) (tau_term : nat -> term)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_ty sigma_term s = subst_term tau_ty tau_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (ext_ty sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s0)
        (ext_ty sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s1)
        (ext_term (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (up_ty_ty tau_ty) (up_ty_term tau_term) (upExt_ty_ty _ _ Eq_ty)
           (upExt_ty_term _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (ext_ty sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s0)
        (ext_ty sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s1)
        (ext_term sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s2)
        (ext_term sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (ext_term sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s1)
        (ext_term (up_term_ty sigma_ty) (up_term_term sigma_term)
           (up_term_ty tau_ty) (up_term_term tau_term)
           (upExt_term_ty _ _ Eq_ty) (upExt_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (ext_term sigma_ty sigma_term tau_ty tau_term Eq_ty Eq_term s2)
  end.

Lemma up_ren_ren_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_ty_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_ty_term zeta) (upRen_ty_term xi) x = upRen_ty_term rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_term_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_ty zeta) (upRen_term_ty xi) x = upRen_term_ty rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat) (rho_ty : nat -> nat)
(rho_term : nat -> nat)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : ty)
{struct s} :
ren_ty zeta_ty zeta_term (ren_ty xi_ty xi_term s) = ren_ty rho_ty rho_term s
:=
  match s with
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
  | Prod s0 s1 =>
      congr_Prod
        (compRenRen_ty xi_ty xi_term zeta_ty zeta_term rho_ty rho_term Eq_ty
           Eq_term s0)
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (upRen_ty_ty rho_ty) (upRen_ty_term rho_term)
           (up_ren_ren _ _ _ Eq_ty) Eq_term s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compRenRen_term xi_ty xi_term zeta_ty zeta_term rho_ty rho_term
           Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compRenRen_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat) (rho_ty : nat -> nat)
(rho_term : nat -> nat)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} :
ren_term zeta_ty zeta_term (ren_term xi_ty xi_term s) =
ren_term rho_ty rho_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compRenRen_ty xi_ty xi_term zeta_ty zeta_term rho_ty rho_term Eq_ty
           Eq_term s0)
        (compRenRen_ty xi_ty xi_term zeta_ty zeta_term rho_ty rho_term Eq_ty
           Eq_term s1)
        (compRenRen_term (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (upRen_ty_ty rho_ty) (upRen_ty_term rho_term)
           (up_ren_ren _ _ _ Eq_ty) Eq_term s2)
  | App s0 s1 s2 s3 =>
      congr_App
        (compRenRen_ty xi_ty xi_term zeta_ty zeta_term rho_ty rho_term Eq_ty
           Eq_term s0)
        (compRenRen_ty xi_ty xi_term zeta_ty zeta_term rho_ty rho_term Eq_ty
           Eq_term s1)
        (compRenRen_term xi_ty xi_term zeta_ty zeta_term rho_ty rho_term
           Eq_ty Eq_term s2)
        (compRenRen_term xi_ty xi_term zeta_ty zeta_term rho_ty rho_term
           Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compRenRen_term xi_ty xi_term zeta_ty zeta_term rho_ty rho_term
           Eq_ty Eq_term s1)
        (compRenRen_term (upRen_term_ty xi_ty) (upRen_term_term xi_term)
           (upRen_term_ty zeta_ty) (upRen_term_term zeta_term)
           (upRen_term_ty rho_ty) (upRen_term_term rho_term) Eq_ty
           (up_ren_ren _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_ty xi_term zeta_ty zeta_term rho_ty rho_term
           Eq_ty Eq_term s2)
  end.

Lemma up_ren_subst_ty_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma up_ren_subst_ty_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_ty_term tau) (upRen_ty_term xi) x = up_ty_term theta x.
Proof.
exact (fun n => ap (ren_term shift id) (Eq n)).
Qed.

Lemma up_ren_subst_term_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_ty tau) (upRen_term_ty xi) x = up_term_ty theta x.
Proof.
exact (fun n => ap (ren_ty id shift) (Eq n)).
Qed.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
(tau_ty : nat -> ty) (tau_term : nat -> term) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : ty)
{struct s} :
subst_ty tau_ty tau_term (ren_ty xi_ty xi_term s) =
subst_ty theta_ty theta_term s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod
        (compRenSubst_ty xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s0)
        (compRenSubst_ty (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (up_ty_ty tau_ty) (up_ty_term tau_term) (up_ty_ty theta_ty)
           (up_ty_term theta_term) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_term _ _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compRenSubst_term xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compRenSubst_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
(tau_ty : nat -> ty) (tau_term : nat -> term) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_ty tau_term (ren_term xi_ty xi_term s) =
subst_term theta_ty theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compRenSubst_ty xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s0)
        (compRenSubst_ty xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s1)
        (compRenSubst_term (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (up_ty_ty tau_ty) (up_ty_term tau_term) (up_ty_ty theta_ty)
           (up_ty_term theta_term) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_term _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App
        (compRenSubst_ty xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s0)
        (compRenSubst_ty xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s1)
        (compRenSubst_term xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s2)
        (compRenSubst_term xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compRenSubst_term xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s1)
        (compRenSubst_term (upRen_term_ty xi_ty) (upRen_term_term xi_term)
           (up_term_ty tau_ty) (up_term_term tau_term) (up_term_ty theta_ty)
           (up_term_term theta_term) (up_ren_subst_term_ty _ _ _ Eq_ty)
           (up_ren_subst_term_term _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_ty xi_term tau_ty tau_term theta_ty theta_term
           Eq_ty Eq_term s2)
  end.

Lemma up_subst_ren_ty_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (zeta_term : nat -> nat) (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term))
    (up_ty_ty sigma) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_ty shift id (upRen_ty_ty zeta_ty)
                (upRen_ty_term zeta_term) (funcomp shift zeta_ty)
                (funcomp id zeta_term) (fun x => eq_refl) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_ty zeta_ty zeta_term shift id
                      (funcomp shift zeta_ty) (funcomp id zeta_term)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_ty shift id) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma up_subst_ren_ty_term (sigma : nat -> term) (zeta_ty : nat -> nat)
  (zeta_term : nat -> nat) (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_ty zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term))
    (up_ty_term sigma) x = up_ty_term theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_term shift id (upRen_ty_ty zeta_ty)
            (upRen_ty_term zeta_term) (funcomp shift zeta_ty)
            (funcomp id zeta_term) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_term zeta_ty zeta_term shift id
                  (funcomp shift zeta_ty) (funcomp id zeta_term)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_term shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_term_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (zeta_term : nat -> nat) (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_term_ty zeta_ty) (upRen_term_term zeta_term))
    (up_term_ty sigma) x = up_term_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty id shift (upRen_term_ty zeta_ty)
            (upRen_term_term zeta_term) (funcomp id zeta_ty)
            (funcomp shift zeta_term) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_ty zeta_term id shift (funcomp id zeta_ty)
                  (funcomp shift zeta_term) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_ty id shift) (Eq n)))).
Qed.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_ty : nat -> nat)
  (zeta_term : nat -> nat) (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_ty zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_ty zeta_ty) (upRen_term_term zeta_term))
    (up_term_term sigma) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term id shift (upRen_term_ty zeta_ty)
                (upRen_term_term zeta_term) (funcomp id zeta_ty)
                (funcomp shift zeta_term) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_ty zeta_term id shift
                      (funcomp id zeta_ty) (funcomp shift zeta_term)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_term id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty zeta_term) sigma_ty x = theta_ty x)
(Eq_term : forall x,
           funcomp (ren_term zeta_ty zeta_term) sigma_term x = theta_term x)
(s : ty) {struct s} :
ren_ty zeta_ty zeta_term (subst_ty sigma_ty sigma_term s) =
subst_ty theta_ty theta_term s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod
        (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstRen_ty (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (up_ty_ty theta_ty) (up_ty_term theta_term)
           (up_subst_ren_ty_ty _ _ _ _ Eq_ty)
           (up_subst_ren_ty_term _ _ _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compSubstRen_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(zeta_ty : nat -> nat) (zeta_term : nat -> nat) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty zeta_term) sigma_ty x = theta_ty x)
(Eq_term : forall x,
           funcomp (ren_term zeta_ty zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_ty zeta_term (subst_term sigma_ty sigma_term s) =
subst_term theta_ty theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstRen_term (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (upRen_ty_ty zeta_ty) (upRen_ty_term zeta_term)
           (up_ty_ty theta_ty) (up_ty_term theta_term)
           (up_subst_ren_ty_ty _ _ _ _ Eq_ty)
           (up_subst_ren_ty_term _ _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App
        (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s2)
        (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstRen_term (up_term_ty sigma_ty) (up_term_term sigma_term)
           (upRen_term_ty zeta_ty) (upRen_term_term zeta_term)
           (up_term_ty theta_ty) (up_term_term theta_term)
           (up_subst_ren_term_ty _ _ _ _ Eq_ty)
           (up_subst_ren_term_term _ _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term theta_ty
           theta_term Eq_ty Eq_term s2)
  end.

Lemma up_subst_subst_ty_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (tau_term : nat -> term) (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty) (up_ty_term tau_term)) (up_ty_ty sigma)
    x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_ty shift id (up_ty_ty tau_ty)
                (up_ty_term tau_term) (funcomp (up_ty_ty tau_ty) shift)
                (funcomp (up_ty_term tau_term) id) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_ty tau_ty tau_term shift id
                      (funcomp (ren_ty shift id) tau_ty)
                      (funcomp (ren_term shift id) tau_term)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_ty shift id) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma up_subst_subst_ty_term (sigma : nat -> term) (tau_ty : nat -> ty)
  (tau_term : nat -> term) (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_ty tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_ty_ty tau_ty) (up_ty_term tau_term))
    (up_ty_term sigma) x = up_ty_term theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_term shift id (up_ty_ty tau_ty) (up_ty_term tau_term)
            (funcomp (up_ty_ty tau_ty) shift)
            (funcomp (up_ty_term tau_term) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_term tau_ty tau_term shift id
                  (funcomp (ren_ty shift id) tau_ty)
                  (funcomp (ren_term shift id) tau_term) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_term shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_term_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (tau_term : nat -> term) (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_term_ty tau_ty) (up_term_term tau_term))
    (up_term_ty sigma) x = up_term_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty id shift (up_term_ty tau_ty)
            (up_term_term tau_term) (funcomp (up_term_ty tau_ty) id)
            (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty tau_term id shift
                  (funcomp (ren_ty id shift) tau_ty)
                  (funcomp (ren_term id shift) tau_term) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_ty id shift) (Eq n)))).
Qed.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_ty : nat -> ty)
  (tau_term : nat -> term) (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_ty tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_ty tau_ty) (up_term_term tau_term))
    (up_term_term sigma) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term id shift (up_term_ty tau_ty)
                (up_term_term tau_term) (funcomp (up_term_ty tau_ty) id)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_ty tau_term id shift
                      (funcomp (ren_ty id shift) tau_ty)
                      (funcomp (ren_term id shift) tau_term)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_term id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(tau_ty : nat -> ty) (tau_term : nat -> term) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp (subst_ty tau_ty tau_term) sigma_ty x = theta_ty x)
(Eq_term : forall x,
           funcomp (subst_term tau_ty tau_term) sigma_term x = theta_term x)
(s : ty) {struct s} :
subst_ty tau_ty tau_term (subst_ty sigma_ty sigma_term s) =
subst_ty theta_ty theta_term s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod
        (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (up_ty_ty tau_ty) (up_ty_term tau_term) (up_ty_ty theta_ty)
           (up_ty_term theta_term) (up_subst_subst_ty_ty _ _ _ _ Eq_ty)
           (up_subst_subst_ty_term _ _ _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compSubstSubst_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
(tau_ty : nat -> ty) (tau_term : nat -> term) (theta_ty : nat -> ty)
(theta_term : nat -> term)
(Eq_ty : forall x, funcomp (subst_ty tau_ty tau_term) sigma_ty x = theta_ty x)
(Eq_term : forall x,
           funcomp (subst_term tau_ty tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_ty tau_term (subst_term sigma_ty sigma_term s) =
subst_term theta_ty theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstSubst_term (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (up_ty_ty tau_ty) (up_ty_term tau_term) (up_ty_ty theta_ty)
           (up_ty_term theta_term) (up_subst_subst_ty_ty _ _ _ _ Eq_ty)
           (up_subst_subst_ty_term _ _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App
        (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s0)
        (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s2)
        (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s1)
        (compSubstSubst_term (up_term_ty sigma_ty) (up_term_term sigma_term)
           (up_term_ty tau_ty) (up_term_term tau_term) (up_term_ty theta_ty)
           (up_term_term theta_term) (up_subst_subst_term_ty _ _ _ _ Eq_ty)
           (up_subst_subst_term_term _ _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term theta_ty
           theta_term Eq_ty Eq_term s2)
  end.

Lemma renRen_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) (s : ty) :
  ren_ty zeta_ty zeta_term (ren_ty xi_ty xi_term s) =
  ren_ty (funcomp zeta_ty xi_ty) (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_ty xi_ty xi_term zeta_ty zeta_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_ty_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_ty zeta_ty zeta_term) (ren_ty xi_ty xi_term))
    (ren_ty (funcomp zeta_ty xi_ty) (funcomp zeta_term xi_term)).
Proof.
exact (fun s =>
       compRenRen_ty xi_ty xi_term zeta_ty zeta_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) (s : term) :
  ren_term zeta_ty zeta_term (ren_term xi_ty xi_term s) =
  ren_term (funcomp zeta_ty xi_ty) (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_ty xi_term zeta_ty zeta_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_ty zeta_term) (ren_term xi_ty xi_term))
    (ren_term (funcomp zeta_ty xi_ty) (funcomp zeta_term xi_term)).
Proof.
exact (fun s =>
       compRenRen_term xi_ty xi_term zeta_ty zeta_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (tau_ty : nat -> ty) (tau_term : nat -> term) (s : ty) :
  subst_ty tau_ty tau_term (ren_ty xi_ty xi_term s) =
  subst_ty (funcomp tau_ty xi_ty) (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_ty xi_ty xi_term tau_ty tau_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (tau_ty : nat -> ty) (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_ty tau_ty tau_term) (ren_ty xi_ty xi_term))
    (subst_ty (funcomp tau_ty xi_ty) (funcomp tau_term xi_term)).
Proof.
exact (fun s =>
       compRenSubst_ty xi_ty xi_term tau_ty tau_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (tau_ty : nat -> ty) (tau_term : nat -> term) (s : term) :
  subst_term tau_ty tau_term (ren_term xi_ty xi_term s) =
  subst_term (funcomp tau_ty xi_ty) (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_ty xi_term tau_ty tau_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat)
  (tau_ty : nat -> ty) (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_ty tau_term) (ren_term xi_ty xi_term))
    (subst_term (funcomp tau_ty xi_ty) (funcomp tau_term xi_term)).
Proof.
exact (fun s =>
       compRenSubst_term xi_ty xi_term tau_ty tau_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) (s : ty) :
  ren_ty zeta_ty zeta_term (subst_ty sigma_ty sigma_term s) =
  subst_ty (funcomp (ren_ty zeta_ty zeta_term) sigma_ty)
    (funcomp (ren_term zeta_ty zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_ty_pointwise (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_ty zeta_ty zeta_term) (subst_ty sigma_ty sigma_term))
    (subst_ty (funcomp (ren_ty zeta_ty zeta_term) sigma_ty)
       (funcomp (ren_term zeta_ty zeta_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstRen_ty sigma_ty sigma_term zeta_ty zeta_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  (zeta_ty : nat -> nat) (zeta_term : nat -> nat) (s : term) :
  ren_term zeta_ty zeta_term (subst_term sigma_ty sigma_term s) =
  subst_term (funcomp (ren_ty zeta_ty zeta_term) sigma_ty)
    (funcomp (ren_term zeta_ty zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_ty : nat -> ty)
  (sigma_term : nat -> term) (zeta_ty : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_ty zeta_term) (subst_term sigma_ty sigma_term))
    (subst_term (funcomp (ren_ty zeta_ty zeta_term) sigma_ty)
       (funcomp (ren_term zeta_ty zeta_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstRen_term sigma_ty sigma_term zeta_ty zeta_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  (tau_ty : nat -> ty) (tau_term : nat -> term) (s : ty) :
  subst_ty tau_ty tau_term (subst_ty sigma_ty sigma_term s) =
  subst_ty (funcomp (subst_ty tau_ty tau_term) sigma_ty)
    (funcomp (subst_term tau_ty tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty_pointwise (sigma_ty : nat -> ty)
  (sigma_term : nat -> term) (tau_ty : nat -> ty) (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_ty tau_ty tau_term) (subst_ty sigma_ty sigma_term))
    (subst_ty (funcomp (subst_ty tau_ty tau_term) sigma_ty)
       (funcomp (subst_term tau_ty tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_ty sigma_ty sigma_term tau_ty tau_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  (tau_ty : nat -> ty) (tau_term : nat -> term) (s : term) :
  subst_term tau_ty tau_term (subst_term sigma_ty sigma_term s) =
  subst_term (funcomp (subst_ty tau_ty tau_term) sigma_ty)
    (funcomp (subst_term tau_ty tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_ty sigma_term tau_ty tau_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_ty : nat -> ty)
  (sigma_term : nat -> term) (tau_ty : nat -> ty) (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_ty tau_term) (subst_term sigma_ty sigma_term))
    (subst_term (funcomp (subst_ty tau_ty tau_term) sigma_ty)
       (funcomp (subst_term tau_ty tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_ty sigma_term tau_ty tau_term _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ty_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_ty_ty xi) x = up_ty_ty sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift id) (Eq n')
       | O => eq_refl
       end).
Qed.

Lemma rinstInst_up_ty_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var_term) xi x = sigma x) :
  forall x, funcomp (var_term) (upRen_ty_term xi) x = up_ty_term sigma x.
Proof.
exact (fun n => ap (ren_term shift id) (Eq n)).
Qed.

Lemma rinstInst_up_term_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_term_ty xi) x = up_term_ty sigma x.
Proof.
exact (fun n => ap (ren_ty id shift) (Eq n)).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var_term) xi x = sigma x) :
  forall x, funcomp (var_term) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_ty (xi_ty : nat -> nat) (xi_term : nat -> nat)
(sigma_ty : nat -> ty) (sigma_term : nat -> term)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : ty)
{struct s} : ren_ty xi_ty xi_term s = subst_ty sigma_ty sigma_term s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | Prod s0 s1 =>
      congr_Prod
        (rinst_inst_ty xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s0)
        (rinst_inst_ty (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_term _ _ Eq_term)
           s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (rinst_inst_term xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with rinst_inst_term (xi_ty : nat -> nat) (xi_term : nat -> nat)
(sigma_ty : nat -> ty) (sigma_term : nat -> term)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_ty xi_term s = subst_term sigma_ty sigma_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (rinst_inst_ty xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s0)
        (rinst_inst_ty xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s1)
        (rinst_inst_term (upRen_ty_ty xi_ty) (upRen_ty_term xi_term)
           (up_ty_ty sigma_ty) (up_ty_term sigma_term)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_term _ _ Eq_term)
           s2)
  | App s0 s1 s2 s3 =>
      congr_App
        (rinst_inst_ty xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s0)
        (rinst_inst_ty xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s1)
        (rinst_inst_term xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s2)
        (rinst_inst_term xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (rinst_inst_term xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s1)
        (rinst_inst_term (upRen_term_ty xi_ty) (upRen_term_term xi_term)
           (up_term_ty sigma_ty) (up_term_term sigma_term)
           (rinstInst_up_term_ty _ _ Eq_ty)
           (rinstInst_up_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_ty xi_term sigma_ty sigma_term Eq_ty Eq_term s2)
  end.

Lemma rinstInst'_ty (xi_ty : nat -> nat) (xi_term : nat -> nat) (s : ty) :
  ren_ty xi_ty xi_term s =
  subst_ty (funcomp (var_ty) xi_ty) (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_ty xi_ty xi_term _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstInst'_ty_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_ty xi_ty xi_term)
    (subst_ty (funcomp (var_ty) xi_ty) (funcomp (var_term) xi_term)).
Proof.
exact (fun s =>
       rinst_inst_ty xi_ty xi_term _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstInst'_term (xi_ty : nat -> nat) (xi_term : nat -> nat) (s : term)
  :
  ren_term xi_ty xi_term s =
  subst_term (funcomp (var_ty) xi_ty) (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_term xi_ty xi_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_ty xi_term)
    (subst_term (funcomp (var_ty) xi_ty) (funcomp (var_term) xi_term)).
Proof.
exact (fun s =>
       rinst_inst_term xi_ty xi_term _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_ty (s : ty) : subst_ty (var_ty) (var_term) s = s.
Proof.
exact (idSubst_ty (var_ty) (var_term) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_ty_pointwise :
  pointwise_relation _ eq (subst_ty (var_ty) (var_term)) id.
Proof.
exact (fun s =>
       idSubst_ty (var_ty) (var_term) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var_ty) (var_term) s = s.
Proof.
exact (idSubst_term (var_ty) (var_term) (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma instId'_term_pointwise :
  pointwise_relation _ eq (subst_term (var_ty) (var_term)) id.
Proof.
exact (fun s =>
       idSubst_term (var_ty) (var_term) (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstId'_ty (s : ty) : ren_ty id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id id s)).
Qed.

Lemma rinstId'_ty_pointwise : pointwise_relation _ eq (@ren_ty id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id id s)).
Qed.

Lemma rinstId'_term (s : term) : ren_term id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id id s)).
Qed.

Lemma varL'_ty (sigma_ty : nat -> ty) (sigma_term : nat -> term) (x : nat) :
  subst_ty sigma_ty sigma_term (var_ty x) = sigma_ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ty_pointwise (sigma_ty : nat -> ty) (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_ty sigma_ty sigma_term) (var_ty))
    sigma_ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varL'_term (sigma_ty : nat -> ty) (sigma_term : nat -> term) (x : nat)
  : subst_term sigma_ty sigma_term (var_term x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_ty : nat -> ty) (sigma_term : nat -> term)
  :
  pointwise_relation _ eq
    (funcomp (subst_term sigma_ty sigma_term) (var_term)) sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_ty (xi_ty : nat -> nat) (xi_term : nat -> nat) (x : nat) :
  ren_ty xi_ty xi_term (var_ty x) = var_ty (xi_ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ty_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty xi_ty xi_term) (var_ty))
    (funcomp (var_ty) xi_ty).
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_ty : nat -> nat) (xi_term : nat -> nat) (x : nat) :
  ren_term xi_ty xi_term (var_term x) = var_term (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_ty : nat -> nat) (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_ty xi_term) (var_term))
    (funcomp (var_term) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

#[global] Instance Subst_term : (Subst2 _ _ _ _) := @subst_term.

#[global] Instance Subst_ty : (Subst2 _ _ _ _) := @subst_ty.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Up_term_ty : (Up_ty _ _) := @up_term_ty.

#[global] Instance Up_ty_term : (Up_term _ _) := @up_ty_term.

#[global] Instance Up_ty_ty : (Up_ty _ _) := @up_ty_ty.

#[global] Instance Ren_term : (Ren2 _ _ _ _) := @ren_term.

#[global] Instance Ren_ty : (Ren2 _ _ _ _) := @ren_ty.

#[global] Instance VarInstance_term : (Var _ _) := @var_term.

#[global]
Instance VarInstance_ty : (Var _ _) := @var_ty.

Notation "[ sigma_ty ; sigma_term ]" := (subst_term sigma_ty sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ty ; sigma_term ]" := (subst_term sigma_ty sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "[ sigma_ty ; sigma_term ]" := (subst_ty sigma_ty sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ty ; sigma_term ]" := (subst_ty sigma_ty sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ty" := up_ty (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "↑__ty" := up_term_ty (only printing)  : subst_scope.

Notation "↑__term" := up_ty_term (only printing)  : subst_scope.

Notation "↑__ty" := up_ty_ty (only printing)  : subst_scope.

Notation "⟨ xi_ty ; xi_term ⟩" := (ren_term xi_ty xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_ty ; xi_term ⟩" := (ren_term xi_ty xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "⟨ xi_ty ; xi_term ⟩" := (ren_ty xi_ty xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_ty ; xi_term ⟩" := (ren_ty xi_ty xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_term ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var_term x) ( at level 5, format "x __term")  :
subst_scope.

Notation "'var'" := var_ty ( at level 1, only printing)  : subst_scope.

Notation "x '__ty'" := (@ids _ _ VarInstance_ty x)
( at level 5, format "x __ty", only printing)  : subst_scope.

Notation "x '__ty'" := (var_ty x) ( at level 5, format "x __ty")  :
subst_scope.

#[global]
Instance subst_term_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_term)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s t Eq_st =>
       eq_ind s
         (fun t' => subst_term f_ty f_term s = subst_term g_ty g_term t')
         (ext_term f_ty f_term g_ty g_term Eq_ty Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_term)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s =>
       ext_term f_ty f_term g_ty g_term Eq_ty Eq_term s).
Qed.

#[global]
Instance subst_ty_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_ty f_ty f_term s = subst_ty g_ty g_term t')
         (ext_ty f_ty f_term g_ty g_term Eq_ty Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_ty_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s =>
       ext_ty f_ty f_term g_ty g_term Eq_ty Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_term)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_ty f_term s = ren_term g_ty g_term t')
         (extRen_term f_ty f_term g_ty g_term Eq_ty Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_term)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s =>
       extRen_term f_ty f_term g_ty g_term Eq_ty Eq_term s).
Qed.

#[global]
Instance ren_ty_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_ty f_term s = ren_ty g_ty g_term t')
         (extRen_ty f_ty f_term g_ty g_term Eq_ty Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_ty_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty f_term g_term Eq_term s =>
       extRen_ty f_ty f_term g_ty g_term Eq_ty Eq_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ty, Var, ids, VarInstance_term, Var,
                      ids, Ren_ty, Ren2, ren2, Ren_term, Ren2, ren2,
                      Up_ty_ty, Up_ty, up_ty, Up_ty_term, Up_term, up_term,
                      Up_term_ty, Up_ty, up_ty, Up_term_term, Up_term,
                      up_term, Subst_ty, Subst2, subst2, Subst_term, Subst2,
                      subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ty, Var, ids,
                                            VarInstance_term, Var, ids,
                                            Ren_ty, Ren2, ren2, Ren_term,
                                            Ren2, ren2, Up_ty_ty, Up_ty,
                                            up_ty, Up_ty_term, Up_term,
                                            up_term, Up_term_ty, Up_ty,
                                            up_ty, Up_term_term, Up_term,
                                            up_term, Subst_ty, Subst2,
                                            subst2, Subst_term, Subst2,
                                            subst2 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substSubst_ty_pointwise
                 | progress setoid_rewrite substSubst_ty
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite substRen_ty_pointwise
                 | progress setoid_rewrite substRen_ty
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renSubst_ty_pointwise
                 | progress setoid_rewrite renSubst_ty
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite renRen'_ty_pointwise
                 | progress setoid_rewrite renRen_ty
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varLRen'_ty_pointwise
                 | progress setoid_rewrite varLRen'_ty
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite varL'_ty_pointwise
                 | progress setoid_rewrite varL'_ty
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite rinstId'_ty_pointwise
                 | progress setoid_rewrite rinstId'_ty
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress setoid_rewrite instId'_ty_pointwise
                 | progress setoid_rewrite instId'_ty
                 | progress
                    unfold up_term_term, up_term_ty, up_ty_term, up_ty_ty,
                     upRen_term_term, upRen_term_ty, upRen_ty_term,
                     upRen_ty_ty, up_ren
                 | progress cbn[subst_term subst_ty ren_term ren_ty]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ty, Var, ids, VarInstance_term, Var, ids,
                  Ren_ty, Ren2, ren2, Ren_term, Ren2, ren2, Up_ty_ty, Up_ty,
                  up_ty, Up_ty_term, Up_term, up_term, Up_term_ty, Up_ty,
                  up_ty, Up_term_term, Up_term, up_term, Subst_ty, Subst2,
                  subst2, Subst_term, Subst2, subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term;
                  try setoid_rewrite rinstInst'_ty_pointwise;
                  try setoid_rewrite rinstInst'_ty.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term;
                  try setoid_rewrite_left rinstInst'_ty_pointwise;
                  try setoid_rewrite_left rinstInst'_ty.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque subst_ty: rewrite.

#[global] Hint Opaque ren_term: rewrite.

#[global] Hint Opaque ren_ty: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

