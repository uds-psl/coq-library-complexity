From Undecidability Require Export fintype header_extensible.

Section utlc.
Inductive utlc (nutlc : nat) : Type :=
  | var_utlc : (fin) (nutlc) -> utlc (nutlc)
  | appUtlc : utlc  (nutlc) -> utlc  (nutlc) -> utlc (nutlc)
  | lamUtlc : utlc  ((S) nutlc) -> utlc (nutlc).

Lemma congr_appUtlc { mutlc : nat } { s0 : utlc  (mutlc) } { s1 : utlc  (mutlc) } { t0 : utlc  (mutlc) } { t1 : utlc  (mutlc) } (H1 : s0 = t0) (H2 : s1 = t1) : appUtlc (mutlc) s0 s1 = appUtlc (mutlc) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lamUtlc { mutlc : nat } { s0 : utlc  ((S) mutlc) } { t0 : utlc  ((S) mutlc) } (H1 : s0 = t0) : lamUtlc (mutlc) s0 = lamUtlc (mutlc) t0 .
Proof. congruence. Qed.

Definition upRen_utlc_utlc { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_utlc_utlc (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Fixpoint ren_utlc { mutlc : nat } { nutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (nutlc)) (s : utlc (mutlc)) : utlc (nutlc) :=
    match s with
    | var_utlc (_) s => (var_utlc (nutlc)) (xiutlc s)
    | appUtlc (_) s0 s1 => appUtlc (nutlc) ((ren_utlc xiutlc) s0) ((ren_utlc xiutlc) s1)
    | lamUtlc (_) s0 => lamUtlc (nutlc) ((ren_utlc (upRen_utlc_utlc xiutlc)) s0)
    end.

Definition up_utlc_utlc { m : nat } { nutlc : nat } (sigma : (fin) (m) -> utlc (nutlc)) : (fin) ((S) (m)) -> utlc ((S) nutlc) :=
  (scons) ((var_utlc ((S) nutlc)) (var_zero)) ((funcomp) (ren_utlc (shift)) sigma).

Definition upList_utlc_utlc (p : nat) { m : nat } { nutlc : nat } (sigma : (fin) (m) -> utlc (nutlc)) : (fin) (p+ (m)) -> utlc (p+ nutlc) :=
  scons_p  p ((funcomp) (var_utlc (p+ nutlc)) (zero_p p)) ((funcomp) (ren_utlc (shift_p p)) sigma).

Fixpoint subst_utlc { mutlc : nat } { nutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (nutlc)) (s : utlc (mutlc)) : utlc (nutlc) :=
    match s with
    | var_utlc (_) s => sigmautlc s
    | appUtlc (_) s0 s1 => appUtlc (nutlc) ((subst_utlc sigmautlc) s0) ((subst_utlc sigmautlc) s1)
    | lamUtlc (_) s0 => lamUtlc (nutlc) ((subst_utlc (up_utlc_utlc sigmautlc)) s0)
    end.

Definition upId_utlc_utlc { mutlc : nat } (sigma : (fin) (mutlc) -> utlc (mutlc)) (Eq : forall x, sigma x = (var_utlc (mutlc)) x) : forall x, (up_utlc_utlc sigma) x = (var_utlc ((S) mutlc)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_utlc (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_utlc_utlc { p : nat } { mutlc : nat } (sigma : (fin) (mutlc) -> utlc (mutlc)) (Eq : forall x, sigma x = (var_utlc (mutlc)) x) : forall x, (upList_utlc_utlc p sigma) x = (var_utlc (p+ mutlc)) x :=
  fun n => scons_p_eta (var_utlc (p+ mutlc)) (fun n => (ap) (ren_utlc (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_utlc { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (mutlc)) (Equtlc : forall x, sigmautlc x = (var_utlc (mutlc)) x) (s : utlc (mutlc)) : subst_utlc sigmautlc s = s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((idSubst_utlc sigmautlc Equtlc) s0) ((idSubst_utlc sigmautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((idSubst_utlc (up_utlc_utlc sigmautlc) (upId_utlc_utlc (_) Equtlc)) s0)
    end.

Definition upExtRen_utlc_utlc { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_utlc_utlc xi) x = (upRen_utlc_utlc zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_list_utlc_utlc { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_utlc_utlc p xi) x = (upRenList_utlc_utlc p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_utlc { mutlc : nat } { nutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (nutlc)) (zetautlc : (fin) (mutlc) -> (fin) (nutlc)) (Equtlc : forall x, xiutlc x = zetautlc x) (s : utlc (mutlc)) : ren_utlc xiutlc s = ren_utlc zetautlc s :=
    match s with
    | var_utlc (_) s => (ap) (var_utlc (nutlc)) (Equtlc s)
    | appUtlc (_) s0 s1 => congr_appUtlc ((extRen_utlc xiutlc zetautlc Equtlc) s0) ((extRen_utlc xiutlc zetautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((extRen_utlc (upRen_utlc_utlc xiutlc) (upRen_utlc_utlc zetautlc) (upExtRen_utlc_utlc (_) (_) Equtlc)) s0)
    end.

Definition upExt_utlc_utlc { m : nat } { nutlc : nat } (sigma : (fin) (m) -> utlc (nutlc)) (tau : (fin) (m) -> utlc (nutlc)) (Eq : forall x, sigma x = tau x) : forall x, (up_utlc_utlc sigma) x = (up_utlc_utlc tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_utlc (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_utlc_utlc { p : nat } { m : nat } { nutlc : nat } (sigma : (fin) (m) -> utlc (nutlc)) (tau : (fin) (m) -> utlc (nutlc)) (Eq : forall x, sigma x = tau x) : forall x, (upList_utlc_utlc p sigma) x = (upList_utlc_utlc p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_utlc (shift_p p)) (Eq n)).

Fixpoint ext_utlc { mutlc : nat } { nutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (nutlc)) (tauutlc : (fin) (mutlc) -> utlc (nutlc)) (Equtlc : forall x, sigmautlc x = tauutlc x) (s : utlc (mutlc)) : subst_utlc sigmautlc s = subst_utlc tauutlc s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((ext_utlc sigmautlc tauutlc Equtlc) s0) ((ext_utlc sigmautlc tauutlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((ext_utlc (up_utlc_utlc sigmautlc) (up_utlc_utlc tauutlc) (upExt_utlc_utlc (_) (_) Equtlc)) s0)
    end.

Definition up_ren_ren_utlc_utlc { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_utlc_utlc tau) (upRen_utlc_utlc xi)) x = (upRen_utlc_utlc theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_utlc_utlc { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_utlc_utlc p tau) (upRenList_utlc_utlc p xi)) x = (upRenList_utlc_utlc p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) (rhoutlc : (fin) (mutlc) -> (fin) (lutlc)) (Equtlc : forall x, ((funcomp) zetautlc xiutlc) x = rhoutlc x) (s : utlc (mutlc)) : ren_utlc zetautlc (ren_utlc xiutlc s) = ren_utlc rhoutlc s :=
    match s with
    | var_utlc (_) s => (ap) (var_utlc (lutlc)) (Equtlc s)
    | appUtlc (_) s0 s1 => congr_appUtlc ((compRenRen_utlc xiutlc zetautlc rhoutlc Equtlc) s0) ((compRenRen_utlc xiutlc zetautlc rhoutlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((compRenRen_utlc (upRen_utlc_utlc xiutlc) (upRen_utlc_utlc zetautlc) (upRen_utlc_utlc rhoutlc) (up_ren_ren (_) (_) (_) Equtlc)) s0)
    end.

Definition up_ren_subst_utlc_utlc { k : nat } { l : nat } { mutlc : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> utlc (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_utlc_utlc tau) (upRen_utlc_utlc xi)) x = (up_utlc_utlc theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_utlc (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_list_utlc_utlc { p : nat } { k : nat } { l : nat } { mutlc : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> utlc (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_utlc_utlc p tau) (upRenList_utlc_utlc p xi)) x = (upList_utlc_utlc p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_utlc (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) (thetautlc : (fin) (mutlc) -> utlc (lutlc)) (Equtlc : forall x, ((funcomp) tauutlc xiutlc) x = thetautlc x) (s : utlc (mutlc)) : subst_utlc tauutlc (ren_utlc xiutlc s) = subst_utlc thetautlc s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((compRenSubst_utlc xiutlc tauutlc thetautlc Equtlc) s0) ((compRenSubst_utlc xiutlc tauutlc thetautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((compRenSubst_utlc (upRen_utlc_utlc xiutlc) (up_utlc_utlc tauutlc) (up_utlc_utlc thetautlc) (up_ren_subst_utlc_utlc (_) (_) (_) Equtlc)) s0)
    end.

Definition up_subst_ren_utlc_utlc { k : nat } { lutlc : nat } { mutlc : nat } (sigma : (fin) (k) -> utlc (lutlc)) (zetautlc : (fin) (lutlc) -> (fin) (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) (ren_utlc zetautlc) sigma) x = theta x) : forall x, ((funcomp) (ren_utlc (upRen_utlc_utlc zetautlc)) (up_utlc_utlc sigma)) x = (up_utlc_utlc theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_utlc (shift) (upRen_utlc_utlc zetautlc) ((funcomp) (shift) zetautlc) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_utlc zetautlc (shift) ((funcomp) (shift) zetautlc) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_utlc (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_list_utlc_utlc { p : nat } { k : nat } { lutlc : nat } { mutlc : nat } (sigma : (fin) (k) -> utlc (lutlc)) (zetautlc : (fin) (lutlc) -> (fin) (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) (ren_utlc zetautlc) sigma) x = theta x) : forall x, ((funcomp) (ren_utlc (upRenList_utlc_utlc p zetautlc)) (upList_utlc_utlc p sigma)) x = (upList_utlc_utlc p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_utlc (p+ mutlc)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_utlc (shift_p p) (upRenList_utlc_utlc p zetautlc) ((funcomp) (shift_p p) zetautlc) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_utlc zetautlc (shift_p p) ((funcomp) (shift_p p) zetautlc) (fun x => eq_refl) (sigma n))) ((ap) (ren_utlc (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) (thetautlc : (fin) (mutlc) -> utlc (lutlc)) (Equtlc : forall x, ((funcomp) (ren_utlc zetautlc) sigmautlc) x = thetautlc x) (s : utlc (mutlc)) : ren_utlc zetautlc (subst_utlc sigmautlc s) = subst_utlc thetautlc s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((compSubstRen_utlc sigmautlc zetautlc thetautlc Equtlc) s0) ((compSubstRen_utlc sigmautlc zetautlc thetautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((compSubstRen_utlc (up_utlc_utlc sigmautlc) (upRen_utlc_utlc zetautlc) (up_utlc_utlc thetautlc) (up_subst_ren_utlc_utlc (_) (_) (_) Equtlc)) s0)
    end.

Definition up_subst_subst_utlc_utlc { k : nat } { lutlc : nat } { mutlc : nat } (sigma : (fin) (k) -> utlc (lutlc)) (tauutlc : (fin) (lutlc) -> utlc (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) (subst_utlc tauutlc) sigma) x = theta x) : forall x, ((funcomp) (subst_utlc (up_utlc_utlc tauutlc)) (up_utlc_utlc sigma)) x = (up_utlc_utlc theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_utlc (shift) (up_utlc_utlc tauutlc) ((funcomp) (up_utlc_utlc tauutlc) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_utlc tauutlc (shift) ((funcomp) (ren_utlc (shift)) tauutlc) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_utlc (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_utlc_utlc { p : nat } { k : nat } { lutlc : nat } { mutlc : nat } (sigma : (fin) (k) -> utlc (lutlc)) (tauutlc : (fin) (lutlc) -> utlc (mutlc)) (theta : (fin) (k) -> utlc (mutlc)) (Eq : forall x, ((funcomp) (subst_utlc tauutlc) sigma) x = theta x) : forall x, ((funcomp) (subst_utlc (upList_utlc_utlc p tauutlc)) (upList_utlc_utlc p sigma)) x = (upList_utlc_utlc p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_utlc (p+ lutlc)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_utlc (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_utlc (shift_p p) (upList_utlc_utlc p tauutlc) ((funcomp) (upList_utlc_utlc p tauutlc) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_utlc tauutlc (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_utlc (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) (thetautlc : (fin) (mutlc) -> utlc (lutlc)) (Equtlc : forall x, ((funcomp) (subst_utlc tauutlc) sigmautlc) x = thetautlc x) (s : utlc (mutlc)) : subst_utlc tauutlc (subst_utlc sigmautlc s) = subst_utlc thetautlc s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((compSubstSubst_utlc sigmautlc tauutlc thetautlc Equtlc) s0) ((compSubstSubst_utlc sigmautlc tauutlc thetautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((compSubstSubst_utlc (up_utlc_utlc sigmautlc) (up_utlc_utlc tauutlc) (up_utlc_utlc thetautlc) (up_subst_subst_utlc_utlc (_) (_) (_) Equtlc)) s0)
    end.

Definition rinstInst_up_utlc_utlc { m : nat } { nutlc : nat } (xi : (fin) (m) -> (fin) (nutlc)) (sigma : (fin) (m) -> utlc (nutlc)) (Eq : forall x, ((funcomp) (var_utlc (nutlc)) xi) x = sigma x) : forall x, ((funcomp) (var_utlc ((S) nutlc)) (upRen_utlc_utlc xi)) x = (up_utlc_utlc sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_utlc (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_list_utlc_utlc { p : nat } { m : nat } { nutlc : nat } (xi : (fin) (m) -> (fin) (nutlc)) (sigma : (fin) (m) -> utlc (nutlc)) (Eq : forall x, ((funcomp) (var_utlc (nutlc)) xi) x = sigma x) : forall x, ((funcomp) (var_utlc (p+ nutlc)) (upRenList_utlc_utlc p xi)) x = (upList_utlc_utlc p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_utlc (p+ nutlc)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_utlc (shift_p p)) (Eq n))).

Fixpoint rinst_inst_utlc { mutlc : nat } { nutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (nutlc)) (sigmautlc : (fin) (mutlc) -> utlc (nutlc)) (Equtlc : forall x, ((funcomp) (var_utlc (nutlc)) xiutlc) x = sigmautlc x) (s : utlc (mutlc)) : ren_utlc xiutlc s = subst_utlc sigmautlc s :=
    match s with
    | var_utlc (_) s => Equtlc s
    | appUtlc (_) s0 s1 => congr_appUtlc ((rinst_inst_utlc xiutlc sigmautlc Equtlc) s0) ((rinst_inst_utlc xiutlc sigmautlc Equtlc) s1)
    | lamUtlc (_) s0 => congr_lamUtlc ((rinst_inst_utlc (upRen_utlc_utlc xiutlc) (up_utlc_utlc sigmautlc) (rinstInst_up_utlc_utlc (_) (_) Equtlc)) s0)
    end.

Lemma rinstInst_utlc { mutlc : nat } { nutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (nutlc)) : ren_utlc xiutlc = subst_utlc ((funcomp) (var_utlc (nutlc)) xiutlc) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_utlc xiutlc (_) (fun n => eq_refl) x)). Qed.

Lemma instId_utlc { mutlc : nat } : subst_utlc (var_utlc (mutlc)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_utlc (var_utlc (mutlc)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_utlc { mutlc : nat } : @ren_utlc (mutlc) (mutlc) (id) = id .
Proof. exact ((eq_trans) (rinstInst_utlc ((id) (_))) instId_utlc). Qed.

Lemma varL_utlc { mutlc : nat } { nutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (nutlc)) : (funcomp) (subst_utlc sigmautlc) (var_utlc (mutlc)) = sigmautlc .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_utlc { mutlc : nat } { nutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (nutlc)) : (funcomp) (ren_utlc xiutlc) (var_utlc (mutlc)) = (funcomp) (var_utlc (nutlc)) xiutlc .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) (s : utlc (mutlc)) : subst_utlc tauutlc (subst_utlc sigmautlc s) = subst_utlc ((funcomp) (subst_utlc tauutlc) sigmautlc) s .
Proof. exact (compSubstSubst_utlc sigmautlc tauutlc (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) : (funcomp) (subst_utlc tauutlc) (subst_utlc sigmautlc) = subst_utlc ((funcomp) (subst_utlc tauutlc) sigmautlc) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_utlc sigmautlc tauutlc n)). Qed.

Lemma compRen_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) (s : utlc (mutlc)) : ren_utlc zetautlc (subst_utlc sigmautlc s) = subst_utlc ((funcomp) (ren_utlc zetautlc) sigmautlc) s .
Proof. exact (compSubstRen_utlc sigmautlc zetautlc (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (sigmautlc : (fin) (mutlc) -> utlc (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) : (funcomp) (ren_utlc zetautlc) (subst_utlc sigmautlc) = subst_utlc ((funcomp) (ren_utlc zetautlc) sigmautlc) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_utlc sigmautlc zetautlc n)). Qed.

Lemma renComp_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) (s : utlc (mutlc)) : subst_utlc tauutlc (ren_utlc xiutlc s) = subst_utlc ((funcomp) tauutlc xiutlc) s .
Proof. exact (compRenSubst_utlc xiutlc tauutlc (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (tauutlc : (fin) (kutlc) -> utlc (lutlc)) : (funcomp) (subst_utlc tauutlc) (ren_utlc xiutlc) = subst_utlc ((funcomp) tauutlc xiutlc) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_utlc xiutlc tauutlc n)). Qed.

Lemma renRen_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) (s : utlc (mutlc)) : ren_utlc zetautlc (ren_utlc xiutlc s) = ren_utlc ((funcomp) zetautlc xiutlc) s .
Proof. exact (compRenRen_utlc xiutlc zetautlc (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_utlc { kutlc : nat } { lutlc : nat } { mutlc : nat } (xiutlc : (fin) (mutlc) -> (fin) (kutlc)) (zetautlc : (fin) (kutlc) -> (fin) (lutlc)) : (funcomp) (ren_utlc zetautlc) (ren_utlc xiutlc) = ren_utlc ((funcomp) zetautlc xiutlc) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_utlc xiutlc zetautlc n)). Qed.

End utlc.

Section pcf.
Inductive pcf (npcf : nat) : Type :=
  | var_pcf : (fin) (npcf) -> pcf (npcf)
  | constPcf : nat   -> pcf (npcf)
  | appPcf : pcf  (npcf) -> pcf  (npcf) -> pcf (npcf)
  | lamPcf : pcf  ((S) npcf) -> pcf (npcf)
  | fixPcf : pcf  (npcf) -> pcf (npcf)
  | caseNatPcf : pcf  (npcf) -> pcf  (npcf) -> pcf  (npcf) -> pcf (npcf)
  | succPcf : pcf (npcf).

Lemma congr_constPcf { mpcf : nat } { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : constPcf (mpcf) s0 = constPcf (mpcf) t0 .
Proof. congruence. Qed.

Lemma congr_appPcf { mpcf : nat } { s0 : pcf  (mpcf) } { s1 : pcf  (mpcf) } { t0 : pcf  (mpcf) } { t1 : pcf  (mpcf) } (H1 : s0 = t0) (H2 : s1 = t1) : appPcf (mpcf) s0 s1 = appPcf (mpcf) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lamPcf { mpcf : nat } { s0 : pcf  ((S) mpcf) } { t0 : pcf  ((S) mpcf) } (H1 : s0 = t0) : lamPcf (mpcf) s0 = lamPcf (mpcf) t0 .
Proof. congruence. Qed.

Lemma congr_fixPcf { mpcf : nat } { s0 : pcf  (mpcf) } { t0 : pcf  (mpcf) } (H1 : s0 = t0) : fixPcf (mpcf) s0 = fixPcf (mpcf) t0 .
Proof. congruence. Qed.

Lemma congr_caseNatPcf { mpcf : nat } { s0 : pcf  (mpcf) } { s1 : pcf  (mpcf) } { s2 : pcf  (mpcf) } { t0 : pcf  (mpcf) } { t1 : pcf  (mpcf) } { t2 : pcf  (mpcf) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : caseNatPcf (mpcf) s0 s1 s2 = caseNatPcf (mpcf) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_succPcf { mpcf : nat } : succPcf (mpcf) = succPcf (mpcf) .
Proof. congruence. Qed.

Definition upRen_pcf_pcf { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_pcf_pcf (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Fixpoint ren_pcf { mpcf : nat } { npcf : nat } (xipcf : (fin) (mpcf) -> (fin) (npcf)) (s : pcf (mpcf)) : pcf (npcf) :=
    match s with
    | var_pcf (_) s => (var_pcf (npcf)) (xipcf s)
    | constPcf (_) s0 => constPcf (npcf) ((fun x => x) s0)
    | appPcf (_) s0 s1 => appPcf (npcf) ((ren_pcf xipcf) s0) ((ren_pcf xipcf) s1)
    | lamPcf (_) s0 => lamPcf (npcf) ((ren_pcf (upRen_pcf_pcf xipcf)) s0)
    | fixPcf (_) s0 => fixPcf (npcf) ((ren_pcf xipcf) s0)
    | caseNatPcf (_) s0 s1 s2 => caseNatPcf (npcf) ((ren_pcf xipcf) s0) ((ren_pcf xipcf) s1) ((ren_pcf xipcf) s2)
    | succPcf (_)  => succPcf (npcf)
    end.

Definition up_pcf_pcf { m : nat } { npcf : nat } (sigma : (fin) (m) -> pcf (npcf)) : (fin) ((S) (m)) -> pcf ((S) npcf) :=
  (scons) ((var_pcf ((S) npcf)) (var_zero)) ((funcomp) (ren_pcf (shift)) sigma).

Definition upList_pcf_pcf (p : nat) { m : nat } { npcf : nat } (sigma : (fin) (m) -> pcf (npcf)) : (fin) (p+ (m)) -> pcf (p+ npcf) :=
  scons_p  p ((funcomp) (var_pcf (p+ npcf)) (zero_p p)) ((funcomp) (ren_pcf (shift_p p)) sigma).

Fixpoint subst_pcf { mpcf : nat } { npcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (npcf)) (s : pcf (mpcf)) : pcf (npcf) :=
    match s with
    | var_pcf (_) s => sigmapcf s
    | constPcf (_) s0 => constPcf (npcf) ((fun x => x) s0)
    | appPcf (_) s0 s1 => appPcf (npcf) ((subst_pcf sigmapcf) s0) ((subst_pcf sigmapcf) s1)
    | lamPcf (_) s0 => lamPcf (npcf) ((subst_pcf (up_pcf_pcf sigmapcf)) s0)
    | fixPcf (_) s0 => fixPcf (npcf) ((subst_pcf sigmapcf) s0)
    | caseNatPcf (_) s0 s1 s2 => caseNatPcf (npcf) ((subst_pcf sigmapcf) s0) ((subst_pcf sigmapcf) s1) ((subst_pcf sigmapcf) s2)
    | succPcf (_)  => succPcf (npcf)
    end.

Definition upId_pcf_pcf { mpcf : nat } (sigma : (fin) (mpcf) -> pcf (mpcf)) (Eq : forall x, sigma x = (var_pcf (mpcf)) x) : forall x, (up_pcf_pcf sigma) x = (var_pcf ((S) mpcf)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_pcf (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_pcf_pcf { p : nat } { mpcf : nat } (sigma : (fin) (mpcf) -> pcf (mpcf)) (Eq : forall x, sigma x = (var_pcf (mpcf)) x) : forall x, (upList_pcf_pcf p sigma) x = (var_pcf (p+ mpcf)) x :=
  fun n => scons_p_eta (var_pcf (p+ mpcf)) (fun n => (ap) (ren_pcf (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_pcf { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (mpcf)) (Eqpcf : forall x, sigmapcf x = (var_pcf (mpcf)) x) (s : pcf (mpcf)) : subst_pcf sigmapcf s = s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((idSubst_pcf sigmapcf Eqpcf) s0) ((idSubst_pcf sigmapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((idSubst_pcf (up_pcf_pcf sigmapcf) (upId_pcf_pcf (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((idSubst_pcf sigmapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((idSubst_pcf sigmapcf Eqpcf) s0) ((idSubst_pcf sigmapcf Eqpcf) s1) ((idSubst_pcf sigmapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition upExtRen_pcf_pcf { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_pcf_pcf xi) x = (upRen_pcf_pcf zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_list_pcf_pcf { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_pcf_pcf p xi) x = (upRenList_pcf_pcf p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_pcf { mpcf : nat } { npcf : nat } (xipcf : (fin) (mpcf) -> (fin) (npcf)) (zetapcf : (fin) (mpcf) -> (fin) (npcf)) (Eqpcf : forall x, xipcf x = zetapcf x) (s : pcf (mpcf)) : ren_pcf xipcf s = ren_pcf zetapcf s :=
    match s with
    | var_pcf (_) s => (ap) (var_pcf (npcf)) (Eqpcf s)
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((extRen_pcf xipcf zetapcf Eqpcf) s0) ((extRen_pcf xipcf zetapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((extRen_pcf (upRen_pcf_pcf xipcf) (upRen_pcf_pcf zetapcf) (upExtRen_pcf_pcf (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((extRen_pcf xipcf zetapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((extRen_pcf xipcf zetapcf Eqpcf) s0) ((extRen_pcf xipcf zetapcf Eqpcf) s1) ((extRen_pcf xipcf zetapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition upExt_pcf_pcf { m : nat } { npcf : nat } (sigma : (fin) (m) -> pcf (npcf)) (tau : (fin) (m) -> pcf (npcf)) (Eq : forall x, sigma x = tau x) : forall x, (up_pcf_pcf sigma) x = (up_pcf_pcf tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_pcf (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_pcf_pcf { p : nat } { m : nat } { npcf : nat } (sigma : (fin) (m) -> pcf (npcf)) (tau : (fin) (m) -> pcf (npcf)) (Eq : forall x, sigma x = tau x) : forall x, (upList_pcf_pcf p sigma) x = (upList_pcf_pcf p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_pcf (shift_p p)) (Eq n)).

Fixpoint ext_pcf { mpcf : nat } { npcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (npcf)) (taupcf : (fin) (mpcf) -> pcf (npcf)) (Eqpcf : forall x, sigmapcf x = taupcf x) (s : pcf (mpcf)) : subst_pcf sigmapcf s = subst_pcf taupcf s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((ext_pcf sigmapcf taupcf Eqpcf) s0) ((ext_pcf sigmapcf taupcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((ext_pcf (up_pcf_pcf sigmapcf) (up_pcf_pcf taupcf) (upExt_pcf_pcf (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((ext_pcf sigmapcf taupcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((ext_pcf sigmapcf taupcf Eqpcf) s0) ((ext_pcf sigmapcf taupcf Eqpcf) s1) ((ext_pcf sigmapcf taupcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition up_ren_ren_pcf_pcf { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_pcf_pcf tau) (upRen_pcf_pcf xi)) x = (upRen_pcf_pcf theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_pcf_pcf { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_pcf_pcf p tau) (upRenList_pcf_pcf p xi)) x = (upRenList_pcf_pcf p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) (rhopcf : (fin) (mpcf) -> (fin) (lpcf)) (Eqpcf : forall x, ((funcomp) zetapcf xipcf) x = rhopcf x) (s : pcf (mpcf)) : ren_pcf zetapcf (ren_pcf xipcf s) = ren_pcf rhopcf s :=
    match s with
    | var_pcf (_) s => (ap) (var_pcf (lpcf)) (Eqpcf s)
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s0) ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((compRenRen_pcf (upRen_pcf_pcf xipcf) (upRen_pcf_pcf zetapcf) (upRen_pcf_pcf rhopcf) (up_ren_ren (_) (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s0) ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s1) ((compRenRen_pcf xipcf zetapcf rhopcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition up_ren_subst_pcf_pcf { k : nat } { l : nat } { mpcf : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> pcf (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_pcf_pcf tau) (upRen_pcf_pcf xi)) x = (up_pcf_pcf theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_pcf (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_list_pcf_pcf { p : nat } { k : nat } { l : nat } { mpcf : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> pcf (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_pcf_pcf p tau) (upRenList_pcf_pcf p xi)) x = (upList_pcf_pcf p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_pcf (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) (thetapcf : (fin) (mpcf) -> pcf (lpcf)) (Eqpcf : forall x, ((funcomp) taupcf xipcf) x = thetapcf x) (s : pcf (mpcf)) : subst_pcf taupcf (ren_pcf xipcf s) = subst_pcf thetapcf s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s0) ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((compRenSubst_pcf (upRen_pcf_pcf xipcf) (up_pcf_pcf taupcf) (up_pcf_pcf thetapcf) (up_ren_subst_pcf_pcf (_) (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s0) ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s1) ((compRenSubst_pcf xipcf taupcf thetapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition up_subst_ren_pcf_pcf { k : nat } { lpcf : nat } { mpcf : nat } (sigma : (fin) (k) -> pcf (lpcf)) (zetapcf : (fin) (lpcf) -> (fin) (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) (ren_pcf zetapcf) sigma) x = theta x) : forall x, ((funcomp) (ren_pcf (upRen_pcf_pcf zetapcf)) (up_pcf_pcf sigma)) x = (up_pcf_pcf theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_pcf (shift) (upRen_pcf_pcf zetapcf) ((funcomp) (shift) zetapcf) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_pcf zetapcf (shift) ((funcomp) (shift) zetapcf) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_pcf (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_list_pcf_pcf { p : nat } { k : nat } { lpcf : nat } { mpcf : nat } (sigma : (fin) (k) -> pcf (lpcf)) (zetapcf : (fin) (lpcf) -> (fin) (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) (ren_pcf zetapcf) sigma) x = theta x) : forall x, ((funcomp) (ren_pcf (upRenList_pcf_pcf p zetapcf)) (upList_pcf_pcf p sigma)) x = (upList_pcf_pcf p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_pcf (p+ mpcf)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_pcf (shift_p p) (upRenList_pcf_pcf p zetapcf) ((funcomp) (shift_p p) zetapcf) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_pcf zetapcf (shift_p p) ((funcomp) (shift_p p) zetapcf) (fun x => eq_refl) (sigma n))) ((ap) (ren_pcf (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) (thetapcf : (fin) (mpcf) -> pcf (lpcf)) (Eqpcf : forall x, ((funcomp) (ren_pcf zetapcf) sigmapcf) x = thetapcf x) (s : pcf (mpcf)) : ren_pcf zetapcf (subst_pcf sigmapcf s) = subst_pcf thetapcf s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s0) ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((compSubstRen_pcf (up_pcf_pcf sigmapcf) (upRen_pcf_pcf zetapcf) (up_pcf_pcf thetapcf) (up_subst_ren_pcf_pcf (_) (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s0) ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s1) ((compSubstRen_pcf sigmapcf zetapcf thetapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition up_subst_subst_pcf_pcf { k : nat } { lpcf : nat } { mpcf : nat } (sigma : (fin) (k) -> pcf (lpcf)) (taupcf : (fin) (lpcf) -> pcf (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) (subst_pcf taupcf) sigma) x = theta x) : forall x, ((funcomp) (subst_pcf (up_pcf_pcf taupcf)) (up_pcf_pcf sigma)) x = (up_pcf_pcf theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_pcf (shift) (up_pcf_pcf taupcf) ((funcomp) (up_pcf_pcf taupcf) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_pcf taupcf (shift) ((funcomp) (ren_pcf (shift)) taupcf) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_pcf (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_pcf_pcf { p : nat } { k : nat } { lpcf : nat } { mpcf : nat } (sigma : (fin) (k) -> pcf (lpcf)) (taupcf : (fin) (lpcf) -> pcf (mpcf)) (theta : (fin) (k) -> pcf (mpcf)) (Eq : forall x, ((funcomp) (subst_pcf taupcf) sigma) x = theta x) : forall x, ((funcomp) (subst_pcf (upList_pcf_pcf p taupcf)) (upList_pcf_pcf p sigma)) x = (upList_pcf_pcf p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_pcf (p+ lpcf)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_pcf (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_pcf (shift_p p) (upList_pcf_pcf p taupcf) ((funcomp) (upList_pcf_pcf p taupcf) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_pcf taupcf (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_pcf (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) (thetapcf : (fin) (mpcf) -> pcf (lpcf)) (Eqpcf : forall x, ((funcomp) (subst_pcf taupcf) sigmapcf) x = thetapcf x) (s : pcf (mpcf)) : subst_pcf taupcf (subst_pcf sigmapcf s) = subst_pcf thetapcf s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s0) ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((compSubstSubst_pcf (up_pcf_pcf sigmapcf) (up_pcf_pcf taupcf) (up_pcf_pcf thetapcf) (up_subst_subst_pcf_pcf (_) (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s0) ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s1) ((compSubstSubst_pcf sigmapcf taupcf thetapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Definition rinstInst_up_pcf_pcf { m : nat } { npcf : nat } (xi : (fin) (m) -> (fin) (npcf)) (sigma : (fin) (m) -> pcf (npcf)) (Eq : forall x, ((funcomp) (var_pcf (npcf)) xi) x = sigma x) : forall x, ((funcomp) (var_pcf ((S) npcf)) (upRen_pcf_pcf xi)) x = (up_pcf_pcf sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_pcf (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_list_pcf_pcf { p : nat } { m : nat } { npcf : nat } (xi : (fin) (m) -> (fin) (npcf)) (sigma : (fin) (m) -> pcf (npcf)) (Eq : forall x, ((funcomp) (var_pcf (npcf)) xi) x = sigma x) : forall x, ((funcomp) (var_pcf (p+ npcf)) (upRenList_pcf_pcf p xi)) x = (upList_pcf_pcf p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_pcf (p+ npcf)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_pcf (shift_p p)) (Eq n))).

Fixpoint rinst_inst_pcf { mpcf : nat } { npcf : nat } (xipcf : (fin) (mpcf) -> (fin) (npcf)) (sigmapcf : (fin) (mpcf) -> pcf (npcf)) (Eqpcf : forall x, ((funcomp) (var_pcf (npcf)) xipcf) x = sigmapcf x) (s : pcf (mpcf)) : ren_pcf xipcf s = subst_pcf sigmapcf s :=
    match s with
    | var_pcf (_) s => Eqpcf s
    | constPcf (_) s0 => congr_constPcf ((fun x => (eq_refl) x) s0)
    | appPcf (_) s0 s1 => congr_appPcf ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s0) ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s1)
    | lamPcf (_) s0 => congr_lamPcf ((rinst_inst_pcf (upRen_pcf_pcf xipcf) (up_pcf_pcf sigmapcf) (rinstInst_up_pcf_pcf (_) (_) Eqpcf)) s0)
    | fixPcf (_) s0 => congr_fixPcf ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s0)
    | caseNatPcf (_) s0 s1 s2 => congr_caseNatPcf ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s0) ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s1) ((rinst_inst_pcf xipcf sigmapcf Eqpcf) s2)
    | succPcf (_)  => congr_succPcf 
    end.

Lemma rinstInst_pcf { mpcf : nat } { npcf : nat } (xipcf : (fin) (mpcf) -> (fin) (npcf)) : ren_pcf xipcf = subst_pcf ((funcomp) (var_pcf (npcf)) xipcf) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_pcf xipcf (_) (fun n => eq_refl) x)). Qed.

Lemma instId_pcf { mpcf : nat } : subst_pcf (var_pcf (mpcf)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_pcf (var_pcf (mpcf)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_pcf { mpcf : nat } : @ren_pcf (mpcf) (mpcf) (id) = id .
Proof. exact ((eq_trans) (rinstInst_pcf ((id) (_))) instId_pcf). Qed.

Lemma varL_pcf { mpcf : nat } { npcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (npcf)) : (funcomp) (subst_pcf sigmapcf) (var_pcf (mpcf)) = sigmapcf .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_pcf { mpcf : nat } { npcf : nat } (xipcf : (fin) (mpcf) -> (fin) (npcf)) : (funcomp) (ren_pcf xipcf) (var_pcf (mpcf)) = (funcomp) (var_pcf (npcf)) xipcf .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) (s : pcf (mpcf)) : subst_pcf taupcf (subst_pcf sigmapcf s) = subst_pcf ((funcomp) (subst_pcf taupcf) sigmapcf) s .
Proof. exact (compSubstSubst_pcf sigmapcf taupcf (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) : (funcomp) (subst_pcf taupcf) (subst_pcf sigmapcf) = subst_pcf ((funcomp) (subst_pcf taupcf) sigmapcf) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_pcf sigmapcf taupcf n)). Qed.

Lemma compRen_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) (s : pcf (mpcf)) : ren_pcf zetapcf (subst_pcf sigmapcf s) = subst_pcf ((funcomp) (ren_pcf zetapcf) sigmapcf) s .
Proof. exact (compSubstRen_pcf sigmapcf zetapcf (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (sigmapcf : (fin) (mpcf) -> pcf (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) : (funcomp) (ren_pcf zetapcf) (subst_pcf sigmapcf) = subst_pcf ((funcomp) (ren_pcf zetapcf) sigmapcf) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_pcf sigmapcf zetapcf n)). Qed.

Lemma renComp_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) (s : pcf (mpcf)) : subst_pcf taupcf (ren_pcf xipcf s) = subst_pcf ((funcomp) taupcf xipcf) s .
Proof. exact (compRenSubst_pcf xipcf taupcf (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (taupcf : (fin) (kpcf) -> pcf (lpcf)) : (funcomp) (subst_pcf taupcf) (ren_pcf xipcf) = subst_pcf ((funcomp) taupcf xipcf) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_pcf xipcf taupcf n)). Qed.

Lemma renRen_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) (s : pcf (mpcf)) : ren_pcf zetapcf (ren_pcf xipcf s) = ren_pcf ((funcomp) zetapcf xipcf) s .
Proof. exact (compRenRen_pcf xipcf zetapcf (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_pcf { kpcf : nat } { lpcf : nat } { mpcf : nat } (xipcf : (fin) (mpcf) -> (fin) (kpcf)) (zetapcf : (fin) (kpcf) -> (fin) (lpcf)) : (funcomp) (ren_pcf zetapcf) (ren_pcf xipcf) = ren_pcf ((funcomp) zetapcf xipcf) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_pcf xipcf zetapcf n)). Qed.

End pcf.

Arguments var_utlc {nutlc}.

Arguments appUtlc {nutlc}.

Arguments lamUtlc {nutlc}.

Arguments var_pcf {npcf}.

Arguments constPcf {npcf}.

Arguments appPcf {npcf}.

Arguments lamPcf {npcf}.

Arguments fixPcf {npcf}.

Arguments caseNatPcf {npcf}.

Arguments succPcf {npcf}.

Global Instance Subst_utlc { mutlc : nat } { nutlc : nat } : Subst1 ((fin) (mutlc) -> utlc (nutlc)) (utlc (mutlc)) (utlc (nutlc)) := @subst_utlc (mutlc) (nutlc) .

Global Instance Subst_pcf { mpcf : nat } { npcf : nat } : Subst1 ((fin) (mpcf) -> pcf (npcf)) (pcf (mpcf)) (pcf (npcf)) := @subst_pcf (mpcf) (npcf) .

Global Instance Ren_utlc { mutlc : nat } { nutlc : nat } : Ren1 ((fin) (mutlc) -> (fin) (nutlc)) (utlc (mutlc)) (utlc (nutlc)) := @ren_utlc (mutlc) (nutlc) .

Global Instance Ren_pcf { mpcf : nat } { npcf : nat } : Ren1 ((fin) (mpcf) -> (fin) (npcf)) (pcf (mpcf)) (pcf (npcf)) := @ren_pcf (mpcf) (npcf) .

Global Instance VarInstance_utlc { mutlc : nat } : Var ((fin) (mutlc)) (utlc (mutlc)) := @var_utlc (mutlc) .

Notation "x '__utlc'" := (var_utlc x) (at level 5, format "x __utlc") : subst_scope.

Notation "x '__utlc'" := (@ids (_) (_) VarInstance_utlc x) (at level 5, only printing, format "x __utlc") : subst_scope.

Notation "'var'" := (var_utlc) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_pcf { mpcf : nat } : Var ((fin) (mpcf)) (pcf (mpcf)) := @var_pcf (mpcf) .

Notation "x '__pcf'" := (var_pcf x) (at level 5, format "x __pcf") : subst_scope.

Notation "x '__pcf'" := (@ids (_) (_) VarInstance_pcf x) (at level 5, only printing, format "x __pcf") : subst_scope.

Notation "'var'" := (var_pcf) (only printing, at level 1) : subst_scope.

Class Up_utlc X Y := up_utlc : X -> Y.

Notation "↑__utlc" := (up_utlc) (only printing) : subst_scope.

Class Up_pcf X Y := up_pcf : X -> Y.

Notation "↑__pcf" := (up_pcf) (only printing) : subst_scope.

Notation "↑__utlc" := (up_utlc_utlc) (only printing) : subst_scope.

Global Instance Up_utlc_utlc { m : nat } { nutlc : nat } : Up_utlc (_) (_) := @up_utlc_utlc (m) (nutlc) .

Notation "↑__pcf" := (up_pcf_pcf) (only printing) : subst_scope.

Global Instance Up_pcf_pcf { m : nat } { npcf : nat } : Up_pcf (_) (_) := @up_pcf_pcf (m) (npcf) .

Notation "s [ sigmautlc ]" := (subst_utlc sigmautlc s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmautlc ]" := (subst_utlc sigmautlc) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiutlc ⟩" := (ren_utlc xiutlc s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiutlc ⟩" := (ren_utlc xiutlc) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmapcf ]" := (subst_pcf sigmapcf s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmapcf ]" := (subst_pcf sigmapcf) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xipcf ⟩" := (ren_pcf xipcf s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xipcf ⟩" := (ren_pcf xipcf) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_utlc,  Subst_pcf,  Ren_utlc,  Ren_pcf,  VarInstance_utlc,  VarInstance_pcf.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_utlc,  Subst_pcf,  Ren_utlc,  Ren_pcf,  VarInstance_utlc,  VarInstance_pcf in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_utlc| progress rewrite ?compComp_utlc| progress rewrite ?compComp'_utlc| progress rewrite ?instId_pcf| progress rewrite ?compComp_pcf| progress rewrite ?compComp'_pcf| progress rewrite ?rinstId_utlc| progress rewrite ?compRen_utlc| progress rewrite ?compRen'_utlc| progress rewrite ?renComp_utlc| progress rewrite ?renComp'_utlc| progress rewrite ?renRen_utlc| progress rewrite ?renRen'_utlc| progress rewrite ?rinstId_pcf| progress rewrite ?compRen_pcf| progress rewrite ?compRen'_pcf| progress rewrite ?renComp_pcf| progress rewrite ?renComp'_pcf| progress rewrite ?renRen_pcf| progress rewrite ?renRen'_pcf| progress rewrite ?varL_utlc| progress rewrite ?varL_pcf| progress rewrite ?varLRen_utlc| progress rewrite ?varLRen_pcf| progress (unfold up_ren, upRen_utlc_utlc, upRenList_utlc_utlc, upRen_pcf_pcf, upRenList_pcf_pcf, up_utlc_utlc, upList_utlc_utlc, up_pcf_pcf, upList_pcf_pcf)| progress (cbn [subst_utlc subst_pcf ren_utlc ren_pcf])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_utlc in *| progress rewrite ?compComp_utlc in *| progress rewrite ?compComp'_utlc in *| progress rewrite ?instId_pcf in *| progress rewrite ?compComp_pcf in *| progress rewrite ?compComp'_pcf in *| progress rewrite ?rinstId_utlc in *| progress rewrite ?compRen_utlc in *| progress rewrite ?compRen'_utlc in *| progress rewrite ?renComp_utlc in *| progress rewrite ?renComp'_utlc in *| progress rewrite ?renRen_utlc in *| progress rewrite ?renRen'_utlc in *| progress rewrite ?rinstId_pcf in *| progress rewrite ?compRen_pcf in *| progress rewrite ?compRen'_pcf in *| progress rewrite ?renComp_pcf in *| progress rewrite ?renComp'_pcf in *| progress rewrite ?renRen_pcf in *| progress rewrite ?renRen'_pcf in *| progress rewrite ?varL_utlc in *| progress rewrite ?varL_pcf in *| progress rewrite ?varLRen_utlc in *| progress rewrite ?varLRen_pcf in *| progress (unfold up_ren, upRen_utlc_utlc, upRenList_utlc_utlc, upRen_pcf_pcf, upRenList_pcf_pcf, up_utlc_utlc, upList_utlc_utlc, up_pcf_pcf, upList_pcf_pcf in *)| progress (cbn [subst_utlc subst_pcf ren_utlc ren_pcf] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_utlc); try repeat (erewrite rinstInst_pcf).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_utlc); try repeat (erewrite <- rinstInst_pcf).
