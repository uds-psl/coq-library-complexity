From Undecidability Require Export fintype header_extensible.

Section tm.
Inductive tm (ntm : nat) : Type :=
  | var_tm : (fin) (ntm) -> tm (ntm)
  | app : tm  (ntm) -> tm  (ntm) -> tm (ntm)
  | lam : tm  ((S) ntm) -> tm (ntm).

Lemma congr_app { mtm : nat } { s0 : tm  (mtm) } { s1 : tm  (mtm) } { t0 : tm  (mtm) } { t1 : tm  (mtm) } (H1 : s0 = t0) (H2 : s1 = t1) : app (mtm) s0 s1 = app (mtm) t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam { mtm : nat } { s0 : tm  ((S) mtm) } { t0 : tm  ((S) mtm) } (H1 : s0 = t0) : lam (mtm) s0 = lam (mtm) t0 .
Proof. congruence. Qed.

Definition upRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Definition upRenList_tm_tm (p : nat) { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) (p+ (m)) -> (fin) (p+ (n)) :=
  upRen_p p xi.

Fixpoint ren_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s with
    | var_tm (_) s => (var_tm (ntm)) (xitm s)
    | app (_) s0 s1 => app (ntm) ((ren_tm xitm) s0) ((ren_tm xitm) s1)
    | lam (_) s0 => lam (ntm) ((ren_tm (upRen_tm_tm xitm)) s0)
    end.

Definition up_tm_tm { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) : (fin) ((S) (m)) -> tm ((S) ntm) :=
  (scons) ((var_tm ((S) ntm)) (var_zero)) ((funcomp) (ren_tm (shift)) sigma).

Definition upList_tm_tm (p : nat) { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) : (fin) (p+ (m)) -> tm (p+ ntm) :=
  scons_p  p ((funcomp) (var_tm (p+ ntm)) (zero_p p)) ((funcomp) (ren_tm (shift_p p)) sigma).

Fixpoint subst_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (s : tm (mtm)) : tm (ntm) :=
    match s with
    | var_tm (_) s => sigmatm s
    | app (_) s0 s1 => app (ntm) ((subst_tm sigmatm) s0) ((subst_tm sigmatm) s1)
    | lam (_) s0 => lam (ntm) ((subst_tm (up_tm_tm sigmatm)) s0)
    end.

Definition upId_tm_tm { mtm : nat } (sigma : (fin) (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (up_tm_tm sigma) x = (var_tm ((S) mtm)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upIdList_tm_tm { p : nat } { mtm : nat } (sigma : (fin) (mtm) -> tm (mtm)) (Eq : forall x, sigma x = (var_tm (mtm)) x) : forall x, (upList_tm_tm p sigma) x = (var_tm (p+ mtm)) x :=
  fun n => scons_p_eta (var_tm (p+ mtm)) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)) (fun n => eq_refl).

Fixpoint idSubst_tm { mtm : nat } (sigmatm : (fin) (mtm) -> tm (mtm)) (Eqtm : forall x, sigmatm x = (var_tm (mtm)) x) (s : tm (mtm)) : subst_tm sigmatm s = s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((idSubst_tm sigmatm Eqtm) s0) ((idSubst_tm sigmatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((idSubst_tm (up_tm_tm sigmatm) (upId_tm_tm (_) Eqtm)) s0)
    end.

Definition upExtRen_tm_tm { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_tm_tm xi) x = (upRen_tm_tm zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExtRen_list_tm_tm { p : nat } { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRenList_tm_tm p xi) x = (upRenList_tm_tm p zeta) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (shift_p p) (Eq n)).

Fixpoint extRen_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (zetatm : (fin) (mtm) -> (fin) (ntm)) (Eqtm : forall x, xitm x = zetatm x) (s : tm (mtm)) : ren_tm xitm s = ren_tm zetatm s :=
    match s with
    | var_tm (_) s => (ap) (var_tm (ntm)) (Eqtm s)
    | app (_) s0 s1 => congr_app ((extRen_tm xitm zetatm Eqtm) s0) ((extRen_tm xitm zetatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((extRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upExtRen_tm_tm (_) (_) Eqtm)) s0)
    end.

Definition upExt_tm_tm { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) (tau : (fin) (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (up_tm_tm sigma) x = (up_tm_tm tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition upExt_list_tm_tm { p : nat } { m : nat } { ntm : nat } (sigma : (fin) (m) -> tm (ntm)) (tau : (fin) (m) -> tm (ntm)) (Eq : forall x, sigma x = tau x) : forall x, (upList_tm_tm p sigma) x = (upList_tm_tm p tau) x :=
  fun n => scons_p_congr (fun n => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n)).

Fixpoint ext_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) (tautm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, sigmatm x = tautm x) (s : tm (mtm)) : subst_tm sigmatm s = subst_tm tautm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((ext_tm sigmatm tautm Eqtm) s0) ((ext_tm sigmatm tautm Eqtm) s1)
    | lam (_) s0 => congr_lam ((ext_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (upExt_tm_tm (_) (_) Eqtm)) s0)
    end.

Definition up_ren_ren_tm_tm { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_tm_tm tau) (upRen_tm_tm xi)) x = (upRen_tm_tm theta) x :=
  up_ren_ren xi tau theta Eq.

Definition up_ren_ren_list_tm_tm { p : nat } { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRenList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upRenList_tm_tm p theta) x :=
  up_ren_ren_p Eq.

Fixpoint compRenRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (rhotm : (fin) (mtm) -> (fin) (ltm)) (Eqtm : forall x, ((funcomp) zetatm xitm) x = rhotm x) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm rhotm s :=
    match s with
    | var_tm (_) s => (ap) (var_tm (ltm)) (Eqtm s)
    | app (_) s0 s1 => congr_app ((compRenRen_tm xitm zetatm rhotm Eqtm) s0) ((compRenRen_tm xitm zetatm rhotm Eqtm) s1)
    | lam (_) s0 => congr_lam ((compRenRen_tm (upRen_tm_tm xitm) (upRen_tm_tm zetatm) (upRen_tm_tm rhotm) (up_ren_ren (_) (_) (_) Eqtm)) s0)
    end.

Definition up_ren_subst_tm_tm { k : nat } { l : nat } { mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_tm_tm tau) (upRen_tm_tm xi)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition up_ren_subst_list_tm_tm { p : nat } { k : nat } { l : nat } { mtm : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upList_tm_tm p tau) (upRenList_tm_tm p xi)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun z => scons_p_head' (_) (_) z) (fun z => (eq_trans) (scons_p_tail' (_) (_) (xi z)) ((ap) (ren_tm (shift_p p)) (Eq z)))).

Fixpoint compRenSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) tautm xitm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compRenSubst_tm xitm tautm thetatm Eqtm) s0) ((compRenSubst_tm xitm tautm thetatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((compRenSubst_tm (upRen_tm_tm xitm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_ren_subst_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition up_subst_ren_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRen_tm_tm zetatm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_tm (shift) (upRen_tm_tm zetatm) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift) ((funcomp) (shift) zetatm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_ren_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (zetatm : (fin) (ltm) -> (fin) (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (ren_tm zetatm) sigma) x = theta x) : forall x, ((funcomp) (ren_tm (upRenList_tm_tm p zetatm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (_) n) (scons_p_congr (fun x => (ap) (var_tm (p+ mtm)) (scons_p_head' (_) (_) x)) (fun n => (eq_trans) (compRenRen_tm (shift_p p) (upRenList_tm_tm p zetatm) ((funcomp) (shift_p p) zetatm) (fun x => scons_p_tail' (_) (_) x) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_tm zetatm (shift_p p) ((funcomp) (shift_p p) zetatm) (fun x => eq_refl) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (ren_tm zetatm) sigmatm) x = thetatm x) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s0) ((compSubstRen_tm sigmatm zetatm thetatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((compSubstRen_tm (up_tm_tm sigmatm) (upRen_tm_tm zetatm) (up_tm_tm thetatm) (up_subst_ren_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition up_subst_subst_tm_tm { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (tautm : (fin) (ltm) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (up_tm_tm tautm)) (up_tm_tm sigma)) x = (up_tm_tm theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_tm (shift) (up_tm_tm tautm) ((funcomp) (up_tm_tm tautm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift) ((funcomp) (ren_tm (shift)) tautm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_tm (shift)) (Eq fin_n)))
  | None => eq_refl
  end.

Definition up_subst_subst_list_tm_tm { p : nat } { k : nat } { ltm : nat } { mtm : nat } (sigma : (fin) (k) -> tm (ltm)) (tautm : (fin) (ltm) -> tm (mtm)) (theta : (fin) (k) -> tm (mtm)) (Eq : forall x, ((funcomp) (subst_tm tautm) sigma) x = theta x) : forall x, ((funcomp) (subst_tm (upList_tm_tm p tautm)) (upList_tm_tm p sigma)) x = (upList_tm_tm p theta) x :=
  fun n => (eq_trans) (scons_p_comp' ((funcomp) (var_tm (p+ ltm)) (zero_p p)) (_) (_) n) (scons_p_congr (fun x => scons_p_head' (_) (fun z => ren_tm (shift_p p) (_)) x) (fun n => (eq_trans) (compRenSubst_tm (shift_p p) (upList_tm_tm p tautm) ((funcomp) (upList_tm_tm p tautm) (shift_p p)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_tm tautm (shift_p p) (_) (fun x => (eq_sym) (scons_p_tail' (_) (_) x)) (sigma n))) ((ap) (ren_tm (shift_p p)) (Eq n))))).

Fixpoint compSubstSubst_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (thetatm : (fin) (mtm) -> tm (ltm)) (Eqtm : forall x, ((funcomp) (subst_tm tautm) sigmatm) x = thetatm x) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm thetatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s0) ((compSubstSubst_tm sigmatm tautm thetatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((compSubstSubst_tm (up_tm_tm sigmatm) (up_tm_tm tautm) (up_tm_tm thetatm) (up_subst_subst_tm_tm (_) (_) (_) Eqtm)) s0)
    end.

Definition rinstInst_up_tm_tm { m : nat } { ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm)) (Eq : forall x, ((funcomp) (var_tm (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm ((S) ntm)) (upRen_tm_tm xi)) x = (up_tm_tm sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_tm (shift)) (Eq fin_n)
  | None => eq_refl
  end.

Definition rinstInst_up_list_tm_tm { p : nat } { m : nat } { ntm : nat } (xi : (fin) (m) -> (fin) (ntm)) (sigma : (fin) (m) -> tm (ntm)) (Eq : forall x, ((funcomp) (var_tm (ntm)) xi) x = sigma x) : forall x, ((funcomp) (var_tm (p+ ntm)) (upRenList_tm_tm p xi)) x = (upList_tm_tm p sigma) x :=
  fun n => (eq_trans) (scons_p_comp' (_) (_) (var_tm (p+ ntm)) n) (scons_p_congr (fun z => eq_refl) (fun n => (ap) (ren_tm (shift_p p)) (Eq n))).

Fixpoint rinst_inst_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) (sigmatm : (fin) (mtm) -> tm (ntm)) (Eqtm : forall x, ((funcomp) (var_tm (ntm)) xitm) x = sigmatm x) (s : tm (mtm)) : ren_tm xitm s = subst_tm sigmatm s :=
    match s with
    | var_tm (_) s => Eqtm s
    | app (_) s0 s1 => congr_app ((rinst_inst_tm xitm sigmatm Eqtm) s0) ((rinst_inst_tm xitm sigmatm Eqtm) s1)
    | lam (_) s0 => congr_lam ((rinst_inst_tm (upRen_tm_tm xitm) (up_tm_tm sigmatm) (rinstInst_up_tm_tm (_) (_) Eqtm)) s0)
    end.

Lemma rinstInst_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) : ren_tm xitm = subst_tm ((funcomp) (var_tm (ntm)) xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tm xitm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_tm { mtm : nat } : subst_tm (var_tm (mtm)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tm (var_tm (mtm)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_tm { mtm : nat } : @ren_tm (mtm) (mtm) (id) = id .
Proof. exact ((eq_trans) (rinstInst_tm ((id) (_))) instId_tm). Qed.

Lemma varL_tm { mtm : nat } { ntm : nat } (sigmatm : (fin) (mtm) -> tm (ntm)) : (funcomp) (subst_tm sigmatm) (var_tm (mtm)) = sigmatm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_tm { mtm : nat } { ntm : nat } (xitm : (fin) (mtm) -> (fin) (ntm)) : (funcomp) (ren_tm xitm) (var_tm (mtm)) = (funcomp) (var_tm (ntm)) xitm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (subst_tm sigmatm s) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) s .
Proof. exact (compSubstSubst_tm sigmatm tautm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) : (funcomp) (subst_tm tautm) (subst_tm sigmatm) = subst_tm ((funcomp) (subst_tm tautm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tm sigmatm tautm n)). Qed.

Lemma compRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mtm)) : ren_tm zetatm (subst_tm sigmatm s) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) s .
Proof. exact (compSubstRen_tm sigmatm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (sigmatm : (fin) (mtm) -> tm (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetatm) (subst_tm sigmatm) = subst_tm ((funcomp) (ren_tm zetatm) sigmatm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tm sigmatm zetatm n)). Qed.

Lemma renComp_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) (s : tm (mtm)) : subst_tm tautm (ren_tm xitm s) = subst_tm ((funcomp) tautm xitm) s .
Proof. exact (compRenSubst_tm xitm tautm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (tautm : (fin) (ktm) -> tm (ltm)) : (funcomp) (subst_tm tautm) (ren_tm xitm) = subst_tm ((funcomp) tautm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tm xitm tautm n)). Qed.

Lemma renRen_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) (s : tm (mtm)) : ren_tm zetatm (ren_tm xitm s) = ren_tm ((funcomp) zetatm xitm) s .
Proof. exact (compRenRen_tm xitm zetatm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_tm { ktm : nat } { ltm : nat } { mtm : nat } (xitm : (fin) (mtm) -> (fin) (ktm)) (zetatm : (fin) (ktm) -> (fin) (ltm)) : (funcomp) (ren_tm zetatm) (ren_tm xitm) = ren_tm ((funcomp) zetatm xitm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tm xitm zetatm n)). Qed.

End tm.

Arguments var_tm {ntm}.

Arguments app {ntm}.

Arguments lam {ntm}.

Global Instance Subst_tm { mtm : nat } { ntm : nat } : Subst1 ((fin) (mtm) -> tm (ntm)) (tm (mtm)) (tm (ntm)) := @subst_tm (mtm) (ntm) .

Global Instance Ren_tm { mtm : nat } { ntm : nat } : Ren1 ((fin) (mtm) -> (fin) (ntm)) (tm (mtm)) (tm (ntm)) := @ren_tm (mtm) (ntm) .

Global Instance VarInstance_tm { mtm : nat } : Var ((fin) (mtm)) (tm (mtm)) := @var_tm (mtm) .

Notation "x '__tm'" := (var_tm x) (at level 5, format "x __tm") : subst_scope.

Notation "x '__tm'" := (@ids (_) (_) VarInstance_tm x) (at level 5, only printing, format "x __tm") : subst_scope.

Notation "'var'" := (var_tm) (only printing, at level 1) : subst_scope.

Class Up_tm X Y := up_tm : X -> Y.

Notation "↑__tm" := (up_tm) (only printing) : subst_scope.

Notation "↑__tm" := (up_tm_tm) (only printing) : subst_scope.

Global Instance Up_tm_tm { m : nat } { ntm : nat } : Up_tm (_) (_) := @up_tm_tm (m) (ntm) .

Notation "s [ sigmatm ]" := (subst_tm sigmatm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatm ]" := (subst_tm sigmatm) (at level 0, left associativity, only printing) : fscope.

Notation "s ⟨ xitm ⟩" := (ren_tm xitm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitm ⟩" := (ren_tm xitm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_tm,  Ren_tm,  VarInstance_tm in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_tm| progress rewrite ?compComp_tm| progress rewrite ?compComp'_tm| progress rewrite ?rinstId_tm| progress rewrite ?compRen_tm| progress rewrite ?compRen'_tm| progress rewrite ?renComp_tm| progress rewrite ?renComp'_tm| progress rewrite ?renRen_tm| progress rewrite ?renRen'_tm| progress rewrite ?varL_tm| progress rewrite ?varLRen_tm| progress (unfold up_ren, upRen_tm_tm, upRenList_tm_tm, up_tm_tm, upList_tm_tm)| progress (cbn [subst_tm ren_tm])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_tm in *| progress rewrite ?compComp_tm in *| progress rewrite ?compComp'_tm in *| progress rewrite ?rinstId_tm in *| progress rewrite ?compRen_tm in *| progress rewrite ?compRen'_tm in *| progress rewrite ?renComp_tm in *| progress rewrite ?renComp'_tm in *| progress rewrite ?renRen_tm in *| progress rewrite ?renRen'_tm in *| progress rewrite ?varL_tm in *| progress rewrite ?varLRen_tm in *| progress (unfold up_ren, upRen_tm_tm, upRenList_tm_tm, up_tm_tm, upList_tm_tm in *)| progress (cbn [subst_tm ren_tm] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_tm).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_tm).
