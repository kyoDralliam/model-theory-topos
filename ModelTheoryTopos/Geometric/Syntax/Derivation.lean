import ModelTheoryTopos.Geometric.Syntax.Formula

open CategoryTheory Limits

inductive Foo : (n : Nat) → Type where
  | foo (x : Nat × Nat) : Foo x.fst → Foo x.snd


def test {n} (x : Foo n) : Type :=
  match n, x with
  | _, .foo x f => sorry -- x.snd is not available

namespace Signature

variable {S : Signature} [κ : SmallUniverse S] [T : S.Theory]

inductive Derivation : {xs : S.Context} → FormulaContext xs → Formula xs → Type* where
  | axiom {xs} {Γ : FormulaContext xs} {φ : S.Sequent} {σ : xs ⟶ φ.ctx}
      (φinT : φ ∈ T) (D : Derivation Γ (φ.premise.subst σ)) : Derivation Γ (φ.concl.subst σ)
  | var {xs} (Γ : S.FormulaContext xs) (i : Fin Γ.length) : Derivation Γ (Γ.nth i)
  | true_intro {xs} {Γ : FormulaContext xs} : Derivation Γ ⊤'
  | false_elim {xs} {Γ : FormulaContext xs} {φ : Formula xs} (D_false : Derivation Γ ⊥') :
      Derivation Γ φ
  | conj_intro {Γ φ ψ} (D_left : Derivation Γ φ) (D_right : Derivation Γ ψ) : Derivation Γ (φ ∧' ψ)
  | conj_elim_l {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ φ
  | conj_elim_r {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ ψ
  | disj_intro {xs Γ} {I : Set κ} (φᵢ : I → S.Formula xs) (i : I) (D : Derivation Γ (φᵢ i)) :
      Derivation Γ (⋁' φᵢ)
  | disj_elim {xs Γ ψ} {I : Set κ} {φᵢ : I → S.Formula xs} (D_disj : Derivation Γ (⋁' φᵢ))
    (Dᵢ : (i : I) → Derivation (Γ.cons (φᵢ i)) ψ) : Derivation Γ ψ
  | eq_intro {Γ t} : Derivation Γ (.eq t t)
  | eq_elim {xs A t1 t2} {Γ Γ' : S.FormulaContext xs} (φ : S.Formula (A ∶ xs))
    (D_eq : Derivation Γ (t1 =' t2)) (D : Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.cons_Id t1))) :
    Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.cons_Id t2))
  | eq_proj_pair {xs n} {Aᵢ : (i : Fin n) → S} (tᵢ : (i : Fin n) → ⊢ᵗ[xs] (Aᵢ i)) {i : Fin n} {Γ} :
      Derivation Γ ((Term.pair tᵢ).proj i =' tᵢ i)
  | eq_pair_proj {xs n} {Aᵢ : Fin n → DerivedSorts S.Sorts} (t : ⊢ᵗ[xs] .prod Aᵢ) {Γ} :
      Derivation Γ (Term.pair (fun i ↦ t.proj i) =' t)
  | exists_intro {xs A} {Γ : S.FormulaContext xs} (φ : S.Formula (A ∶ xs)) (t : S.Term xs A)
      (D : Derivation Γ (φ.subst (Context.Hom.cons_Id t))) : Derivation Γ (∃' φ)
  | exists_elim {xs A} {Γ : S.FormulaContext xs} {φ : S.Formula (A ∶ xs)}
      (D_exists : Derivation Γ (∃' φ)) {ψ}
      (D : Derivation ((Γ.subst (xs.π A)).cons φ) (ψ.subst (xs.π A))) :
      Derivation Γ ψ

scoped notation:25 Γ " ⊢ᵈ[ " xs:51 " ] " φ:50  => Derivation (xs := xs) Γ φ
scoped notation:25 Γ " ⊢ᵈ " φ:50  => Derivation Γ φ

variable {xs : S.Context} {Δ Γ : FormulaContext xs} {φ : Formula xs}

variable (Δ Γ) in
def FormulaContext.Hom : Type _ :=
  (i : Fin Γ.length) → Δ ⊢ᵈ Γ.nth i

instance : Quiver (FormulaContext xs) where
  Hom := FormulaContext.Hom

def FormulaContext.Hom.Id (Γ : FormulaContext xs) : Γ ⟶ Γ := .var Γ

def FormulaContext.Hom.cons (ξ : Δ ⟶ Γ) (D : Δ ⊢ᵈ φ) : Δ ⟶ (Γ.cons φ) :=
  Fin.cases D ξ

variable (Δ φ) in
def FormulaContext.Hom.π : (Δ.cons φ) ⟶ Δ :=
  fun i ↦ .var (Δ.cons φ) i.succ

noncomputable def Derivation.wkTm {xs} {Γ : FormulaContext xs} {φ : Formula xs}
    (D : Γ ⊢ᵈ φ) {ys} (ρ : ys ⟶ xs) : Derivation (T := T) (Γ.subst ρ) (φ.subst ρ) :=
  sorry

def Derivation.wkFml {xs} {Γ : FormulaContext xs} {φ : Formula xs}
    (D : Γ ⊢ᵈ φ) : (Δ : FormulaContext xs) → (ξ : Γ ⊆' Δ) → Derivation (T := T) Δ φ :=
  match D with
  | @«axiom» _ _ _ xs Γ ψ σ φinT D => fun _ ξ ↦
      .axiom (T := T) φinT (.wkFml D _ ξ)
  | @var _ _ _ xs Γ i => fun Δ ξ ↦
      let ⟨j, q⟩ := ξ (Γ.nth i) ⟨i, rfl⟩
      q ▸ .var Δ j
  | @true_intro _ _ _ xs Γ => fun _ _ ↦ .true_intro
  | @false_elim _ _ _ xs Γ φ D_false => fun _ ξ ↦ false_elim (.wkFml D_false _ ξ)
  | @conj_intro _ _ _ xs Γ φ ψ D_left D_right => fun _ ξ ↦
      conj_intro (.wkFml D_left _ ξ) (.wkFml D_right _ ξ)
  | @conj_elim_l _ _ _  xs Γ φ ψ D_conj => fun _ ξ ↦ conj_elim_l (.wkFml D_conj _ ξ)
  | @conj_elim_r _ _ _ xs Γ φ ψ D_conj => fun _ ξ ↦ conj_elim_r (.wkFml D_conj _ ξ)
  | @disj_intro _ _ _ xs Γ I φᵢ i D => fun _ ξ ↦ disj_intro φᵢ i (.wkFml D _ ξ)
  | @disj_elim _ _ _ xs Γ ψ _ φᵢ D_disj Dᵢ  => fun Δ ξ ↦
      disj_elim (wkFml D_disj _ ξ) fun i ↦
        (wkFml (Dᵢ i) (Δ.cons (φᵢ i)) (FormulaContext.incl_cons_cons (φᵢ i) ξ))
  | @eq_intro _ _ _ xs A Γ t => fun _ _ ↦ eq_intro
  | @eq_elim _ _ _ xs A _ t2 Γ Γ' φ D_eq D  => fun Δ ξ ↦
    FormulaContext.nil_append (κ := κ) Δ ▸
      eq_elim φ (Γ' := .nil _) (.wkFml D_eq _ (FormulaContext.append_incl_l ξ))
        (.wkFml D _ (FormulaContext.nil_append (κ := κ) _ ▸ ξ))
  | @eq_proj_pair _ _ _ xs n Aᵢ tᵢ i Γ => fun _ _ ↦ eq_proj_pair tᵢ
  | @eq_pair_proj _ _ _ xs n Aᵢ t Γ => fun _ _ ↦ eq_pair_proj t
  | @exists_intro _ _ _ xs A Γ φ t D => fun _ ξ ↦ exists_intro φ t (.wkFml D _ ξ)
  | @exists_elim _ _ _ xs _ Γ φ D_exists ψ D => fun _ ξ ↦
    exists_elim (.wkFml D_exists _ ξ)
      (.wkFml D _ (FormulaContext.incl_cons_cons φ (FormulaContext.incl_subst ξ _)))

noncomputable def Derivation.subst' {xs} {Γ : FormulaContext xs} {φ : Formula xs} (D : Γ ⊢ᵈ φ) :
    (ys : S.Context) → (σ : ys ⟶ xs) → (Δ : FormulaContext ys) → (ξ : Δ ⟶ (Γ.subst σ)) →
    Derivation (T := T) Δ (φ.subst σ) :=
  match Γ, φ, D with
  | .(Γ), .(Formula.subst σ (Sequent.concl ψ)), @«axiom» _ _ _ .(xs) Γ ψ σ φinT D => fun ys σ' Δ ξ ↦
      (Formula.subst_comp ψ.concl σ' σ) ▸ Derivation.axiom φinT
        (Formula.subst_comp ψ.premise σ' σ ▸ Derivation.subst' D ys σ' Δ ξ)
  | .(Γ), .(Γ.nth i), @var _ _ _ .(xs) Γ i => fun ys σ Δ ξ ↦ ξ i
  | .(Γ), .(⊤'), @true_intro _ _ _ .(xs) Γ => fun ys σ Δ ξ ↦ .true_intro
  | .(Γ), .(φ), @false_elim _ _ _ .(xs) Γ φ D_false => fun ys σ Δ ξ ↦
      .false_elim (Derivation.subst' D_false _ _ _ ξ)
  | .(Γ), _, @conj_intro _ _ _ .(xs) Γ φ ψ D_left D_right => fun ys σ Δ ξ ↦
      conj_intro (Derivation.subst' D_left _ _ _ ξ) (Derivation.subst' D_right _ _ _ ξ)
  | .(Γ), _, @conj_elim_l _ _ _  .(xs) Γ φ ψ D_conj => fun ys σ Δ ξ ↦
      conj_elim_l (Derivation.subst' D_conj _ _ _ ξ)
  | .(Γ), _, @conj_elim_r _ _ _ .(xs) Γ φ ψ D_conj => fun ys σ Δ ξ ↦
      conj_elim_r (Derivation.subst' D_conj _ _ _ ξ)
  | .(Γ), _, @disj_intro _ _ _ .(xs) Γ I φᵢ i D => fun ys σ Δ ξ ↦
      disj_intro (fun i ↦ (φᵢ i).subst σ) i (Derivation.subst' D _ _ _ ξ)
  | .(Γ), .(ψ), @disj_elim _ _ _ .(xs) Γ ψ I φᵢ D_disj Dᵢ  => fun ys σ Δ ξ ↦
      by
      apply disj_elim (Derivation.subst' D_disj _ _ _ ξ) fun i ↦ ?_
      apply Derivation.subst' (Dᵢ i)
      intro j
      cases j using Fin.cases with
        | zero => exact Derivation.var _ 0
        | succ k =>
          have : ((Γ.cons (φᵢ i)).subst σ).nth k.succ = (Γ.subst σ).nth k := sorry
          rw [this]
          apply Derivation.wkFml (ξ k)
          exact Δ.incl_cons _
  | .(Γ), _, @eq_intro _ _ _ .(xs) A Γ t => fun ys σ Δ ξ ↦
      sorry
  | .(Γ' ++ Γ), _, @eq_elim _ _ _ .(xs) A t1 t2 Γ Γ' φ D_eq D  => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @eq_proj_pair _ _ _ .(xs) n Aᵢ tᵢ i Γ => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @eq_pair_proj _ _ _ .(xs) n Aᵢ t Γ => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @exists_intro _ _ _ .(xs) A Γ φ t D => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @exists_elim _ _ _ .(xs) A Γ φ D_exists ψ D => fun ys σ Δ ξ ↦
      by
      apply exists_elim (Derivation.subst' D_exists _ _ _ ξ)
      have : Formula.subst (ys.π A) (Formula.subst σ ψ) =
        Formula.subst ((Context.consFunctor A).map σ) (Formula.subst (xs.π A) ψ) := sorry
      rw [this]
      apply Derivation.subst' D
      rw [FormulaContext.subst_cons]
      apply FormulaContext.Hom.cons
      · rw [FormulaContext.subst_comp]
        have : ((Context.consFunctor A).map σ ≫ xs.π A) = ys.π A ≫ σ := sorry
        rw [this]
        intro i
        have : (Γ.subst (ys.π A ≫ σ)).nth i = Formula.subst (ys.π A) ((Γ.subst σ).nth i) := sorry
        rw [this]
        exact Derivation.subst' (ξ i) (A ∶ ys) (ys.π A) _
          (FormulaContext.Hom.π (Δ.subst (ys.π A)) (Formula.subst ((Context.consFunctor A).map σ) φ))
      · exact Derivation.var _ 0
  termination_by sizeOf Γ -- Placeholder to typecheck
  decreasing_by all_goals sorry

instance {xs} : Category (FormulaContext (κ := κ) xs) where
  id Γ i := .var Γ i
  comp ξ ξ' i := sorry
  id_comp σ := by funext; sorry
  assoc := sorry

end Signature
