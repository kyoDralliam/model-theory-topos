import ModelTheoryTopos.Geometric.Syntax.Formula

open CategoryTheory Limits

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
      (D : Derivation Γ (φ.subst (Context.Hom.cons_Id t))) : Derivation Γ (.existsQ φ)
  | exists_elim {xs A} {Γ : S.FormulaContext xs} {φ : S.Formula (A ∶ xs)}
      (D_exists : Derivation Γ (∃' φ)) :
      Derivation (Γ.subst (xs.π A)) φ

scoped notation:25 Γ " ⊢ᵈ[ " xs:51 " ] " φ:50  => Derivation (xs := xs) Γ φ
scoped notation:25 Γ " ⊢ᵈ " φ:50  => Derivation Γ φ

variable {xs : S.Context} {Δ Γ : FormulaContext xs} {φ : Formula xs}

variable (Δ Γ) in
def FormulaContext.Hom : Type _ :=
  (i : Fin Γ.length) → Δ ⊢ᵈ Γ.nth i

def FormulaContext.Hom.cons (ξ : Δ.Hom Γ) (D : Δ ⊢ᵈ φ) : Δ.Hom (Γ.cons φ) :=
  Fin.cases D ξ

def FormulaContext.Hom.π : (Δ.cons φ).Hom Δ :=
  fun i ↦ .var (Δ.cons φ) i.succ

instance : Quiver (FormulaContext xs) where
  Hom := FormulaContext.Hom

/- I'm not sure why Lean is complaining -/
-- def Derivation.subst (D : Derivation Γ φ) : (Δ : FormulaContext xs) → Δ.Hom Γ → Derivation Δ φ := fun Δ ξ ↦
--   match xs, Γ, φ, D, Δ, ξ with
--   | .(xs), .(Γ), .(Formula.subst σ _), @«axiom» S κ T .(xs) .(Γ) φ σ φinT D, Δ, ξ => by
--       refine .axiom (T := T) φinT ?_
--       #check Derivation.subst D
--       -- (Derivation.subst _ _ ξ)


noncomputable def Derivation.subst'' {xs} {Γ : FormulaContext xs} {φ : Formula xs}
    (D : Γ ⊢ᵈ φ) {Δ : FormulaContext xs} (ξ : Δ.Hom Γ) : Derivation (T := T) Δ φ := by
  induction D with
  | «axiom» φinT D ih => exact .axiom (T := T) φinT (ih ξ)
  | var Γ i => exact ξ i
  | true_intro => exact .true_intro
  | false_elim D_false ih => exact false_elim (ih ξ)
  | conj_intro D_left D_right ih_left ih_right => exact conj_intro (ih_left ξ) (ih_right ξ)
  | conj_elim_l D_conj ih => exact conj_elim_l (ih ξ)
  | conj_elim_r D_conj ih => exact conj_elim_r (ih ξ)
  | disj_intro φᵢ i d ih => exact disj_intro φᵢ i (ih ξ)
  | disj_elim D_disj d'ᵢ ih ihᵢ =>
      refine disj_elim (ih ξ) fun i ↦ ihᵢ i ?_
      intro j
      cases j using Fin.cases with
      | zero => exact Derivation.var _ 0
      | succ i =>
          simp
          let almost_there := ξ i
          -- Needs weakening
          sorry
  | eq_intro => exact eq_intro
  | @eq_elim _ _ t1 t2 Γ Γ' φ D_eq d ih_eq ih =>
      let Δ_t1_eq_t2 := by
        refine ih_eq (Δ := Δ) fun i ↦ ?_
        let D' := ξ ⟨Γ'.length + i, by simp⟩
        simp at D'
        exact D'
      let goal : FormulaContext.nil _ ++ Δ ⊢ᵈ φ.subst (Context.Hom.cons_Id t2) :=
        eq_elim φ Δ_t1_eq_t2 (FormulaContext.nil_append (κ := κ) _ ▸ ih ξ)
      simp at goal
      exact goal
  | eq_proj_pair tᵢ => exact eq_proj_pair tᵢ
  | eq_pair_proj t => exact eq_pair_proj t
  | exists_intro φ t d ih => exact exists_intro φ t (ih ξ)
  | exists_elim D_exists ih =>
      let Γφ := Derivation.exists_elim D_exists
      -- Stucked, the induction hypothesis doesn't apply to the weakening of Γ
      sorry

instance {xs} : Category (FormulaContext (κ := κ) xs) where
  id Γ i := .var Γ i
  comp ξ ξ' i := sorry
  id_comp σ := by funext; sorry
  assoc := sorry

end Signature
