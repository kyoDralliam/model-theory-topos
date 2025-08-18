import ModelTheoryTopos.Geometric.Syntax.Formula

open CategoryTheory Limits

namespace Signature

variable {S : Signature} [κ : SmallUniverse S] [T : S.Theory]

inductive Derivation : {Γ : S.Context} → S.FormulaContext Γ → S.Formula Γ → Type* where
  | axiom {Γ} {Θ : S.FormulaContext Γ} {φ : S.Sequent} {σ : Context.Hom Γ φ.ctx} :
      φ ∈ T → Derivation Θ (φ.premise.subst σ) → Derivation Θ (φ.concl.subst σ)
  | var {Γ} (Θ : S.FormulaContext Γ) (i : Fin Θ.length) : Derivation Θ (Θ.ctx i)
  | true_intro {Θ} : Derivation Θ .true
  | false_elim {Θ φ} : Derivation Θ .false → Derivation Θ φ
  | conj_intro {Θ φ ψ} : Derivation Θ φ → Derivation Θ ψ → Derivation Θ (φ ∧' ψ)
  | conj_elim_l {Θ φ ψ} : Derivation Θ (φ ∧' ψ) → Derivation Θ φ
  | conj_elim_r {Θ φ ψ} : Derivation Θ (φ ∧' ψ) → Derivation Θ ψ
  | infdisj_intro {Γ Θ} {I : Set κ} (P : I → S.Formula Γ) (i : I) :
      Derivation Θ (P i) → Derivation Θ (⋁' P)
  | infdisj_elim {Γ Θ ξ} {I : Set κ} {P : I → S.Formula Γ} : Derivation Θ (⋁' P) →
    ((i : I) → Derivation (Θ.cons (P i)) ξ) → Derivation Θ ξ
  | eq_intro {Θ t} : Derivation Θ (.eq t t)
  | eq_elim {Γ A t1 t2} {Θ Θ' : S.FormulaContext Γ} (φ : S.Formula (A ∶ Γ)) :
    Derivation Θ (t1 =' t2) →
    Derivation (Θ' ++ Θ) (φ.subst (Context.Hom.cons_Id t1)) →
    Derivation (Θ' ++ Θ) (φ.subst (Context.Hom.cons_Id t2))
  | eq_proj_pair {Γ n} {Aᵢ : (i : Fin n) → S} (tᵢ : (i : Fin n) → Γ ⊢ᵗ (Aᵢ i)) {i : Fin n} {Θ} :
      Derivation Θ ((Term.pair tᵢ).proj i =' tᵢ i)
  | eq_pair_proj {Γ n} {Aᵢ : Fin n → DerivedSorts S.Sorts} (t : Γ ⊢ᵗ .prod Aᵢ) {Θ} :
      Derivation Θ (Term.pair (fun i ↦ t.proj i) =' t)
  | existsQ_intro {Γ A} {Θ : S.FormulaContext Γ} (φ : S.Formula (A ∶ Γ)) (t : S.Term Γ A):
    Derivation Θ (φ.subst (Context.Hom.cons_Id t)) → Derivation Θ (.existsQ φ)
  | existsQ_elim {Γ A} {Θ : S.FormulaContext Γ} (φ : S.Formula (A ∶ Γ)) :
      Derivation Θ (∃' φ) → Derivation (Θ.subst (Γ.π A)) φ

variable {Γ : S.Context} {Θ Θ' : FormulaContext Γ} {ψ : Formula Γ}

def Derivation.weaken (D : Derivation Θ ψ) : Derivation (Θ' ++ Θ) ψ := sorry

def Derivation.cut (D : Derivation Θ' ψ) (Dᵢ : (i : Fin Θ'.length) → Derivation Θ (Θ'.ctx i)) :
    Derivation Θ ψ :=
  sorry

end Signature
