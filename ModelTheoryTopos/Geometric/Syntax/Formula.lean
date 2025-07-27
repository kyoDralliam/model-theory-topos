import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Basic
import ModelTheoryTopos.Geometric.Syntax.Term

namespace Signature

open Cardinal CategoryTheory

variable {S : Signature}

class SmallUniverse (S : Signature) where
  type : Type*

attribute [coe] SmallUniverse.type

instance : CoeSort (SmallUniverse S) Type* where
  coe κ := κ.type

variable [κ : SmallUniverse S]

inductive Formula : S.Context → Type* where
  | rel {Γ} (o : S.Relations) :
      ((i : Fin o.arity) → S.Term Γ (o.sortedArity i)) → Formula Γ
  | true {Γ} : Formula Γ
  | false {Γ} : Formula Γ
  | conj {Γ} : Formula Γ → Formula Γ → Formula Γ
  | infdisj {Γ} : (κ → Formula Γ) → Formula Γ
  | eq {Γ A} : S.Term Γ A → S.Term Γ A → Formula Γ
  | existsQ {A Γ} : Formula (A ∶ Γ) → Formula Γ

scoped notation:min "⊤'" => Formula.true
scoped notation:min "⊤'" => Formula.false
scoped infixr:62 " ∧' " => Formula.conj
scoped prefix:100 "⋁'" => Formula.infdisj
scoped infixr:50 " =' " => Formula.eq
scoped prefix:110 "∃'" => Formula.existsQ

scoped syntax:25 term:51 " ⊢ᶠ𝐏" : term

scoped macro_rules
  | `($Γ ⊢ᶠ𝐏) => `(Formula $Γ)

def Formula.subst {Γ Δ : S.Context} (σ : Δ ⟶ Γ) (P : Γ ⊢ᶠ𝐏) : Δ ⊢ᶠ𝐏 :=
  match P with
  | rel P ft => .rel P (fun i ↦ (ft i).subst σ)
  | true => true
  | false => false
  | conj P Q => conj (P.subst σ) (Q.subst σ)
  | infdisj fP => infdisj (fun i ↦ (fP i).subst σ)
  | eq t1 t2 => eq (t1.subst σ) (t2.subst σ)
  | existsQ (A := A) P =>
      existsQ (P.subst (Context.Hom.cons (Δ.π A ≫ σ) (Context.var Δ A)))

variable (S) in
structure Sequent : Type* where
  ctx : S.Context
  premise : Formula ctx := .true
  concl : Formula ctx

variable (S) in
class Theory where
  axioms : Set S.Sequent

attribute [coe] Theory.axioms

instance : Coe (Theory (κ := κ)) (Set S.Sequent) where
  coe T := T.axioms

@[ext]
structure FormulaContext (Γ : S.Context) : Type* where
  length : ℕ
  ctx : Fin length → S.Formula Γ

def FormulaContext.cons {Γ} (Θ : S.FormulaContext Γ) (P : S.Formula Γ) :
    FormulaContext Γ where
  length := Θ.length + 1
  ctx := Matrix.vecCons P Θ.ctx

def FormulaContext.subst {Δ Γ : S.Context} (σ : Δ ⟶ Γ) :
    S.FormulaContext Γ → S.FormulaContext Δ := fun Θ ↦ {
  length := Θ.length
  ctx i := (Θ.ctx i).subst σ }

instance instHAppendFormulaContext {Γ} :
  HAppend (FormulaContext Γ) (FormulaContext Γ) (FormulaContext (κ := κ) Γ) := {
  hAppend Θ Θ' := {
    length := Θ.length + Θ'.length
    ctx := Matrix.vecAppend (by simp) Θ.ctx Θ'.ctx
  }
}

instance instMembershipFormulaContext {Γ} :
  Membership (Formula Γ) (FormulaContext (κ := κ) Γ) := {
  mem Θ P := ∃ i, Θ.ctx i = P
}

instance instMembershipTheory :
  Membership (S.Sequent) (S.Theory (κ := κ)) := {
  mem T P := P ∈ T.axioms
}
