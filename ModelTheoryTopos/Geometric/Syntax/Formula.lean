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
  | infdisj {Γ} {I : Set κ} : (I → Formula Γ) → Formula Γ
  | eq {Γ A} : Γ ⊢ᵗ A → Γ ⊢ᵗ A → Formula Γ
  | existsQ {A Γ} : Formula (A ∶ Γ) → Formula Γ

scoped notation:min "⊤'" => Formula.true
scoped notation:min "⊥'" => Formula.false
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
  | ⊤' => ⊤'
  | ⊥' => ⊥'
  | P ∧' Q => (P.subst σ) ∧' (Q.subst σ)
  | ⋁' fP => ⋁' (fun i ↦ (fP i).subst σ)
  | t1 =' t2 => (t1.subst σ) =' (t2.subst σ)
  | existsQ (A := A) P => ∃' (P.subst (Context.Hom.cons (Δ.π A ≫ σ) (Context.var Δ A)))

@[ext]
structure FormulaContext (Γ : S.Context) : Type* where
  length : ℕ
  ctx : Fin length → S.Formula Γ

def FormulaContext.nil (Γ : S.Context) : FormulaContext Γ where
  length := 0
  ctx := ![]

variable {Δ Γ : S.Context} (Θ : S.FormulaContext Γ)

@[simp]
lemma FormulaContext.length_0_isNil (φ : Fin 0 → S.Formula Γ) :
    FormulaContext.mk 0 φ = FormulaContext.nil Γ := by
  ext <;> simp [nil]; ext i; exact Fin.elim0 i

def FormulaContext.cons (P : S.Formula Γ) : FormulaContext Γ where
  length := Θ.length + 1
  ctx := Matrix.vecCons P Θ.ctx

@[simp]
lemma FormulaContext.lenght_cons (P : S.Formula Γ) : (Θ.cons P).length = Θ.length + 1 := by
  simp [cons]

def FormulaContext.snoc (P : S.Formula Γ) : FormulaContext Γ where
  length := Θ.length + 1
  ctx := Matrix.vecSnoc P Θ.ctx

def FormulaContext.subst (σ : Δ ⟶ Γ) (Θ : S.FormulaContext Γ) : S.FormulaContext Δ where
  length := Θ.length
  ctx i := (Θ.ctx i).subst σ

instance instHAppendFormulaContext :
    HAppend (FormulaContext Γ) (FormulaContext Γ) (FormulaContext (κ := κ) Γ) where
  hAppend Θ Θ' := {
    length := Θ.length + Θ'.length
    ctx := Matrix.vecAppend (by simp) Θ.ctx Θ'.ctx
  }

instance instMembershipFormulaContext : Membership (Formula Γ) (FormulaContext (κ := κ) Γ) where
  mem Θ P := ∃ i, Θ.ctx i = P

@[simp]
lemma FormulaContext.append_nil : Θ ++ FormulaContext.nil Γ = Θ := by
  ext <;> simp [nil, HAppend.hAppend]

@[simp]
lemma FormulaContext.snoc_append {n : ℕ} (φᵢ : Fin (n + 1) → Formula Γ) :
    (Θ ++ { length := n, ctx := Matrix.vecInit φᵢ}).snoc (Matrix.vecLast φᵢ) =
    Θ ++ { length := n + 1, ctx := φᵢ } := by
  ext
  · simp [HAppend.hAppend, FormulaContext.snoc]; omega
  · simp [HAppend.hAppend, FormulaContext.snoc]
    rw [← Matrix.vecLast_Append (n := Θ.length) (m := n) Θ.ctx φᵢ,
      ← Matrix.vecAppend_init, Matrix.snoc_last_init]

variable (S) in
structure Sequent : Type* where
  ctx : S.Context
  premise : Formula ctx
  concl : Formula ctx

variable (S) in
class Theory where
  axioms : Set S.Sequent

attribute [coe] Theory.axioms

instance : Coe (Theory (κ := κ)) (Set S.Sequent) where
  coe T := T.axioms

instance instMembershipTheory :
  Membership (S.Sequent) (S.Theory (κ := κ)) := {
  mem T P := P ∈ T.axioms
}
