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
  | rel {xs} (o : S.Relations) : Term xs (o.domain) → Formula xs
  | true {xs} : Formula xs
  | false {xs} : Formula xs
  | conj {xs} : Formula xs → Formula xs → Formula xs
  | infdisj {xs} {I : Set κ} : (I → Formula xs) → Formula xs
  | eq {xs A} : ⊢ᵗ[xs] A → ⊢ᵗ[xs] A → Formula xs
  | existsQ {A xs} : Formula (A ∶ xs) → Formula xs

scoped notation:max "⊤'" => Formula.true
scoped notation:max "⊥'" => Formula.false
scoped infixr:62 " ∧' " => Formula.conj
scoped prefix:100 "⋁'" => Formula.infdisj
scoped infixr:50 " =' " => Formula.eq
scoped prefix:110 "∃'" => Formula.existsQ

scoped syntax:25 term:51 " ⊢ᶠ𝐏" : term

scoped macro_rules
  | `($xs ⊢ᶠ𝐏) => `(Formula $xs)

def Formula.subst {xs ys : S.Context} (σ : ys ⟶ xs) (φ : xs ⊢ᶠ𝐏) : ys ⊢ᶠ𝐏 :=
  match φ with
  | rel φ t => .rel φ (t.subst σ)
  | ⊤' => ⊤'
  | ⊥' => ⊥'
  | φ ∧' Q => (φ.subst σ) ∧' (Q.subst σ)
  | ⋁' φᵢ => ⋁' (fun i ↦ (φᵢ i).subst σ)
  | t1 =' t2 => (t1.subst σ) =' (t2.subst σ)
  | existsQ (A := A) φ => ∃' (φ.subst (Context.Hom.cons (ys.π A ≫ σ) (Context.var ys A)))

@[ext]
structure FormulaContext (xs : S.Context) : Type* where
  length : ℕ
  nth : Fin length → Formula xs

def FormulaContext.nil (xs : S.Context) : FormulaContext xs where
  length := 0
  nth := ![]

variable {ys xs : S.Context} (Γ : FormulaContext xs)

@[simp]
lemma FormulaContext.length_0_isNil (φ : Fin 0 → Formula xs) :
    FormulaContext.mk 0 φ = FormulaContext.nil xs := by
  ext <;> simp [nil]; ext i; exact Fin.elim0 i

@[reducible]
def FormulaContext.cons (φ : Formula xs) : FormulaContext xs where
  length := Γ.length + 1
  nth := Matrix.vecCons φ Γ.nth

@[simp]
lemma FormulaContext.cons_nth0 (Γ : FormulaContext xs) (φ) : (Γ.cons φ).nth 0 = φ := by simp

@[simp]
lemma FormulaContext.lenght_cons (φ : Formula xs) : (Γ.cons φ).length = Γ.length + 1 := by
  simp [cons]

def FormulaContext.snoc (φ : Formula xs) : FormulaContext xs where
  length := Γ.length + 1
  nth := Matrix.vecSnoc φ Γ.nth

def FormulaContext.subst (σ : ys ⟶ xs) (Γ : FormulaContext xs) : FormulaContext ys where
  length := Γ.length
  nth i := (Γ.nth i).subst σ

instance instHAppendFormulaContext :
    HAppend (FormulaContext xs) (FormulaContext xs) (FormulaContext (κ := κ) xs) where
  hAppend Γ Γ' := {
    length := Γ.length + Γ'.length
    nth := Matrix.vecAppend (by simp) Γ.nth Γ'.nth
  }

instance instMembershipFormulaContext : Membership (Formula xs) (FormulaContext (κ := κ) xs) where
  mem Γ φ := ∃ i, Γ.nth i = φ

@[simp]
lemma FormulaContext.append_nil : Γ ++ FormulaContext.nil xs = Γ := by
  ext <;> simp [nil, HAppend.hAppend]

@[simp]
lemma FormulaContext.nil_append : FormulaContext.nil xs ++ Γ = Γ := by
  ext
  · simp [nil, HAppend.hAppend]
  · simp [nil, HAppend.hAppend]
    nth_rw 2 [← Matrix.empty_vecAppend Γ.nth]
    grind

@[simp]
lemma FormulaContext.append_length {Γ'} : (Γ' ++ Γ).length = Γ'.length + Γ.length := by
  simp [HAppend.hAppend]

@[simp]
lemma FormulaContext.append_nth_l {Γ'} {i : Fin Γ'.length} :
    (Γ' ++ Γ).nth ⟨i, by simp; omega⟩ = Γ'.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.append_nth_r {Γ'} {i : Fin Γ.length} :
    (Γ' ++ Γ).nth ⟨Γ'.length + i, by simp⟩ = Γ.nth i := by
  simp [HAppend.hAppend, Matrix.vecAppend_eq_ite]

@[simp]
lemma FormulaContext.snoc_append {n : ℕ} (φᵢ : Fin (n + 1) → Formula xs) :
    (Γ ++ { length := n, nth := Matrix.vecInit φᵢ}).snoc (Matrix.vecLast φᵢ) =
    Γ ++ { length := n + 1, nth := φᵢ } := by
  ext
  · simp [HAppend.hAppend, FormulaContext.snoc]; omega
  · simp [HAppend.hAppend, FormulaContext.snoc]
    rw [← Matrix.vecLast_Append (n := Γ.length) (m := n) Γ.nth φᵢ,
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

instance instMembershipTheory : Membership (S.Sequent) (S.Theory (κ := κ)) := {
  mem T φ := φ ∈ T.axioms
}
