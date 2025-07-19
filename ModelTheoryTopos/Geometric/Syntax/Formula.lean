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

open Cardinal

variable {S : Signature}

class SmallUniverse (S : Signature) where
  type : Type*

attribute [coe] SmallUniverse.type

instance : CoeSort (SmallUniverse S) Type* where
  coe κ := κ.type

variable [κ : SmallUniverse S]

inductive Formula : S.Context → Type _ where
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
