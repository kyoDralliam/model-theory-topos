import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import ModelTheoryTopos.Geometric.Syntax.Signature

open CategoryTheory Limits

namespace Signature

variable {S : Signature}

variable (S) in
@[ext]
structure Context : Type* where
  length : ℕ
  ctx : Fin length → S.Sorts

abbrev Context.cons (A : S) (Γ : S.Context) : S.Context where
  length := Γ.length + 1
  ctx := Matrix.vecCons A Γ.ctx

abbrev Context.signature : S.Context → Signature := fun _ => S

-- Note that this is `\:`
scoped[Signature] infixr:67 " ∶ " => Signature.Context.cons

inductive Term : S.Context → S → Type* where
  -- x1, .. xn ⊢ xk
  | var {Γ A} : {i : Fin Γ.length // Γ.ctx i = A} → Term Γ A
  | func {Γ} (f : S.Functions) :
      ((i : Fin f.arity) → Term Γ (f.sortedArity i)) → Term Γ f.codomain

scoped syntax:25 term:51 " ⊢ᵗ " term:50 : term

scoped macro_rules
  | `($Γ ⊢ᵗ $A:term) => `(Term $Γ $A)

def Context.nth (Γ : S.Context) (i : Fin Γ.length) : Γ ⊢ᵗ Γ.ctx i :=
  Term.var ⟨i , rfl⟩

def Context.Hom (Δ Γ : S.Context) : Type* := (i : Fin Γ.length) → Δ ⊢ᵗ Γ.ctx i

def Context.id (Γ : S.Context) : Context.Hom Γ Γ := Γ.nth

def Term.subst {Δ Γ : S.Context} {A : S} (σ : Context.Hom Δ Γ) (t : Γ ⊢ᵗ A) :
    Δ ⊢ᵗ A :=
  match t with
  | var v => v.prop ▸ σ v.val
  | func f h => .func f fun i => Term.subst σ (h i)

@[simp]
def Context.comp {Θ Δ Γ : S.Context} (f : Context.Hom Θ Δ) (g : Context.Hom Δ Γ) :
  Context.Hom Θ Γ := fun i ↦ (g i).subst f

@[simp]
lemma Term.subst_id {Γ : S.Context} {A : S} (t : Γ ⊢ᵗ A) : t.subst Γ.id = t :=
  match t with
  | var v => by aesop
  | func f h => by simp only [subst, func.injEq]; funext i; simp [Term.subst_id]

lemma Context.assoc {Θ Δ Γ Υ : S.Context}
    (σ : Context.Hom Θ Δ) (σ' : Context.Hom Δ Γ) (σ'' : Context.Hom Γ Υ) :
    Context.comp (Context.comp σ σ') σ'' = Context.comp σ (Context.comp σ' σ'') :=
  funext fun i ↦ sorry

instance : Category S.Context where
  Hom := Context.Hom
  id := Context.id
  comp := Context.comp
  id_comp σ := by funext; simp
  assoc := Context.assoc

def Context.π (Γ : S.Context) (A : S) :
    Context.Hom (A ∶ Γ) Γ := fun i ↦ Term.var ⟨i.succ, rfl⟩

def Context.var (Γ : S.Context) (A : S) : A ∶ Γ ⊢ᵗ A :=
  Term.var ⟨0 , rfl⟩

@[simp]
lemma Context.cons_succ (Γ : S.Context) (A : S) (i : Fin Γ.length) :
  (A ∶ Γ).ctx i.succ = Γ.ctx i := by simp

def Context.Hom.cons {Δ Γ : S.Context} (σ : Δ ⟶ Γ) {A : S} (t : S.Term Δ A) :
    Context.Hom Δ (A ∶ Γ) :=
  Fin.cons t (fun i ↦ Context.cons_succ Γ A i ▸ σ i)

def Context.Hom.cons_Id {Γ : S.Context} {A : S} (t : S.Term Γ A) :
    Context.Hom Γ (A ∶ Γ) := (Context.id Γ).cons t

end Signature
