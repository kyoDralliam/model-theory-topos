import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import ModelTheoryTopos.Geometric.Syntax.Signature
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import ModelTheoryTopos.ForMathlib.Data.Fin.VecNotation

open CategoryTheory Limits

namespace Signature

variable {S : Signature}

variable (S) in
@[ext]
structure Context : Type* where
  length : ℕ
  nth : Fin length → S

@[reducible]
def Context.cons (A : S) (xs : S.Context) : S.Context where
  length := xs.length + 1
  nth := Matrix.vecCons A xs.nth

@[reducible]
def Context.signature : S.Context → Signature := fun _ => S

-- Note that this is `\:`
scoped[Signature] infixr:67 " ∶ " => Signature.Context.cons

inductive Term (xs : S.Context) : S → Type* where
  | var {A} : {i : Fin xs.length // xs.nth i = A} → Term xs A
  | func (f : S.Functions) : Term xs f.domain → Term xs f.codomain
  | pair {n} {Aᵢ : Fin n → S} :
      ((i : Fin n) → Term xs (Aᵢ i)) → Term xs (.prod Aᵢ)
  | proj {n} {Aᵢ : Fin n → S} : Term xs (.prod Aᵢ) → (i : Fin n) → Term xs (Aᵢ i)

scoped notation:25 "⊢ᵗ[" xs:51 "] " t:50  => Term xs t

def Context.nthTerm (xs : S.Context) (i : Fin xs.length) : ⊢ᵗ[xs] xs.nth i :=
  Term.var ⟨i , rfl⟩

def Context.Hom (ys xs : S.Context) : Type* := (i : Fin xs.length) → ⊢ᵗ[ys] xs.nth i

def Context.id (xs : S.Context) : Context.Hom xs xs := xs.nthTerm

@[reducible]
def Term.subst {ys xs : S.Context} (σ : Context.Hom ys xs) {A : S} :
   ⊢ᵗ[xs] A → ⊢ᵗ[ys] A
  | var v => v.prop ▸ σ v.val
  | func f t  => .func f (t.subst σ)
  | pair tᵢ => pair (fun i ↦ (tᵢ i).subst σ)
  | proj (Aᵢ := Aᵢ) t i => proj (t.subst σ) i

def Term.subst_subst (σ : Context.Hom zs ys) (σ' : Context.Hom ys xs) (t : ⊢ᵗ[xs] A) :
    t.subst (fun i ↦ Term.subst σ (σ' i)) = (t.subst σ').subst σ := by
  induction t with
  | var i => simp only [subst]; aesop
  | func f _ _ => simp only [subst, func.injEq]; aesop
  | pair _ _ => simp only [subst, pair.injEq]; aesop
  | proj _ i _ => simp only [subst, proj.injEq]; aesop

@[simp]
def Context.comp {Θ ys xs : S.Context} (f : Context.Hom Θ ys) (g : Context.Hom ys xs) :
  Context.Hom Θ xs := fun i ↦ (g i).subst f

@[simp]
lemma Term.subst_id {xs : S.Context} {A : S} (t : ⊢ᵗ[xs] A) : t.subst xs.id = t :=
  match t with
  | var v => by aesop
  | func f h => by simp only [subst, func.injEq]; simp [Term.subst_id]
  | pair tᵢ => by simp [subst]; funext i; simp [Term.subst_id]
  | proj (Aᵢ := Aᵢ) t i => by simp [subst, Term.subst_id]

lemma Context.assoc {zs ys xs ws : S.Context}
    (σ : Context.Hom zs ys) (σ' : Context.Hom ys xs) (σ'' : Context.Hom xs ws) :
    Context.comp (Context.comp σ σ') σ'' = Context.comp σ (Context.comp σ' σ'') :=
  funext fun i ↦ by unfold Context.comp; apply Term.subst_subst

instance : Category S.Context where
  Hom := Context.Hom
  id := Context.id
  comp := Context.comp
  id_comp σ := by funext; simp
  assoc := Context.assoc

def Context.π (xs : S.Context) (A : S) :
    Context.Hom (A ∶ xs) xs := fun i ↦ Term.var ⟨i.succ, rfl⟩

def Context.var (xs : S.Context) (A : S) : ⊢ᵗ[A∶xs] A :=
  Term.var ⟨0 , rfl⟩

@[simp]
lemma Context.cons_succ (xs : S.Context) (A : S) (i : Fin xs.length) :
  (A ∶ xs).nth i.succ = xs.nth i := by simp

def Context.Hom.cons {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} (t : S.Term ys A) :
    ys ⟶ (A ∶ xs) :=
  Fin.cons t (fun i ↦ Context.cons_succ xs A i ▸ σ i)

def Context.Hom.cons_Id {xs : S.Context} {A : S} (t : S.Term xs A) :
  Context.Hom xs (A ∶ xs) := (Context.id xs).cons t

end Signature
