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

/-!
# Contexts and terms

In this file we define context and terms over a signatures, as well as provide basic API to use
them. Notably, we show that contexts form a category and that terms can be substituted along
morphisms of this category.

We remark that our terms are all well formed and intrinsically typed.
-/

open CategoryTheory Limits

namespace Signature

variable {S : Signature}

variable (S) in
/-- A context is a vector of sorts of a signature. -/
@[ext]
structure Context : Type* where
  length : ℕ
  nth : Fin length → S

/--
A term on a context `xs` is either (1) a variable appearing in that context, (2) a function
symbol applied to terms of its domain, (3) a tuple of terms or (4) a projection of a tuple.
-/
inductive Term (xs : S.Context) : S → Type* where
  | var (i : Fin xs.length) :  Term xs (xs.nth i)
  | func (f : S.Functions) : Term xs f.domain → Term xs f.codomain
  | pair {n} {Aᵢ : Fin n → S} :
      ((i : Fin n) → Term xs (Aᵢ i)) → Term xs (.prod Aᵢ)
  | proj {n} {Aᵢ : Fin n → S} : Term xs (.prod Aᵢ) → (i : Fin n) → Term xs (Aᵢ i)

scoped notation:25 "⊢ᵗ[" xs:51 "] " t:50  => Term xs t

/-- The nth variable in a context, as a term. -/
def Context.nthTerm (xs : S.Context) (i : Fin xs.length) : ⊢ᵗ[xs] xs.nth i :=
  Term.var i

/--
A morphism between two contexts `xs` and `ys` consist of giving a term in context `xs` for each sort
in the context `ys.
-/
def Context.Hom (xs ys : S.Context) : Type* := (i : Fin ys.length) → ⊢ᵗ[xs] ys.nth i

instance : Quiver S.Context where
  Hom := Context.Hom

/-- Substitution of a term along a contexts morphism. -/
@[reducible]
def Term.subst {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} :
   ⊢ᵗ[xs] A → ⊢ᵗ[ys] A
  | var i => σ i
  | func f t  => .func f (t.subst σ)
  | pair tᵢ => pair (fun i ↦ (tᵢ i).subst σ)
  | proj (Aᵢ := Aᵢ) t i => proj (t.subst σ) i

/-- The `CategoryStruct` structure on contexts. -/
instance : CategoryStruct S.Context where
  id xs := xs.nthTerm
  comp σ σ' i := (σ' i).subst σ

lemma Term.subst_comp (σ : zs ⟶ ys) (σ' : ys ⟶ xs) (t : ⊢ᵗ[xs] A) :
    t.subst (σ ≫ σ') = (t.subst σ').subst σ := by
  induction t with
  | var i => simp only [subst]; aesop
  | func f _ _ => simp only [subst, func.injEq]; aesop
  | pair _ _ => simp only [subst, pair.injEq]; aesop
  | proj _ i _ => simp only [subst, proj.injEq]; aesop

@[simp]
lemma Term.subst_id {xs : S.Context} {A : S} (t : ⊢ᵗ[xs] A) : t.subst (𝟙 xs) = t :=
  match t with
  | var v => by aesop
  | func f h => by simp only [subst, func.injEq]; simp [Term.subst_id]
  | pair tᵢ => by simp [subst]; funext i; simp [Term.subst_id]
  | proj (Aᵢ := Aᵢ) t i => by simp [subst, Term.subst_id]

instance : Category S.Context where
  id_comp σ := by funext; simp [CategoryStruct.comp]
  assoc σ σ' σ'' := funext fun i ↦ by unfold CategoryStruct.comp; apply Term.subst_comp

/-- Extension (or `cons`ing) of a context with a new variable. -/
@[reducible]
def Context.cons (A : S) (xs : S.Context) : S.Context where
  length := xs.length + 1
  nth := Matrix.vecCons A xs.nth

-- Note that this is `\:`
scoped[Signature] infixr:67 " ∶ " => Signature.Context.cons

/-- The projection context morphism. -/
def Context.π (xs : S.Context) (A : S) :
    (A ∶ xs) ⟶ xs := fun i ↦ .var (xs := A ∶ xs) i.succ

/-- The last variable in an extended context, as a term. -/
def Context.var (xs : S.Context) (A : S) : ⊢ᵗ[A∶xs] A :=
  Term.var 0

@[simp]
lemma Context.cons_succ (xs : S.Context) (A : S) (i : Fin xs.length) :
  (A ∶ xs).nth i.succ = xs.nth i := by simp

/-- Extending a context morphism with a new term. -/
def Context.Hom.cons {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} (t : S.Term ys A) :
    ys ⟶ (A ∶ xs) :=
  Fin.cons t (fun i ↦ Context.cons_succ xs A i ▸ σ i)

/-- The functor induced by the `cons` operation on contexts. -/
def Context.consFunctor (A : S) : S.Context ⥤ S.Context where
  obj xs := A ∶ xs
  map {xs} {ys} σ := Context.Hom.cons (xs.π A ≫ σ) (xs.var A)
  map_id xs := by
    funext i
    simp [cons, CategoryStruct.id]
    cases i using Fin.cases with
    | zero => simp [nthTerm, Context.var, Hom.cons]
    | succ i => simp [nthTerm, CategoryStruct.comp, Context.π, Hom.cons]
  map_comp σ σ' := by
    funext i
    simp [cons, CategoryStruct.comp]
    cases i using Fin.cases with
    | zero => simp [Context.var, Term.subst, Hom.cons]
    | succ i => simp [Context.var, Hom.cons]; rw [← Term.subst_comp, ← Term.subst_comp]; congr

/-- A term in context `xs` induces a context morphism `xs ⟶ (A ∶ xs)`. -/
def Context.Hom.consId {xs : S.Context} {A : S} (t : S.Term xs A) :
    xs ⟶ (A ∶ xs) :=
  Context.Hom.cons (𝟙 xs) t

lemma Context.Hom.consId_naturality {ys xs : S.Context} (σ : ys ⟶ xs) {A : S} (t : S.Term xs A) :
  (σ ≫ Context.Hom.consId t) =
    (Context.Hom.consId (Term.subst σ t) ≫ (Context.consFunctor A).map σ) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp [consId, CategoryStruct.comp, consFunctor, cons, CategoryStruct.id, Context.nthTerm]
    rw [← Term.subst_comp];
    simp [CategoryStruct.comp, Context.π, Term.subst]
    nth_rw 1 [← Term.subst_id (σ i)]
    rfl

@[simp]
lemma Context.Hom.cons_π (xs : S.Context) (A : S) (t : ⊢ᵗ[xs] A):
  Context.Hom.consId t ≫ xs.π A = 𝟙 _ := by
  funext i
  simp [CategoryStruct.comp, Context.Hom.consId,
    Context.π, Term.subst, CategoryStruct.id, Context.Hom.cons]

lemma Context.π_naturality (A : S) (σ : xs ⟶ ys) :
  (Context.consFunctor A).map σ ≫ ys.π A = xs.π A ≫ σ := by rfl

end Signature
