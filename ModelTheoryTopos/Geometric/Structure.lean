import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import ModelTheoryTopos.Geometric.Syntax.Formula
import ModelTheoryTopos.Geometric.RegularCategory

open CategoryTheory Limits Signature

namespace Signature

universe u v

section
variable {S : Signature} {C : Type u} [Category.{v} C] [HasFiniteProducts C]

variable (S) (C) in
structure Structure where
  sorts : S → C
  Functions (f : S.Functions) : ∏ᶜ (sorts ∘ f.sortedArity) ⟶ sorts f.codomain
  Relations (f : S.Relations) : Subobject <| ∏ᶜ (sorts ∘ f.sortedArity)

noncomputable section

variable (M : Structure S C) {Δ Γ : S.Context} (σ : Context.Hom Δ Γ)

abbrev Context.interpret (Γ : S.Context) : C :=
  ∏ᶜ M.sorts ∘ Γ.ctx

notation:arg "⟦" M "|" Γ "⟧ᶜ" =>  Context.interpret M Γ
notation:arg "⟦" M "|" A "⟧ˢ" => Structure.sorts (self := M) A
notation:arg "⟦" M "|" Γ "⟧ᵖ" =>
  Subobject <| ∏ᶜ Structure.sorts (self := M) ∘ Context.ctx Γ

@[simp]
def Term.interpret {A : S} :
    Γ ⊢ᵗ A → (⟦M | Γ⟧ᶜ ⟶ (⟦M | A⟧ˢ))
  | .var v => Pi.π (M.sorts ∘ Γ.ctx) v.val ≫ eqToHom (congrArg M.sorts v.prop)
  | .func f t => Pi.lift (fun b ↦ (t b).interpret) ≫ M.Functions f

notation:arg "⟦" M "|" t "⟧ᵗ" =>
  Term.interpret M t

@[simp]
def Context.Hom.interpret : ⟦M | Δ⟧ᶜ ⟶ ⟦M | Γ⟧ᶜ := Pi.lift (fun i ↦ ⟦M | σ i⟧ᵗ)

notation:arg "⟦" M "|" σ "⟧ʰ" => Context.Hom.interpret M σ

@[simp]
lemma Context.Hom.interpret_subst {A : S} (t : Γ ⊢ᵗ A) :
    ⟦M | t.subst σ ⟧ᵗ = ⟦M | σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var v => aesop
  | func f s ih =>
      simp only [Term.subst, Term.interpret, Context.Hom.interpret]
      rw [← Category.assoc]
      congr
      aesop_cat
end

variable {S : Signature} {C : Type u} [Category.{v} C]
variable [κ : SmallUniverse S] [G : Geometric κ C] (M : Structure S C)

@[simp]
noncomputable def Formula.interpret {Γ : Context S} : Γ ⊢ᶠ𝐏 →
    (Subobject <| ⟦M | Γ ⟧ᶜ)
  | .rel P t => (Subobject.pullback (Pi.lift (fun b ↦ ⟦M | t b⟧ᵗ))).obj <|
      M.Relations P
  | .true => ⊤
  | .false => ⊥_ _
  | .conj P Q => P.interpret ⊓ Q.interpret
  | .eq t1 t2 => .mk <| equalizer.ι ⟦M | t1⟧ᵗ ⟦M | t2⟧ᵗ
  | .existsQ (A := A) P => (Subobject.«exists» ((Γ.π A).interpret M)).obj <|
      P.interpret
  | .infdisj fP => ∐ (Formula.interpret ∘ fP)

end
end Signature
