import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import ModelTheoryTopos.Geometric.Syntax.Formula
import ModelTheoryTopos.Geometric.Syntax.Derivation
import ModelTheoryTopos.Geometric.RegularCategory

open CategoryTheory Limits Signature

namespace Signature

universe u v

section
variable {S : Signature} {C : Type u} [Category.{v} C] [HasFiniteProducts C]

@[simp, reducible]
noncomputable def DerivedSorts.interpret {Sorts : Type*} (f : Sorts → C) : DerivedSorts Sorts → C := fun
  | .inj x => f x
  | .prod fᵢ => ∏ᶜ (fun i ↦ DerivedSorts.interpret f (fᵢ i))

variable (S) (C) in
structure Structure where
  sorts : S.Sorts → C
  Functions (f : S.Functions) : f.domain.interpret sorts ⟶ f.codomain.interpret sorts
  Relations (f : S.Relations) : Subobject <| f.domain.interpret sorts

noncomputable section

variable (M : Structure S C) {Δ Γ : S.Context} (σ : Context.Hom Δ Γ)

abbrev Context.interpret (Γ : S.Context) : C :=
  ∏ᶜ (fun i ↦ (Γ.ctx i).interpret M.sorts)

notation:arg "⟦" M "|" A "⟧ᵈ" => DerivedSorts.interpret (Structure.sorts M) A
notation:arg "⟦" M "|" Γ "⟧ᶜ" => Context.interpret M Γ
notation:arg "⟦" M "|" A "⟧ˢ" => Structure.sorts (self := M) A
notation:arg "⟦" M "|" Γ "⟧ᵖ" =>
  Subobject <| ∏ᶜ Structure.sorts (self := M) ∘ Context.ctx Γ

@[reducible]
def Term.interpret {A : S} :
    Γ ⊢ᵗ A → (⟦M | Γ⟧ᶜ ⟶ (⟦M | A⟧ᵈ))
  | .var v => Pi.π (fun i ↦ ⟦M | Γ.ctx i⟧ᵈ) v.val ≫ eqToHom (by aesop)
  | .func f t => t.interpret ≫ M.Functions f
  | pair tᵢ => Pi.lift fun i ↦ (tᵢ i).interpret
  | proj (Aᵢ := Aᵢ) t i => t.interpret ≫ Pi.π (fun i ↦ ⟦M | Aᵢ i⟧ᵈ) i

notation:arg "⟦" M "|" t "⟧ᵗ" =>
  Term.interpret M t

@[reducible]
def Context.Hom.interpret : ⟦M | Δ⟧ᶜ ⟶ ⟦M | Γ⟧ᶜ := Pi.lift (fun i ↦ ⟦M | σ i⟧ᵗ)

notation:arg "⟦" M "|" σ "⟧ʰ" => Context.Hom.interpret M σ

@[simp]
lemma Context.Hom.interpret_subst {A : S} (t : Γ ⊢ᵗ A) :
    ⟦M | t.subst σ ⟧ᵗ = ⟦M | σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var v => aesop
  | func f s ih =>
      simp only [Term.interpret, Context.Hom.interpret]
      rw [← Category.assoc]; congr
  | pair tᵢ =>
      simp only [Term.interpret, Context.Hom.interpret]
      ext; simp_all
  | proj t i =>
      simp only [Term.interpret, Context.Hom.interpret]
      rw [← Category.assoc]; congr

end

variable {S : Signature} {C : Type u} [Category.{v} C]
variable [κ : SmallUniverse S] [G : Geometric κ C] (M : Structure S C)

@[simp]
noncomputable def Formula.interpret {Γ : Context S} : Γ ⊢ᶠ𝐏 →
    (Subobject <| ⟦M | Γ ⟧ᶜ)
  | .rel P t => (Subobject.pullback ⟦M | t⟧ᵗ).obj <| M.Relations P
  | .true => ⊤
  | .false => ⊥
  | .conj P Q => P.interpret ⊓ Q.interpret
  | .eq t1 t2 => .mk <| equalizer.ι ⟦M | t1⟧ᵗ ⟦M | t2⟧ᵗ
  | .existsQ (A := A) P => (Subobject.«exists» ((Γ.π A).interpret M)).obj <|
      P.interpret
  | .infdisj fP => ∐ (fun i ↦ Formula.interpret (fP i))

notation:arg "⟦" M "|" P "⟧ᶠ" =>
  Formula.interpret M P

@[simp]
noncomputable def Formula.interpret_subst
    {Δ Γ : Context S} (σ: Δ ⟶ Γ) (P : Γ ⊢ᶠ𝐏) :
    ⟦M | P.subst σ⟧ᶠ = (Subobject.pullback ⟦M|σ⟧ʰ).obj ⟦M | P⟧ᶠ := by
  induction P with
  | rel o _ => sorry
  | true => sorry
  | false => sorry
  | conj _ _ _ _ => sorry
  | infdisj _ _ => sorry
  | eq _ _ => sorry
  | existsQ _ _ => sorry

def Sequent.interpret (U : S.Sequent) : Prop :=
  ⟦M | U.premise⟧ᶠ ≤ ⟦M | U.concl⟧ᶠ

def Theory.interpret (T : S.Theory) : Prop := ∀ Seq ∈ T.axioms, Seq.interpret M

def Soundness {T : S.Theory} {Γ : Context S} {Θ : FormulaContext Γ} {P : Γ ⊢ᶠ𝐏} :
  Derivation (T := T) Θ P → Theory.interpret M T →
    ∏ᶜ (fun i ↦ ⟦M | Θ.ctx i⟧ᶠ) ≤ ⟦M | P⟧ᶠ := by
  intro D int
  induction D with
  | «axiom» φinT D hp =>
      apply le_trans hp; simp only [Formula.interpret_subst];
      apply Functor.monotone; exact int _ φinT
  | var i => sorry
  | true_intro => simp
  | false_elim D h => rw [bot_unique h]; simp
  | conj_intro _ _ _ _ => sorry
  | conj_elim_l _ _ => sorry
  | conj_elim_r _ _ => sorry
  | infdisj_intro P i _ _ => sorry
  | infdisj_elim _ _ _ _ => sorry
  | eq_intro => sorry
  | eq_elim φ _ _ _ _ => sorry
  | existsQ_intro φ t _ _ => sorry
  | existsQ_elim φ _ _ => sorry

end
end Signature
