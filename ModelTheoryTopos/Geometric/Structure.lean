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
import ModelTheoryTopos.ForMathlib.Subobject
import ModelTheoryTopos.ForMathlib.Miscellaneous

open CategoryTheory Limits Signature

namespace Signature

universe u v

section
variable {S : Signature} {C : Type u} [Category.{v} C] [HasFiniteProducts C]

@[simp, reducible]
noncomputable def DerivedSorts.interpret {Sorts : Type*} (f : Sorts → C) :
    DerivedSorts Sorts → C := fun
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

@[simp]
lemma Term.eqToHom_sort {A B : S} (p : A = B) (t : Γ ⊢ᵗ A) :
    ⟦M| p ▸ t⟧ᵗ = ⟦M | t⟧ᵗ ≫ eqToHom (p ▸ rfl : ⟦M|A⟧ᵈ=⟦M|B⟧ᵈ) := by
  induction p
  simp

@[simp]
lemma Term.interpret_pair_proj {Γ n} {Aᵢ : (i : Fin n) → S}
    (tᵢ : (i : Fin n) → Γ ⊢ᵗ (Aᵢ i)) {i : Fin n} :
    ⟦M|(Term.pair tᵢ).proj i⟧ᵗ = ⟦M|tᵢ i⟧ᵗ := by simp

@[simp]
lemma Term.interpret_proj {Γ n} {Aᵢ : (i : Fin n) → S} (t : Γ ⊢ᵗ .prod Aᵢ) :
    ⟦M|Term.pair (fun i ↦ t.proj i)⟧ᵗ = ⟦M|t⟧ᵗ := by
  apply Pi.hom_ext; simp


@[reducible]
def Context.Hom.interpret : ⟦M | Δ⟧ᶜ ⟶ ⟦M | Γ⟧ᶜ := Pi.lift (fun i ↦ ⟦M | σ i⟧ᵗ)

notation:arg "⟦" M "|" σ "⟧ʰ" => Context.Hom.interpret M σ

@[simp]
lemma Context.Hom.interpret_subst {A : S} (t : Γ ⊢ᵗ A) :
    ⟦M | t.subst σ⟧ᵗ = ⟦M | σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
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
lemma Term.interpret_subst
    {Δ Γ : Context S} (σ: Δ ⟶ Γ) {A : S} (t : Γ ⊢ᵗ A) :
    ⟦M | t.subst σ⟧ᵗ = ⟦M|σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var _ => simp
  | func f _ _ => simp [interpret]
  | pair tᵢ h =>
      simp only [DerivedSorts.interpret, interpret, Context.Hom.interpret_subst]
      rw [← funext h]; ext; simp
  | proj t i h => simp [interpret]

@[simp]
noncomputable def Formula.interpret {Γ : Context S} : Γ ⊢ᶠ𝐏 →
    (Subobject <| ⟦M | Γ ⟧ᶜ)
  | .rel P t => (Subobject.pullback ⟦M | t⟧ᵗ).obj <| M.Relations P
  | .true => ⊤
  | .false => ⊥
  | .conj P Q => P.interpret ⨯ Q.interpret
  | .eq t1 t2 => .mk <| equalizer.ι ⟦M | t1⟧ᵗ ⟦M | t2⟧ᵗ
  | .existsQ (A := A) P => (Subobject.«exists» ((Γ.π A).interpret M)).obj <|
      P.interpret
  | .infdisj fP => ∐ (fun i ↦ Formula.interpret (fP i))

notation:arg "⟦" M "|" P "⟧ᶠ" =>
  Formula.interpret M P



@[simp]
lemma Formula.interpret_subst
    {Δ Γ : Context S} (σ: Δ ⟶ Γ) (P : Γ ⊢ᶠ𝐏) :
    ⟦M | P.subst σ⟧ᶠ = (Subobject.pullback ⟦M|σ⟧ʰ).obj ⟦M | P⟧ᶠ := by
  induction P with
  | rel R t => simp[subst, Subobject.pullback_comp]
  | true => simp [subst, Subobject.pullback_top]
  | false => simp [subst]; sorry
  | conj P Q hp hq => simp [subst, interpret, hp, hq]
  | infdisj fP h =>
      simp only [interpret, subst]
      rw [← G.isJoin_isStableUnderBaseChange]
      have := funext (fun i ↦ h i σ)
      congr
  | eq t1 t2 =>
      simp only [interpret, subst]
      rw [← Subobject.pullback_equalizer]
      congr <;> try simp
      apply HEq_prop
      simp only [eq_iff_iff]
      apply Iff.intro <;> infer_instance
  | @existsQ A Γ P hp =>
      simp only [interpret, subst]
      sorry

def Sequent.interpret (U : S.Sequent) : Prop :=
  ⟦M | U.premise⟧ᶠ ≤ ⟦M | U.concl⟧ᶠ

def Theory.interpret (T : S.Theory) : Prop := ∀ Seq ∈ T.axioms, Seq.interpret M

@[reducible]
noncomputable def FormulaContext.interpret
    {Γ : Context S} (Θ : FormulaContext Γ) : Subobject ⟦M|Γ⟧ᶜ :=
  ∏ᶜ (fun i ↦ ⟦M | Θ.ctx i⟧ᶠ)

notation:arg "⟦" M "|" Θ "⟧ᶠᶜ" => FormulaContext.interpret (M := M) Θ

@[simp]
lemma FormulaContext.interpret_cons
    {Γ : Context S} (Θ : FormulaContext Γ) (P : Γ ⊢ᶠ𝐏) : ⟦M|Θ.cons P⟧ᶠᶜ = (⟦M|Θ⟧ᶠᶜ ⨯ ⟦M|P⟧ᶠ) := by
  apply Subobject.skeletal_subobject
  simp [interpret]
  constructor
  apply iso_of_both_ways
  · apply prod.lift
    · exact Pi.lift <| fun i ↦ Pi.π (fun i ↦ ⟦M|(Θ.cons P).ctx i⟧ᶠ) i.succ
    · let proj := Pi.π (fun i ↦ ⟦M|(Θ.cons P).ctx i⟧ᶠ)
      simp [cons] at proj
      exact proj 0
  · apply Pi.lift
    simp [cons]
    intro b
    cases b using Fin.cases
    · simpa using prod.snd
    · simp only [Matrix.cons_val_succ]
      refine prod.fst (X := ∏ᶜ fun i ↦ ⟦M|Θ.ctx i⟧ᶠ) (Y := ⟦M|P⟧ᶠ) ≫ ?_
      apply Pi.π

lemma FormulaContext.interpret_cons_pullback
    {Γ : Context S} (Θ : FormulaContext Γ) {I : Set κ} (P : Γ ⊢ᶠ𝐏) :
    ⟦M|Θ.cons P⟧ᶠᶜ = (Subobject.map (⟦M|Θ⟧ᶠᶜ).arrow).obj
      (((Subobject.pullback (⟦M|Θ⟧ᶠᶜ).arrow).obj ⟦M|P⟧ᶠ))  := by
  -- This should follow from the above and products `Subobject X` being pullbacks in `C`
  sorry

lemma FormulaContext.interpret_cons_join
    {Γ : Context S} (Θ : FormulaContext Γ) {I : Set κ} (Pᵢ : I → Γ ⊢ᶠ𝐏) :
    ⟦M|Θ.cons (⋁' Pᵢ)⟧ᶠᶜ = ∐ fun i ↦ ⟦M|Θ.cons (Pᵢ i)⟧ᶠᶜ := by
  rw [FormulaContext.interpret_cons_pullback]
  unfold Formula.interpret
  rw [← Geometric.isJoin_isStableUnderBaseChange]
  simp
  ext
  · sorry
  · sorry
  · sorry

def Soundness {T : S.Theory} {Γ : Context S} {Θ : FormulaContext Γ} {P : Γ ⊢ᶠ𝐏} :
  Derivation (T := T) Θ P → Theory.interpret M T →
    (⟦M | Θ⟧ᶠᶜ ≤ ⟦M | P⟧ᶠ) := by
  intro D int
  induction D with
  | «axiom» φinT D hp =>
      apply le_trans hp; simp only [Formula.interpret_subst];
      apply Functor.monotone; exact int _ φinT
  | @var Γ Θ i => exact (Pi.π (fun i ↦ ⟦M|Θ.ctx i⟧ᶠ) i).le
  | true_intro => simp
  | false_elim D h => rw [bot_unique h]; simp
  | conj_intro D D' h h' => exact (prod.lift h.hom h'.hom).le
  | conj_elim_l D h => exact (h.hom ≫ prod.fst).le
  | conj_elim_r D h => exact (h.hom ≫ prod.snd).le
  | infdisj_intro Pᵢ i D h => exact (h.hom ≫ Sigma.ι (fun i ↦ ⟦M|Pᵢ i⟧ᶠ) i).le
  | @infdisj_elim Γ Θ Q I Pᵢ D Dᵢ h h' =>
      apply leOfHom
      refine ?_ ≫ eqToHom (Θ.interpret_cons_join M Pᵢ) ≫ Sigma.desc (fun b ↦ (h' b).hom)
      simp only [FormulaContext.interpret_cons]
      exact prod.lift (𝟙 _) h.hom
  | eq_intro => simp [FormulaContext.interpret]
  | @eq_elim Γ A t1 t2 Θ Θ' φ D D' h h' =>
      sorry
  | @eq_proj_pair Γ n A tᵢ i Θ => simp
  | @eq_pair_proj Γ n Aᵢ t Θ =>
      have : IsIso (equalizer.ι ⟦M|Term.pair fun i ↦ t.proj i⟧ᵗ ⟦M|t⟧ᵗ) :=
        equalizer.ι_of_eq <| Term.interpret_proj M t
      simp [CategoryTheory.Subobject.mk_eq_top_of_isIso]
  | existsQ_intro φ t D h => sorry
  | existsQ_elim φ D h => sorry

end
end Signature
