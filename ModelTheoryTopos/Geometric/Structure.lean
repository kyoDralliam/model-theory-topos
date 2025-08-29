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
  Relations (R : S.Relations) : Subobject <| R.domain.interpret sorts

noncomputable section

variable (M : Structure S C) {ys xs : S.Context} (σ : ys ⟶ xs)

abbrev Context.interpret (xs : S.Context) : C :=
  ∏ᶜ (fun i ↦ (xs.nth i).interpret M.sorts)

notation:arg "⟦" M "|" A "⟧ᵈ" => DerivedSorts.interpret (Structure.sorts M) A
notation:arg "⟦" M "|" xs "⟧ᶜ" => Context.interpret M xs
notation:arg "⟦" M "|" A "⟧ˢ" => Structure.sorts (self := M) A
notation:arg "⟦" M "|" xs "⟧ᵖ" =>
  Subobject <| ∏ᶜ Structure.sorts (self := M) ∘ Context.nth xs

@[reducible]
def Term.interpret {A : S} :
    ⊢ᵗ[xs] A → (⟦M | xs⟧ᶜ ⟶ (⟦M | A⟧ᵈ))
  | .var v => Pi.π (fun i ↦ ⟦M | xs.nth i⟧ᵈ) v.val ≫ eqToHom (by aesop)
  | .func f t => t.interpret ≫ M.Functions f
  | pair tᵢ => Pi.lift fun i ↦ (tᵢ i).interpret
  | proj (Aᵢ := Aᵢ) t i => t.interpret ≫ Pi.π (fun i ↦ ⟦M | Aᵢ i⟧ᵈ) i

notation:arg "⟦" M "|" t "⟧ᵗ" =>
  Term.interpret M t

@[simp]
lemma Term.eqToHom_sort {A B : S} (p : A = B) (t : ⊢ᵗ[xs] A) :
    ⟦M| p ▸ t⟧ᵗ = ⟦M | t⟧ᵗ ≫ eqToHom (p ▸ rfl : ⟦M|A⟧ᵈ=⟦M|B⟧ᵈ) := by
  induction p; simp

@[simp]
lemma Term.interpret_pair_proj {xs n} {Aᵢ : (i : Fin n) → S}
    (tᵢ : (i : Fin n) → ⊢ᵗ[xs] (Aᵢ i)) {i : Fin n} :
    ⟦M|(Term.pair tᵢ).proj i⟧ᵗ = ⟦M|tᵢ i⟧ᵗ := by simp

@[simp]
lemma Term.interpret_proj {xs n} {Aᵢ : (i : Fin n) → S} (t : ⊢ᵗ[xs] .prod Aᵢ) :
    ⟦M|Term.pair (fun i ↦ t.proj i)⟧ᵗ = ⟦M|t⟧ᵗ := by
  apply Pi.hom_ext; simp


@[reducible]
def Context.Hom.interpret : ⟦M | ys⟧ᶜ ⟶ ⟦M | xs⟧ᶜ := Pi.lift (fun i ↦ ⟦M | σ i⟧ᵗ)

notation:arg "⟦" M "|" σ "⟧ʰ" => Context.Hom.interpret M σ

@[simp]
lemma Context.Hom.interpret_subst {A : S} (t : ⊢ᵗ[xs] A) :
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
    {ys xs : Context S} (σ: ys ⟶ xs) {A : S} (t : ⊢ᵗ[xs] A) :
    ⟦M | t.subst σ⟧ᵗ = ⟦M|σ⟧ʰ ≫ ⟦M | t⟧ᵗ := by
  induction t with
  | var _ => simp
  | func f _ _ => simp [interpret]
  | pair tᵢ h =>
      simp only [DerivedSorts.interpret, interpret, Context.Hom.interpret_subst]
      rw [← funext h]; ext; simp
  | proj t i h => simp [interpret]

@[simp]
noncomputable def Formula.interpret {xs : Context S} : xs ⊢ᶠ𝐏 →
    (Subobject <| ⟦M | xs ⟧ᶜ)
  | .rel P t => (Subobject.pullback ⟦M | t⟧ᵗ).obj <| M.Relations P
  | .true => ⊤
  | .false => ⊥
  | .conj P Q => P.interpret ⨯ Q.interpret
  | .eq t1 t2 => .mk <| equalizer.ι ⟦M | t1⟧ᵗ ⟦M | t2⟧ᵗ
  | .exists (A := A) P => (Subobject.«exists» ((xs.π A).interpret M)).obj <|
      P.interpret
  | .infdisj fP => ∐ (fun i ↦ Formula.interpret (fP i))

notation:arg "⟦" M "|" P "⟧ᶠ" =>
  Formula.interpret M P

@[simp]
lemma Formula.interpret_subst
    {ys xs : Context S} (σ: ys ⟶ xs) (P : xs ⊢ᶠ𝐏) :
    ⟦M | P.subst σ⟧ᶠ = (Subobject.pullback ⟦M|σ⟧ʰ).obj ⟦M | P⟧ᶠ := by
  induction P with
  | rel R t => simp [Subobject.pullback_comp]
  | true => simp [Subobject.pullback_top]
  | false => simp only [interpret]; sorry
  | conj P Q hp hq => simp [interpret, hp, hq]
  | infdisj fP h =>
      simp only [interpret]
      rw [← G.isJoin_isStableUnderBaseChange]
      have := funext (fun i ↦ h i σ)
      congr
  | eq t1 t2 =>
      simp only [interpret]
      rw [← Subobject.pullback_equalizer]
      congr <;> try simp
      apply HEq_prop
      simp only [eq_iff_iff]
      apply Iff.intro <;> infer_instance
  | @«exists» A xs P hp =>
      simp only [interpret]
      sorry

def Sequent.interpret (U : S.Sequent) : Prop :=
  ⟦M | U.premise⟧ᶠ ≤ ⟦M | U.concl⟧ᶠ

def Theory.interpret (T : S.Theory) : Prop := ∀ Seq ∈ T.axioms, Seq.interpret M

@[reducible]
noncomputable def FormulaContext.interpret
    {xs : Context S} (Γ : FormulaContext xs) : Subobject ⟦M|xs⟧ᶜ :=
  ∏ᶜ (fun i ↦ ⟦M | Γ.nth i⟧ᶠ)

notation:arg "⟦" M "|" Γ "⟧ᶠᶜ" => FormulaContext.interpret (M := M) Γ

@[simp]
lemma FormulaContext.interpret_append
    {xs : Context S} (Γ Δ : FormulaContext xs) :
    ⟦M|Γ ++ Δ⟧ᶠᶜ = (⟦M|Γ⟧ᶠᶜ ⨯ ⟦M|Δ⟧ᶠᶜ) := by
  apply Subobject.skeletal_subobject
  simp [interpret]
  constructor
  apply iso_of_both_ways
    ( prod.lift
      ( Pi.lift <| fun i ↦
        append_nth_l Γ _ _ ▸ Pi.π (fun i ↦ ⟦M|(Γ ++ Δ).nth i⟧ᶠ) ⟨i, by simp; omega⟩)
      ( Pi.lift <| fun i ↦
        append_nth_r Γ _ _ ▸ Pi.π (fun i ↦ ⟦M|(Γ ++ Δ).nth i⟧ᶠ) ⟨Γ.length + i, by simp⟩))
  apply Pi.lift
  intro ⟨i, i_leq⟩
  by_cases h : i < Γ.length
  · refine prod.fst ≫ Pi.π _ ⟨i, h⟩ ≫ eqToHom ?_
    rw [FormulaContext.append_nth_l'']
  · let k : ℕ := i - Γ.length
    have p : i = Γ.length + k := by aesop
    have k_leq : k < Δ.length := by
      simp [append_length] at i_leq
      omega
    refine prod.snd ≫ Pi.π _ ⟨k, k_leq⟩ ≫ eqToHom ?_
    have : Δ.nth ⟨k, k_leq⟩ = (Γ ++ Δ).nth ⟨Γ.length + k, p ▸ i_leq⟩ := by
      rw [FormulaContext.append_nth_r'']
    rw [this]
    congr
    exact p.symm

@[simp]
lemma FormulaContext.interpret_cons
    {xs : Context S} (Γ : FormulaContext xs) (φ : xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons φ⟧ᶠᶜ = (⟦M|Γ⟧ᶠᶜ ⨯ ⟦M|φ⟧ᶠ) := by
  apply Subobject.skeletal_subobject
  simp [interpret]
  constructor
  apply iso_of_both_ways
  · apply prod.lift
    · exact Pi.lift <| fun i ↦ Pi.π (fun i ↦ ⟦M|(Γ.cons φ).nth i⟧ᶠ) i.succ
    · let proj := Pi.π (fun i ↦ ⟦M|(Γ.cons φ).nth i⟧ᶠ)
      simp [cons] at proj
      exact proj 0
  · apply Pi.lift
    intro b
    cases b using Fin.cases
    · simpa using prod.snd
    · simp only [Matrix.cons_val_succ]
      refine prod.fst (X := ∏ᶜ fun i ↦ ⟦M|Γ.nth i⟧ᶠ) (Y := ⟦M|φ⟧ᶠ) ≫ ?_
      apply Pi.π

lemma FormulaContext.interpret_eq (t1 t2 : ⊢ᵗ[xs] A) :
  ⟦M|t1 =' t2⟧ᶠ =
    Subobject.mk (equalizer.ι ⟦M|Context.Hom.consId t1⟧ʰ ⟦M|Context.Hom.consId t2⟧ʰ) := sorry

lemma FormulaContext.interpret_cons_pullback
    {xs : Context S} (Γ : FormulaContext xs) {I : Set κ} (P : xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons P⟧ᶠᶜ = (Subobject.map (⟦M|Γ⟧ᶠᶜ).arrow).obj
      (((Subobject.pullback (⟦M|Γ⟧ᶠᶜ).arrow).obj ⟦M|P⟧ᶠ))  := by
  -- This should follow from the above and products in `Subobject X` being pullbacks in `C`
  sorry

lemma FormulaContext.interpret_cons_join
    {xs : Context S} (Γ : FormulaContext xs) {I : Set κ} (Pᵢ : I → xs ⊢ᶠ𝐏) :
    ⟦M|Γ.cons (⋁' Pᵢ)⟧ᶠᶜ = ∐ fun i ↦ ⟦M|Γ.cons (Pᵢ i)⟧ᶠᶜ := by
  rw [FormulaContext.interpret_cons_pullback]
  unfold Formula.interpret
  rw [← Geometric.isJoin_isStableUnderBaseChange]
  simp
  ext
  · sorry
  · sorry
  · sorry

def Soundness {T : S.Theory} {xs : Context S} {Γ : FormulaContext xs} {P : xs ⊢ᶠ𝐏} :
  Derivation (T := T) Γ P → Theory.interpret M T →
    (⟦M | Γ⟧ᶠᶜ ≤ ⟦M | P⟧ᶠ) := by
  intro D int
  induction D with
  | «axiom» φinT D hp =>
      apply le_trans hp; simp only [Formula.interpret_subst];
      apply Functor.monotone; exact int _ φinT
  | @var xs Γ i => exact (Pi.π (fun i ↦ ⟦M|Γ.nth i⟧ᶠ) i).le
  | true_intro => simp
  | false_elim D h => rw [bot_unique h]; simp
  | conj_intro D D' h h' => exact (prod.lift h.hom h'.hom).le
  | conj_elim_l D h => exact (h.hom ≫ prod.fst).le
  | conj_elim_r D h => exact (h.hom ≫ prod.snd).le
  | disj_intro Pᵢ i D h => exact (h.hom ≫ Sigma.ι (fun i ↦ ⟦M|Pᵢ i⟧ᶠ) i).le
  | @disj_elim xs Γ Q I Pᵢ D Dᵢ h h' =>
      apply leOfHom
      refine ?_ ≫ eqToHom (Γ.interpret_cons_join M Pᵢ) ≫ Sigma.desc (fun b ↦ (h' b).hom)
      simp only [FormulaContext.interpret_cons]
      exact prod.lift (𝟙 _) h.hom
  | eq_intro => simp [FormulaContext.interpret]
  | @eq_elim xs A t1 t2 Γ Γ' φ D_eq D' h h' =>
      simp at *
      apply leOfHom
      sorry
  | @eq_proj_pair xs n A tᵢ i Γ => simp
  | @eq_pair_proj xs n Aᵢ t Γ =>
      have : IsIso (equalizer.ι ⟦M|Term.pair fun i ↦ t.proj i⟧ᵗ ⟦M|t⟧ᵗ) :=
        equalizer.ι_of_eq <| Term.interpret_proj M t
      simp [CategoryTheory.Subobject.mk_eq_top_of_isIso]
  | exists_intro φ t D h => sorry
  | exists_elim D h => sorry

end
end Signature
