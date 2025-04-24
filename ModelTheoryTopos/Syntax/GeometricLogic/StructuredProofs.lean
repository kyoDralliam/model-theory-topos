import ModelTheoryTopos.Syntax.GeometricLogic.Defs

-- UNUSED FILE
-- An early attempt to devise structured proofs objects for geometric logic
-- (so that weakening and substitution are admissible)
-- This is not necessary for the current goal of interpreting into
-- the (definitionally) proof irrelevant propositions of a topos

namespace StructuredProofs
inductive proof [SmallUniverse] {T : theory}: {n : RenCtx} → FmlCtx T n → fml T.sig n → Prop where
  | axiom : s ∈ T.axioms -> proof Γ (s.premise.subst σ) -> proof Γ (s.concl.subst σ)
  -- | cut : (forall φ, φ ∈ Δ -> proof Γ φ) -> proof Δ ψ -> proof Γ ψ
  | var : φ ∈ Γ → proof Γ φ
  | true_intro : proof Γ .true
  | false_elim : proof Γ .false → proof Γ φ
  | conj_intro : proof Γ φ → proof Γ ψ → proof Γ (.conj φ ψ)
  | conj_elim_l : proof Γ (.conj φ  ψ) → proof Γ φ
  | conj_elim_r : proof Γ (.conj φ  ψ) → proof Γ ψ
  | disj_intro_l : proof Γ φ → proof Γ (.disj φ ψ)
  | disj_intro_r : proof Γ ψ → proof Γ (.disj φ ψ)
  | disj_elim : proof Γ (.disj φ ψ) →
    proof (φ :: Γ) ξ → proof (ψ :: Γ) ξ → proof Γ ξ
  | infdisj_intro (a : SmallUniverse.U) (φ : SmallUniverse.El a → fml T.sig n) (i: SmallUniverse.El a) : proof Γ (φ i) → proof Γ (.infdisj a φ)
  | infdisj_elim : proof Γ (.infdisj a φ) →
    (forall k, proof (φ k :: Γ) ξ) → proof Γ ξ
  | eq_intro : proof Γ (.eq t t)
  | eq_elim (φ : fml _ _) (Γ : FmlCtx _ _) : proof Δ (.eq t u) →
    proof (Δ ++ Γ⟪t ∷ 𝟙 _ ⟫) (φ⟪t ∷ 𝟙 _⟫) →
    proof (Δ ++ Γ⟪u ∷ 𝟙 _ ⟫) (φ⟪u ∷ 𝟙 _ ⟫)
  | existsQ_intro (φ : (Fml _).obj _) : proof Γ (φ⟪t ∷ 𝟙 _⟫) → proof Γ (.existsQ φ)
  | existsQ_elim : proof Γ (.existsQ φ) →
    proof (List.map (fml.ren Fin.succ) Γ) φ

#check proof
theorem proof.weaken [SmallUniverse] {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> φ ∈ Γ), proof Γ ψ :=
  by sorry

-- TODO: cut could be made admissible ; requires weakening first
theorem proof.cut [SmallUniverse] {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> proof Γ φ), proof Γ ψ := by
  induction hψ with
  | «axiom» _ _ ih =>
    intros ; apply proof.axiom ; assumption ; apply ih ; assumption
  | var hin => intros Γ hsub; apply hsub ; assumption
  | true_intro => intros ; apply true_intro
  | false_elim _ _ => sorry
  | conj_intro _ _ ih₁ ih₂ =>
    intros; apply conj_intro
    · apply ih₁ ; assumption
    · apply ih₂ ; assumption
  | conj_elim_l _ ih => intros; apply conj_elim_l <;> apply ih ; assumption
  | conj_elim_r _ ih => intros; apply conj_elim_r <;> apply ih ; assumption
  | disj_intro_l _ ih => intros; apply disj_intro_l ; apply ih ; assumption
  | disj_intro_r _ ih => intros; apply disj_intro_r ; apply ih ; assumption
  | disj_elim h hl hr ih ihl ihr =>
    intros _ hsub ; apply disj_elim
    · apply ih ; assumption
    · apply ihl ; try assumption
      simp only [List.mem_cons, forall_eq_or_imp] ; constructor <;> try assumption
      · apply var ; simp only [List.mem_cons, true_or]
      · intros ; apply weaken ; apply hsub ; assumption
        intros ; simp only [List.mem_cons] ; right ; assumption
    · apply ihr ; try assumption
      simp ; constructor <;> try assumption
      · apply var ; simp only [List.mem_cons, true_or]
      · intros ; apply weaken ; apply hsub ; assumption
        intros ; simp only [List.mem_cons] ; right ; assumption
  | infdisj_intro _ _ => sorry
  | infdisj_elim _ _ _ _ => sorry
  | eq_intro => sorry
  | eq_elim φ Γ _ _ _ _ => sorry
  | existsQ_intro φ _ _ => sorry
  | existsQ_elim _ _ => sorry

def derivable [SmallUniverse] (T : theory) (s : sequent T.sig) := proof [s.premise] s.concl

def sequent.of_formulas [SmallUniverse] {T : theory} (Γ : FmlCtx T n) (φ : fml T.sig n) : sequent T.sig where
  ctx := n
  premise := List.foldr .conj .true Γ
  concl := φ

theorem sequent.from_proof [SmallUniverse] {T : theory} {Γ : FmlCtx T n} {φ : fml T.sig n}: proof Γ φ -> derivable _ (of_formulas Γ φ) := by
  intros hΓφ
  apply proof.cut _ _ _ hΓφ
  clear hΓφ
  induction Γ with
  | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons ψ Γ ih =>
    simp only [List.mem_cons, of_formulas, List.foldr_cons, forall_eq_or_imp] ; constructor
    · apply proof.conj_elim_l ; apply proof.var ; simp only [List.mem_singleton, fml.conj.injEq,
      true_and] ; rfl
    · intros τ hτ ; apply proof.cut _ _ _ (ih _ hτ) ; simp only [of_formulas,
      List.mem_singleton, forall_eq]
      apply proof.conj_elim_r ; apply proof.var ; simp only [List.mem_singleton, fml.conj.injEq,
        and_true] ; rfl

theorem sequent.to_proof [SmallUniverse] {T : theory} {Γ : FmlCtx T n} {φ : fml T.sig n}: derivable _ (of_formulas Γ φ) -> proof Γ φ := by
  intros hs ; apply proof.cut _ _ _ hs
  clear hs
  induction Γ with
  | nil => simp only [of_formulas, List.foldr_nil, List.mem_singleton, forall_eq] ; exact proof.true_intro
  | cons ψ Γ ih =>
    simp only [of_formulas, List.foldr_cons, List.mem_singleton, forall_eq] ; apply proof.conj_intro
    · apply proof.var ; simp only [List.mem_cons, true_or]
    · simp only [List.mem_singleton, forall_eq] at ih ; apply proof.cut _ _ _ ih
      intros ; apply proof.var; simp only [List.mem_cons] ; right ; assumption
end StructuredProofs
