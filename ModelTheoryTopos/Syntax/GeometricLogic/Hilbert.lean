import ModelTheoryTopos.Syntax.GeometricLogic.Defs

open CategoryTheory

namespace Hilbert
inductive proof [SmallUniverse] {T : theory}: {n : RenCtx} → fml T.sig n → fml T.sig n → Prop where
  | axiom : s ∈ T.axioms -> proof (s.premise.subst σ) (s.concl.subst σ)
  | cut : proof φ τ -> proof τ ψ -> proof φ ψ
  | var : proof φ φ
  | true_intro : proof φ .true
  | false_elim : proof φ .false → proof φ ψ
  | conj_intro : proof ν φ → proof ν ψ → proof ν (.conj φ ψ)
  | conj_elim_l : proof (.conj φ  ψ) φ
  | conj_elim_r : proof (.conj φ  ψ) ψ
  | disj_intro_l : proof φ (.disj φ ψ)
  | disj_intro_r : proof ψ (.disj φ ψ)
  | disj_elim : proof δ (.disj φ ψ) →
    proof (φ.conj δ) ξ → proof (ψ.conj δ) ξ → proof δ ξ
  | infdisj_intro (k : SmallUniverse.El a) : proof (φ k) (.infdisj a φ)
  | infdisj_elim : proof δ (.infdisj a φ) →
    (forall k, proof (.conj (φ k) δ) ξ) → proof δ ξ
  | eq_intro : proof .true (.eq t t)
  | eq_elim (φ γ : (Fml _).obj _) : proof δ (.eq t u) →
    proof (δ.conj (γ⟪t ∷ 𝟙 _⟫)) (φ⟪t ∷ 𝟙 _⟫) →
    proof (δ.conj (γ⟪u ∷ 𝟙 _⟫)) (φ⟪u ∷ 𝟙 _⟫)
  | existsQ_intro (t : tm T.sig _) (φ : fml _ _) : proof (φ⟪t ∷ 𝟙 _⟫) (.existsQ φ)
  | existsQ_elim : proof  phi (fml.ren Fin.succ psi) -> proof (.existsQ phi) psi
    --existsQ_elim : proof (fml.ren Fin.succ (.existsQ φ)) φ
  | ren : proof φ ψ -> proof (fml.ren ρ φ) (fml.ren ρ ψ)

variable [SmallUniverse] {T : theory}

infix:30 " ⊢ " => proof

def proof.existn_intro {n k : Subst T.sig} (σ : n ⟶ k) (ψ : fml T.sig k) (φ : fml T.sig (k + n)) :
  proof ψ (φ.subst (substn σ)) -> proof ψ φ.existsn := by
  induction n generalizing ψ with
  | zero => simp only [substn0, fml.existsn] ; intros; rw [<-φ.subst_id]; assumption
  | succ i ih =>
    simp only [substnsucc, fml.existsn, fml.subst_comp]
    intros h
    apply ih (σ ∘ Fin.succ)
    simp only [fml.subst]
    apply cut h
    apply existsQ_intro

def proof.existn_elim {n k : Subst T.sig}  (ψ : fml T.sig k) (φ : fml T.sig (k + n)) :
  proof φ (ψ.ren (fun i ↦ i.addNat n)) -> proof φ.existsn ψ  := by
  induction n generalizing ψ with
  | zero =>
    simp only [fml.existsn, Fin.addNat_zero]
    intros
    rw [<-(fml.ren_id ψ)]
    assumption
  | succ i ih =>
    simp only [fml.existsn]
    intros
    apply ih
    apply existsQ_elim
    rw [<-fml.ren_comp]
    assumption



theorem eq_elim_subst0 {φ γ : fml T.sig (n+1)} (eq : δ ⊢ .eq t u)
  (pf : δ.conj (γ.subst (subst0 t)) ⊢ φ.subst (subst0 t)) :
  δ.conj (.subst (subst0 u) γ) ⊢ φ.subst (subst0 u) :=  by
  apply proof.eq_elim <;> assumption

theorem proof.conjn  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (fs: Fin k → fml T.sig n) :
 (∀ (i: Fin k), proof φ (fs i)) → proof φ (fml.conjn fs) := by
   induction k with
   | zero =>
     simp only [IsEmpty.forall_iff, fml.conjn, Fin.foldr_zero, Hilbert.proof.true_intro, imp_self]
   | succ n1 ih =>
     intro h
     have h1 : Hilbert.proof φ (fml.conjn (fs ∘ Fin.succ)) := by
       apply ih (fs ∘ Fin.succ)
       intro i
       have := h (Fin.succ i)
       assumption
     rw[fml.conjn_succ]
     apply Hilbert.proof.conj_intro
     · apply h
     · assumption

theorem proof.conj_iff
  {T: theory}  {n : RenCtx} (μ φ ψ: fml T.sig n) :
    μ ⊢ φ.conj ψ ↔ (μ ⊢ φ) ∧ (μ ⊢ ψ) := by
      constructor
      · intro h ; constructor <;> apply cut h
        · apply conj_elim_l
        · apply conj_elim_r
      · rintro ⟨⟩
        apply Hilbert.proof.conj_intro <;> assumption

theorem proof.conjn_elim_0 {T : theory} {n} (φ : fml T.sig n) (fs: Fin 0 → fml T.sig n) :
  φ ⊢ fml.conjn fs := by
  simp [fml.conjn]
  apply true_intro

theorem proof.conjn_elim_succ_l {T : theory} {n k} (φ : fml T.sig n)
  (fs: Fin (k+1) → fml T.sig n)
  (pf : φ ⊢ fml.conjn fs) :
  φ ⊢ fs (0 : Fin (k + 1)) := by
  apply cut pf
  simp [fml.conjn, Fin.foldr_succ]
  apply conj_elim_l

theorem proof.conjn_elim_succ_r {T : theory} {n k} (φ : fml T.sig n)
  (fs: Fin (k+1) → fml T.sig n)
  (pf : φ ⊢ fml.conjn fs) :
  φ ⊢ fml.conjn (fs ∘ Fin.succ) := by
  apply cut pf
  simp [fml.conjn, Fin.foldr_succ]
  apply conj_elim_r

theorem proof.conjn_elim  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (fs: Fin k → fml T.sig n) :
  Hilbert.proof φ (fml.conjn fs)  → (∀ (i: Fin k), Hilbert.proof φ (fs i)) := by
  induction k with
  | zero => intros _ i ; apply Fin.elim0 i
  | succ k ih =>
    intros pf i
    induction i using Fin.cases
    · apply conjn_elim_succ_l _ _ pf
    · apply ih (fs ∘ Fin.succ)
      apply conjn_elim_succ_r _ _ pf

theorem proof.eqs  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (ts1 ts2: Fin k → tm T.sig n)
  (h : ∀ (i: Fin k), φ ⊢ fml.eq (ts1 i) (ts2 i)) :
  Hilbert.proof φ (fml.eqs ts1 ts2) := by
  simp only[fml.eqs]
  apply conjn
  assumption

theorem proof.eqs'  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (ts1 ts2: Fin k → tm T.sig n):
  Hilbert.proof φ (fml.eqs ts1 ts2) →
  (∀ (i: Fin k), Hilbert.proof φ (fml.eq  (ts1 i) (ts2 i))) := by
  simp only[fml.eqs]
  apply conjn_elim


theorem proof.eqs_iff  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (ts1 ts2: Fin k → tm T.sig n):
  Hilbert.proof φ (fml.eqs ts1 ts2) ↔
  (∀ (i: Fin k), Hilbert.proof φ (fml.eq  (ts1 i) (ts2 i))) :=
  ⟨proof.eqs' _ ts1 ts2, proof.eqs _ _ _⟩

theorem any_eq_intro {T: theory} {n : RenCtx} (φ: fml T.sig n) (t u: tm T.sig n):
  t = u → Hilbert.proof φ (.eq t u) := by
  intro h ; rw [h]
  apply @Hilbert.proof.cut _ _ _ _ .true
  · apply Hilbert.proof.true_intro
  · apply Hilbert.proof.eq_intro

#check Hilbert.proof.eq_elim


end Hilbert
