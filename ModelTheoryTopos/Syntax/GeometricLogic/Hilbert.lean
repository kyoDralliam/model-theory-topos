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



theorem conj_copy {T: theory} (φ ψ : fml T.sig n) :
 Hilbert.proof φ ψ → Hilbert.proof φ (fml.conj φ ψ) := by
   intro p
   apply Hilbert.proof.conj_intro
   · apply Hilbert.proof.var
   · assumption


theorem conj_infdisj_distr_d1 :
   Hilbert.proof (fml.conj φ (fml.infdisj a f))
    (fml.infdisj a (fun i => fml.conj φ (f i))) := by
     apply Hilbert.proof.infdisj_elim (Hilbert.proof.conj_elim_r)
     intro k
     have p : (f k).conj (φ.conj (fml.infdisj a f)) ⊢ fml.conj φ (f k) := by
      apply Hilbert.proof.conj_intro
      · have p1 :
         (f k).conj (φ.conj (fml.infdisj a f)) ⊢ (φ.conj (fml.infdisj a f)) := by
         apply Hilbert.proof.conj_elim_r
        apply Hilbert.proof.cut p1
        apply Hilbert.proof.conj_elim_l
      · apply Hilbert.proof.conj_elim_l
     apply Hilbert.proof.cut p
     apply Hilbert.proof.infdisj_intro k



  theorem infdisj_elim' (a : SmallUniverse.U)
   (φ : SmallUniverse.El a → fml _ m) :
   (∀ k, φ k ⊢ ψ) → fml.infdisj a φ ⊢ ψ := by
    intro h
    have p: (fml.infdisj a φ) ⊢ (fml.infdisj a φ) := by
     apply Hilbert.proof.var
    apply Hilbert.proof.infdisj_elim p
    intro k
    have p' : (φ k).conj (fml.infdisj a φ) ⊢ φ k := by apply Hilbert.proof.conj_elim_l
    apply Hilbert.proof.cut p'
    apply h


  theorem conj_infdisj_distr_d2 :
   Hilbert.proof
    (fml.infdisj a (fun i => fml.conj φ (f i)))
    (fml.conj φ (fml.infdisj a f)) := by
    apply Hilbert.proof.conj_intro
    · apply infdisj_elim'
      intro k
      apply Hilbert.proof.conj_elim_l
    · apply infdisj_elim'
      intro k
      have p: φ.conj (f k) ⊢ f k := by
        apply Hilbert.proof.conj_elim_r
      apply Hilbert.proof.cut p
      apply Hilbert.proof.infdisj_intro k

  --YX: should think about a uniform way of doing that, like a conv
  theorem conj_infdisj_distr_iff_left :
   Hilbert.proof
    (fml.infdisj a (fun i => fml.conj φ (f i)))
    ψ ↔
    Hilbert.proof
   (fml.conj φ (fml.infdisj a f)) ψ
    := sorry


  --TODO: YX:IT HAS TO BE AN AXIOM!!!
  theorem push_conj_into_existsn  :
   Hilbert.proof (fml.conj φ (fml.existsn ψ))
    (fml.existsn (fml.conj (fml.ren R.in10 φ) ψ) ):= by
    sorry


  theorem Frobenius_reduction_lemma  :
   Hilbert.proof
    (fml.existsn (fml.conj (fml.ren R.in10 φ) ψ) ) ξ
    →
    Hilbert.proof
  (fml.conj φ (fml.existsn ψ)) ξ := by
   intro h
   apply Hilbert.proof.cut _ h
   apply push_conj_into_existsn


   theorem proof.existn_elim' {m: theory}{n k }  (ψ : fml m.sig k) (φ : fml _ (k + n)) :
  Hilbert.proof φ (fml.ren R.in10 ψ) -> Hilbert.proof (fml.existsn φ) ψ := by
    apply Hilbert.proof.existn_elim


  theorem proof.var' {m: theory}{k }  (φ ψ: fml m.sig k) (e: φ = ψ):
  Hilbert.proof φ ψ := by
   convert Hilbert.proof.var


  theorem fml.subst_cong : σ1 = σ2 → fml.subst σ1 f = fml.subst σ2 f := by
    intro h
    congr


  theorem proof.eqs_eq (i) :
  Hilbert.proof (fml.eqs ts1 ts2)  (fml.eq  (ts1 i) (ts2 i)) := by
   apply Hilbert.proof.eqs'
   apply Hilbert.proof.var



  theorem proof.eqs_elim (i) :
  Hilbert.proof (fml.eq (lhs i) (rhs i)) φ → Hilbert.proof (fml.eqs lhs rhs) φ := by
   intro h
   apply Hilbert.proof.cut (Hilbert.proof.eqs_eq i)
   assumption


  lemma proof.infdisj_intro' (k : SmallUniverse.El a) :
    Hilbert.proof ψ (φ k) → Hilbert.proof ψ (.infdisj a φ) := by
    intro h
    apply Hilbert.proof.cut h
    apply Hilbert.proof.infdisj_intro





theorem eqs_elim {T: theory} {n' n : Subst T.sig}  (δ : fml T.sig n')  (φ γ: fml T.sig (n'+n)) (ts1 ts2:  n ⟶  n'):
 Hilbert.proof δ (.eqs ts1 ts2) →
 Hilbert.proof (δ.conj (.subst (substn ts1) γ)) (.subst (substn ts1) φ) →
 Hilbert.proof (δ.conj (.subst (substn ts2) γ)) (.subst (substn ts2) φ) := by
     induction n  with
     | zero =>
       simp only[substn0]
       intros h1 h2
       assumption
     | succ n1 ih =>
       intros h1 h2
       simp only [Nat.succ_eq_add_one, substnsucc'] at *
       simp only [fml.subst_comp] at *
       apply ih _ _ (ts1 ∘ Fin.succ) (ts2 ∘ Fin.succ)
       · simp only [Hilbert.proof.eqs_iff, Nat.succ_eq_add_one, Function.comp_apply] at *
         intro i
         apply h1
       · simp only [← fml.subst_comp,
         Nat.succ_eq_add_one] at *
         simp only[← substnsucc'] at *
         simp only[← substnsucc'']
         simp only[substnsucc] at *
         simp only [fml.subst_comp] at *
         set γ' := (fml.subst (lift_subst (substn (ts1 ∘ Fin.succ))) γ)
         set φ' := (fml.subst (lift_subst (substn (ts1 ∘ Fin.succ))) φ)
         have h10 : Hilbert.proof δ (fml.eq (ts1 (0:Fin n1.succ)) ( ts2 (0:Fin n1.succ))) := by
           simp only [Hilbert.proof.eqs_iff] at h1
           exact h1 0
         have := Hilbert.eq_elim_subst0 h10 h2
         set si := (scons (ts2 (0:Fin n1.succ)) (ts1 ∘ Fin.succ))
         have t20 : si (0:Fin n1.succ) = ts2 (0:Fin n1.succ) := by
           simp only [Nat.succ_eq_add_one, Fin.cases_zero, si]
         simp only [t20, si]
         have geq: γ' = (fml.subst (lift_subst (substn (si ∘ Fin.succ))) γ) := by
          simp only [Nat.succ_eq_add_one, γ', si]
          congr --????? how?????
         have peq: φ' = (fml.subst (lift_subst (substn (si ∘ Fin.succ))) φ) := by
          simp only [Nat.succ_eq_add_one, φ', si]
          congr
         simp only [← geq, ← peq, γ', φ', si]
         assumption



theorem eqs_elim' {T: theory} {k n : Subst T.sig} (δ : fml T.sig n)  (φ ψ: fml T.sig k) (σ τ:  k ⟶ n)
  (h : Hilbert.proof δ (.eqs σ τ)):
  Hilbert.proof (δ.conj (ψ.subst σ)) (φ.subst σ) →
  Hilbert.proof (δ.conj (ψ.subst τ)) (φ.subst τ) := by
  rw [<-fml.substn_section ψ σ, <-fml.substn_section φ σ,
    <-fml.substn_section ψ τ, <-fml.substn_section φ τ]
  apply Hilbert.eqs_elim δ _ _ σ τ h



theorem conj_add_true {T: theory} (φ ψ : fml T.sig n) :
 Hilbert.proof φ ψ ↔ Hilbert.proof (φ.conj .true) ψ := by
  constructor
  · intro h
    apply Hilbert.proof.cut _ h
    exact Hilbert.proof.conj_elim_l
  · intro h
    apply Hilbert.proof.cut _ h
    apply Hilbert.proof.conj_intro
    · exact Hilbert.proof.var
    · exact Hilbert.proof.true_intro

omit [SmallUniverse] in
theorem Subst_comp_o {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  ( tm.var ∘ f) ≫ g = g ∘ f := rfl

omit [SmallUniverse] in
theorem Subst_comp_o' {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  (fun i => tm.var (f i)) ≫ g = g ∘ f := rfl


-- TODO: this should be a straightforward application of fml.ren_id and fml.ren_comp
theorem fml.subst_ren_id  {T: theory} {n: Subst T.sig} (φ: fml T.sig n):
 (fml.subst (substn fun i ↦ tm.var i) (fml.ren R.in10 φ)) = φ := by
      simp[fml.ren_to_subst,<-fml.subst_comp]
      have := @Subst_comp_o' T.sig _ _ _ (@R.in10 n n) (substn tm.var)
      let v : emb.obj n → tm T.sig n:= @tm.var T.sig n
      have h0: (fun i ↦ tm.var i) = @tm.var T.sig n:= rfl
      simp [emb]
      simp only[h0]
      simp[this]
      have := @fml.subst_id _ T.sig n
      let ff : n ⟶ n := ((@substn T.sig n n tm.var) ∘  (@R.in10 n n) )
      have h : ff = 𝟙 n := by
       funext
       simp[ff,substn_left,R.in10]
       rfl
      simp[ff] at h
      simp[h]
      apply this


end Hilbert
