import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Misc
import ModelTheoryTopos.Syntax.Signature

class SmallUniverse where
  U : Type
  El : U -> Type

-- instance natSU : SmallUniverse where
--   U := Unit
--   El _ := Nat

inductive fml [SmallUniverse] (m : monosig) : RenCtx -> Type where
--inductive fml.{u} (m : monosig) : RenCtx -> Type (u+1) where
  | pred : (p : m.preds) -> (Fin (m.arity_preds p) -> tm m n) -> fml m n
  | true : fml m n
  | false : fml m n
  | conj : fml m n -> fml m n -> fml m n
  | disj : fml m n -> fml m n -> fml m n
  | infdisj : (a : SmallUniverse.U) -> (SmallUniverse.El a -> fml m n) -> fml m n
--  | infdisj : (A : Type u) -> (A -> fml m n) -> fml m n
  | eq : tm m n -> tm m n -> fml m n
  | existsQ : fml m (n + 1) -> fml m n

namespace fml
variable [SmallUniverse]

def existsn : {n' : Nat} -> fml m (n + n') -> fml m n
| 0, φ => φ
| _+1, φ => existsn φ.existsQ

def conjn {k : ℕ} (fs: Fin k -> fml m n): fml m n :=
  Fin.foldr k (.conj ∘ fs) .true

theorem conjn_succ {k : ℕ} (fs: Fin (k + 1) -> fml m n):
   conjn fs = fml.conj (fs ((0 : Fin (k + 1)))) (fml.conjn (fs ∘ Fin.succ)) := by
    rw[conjn,Fin.foldr_succ]
    simp only [Function.comp_apply, conj.injEq, true_and]
    rw[conjn]
    congr

def eqs (lhs rhs : Fin k -> tm m n) : fml m n :=
  conjn  fun i => .eq (lhs i) (rhs i)

def ren {n n' : RenCtx} (f : n ⟶ n') : fml m n -> fml m n'
| .pred p k => .pred p (fun i => (k i).ren f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.ren f) (ψ.ren f)
| .disj φ ψ => .disj (φ.ren f) (ψ.ren f)
| .infdisj a φ => .infdisj a (fun i => (φ i).ren f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).ren f)
| .eq t u => .eq (t.ren f) (u.ren f)
| .existsQ φ => .existsQ (φ.ren (lift₁ f))

def subst {n n' : Subst m} (f : n ⟶ n') : fml m n → fml m n'
| .pred p k => .pred p (fun i => (k i).subst f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.subst f) (ψ.subst f)
| .disj φ ψ => .disj (φ.subst f) (ψ.subst f)
| .infdisj a φ => .infdisj a (fun i => (φ i).subst f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).subst f)
| .eq t u => .eq (t.subst f) (u.subst f)
| .existsQ φ => .existsQ (φ.subst (lift_subst f))

theorem ren_to_subst  (f : n ⟶ n') (φ: fml S n):
  (ren f φ) = fml.subst (fun i => tm.var (f i)) φ := by
  induction φ generalizing n' with
  | pred p _ =>
    simp only [ren, tm.ren_to_subst, fml.subst, fml.pred.injEq, heq_eq_eq, true_and];rfl
  | true => simp only [ren, fml.subst]
  | false => simp only [ren, fml.subst]
  | conj _ _ h1 h2 =>
    simp only [ren, h1, h2, fml.subst]
  | disj _ _ h1 h2 =>
    simp only [ren, h1, h2, fml.subst]
  | infdisj _ _ ih =>
    simp only [ren, fml.subst, ih]
  | eq _ _ =>
    simp only [ren, tm.ren_to_subst, fml.subst, fml.eq.injEq]
    exact ⟨by rfl, by rfl⟩
  | existsQ _ ih =>
    simp only [ren, fml.subst, ih]
    congr
    funext i
    simp [lift_subst, lift₁]
    induction i using Fin.cases with
    | zero => simp [lift₁]
    | succ i =>
      simp only [lift₁, Fin.cases_succ, Function.comp_apply, tm.ren]

end fml

-- x1, .., xn | φ ⊢ ψ
structure sequent [SmallUniverse] (m : monosig) where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx


structure theory [SmallUniverse] where
  sig : monosig
  axioms : List (sequent sig)

instance fmlSubst [SmallUniverse] : ScopedSubstitution (tm S) (fml S) where
  ssubst σ t := fml.subst σ t

namespace fml
  variable [SmallUniverse]
theorem subst_conjn {k n n': RenCtx} (σ : Fin n -> tm m n') (fs: Fin k -> fml m n):
 subst σ (conjn fs) = conjn (fun i => subst σ (fs i)) := by
   induction k generalizing n with
   | zero =>
     simp only [conjn,  Fin.foldr,
          Nat.zero_eq,Fin.foldr.loop,subst]
   | succ n1 ih =>
     have := ih σ (fs ∘ Fin.succ)--(fun i => fs (Fin.castAdd 1 i))
     simp only[conjn,subst]
     simp only[Fin.foldr_succ]
     simp only [Nat.succ_eq_add_one, Function.comp_apply]
     simp only[subst]
     congr

theorem subst_eq:
  subst σ (eq t1 t2) = eq (tm.subst σ t1) (tm.subst σ t2) := rfl

theorem subst_eqs :
  subst σ (eqs ts1 ts2) =
  eqs (fun i => tm.subst σ (ts1 i)) (fun i => tm.subst σ (ts2 i)) := by
   simp only[subst,eqs]
   simp only[subst_conjn,subst_eq]


open CategoryTheory

theorem ren_id {n : RenCtx} (f : fml m n)
  : ren (𝟙 n) f = f := by
  induction f with
  | pred => simp only [ren, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.ren_id]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [ren, conj.injEq,disj.injEq] ; constructor <;> simp only[ihφ, ihψ]
  | infdisj a φ ih => rw [ren] ; congr ; funext i ; exact ih _
  | eq t u => simp only [ren, tm.ren_id]
  | existsQ φ ih => rw [ren, lift₁_id, ih]

theorem ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  induction t generalizing n2 n3 with
  | pred => simp only [ren, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.ren_comp]
  | true | false => simp only [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [ren, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj a φ ih => simp only [ren]; congr ; funext i ; exact ih _ _ _
  | eq t u => simp only [ren, tm.ren_comp]
  | existsQ φ ih => simp only [ren, lift₁_comp, ih]

theorem subst_id {n : Subst m} (f : fml m n)
  : subst (𝟙 n) f = f := by
  induction f with
  | pred => simp only [subst, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.subst_id]
  | true | false => simp only [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [subst, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj a φ ih => simp only [subst]; congr ; funext i ; apply ih
  | eq t u => simp only [subst, tm.subst_id]
  | existsQ φ ih => simp only [subst, lift_subst_id, ih]

theorem subst_comp {n1 n2 n3 : Subst m} (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  subst (f ≫ g) t = subst g (subst f t) := by
  induction t generalizing n2 n3 with
  | pred => simp only [subst, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.subst_comp]
  | true | false => simp only [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [subst, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj a φ ih => simp only [subst]; congr ; funext i ; exact ih _ _ _
  | eq t u => simp only [subst, tm.subst_comp]
  | existsQ φ ih => simp only [subst, lift_subst_comp, ih]
end fml

open CategoryTheory


def Fml [SmallUniverse] m : Subst m ⥤ Type where
  map := fml.subst
  map_id := by intros ; funext t ; simp [fml.subst_id]
  map_comp := by intros ; funext t ; simp [fml.subst_comp]

-- def fml.subst_fst (t : (Fml m).obj (n+1)) (a : tm m n) : fml m n :=
--   t[a..]

def ListFunctor : Type ⥤ Type where
  map := List.map

def Ctx m : Subst m ⥤ Type := Fml m ⋙ ListFunctor


-- Is there a way to make Ctx transparent enough for typeclass search ?
instance: HAppend (List (fml m n)) ((Ctx m).obj n) (List (fml m n)) where
  hAppend := fun l l' => let l'' : List (fml m n) := l' ; l ++ l''

abbrev FmlCtx (T : theory) n := List (fml T.sig n)

instance : ScopedSubstitution (tm T.sig) (FmlCtx T) where
  ssubst σ t := (Ctx T.sig).map σ t

namespace StructuredProofs
inductive proof {T : theory}: {n : RenCtx} → FmlCtx T n → fml T.sig n → Prop where
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
  | infdisj_intro (a : SmallUniverse.U) (φ : SmallUniverse.El a → fml T.sig n) : proof Γ (φ k) → proof Γ (.infdisj a φ)
  | infdisj_elim : proof Γ (.infdisj a φ) →
    (forall k, proof (φ k :: Γ) ξ) → proof Γ ξ
  | eq_intro : proof Γ (.eq t t)
  | eq_elim (φ : fml _ _) (Γ : FmlCtx _ _) : proof Δ (.eq t u) →
    proof (Δ ++ Γ⟪t ∷ 𝟙 _ ⟫) (φ⟪t ∷ 𝟙 _⟫) →
    proof (Δ ++ Γ⟪u ∷ 𝟙 _ ⟫) (φ⟪u ∷ 𝟙 _ ⟫)
  | existsQ_intro (φ : (Fml _).obj _) : proof Γ (φ⟪t ∷ 𝟙 _⟫) → proof Γ (.existsQ φ)
  | existsQ_elim : proof Γ (.existsQ φ) →
    proof (List.map (fml.ren Fin.succ) Γ) φ


theorem proof.weaken {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> φ ∈ Γ), proof Γ ψ :=
  by sorry

-- TODO: cut could be made admissible ; requires weakening first
theorem proof.cut {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> proof Γ φ), proof Γ ψ := by
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


def derivable (T : theory) (s : sequent T.sig) := proof [s.premise] s.concl

def sequent.of_formulas (Γ : FmlCtx T n) (φ : fml T.sig n) : sequent T.sig where
  ctx := n
  premise := List.foldr .conj .true Γ
  concl := φ

theorem sequent.from_proof : proof Γ φ -> derivable _ (of_formulas Γ φ) := by
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

theorem sequent.to_proof : derivable _ (of_formulas Γ φ) -> proof Γ φ := by
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

namespace Hilbert
inductive proof {T : theory}: {n : RenCtx} → fml T.sig n → fml T.sig n → Prop where
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
    (forall k, proof (.conj (φ k) δ) ξ) → proof Γ ξ
  | eq_intro : proof .true (.eq t t)
  | eq_elim (φ γ : (Fml _).obj _) : proof δ (.eq t u) →
    proof (δ.conj (γ⟪t ∷ 𝟙 _⟫)) (φ⟪t ∷ 𝟙 _⟫) →
    proof (δ.conj (γ⟪u ∷ 𝟙 _⟫)) (φ⟪u ∷ 𝟙 _⟫)
  | existsQ_intro (t : tm T.sig _) (φ : fml _ _) : proof (φ⟪t ∷ 𝟙 _⟫) (.existsQ φ)
  | existsQ_elim : proof  phi (fml.ren Fin.succ psi) -> proof (.existsQ phi) psi
    --existsQ_elim : proof (fml.ren Fin.succ (.existsQ φ)) φ
  | ren : proof φ ψ -> proof (fml.ren ρ φ) (fml.ren ρ ψ)

variable {T : theory}

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

def proof.existn_elim {n k : Subst T.sig} (σ : n ⟶ k) (ψ : fml T.sig k) (φ : fml T.sig (k + n)) :
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
    apply ih (σ ∘ Fin.succ)
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

theorem any_eq_intro {T: theory} {n : RenCtx} (φ: fml T.sig n) (t: tm T.sig n):
  Hilbert.proof φ (.eq t t) := by
  apply @Hilbert.proof.cut _ _ _ .true
  · apply Hilbert.proof.true_intro
  · apply Hilbert.proof.eq_intro

#check Hilbert.proof.eq_elim


end Hilbert

namespace SyntacticSite


namespace R
abbrev in10 (i : Fin n) : Fin (n + k) := i.addNat k
abbrev in01 (i : Fin n) : Fin (k + n) := i.castAdd' k
abbrev in101 : Fin (n + k) -> Fin (n + k + k) :=
  Fin.casesAdd (in10 ∘ in10) in01
abbrev in110 : Fin (n + k) -> Fin (n + k + k) := in10
abbrev in001 : Fin k -> Fin (n + k + k) := in01
abbrev in010 : Fin k -> Fin (n + k + k) := in10 ∘ in01
abbrev in100 : Fin n -> Fin (n + k + k) := in10 ∘ in10
end R
#check substn



--theorem in10_substn (φ: fml m k): fml.ren (@R.in01 n k) φ  =  fml.subst (substn (@R.in01 n k)) φ := sorry

--theorem in10_substn_in01 (φ: fml m k): fml.ren (@R.in01 n k) φ =
structure functional {T: theory} {n1 n2 : RenCtx} (φ: fml T.sig n1) (ψ : fml T.sig n2) (θ  : fml T.sig (n1 + n2)) where
 total : Hilbert.proof φ θ.existsn
 range: Hilbert.proof θ ((φ.ren R.in10).conj (ψ.ren R.in01))
 unique : Hilbert.proof ((θ.ren R.in101).conj (θ.ren R.in110)) (fml.eqs (tm.var ∘ R.in010) (tm.var ∘ R.in001))


/-namespace Example

  def phi : fml S 1 := fml.existsQ (.eq (.var 0) (.var 1))

  def psi : (Fml S).obj 2 := .eq (.var (0 : Fin 2)) (.var (1 : Fin 2))

  def proof_phi : Hilbert.proof (T:=T) .true phi := by
    simp only [phi]
    apply Hilbert.proof.cut (τ:=psi[(.var 0)..])
    · apply Hilbert.proof.eq_intro
    · apply Hilbert.proof.existsQ_intro

end Example


-/



def id_rep {T: theory} {n : RenCtx} (φ: fml T.sig n) : fml T.sig (n+n) :=
 (φ.ren R.in10).conj
 (fml.eqs (tm.var ∘ R.in10) (tm.var ∘ R.in01))


theorem Hilbert.eqs_elim {T: theory} {n' n : Subst T.sig}  (δ : fml T.sig n')  (φ γ: fml T.sig (n'+n)) (ts1 ts2:  n ⟶  n'):
 Hilbert.proof δ (.eqs ts1 ts2) →
 Hilbert.proof (δ.conj (.subst (substn ts1) γ)) (.subst (substn ts1) φ) →
 Hilbert.proof (δ.conj (.subst (substn ts2) γ)) (.subst (substn ts2) φ) := by
     induction n  with
     | zero =>
       simp only[substn0, fml.subst_id]
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
           --have := @substnsucc'
         --have := @substnsucc'
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
          simp only [Nat.succ_eq_add_one, φ', γ', si]
          congr
         simp only [← geq, ← peq, γ', φ', si]
         assumption


namespace S
  def in10 {n k : Subst S} : n  ⟶ n + k := tm.var ∘ R.in10
  def in01 {n k : Subst S} : k  ⟶ n + k := tm.var ∘ R.in01

  -- #check fun S (n k : Subst S) => @in10 S n k ++ @in10 S n k ++ @in01 S n k
end S

theorem substn_section {T: theory} {k n : Subst T.sig} (φ : fml T.sig k) (σ :  k ⟶ n) :
  (φ.ren R.in01).subst (substn σ) = φ.subst σ := by
  simp [fml.ren_to_subst, <-fml.subst_comp, R.in01]
  congr
  funext i
  simp [tm.subst_comp_app, tm.subst, substn]

theorem Hilbert.eqs_elim' {T: theory} {k n : Subst T.sig} (δ : fml T.sig n)  (φ ψ: fml T.sig k) (σ τ:  k ⟶ n)
  (h : Hilbert.proof δ (.eqs σ τ)):
  Hilbert.proof (δ.conj (ψ.subst σ)) (φ.subst σ) →
  Hilbert.proof (δ.conj (ψ.subst τ)) (φ.subst τ) := by
  rw [<-substn_section ψ σ, <-substn_section φ σ,
    <-substn_section ψ τ, <-substn_section φ τ]
  apply Hilbert.eqs_elim δ _ _ σ τ h

theorem Hilbert_eqs_intro {T: theory} {n k: RenCtx} (φ: fml T.sig n) (σ: Fin k → tm T.sig n):
 φ ⊢ fml.eqs σ σ := sorry

theorem Hilbert_eq_symm {T: theory} {n k: RenCtx} (t1 t2:  tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → φ ⊢ fml.eq t2 t1 :=

   sorry

theorem Hilbert_eqs_symm {T: theory} {n k: RenCtx} (σ1 σ2: Fin k → tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eqs σ1 σ2 → φ ⊢ fml.eqs σ2 σ1 :=
  sorry

theorem Hilbert.conj_add_true {T: theory} (φ ψ : fml T.sig n) :
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

-- namespace Example

--   def phi : fml S 1 := fml.existsQ (.eq (.var 0) (.var 1))

--   def psi : (Fml S).obj 2 := .eq (.var (0 : Fin 2)) (.var (1 : Fin 2))

--   def proof_phi : Hilbert.proof (T:=T) .true phi := by
--     simp only [phi]
--     apply Hilbert.proof.cut (τ:=psi[(.var 0)..])
--     · apply Hilbert.proof.eq_intro
--     · apply Hilbert.proof.existsQ_intro

-- end Example
-- theorem substn_left {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n'):
--   substn σ (Fin.addNat a n) = .var a := by
--    simp only [substn, Fin.casesAdd_left]
--    rfl

-- theorem substn_right {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n):
--   substn σ (Fin.castAdd' n' a ) = σ a := by
--    simp only [substn, Fin.casesAdd_right]

-- TODO: this should us fml.subst_id, fml.ren_to_subst and fml.subst_comp
theorem tm.subst_ren_id {T: theory} {n: RenCtx} (t: tm T.sig n):
 (.subst (substn fun i ↦ tm.var i) (tm.ren R.in10 t)) = t := by
   induction t with
   | var a => simp only [tm.ren, R.in10, tm.subst, substn_left]
   | op o σ ih =>
    simp only [tm.ren, tm.subst, tm.op.injEq, heq_eq_eq, true_and]
    ext
    simp only [ih]

-- theorem tm.subst_ren_id' {T: theory} {n k: RenCtx} (t: tm T.sig n):
--  (.subst (substn fun i ↦ foo i) (tm.ren (@R.in10 n k) t)) = t := sorry

theorem Subst_comp_o {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  ( tm.var ∘ f) ≫ g = g ∘ f := rfl

theorem Subst_comp_o' {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  (fun i => tm.var (f i)) ≫ g = g ∘ f := rfl


-- TODO: this should be a straightforward application of fml.ren_id and fml.ren_comp
theorem fml.subst_ren_id {T: theory} {n: Subst T.sig} (φ: fml T.sig n):
 (fml.subst (substn fun i ↦ tm.var i) (fml.ren R.in10 φ)) = φ := by
      simp[fml.ren_to_subst,<-fml.subst_comp]
      have := @SyntacticSite.Subst_comp_o' T.sig _ _ _ (@R.in10 n n) (substn tm.var)
      let v : emb.obj n → tm T.sig n:= @tm.var T.sig n
      have h0: (fun i ↦ tm.var i) = @tm.var T.sig n:= rfl
      simp [emb]
      simp only[h0]
      simp[this]
      have := @fml.subst_id T.sig n
      let ff : n ⟶ n := ((@substn T.sig n n tm.var) ∘  (@R.in10 n n) )
      have h : ff = 𝟙 n := by
       funext
       simp[ff,substn_left,R.in10]
       rfl
      simp[ff] at h
      simp[h]
      apply this




theorem fun_map_comp : (fun i ↦ g (f i)) = fun i => (g ∘ f) i := rfl
theorem fun_map_comp' : (fun i ↦ g (f i)) =(g ∘ f) := rfl



theorem subst_comp_var: (tm.subst σ) ∘ .var = σ := rfl

theorem in110_01_010 : (@R.in110 n k) ∘ R.in01 = R.in010 := rfl
theorem in110_10_100 : (@R.in110 n k) ∘ R.in10 = R.in100 := rfl
theorem in101_10_100 : (@R.in101 n k) ∘ R.in10 = R.in100 := by
  ext i
  simp only [Function.comp_apply, Fin.casesAdd_left, Fin.coe_addNat]
theorem in101_10_010 : (@R.in101 n k) ∘ R.in01 = R.in001 := by
  ext i
  simp only [Function.comp_apply, Fin.casesAdd_right, Fin.coe_castAdd']

theorem Hilbert_eq_trans {T: theory} {n : RenCtx} (t1 t2 t3: tm T.sig n) (φ ψ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → ψ ⊢ fml.eq t2 t3 → φ.conj ψ ⊢ fml.eq t1 t3 := sorry

theorem Hilbert_eq_trans' {T: theory} {n : RenCtx} (t1 t2 t3: tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → φ ⊢ fml.eq t2 t3 → φ ⊢ fml.eq t1 t3 := sorry

theorem Hilbert_eqs_trans' {T: theory} {n k: RenCtx} (σ1 σ2 σ3: Fin k →  tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eqs σ1 σ2 → φ ⊢ fml.eqs σ2 σ3→ φ ⊢ fml.eqs σ1 σ3 := sorry



theorem Hilbert_conj_1  {T: theory} {n: RenCtx} (δ φ ψ: fml T.sig n):
 δ ⊢ φ.conj ψ → δ ⊢ φ := by
   intro h
   have := @Hilbert.proof.cut T n δ (φ.conj ψ)
   apply this h
   exact Hilbert.proof.conj_elim_l

theorem Hilbert_conj_2  {T: theory} {n: RenCtx} (δ φ ψ: fml T.sig n):
 δ ⊢ φ.conj ψ → δ ⊢ ψ := by
   intro h
   have := @Hilbert.proof.cut T n δ (φ.conj ψ)
   apply this h
   exact Hilbert.proof.conj_elim_r



theorem id_rep_functional  {T: theory} {n : RenCtx} (φ: fml T.sig n) :
  functional φ φ (id_rep φ) where
    total := by
      apply Hilbert.proof.existn_intro (fun i => tm.var i)
      rw[id_rep,fml.subst,fml.subst_eqs]
      apply Hilbert.proof.conj_intro
      · simp only [fml.subst_ren_id]; apply Hilbert.proof.var
      · apply Hilbert.proof.eqs
        intro i
        simp [R.in10,R.in01,tm.subst,substn_left,substn_right]--some simp lemmas maybe
        apply Hilbert.any_eq_intro
    range := by
      simp[id_rep]
      apply Hilbert.proof.conj_intro
      · apply Hilbert.proof.conj_elim_l
      ·  simp only[fml.ren_to_subst]
         simp only[fun_map_comp']
         set σ  :=  (tm.var ∘ R.in10)
         set τ := (tm.var ∘ R.in01)
         set δ := (fml.subst σ φ).conj (fml.eqs σ τ)
         have h1 : δ ⊢ fml.eqs σ τ := by
           simp only[δ]
           exact Hilbert.proof.conj_elim_r
         have := @Hilbert.eqs_elim' T n (n+n) δ φ .true σ τ h1
         simp[fml.subst,← Hilbert.conj_add_true] at this
         apply this
         simp only[δ]
         exact Hilbert.proof.conj_elim_l
    unique := by
     simp only [fml.ren_to_subst, fun_map_comp']
     simp only[id_rep,fml.subst] --does Lean have match abbrev which will not require copy-and-paste?
     simp only[fml.subst_eqs,fun_map_comp']
     simp[← Function.comp_assoc]
     simp[subst_comp_var]
     simp[Function.comp_assoc]
     simp[in110_10_100,in110_01_010,in101_10_100,in101_10_010]
     apply Hilbert_eqs_trans' _ (tm.var ∘ R.in100)
     · apply Hilbert_eqs_symm
       apply Hilbert_conj_2 _ (fml.subst (tm.var ∘ R.in110) (fml.ren R.in10 φ))
       apply Hilbert_conj_2 _ ((fml.subst (tm.var ∘ R.in101) (fml.ren R.in10 φ)).conj (fml.eqs (tm.var ∘ R.in100) (tm.var ∘ R.in001)))
       apply Hilbert.proof.var
     · apply Hilbert_conj_2 _ (fml.subst (tm.var ∘ R.in101) (fml.ren R.in10 φ))
       apply Hilbert_conj_1 _ _ ((fml.subst (tm.var ∘ R.in110) (fml.ren R.in10 φ)).conj (fml.eqs (tm.var ∘ R.in100) (tm.var ∘ R.in010)))
       apply Hilbert.proof.var



@[simp]
def fml_equiv {T: theory} {n : RenCtx} (φ ψ: fml T.sig n) := Hilbert.proof φ ψ ∧ Hilbert.proof ψ φ

theorem fml_equiv_Equivalence {T: theory} {n : RenCtx} : Equivalence (@fml_equiv T n) where
  refl := by
    intro φ
    simp
    apply Hilbert.proof.var
  symm := by
    intros φ ψ asm
    simp only [fml_equiv] at *
    simp only [asm, and_self]
  trans := by
    intro x y z a1 a2
    simp only [fml_equiv] at *
    constructor <;> apply Hilbert.proof.cut (τ:=y) <;> simp [a1, a2]

structure theory_fml (T: theory) where
  ctx: RenCtx
  fml : fml T.sig n


end SyntacticSite
