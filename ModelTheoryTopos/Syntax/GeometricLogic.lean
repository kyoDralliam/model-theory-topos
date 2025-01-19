import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Misc
import ModelTheoryTopos.Syntax.Signature


inductive fml (m : monosig) : RenCtx -> Type where
--inductive fml.{u} (m : monosig) : RenCtx -> Type (u+1) where
  | pred : (p : m.preds) -> (Fin (m.arity_preds p) -> tm m n) -> fml m n
  | true : fml m n
  | false : fml m n
  | conj : fml m n -> fml m n -> fml m n
  | disj : fml m n -> fml m n -> fml m n
  | infdisj : (Nat -> fml m n) -> fml m n
--  | infdisj : (A : Type u) -> (A -> fml m n) -> fml m n
  | eq : tm m n -> tm m n -> fml m n
  | existsQ : fml m (n + 1) -> fml m n

def fml.existsn : {n' : Nat} -> fml m (n + n') -> fml m n
| 0, φ => φ
| _+1, φ => existsn φ.existsQ

def fml.conjn {k : ℕ} (fs: Fin k -> fml m n): fml m n :=
  Fin.foldr k (.conj ∘ fs) .true

theorem fml.conjn_succ {k : ℕ} (fs: Fin (k + 1) -> fml m n):
   fml.conjn fs = fml.conj (fs ((0 : Fin (k + 1)))) (fml.conjn (fs ∘ Fin.succ)) := by
    rw[fml.conjn,Fin.foldr_succ]
    simp only [Function.comp_apply, conj.injEq, true_and]
    rw[fml.conjn]
    congr

def fml.eqs (lhs rhs : Fin k -> tm m n) : fml m n :=
  fml.conjn  fun i => .eq (lhs i) (rhs i)


-- x1, .., xn | φ ⊢ ψ
structure sequent (m : monosig) where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx


structure theory where
  sig : monosig
  axioms : List (sequent sig)

def fml.ren {n n' : RenCtx} (f : n ⟶ n') : fml m n -> fml m n'
| .pred p k => .pred p (fun i => (k i).ren f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.ren f) (ψ.ren f)
| .disj φ ψ => .disj (φ.ren f) (ψ.ren f)
| .infdisj φ => .infdisj (fun i => (φ i).ren f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).ren f)
| .eq t u => .eq (t.ren f) (u.ren f)
| .existsQ φ => .existsQ (φ.ren (lift f))

def fml.subst {n n' : Subst m} (f : n ⟶ n') : fml m n → fml m n'
| .pred p k => .pred p (fun i => (k i).subst f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.subst f) (ψ.subst f)
| .disj φ ψ => .disj (φ.subst f) (ψ.subst f)
| .infdisj φ => .infdisj (fun i => (φ i).subst f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).subst f)
| .eq t u => .eq (t.subst f) (u.subst f)
| .existsQ φ => .existsQ (φ.subst (lift_subst f))

theorem fml.ren_to_subst  (f : n ⟶ n') (φ: fml S n):
  (fml.ren f φ) = fml.subst (fun i => tm.var (f i)) φ := by
  induction φ generalizing n' with
  | pred p _ =>
    simp only [fml.ren, tm.ren_to_subst, fml.subst, fml.pred.injEq, heq_eq_eq, true_and];rfl
  | true => simp only [fml.ren, fml.subst]
  | false => simp only [fml.ren, fml.subst]
  | conj _ _ h1 h2 =>
    simp only [fml.ren, h1, h2, fml.subst]
  | disj _ _ h1 h2 =>
    simp only [fml.ren, h1, h2, fml.subst]
  | infdisj _ ih =>
    simp only [fml.ren, fml.subst, ih]
  | eq _ _ =>
    simp only [fml.ren, tm.ren_to_subst, fml.subst, fml.eq.injEq]
    exact ⟨by rfl, by rfl⟩
  | existsQ _ ih =>
    simp only [fml.ren, fml.subst, ih]
    congr
    funext i
    simp [lift_subst, _root_.lift]
    induction i using Fin.cases with
    | zero => simp
    | succ i =>
      simp only [Fin.cases_succ, Function.comp_apply, tm.ren]


open CategoryTheory

theorem fml.ren_id {n : RenCtx} (f : fml m n)
  : fml.ren (𝟙 n) f = f := by
  induction f with
  | pred => simp only [ren, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.ren_id]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [ren, conj.injEq,disj.injEq] ; constructor <;> simp only[ihφ, ihψ]
  | infdisj φ ih => rw [ren, infdisj.injEq] ; funext i ; exact ih _
  | eq t u => simp only [ren, tm.ren_id]
  | existsQ φ ih => rw [ren, lift_id, ih]

theorem fml.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  induction t generalizing n2 n3 with
  | pred => simp only [ren, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.ren_comp]
  | true | false => simp only [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [ren, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj φ ih => simp only [ren, infdisj.injEq] ; funext i ; exact ih _ _ _
  | eq t u => simp only [ren, tm.ren_comp]
  | existsQ φ ih => simp only [ren, lift_comp, ih]

theorem lift_subst_id (n : Subst m) : lift_subst (𝟙 n) = 𝟙 (n+1: Subst m) := by
  funext i ; simp only [lift_subst, CategoryStruct.id]
  induction i using Fin.cases <;> simp only [RelativeMonad.ret,Fin.cases_zero, Fin.cases_succ, Function.comp_apply,
    tm.ren]

theorem lift_subst_comp : lift_subst (f ≫ g) = lift_subst f ≫ lift_subst g := by
  funext i ; simp [lift_subst, CategoryStruct.comp]
  induction i using Fin.cases with
    | zero => simp only [RelativeMonad.bind, Fin.cases_zero, tm.subst, lift_subst]
    | succ i =>
      simp only [RelativeMonad.bind, Fin.cases_succ, Function.comp_apply, ← tm.subst_ren_comp, ←
        tm.ren_subst_comp]
      congr; ext x; simp only [CategoryStruct.comp, Function.comp_apply, lift_subst, Fin.cases_succ,
        tm.ren_map]
      rfl


theorem fml.subst_id {n : Subst m} (f : fml m n)
  : subst (𝟙 n) f = f := by
  induction f with
  | pred => simp only [subst, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.subst_id]
  --  ; simp [tm.subst_id]
  | true | false => simp only [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [subst, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj φ ih => simp only [subst, infdisj.injEq] ; funext i ; apply ih
  | eq t u => simp only [subst, tm.subst_id]
  | existsQ φ ih => simp only [subst, lift_subst_id, ih]

theorem fml.subst_comp {n1 n2 n3 : Subst m} (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  subst (f ≫ g) t = subst g (subst f t) := by
  induction t generalizing n2 n3 with
  | pred => simp only [subst, pred.injEq, heq_eq_eq, true_and] ; funext i ; simp only [tm.subst_comp]
  | true | false => simp only [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp only [subst, conj.injEq,disj.injEq] ; constructor <;> simp only [ihφ, ihψ]
  | infdisj φ ih => simp only [subst, infdisj.injEq] ; funext i ; exact ih _ _ _
  | eq t u => simp only [subst, tm.subst_comp]
  | existsQ φ ih => simp only [subst, lift_subst_comp, ih]

def Fml m : Subst m ⥤ Type where
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
  | infdisj_intro : proof Γ (φ k) → proof Γ (.infdisj φ)
  | infdisj_elim : proof Γ (.infdisj φ) →
    (forall k, proof (φ k :: Γ) ξ) → proof Γ ξ
  | eq_intro : proof Γ (.eq t t)
  | eq_elim (φ : (Fml _).obj _) (Γ : (Ctx _).obj _) : proof Δ (.eq t u) →
    proof (Δ ++ Γ[t..]) (φ[t..]) →
    proof (Δ ++ Γ[u..]) (φ[u..])
  | existsQ_intro (φ : (Fml _).obj _) : proof Γ (φ[t..]) → proof Γ (.existsQ φ)
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


def sequent.derivable (T : theory) (s : sequent T.sig) := proof [s.premise] s.concl

def sequent.of_formulas (Γ : FmlCtx T n) (φ : fml T.sig n) : sequent T.sig where
  ctx := n
  premise := List.foldr .conj .true Γ
  concl := φ

theorem sequent.from_proof : proof Γ φ -> (of_formulas Γ φ).derivable := by
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

theorem sequent.to_proof : (of_formulas Γ φ).derivable -> proof Γ φ := by
  intros hs ; apply proof.cut _ _ _ hs
  clear hs
  induction Γ with
  | nil => simp only [of_formulas, List.foldr_nil, List.mem_singleton, forall_eq] ; exact proof.true_intro
  | cons ψ Γ ih =>
    simp only [of_formulas, List.foldr_cons, List.mem_singleton, forall_eq] ; apply proof.conj_intro
    · apply proof.var ; simp only [List.mem_cons, true_or]
    · simp only [List.mem_singleton, forall_eq] at ih ; apply proof.cut _ _ _ ih
      intros ; apply proof.var; simp only [List.mem_cons] ; right ; assumption

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
    | infdisj_intro : proof (φ k) (.infdisj φ)
    | infdisj_elim : proof δ (.infdisj φ) →
      (forall k, proof (.conj (φ k) δ) ξ) → proof Γ ξ
    | eq_intro : proof .true (.eq t t)
    | eq_elim (φ γ : (Fml _).obj _) : proof δ (.eq t u) →
      proof (δ.conj (γ[t..])) (φ[t..]) →
      proof (δ.conj (γ[u..])) (φ[u..])
    | existsQ_intro (φ : (Fml _).obj _) : proof (φ[t..]) (.existsQ φ)
    | existsQ_elim : proof  phi (fml.ren Fin.succ psi) -> proof (.existsQ phi) psi
      --existsQ_elim : proof (fml.ren Fin.succ (.existsQ φ)) φ
    | ren : proof φ ψ -> proof (fml.ren ρ φ) (fml.ren ρ ψ)

  variable {T : theory}



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
end R

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

theorem fml.subst_conj {n n': RenCtx} (σ : Fin n -> tm m n') (φ ψ: fml m n) :
 fml.subst σ (fml.conj φ ψ) = fml.conj (fml.subst σ φ) (fml.subst σ ψ) := rfl

theorem fml.subst_conjn {k n n': RenCtx} (σ : Fin n -> tm m n') (fs: Fin k -> fml m n):
 fml.subst σ (fml.conjn fs) = fml.conjn (fun i => fml.subst σ (fs i)) := by
   induction k generalizing n with
   | zero =>
     simp only [fml.conjn,  Fin.foldr,
          Nat.zero_eq,Fin.foldr.loop,fml.subst]
   | succ n1 ih =>
     have := ih σ (fs ∘ Fin.succ)--(fun i => fs (Fin.castAdd 1 i))
     simp only[fml.conjn,fml.subst]
     simp only[Fin.foldr_succ]
     simp only [Nat.succ_eq_add_one, Function.comp_apply]
     simp only[fml.subst_conj]
     congr

theorem fml.subst_eq:
  fml.subst σ (fml.eq t1 t2) = fml.eq (tm.subst σ t1) (tm.subst σ t2) := rfl

theorem fml.subst_eqs :
  fml.subst σ (fml.eqs ts1 ts2) =
  fml.eqs (fun i => tm.subst σ (ts1 i)) (fun i => tm.subst σ (ts2 i)) := by
   simp only[fml.subst,fml.eqs]
   simp only[fml.subst_conjn,fml.subst_eq]



theorem Hilbert.proof.conjn  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (fs: Fin k → fml T.sig n) :
 (∀ (i: Fin k), Hilbert.proof φ (fs i)) → Hilbert.proof φ (fml.conjn fs) := by
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

theorem Hilbert.proof.eqs  {T: theory} {k : ℕ} {n : RenCtx} (φ: fml T.sig n) (ts1 ts2: Fin k → tm T.sig n):
 (∀ (i: Fin k), Hilbert.proof φ (fml.eq  (ts1 i) (ts2 i))) →
  Hilbert.proof φ (fml.eqs ts1 ts2) := by
  simp only[fml.eqs]
  intro h
  apply Hilbert.proof.conjn
  assumption

theorem Hilbert.any_eq_intro {T: theory} {n : RenCtx} (φ: fml T.sig n) (t: tm T.sig n):
 Hilbert.proof φ (.eq t t) := by
  apply @Hilbert.proof.cut _ _ _ .true
  · apply Hilbert.proof.true_intro
  · apply Hilbert.proof.eq_intro

theorem tm.substn_zero (ts:  0 ⟶  n') : (tm.subst (substn ts) t) = t := by
  induction t with
  | var a => simp only [tm.subst, substn, Nat.add_zero];rfl
  | op o σ ih =>
    simp only [tm.subst, substn]
    congr
    funext
    simp only [ih]

theorem fml.substn_zero (ts:  0 ⟶  n') : (fml.subst (substn ts) f) = f := by
  simp only[substn0]
  apply fml.subst_id


theorem Hilbert.eqs_elim {T: theory} {n' n : Subst T.sig}  (δ : fml T.sig n')  (φ γ: fml T.sig (n'+n)) (ts1 ts2:  n ⟶  n'):
 Hilbert.proof δ (.eqs ts1 ts2) →
 Hilbert.proof (δ.conj (.subst (substn ts1) γ)) (.subst (substn ts1) φ) →
 Hilbert.proof (δ.conj (.subst (substn ts2) γ)) (.subst (substn ts2) φ) := by
  induction n with
  | zero =>
    simp only[fml.substn_zero]
    intros h1 h2
    assumption
  | succ n ih =>
    intros h1 h2
    sorry


--  proof (δ.conj (γ[t..])) (φ[t..]) →
--       proof (δ.conj (γ[u..])) (φ[u..])

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
      #check Hilbert.proof.eq_elim
      · sorry
    unique := sorry


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
