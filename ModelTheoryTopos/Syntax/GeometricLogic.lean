import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
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

def lift_subst (f : Fin n → tm m n') : Fin (n+1) → tm m (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

def fml.subst {n n' : RenCtx} (f : Fin n ⟶  tm m n') : fml m n -> fml m n'
| .pred p k => .pred p (fun i => (k i).subst f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.subst f) (ψ.subst f)
| .disj φ ψ => .disj (φ.subst f) (ψ.subst f)
| .infdisj φ => .infdisj (fun i => (φ i).subst f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).subst f)
| .eq t u => .eq (t.subst f) (u.subst f)
| .existsQ φ => .existsQ (φ.subst (lift_subst f))


def fml.subst_fst (t : fml m (n+1)) (a : tm m n) : fml m n :=
  subst (Fin.cases a .var) t

def ctx_subst_fst (Γ : List (fml m (n+1))) (a : tm m n) : List (fml m n) :=
  List.map (fun φ => φ.subst_fst a) Γ

open CategoryTheory


theorem fml.ren_id {n : RenCtx} (f : fml m n)
  : fml.ren (𝟙 n) f = f := by
  induction f with
  | pred => simp [ren] ; funext i ; simp [tm.ren_id]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [ren] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [ren] ; funext i ; apply ih
  | eq t u => simp [ren, tm.ren_id]
  | existsQ φ ih => simp [ren, lift_id, ih]

theorem fml.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  induction t generalizing n2 n3 with
  | pred => simp [ren] ; funext i ; simp [tm.ren_comp]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [ren] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [ren] ; funext i ; apply ih
  | eq t u => simp [ren, tm.ren_comp]
  | existsQ φ ih => simp [ren, lift_comp, ih]


instance formulas (m : monosig) : RenCtx ⥤ Type where
  obj := fml m
  map := fml.ren
  map_id := by
    intros n ; simp ; funext t ; apply fml.ren_id
  map_comp := by
    intros ; simp ; funext t ; apply fml.ren_comp



-- TODO : syntactic proofs for geometric logic

inductive proof : {n : RenCtx} → List (fml m n) → fml m n → Type where
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
  | infdisj_intro : proof Γ (φ n) → proof Γ (.infdisj φ)
  | infdisj_elim : proof Γ (.infdisj φ) →
    (forall n, proof (φ n :: Γ) ξ) → proof Γ ξ
  | eq_intro : proof Γ (.eq t t)
  | eq_elim (φ : fml _ _) : proof Δ (.eq t u) →
    proof (Δ ++ ctx_subst_fst Γ t) (φ.subst_fst t) →
    proof (Δ ++ ctx_subst_fst Γ u) (φ.subst_fst u)
  | existsQ_intro : proof Γ (φ.subst_fst t) → proof Γ (.existsQ φ)
  | existsQ_elim : proof Γ (.existsQ φ) →
    proof (List.map (fml.ren Fin.succ) Γ) φ
