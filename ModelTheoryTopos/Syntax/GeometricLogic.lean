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

def lift_subst {n n' : Subst m} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

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

theorem lift_subst_id (n : Subst m) : lift_subst (𝟙 n) = 𝟙 (n+1: Subst m) := by
  funext i ; simp [lift_subst, CategoryStruct.id]
  induction i using Fin.cases <;> simp [RelativeMonad.ret, tm.ren]

theorem lift_subst_comp : lift_subst (f ≫ g) = lift_subst f ≫ lift_subst g := by
  funext i ; simp [lift_subst, CategoryStruct.comp]
  induction i using Fin.cases with
    | zero => simp [RelativeMonad.bind, tm.subst, lift_subst]
    | succ i =>
      simp [RelativeMonad.bind, <-tm.ren_subst_comp, <-tm.subst_ren_comp]
      congr; ext x; simp [CategoryStruct.comp, tm.ren_map, lift_subst]
      rfl


theorem fml.subst_id {n : Subst m} (f : fml m n)
  : subst (𝟙 n) f = f := by
  induction f with
  | pred => simp [subst] ; funext i ; simp [tm.subst_id]
  --  ; simp [tm.subst_id]
  | true | false => simp [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [subst] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [subst] ; funext i ; apply ih
  | eq t u => simp [subst, tm.subst_id]
  | existsQ φ ih => simp [subst, lift_subst_id, ih]

theorem fml.subst_comp {n1 n2 n3 : Subst m} (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  subst (f ≫ g) t = subst g (subst f t) := by
  induction t generalizing n2 n3 with
  | pred => simp [subst] ; funext i ; simp [tm.subst_comp]
  | true | false => simp [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [subst] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [subst] ; funext i ; apply ih
  | eq t u => simp [subst, tm.subst_comp]
  | existsQ φ ih => simp [subst, lift_subst_comp, ih]

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
  | eq_elim (φ : (Fml _).obj _) (Γ : (Ctx m).obj _) : proof Δ (.eq t u) →
    proof (Δ ++ Γ[t..]) (φ[t..]) →
    proof (Δ ++ Γ[u..]) (φ[u..])
  | existsQ_intro (φ : (Fml _).obj _) : proof Γ (φ[t..]) → proof Γ (.existsQ φ)
  | existsQ_elim : proof Γ (.existsQ φ) →
    proof (List.map (fml.ren Fin.succ) Γ) φ




namespace Miscellaneous

-- just to show how to use
def weaken_fml_for_functional_prop1 (φ : fml m (n1 + n2)) : fml m (n1 + n1 + n2) :=
  φ.ren (Fin.addCases (Fin.castAdd n2 ∘ Fin.castAdd n1) (Fin.natAdd (n1+n1)))

def weaken_fml_for_functional_prop2 (φ : fml m (n1 + n2)) : fml m (n1 + n1 + n2) :=
  φ.ren (Fin.addCases (Fin.castAdd n2 ∘ Fin.natAdd n1) (Fin.natAdd (n1+n1)))

end Miscellaneous