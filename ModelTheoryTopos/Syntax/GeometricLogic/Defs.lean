
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
  obj := fml m
  map := fml.subst
  map_id := by intros ; funext t ; simp [fml.subst_id]
  map_comp := by intros ; funext t ; simp [fml.subst_comp]

-- def fml.subst_fst (t : (Fml m).obj (n+1)) (a : tm m n) : fml m n :=
--   t[a..]

def ListFunctor : Type ⥤ Type where
  obj := List
  map := List.map

def Ctx m [SmallUniverse]: Subst m ⥤ Type := Fml m ⋙ ListFunctor


-- Is there a way to make Ctx transparent enough for typeclass search ?
instance [SmallUniverse]: HAppend (List (fml m n)) ((Ctx m).obj n) (List (fml m n)) where
  hAppend := fun l l' => let l'' : List (fml m n) := l' ; l ++ l''

abbrev FmlCtx [SmallUniverse] (T : theory) n := List (fml T.sig n)

instance [SmallUniverse] {T : theory}: ScopedSubstitution (tm T.sig) (FmlCtx T) where
  ssubst σ t := (Ctx T.sig).map σ t
