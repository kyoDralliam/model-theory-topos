import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Category.RelativeMonad

structure monosig where
  ops : Type
  arity_ops : ops -> Nat
  preds : Type
  arity_preds : preds -> Nat

-- terms with n variables on the signature m
inductive tm (m : monosig) (n : Nat) where
  | var : Fin n -> tm m n     -- x1, .. xn ⊢ xk     k ∈ Fin n
  | op : (o : m.ops) -> (Fin (m.arity_ops o) -> tm m n) -> tm m n
    -- σ ∈ m.ops   x1, .. xn ⊢ t1,.., tj      x1, .. xn ⊢ σ(t1, .., tj)    arity(σ) = j

abbrev RenCtx := Nat

open CategoryTheory

instance CategoryTheory.RenCat : Category RenCtx where
  Hom n1 n2 := Fin n1 -> Fin n2
  id := fun _ x => x
  comp := fun f g => g ∘ f

-- TODO: there's probably a name for that def in Fin
def lift {n n' : RenCtx} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

theorem lift_id : lift (𝟙 n) = 𝟙 (n+1) := by
  funext i ; simp [lift, CategoryStruct.id]
  induction i using Fin.cases <;> simp

theorem lift_comp : lift (f ≫ g) = lift f ≫ lift g := by
  funext i ; simp [lift, CategoryStruct.comp]
  induction i using Fin.cases <;> simp

def tm.ren {n n' : RenCtx} (f : n ⟶ n') : tm m n -> tm m n'
| .var i => .var (f i)
| .op o k => .op o (fun i => (k i).ren f)


theorem tm.ren_id {n : RenCtx} (t : tm m n)
  : tm.ren (𝟙 n) t = t := by
  induction t with
  | var => simp [tm.ren, CategoryStruct.id]
  | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]

theorem tm.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  induction t with
  | var => simp [tm.ren, CategoryStruct.comp]
  | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]

def tm.subst {n n' : RenCtx} (f : Fin n → tm m n') : tm m n → tm m n'
  | .var x => f x
  | .op o k => .op o (fun i => (k i).subst f)

instance emb : RenCtx ⥤ Type where
  obj := Fin
  map := id

-- relative monad structure of terms over emb

instance tm.substitution : RelativeMonad emb (tm m) where
  ret := fun n i => .var i
  bind := fun f t => t.subst f
  lunit := by intros ; simp []; funext t ; induction t with
    | var => simp [subst]
    | op _ _ ih => simp [subst] ; funext i ; simp [ih]
  runit := by intros ; funext i ; simp [CategoryStruct.comp, subst]
  assoc := by intros ; simp []; funext t ; induction t with
    | var => simp [subst]
    | op _ _ ih => simp [subst] ; funext i ; simp [ih]


-- Category of contexts (natural numbers) and substitutions (maps Fin k -> tm m n)
abbrev Subst m := (tm.substitution (m:=m)).kl

-- it would have probably been simpler to do the proof directly..
theorem tm.subst_id (n : Subst m) (t : tm m n) : t.subst (𝟙 n) = t := by
  calc
    subst (𝟙 n) t = tm.substitution.bind (tm.substitution.ret _) t := by simp [tm.substitution, CategoryStruct.id]
    _ = t := by simp [tm.substitution.lunit]

theorem tm.subst_comp (n1 n2 n3 : Subst m) (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1)
  : t.subst (f ≫ g) = (t.subst f).subst g := by
  calc
    subst (f ≫ g) t = tm.substitution.bind (f ≫ tm.substitution.bind g) t := by simp [tm.substitution, CategoryStruct.comp]
   _ = subst g (subst f t) := by simp [tm.substitution.assoc]; simp [tm.substitution]


def subst_fst {m} {H : Subst m ⥤ Type} (t : H.obj (n+1)) (a : tm m n) : H.obj n :=
  H.map (Fin.cases a (tm.substitution.ret _)) t

-- TODO: introduce a proper namespace for substitutions
-- and define the other usual combinators
notation t "[" a ".." "]" => (subst_fst t a)


abbrev Tm (m : monosig) := RelativeMonad.kleisli.forgetful (tm.substitution (m:=m))

instance : OfNat (Subst m) n where
  ofNat := tm.substitution.to_kl n

instance : HAdd (Subst m) Nat (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + l)

namespace Example
-- a simple signature with a nullary operation and a binary operation
def magma : monosig where
  ops := Bool
  arity_ops := fun b => if b then 0 else 2
  preds := Empty
  arity_preds := Empty.elim


def v0 : (Tm magma).obj 1 := .var (0 : Fin 1)
def ε : (Tm magma).obj n := .op true Fin.elim0
def mult (t u : (Tm magma).obj n) : (Tm magma).obj n :=
  .op false (fun i : Fin 2 => [ t , u ][i])

#check v0[ε..]

-- Oups...
#reduce (mult v0 (mult v0 v0))[ε..]

end Example


