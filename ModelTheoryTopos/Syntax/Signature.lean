import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types

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

instance CategoryTheory.RenCat : Category RenCtx where
  Hom n1 n2 := Fin n1 -> Fin n2
  id := fun _ x => x
  comp := fun f g => g ∘ f


-- TODO: there's probably a name for that def in Fin
def lift {n n' : RenCtx} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

def tm.ren {n n' : RenCtx} (f : n ⟶ n') : tm m n -> tm m n'
| .var i => .var (f i)
| .op o k => .op o (fun i => (k i).ren f)

open CategoryTheory

instance terms (m : monosig) : RenCtx ⥤ Type where
  obj := tm m
  map := tm.ren
  map_id := by
    intros n ; simp ; funext t
    induction t with
    | var => simp [tm.ren, CategoryStruct.id]
    | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]
  map_comp := by
    intros ; simp ; funext t
    induction t with
    | var => simp [tm.ren, CategoryStruct.comp]
    | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]
