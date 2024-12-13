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


instance terms (m : monosig) : RenCtx ⥤ Type where
  obj := tm m
  map := tm.ren
  map_id := by
    intros n ; simp ; funext t ; apply tm.ren_id
  map_comp := by
    intros ; simp ; funext t ; apply tm.ren_comp

def tm.subst : tm m n → (Fin n → tm m n') → tm m n'
  | .var x, f => f x
  | .op o k, f => .op o (fun i => (k i).subst f)





instance emb : RenCtx ⥤ Type where
  obj := Fin
  map := id

-- relative monad structure of terms over emb

class relativeMonad {C D} [Category C] [Category D] (ι : C ⥤ D) (F : C ⥤ D) where
  ret : (x : C) → ι.obj x ⟶ F.obj x
  bind : {x y : C} → (ι.obj x ⟶ F.obj y) → (F.obj x ⟶ F.obj y)
  lunit : forall x, bind (ret x) = 𝟙 _
  runit : forall {x y} (f : ι.obj x ⟶ F.obj y), ret _ ≫ bind f = f
  assoc : forall {x y z}
    (f : ι.obj x ⟶ F.obj y) (g : ι.obj y ⟶ F.obj z),
    bind (f ≫ bind g) = bind f ≫ bind g
  map : forall {x y} (f : x ⟶ y), F.map f = bind (ι.map f ≫ ret _)

namespace relativeMonad
  variable {C D} [Category C] [Category D] (ι : C ⥤ D) (F : C ⥤ D) (r : relativeMonad ι F)
-- TODO: link with the standard defs of naturality
theorem ret_natural {x y} (f : x ⟶ y) :
  ι.map f ≫ r.ret _ = r.ret _ ≫ F.map f := by
  rw [r.map, r.runit]

theorem bind_natural {x x' y y'} (f : x' ⟶ x) (g : ι.obj x ⟶ F.obj y) (h : y ⟶ y') :
  r.bind (ι.map f ≫ g ≫ F.map h) = F.map f ≫ r.bind g ≫ F.map h := by
  rw [r.map,r.map, <-Category.assoc, r.assoc,
    <-Category.assoc, <-(r.assoc _ g), Category.assoc, r.runit]
end relativeMonad


instance tm.substitution : relativeMonad emb (terms m) where
  ret := fun n i => .var i
  bind := fun f t => t.subst f
  lunit := by intros ; simp [terms]; funext t ; induction t with
    | var => simp [subst]
    | op _ _ ih => simp [subst] ; funext i ; simp [ih]
  runit := by intros ; funext i ; simp [CategoryStruct.comp, subst]
  assoc := by intros ; simp [terms]; funext t ; induction t with
    | var => simp [subst]
    | op _ _ ih => simp [subst] ; funext i ; simp [ih]
  map := by intros ; funext t ; induction t with
    | var => simp [subst, terms, ren, emb]
    | op _ _ ih => simp [subst, terms, ren] ; funext i ; apply ih i


namespace Example

-- def subst_fst [r: relativeMonad emb F] (a : F.obj n) : Fin (n + 1) → F.obj n := Fin.cases a (r.ret _)
def subst_fst [r: relativeMonad emb F] (t : F.obj (n+1)) (a : F.obj n) : F.obj n :=
  r.bind (Fin.cases a (r.ret _)) t


-- TODO: introduce a proper namespace for substitutions
-- and define the other usual combinators
notation t "[" a ".." "]" => (subst_fst t a)


-- a simple signature with a nullary operation and a binary operation
def magma : monosig where
  ops := Bool
  arity_ops := fun b => if b then 0 else 2
  preds := Empty
  arity_preds := Empty.elim

def v0 : (terms magma).obj 1 := .var 0
def ε : (terms magma).obj n := .op true Fin.elim0
def mult (t u : (terms magma).obj n) : (terms magma).obj n :=
  .op false (fun i : Fin 2 => [ t , u ][i])

#check v0[ε..]

-- Oups...
#reduce (mult v0 (mult v0 v0))[ε..]

end Example


