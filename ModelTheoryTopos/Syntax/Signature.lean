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


-- theorem tm.ren_id {n : RenCtx} (t : tm m n)
--   : tm.ren (𝟙 n) t = t := by
--   induction t with
--   | var => simp [tm.ren, CategoryStruct.id]
--   | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]

-- theorem tm.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1):
--   ren (f ≫ g) t = ren g (ren f t) := by
--   induction t with
--   | var => simp [tm.ren, CategoryStruct.comp]
--   | op _ _ ih => simp [tm.ren] ; funext i ; simp [ih]

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

theorem tm.ren_map {n1 n2 : RenCtx} (f : n1 ⟶ n2) (t : tm m n1) : tm.ren f t = tm.substitution.functor.map f t :=
  by induction t with
    | var => simp [RelativeMonad.functor, RelativeMonad.bind, subst, ren, RelativeMonad.ret, emb]
    | op _ _ ih =>
      simp [RelativeMonad.functor, RelativeMonad.bind, subst, ren, RelativeMonad.ret, emb]
      funext i ; apply ih i

abbrev Subst m := (tm.substitution (m:=m)).kl

theorem tm.subst_comp_app {x y z : Subst m} (f : x ⟶ y) (g : y ⟶ z) (i : Fin x) : (f ≫ g) i = (f i).subst g :=
  rfl

theorem tm.subst_id_app {x : Subst m}  (i : Fin x) : (𝟙 x) i = .var i :=
  rfl

theorem tm.subst_map {n n' : Subst m} (f : n ⟶ n') (t : tm m n) :
  t.subst f = tm.substitution.bind f t := rfl

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

theorem tm.ren_id {n : RenCtx} (t : tm m n)
  : tm.ren (𝟙 n) t = t := by
  rw [ren_map, substitution.functor.map_id]
  rfl

theorem tm.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  rw [ren_map, substitution.functor.map_comp, ren_map, ren_map]
  rfl

theorem tm.ren_subst_comp {n2 : Subst m} (f : Fin n1 ⟶ Fin n2) (g : n2 ⟶ n3) (t : tm m n1):
  subst (g ∘ f) t = subst g (ren f t) := by
  have := RelativeMonad.bind_natural_l tm.substitution f g
  calc
    subst (g ∘ f) t = tm.substitution.bind (emb.map f ≫ g) t := rfl
    _ = (substitution.functor.map f ≫ tm.substitution.bind g) t := by rw [this]
    _ = subst g (ren f t) := by rw [subst_map, ren_map]; simp [CategoryStruct.comp]


theorem tm.subst_ren_comp {n2 : Subst m} (f : n1 ⟶ n2) (g : Fin n2 ⟶ Fin n3) (t : tm m n1):
  subst (f ≫ (tm.substitution.ret _ ∘ g)) t = ren g (subst f t) := by
  have := RelativeMonad.bind_natural_r tm.substitution f g
  calc
    subst (f ≫ (tm.substitution.ret _ ∘ g)) t = (substitution.bind (f ≫ substitution.functor.map g)) t := rfl
    _ = (substitution.bind f ≫ substitution.functor.map g) t:= by rw [this]
    _ = ren g (subst f t) := by rw [ren_map, subst_map]; simp [CategoryStruct.comp]



instance : OfNat (Subst m) n where
  ofNat := tm.substitution.to_kl n

instance : HAdd (Subst m) Nat (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + l)

instance : HAdd  Nat (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (k + tm.substitution.from_kl l)

instance : HAdd  (Subst m) (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + tm.substitution.from_kl l)


def subst0 {m} {n : Subst m} (a : tm m n) : (n+1) ⟶ n :=
  Fin.cases a (tm.substitution.ret _)

def substn {m} {n n' : Subst m} (σ : n ⟶ n') : (n+n') ⟶ n' :=
  Fin.addCases σ (tm.substitution.ret _)

def lift_subst {n n' : Subst m} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

def liftn_subst {n: Nat} {k k' : Subst m} (f : k ⟶ k') : (n+k) ⟶ (n+k') :=
  Fin.addCases
    (fun i ↦ .var (i.castAdd k'))
    (tm.ren (Fin.natAdd n) ∘ f)

theorem tm.subst_id_ext {n : Subst m} (f : n ⟶ n) (t : tm m n) : f = 𝟙 n → t.subst f = t := by
  rintro rfl
  simp [subst_id]


theorem subst0_lift_subst {n n' : Subst m} (a : tm m n) (σ : n ⟶ n') :
  subst0 a ≫ σ = lift_subst σ ≫ subst0 (a.subst σ) := by
  funext x
  induction x using Fin.cases
  · simp [CategoryStruct.comp, subst0, lift_subst, RelativeMonad.bind, tm.subst]
  · simp [CategoryStruct.comp, subst0, lift_subst, RelativeMonad.bind,
    <-tm.ren_subst_comp, RelativeMonad.ret, tm.subst]
    symm ; apply tm.subst_id_ext
    funext y
    simp [subst0]
    rfl


theorem substn_liftn_subst {n k k' : Subst m} (σ : n ⟶ k) (f : k ⟶ k') :
  substn σ ≫ f = liftn_subst f ≫ substn (σ ≫ f) := by
  funext i
  induction i using Fin.addCases
  · simp [tm.subst_comp_app, substn, liftn_subst, tm.subst]
  · simp [tm.subst_comp_app, substn, tm.subst, liftn_subst, <-tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext
    funext y
    simp [substn]
    rfl


def subst_fst {m} {H : Subst m ⥤ Type} (t : H.obj (n+1)) (a : tm m n) : H.obj n :=
  H.map (subst0 a) t

-- TODO: introduce a proper namespace for substitutions
-- and define the other usual combinators
notation t "[" a ".." "]" => (subst_fst t a)


abbrev Tm (m : monosig) := RelativeMonad.kleisli.forgetful (tm.substitution (m:=m))

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


