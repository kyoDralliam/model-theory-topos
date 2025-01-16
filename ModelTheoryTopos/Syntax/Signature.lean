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
  funext i ; simp only [lift, CategoryStruct.id]
  induction i using Fin.cases <;> simp?

theorem lift_comp : lift (f ≫ g) = lift f ≫ lift g := by
  funext i ; simp [lift, CategoryStruct.comp]
  induction i using Fin.cases <;> simp?

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
  lunit := by intros ; simp only; funext t ; induction t with
    | var => rw [subst, types_id_apply]
    | op _ _ ih => simp only [subst, types_id_apply, op.injEq, heq_eq_eq, true_and] ; funext i ; rw [ih,
      types_id_apply]
  runit := by intros ; funext i ; simp only [CategoryStruct.comp, Function.comp_apply, subst]
  assoc := by intros ; simp only; funext t ; induction t with
    | var => simp only [subst, types_comp_apply]
    | op _ _ ih => simp only [subst, types_comp_apply, op.injEq, heq_eq_eq, true_and] ; funext i ; rw [ih,
      types_comp_apply]

theorem tm.ren_map {n1 n2 : RenCtx} (f : n1 ⟶ n2) (t : tm m n1) : tm.ren f t = tm.substitution.functor.map f t :=
  by induction t with
    | var => simp only [ren, emb, RelativeMonad.functor, id_eq, RelativeMonad.ret,
      RelativeMonad.bind, subst, types_comp_apply]
    | op _ _ ih =>
      simp only [ren, emb, RelativeMonad.functor, id_eq, RelativeMonad.ret, RelativeMonad.bind,
        subst, op.injEq, heq_eq_eq, true_and]
      funext i ; exact ih i

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
    _ = t := by rw [tm.substitution.lunit, types_id_apply]

theorem tm.subst_comp (n1 n2 n3 : Subst m) (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1)
  : t.subst (f ≫ g) = (t.subst f).subst g := by
  calc
    subst (f ≫ g) t = tm.substitution.bind (f ≫ tm.substitution.bind g) t := by simp [tm.substitution, CategoryStruct.comp]
   _ = subst g (subst f t) := by simp only [tm.substitution.assoc, types_comp_apply]; simp only [substitution]

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
    _ = subst g (ren f t) := by rw [subst_map, ren_map]; simp only [CategoryStruct.comp,
      RelativeMonad.functor_eq, Function.comp_apply]


theorem tm.subst_ren_comp {n2 : Subst m} (f : n1 ⟶ n2) (g : Fin n2 ⟶ Fin n3) (t : tm m n1):
  subst (f ≫ (tm.substitution.ret _ ∘ g)) t = ren g (subst f t) := by
  have := RelativeMonad.bind_natural_r tm.substitution f g
  calc
    subst (f ≫ (tm.substitution.ret _ ∘ g)) t = (substitution.bind (f ≫ substitution.functor.map g)) t := rfl
    _ = (substitution.bind f ≫ substitution.functor.map g) t:= by rw [this]
    _ = ren g (subst f t) := by rw [ren_map, subst_map]; simp only [RelativeMonad.functor_eq,
      CategoryStruct.comp, Function.comp_apply]



instance : OfNat (Subst m) n where
  ofNat := tm.substitution.to_kl n

instance : HAdd (Subst m) Nat (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + l)

instance : HAdd  Nat (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (k + tm.substitution.from_kl l)

instance : HAdd  (Subst m) (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + tm.substitution.from_kl l)


namespace Fin
/-- `castAdd m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAdd` and `Fin.addNat`. -/
@[inline] def castAdd' (n) : Fin m → Fin (n + m) :=
  castLE <| Nat.le_add_left m n

@[simp] theorem castAdd'_castLT (n : Nat) (i : Fin (n + m)) (hi : i.val < m) :
    castAdd' n (castLT i hi) = i := rfl

@[simp] theorem coe_castAdd' (m : Nat) (i : Fin n) : (castAdd' m i : Nat) = i := rfl

theorem castAdd'_lt {m : Nat} (n : Nat) (i : Fin m) : (castAdd' n i : Nat) < m := by simp only [coe_castAdd',
  is_lt]

@[elab_as_elim] def casesAdd {m n : Nat} {motive : Fin (m + n) → Sort u}
    (left : ∀ i : Fin m, motive (addNat i n)) (right : ∀ i : Fin n, motive (castAdd' m i))
    (i : Fin (m + n)) : motive i :=
  if hi : (i : Nat) < n then (castAdd'_castLT m i hi) ▸ (right (castLT i hi))
  else (addNat_subNat (Nat.le_of_not_lt hi)) ▸ (left _)

@[simp] theorem casesAdd_left {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin m) :
    casesAdd (motive := motive) left right (addNat i n) = left i := by
  have : ¬(addNat i n : Nat) < n := Nat.not_lt.2 (le_coe_addNat ..)
  rw [casesAdd, dif_neg this]; exact eq_of_heq <| (eqRec_heq _ _).trans (by congr 1; simp)

@[simp]
theorem casesAdd_right {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin n) :
    casesAdd (motive := motive) left right (castAdd' m i) = right i := by
  rw [casesAdd, dif_pos (castAdd'_lt _ _)]; rfl

-- @[simp] theorem casesAdd_left_le {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin (m + n)) (h : n ≤ i) :
--     casesAdd (motive := motive) left right i = left i := by
--   have : ¬(addNat i n : Nat) < n := Nat.not_lt.2 (le_coe_addNat ..)
--   rw [casesAdd, dif_neg this]; exact eq_of_heq <| (eqRec_heq _ _).trans (by congr 1; simp)

end Fin

def subst0 {m} {n : Subst m} (a : tm m n) : (n+1) ⟶ n :=
  Fin.cases a (tm.substitution.ret _)

def substn {m} {n n' : Subst m} (σ : n ⟶ n') : (n'+n) ⟶ n' :=
  Fin.casesAdd (tm.substitution.ret _) σ

-- def substn {m} {n n' : Subst m} (σ : n ⟶ n') : (n+n') ⟶ n' :=
--   Fin.addCases σ (tm.substitution.ret _)

def lift_subst {n n' : Subst m} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

def liftn_subst {n: Nat} {k k' : Subst m} (f : k ⟶ k') : (k+n) ⟶ (k'+n) :=
  Fin.casesAdd
    (tm.ren (fun i ↦ Fin.addNat i n) ∘ f)
    (fun i ↦ .var (i.castAdd' k'))

-- def liftn_subst {n: Nat} {k k' : Subst m} (f : k ⟶ k') : (n+k) ⟶ (n+k') :=
--   Fin.addCases
--     (fun i ↦ .var (i.castAdd k'))
--     (tm.ren (Fin.natAdd n) ∘ f)

theorem tm.subst_id_ext {n : Subst m} (f : n ⟶ n) (t : tm m n) : f = 𝟙 n → t.subst f = t := by
  rintro rfl
  rw [subst_id]


theorem subst0_lift_subst {n n' : Subst m} (a : tm m n) (σ : n ⟶ n') :
  subst0 a ≫ σ = lift_subst σ ≫ subst0 (a.subst σ) := by
  funext x
  induction x using Fin.cases
  · simp only [CategoryStruct.comp, RelativeMonad.bind, Function.comp_apply, subst0,
    Fin.cases_zero, tm.subst]
  · simp only [CategoryStruct.comp, RelativeMonad.bind, Function.comp_apply, tm.subst, Fin.eta,
    lift_subst, Fin.cases_succ, ← tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext
    funext y
    simp only [Function.comp_apply, subst0, Fin.cases_succ]
    rfl

theorem lift_subst_subst0 {n n' : Subst m} (σ : (n+1) ⟶ n') :
  lift_subst (σ ∘ Fin.succ) ≫ subst0 (σ (0 : Fin (n+1))) = σ := by
  funext i
  induction i using Fin.cases
  · simp only [tm.subst_comp_app, tm.subst, subst0, Fin.cases_zero]
  · simp only [tm.subst_comp_app, lift_subst, Fin.cases_succ, Function.comp_apply, ←
    tm.ren_subst_comp]
    apply tm.subst_id_ext
    funext y
    rfl


theorem substn_liftn_subst {n k k' : Subst m} (σ : n ⟶ k) (f : k ⟶ k') :
  substn σ ≫ f = liftn_subst f ≫ substn (σ ≫ f) := by
  funext i
  induction i using Fin.casesAdd
  · simp only [tm.subst_comp_app, substn, Fin.casesAdd_left, tm.subst, liftn_subst,
    Function.comp_apply, ← tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext
    funext y
    rw [Function.comp_apply, substn, Fin.casesAdd_left]
    rfl
  · simp only [tm.subst_comp_app, substn, Fin.casesAdd_right, liftn_subst, tm.subst]

theorem substn0 (σ : 0 ⟶ k) : substn σ = 𝟙 k := by
  funext i
  rw [substn, <-Fin.addNat_zero _ i, Fin.casesAdd_left, Fin.addNat_zero]
  rfl

theorem substn_at0 (σ : (n+1) ⟶ k) : substn σ (0 : Fin (k + n + 1)) = σ (0 : Fin (n+1)) := by
  have : (0 : Fin (k + n + 1)) = Fin.castAdd' k (0 : Fin (n+1)) := rfl
  rw [this, substn, Fin.casesAdd_right]


theorem substn_atsucc (σ : (n+1) ⟶ k) : substn (σ ∘ Fin.succ) = substn σ ∘ Fin.succ := by
  funext i
  induction i using Fin.casesAdd with
  | left i =>
    simp only [substn, Fin.casesAdd_left, Nat.add_eq, Function.comp_apply]
    have : (i.addNat n).succ = i.addNat (n+1) := by ext ; simp only [Fin.val_succ, Fin.coe_addNat,
      Nat.add_assoc]
    rw [this, Fin.casesAdd_left]
  | right i =>
    simp only [substn, Fin.casesAdd_right, Function.comp_apply, Nat.add_eq]
    have : (Fin.castAdd' k i).succ = Fin.castAdd' k i.succ := by ext ; simp only [Fin.val_succ,
      Fin.coe_castAdd']
    rw [this, Fin.casesAdd_right]

theorem substnsucc (σ : (n+1) ⟶ k) :
  substn σ = lift_subst (substn (σ ∘ Fin.succ)) ≫ subst0 (σ (0 : Fin (n+1))) := by
  rw [<-(lift_subst_subst0 (substn σ : ((k+n)+1) ⟶ k)), substn_atsucc, substn_at0]

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
