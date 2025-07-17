import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Misc
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
def lift₁ {n n' : RenCtx} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

theorem lift₁_id : lift₁ (𝟙 n) = 𝟙 (n+1) := by
  funext i ; simp only [lift₁, CategoryStruct.id]
  induction i using Fin.cases <;> simp?

theorem lift₁_comp : lift₁ (f ≫ g) = lift₁ f ≫ lift₁ g := by
  funext i ; simp [lift₁, CategoryStruct.comp]
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
  lunit := by intros ; funext t ; induction t with
    | var => rw [subst, types_id_apply]
    | op _ _ ih => simp only [subst, types_id_apply, op.injEq, heq_eq_eq, true_and] ; funext i ; rw [ih,
      types_id_apply]
  runit := by intros ; funext i ; simp only [CategoryStruct.comp, Function.comp_apply, subst]
  assoc := by intros ; funext t ; induction t with
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

theorem tm.ret_var m (n : Subst m) : (tm.substitution (m:=m)).ret n = tm.var := rfl

theorem tm.ren_to_subst {n n' : RenCtx} (f : n ⟶ n') (t : tm m n) :
  t.ren f = t.subst (tm.var ∘ f) := by
  rw [tm.ren_map, tm.subst_map]
  rfl

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

theorem tm.subst_id_ext {n : Subst m} (f : n ⟶ n) (t : tm m n) : f = 𝟙 n → t.subst f = t := by
  rintro rfl
  simp [subst_id]

theorem tm.subst_id_ext' {n : Subst m} (f : n ⟶ n) (t : tm m n)
  (h : forall i : Fin n, f i = .var i) :
  t.subst f = t := by
  apply tm.subst_id_ext ; funext i; apply h

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

def substn {m} {n n' : Subst m} (σ : n ⟶ n') : (n'+n) ⟶ n' :=
  Fin.casesAdd (tm.substitution.ret _) σ

class ScopedSubstitution (T : Nat -> Type u) (F : Nat -> Type v) where
  ssubst : forall {k n : Nat} (_σ : Fin k → T n), F k -> F n

-- instance substGetElem (T : Nat -> Type u) (F : Nat -> Type v) [ScopedSubstitution T F] {k n : Nat} :
--   GetElem (F k) ( Fin k → T n) (F n) (fun _ _ => True) where
--   getElem t σ _ := ScopedSubstitution.ssubst σ t

notation t "⟪" σ "⟫" => (ScopedSubstitution.ssubst σ t)

instance append_substitutions {k n m : Subst S} : HAppend (k ⟶ m) (n ⟶ m) (k + n ⟶ m) where
  hAppend σ τ := Fin.casesAdd σ τ

abbrev scons {k n : Subst S} (a : tm S n) (σ : k ⟶ n) : (k+1) ⟶ n :=
  Fin.cases a σ

infix:50 " ∷ " => scons
-- infix:50 " ⇑ " => scons


instance : ScopedSubstitution (tm S) (tm S) where
  ssubst σ t := tm.subst σ t

theorem subst0_substn {n : Subst m} (a : tm m n) :
  subst0 a = substn (fun _ => a) := by
  funext x ; induction x using Fin.cases <;>
    simp only [subst0, Fin.cases_zero, Fin.cases_succ, substn] <;> rfl

theorem subst0_substn' {n : Subst m} (σ : 1 ⟶ n) (a : tm m n) (h : a = σ (0 : Fin 1)) :
  subst0 a = substn σ := by
  have : σ = (fun _ => a) := by
    funext i ; simp [emb] at i
    rw [Fin.fin_one_eq_zero i] ; symm; assumption
  subst this ; apply subst0_substn

theorem substn_left {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n'):
  substn σ (Fin.addNat a n) = .var a := by
   simp only [substn, Fin.casesAdd_left]
   rfl

theorem substn_right {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n):
  substn σ (Fin.castAdd' n' a ) = σ a := by
   simp only [substn, Fin.casesAdd_right]


def lift_subst {n n' : Subst m} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

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


def liftn_subst {n: Nat} {k k' : Subst m} (f : k ⟶ k') : (k+n) ⟶ (k'+n) :=
  Fin.casesAdd
    (tm.ren (fun i ↦ Fin.addNat i n) ∘ f)
    (fun i ↦ .var (i.castAdd' k'))

abbrev lift  (n: Nat) {k k' : Subst m} (f : k ⟶ k') := liftn_subst (n:=n) f

theorem subst0_lift_subst {n n' : Subst m} (a : tm m n) (σ : n ⟶ n') :
  subst0 a ≫ σ = lift_subst σ ≫ subst0 (a.subst σ) := by
  funext x
  induction x using Fin.cases
  · simp only [CategoryStruct.comp, RelativeMonad.bind, Function.comp_apply,
      subst0, lift_subst, Fin.cases_zero, tm.subst]
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
  · simp only [tm.subst_comp_app, tm.subst, subst0, Fin.cases_zero, lift_subst]
  · simp only [tm.subst_comp_app, lift_subst, Fin.cases_succ, Function.comp_apply, ←
    tm.ren_subst_comp]
    apply tm.subst_id_ext
    funext y
    rfl

theorem subst_0_succ {k n : Subst m} (σ : (k+1) ⟶ n) :
  let σ0 : (k + 1) ⟶ (n + k) := (σ (0 : Fin (k+1))).ren (fun i => i.addNat k) ∷ (tm.var ∘ Fin.castAdd' _)
  let σ' : k ⟶ n := σ ∘ Fin.succ
  let σsucc : (n + k) ⟶ n := 𝟙 n ++ σ'
  σ = σ0 ≫ σsucc := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp [tm.subst_comp_app, <-tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext' ; intros i
    simp [HAppend.hAppend]
    rfl
  | succ i =>
    simp [tm.subst_comp_app, <-tm.ren_subst_comp, tm.subst, HAppend.hAppend]


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


theorem substnsucc' (σ : (n+1) ⟶ k) :
  substn σ = subst0 ((σ (0 : Fin (n+1))).ren (fun i => i.addNat n)) ≫ substn (σ ∘ Fin.succ) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [substn_at0, tm.subst_comp_app, subst0, Fin.cases_zero, ← tm.ren_subst_comp]
    symm; apply tm.subst_id_ext
    funext i; simp only [Function.comp_apply, substn, Fin.casesAdd_left]
    rfl
  | succ i =>
    simp only [Nat.add_eq, tm.subst_comp_app, subst0, Fin.cases_succ, tm.subst]
    rw [substn_atsucc]
    rfl

theorem substnsucc'' (σ : Fin n ⟶ tm m k) (t: tm m k):
  substn (scons t σ ) = subst0 (t.ren (fun i => i.addNat n)) ≫ substn σ := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp [tm.subst_comp_app, subst0, substn_at0, <-tm.ren_subst_comp]
    symm; apply tm.subst_id_ext
    funext i; simp [substn]
    rfl
  | succ i =>
    simp [tm.subst_comp_app,subst0,tm.subst]
    have := substn_atsucc (scons t σ)
    have h : substn (scons t σ) i.succ = (substn (scons t σ) ∘ Fin.succ) i := rfl
    rw [h]
    rw[← this]
    congr


abbrev Tm (m : monosig) := RelativeMonad.kleisli.forgetful (tm.substitution (m:=m))

namespace Example
-- a simple signature with a nullary operation and a binary operation
def magma : monosig where
  ops := Bool
  arity_ops := fun b => if b then 0 else 2
  preds := Empty
  arity_preds := Empty.elim


def v0 : tm magma 1 := .var (0 : Fin 1)
def ε : tm magma n := .op true Fin.elim0
def mult (t u : tm magma n) : tm magma n :=
  .op false (fun i : Fin 2 => [ t , u ][i])

#check v0⟪ε ∷ 𝟙 _ ⟫

-- Oups...
#reduce (mult v0 (mult v0 v0))⟪ε ∷ 𝟙 _ ⟫

end Example
