import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Misc
import ModelTheoryTopos.Category.RelativeMonad
import ModelTheoryTopos.Tactics

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

/-
  From the definitions of the category of renamings, the action of substitution on well-scoped terms
  and the embedding of finite types into types we obtain all the algebraic
  properties of renaming and substitutions through the relative monad tm.substitution

  The very annoying bit is that all these abstract definitions do not unify well
  in practice and we need to re-declare pointwise versions
-/

instance CategoryTheory.RenCat : Category RenCtx where
  Hom n1 n2 := Fin n1 -> Fin n2
  id := fun _ x => x
  comp := fun f g => g ∘ f

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

-- Category of finite context and substitutions
abbrev Subst m := (tm.substitution (m:=m)).kl

-- redefinition of tm keeping track of the relevant functor structure wrt substitutions
abbrev Tm (m : monosig) : Subst m ⥤ Type :=
  RelativeMonad.kleisli.forgetful (tm.substitution (m:=m))

def tm.ren {n1 n2 : RenCtx} (f : n1 ⟶ n2) (t : tm m n1) := tm.substitution.functor.map f t

-- Instances to use concrete natural numbers in context expressions
instance : OfNat (Subst m) n where
  ofNat := tm.substitution.to_kl n

instance : HAdd (Subst m) Nat (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + l)

instance : HAdd  Nat (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (k + tm.substitution.from_kl l)

instance : HAdd  (Subst m) (Subst m) (Subst m) where
  hAdd := fun k l => tm.substitution.to_kl (tm.substitution.from_kl k + tm.substitution.from_kl l)


-- Standard unary combinators on renamings and substitutions

def lift_ren {n n' : RenCtx} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases 0 (Fin.succ ∘ f)

def lift_subst {n n' : Subst m} (f : n ⟶ n') : (n+1) ⟶ (n'+1) :=
  Fin.cases (.var 0) (tm.ren Fin.succ ∘ f)

def subst0 {m} {n : Subst m} (a : tm m n) : (n+1) ⟶ n :=
  Fin.cases a (𝟙 n)

abbrev scons {k n : Subst S} (a : tm S n) (σ : k ⟶ n) : (k+1) ⟶ n :=
  Fin.cases a σ

-- n-ary combinators

-- Mnemonics for some block-based n-ary renamings
-- 1 means that the block is in the image of the renaming, 0 that it is not
namespace R
abbrev in10 (i : Fin n) : Fin (n + k) := i.addNat k
abbrev in01 (i : Fin n) : Fin (k + n) := i.castAdd' k
abbrev in101 k' : Fin (n + k) -> Fin (n + k' + k) :=
  Fin.casesAdd (in10 ∘ in10) in01
abbrev in110 k' : Fin (n + k) -> Fin (n + k + k') := in10
abbrev in001 : Fin k -> Fin (n + k + k) := in01
abbrev in010 : Fin k -> Fin (n + k + k) := in10 ∘ in01
abbrev in100 : Fin n -> Fin (n + k + k) := in10 ∘ in10
end R


def substn {m} {n n' : Subst m} (σ : n' ⟶ n) : (n+n') ⟶ n :=
  Fin.casesAdd (𝟙 n) σ

def liftn_subst {n: Nat} {k k' : Subst m} (f : k ⟶ k') : (k+n) ⟶ (k'+n) :=
  Fin.casesAdd
    (tm.ren R.in10 ∘ f)
    (fun i ↦ .var (R.in01 i))

def liftn_ren {n1 n2 n : RenCtx} (f : n1 ⟶ n2) : (n1+n) ⟶ (n2+n) :=
  Fin.casesAdd (R.in10 ∘ f) R.in01

abbrev lift  (n: Nat) {k k' : Subst m} (f : k ⟶ k') := liftn_subst (n:=n) f



-- Re-declaration of the definitions in tm.substitution in a pointwise fashion

@[simp, grind]
theorem tm.ren_var {n1 n2 : RenCtx} (i : Fin n1) (f : n1 ⟶ n2) : (tm.var (m:=m) i).ren f = .var (f i) := by
  simp only [ren, emb, RelativeMonad.functor, id_eq, RelativeMonad.ret,
    RelativeMonad.bind, subst, types_comp_apply]

@[simp, grind]
theorem tm.ren_op {n1 n2 : RenCtx} (o : m.ops) (k : Fin (m.arity_ops o) -> tm m n1) (f : n1 ⟶ n2)
  : (tm.op o k).ren f = .op o fun i ↦ (k i).ren f := by
  simp only [ren, emb, RelativeMonad.functor, id_eq, RelativeMonad.ret, RelativeMonad.bind,
    subst]


@[grind]
theorem tm.subst_comp_app {x y z : Subst m} (f : x ⟶ y) (g : y ⟶ z) (i : Fin x)
  : (f ≫ g) i = (f i).subst g :=
  rfl

@[grind]
theorem tm.subst_id_app {x : Subst m}  (i : Fin x)
  : (𝟙 x) i = .var i :=
  rfl

theorem tm.subst_map {n n' : Subst m} (f : n ⟶ n') (t : tm m n) :
  t.subst f = tm.substitution.bind f t := rfl

theorem tm.ret_var (n : Subst m)
  : tm.var = 𝟙 n := rfl

@[grind]
theorem tm.ren_to_subst {n n' : RenCtx} (f : n ⟶ n') (t : tm m n) :
  t.ren f = t.subst (tm.var ∘ f) := by
  rfl

-- it would have probably been simpler to do the proof directly..
@[grind]
theorem tm.subst_id (n : Subst m) (t : tm m n) : t.subst (𝟙 n) = t := by
  simp [subst_map, CategoryStruct.id, tm.substitution.lunit]

@[grind]
theorem tm.subst_comp (n1 n2 n3 : Subst m) (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1)
  : t.subst (f ≫ g) = (t.subst f).subst g := by
  calc
    subst (f ≫ g) t = tm.substitution.bind (f ≫ tm.substitution.bind g) t := by simp [tm.substitution, CategoryStruct.comp]
   _ = subst g (subst f t) := by simp only [tm.substitution.assoc, types_comp_apply]; simp only [substitution]

@[grind]
theorem tm.ren_id {n : RenCtx} (t : tm m n)
  : t.ren (𝟙 n) = t := by
  rw [ren, substitution.functor.map_id]
  rfl

@[grind]
theorem tm.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : tm m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  rw [ren, substitution.functor.map_comp]
  rfl

@[grind]
theorem tm.ren_subst_comp {n2 : Subst m} (f : Fin n1 ⟶ Fin n2) (g : n2 ⟶ n3) (t : tm m n1):
  subst (g ∘ f) t = subst g (ren f t) := by
  have := RelativeMonad.bind_natural_l tm.substitution f g
  calc
    subst (g ∘ f) t = tm.substitution.bind (emb.map f ≫ g) t := rfl
    _ = (substitution.functor.map f ≫ tm.substitution.bind g) t := by rw [this]
    _ = subst g (ren f t) := by rw [subst_map, ren]; simp only [CategoryStruct.comp,
      RelativeMonad.functor_eq, Function.comp_apply]

@[grind]
theorem tm.subst_ren_comp {n2 n3: Subst m} (f : n1 ⟶ n2) (g : Fin n2 ⟶ Fin n3) (t : tm m n1):
  subst (f ≫ (𝟙 n3 ∘ g)) t = ren g (subst f t) := by
  have := RelativeMonad.bind_natural_r tm.substitution f g
  calc
    subst (f ≫ (𝟙 n3 ∘ g)) t = (substitution.bind (f ≫ substitution.functor.map g)) t := rfl
    _ = (substitution.bind f ≫ substitution.functor.map g) t:= by rw [this]
    _ = ren g (subst f t) := by rw [ren, subst_map]; simp only [RelativeMonad.functor_eq,
      CategoryStruct.comp, Function.comp_apply]


-- Why do I need these 2 extensionality lemmas ? They look like boilerplate...
theorem tm.subst_id_ext {n : Subst m} (f : n ⟶ n) (t : tm m n) : f = 𝟙 n → t.subst f = t := by
  rintro rfl
  simp [subst_id]

theorem tm.subst_id_ext' {n : Subst m} (f : n ⟶ n) (t : tm m n)
  (h : forall i : Fin n, f i = .var i) :
  t.subst f = t := by
  apply tm.subst_id_ext ; funext i; apply h



-- Lemmas for unary combinators on renaming and substitutions

@[grind]
theorem lift_ren_id : lift_ren (𝟙 n) = 𝟙 (n+1) := by
  funext i ; simp only [lift_ren, CategoryStruct.id]
  induction i using Fin.cases <;> simp?

@[grind]
theorem lift_ren_comp : lift_ren (f ≫ g) = lift_ren f ≫ lift_ren g := by
  funext i ; simp [lift_ren, CategoryStruct.comp]
  induction i using Fin.cases <;> simp?

@[grind]
theorem lift_subst_id (n : Subst m) : lift_subst (𝟙 n) = 𝟙 (n+1: Subst m) := by
  funext i ; simp only [lift_subst, CategoryStruct.id]
  induction i using Fin.cases <;> simp only [RelativeMonad.ret,Fin.cases_zero, Fin.cases_succ, Function.comp_apply,
    tm.ren_var]

@[grind]
theorem lift_subst_comp : lift_subst (f ≫ g) = lift_subst f ≫ lift_subst g := by
  funext i ; simp [lift_subst, CategoryStruct.comp]
  induction i using Fin.cases with
    | zero => simp only [RelativeMonad.bind, Fin.cases_zero, tm.subst, lift_subst]
    | succ i =>
      simp only [RelativeMonad.bind, Fin.cases_succ, Function.comp_apply, ← tm.subst_ren_comp, ← tm.ren_subst_comp]
      congr

@[grind]
theorem subst0_lift_subst {n n' : Subst m} (a : tm m n) (σ : n ⟶ n') :
  subst0 a ≫ σ = lift_subst σ ≫ subst0 (a.subst σ) := by
  funext x
  induction x using Fin.cases
  · simp only [CategoryStruct.comp, RelativeMonad.bind, Function.comp_apply,
      subst0, lift_subst, Fin.cases_zero, tm.subst]
  · simp only [CategoryStruct.comp, RelativeMonad.bind, Function.comp_apply,
    lift_subst, Fin.cases_succ, ← tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext
    funext y
    simp only [Function.comp_apply, subst0, Fin.cases_succ]

@[grind]
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

lemma lift_ren_zero {n n' : RenCtx} (f : n ⟶ n'):
 lift_ren f 0 = 0 := by
  simp[lift_ren]

lemma lift_ren_succ {n n' : RenCtx} (f : n ⟶ n') (i: Fin n):
 lift_ren f (Fin.succ i) = Fin.succ (f i) := by
  simp[lift_ren]


-- Lemmas on n-ary combinators

@[grind]
theorem substn_left {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n'):
  substn σ (Fin.addNat a n) = .var a := by
   simp only [substn, Fin.casesAdd_left]
   rfl

@[grind]
theorem substn_right {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n):
  substn σ (Fin.castAdd' n' a ) = σ a := by
   simp only [substn, Fin.casesAdd_right]


@[grind]
theorem substn_liftn_subst {n k k' : Subst m} (σ : n ⟶ k) (f : k ⟶ k') :
  substn σ ≫ f = liftn_subst f ≫ substn (σ ≫ f) := by
  funext i
  induction i using Fin.casesAdd
  · simp only [tm.subst_comp_app, substn, Fin.casesAdd_left, tm.subst, liftn_subst,
    Function.comp_apply, ← tm.ren_subst_comp]
    symm ; apply tm.subst_id_ext
    funext y
    rw [Function.comp_apply, substn, Fin.casesAdd_left]
  · simp only [tm.subst_comp_app, substn, Fin.casesAdd_right, liftn_subst, tm.subst]

lemma liftn_ren_left {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n1):
 liftn_ren (n:=n) f (R.in10 i) = R.in10 (f i) := by
  simp[liftn_ren]

lemma liftn_ren_right {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n) :
 liftn_ren (n:=n) f (R.in01 i) = R.in01 i := by
  simp[liftn_ren]



-- Comparison of n-ary combinators with unary/0-ary operators

theorem subst0_substn {n : Subst m} (a : tm m n) :
  subst0 a = substn (fun _ => a) := by
  funext x ; induction x using Fin.cases <;>
    simp only [subst0, Fin.cases_zero, Fin.cases_succ, substn] <;> rfl

theorem subst0_substn_ext {n : Subst m} (σ : 1 ⟶ n) (a : tm m n) (h : a = σ (0 : Fin 1)) :
  subst0 a = substn σ := by
  have : σ = (fun _ => a) := by
    funext i ; simp [emb] at i
    rw [Fin.fin_one_eq_zero i] ; symm; assumption
  subst this ; apply subst0_substn

theorem substn0 (σ : 0 ⟶ k) : substn σ = 𝟙 k := by
  funext i
  rw [substn, <-Fin.addNat_zero _ i, Fin.casesAdd_left, Fin.addNat_zero]

theorem substn_at0 (σ : (n+1) ⟶ k) : substn σ (0 : Fin (k + n + 1)) = σ (0 : Fin (n+1)) := by
  change 0 with Fin.castAdd' k (0 : Fin (n+1))
  rw [substn, Fin.casesAdd_right]

theorem substn_atsucc (σ : (n+1) ⟶ k) : substn (σ ∘ Fin.succ) = substn σ ∘ Fin.succ := by
  funext i
  induction i using Fin.casesAdd with
  | left i =>
    simp only [substn, Fin.casesAdd_left, Nat.add_eq, Function.comp_apply]
    change (i.addNat n).succ with i.addNat (n+1)
    rw [Fin.casesAdd_left]
  | right i =>
    simp only [substn, Fin.casesAdd_right, Function.comp_apply, Nat.add_eq]
    change (Fin.castAdd' k i).succ with Fin.castAdd' k i.succ
    rw [Fin.casesAdd_right]

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
  | succ i =>
    simp [tm.subst_comp_app,subst0,tm.subst]
    change substn (scons t σ) i.succ with (substn (scons t σ) ∘ Fin.succ) i
    rw [← substn_atsucc (scons t σ)]
    rfl

lemma lift_liftn_ren {n1 n2 n : RenCtx} (f : n1 ⟶ n2) :
  lift_ren (liftn_ren f) = liftn_ren (n:=n+ 1) f := by
    funext x
    induction x using Fin.cases with
    | zero =>
      simp [lift_ren]
      change 0 with @R.in01 (n+1) n1 0
      simp [liftn_ren_right]
      rfl
    | succ i =>
      simp [lift_ren]
      induction i using Fin.casesAdd with
      | left i =>
        change(i.addNat n).succ with R.in10 (k:=n+1) i
        change i.addNat n with R.in10 i
        simp [liftn_ren_left]
        rfl
      | right i =>
        change (Fin.castAdd' n1 i).succ with R.in01 i.succ
        change Fin.castAdd' n1 i with R.in01 i
        simp [liftn_ren]
        rfl


-- Tentative notations for substitutions that should apply to formulas as well

class ScopedSubstitution (T : Nat -> Type u) (F : Nat -> Type v) where
  ssubst : forall {k n : Nat} (_σ : Fin k → T n), F k -> F n

-- instance substGetElem (T : Nat -> Type u) (F : Nat -> Type v) [ScopedSubstitution T F] {k n : Nat} :
--   GetElem (F k) ( Fin k → T n) (F n) (fun _ _ => True) where
--   getElem t σ _ := ScopedSubstitution.ssubst σ t

notation t "⟪" σ "⟫" => (ScopedSubstitution.ssubst σ t)

instance append_substitutions {k n m : Subst S} : HAppend (k ⟶ m) (n ⟶ m) (k + n ⟶ m) where
  hAppend σ τ := Fin.casesAdd σ τ


infix:50 " ∷ " => scons
-- infix:50 " ⇑ " => scons


instance : ScopedSubstitution (tm S) (tm S) where
  ssubst σ t := tm.subst σ t

-- experiment ??
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
    simp [tm.subst_comp_app, tm.subst, HAppend.hAppend]

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

-- #check v0⟪ε ∷ 𝟙 _ ⟫

-- Oups...
-- #reduce (mult v0 (mult v0 v0))⟪ε ∷ 𝟙 _ ⟫

end Example
