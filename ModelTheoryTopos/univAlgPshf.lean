import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Sites.Sieves


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

inductive fml (m : monosig) : Nat -> Type where
  | pred : (p : m.preds) -> (Fin (m.arity_preds p) -> tm m n) -> fml m n
  | true : fml m n
  | false : fml m n
  | conj : fml m n -> fml m n -> fml m n
  | disj : fml m n -> fml m n -> fml m n
  -- | infdisj : (A : Type) -> (A -> fml m n) -> fml m n
  | eq : tm m n -> tm m n -> fml m n
  | exists : fml m (n + 1) -> fml m n

def fml.existsn : {n' : Nat} -> fml m (n + n') -> fml m n
| 0, φ => φ
| _+1, φ => existsn φ.exists


-- x1, .., xn | φ ⊢ ψ
structure sequent (m : monosig) where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx


structure theory where
  sig : monosig
  axioms : List (sequent sig)

def Ren n n' := Fin n -> Fin n'

-- TODO: there's probably a name for that def in Fin
def Ren.lift (f : Ren n n') : Ren (n+1) (n'+1) :=
  Fin.cases 0 (fun i => f i + 1)

def tm.ren (f : Ren n n') : tm m n -> tm m n'
| .var i => .var (f i)
| .op o k => .op o (fun i => (k i).ren f)

def fml.ren (f : Ren n n') : fml m n -> fml m n'
| .pred p k => .pred p (fun i => (k i).ren f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.ren f) (ψ.ren f)
| .disj φ ψ => .disj (φ.ren f) (ψ.ren f)
| .eq t u => .eq (t.ren f) (u.ren f)
| .exists φ => .exists (φ.ren f.lift)

-- just to show how to use
def weaken_fml_for_functional_prop1 (φ : fml m (n1 + n2)) : fml m (n1 + n1 + n2) :=
  φ.ren (Fin.addCases (Fin.castAdd n2 ∘ Fin.castAdd n1) (Fin.natAdd (n1+n1)))

def weaken_fml_for_functional_prop2 (φ : fml m (n1 + n2)) : fml m (n1 + n1 + n2) :=
  φ.ren (Fin.addCases (Fin.castAdd n2 ∘ Fin.natAdd n1) (Fin.natAdd (n1+n1)))


namespace HeytingThy

  inductive ops where
    | conj
    | true
    | impl

  def arity_ops : ops -> Nat
    | .conj => 2
    | .impl => 2
    | .true => 0

  def heytingSig : monosig where
    ops := ops
    arity_ops := arity_ops
    preds := Unit
    arity_preds _ := 2

  def htrue : tm heytingSig n := .op .true Fin.elim0
  def hconj (t u : tm heytingSig n) : tm heytingSig n :=
    .op .conj (fun i : Fin 2 => [t, u][i])
  def himpl (t u : tm heytingSig n) : tm heytingSig n :=
    .op .impl (fun i : Fin 2 => [t, u][i])

  def le (t u : tm heytingSig n) : fml heytingSig n :=
    .pred () (fun i : Fin 2 => [t, u][i])

  def le_refl : sequent heytingSig where
    ctx := 1
    concl := le (.var 0) (.var 0)

  -- x, y, z | x <= y /\ y <= z ⊢ x <= z
  def le_trans : sequent heytingSig where
    ctx := 2
    premise := .conj (le (.var 0) (.var 1)) (le (.var 1) (.var 2))
    concl := le (.var 0) (.var 2)

  def le_antisym : sequent heytingSig where
    ctx := 2
    premise := .conj (le (.var 0) (.var 1)) (le (.var 1) (.var 0))
    concl := .eq (.var 0) (.var 1)

  def top : sequent heytingSig where
    ctx := 1
    concl := le (.var 0) htrue

  def hconj_left : sequent heytingSig where
    ctx := 2
    concl := le (hconj (.var 0) (.var 1)) (.var 0)

  def hconj_right : sequent heytingSig where
    ctx := 2
    concl := le (hconj (.var 0) (.var 1)) (.var 1)

  def hconj_univ : sequent heytingSig where
    ctx := 3
    premise := .conj (le (.var 0) (.var 1)) (le (.var 0) (.var 2))
    concl := le (.var 0) (hconj (.var 1) (.var 2))

  def himpl_curry : sequent heytingSig where
    ctx := 3
    premise := le (hconj (.var 0) (.var 1)) (.var 2)
    concl := le (.var 0) (himpl (.var 1) (.var 2))

  def himpl_uncurry : sequent heytingSig where
    ctx := 3
    premise := le (.var 0) (himpl (.var 1) (.var 2))
    concl := le (hconj (.var 0) (.var 1)) (.var 2)

  def heytingThy : theory where
    sig := heytingSig
    axioms :=
      [le_refl, le_trans, le_antisym,
        top,
        hconj_left, hconj_right, hconj_univ,
        himpl_curry, himpl_uncurry ]

end HeytingThy

namespace CategoryTheory.ChosenFiniteProducts
  open MonoidalCategory

  variable {D : Type u} [Category D] [ChosenFiniteProducts D]

  def npow (x : D) : Nat -> D
    | 0 => 𝟙_ D
    | n+1 => x  ⊗ (npow x n)

  def nproj (x : D) (n : Nat) (k : Fin n) : (npow x n ⟶ x) :=
    k.succRecOn
      (fun _ => ChosenFiniteProducts.fst x _)
      (fun _ _ ih => ChosenFiniteProducts.snd _ _ ≫ ih)

  def npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : x ⟶ npow y n :=
    match n with
    | 0 => ChosenFiniteProducts.toUnit x
    | n+1 => ChosenFiniteProducts.lift (k 0) (npair x y n (fun i => k (i+1)))

  def nlift (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : npow x n ⟶ npow y n :=
    match n with
    | 0 => 𝟙 (𝟙_ D)
    | n+1 => k 0 ⊗ nlift x y n (fun i => k (i+1))
    -- npair (npow x n) y n (fun i => nproj x n i ≫ k i)


  def nlift_diag (x y : D) (n : Nat) (f : x ⟶ y) : npow x n ⟶ npow y n :=
    nlift x y n (fun _ => f)

  theorem nlift_diag_id (x : D) : nlift_diag x x n (𝟙 x) = 𝟙 (npow x n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [nlift_diag, nlift]
      simp [nlift_diag] at ih
      rw [ih]
      simp [npow]

  theorem nlift_comp (x y z : D) (n : Nat) (k : Fin n → (x ⟶ y)) (l : Fin n → (y ⟶ z)) :
    nlift x y n k ≫ nlift y z n l = nlift x z n (fun i => k i ≫ l i) := by
    induction n with
    | zero =>
      simp [nlift]
      apply toUnit_unique
    | succ n ih =>
      simp [nlift]
      have := ih (fun i => k (i+1)) (fun i => l (i+1))
      rw [<-tensor_comp, ih]

  theorem nlift_diag_comp (x y z : D) (f: x ⟶ y) (g : y ⟶ z) :
    nlift_diag x y n f ≫ nlift_diag y z n g = nlift_diag x z n (f ≫ g) :=
    nlift_comp x y z n (fun _ => f) (fun _ => g)

end CategoryTheory.ChosenFiniteProducts

abbrev CategoryTheory.Psh (C:Type) [Category C] := Functor Cᵒᵖ Type

namespace SubobjectClassifier
  open CategoryTheory MonoidalCategory ChosenFiniteProducts
  variable {C : Type} [Category C]

  @[simp]
  def prop : Psh C where
    obj X := Sieve X.unop
    map h x := x.pullback h.unop
    map_id := by
      intro
      simp [Sieve.pullback_id]
      rfl
    map_comp := by
      intros
      simp [Sieve.pullback_comp]
      rfl

  def top : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊤ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp

  def bot : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊥ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp [Sieve.ext_iff]
      intros
      constructor <;> apply False.elim

  def conj : prop (C:=C) ⊗ prop  ⟶ prop where
    app X := fun p => (p.1 ⊓ p.2: Sieve X.unop)

  def disj : prop (C:=C) ⊗ prop ⟶ prop where
    app X := fun p => (p.1 ⊔ p.2 : Sieve X.unop)

  def eq {A : Psh C} : A ⊗ A ⟶ prop where
    app X := fun as =>
      {
        arrows :=  fun Y f => A.map f.op as.1 = A.map f.op as.2
        downward_closed := by
          intros _ _ _ eq _
          simp [eq]
      }
    naturality X Y f := by
      funext as
      simp [Sieve.ext_iff]
      intros Z g
      constructor <;> exact id

  def existQ {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) : B ⟶ prop where
    app X := fun b =>
      {
        arrows := fun Y f => exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y)
        downward_closed := by
          intro Y Z f ⟨a, ⟨eq, h⟩⟩ g
          let a' := A.map g.op a
          exists a'
          constructor
          · calc p.app (Opposite.op Z) a' = (A.map g.op ≫ p.app _) a := rfl
            _ = (p.app _ ≫ B.map g.op) a := by rw [p.naturality g.op]
            _ = B.map (g ≫ f).op b := by simp [eq]
          · have eq : φ.app _ a' = prop.map g.op (φ.app _ a) := by
              calc φ.app _ a' = (A.map g.op ≫ φ.app _) a := rfl
              _ = (φ.app _ ≫ prop.map g.op) a := by rw [φ.naturality g.op]
              _ = prop.map g.op (φ.app _ a) := rfl
            simp [eq]
            have := (φ.app _ a).downward_closed h g
            simp at this
            exact this
      }

  -- def existQ {A B : Psh C} (p : A ⟶ B) : B ⟶ prop C where
  --   app X := fun b =>
  --     {
  --       arrows := fun Y f => exists a, p.app (Opposite.op Y) a = B.map f.op b
  --       downward_closed := by
  --         intro Y Z f ⟨a, h⟩ g
  --         exists (A.map g.op a)
  --         calc p.app (Opposite.op Z) (A.map g.op a) = (A.map g.op ≫ p.app _) a := rfl
  --         _ = (p.app _ ≫ B.map g.op) a := by rw [p.naturality g.op]
  --         _ = B.map (g ≫ f).op b := by simp [h]
  --     }

  def existπ {A B : Psh C} (φ : A ⊗ B ⟶ prop) : B ⟶ prop := existQ (snd A B) φ

end SubobjectClassifier

namespace InterpPsh
  open CategoryTheory MonoidalCategory ChosenFiniteProducts
  variable {C : Type} [Category C]

  structure Str (S : monosig) (C : Type) [Category C] where
    carrier : Psh C
    interp_ops : forall (o : S.ops), npow carrier (S.arity_ops o) ⟶ carrier
    interp_preds : forall (p : S.preds), npow carrier (S.arity_preds p) ⟶ SubobjectClassifier.prop

  namespace Str

  def interp_tm {S : monosig} (L : Str S C) : tm S n -> (npow L.carrier n ⟶ L.carrier)
    | .var k => nproj _ _ k
    | .op o k => (npair _ _ _ (fun i => L.interp_tm (k i))) ≫ L.interp_ops o

  def interp_fml {S : monosig} (L : Str S C) : fml S n -> (npow L.carrier n ⟶ SubobjectClassifier.prop)
  | .pred p k => (npair _ _ _ (fun i => interp_tm L (k i))) ≫ L.interp_preds p
  | .true => toUnit _ ≫ SubobjectClassifier.top
  | .false => toUnit _ ≫ SubobjectClassifier.bot
  | .conj φ ψ => lift (L.interp_fml φ) (L.interp_fml ψ) ≫ SubobjectClassifier.conj
  | .disj φ ψ => lift (interp_fml L φ) (interp_fml L ψ) ≫ SubobjectClassifier.disj
  | .exists φ => SubobjectClassifier.existπ (L.interp_fml φ)
  | .eq t u => lift (L.interp_tm t) (interp_tm L u) ≫ SubobjectClassifier.eq

  def model {S : monosig} (L : Str S C) (s : sequent S) : Prop :=
    forall (Γ : Cᵒᵖ) vs,
      let interp_premise : Sieve Γ.unop := (L.interp_fml s.premise).app Γ vs
      let interp_concl := (L.interp_fml s.concl).app Γ vs
      interp_premise ≤ interp_concl

  structure morphism {S : monosig} (L L' : Str S C) where
    map : L.carrier ⟶ L'.carrier
    ops_comm : forall (o : S.ops), nlift_diag _ _ _ map ≫ L'.interp_ops o = L.interp_ops o ≫ map
    preds_comm : forall (p : S.preds), nlift_diag _ _ _ map ≫ L'.interp_preds p  = L.interp_preds p

  instance : {S : monosig} → Category (Str S C) where
    Hom := morphism
    id L := {
      map := 𝟙 L.carrier
      ops_comm := fun o => by simp [nlift_diag_id]
      preds_comm := fun p => by simp [nlift_diag_id]
      }
    comp f g := {
      map := f.map ≫ g.map
      ops_comm := fun o => by
        rw [<-nlift_diag_comp]
        simp [g.ops_comm]
        rw [<-Category.assoc]
        simp [f.ops_comm]
      preds_comm := fun p => by
        rw [<-nlift_diag_comp]
        simp [g.preds_comm, f.preds_comm]
    }

  end Str

  structure Mod (T : theory) (C : Type) [Category C] where
    str : Str T.sig C
    valid : forall s, s ∈ T.axioms → str.model s


  namespace BaseChange
    variable (D : Type) [Category D] (F : Functor C D) (T : theory)

    -- First part, show that a functor F : C ⥤ D
    -- induces by precomposition, a functor
    -- F^* : T-Str(D) ⥤ T-Str(C)
    -- and this restricts to a functor
    -- F^* : T-Mod(D) ⥤ T-Mod(C)
    def pb_obj (L : Str T.sig D) : Str T.sig C where
      carrier := F.op ⋙ L.carrier
      interp_ops := fun o => by sorry -- L.interp_ops o
      interp_preds := by sorry

    def pb_map (L₁ L₂ : Str T.sig D) (f : L₁ ⟶ L₂) :
      pb_obj D F T L₁ ⟶ pb_obj D F T L₂ where
      map := by sorry -- whisker f.map with F
      ops_comm := by sorry
      preds_comm := by sorry

    def pullback : Str T.sig D ⥤ Str T.sig C where
      obj := pb_obj D F T
      map := pb_map D F T _ _
      map_id := by sorry -- check whether an explicit proof is necessary once pb_map is defined
      map_comp := by sorry -- check whether an explicit proof is necessary once pb_map is defined


    -- Second part, (-)^* assembles as a 2-functor
    -- T-Mod : Cat^op -> CAT

    -- Third part, T-Mod is representable
    -- T-Mod(C) ≅ Topos(Set[T], Psh(C))


    -- Fourth part, 2-Grothendieck construction
    -- 2-category T-Mod    T: theory
    -- Objects (C, M)  C : category, M : T-Mod(C)
    -- 1-cell  (C, M) ==> (D, N)    F : C ==> D functor, f : M -> F^*N
    -- 2-cells (F, f) -> (G, g)   μ : F -> G,  μ_N T-Mod(F^* N, G^* N)

  end BaseChange

end InterpPsh
