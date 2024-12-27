import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Whiskering
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic

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
      (fun _ => fst x _)
      (fun _ _ ih => snd _ _ ≫ ih)

  def npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : x ⟶ npow y n :=
    match n with
    | 0 => toUnit x
    | n+1 => lift (k 0) (npair x y n (fun i => k (i+1)))

  theorem npair_univ {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (f : x ⟶ npow y n)
    (h : forall i : Fin n, k i = f ≫ nproj y n i) :
    npair x y n k = f := by
    induction n with
      | zero => apply toUnit_unique
      | succ n ih =>
        simp [npair] ; apply hom_ext <;> simp
        · have := h 0
          simp [nproj] at this
          assumption
        · rw [ih]
          intros i
          have hi := h i.succ
          simp [nproj] at hi
          rw [hi, Category.assoc]
          congr
  --new: to_npow_pair npair_univ'(maybe a better name would be npair_ext)
  --nproj_succ nlift_nproj nlift_npair
  theorem to_npow_npair  {x y : D} (n : Nat)  (f : x ⟶ npow y n) :
   npair x y n (fun i => f ≫ nproj y n i )= f := by
     apply npair_univ
     intros i
     simp


  theorem npair_univ' {x y : D} (n : Nat) (f g: x ⟶ npow y n)
    (h : forall i : Fin n, f ≫ nproj y n i = g ≫ nproj y n i) : f = g := by
     have a : f = npair x y n (fun i => f ≫ nproj y n i ):=
          by simp[to_npow_npair]
     rw[a]
     apply npair_univ
     intros i
     simp[h]

  theorem nproj_succ  (x : D) (n : Nat) (i : Fin n) :
    nproj x (n+1) i.succ = snd _ _ ≫ (nproj x n i) := by
   simp[nproj ]


  theorem npair_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    npair x y n k ≫ nproj y n i = k i := by
      induction n with
       | zero => exact (Fin.elim0 i)
       | succ n ih =>
         induction i using Fin.cases with
         | zero =>
           simp[nproj,npair]
         | succ i =>
           simp[npair]
           simp[nproj_succ]
           simp[ih]



  theorem npair_natural (x y z: D) (n : Nat) (f : x ⟶ y) (k : Fin n → (y ⟶ z))  :
    npair x z n (fun i => f ≫ k i) = f ≫ npair y z n k := by
    induction n with
      | zero => apply toUnit_unique
      | succ n ih =>
        simp [npair, ih]

  def nlift (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : npow x n ⟶ npow y n :=
    match n with
    | 0 => 𝟙 (𝟙_ D)
    | n+1 => k 0 ⊗ nlift x y n (fun i => k (i+1))
    -- npair (npow x n) y n (fun i => nproj x n i ≫ k i)

  /-noncomputable
    def pb_prod0 (X : Psh D) (n : Nat) : F.op ⋙ npow X n ⟶ npow (F.op ⋙ X) n :=
      npair _ (F.op ⋙ X) n (fun i => whiskerLeft F.op (nproj X n i))
   -/


  theorem nlift_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    nlift x y n k ≫ nproj y n i = nproj x n i ≫ k i := by
      induction n with
       | zero => exact (Fin.elim0 i)
       | succ n ih =>
         induction i using Fin.cases with
         | zero =>
           simp[nlift,nproj]
         | succ i =>
           simp[nproj_succ]
           simp[nlift]
           simp[ih]

  theorem nlift_npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) :
   nlift x y n k = npair (npow x n) y n (fun i => nproj x n i ≫ k i) := by
    apply npair_univ'
    intros i
    simp[npair_nproj]
    simp[nlift_nproj]

  theorem nlift_npair_nproj (x  : D) (n : Nat) :
   nlift x x n (fun i => 𝟙 x) = npair (npow x n) x n (fun i => nproj x n i) := by
    apply npair_univ'
    intros i
    simp[npair_nproj]
    simp[nlift_nproj]


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

  def npow_functor (n : Nat) : D ⥤ D where
    obj := fun x => npow x n
    map := nlift_diag _ _ n
    map_id := by apply nlift_diag_id
    map_comp := by intros; symm; apply nlift_diag_comp

  -- TODO : get Yiming's version

  theorem nproj_natural (x y : D) (n : Nat) (f : x ⟶ y) (i : Fin n) :
    (npow_functor n).map f ≫ nproj y n i = nproj x n i ≫ f := by
    simp [npow_functor, nlift_diag, nlift_nproj]

  theorem npair_natural' (x y y': D) (n : Nat) (g : y ⟶ y') (k : Fin n → (x ⟶ y))  :
    npair x y' n (fun i => k i ≫ g) = npair x y n k ≫ (npow_functor n).map g := by
    apply npair_univ
    intros i
    simp [nproj_natural]
    rw [<-Category.assoc, npair_nproj]


end CategoryTheory.ChosenFiniteProducts

namespace NatIso
open CategoryTheory

noncomputable
def ofNatTrans {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : (F ≅ G) :=
  NatIso.ofComponents (fun c => asIso (θ.app c)) (fun f => θ.naturality f)

noncomputable
def ofNatTrans' {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : IsIso θ :=
  Iso.isIso_hom (ofNatTrans θ h)

end NatIso

namespace CategoryTheory.ChosenFiniteProducts
  open MonoidalCategory

  variable {C D : Type u} [Category C] [Category D] [ChosenFiniteProducts C] [ChosenFiniteProducts D] (F : C ⥤ D)

  def npow_oplax : npow_functor n ⋙ F ⟶ F ⋙ npow_functor n where
    app := fun X => npair (F.obj (npow X n)) (F.obj X) n (fun i => F.map (nproj X n i))
    naturality := by
      intros X Y f
      simp [npow_functor]
      have natl := npair_natural _ _ (F.obj Y) n (F.map ((npow_functor n).map f))
      have natr := npair_natural' (F.obj (npow X n)) _ _ n (F.map f)
      have := nproj_natural X Y n f
      simp [npow_functor] at natl natr this
      rw [<- natl, <-natr]
      congr; ext i
      rw [<-F.map_comp,<-F.map_comp, this]

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

  theorem existQ_app_arrows {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) (X: Cᵒᵖ) (b: B.obj X) (Y: C) (f: Y ⟶ Opposite.unop X):
    ((existQ p φ).app X b).arrows  f = exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y) := rfl



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

  noncomputable
  def existπ {A B : Psh C} (φ : A ⊗ B ⟶ prop) : B ⟶ prop := existQ (snd A B) φ

end SubobjectClassifier

namespace InterpPsh
  open CategoryTheory MonoidalCategory ChosenFiniteProducts

  structure Str (S : monosig) (C : Type) [Category C]  where
    carrier : Psh C
    interp_ops : forall (o : S.ops), npow carrier (S.arity_ops o) ⟶ carrier
    interp_preds : forall (p : S.preds), npow carrier (S.arity_preds p) ⟶ SubobjectClassifier.prop

  variable {C : Type} [Category C]

  namespace Str


  noncomputable
  def interp_tm {S : monosig} (L : Str S C) : tm S n -> (npow L.carrier n ⟶ L.carrier)
    | .var k => nproj _ _ k
    | .op o k => (npair _ _ _ (fun i => L.interp_tm (k i))) ≫ L.interp_ops o

  noncomputable
  def interp_fml {S : monosig} (L : Str S C) : fml S n -> (npow L.carrier n ⟶ SubobjectClassifier.prop)
  | .pred p k => (npair _ _ _ (fun i => interp_tm L (k i))) ≫ L.interp_preds p
  | .true => toUnit _ ≫ SubobjectClassifier.top
  | .false => toUnit _ ≫ SubobjectClassifier.bot
  | .conj φ ψ => lift (L.interp_fml φ) (L.interp_fml ψ) ≫ SubobjectClassifier.conj
  | .disj φ ψ => lift (interp_fml L φ) (interp_fml L ψ) ≫ SubobjectClassifier.disj
  | .infdisj φ => sorry
  | .existsQ φ => SubobjectClassifier.existπ (L.interp_fml φ)
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


    def pb_prop : F.op ⋙ SubobjectClassifier.prop (C:=D) ⟶ SubobjectClassifier.prop where
      app := fun c x =>
        let x'' : Sieve (F.obj c.unop) := x
        (Sieve.functorPullback F x'' : Sieve _)

    def SubobjectClassifier.pb_prop_top :
      whiskerLeft F.op SubobjectClassifier.top ≫ pb_prop D F  =
      SubobjectClassifier.top := by
      ext x ⟨⟩
      rfl

    def SubobjectClassifier.pb_prop_bot :
      whiskerLeft F.op SubobjectClassifier.bot ≫ pb_prop D F  =
      SubobjectClassifier.bot := by
      ext x ⟨⟩
      rfl

    def SubobjectClassifier.pb_prop_conj :
      whiskerLeft F.op SubobjectClassifier.conj ≫ pb_prop D F  =
      (pb_prop D F ⊗ pb_prop D F) ≫ SubobjectClassifier.conj := by
      ext x ⟨φ , ψ⟩
      rfl

    def SubobjectClassifier.pb_prop_disj :
      whiskerLeft F.op SubobjectClassifier.disj ≫ pb_prop D F  =
      (pb_prop D F ⊗ pb_prop D F) ≫ SubobjectClassifier.disj := by
      ext x ⟨φ , ψ⟩
      rfl



    def SubobjectClassifier.pb_prop_eq (X : Psh D) :
      whiskerLeft F.op (SubobjectClassifier.eq (A:=X)) ≫ pb_prop D F =
      SubobjectClassifier.eq (A:=F.op ⋙ X) := by
        ext x ⟨a1 , a2⟩
        apply CategoryTheory.Sieve.arrows_ext
        simp[CategoryTheory.whiskerLeft,pb_prop,
             SubobjectClassifier.eq]
        funext c0 f
        simp[Presieve.functorPullback]



    -- TODO: rename
    noncomputable
    def f (X : Psh D) (n : Nat) d : (npow X n).obj d ⟶ npow (X.obj d) n :=
      npair _ _ n (fun i => (nproj X n i).app d)

    theorem f_succ : f D X (n+1) d = ChosenFiniteProducts.lift (ChosenFiniteProducts.fst _ _) (ChosenFiniteProducts.snd _ _ ≫ f D X n d) := by
      simp [f, npair]; apply ChosenFiniteProducts.hom_ext <;> simp [nproj]
      · rfl
      · simp [npair_natural] ;rfl

    theorem f_iso X n d : IsIso (f D X n d) := by
      induction n with
        | zero => exists (ChosenFiniteProducts.toUnit _)
        | succ n ih =>
          exists (𝟙 (X.obj d) ⊗ inv (f D X n d)) ; constructor
          · rw [f_succ, lift_map] ; apply hom_ext <;> simp <;> rfl
          · simp [f_succ, npow]




    noncomputable
    def pb_prod0 (X : Psh D) (n : Nat) : F.op ⋙ npow X n ⟶ npow (F.op ⋙ X) n :=
      npair _ (F.op ⋙ X) n (fun i => whiskerLeft F.op (nproj X n i))

   -- theorem npow_app (X : Psh D) (n : Nat) (d:D) :
    --(npow X n).obj (Opposite.op d) = npow (X.obj (Opposite.op d)) n := sorry
    /-
    def pb_prod1 (X : Psh D) (n : Nat) : npow (F.op ⋙ X) n ⟶ F.op ⋙ npow X n :=
    match n with
    | 0 =>
    {
      app := by
       intros c
       exact CategoryTheory.ChosenFiniteProducts.toUnit
       sorry
      naturality := sorry
    }
    | (n + 1) => {
      app := fun
        | .op unop => by
          intro a
          simp
          simp[npow_app] at a
          simp[npow_app]
          simp[npow]
          sorry
      naturality := sorry
    }--fun a => sorry -- 𝟙 (F.op ⋙ X) ⊗ pb_prod1 D F X n
-/
    --def pb_prod1 (X : Psh D) (n : Nat) : npow (F.op ⋙ X) n ⟶ F.op ⋙ npow X n :=





    def ev (c : Cᵒᵖ) : Psh C ⥤ Type where
      obj := fun X => X.obj c
      map := fun f => f.app c

    theorem ev_map c {X Y : Psh C} (f : X ⟶ Y) : (ev c).map f = f.app c := rfl
    theorem pb_prob0_comm_lemma (X : Psh D) n c :
     ((pb_prod0 D F X n).app c) ≫ (f C (F.op ⋙ X) n c) = f D X n (F.op.obj c) := by
      let h1 := (pb_prod0 D F X n).app c
      let h2 := f C (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := f D X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, f, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod0 D F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod0, npair_nproj] at this
        simp [this, ev_map,pb_prod0 ]
      simp[h1,h2,h3,d] at eq
      exact eq


    theorem pb_prod0_pair (X : Psh D) (m : Nat) (Y: C)
     (t1: (F.op ⋙ X).obj (Opposite.op Y))
     (tm: (F.op ⋙ npow X m).obj (Opposite.op Y)):
    (pb_prod0 D F X (m + 1)).app (Opposite.op Y) (t1, tm) =
    (t1, (pb_prod0 D F X m).app (Opposite.op Y) tm) := by
      let k0 : (npow X (m + 1)).obj (F.op.obj (Opposite.op Y)) := (t1, tm)
      let h1 := (pb_prod0 D F X (m+1)).app (Opposite.op Y)
      let k1 := h1 k0
      let h2 := f C (F.op ⋙ X) (m+1) (Opposite.op Y)
      let d := F.op.obj (Opposite.op Y)
      let h3 := f D X (m+1) d
      have eq : h1 ≫ h2 = h3 := by
       have a00 := pb_prob0_comm_lemma D F X (m+1) (Opposite.op Y)
       simp[h1,h2,h3,d]
       exact a00
      have a1: (pb_prod0 D F X (m + 1)).app (Opposite.op Y) (t1, tm) = h1 k0 := by
       simp[h1,k0]

      let a2:= h2 (h1 k0)
      have e0 : h2 (h1 k0) = (h1 ≫ h2) k0 := by simp
      simp only [eq] at e0
      simp only [h3,k0] at e0
      simp only [f_succ] at e0
      have eid: (fst (X.obj d) ((npow X m).obj d)) = (fst (X.obj d) ((npow X m).obj d)) ≫ 𝟙 (X.obj d) := by simp
      rw[eid] at e0
      simp only[CategoryTheory.ChosenFiniteProducts.lift_fst_comp_snd_comp] at e0
      simp at e0

      let h1' := (pb_prod0 D F X m).app (Opposite.op Y)
      let h2' := f C (F.op ⋙ X) m (Opposite.op Y)

      let h3' := f D X m d
      have eq' : h1' ≫ h2' = h3' := by
       have a000 := pb_prob0_comm_lemma D F X m (Opposite.op Y)
       simp[h1',h2',h3',d]
       exact a000


      simp only[a1]
      have ff : (h1≫ h2) k0 = h2 (t1, (pb_prod0 D F X m).app (Opposite.op Y) tm) := by
       simp[k0]
       simp[e0]
       simp[h2,f_succ]
       have eid' : (fst (X.obj (Opposite.op (F.obj Y))) ((npow (F.op ⋙ X) m).obj (Opposite.op Y))) =
        (fst (X.obj (Opposite.op (F.obj Y))) ((npow (F.op ⋙ X) m).obj (Opposite.op Y)))≫ 𝟙 _ := by simp
       rw[eid']
       simp only[CategoryTheory.ChosenFiniteProducts.lift_fst_comp_snd_comp]
       simp []
       have al: f D X m d tm = h3' tm := by
        simp[h3']
       have a:f D X m d tm = f C (F.op ⋙ X) m (Opposite.op Y) ((pb_prod0 D F X m).app (Opposite.op Y) tm) := by
        simp[al]
        simp[← eq']
       simp[a]


       --simp[Prod.mk.inj_iff] why not work? qqqqq
      have iso2 : IsIso h2 := f_iso C (F.op ⋙ X) (m+1) (Opposite.op Y)
      have eee: (h2 ≫ inv h2)  = (𝟙 _ )  := by simp
      have eel: (h1 ≫ h2 ≫ inv h2) k0 = inv h2 ((h1 ≫ h2) k0 ) := by
        simp only [← Category.assoc]
        simp
      have ee: (h1 ≫ h2 ≫ inv h2) k0 = (h2 ≫ inv h2) (t1, (pb_prod0 D F X m).app (Opposite.op Y) tm):= by
        simp only [eel]
        simp at ff
        simp[ff]
      simp only [eee] at ee
      simp at ee
      exact ee



    theorem pb_prob_pointwise_inv (X : Psh D) n c : IsIso ((pb_prod0 D F X n).app c) := by
      let h1 := (pb_prod0 D F X n).app c
      let h2 := f C (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := f D X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, f, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod0 D F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod0, npair_nproj] at this
        simp [this, ev_map,pb_prod0 ]
      have iso2 : IsIso h2 := f_iso C (F.op ⋙ X) n c
      have iso3 : IsIso h3 := f_iso D X n d
      have iso12 : IsIso (h1 ≫ h2) := by rewrite [eq] ; assumption
      apply IsIso.of_isIso_comp_right h1 h2

    noncomputable
    def pb_prod (X : Psh D) (n : Nat) : F.op ⋙ npow X n ≅ npow (F.op ⋙ X) n :=
      NatIso.ofNatTrans (pb_prod0 D F X n) (pb_prob_pointwise_inv D F X n)


    theorem pb_prod0_pb_prod_hom (X : Psh D) (n : Nat):
     (pb_prod0 D F X n) = (pb_prod D F X n).hom := rfl

    noncomputable
    def pb_prod'  (n : Nat) : npow_functor n ⋙ (whiskeringLeft _ _ _).obj F.op ≅  (whiskeringLeft _ _ Type).obj F.op ⋙ npow_functor n :=
      NatIso.ofNatTrans (npow_oplax ((whiskeringLeft _ _ Type).obj F.op)) (by
        intros X
        simp [npow_oplax]
        have:= NatIso.ofNatTrans' (pb_prod0 D F X n) (pb_prob_pointwise_inv D F X n)
        simp [pb_prod0] at this
        exact this)
      -- NatIso.ofNatTrans (pb_prod0 D F X n) (pb_prob_pointwise_inv D F X n)

    theorem bin_prod_pointwise (X Y : Psh C) c : (X ⊗  Y).obj c = X.obj c ⊗ Y.obj c := rfl

    -- def ev  : Dᵒᵖ ⊗ Psh D ⥤ Type where
    --   obj := fun X => X.obj d
    --   map := fun f => f.app d

    -- def npow_fwd (n:Nat) (d : Dᵒᵖ) : ev D d ⋙ npow_functor n ⟶ npow_functor n ⋙ ev D d ≅  :=

    -- def npow_componentwise (n:Nat) (d : Dᵒᵖ) : npow_functor n ⋙ ev D d ≅ ev D d ⋙ npow_functor n :=

    -- (X : Psh D) d : (npow X n).obj d ≅ npow (X.obj d) n where

    -- def npow_componentwise (X : Psh D) d : (npow X n).obj d ≅ npow (X.obj d) n where
    --   hom := by sorry
    -- --   inv := by sorry


      -- induction n withF
      -- | zero => rfl
      -- | succ _ ih => simp [npow, ih, bin_prod_pointwise]

    -- theorem npow_componentwise (X : Psh D) : (npow X n).obj d = npow (X.obj d) n := by
    --   induction n withF
    --   | zero => rfl
    --   | succ _ ih => simp [npow, ih, bin_prod_pointwise]

    -- def pb_prod_inv (X : Psh D) (n : Nat) c : ((npow (F.op ⋙ X) n).obj c) → (F.op ⋙ npow X n).obj c:=
    --   fun fxn =>
    --   have y := npow_componentwise C (F.op ⋙ X) ▸ fxn
    --   npow_componentwise D X ▸ y

    -- noncomputable
    -- def pb_preserves_prod0 (X : Psh D) (n : Nat) c : (F.op ⋙ npow X n).obj c ≅ (npow (F.op ⋙ X) n).obj c where
    --   hom := (pb_prod D F X n).app c
    --   inv := pb_prod_inv D F X n c
    --   hom_inv_id := by
    --     simp [pb_prod, pb_prod_inv, npair, ]
    --     unfold pb_prod_inv
    --     sorry
    --   inv_hom_id := by
    --     funext fxn
    --     simp [CategoryStruct.comp, Function.comp, pb_prod_inv]; sorry

    -- noncomputable
    -- def pb_preserves_prod (X : Psh D) (n : Nat) : F.op ⋙ npow X n ≅ npow (F.op ⋙ X) n :=
    --   NatIso.ofComponents (pb_preserves_prod0 D F X n) (fun f => (pb_prod D F X n).naturality f)



    -- def pb_prod (X : Psh D) : (n : Nat) → npow (F.op ⋙ X) n ⟶ F.op ⋙ npow X n
    --   | .zero => ChosenFiniteProducts.toUnit _
    --   | .succ n => by
    --     constructor
    --     case app => intros ; simp [npow, bin_prod_pointwise]; exact (𝟙 _ ⊗ (pb_prod X n).app _)
    --     case naturality => intros c c' f; simp [npow] ; sorry
    --    --by simp [npow] sorry

    --  where
    --   app :=
    --   -- by simp [npow_componentwise] at fxn |- ; exact fxn
    --   naturality := by intros; simp; funext fxn; simp; sorry

      -- simp [npow_componentwise] at fxn; sorry



    -- First part, show that a functor F : C ⥤ D
    -- induces by precomposition, a functor
    -- F^* : T-Str(D) ⥤ T-Str(C)
    -- and this restricts to a functor
    -- F^* : T-Mod(D) ⥤ T-Mod(C)




    noncomputable
    def pb_obj (L : Str T.sig D) : Str T.sig C where
      carrier := F.op ⋙ L.carrier
      interp_ops := fun o =>
        let h := L.interp_ops o
        let h' := whiskerLeft F.op h
        (pb_prod D F _ _).inv ≫ h'
      interp_preds := fun p =>
        let h := L.interp_preds p
        let h' := whiskerLeft F.op h
        let h'' := h' ≫ pb_prop D F
        (pb_prod D F _ _).inv ≫ h''

     theorem pb_obj_carrier (L : Str T.sig D) :(pb_obj D F T L).carrier = F.op ⋙ L.carrier
     :=rfl
    theorem pb_obj_interp_preds (L : Str T.sig D)  (p: T.sig.preds):
       (pb_obj D F T L).interp_preds p =
       (pb_prod D F L.carrier (T.sig.arity_preds p)).inv ≫
       whiskerLeft F.op (L.interp_preds p) ≫ pb_prop D F := by

       simp[← Iso.inv_comp_eq]
       simp[pb_obj]


    theorem pb_prod_hom (X : Psh D) (n : Nat):
   (pb_prod D F X n).hom = (pb_prod0 D F X n) := rfl


    theorem nproj_pb_prod0 (X : Psh D)  (n: ℕ ) (i: Fin n):
   (pb_prod0 D F X n)≫ (nproj (F.op ⋙ X) n i) = (whiskerLeft F.op (nproj X n i)):= by
     ext c a
     simp[npair_nproj,pb_prod0 ]

     theorem nproj_pb_prod0_symm (X : Psh D) (n: ℕ ) (i: Fin n):
    (whiskerLeft F.op (nproj X n i)) = (pb_prod0 D F X n)≫ (nproj (F.op ⋙ X) n i) := by
     ext c a
     simp[npair_nproj,pb_prod0 ]

    instance nlift_whisker0 (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
    CategoryTheory.whiskerLeft F.op
    (nlift L₁ L₂ n k) ≫ (pb_prod D F L₂ n).hom =
    (pb_prod D F L₁ n).hom ≫ nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (fun i => CategoryTheory.whiskerLeft F.op (k i))
     := by
      apply npair_univ'
      intros i
      simp
      simp[nlift_nproj]
      simp[pb_prod_hom]
      simp[npair_nproj,pb_prod0 ]
      simp[← Category.assoc]
      simp[npair_nproj]
      simp[← CategoryTheory.whiskerLeft_comp]
      simp[nlift_nproj]

    theorem nlift_whisker  (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
    nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (fun i => CategoryTheory.whiskerLeft F.op (k i)) ≫
    (pb_prod D F L₂ n).inv =
    (pb_prod D F L₁ n).inv ≫
    CategoryTheory.whiskerLeft F.op
    (nlift L₁ L₂ n k) := by
      --why it does not work if I simplify the goal instead? QQQQQ

      have
      a:= nlift_whisker0 D F L₁ L₂ n k
      symm at a
      simp [← CategoryTheory.IsIso.eq_inv_comp] at a
      simp [a]

    def pb_map (L₁ L₂ : Str T.sig D) (f : L₁ ⟶ L₂) :
      pb_obj D F T L₁ ⟶ pb_obj D F T L₂ where
      map := whiskerLeft F.op f.map
      ops_comm := by
        intros o
        simp[pb_obj,← CategoryTheory.whiskerLeft_comp]
        simp[← f.ops_comm]
        simp[← Category.assoc]
        simp[nlift_diag,nlift_whisker]
      preds_comm := by
        intros o
        simp[pb_obj,← CategoryTheory.whiskerLeft_comp]
        simp[← f.preds_comm]
        simp[← Category.assoc]
        simp[nlift_diag,nlift_whisker]



    noncomputable
    def pullback : Str T.sig D ⥤ Str T.sig C where
      obj := pb_obj D F T
      map := pb_map D F T _ _



    theorem pb_obj_interp_ops (L : Str T.sig D)  (o: T.sig.ops):
       whiskerLeft F.op (L.interp_ops o) =
       (pb_prod D F L.carrier (T.sig.arity_ops o)).hom ≫ (pb_obj D F T L).interp_ops o := by

       simp[← Iso.inv_comp_eq]
       simp[pb_obj]


    theorem pb_obj_interp_ops0 (L : Str T.sig D)  (o: T.sig.ops):
       (pb_prod D F L.carrier (T.sig.arity_ops o)).inv ≫ whiskerLeft F.op (L.interp_ops o) =
       (pb_obj D F T L).interp_ops o := by
       simp[Iso.inv_comp_eq]
       simp[pb_obj]


    theorem pb_prod_pb_prod0  (X : Psh D) (n : Nat) :
     (pb_prod D F X n).hom = pb_prod0 D F X n := rfl

    theorem pb_npair_compatible (P : Psh D) (n : Nat) (k: Fin n → (X ⟶  P)):
     npair (F.op⋙ X) (F.op⋙ P) n (fun i => whiskerLeft F.op (k i)) ≫ (pb_prod D F P  n).inv  =
     whiskerLeft F.op (npair X P n k)
     := by
      simp[Iso.comp_inv_eq]
      apply npair_univ'
      intro i
      simp[npair_nproj]
      simp[pb_prod_pb_prod0]
      simp[nproj_pb_prod0]
      simp[← CategoryTheory.whiskerLeft_comp]
      simp[npair_nproj]

    theorem lift_app (X Y Z:Psh C) (f:X⟶ Y) (g:X⟶ Z) (c: Cᵒᵖ )
    (a : X.obj c):
    (ChosenFiniteProducts.lift f g).app c a =
    ⟨f.app c a, g.app c a⟩ := rfl--it should be somewhere in mathlib, cannot find it

    theorem whiskerLeft_lift (X Y Z:Psh D) (f:X⟶ Y) (g:X⟶ Z):
    CategoryTheory.whiskerLeft F.op
    (ChosenFiniteProducts.lift f g) =
    ChosenFiniteProducts.lift
    (CategoryTheory.whiskerLeft F.op f)
    (CategoryTheory.whiskerLeft F.op g) := by
     ext cop a
     simp[CategoryTheory.whiskerLeft_apply]
     simp[lift_app]

    theorem SubobjectClassifier.pb_prop_existQ (F: C⥤ D) {A B : Psh D} (p: A⟶ B) (φ: A ⟶ SubobjectClassifier.prop):
    whiskerLeft F.op (SubobjectClassifier.existQ p φ)  ≫ pb_prop D F =
    SubobjectClassifier.existQ (whiskerLeft F.op p) ((whiskerLeft F.op φ) ≫ pb_prop D F) := by
     ext c a
     simp
     ext Y f
     simp[SubobjectClassifier.existQ_app_arrows]
     simp[pb_prop]
     simp[SubobjectClassifier.existQ_app_arrows]



    theorem snd_app (X Y: Psh D)  (d: D)
    (t1: X.obj (Opposite.op d))
    (t2: Y.obj (Opposite.op d)):
    (snd X Y).app (Opposite.op d) (t1, t2) = t2 := rfl



    theorem SubobjectClassifier.pb_prop_existQ'  (f : fml T.sig (m + 1))
     (ih: CategoryTheory.whiskerLeft F.op (L.interp_fml f) ≫ pb_prop D F =
  (pb_prod D F L.carrier (m + 1)).hom ≫ (pb_obj D F T L).interp_fml f):
      whiskerLeft F.op (SubobjectClassifier.existπ (L.interp_fml f))  ≫ pb_prop D F  =
      (pb_prod D F L.carrier m).hom ≫ SubobjectClassifier.existπ ((pb_obj D F T L).interp_fml f) := by
      simp[SubobjectClassifier.existπ]

      simp[SubobjectClassifier.pb_prop_existQ]
      simp[ih]

      simp[pb_obj_carrier]
      ext c a
      simp[pb_prod_pb_prod0]
      ext Y g
      simp[SubobjectClassifier.existQ_app_arrows]
      constructor
      intros
      · rename_i h
        cases h
        rename_i w h
        cases h
        rename_i h1 h2
        cases w
        rename_i t1 tm
        simp [snd_app] at h1
        let a1:= ((pb_prod D F L.carrier m).hom).app _ tm
        exists  ⟨ t1,a1⟩
        simp
        constructor
        · simp[a1]
          simp[h1]
          simp[snd_app]
          simp[pb_prod_pb_prod0]
          have := (pb_prod0 D F L.carrier m).naturality g.op
          simp at this
          have hh : (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 D F L.carrier m).app c a) =
                  ((pb_prod0 D F L.carrier m).app (Opposite.op (Opposite.unop c)) ≫ (npow (F.op ⋙ L.carrier) m).map g.op) a :=
                    by
                     simp
          simp only[hh]
          simp only [← this]
          simp
        · simp[a1]
          simp[pb_prod_pb_prod0]
          have e : (t1, (pb_prod0 D F L.carrier m).app (Opposite.op Y) tm) =
           ((pb_prod0 D F L.carrier (m + 1)).app (Opposite.op Y) (t1, tm)) := by
            simp only[pb_prod0_pair]
          simp[e]
          exact h2
      intros
      · rename_i h
        cases h
        rename_i w h
        cases h
        rename_i h1 h2
        cases w
        rename_i t10 tm0
        simp [snd_app] at h1
        let a1:= ((pb_prod D F L.carrier m).inv).app _ tm0
        exists  ⟨ t10,a1⟩
        simp[snd_app]
        constructor
        · simp[a1]
          simp[h1]
          have e0:
          (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 D F L.carrier m).app c a) =
          (pb_prod D F L.carrier m).hom.app (Opposite.op Y)
           ((npow L.carrier m).map (F.map g).op a) := by
           simp[pb_prod_pb_prod0]
           have := (pb_prod0 D F L.carrier m).naturality g.op
           simp at this
           have hh : (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 D F L.carrier m).app c a) =
                  ((pb_prod0 D F L.carrier m).app (Opposite.op (Opposite.unop c)) ≫ (npow (F.op ⋙ L.carrier) m).map g.op) a := by simp
           simp only[hh]
           simp only [← this]
           simp
          simp[e0]
        · simp[a1]
          --simp[pb_prod_pb_prod0]
          have e : ((pb_prod0 D F L.carrier (m + 1)).app (Opposite.op Y)
        (t10, (pb_prod D F L.carrier m).inv.app (Opposite.op Y) tm0)) =
           (t10, tm0) := by
           simp
           simp only[pb_prod0_pair D F]
           have e1: (pb_prod0 D F L.carrier m).app (Opposite.op Y) ((pb_prod D F L.carrier m).inv.app (Opposite.op Y) tm0) =
                    ((pb_prod D F L.carrier m).inv ≫ pb_prod0 D F L.carrier m).app (Opposite.op Y) tm0 := by
                     simp[pb_prod0_pb_prod_hom]

           simp only[e1]
           have e11: (pb_prod D F L.carrier m).inv ≫ pb_prod0 D F L.carrier m = 𝟙 _ := by
            simp [pb_prod0_pb_prod_hom]
           simp only[e11]
           simp
          --sorry --may need to define the inverse by induction
          simp[e]
          exact h2





    def pb_prop_interp_tm (L : Str T.sig D)  (n : ℕ ) (t : tm T.sig n) :
      whiskerLeft F.op (L.interp_tm t) =
      (pb_prod D F _ n).hom ≫ (pb_obj D F T L).interp_tm t := by
        simp[← CategoryTheory.IsIso.inv_comp_eq]
        induction t with
        | var _ =>
          simp[Str.interp_tm]
          simp[Iso.inv_comp_eq]
          simp[pb_prod_pb_prod0]
          simp[nproj_pb_prod0_symm]
          simp[pb_obj]
        | op o a a_ih =>
          simp[Str.interp_tm]
          simp[pb_obj_interp_ops]
          simp[← Category.assoc]
          simp[← pb_obj_interp_ops0]
          simp[← a_ih]
          simp[npair_natural]
          simp[← Category.assoc]
          simp
          simp[pb_obj]
          simp[← Category.assoc]
          simp[pb_npair_compatible]

    def pb_prop_interp_fml (L : Str T.sig D) (φ : fml T.sig n) :
      whiskerLeft F.op (L.interp_fml φ) ≫ pb_prop D F =
      (pb_prod D F _ n).hom ≫ (pb_obj D F T L).interp_fml φ  := by
        induction φ with
        | pred p ts =>
           rename_i m
           #check Str.interp_fml (pb_obj D F T L) (fml.pred p ts)
           simp[Str.interp_fml]
           simp[pb_obj_interp_preds]
           simp[← pb_npair_compatible]
           simp[pb_prop_interp_tm]
           simp[npair_natural]
           simp[pb_obj]
        | true =>
          rename_i m
          --simp it does not do anything, why do not report error either?
          simp[Str.interp_fml]
          simp[SubobjectClassifier.pb_prop_top]
          simp[← Category.assoc]
          have a: CategoryTheory.whiskerLeft F.op (toUnit (npow L.carrier m)) =
            ((pb_prod D F L.carrier m).hom ≫ toUnit (npow (pb_obj D F T L).carrier m)) :=
             by
              apply toUnit_unique
          simp only [a]
        | false =>
          rename_i m
          simp[Str.interp_fml]
          simp[SubobjectClassifier.pb_prop_bot ]
          simp[← Category.assoc]
          have a: CategoryTheory.whiskerLeft F.op (toUnit (npow L.carrier m)) =
            ((pb_prod D F L.carrier m).hom ≫ toUnit (npow (pb_obj D F T L).carrier m)) :=
             by
              apply toUnit_unique
          simp only [a]
        | conj f1 f2 ih1 ih2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[SubobjectClassifier.pb_prop_conj]
          have a:
          CategoryTheory.whiskerLeft F.op (ChosenFiniteProducts.lift (L.interp_fml f1) (L.interp_fml f2)) ≫
          (pb_prop D F ⊗ pb_prop D F) =
          (pb_prod D F L.carrier m).hom ≫
    ChosenFiniteProducts.lift ((pb_obj D F T L).interp_fml f1) ((pb_obj D F T L).interp_fml f2)
          := by
            apply hom_ext
            · simp only[Category.assoc]
              simp only[tensorHom_fst]
              simp only[lift_fst]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_fst]
              simp[ih1]

            · simp only[Category.assoc]
              simp only[tensorHom_snd]
              simp only[lift_snd]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_snd]
              simp[ih2]

          simp[← Category.assoc]
          simp[a]

        | disj f1 f2 ih1 ih2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[SubobjectClassifier.pb_prop_disj]
          have a:
          CategoryTheory.whiskerLeft F.op (ChosenFiniteProducts.lift (L.interp_fml f1) (L.interp_fml f2)) ≫
          (pb_prop D F ⊗ pb_prop D F) =
          (pb_prod D F L.carrier m).hom ≫
    ChosenFiniteProducts.lift ((pb_obj D F T L).interp_fml f1) ((pb_obj D F T L).interp_fml f2)
          := by
            apply hom_ext
            · simp only[Category.assoc]
              simp only[tensorHom_fst]
              simp only[lift_fst]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_fst]
              simp[ih1]

            · simp only[Category.assoc]
              simp only[tensorHom_snd]
              simp only[lift_snd]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_snd]
              simp[ih2]

          simp[← Category.assoc]
          simp[a]
        | infdisj _ _ => sorry
        | eq t1 t2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[SubobjectClassifier.pb_prop_eq]
          simp[whiskerLeft_lift]
          simp[pb_prop_interp_tm]
          simp[← comp_lift]
        | existsQ f ih =>
          rename_i m
          simp
          simp[Str.interp_fml]
          --simp[SubobjectClassifier.existπ]
          have := SubobjectClassifier.pb_prop_existQ' D F T f ih
          exact this
         -- simp[SubobjectClassifier.existQ]





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
