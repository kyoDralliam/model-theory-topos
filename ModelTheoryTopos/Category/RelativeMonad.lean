import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types

open CategoryTheory


class RelativeMonad {C D} [Category C] [Category D] (ι : C ⥤ D) (F : C → D) where
  ret : (x : C) → ι.obj x ⟶ F x
  bind : {x y : C} → (ι.obj x ⟶ F y) → (F x ⟶ F y)
  lunit : forall x, bind (ret x) = 𝟙 _
  runit : forall {x y} (f : ι.obj x ⟶ F y), ret _ ≫ bind f = f
  assoc : forall {x y z}
    (f : ι.obj x ⟶ F y) (g : ι.obj y ⟶ F z),
    bind (f ≫ bind g) = bind f ≫ bind g


namespace RelativeMonad

  variable {C D} [Category C] [Category D] {ι : C ⥤ D} {F : C → D} (r : RelativeMonad ι F)

  -- TODO: Can we have an automatic coercion from RelativeMonads to Functor ?
  instance functor : C ⥤ D where
    obj := F
    map := fun f => bind (ι.map f ≫ ret _)
    map_id := fun x => by simp [lunit]
    map_comp := fun f g => by rw [<-assoc] ; simp [runit]


  -- TODO: link with the standard defs of naturality
  theorem ret_natural {x y} (f : x ⟶ y) :
    ι.map f ≫ r.ret _ = r.ret _ ≫ r.functor.map f := by
    simp [functor]; rw [r.runit]

  theorem bind_natural {x x' y y'} (f : x' ⟶ x) (g : ι.obj x ⟶ F y) (h : y ⟶ y') :
    r.bind (ι.map f ≫ g ≫ r.functor.map h) = r.functor.map f ≫ r.bind g ≫ r.functor.map h := by
    simp [functor] ; rw [<-Category.assoc, r.assoc,
      <-Category.assoc, <-(r.assoc _ g), Category.assoc, r.runit]

  class Algebra {A} [Category A] (H : A ⥤ D) where
    alg : {x : C} → {a : A} → (ι.obj x ⟶ H.obj a) → (F x ⟶ H.obj a)
    alg_unit : ret _ ≫ alg f = f
    alg_bind : bind f ≫ alg g = alg (f ≫ alg g)
    alg_natural :
      alg (ι.map f ≫ g ≫ H.map h) = r.functor.map f ≫ alg g ≫ H.map h

  namespace Algebra
    def free : Algebra r r.functor where
      alg := bind
      alg_unit := by simp [runit]
      alg_bind := by simp [assoc]
      alg_natural := by simp [bind_natural]
  end Algebra

  def kl {C D} [Category C] [Category D] {ι : C ⥤ D} {F : C → D} (_ : RelativeMonad ι F) := C
  def to_kl : C → r.kl := fun x => x

  instance kleisli : Category (kl r) where
    Hom := fun x y => ι.obj x ⟶ F y
    id := ret
    comp := fun f g => f ≫ bind g
    id_comp := by simp [runit]
    comp_id := by simp [lunit]
    assoc := by simp [assoc]

  def kleisli.free : C ⥤ kl r where
    obj := id
    map := fun {x y} f =>
      let h := ι.map f ≫ r.ret y
      h
    map_id := by simp [CategoryStruct.id]
    map_comp := by simp [CategoryStruct.comp, runit]

  def kleisli.forgetful : kl r ⥤ D where
    obj := F
    map := bind
    map_id := by simp [CategoryStruct.id, lunit]
    map_comp := by simp [CategoryStruct.comp, assoc]

end RelativeMonad
