import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Images

open CategoryTheory Limits

universe u v w

namespace CategoryTheory

variable (κ : Type w) (C : Type u) [Category.{v} C]

class Regular where
  hasFiniteLimits : HasFiniteLimits C := by infer_instance
  hasStrongEpiMonoFactorizations : Limits.HasStrongEpiMonoFactorisations C := by
    infer_instance
  strongIsRegular {X Y : C} (f : X ⟶ Y) : StrongEpi f → EffectiveEpi f
  RegularStable {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {h : Y' ⟶ X} (sq : IsPullback f' h g f) (hg : RegularEpi g) : RegularEpi h

attribute [instance] Regular.hasFiniteLimits
  Regular.hasStrongEpiMonoFactorizations Regular.strongIsRegular

class Geometric where
  hasFiniteLimits : HasFiniteLimits C := by infer_instance
  hasStrongEpiMonoFactorizations : HasStrongEpiMonoFactorisations C :=
    by infer_instance
  isRegular : Regular C := by infer_instance
  hasFalse (X : C) : HasInitial (Subobject X)
  hasJoins (X : C) : HasCoproductsOfShape κ (Subobject X)

attribute [instance] Geometric.isRegular Geometric.hasFalse Geometric.hasJoins

abbrev Coherent := Geometric C Bool

variable [geo : Geometric κ C]
instance geoHasFiniteProducts (X : C) : HasFiniteProducts (Subobject X) := sorry

end CategoryTheory
