import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Images

open CategoryTheory Limits

universe u v w

namespace CategoryTheory

variable (κ : Type w) (C : Type u) [Category.{v} C]

class Regular extends HasFiniteLimits C, Limits.HasStrongEpiMonoFactorisations C where
  strongIsRegular {X Y : C} (f : X ⟶ Y) : StrongEpi f → EffectiveEpi f
  RegularStable {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {h : Y' ⟶ X} (sq : IsPullback f' h g f) (hg : RegularEpi g) : RegularEpi h

attribute [instance] Regular.strongIsRegular Regular.RegularStable

class Geometric extends Regular C where
  hasFalse (X : C) : HasInitial (Subobject X)
  hasJoins (X : C) (I : Set κ) : HasCoproductsOfShape I (Subobject X)

attribute [instance] Geometric.hasFalse Geometric.hasJoins

abbrev Coherent := Geometric C Bool

variable [geo : Geometric κ C]

/- # TODO lemmas
After more stuff is added, most of these will not have to be even mentioned,
i.e. Lean should automatically infer the instances. See each instance for a
sketch of what should be added to Mathlib for this to be the case. -/

/-
F.C.: It seems to me that the "right" way to reason about the poset of
subobject is the following:
1. `Skeletal` should be a class on categories, and we should have that
   `Thin`+`Skeletal` induces a `PartialOrder`.
2. For a thin category, the proset it induces inherits the relevant structure,
   joins, wedges, exponentials, etc. (Sadly everything about joins, etc is
   stated for posets; so we may need to merge step 2 and 3)
3. This structure is preserved when the proset is a poset.
4. Show that the `ThinSkeleton` inherits colimits, etc
5. Show that the `ThinSkeleton` is `Thin` and `Skeletal`
6. From the previous, it should be automatically inferred that the poset of
   subobjects has the structure it should have.
-/

instance (X : C) : OrderBot (Subobject X) := by sorry

instance geoHasFiniteProducts (X : C) : HasFiniteProducts (Subobject X) := sorry

end CategoryTheory
