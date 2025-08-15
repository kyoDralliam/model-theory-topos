import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Images

open CategoryTheory Limits

universe u v w

namespace CategoryTheory

section

variable (κ : Type w) (C : Type u) [Category.{v} C]

class Regular extends HasFiniteLimits C, Limits.HasStrongEpiMonoFactorisations C where
  strongIsRegular {X Y : C} (f : X ⟶ Y) : StrongEpi f → EffectiveEpi f
  RegularStable {X Y Y' S : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y}
    {h : Y' ⟶ X} (sq : IsPullback f' h g f) (hg : RegularEpi g) : RegularEpi h

attribute [instance] Regular.strongIsRegular Regular.RegularStable

class Geometric extends Regular C where
  has_false (X : C) : HasInitial (Subobject X)
  has_joins_subobject (X : C) (I : Set κ) : HasCoproductsOfShape I (Subobject X)
  isJoin_isStableUnderBaseChange {Y X : C} (f : Y ⟶ X) {I : Set κ} (fP : I → Subobject X) :
    ∐ (fun (i : I) ↦ (Subobject.pullback f).obj (fP i)) = (Subobject.pullback f).obj (∐ fP)

attribute [instance] Geometric.has_false Geometric.has_joins_subobject
attribute [simp] Geometric.isJoin_isStableUnderBaseChange

abbrev Coherent := Geometric C Bool

end

namespace Geometric

variable {κ : Type w} {C : Type u} [Category.{v} C]
variable [geo : Geometric κ C]

def emptymap (X : C) : Set.Elem (fun (_ : κ) ↦ False) → Subobject X := fun i ↦ by
  obtain ⟨val, property⟩ := i
  have := property.out
  simp_all only

noncomputable def initialSubobject (X : C) : Subobject X :=
  let empty : Set κ := ∅
  ∐ (fun (i : empty) ↦ by
  obtain ⟨val, property⟩ := i
  simp_all only [Set.mem_empty_iff_false, empty])

def initialHom {X : C} (m : Subobject X) : initialSubobject (κ := κ) X ⟶ m := by
  constructor
  constructor
  sorry

instance (X : C) : HasInitial (Subobject X) := by
  let myEmpty : Set κ := ∅
  let f : myEmpty → Subobject X := fun i ↦ by aesop
  sorry

instance (X : C) : OrderBot (Subobject X) := by sorry

-- Show
instance (X : C) : HasBinaryProducts (Subobject X) := by sorry


-- instance geoHasFiniteProducts (X : C) : HasFiniteProducts (Subobject X) := sorry

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

end CategoryTheory.Geometric
