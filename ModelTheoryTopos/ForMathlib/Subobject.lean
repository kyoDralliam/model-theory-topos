import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe v u
variable {C : Type u} [Category.{v} C]

-- We should replace HasPullbacks by `HasPullback f g` and make everything precise
instance hasBinaryProducts_of_subobject (X : C) [HasPullbacks C] :
    HasBinaryProducts (Subobject X) := by sorry

-- WARNING: I'm not sure this is true, as the the homs of `Subobject X` live in an unnecessarily
-- high universe, currently. If this is a problem then this should be renamed.
instance hasProducts_of_subobject (X : C) [HasLimits C] :
    HasProducts (Subobject X) := by sorry

instance hasProducts_of_subobject' (X : C) [HasFiniteLimits C] :
    HasFiniteProducts (Subobject X) := by sorry

@[simp]
lemma pullback_product {X Y : C} (a b : Subobject Y) (f : X ⟶ Y) [HasPullbacks C] :
  (Subobject.pullback f).obj (a ⨯ b) =
    ((Subobject.pullback f).obj a ⨯ (Subobject.pullback f).obj b) := by
  sorry

instance skeletal_subobject (X : C) : Skeletal (Subobject X) := ThinSkeleton.skeletal

instance thin_subobject (X : C) : Quiver.IsThin (Subobject X) := by infer_instance

noncomputable def subobject_comp {X Y : C} (m : Subobject X) (f : X ⟶ Y) [Mono f] : Subobject Y :=
  Subobject.mk (m.arrow ≫ f)

noncomputable def underlying_obj_subobject_comp {X Y : C} (m : Subobject X) (f : X ⟶ Y) [Mono f] :
    underlying.obj (m.subobject_comp f) ≅ underlying.obj m := by
  simp [subobject_comp]
  apply underlyingIso

noncomputable def underlying_obj_pullback [HasPullbacks C]
    {X Y : C} (m : Subobject X) (f : Y ⟶ X) [Mono f] :
    underlying.obj ((pullback f).obj m) ≅ Limits.pullback m.arrow f := by sorry

@[simp]
lemma subobject_equalizer' {X Y : C} {f g : X ⟶ Y} (p : f = g) [HasEqualizer f g] :
    Subobject.mk (equalizer.ι f g) = ⊤ := by
  have := equalizer.ι_of_eq p
  apply mk_eq_top_of_isIso

@[simp]
lemma subobject_equalizer {X Y : C} (f : X ⟶ Y) : Subobject.mk (equalizer.ι f f) = ⊤ :=
  subobject_equalizer' rfl

variable [HasPullbacks C] {X Y Z : C} (f g : X ⟶ Y) [HasEqualizer f g]

@[simp]
lemma pullback_equalizer (h : Z ⟶ X) [HasEqualizer (h ≫ f) (h ≫ g)] :
  Subobject.mk (equalizer.ι (h ≫ f) (h ≫ g)) =
    ((Subobject.pullback h).obj <| Subobject.mk (equalizer.ι f g)) := by
  sorry

end CategoryTheory.Subobject
