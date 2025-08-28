import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import ModelTheoryTopos.ForMathlib.Skeleton
import ModelTheoryTopos.ForMathlib.Equalizer

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe v u
variable {C : Type u} [Category.{v} C]

-- We should replace HasPullbacks by `HasPullback f g` and make everything precise
instance hasBinaryProducts_of_subobject (X : C) [HasPullbacks C] :
    HasBinaryProducts (Subobject X) := by
  have : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  have : HasBinaryProducts (MonoOver X) := by
    apply CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits
    -- I want the specific limit I know of, not an arbitrary one
    intro F c hc j
    constructor
    intro X g h eq
    sorry
  apply hasLimitsOfShape_thinSkeleton

-- WARNING: I'm not sure this is true, as the the homs of `Subobject X` live in an unnecessarily
-- high universe, currently. If this is a problem then this should be renamed.
-- instance hasProducts_of_subobject (X : C) [HasLimits C] :
--     HasProducts (Subobject X) := by sorry

instance hasTerminal_of_monoOver (X : C) : HasTerminal (MonoOver X) := by
  -- apply CategoryTheory.Limits.hasLimitsOfShape_of_closedUnderLimits
  sorry

instance hasTerminal_of_subobject (X : C) : HasTerminal (Subobject X) := by
  apply hasLimitsOfShape_thinSkeleton

instance hasProducts_of_subobject' (X : C) [HasFiniteLimits C] :
  HasFiniteProducts (Subobject X) := hasFiniteProducts_of_has_binary_and_terminal

lemma product_is_pullback {X : C} (a b : Subobject X) [HasPullbacks C] :
    (a ⨯ b) = .mk (pullback.fst a.arrow b.arrow ≫ a.arrow) :=
  sorry


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

noncomputable def underlyingObjPullback [HasPullbacks C]
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

variable [HasFiniteLimits C] {Z X Y : C} (f1 f2 : Z ⟶ X) (g1 g2 : Z ⟶ Y)

lemma equalierProdMap' [HasPullbacks C] :
  Subobject.mk (equalizer.ι (prod.lift f1 g1) (prod.lift f2 g2)) =
    ((Subobject.mk (equalizer.ι f1 f2)) ⨯ (Subobject.mk (equalizer.ι g1 g2))) := by
  rw [product_is_pullback]
  apply mk_eq_mk_of_comm
  · sorry
  · refine equalizerProdLiftIso f1 f2 g1 g2 ≪≫ ?_
    sorry


end CategoryTheory.Subobject
