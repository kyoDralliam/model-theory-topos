--This should probably be at CategoryTheory/Limits/Skeleton.lean

import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# (Co)limits of the skeleton of a category

The skeleton of a category inherits all (co)limits the category has. Note however that a thin
skeleton may fail to be complete, even when the corresponding category is complete; because
the homtypes of the skeleton live in a different universe (the same as the objects).
^ TODO: Consider making a PR changing that
-/


section

open CategoryTheory ThinSkeleton

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ w w'
variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {D : Type u₃} [Category.{v₃} D]
variable (F : D ⥤ C) (skF : IsSkeletonOf C D F)

-- Skeletons
instance hasLimitsOfShape_skeleton [HasLimitsOfShape J C] : HasLimitsOfShape J (Skeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromSkeleton C)

instance hasLimitsOfSize_skeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w,w'} (Skeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromSkeleton C)

instance hasLimits_skeleton [HasLimits C] : HasLimits (Skeleton C) := by infer_instance

instance hasColimitsOfShape_skeleton [HasColimitsOfShape J C] : HasColimitsOfShape J (Skeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromSkeleton C)

instance hasColimitsOfSize_skeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w,w'} (Skeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromSkeleton C)

instance hasColimits_skeleton [HasColimits C] : HasColimits (Skeleton C) := by infer_instance

variable [Quiver.IsThin C]
instance hasLimitsOfShape_thinSkeleton [HasLimitsOfShape J C] :
    HasLimitsOfShape J (ThinSkeleton C) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (fromThinSkeleton C)

instance hasLimitsOfSize_thinSkeleton [HasLimitsOfSize.{w, w'} C] :
    HasLimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasLimits_of_hasLimits_createsLimits (fromThinSkeleton C)

instance hasColimitsOfShape_thinSkeleton [HasColimitsOfShape J C] :
    HasColimitsOfShape J (ThinSkeleton C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (fromThinSkeleton C)

instance hasColimitsOfSize_thinSkeleton [HasColimitsOfSize.{w, w'} C] :
    HasColimitsOfSize.{w, w'} (ThinSkeleton C) :=
  hasColimits_of_hasColimits_createsColimits (fromThinSkeleton C)

-- This should be added to Skeletal.lean, in fact that should probably be split in two;
-- Skeletal.lean and ThinSkeleton.lean and
def ThinSkeleton.mk (c : C) : ThinSkeleton C := @Quotient.mk' C (isIsomorphicSetoid C) c

end CategoryTheory.Limits
