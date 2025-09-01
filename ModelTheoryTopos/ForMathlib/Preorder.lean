--This should be added to CategoryTheory/Limits/Preorder.lean


import Mathlib.Order.Bounds.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory

namespace CategoryTheory.Limits

variable {J : Type u} [Category.{v} J]
variable {C : Type u₁} [Preorder C]

def functorOfSet (I : Set C) : Discrete I ⥤ C := Discrete.functor fun i ↦ i

@[simp]
lemma functorOfSet_obj {I : Set C} (i : Discrete I) : (functorOfSet I).obj i ∈ I := by
  simp [functorOfSet]

def setOfFunctor (F : J ⥤ C) : Set C := F.obj '' Set.univ

def coneOfLowerBound (I : Set C) (x : lowerBounds I) : Cone (functorOfSet I) where
  pt := x
  π := {
    app i := by
      simp; apply homOfLE;
      apply x.prop
      simp
  }

-- TODO: add docomentation on the .le and .hom functions
def lowerBoundOfCone (I : Set C) (c : Cone (functorOfSet I)) : lowerBounds I :=
  ⟨c.pt, fun i p ↦ (c.π.app ⟨i, p⟩).le⟩

def isGLB_IsLimit (I : Set C) (c : Cone (functorOfSet I)) (h : IsLimit c) : IsGLB I c.pt :=
  ⟨(lowerBoundOfCone I c).prop, fun i k ↦ (h.lift (coneOfLowerBound I ⟨i, k⟩)).le⟩

def IsLimitOfIsGLB (I : Set C) (c : Cone (functorOfSet I)) (h : IsGLB I c.pt) : IsLimit c where
  lift d := (h.2 (lowerBoundOfCone I d).prop).hom

-- Could be generalized: I : Type*, F : Discrete I ⥤ C, HasLimit F iff ∃ x, IsGLB (Set.range F.obj) x
lemma hasLimit_iff_hasGLB (I : Set C) : HasLimit (functorOfSet I) ↔ ∃ x, IsGLB I x := by
  constructor <;> intro h
  · let limitCone := getLimitCone (functorOfSet I)
    exact ⟨limitCone.cone.pt, isGLB_IsLimit I _ limitCone.isLimit⟩
  · obtain ⟨l, isGLB⟩ := h
    exact ⟨⟨⟨coneOfLowerBound I ⟨l, isGLB.1⟩, IsLimitOfIsGLB I _ isGLB⟩⟩⟩


-- For colimits
def coconeOfUpperBound (I : Set C) (x : upperBounds I) : Cocone (functorOfSet I) where
  pt := x
  ι := {
    app i := by
      simp; apply homOfLE;
      apply x.prop
      simp
  }

def upperBoundOfCocone (I : Set C) (c : Cocone (functorOfSet I)) : upperBounds I :=
  ⟨c.pt, fun i p ↦ (c.ι.app ⟨i, p⟩).le⟩

def isLUB_IsColimit (I : Set C) (c : Cocone (functorOfSet I)) (h : IsColimit c) : IsLUB I c.pt :=
  ⟨(upperBoundOfCocone I c).prop, fun i k ↦ (h.desc (coconeOfUpperBound I ⟨i, k⟩)).le⟩

def IsColimitOfIsLUB (I : Set C) (c : Cocone (functorOfSet I)) (h : IsLUB I c.pt) : IsColimit c where
  desc d := (h.2 (upperBoundOfCocone I d).prop).hom

lemma hasLimit_iff_hasLUB (I : Set C) : HasColimit (functorOfSet I) ↔ ∃ x, IsLUB I x := by
  constructor <;> intro h
  · let limitCocone := getColimitCocone (functorOfSet I)
    exact ⟨limitCocone.cocone.pt, isLUB_IsColimit I _ limitCocone.isColimit⟩
  · obtain ⟨l, isLUB⟩ := h
    exact ⟨⟨⟨coconeOfUpperBound I ⟨l, isLUB.1⟩, IsColimitOfIsLUB I _ isLUB⟩⟩⟩

end CategoryTheory.Limits
