
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.Category

abbrev CategoryTheory.Psh (C:Type) [Category C] := Functor Cᵒᵖ Type
