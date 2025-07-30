import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

open CategoryTheory Limits

namespace Signature

inductive DerivedSorts (Sorts : Type*) where
  | inj : Sorts → DerivedSorts Sorts
  | prod {n : ℕ} : (Fin n → DerivedSorts Sorts) → DerivedSorts Sorts

instance {Sorts : Type*} : Coe Sorts (DerivedSorts Sorts) where
  coe A := DerivedSorts.inj A

structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  domain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols


abbrev SortedSymbols.Symbols.domain
  {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.domain x

structure SortedSymbolsWOutput (Sorts : Type*) extends SortedSymbols Sorts where
  codomain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbolsWOutput

instance {Sorts} : CoeSort (SortedSymbolsWOutput Sorts) Type* where
  coe X := X.toSortedSymbols

abbrev SortedSymbols.Symbols.codomain
  {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) :
  DerivedSorts Sorts := X.codomain x

end Signature

structure Signature where
  Sorts : Type*
  Functions : Signature.SortedSymbolsWOutput Sorts
  Relations : Signature.SortedSymbols Sorts

instance : CoeSort Signature Type* where
  coe S := Signature.DerivedSorts S.Sorts
