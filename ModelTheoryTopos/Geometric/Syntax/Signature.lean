import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Signatures

In this file, we define (multisorted, finitary, non-dependent) signatures. These consist of a type
of sorts, a type of function symbols and a type of relation symbols.
-/

open CategoryTheory Limits

namespace Signature

/--
The type of derived sorts, i.e. those that are tuples (or tuples of tuples, etc.) of the original
type of sorts.
-/
inductive DerivedSorts (Sorts : Type*) where
  | inj : Sorts → DerivedSorts Sorts
  | prod {n : ℕ} : (Fin n → DerivedSorts Sorts) → DerivedSorts Sorts

instance {Sorts : Type*} : Coe Sorts (DerivedSorts Sorts) where
  coe A := DerivedSorts.inj A

/--
A type of sorted symbols over a type `Sorts` of sorts consist of a type of symbols, together with
a function specifying the domain of each symbol, which should be a derived sort of `Sorts`.
-/
structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  domain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols

/-- The domain of a sorted symbol. -/
abbrev SortedSymbols.Symbols.domain
  {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.domain x

/--
A type of sorted symbols with output contains the data of a `SortedSymbol` but also specifies a
codomain for each symbol.
-/
structure SortedSymbolsWOutput (Sorts : Type*) extends SortedSymbols Sorts where
  codomain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbolsWOutput

instance {Sorts} : CoeSort (SortedSymbolsWOutput Sorts) Type* where
  coe X := X.toSortedSymbols

/-- The codomain of a sorted symbol. -/
abbrev SortedSymbols.Symbols.codomain
  {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) :
  DerivedSorts Sorts := X.codomain x

end Signature

/-- A signature consists of sorts, function symbols (with output) and relation symbols. -/
structure Signature where
  Sorts : Type*
  Functions : Signature.SortedSymbolsWOutput Sorts
  Relations : Signature.SortedSymbols Sorts

instance : CoeSort Signature Type* where
  coe S := Signature.DerivedSorts S.Sorts
