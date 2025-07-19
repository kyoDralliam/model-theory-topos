import Mathlib.Data.Matrix.Notation
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

open CategoryTheory Limits

namespace Signature

structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  arity : Symbols → ℕ
  sortedArity : (f : Symbols) → Fin (arity f) → Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols

namespace SortedSymbols.Symbols

abbrev arity {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.arity x
abbrev sortedArity {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) :=
  X.sortedArity x

end SortedSymbols.Symbols

structure SortedSymbolsWOutput (Sorts : Type*) extends SortedSymbols Sorts where
  codomain : Symbols → Sorts

attribute [coe] SortedSymbolsWOutput

instance {Sorts} : CoeSort (SortedSymbolsWOutput Sorts) Type* where
  coe X := X.Symbols

abbrev SortedSymbols.Symbols.codomain
    {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) : Sorts :=
  X.codomain x

end Signature

structure Signature where
  Sorts : Type*
  Functions : Signature.SortedSymbolsWOutput Sorts
  Relations : Signature.SortedSymbols Sorts

instance : CoeSort Signature Type* where
  coe := Signature.Sorts
