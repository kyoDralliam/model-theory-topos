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
  | prod {n : ℕ} : (Fin n → Sorts) → DerivedSorts Sorts

instance {Sorts : Type*} : Coe Sorts (DerivedSorts Sorts) where
  coe A := DerivedSorts.prod (n := 1) (fun _ ↦ A)

structure SortedSymbols (Sorts : Type*) where
  Symbols : Type*
  arity : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbols.Symbols

instance {Sorts : Type*} : CoeSort (SortedSymbols Sorts) Type* where
  coe := SortedSymbols.Symbols

namespace SortedSymbols.Symbols

abbrev arity {Sorts : Type*} {X : SortedSymbols Sorts} (x : X) := X.arity x

end SortedSymbols.Symbols

structure SortedSymbolsWOutput (Sorts : Type*) extends SortedSymbols Sorts where
  codomain : Symbols → DerivedSorts Sorts

attribute [coe] SortedSymbolsWOutput

instance {Sorts} : CoeSort (SortedSymbolsWOutput Sorts) Type* where
  coe X := X.Symbols

abbrev SortedSymbols.Symbols.codomain
    {Sorts : Type*} {X : SortedSymbolsWOutput Sorts} (x : X) : DerivedSorts Sorts :=
  X.codomain x

end Signature

structure Signature where
  Sorts : Type*
  Functions : Signature.SortedSymbolsWOutput Sorts
  Relations : Signature.SortedSymbols Sorts

instance : CoeSort Signature Type* where
  coe := Signature.Sorts

abbrev Signature.derivedSorts (S : Signature) := DerivedSorts S.Sorts
