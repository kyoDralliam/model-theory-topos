import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic

import Mathlib
open CategoryTheory

structure Model (m : monosig) (C: Type) [Category C] where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx
