import ModelTheoryTopos.Syntax.GeometricLogic.Defs
import ModelTheoryTopos.Syntax.GeometricLogic.Hilbert
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
import ModelTheoryTopos.Syntax.GeometricLogic.SyntacticCategory

open CategoryTheory Limits
namespace ClassifyingTopos

variable [SmallUniverse] {m: theory} (J: GrothendieckTopology (fmlInCtx m))  {C : Type u} [Category.{v} C]
[HasFiniteLimits C] [HasFiniteColimits C]


namespace Giraud

/-
https://www.math.ias.edu/~lurie/278xnotes/Lecture10-Giraud.pdf

Lurie's notion of covering seems to be rather easy to formulate
-/
#check Category

structure familyTo (X: C) where
 index : SmallUniverse.U
 maps: SmallUniverse.El index -> Over X

instance : HasCoproducts C := sorry
--#check ∐
structure coverOn (X: C) where
 index : SmallUniverse.U
 maps: SmallUniverse.El index -> Over X
 cover : CategoryTheory.EffectiveEpi (Limits.Sigma.desc (fun (i: SmallUniverse.El index) => (maps i).hom))

/-
limits, colimits, images + compatible with base change, small generating set
-/

/-
for each object in c, choose a cover on c whose domains are in X
-/


class smallGen where
 index : SmallUniverse.U
 genObj: SmallUniverse.El index → C
 cover (c: C) : coverOn c
 inGeneratingSet (c: C) (i : SmallUniverse.El (cover c).index): ∃ (i₀: SmallUniverse.El index), genObj i₀ = ((cover c).maps i).left

class GiraudConditions where
  hasFiniteLimits : HasFiniteLimits C
  hasFinitecoLimits : HasFiniteColimits C
  smallGenerated : @smallGen _ C _


--def GiraudInterp (φ: fml m.sig n) :


end Giraud


end ClassifyingTopos
