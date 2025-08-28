import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {Z X Y : C} (f1 f2 : Z ⟶ X) (g1 g2 : Z ⟶ Y)

def equalizerProdLiftIso :
  equalizer (prod.lift f1 g1) (prod.lift f2 g2) ≅ pullback (equalizer.ι f1 f2) (equalizer.ι g1 g2) :=
  sorry

def equalizerProdLiftIsoFst :
  equalizer (prod.lift f1 g1) (prod.lift f2 g2) ⟶ equalizer f1 f2 := sorry

def equalizerProdLiftIsoSnd :
  equalizer (prod.lift f1 g1) (prod.lift f2 g2) ⟶ equalizer g1 g2 := sorry

lemma equalizerProdLiftIso.hom_fst {Z X Y : C} (f1 f2 : Z ⟶ X) (g1 g2 : Z ⟶ Y) :
  (equalizerProdLiftIso f1 f2 g1 g2).hom ≫ pullback.fst (equalizer.ι f1 f2) (equalizer.ι g1 g2) =
    equalizerProdLiftIsoFst f1 f2 g1 g2 :=
  sorry

lemma equalizerProdLiftIso.hom_snd {Z X Y : C} (f1 f2 : Z ⟶ X) (g1 g2 : Z ⟶ Y) :
  (equalizerProdLiftIso f1 f2 g1 g2).hom ≫ pullback.snd (equalizer.ι f1 f2) (equalizer.ι g1 g2) =
    equalizerProdLiftIsoSnd f1 f2 g1 g2 :=
  sorry

-- Another possible proof is as follows:
-- 1. Given maps f1, f2: C → A and g1,g2 : C → B, the equalizer of the maps CxC → AxB is the
-- product of the equalizers (this is just interchange of limits).
-- 2. The pullback of a map fxg:AxB -> CxD along ⟨h1,h2⟩:E -> CxD is the pullback of h1*f and h2*g.
-- 3. The result follows from the previous by factorizing C -> AxB as C -> CxC -> AxB.
theorem equalizerProdLift_isPullback :
    IsPullback
      (equalizerProdLiftIsoFst f1 f2 g1 g2)
      (equalizerProdLiftIsoSnd f1 f2 g1 g2)
      (equalizer.ι f1 f2)
      (equalizer.ι g1 g2) :=
  IsPullback.of_iso_pullback ⟨sorry⟩
    (equalizerProdLiftIso f1 f2 g1 g2)
    (equalizerProdLiftIso.hom_fst f1 f2 g1 g2)
    (equalizerProdLiftIso.hom_snd f1 f2 g1 g2)
