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

-- The equalizer of <f1,1> and <g1:1> : Z -> X×Z is the equalizer of f1 and g1.
def EqualizerSmth :
  IsLimit (Fork.ofι (f := f1) (g := f2) (equalizer.ι (prod.lift f1 (𝟙 Z)) (prod.lift f2 (𝟙 Z))) (by sorry)) := sorry

def EqualizerIso :
  equalizer (prod.lift f1 (𝟙 Z)) (prod.lift f2 (𝟙 Z)) ≅ equalizer f1 f2 := sorry

lemma Equalizer_eq :
  (EqualizerIso f1 f2).hom ≫ equalizer.ι f1 f2 =
    equalizer.ι (prod.lift f1 (𝟙 Z)) (prod.lift f2 (𝟙 Z)) := sorry

lemma Equalizer_eq' :
  (EqualizerIso f1 f2).inv ≫ equalizer.ι (prod.lift f1 (𝟙 Z)) (prod.lift f2 (𝟙 Z)) =
    equalizer.ι f1 f2 := sorry

-- noncomputable def equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g)
--     (equalizer.condition f g)) :=
