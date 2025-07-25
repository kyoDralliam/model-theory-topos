import ModelTheoryTopos.Syntax.GeometricLogic.Defs
import ModelTheoryTopos.Syntax.GeometricLogic.Hilbert
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
open CategoryTheory


instance : Limits.HasPushouts RenCtx := sorry
instance {x y z} (f: x ⟶ y) (g: x⟶ z) : @Limits.HasPushout RenCtx _ x y z f g := sorry

open Limits pushout

variable [SmallUniverse]

@[ext]
  structure fmlInCtx (m : theory) where
    ctx : RenCtx
    formula : fml m.sig ctx

  @[ext]
  structure fmlMap (xφ yψ : fmlInCtx m) where
    map : yψ.ctx ⟶ xφ.ctx
    preserves_formula : xφ.formula ⊢ yψ.formula.ren map


  def idMap (xφ : fmlInCtx m) : fmlMap xφ xφ where
    map := 𝟙 xφ.ctx
    preserves_formula := by
      simp [fml.ren_id]
      apply Hilbert.proof.var

  def compMap {xφ yψ zξ : fmlInCtx m}  (g : fmlMap xφ yψ) (f : fmlMap yψ zξ)
    : fmlMap xφ zξ where
    map := f.map ≫ g.map
    preserves_formula := by
      simp [fml.ren_comp]
      apply Hilbert.proof.cut g.preserves_formula f.preserves_formula.ren



  instance categoryStruct : CategoryStruct (fmlInCtx m) where
    Hom := fmlMap
    id := idMap
    comp := compMap

  instance (X : fmlInCtx m) : Inhabited (X ⟶ X) :=
  ⟨𝟙 X⟩

  instance : Category (fmlInCtx m) where
    toCategoryStruct := categoryStruct
    -- Hom := fmlMap
    -- id := idMap
    -- comp := compMap

  @[ext]
  lemma fmlMap_eq  (xφ yψ : fmlInCtx m) (f g: xφ⟶  yψ):
   f.map = g.map → f = g := by
   intro a
   simp[categoryStruct]
   ext
   assumption


  lemma fmlInCtx.map_comp {xφ yψ zξ : fmlInCtx m} (f :  xφ⟶  yψ) (g: yψ ⟶ zξ):
  (f ≫ g).map = g.map ≫ f.map := by
   dsimp[CategoryStruct.comp,compMap]

  lemma RenCtx.pushout_comm_sq {xφ yψ zξ: fmlInCtx m} (f :xφ ⟶ yψ)  (g: zξ ⟶ yψ) :
     f.map ≫ inl f.map g.map = g.map ≫ inr f.map g.map := by
     apply CategoryTheory.Limits.pushout.condition


  /-
  constructing the pullback in the syntactic category
  -/

  @[simps!]
  noncomputable
  def pullback_obj   {xφ yψ zξ : fmlInCtx m}  (f : xφ ⟶ yψ) (g: zξ ⟶ yψ) : fmlInCtx m where
    ctx := pushout f.map g.map
    formula := .conj (xφ.formula.ren (inl f.map g.map)) (zξ.formula.ren (inr f.map g.map))


  @[simp]
  noncomputable
  def pullback_fst  {xφ yψ zξ : fmlInCtx m}  (f :  xφ⟶  yψ) (g:  zξ⟶  yψ) :
     (pullback_obj f g) ⟶ xφ where
       map := inl f.map g.map
       preserves_formula := by
        simp[pullback_obj]
        apply Hilbert.proof.conj_elim_l

  @[simp]
  noncomputable
  def pullback_snd  {xφ yψ zξ : fmlInCtx m}  (f : xφ ⟶ yψ) (g: zξ ⟶ yψ) :
     pullback_obj f g ⟶ zξ where
       map := inr f.map g.map
       preserves_formula := by
        simp[pullback_obj]
        apply Hilbert.proof.conj_elim_r

  lemma fmlInCtx.pullback_comm_sq (f : xφ ⟶ yψ) (g: zξ ⟶ yψ):
     (pullback_fst f g) ≫ f = (pullback_snd f g) ≫ g := by
     ext
     simp[fmlInCtx.map_comp,RenCtx.pushout_comm_sq]

  --YX: It should hold in principle, but I am not sure whether it is needed. Should use to API instead of according to the def

  lemma pullback_isPullback :
   CategoryTheory.IsPullback (pullback_fst f g) (pullback_snd f g) f g := by
    sorry



class SmallUniverse.UniverseClosureProps [SmallUniverse] where
  uUnit : U
  utt : El uUnit
