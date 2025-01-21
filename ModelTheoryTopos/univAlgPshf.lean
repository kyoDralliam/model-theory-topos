import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Cat
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic
import ModelTheoryTopos.Category.Presheaf
import ModelTheoryTopos.Category.InterpretGeometricPresheaf

-- Keep this file as main example

section SemigroupExample

def semigroup_sig : monosig where
  ops := sorry
  arity_ops := sorry
  preds := sorry
  arity_preds := sorry

def semigroup_thy : theory where
  sig := semigroup_sig
  axioms := [ sorry ]

def semigroup_set_models :=
  InterpPsh.Mod semigroup_thy Unit

def semigroup_to_model (α : Type) [Semigroup α]
  : semigroup_set_models where
  str := {
      carrier := sorry
      interp_ops := sorry
      interp_preds := sorry
    }
  valid := sorry

def model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul := sorry
  mul_assoc := sorry

end SemigroupExample
