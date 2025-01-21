import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Cat
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic
import ModelTheoryTopos.Category.Presheaf
import ModelTheoryTopos.Category.InterpretGeometricPresheaf

-- Keep this file as main example

section SemigroupExample

def semigroup_sig : monosig where
  ops := Unit
  arity_ops := fun _ => 2
  preds := Empty
  arity_preds := Empty.rec




--def sg_unit n: tm semigroup_sig n := .op false Fin.elim0

-- def idL : (sequent semigroup_sig) where
--   ctx := 1
--   premise := fml.true
--   concl := fml.eq (.op true (fun i => if i = (0: Fin 1) then sg_unit 1 else .var 0)) (.var 0)

-- def idR : (sequent semigroup_sig) := sorry

def mk_mul (t1 t2: tm semigroup_sig n) : tm semigroup_sig n :=
 .op () (fun i => if i = (0: Fin 2) then t1 else t2)

def mk_mul_left (t1 t2 t3: tm semigroup_sig n) := mk_mul (mk_mul t1 t2) t3

def mk_mul_right (t1 t2 t3: tm semigroup_sig n) := mk_mul t1 (mk_mul t2 t3)

def assoc : sequent semigroup_sig where
  ctx := 3
  premise := .true
  concl := fml.eq (mk_mul_left (.var 0) (.var 1) (.var 2)) (mk_mul_right (.var 0) (.var 1) (.var 2))


def semigroup_thy : theory where
  sig := semigroup_sig
  axioms := [ assoc ]

def semigroup_set_models :=
  InterpPsh.Mod semigroup_thy Unit


def Semigroup_to_Psh (α : Type) [Semigroup α] :
  CategoryTheory.Psh Unit where
  obj _ := α
  map := sorry

def semigroup_to_model (α : Type) [Semigroup α]
  : semigroup_set_models where
  str := {
      carrier := {
        obj _ := α
        map := fun
          | .op unop => sorry
      }
      interp_ops := sorry
      interp_preds := sorry
    }
  valid := sorry

def model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul := sorry
  mul_assoc := sorry

end SemigroupExample
