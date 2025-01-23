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
 -- KM: simpler version .op () (fun i => [t1 , t2][i])

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


def Type_to_Psh (α : Type) :
  CategoryTheory.Psh Unit where
  obj _ := α
  map _ := id

open CategoryTheory



instance Type_Psh : Type  ⥤ CategoryTheory.Psh Unit where
  obj a := Type_to_Psh a
  map f := {
    app _ := f
  }


instance Psh_Type:  CategoryTheory.Psh Unit ⥤ Type where
  obj P := P.obj (Opposite.op ())
  map f := f.app (Opposite.op ())

--𝟙 identity morphism
--id identity function
--𝟭 identity functor

open CategoryTheory.Functor
-- KM: you can simplify probably simplify this code with NatIso.ofComponents or NatIso.ofNatTrans
instance Type_equiv_Psh_eta: 𝟭 (CategoryTheory.Psh Unit) ≅
  Psh_Type ⋙ Type_Psh where
    hom := {
      app P := {
        app := fun _ => 𝟙 _
          -- | .op unop => 𝟙 _
        naturality X Y f := by
         simp [] at *
         have : f = 𝟙 (Opposite.op ()) := rfl
         simp [this]
         have := map_id P (Opposite.op ())
         simp [this]
         rfl
      }
    }
    inv := {
      app P := {
        app _ := 𝟙 _
        naturality X Y f := by
         simp [] at *
         have : f = 𝟙 (Opposite.op ()) := rfl
         simp [this]
         have := map_id P (Opposite.op ())
         simp [this]
         rfl
      }
    }

instance Type_equiv_Psh_epsilpon: 𝟭 Type ≅
  Type_Psh ⋙ Psh_Type  where
    hom := {
      app a := 𝟙 a
       }
    inv := {
      app a := 𝟙 a
    }

instance Type_equiv_Psh : CategoryTheory.Psh Unit ≌ Type   :=
 CategoryTheory.Equivalence.mk Psh_Type Type_Psh Type_equiv_Psh_eta Type_equiv_Psh_epsilpon

open Semigroup
#check Semigroup.ext
#check Mul.mul

instance Type_to_Psh_npow (α : Type) (n : ℕ):
 Type_to_Psh (ChosenFiniteProducts.npow α n) ≅ ChosenFiniteProducts.npow (Type_to_Psh α) n :=
   sorry

#check Function.uncurry


instance times_npow_2 (α : Type)  : ChosenFiniteProducts.npow α 2 ≅ α × α := sorry

noncomputable
def semigroup_to_model (α : Type) [Semigroup α]
  : semigroup_set_models where
  str := {
      carrier := Type_to_Psh α
      interp_ops o := {
        app _ p :=
          let x : α := p.1
          let y : α := p.2.1
          x * y
      }
      interp_preds := sorry
    }
  valid := sorry


def model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul a1 a2:= by
    set mul := (m.str.interp_ops ()).app (Opposite.op ())
    let mul' : m.str.carrier.obj (Opposite.op PUnit.unit) × m.str.carrier.obj (Opposite.op PUnit.unit) × _ →
     m.str.carrier.obj (Opposite.op PUnit.unit) := mul
    exact mul' ⟨ a1, ⟨ a2, ()⟩ ⟩
    --(m.str.interp_ops ()).app (Opposite.op ()) ⟨ a1,a2 ⟩ sorry
  mul_assoc := sorry

end SemigroupExample
