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
 .op () (fun i => [t1 , t2][i])--(fun i => if i = (0: Fin 2) then t1 else t2)
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

theorem Type_Psh_obj (α : Type) : (Type_Psh.obj α)= Type_to_Psh α := rfl
theorem Type_Psh_map {α β : Type} (f: α → β) : (Type_Psh.map f).app (Opposite.op ())  = f := rfl

instance Psh_Type:  CategoryTheory.Psh Unit ⥤ Type where
  obj P := P.obj (Opposite.op ())
  map f := f.app (Opposite.op ())

--@simp?
theorem Psh_Type_obj (P: Psh Unit) : Psh_Type.obj P = P.obj (Opposite.op ()) := rfl
theorem Psh_Type_map {P1 P2: Psh Unit} (f: P1 ⟶ P2) : Psh_Type.map f = f.app (Opposite.op ()) := rfl

--𝟙 identity morphism
--id identity function
--𝟭 identity functor

open CategoryTheory.Functor
#check NatIso.ofComponents
#check NatIso.ofNatTrans


theorem Unit_id {X Y: Unit} (f: X ⟶  Y) : f = 𝟙 () :=rfl

theorem Unit_op_id {X Y: Unitᵒᵖ } (f: X ⟶  Y) : f = 𝟙 (Opposite.op ()) :=rfl

instance Psh_itself_to_Type_Psh (P: Psh Unit) : P ⟶ Type_Psh.obj (Psh_Type.obj P) where
  app _ := 𝟙 _
  naturality := by
   intros X Y f
   simp_all only [Category.comp_id, Category.id_comp]
   simp only [Type_Psh_obj, Type_to_Psh]
   simp only [Unit_op_id] at *
   have := map_id P (Opposite.op ())
   simp only [this]
   rfl

theorem Psh_itself_to_Type_Psh_app (P: Psh Unit) :
  (Psh_itself_to_Type_Psh P).app _ = 𝟙 _ := rfl

instance Type_Psh_to_Psh_itself (P: Psh Unit) : Type_Psh.obj (Psh_Type.obj P) ⟶ P where
  app _ := 𝟙 _
  naturality := by
    intro X Y f
    simp_all only [Category.comp_id, Category.id_comp,Type_Psh_obj,Type_to_Psh]
    simp only [Unit_op_id] at *
    have := map_id P (Opposite.op ())
    simp only [this]
    rfl

theorem Type_Psh_to_Psh_itself_app (P: Psh Unit) :
  (Type_Psh_to_Psh_itself P).app _ = 𝟙 _ := rfl

instance Psh_itself_iso_Type_Psh (P: Psh Unit) : P ≅ Type_Psh.obj (Psh_Type.obj P) :=
  NatIso.ofNatTrans_pt_inv (Psh_itself_to_Type_Psh P) (fun _ => 𝟙 _)
  (by intros c;simp[Psh_itself_to_Type_Psh_app P])
  --(by intros c; simp[Psh_itself_to_Type_Psh_app P,Type_Psh_to_Psh_itself_app P])

#check Psh_itself_iso_Type_Psh
instance eta_from_Psh_Unit : 𝟭 (Psh Unit) ⟶ Psh_Type ⋙ Type_Psh where
  app P := Psh_itself_to_Type_Psh P

-- instance Type_equiv_Psh_eta'' : Psh_Type ⋙ Type_Psh  ≅ 𝟭 (CategoryTheory.Psh Unit) :=
--  NatIso.ofNatTrans_pt_inv sorry sorry sorry sorry


instance Type_equiv_Psh_eta' : 𝟭 (CategoryTheory.Psh Unit) ≅
  Psh_Type ⋙ Type_Psh :=
  NatIso.ofNatTrans_pt_inv eta_from_Psh_Unit
  Type_Psh_to_Psh_itself
  (by intros P; ext ; simp[Psh_itself_to_Type_Psh_app P,Type_Psh_to_Psh_itself_app P,eta_from_Psh_Unit])


-- KM: you can simplify probably simplify this code with NatIso.ofComponents or NatIso.ofNatTrans

instance Type_equiv_Psh_eta0: 𝟭 (CategoryTheory.Psh Unit) ≅
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
 CategoryTheory.Equivalence.mk Psh_Type Type_Psh Type_equiv_Psh_eta' Type_equiv_Psh_epsilpon

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

-- theorem interp_fml_assoc_concl :
--  InterpPsh.Str.interp_fml L
--   (fml.eq (mk_mul_left (.var 0) (.var 1) (.var 2)) (mk_mul_right (.var 0) (.var 1) (.var 2))) =

#check top_le_iff -- wrong one, is there a correct one...?

--(fun i => [t1 , t2][i])
theorem interp_tm_mul_left (m : semigroup_set_models):
 m.str.interp_tm (mk_mul_left t1 t2 t3) =
 let f1 := (ChosenFiniteProducts.npair _ _ _
   (fun i => [ChosenFiniteProducts.nproj _ _ (0:Fin 3),ChosenFiniteProducts.nproj _ _ (1:Fin 3)][i])) ≫ m.str.interp_ops ()
 (ChosenFiniteProducts.npair _ _ _
   (fun i => [f1,ChosenFiniteProducts.nproj _ _ (2:Fin 3)][i])) ≫ m.str.interp_ops () := sorry



theorem top_le_iff1 {X: Psh Unit} {a: X ⟶ SubobjectClassifier.prop}: ⊤ <= a →  a = ⊤ := sorry

def mul_on_model (m : semigroup_set_models) :
  m.str.carrier.obj (Opposite.op ()) ×
  m.str.carrier.obj (Opposite.op ()) → m.str.carrier.obj (Opposite.op ()) :=
  fun p =>
   let mul' :
    m.str.carrier.obj (Opposite.op PUnit.unit) × m.str.carrier.obj (Opposite.op PUnit.unit) × _ →
    m.str.carrier.obj (Opposite.op PUnit.unit) :=  (m.str.interp_ops ()).app (Opposite.op ())
   mul' ⟨ p.1, ⟨ p.2, ()⟩⟩

theorem mul_on_model_assoc (m : semigroup_set_models) (a1 a2 a3: m.str.carrier.obj (Opposite.op ())) :
  mul_on_model m ⟨ mul_on_model m ⟨a1,a2⟩,a3⟩  = mul_on_model m ⟨ a1,mul_on_model m ⟨a2,a3⟩⟩ := sorry

def model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul a1 a2:= mul_on_model m ⟨a1,a2⟩
  mul_assoc := by
    have := m.valid assoc
    simp only [semigroup_thy, List.mem_singleton, forall_const,InterpPsh.Str.model,assoc,InterpPsh.Str.interp_fml.eq_2] at *
    have := top_le_iff1 this
    set it1 := (m.str.interp_tm (mk_mul_left (tm.var 0) (tm.var 1) (tm.var (2: Fin 3))))
    set it2 := (m.str.interp_tm (mk_mul_right (tm.var 0) (tm.var 1) (tm.var (2: Fin 3))))
    have h1 := (@InterpPsh.BaseChange.interp_tm_eq Unit _ _ 3 m.str _ _).mp this
    intros a b c
    --have hml: a * b * c = mul_on_model m ⟨ mul_on_model m ⟨a,b⟩,c⟩ :=
    -- have h1 := Iff.mpr  (top_le_iff1 (ChosenFiniteProducts.npow m.str.carrier 3 ⟶ SubobjectClassifier.prop) sorry sorry
    --   (ChosenFiniteProducts.lift it1 it2 ≫ SubobjectClassifier.eq))

    sorry

end SemigroupExample
