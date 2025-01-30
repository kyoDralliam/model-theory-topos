import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Cat
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic
import ModelTheoryTopos.Category.Presheaf
import ModelTheoryTopos.Category.InterpretGeometricPresheaf
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Functor.Category
-- Keep this file as main example

section SemigroupExample

def semigroup_sig : monosig where
  ops := Unit
  arity_ops := fun _ => 2
  preds := Empty
  arity_preds := Empty.rec


abbrev mk_mul (t1 t2: tm semigroup_sig n) : tm semigroup_sig n :=
 .op () (fun i => [t1 , t2][i])


abbrev mk_mul_left (t1 t2 t3: tm semigroup_sig n) := mk_mul (mk_mul t1 t2) t3

abbrev mk_mul_right (t1 t2 t3: tm semigroup_sig n) := mk_mul t1 (mk_mul t2 t3)

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



 def Type_Psh : Type  ⥤ CategoryTheory.Psh Unit where
  obj a := Type_to_Psh a
  map f := {
    app _ := f
  }

theorem Type_Psh_obj (α : Type) : (Type_Psh.obj α)= Type_to_Psh α := rfl
theorem Type_Psh_map {α β : Type} (f: α → β) : (Type_Psh.map f).app (Opposite.op ())  = f := rfl

def Psh_Type:  CategoryTheory.Psh Unit ⥤ Type where
  obj P := P.obj (Opposite.op ())
  map f := f.app (Opposite.op ())

theorem Psh_Type_obj (P: Psh Unit) : Psh_Type.obj P = P.obj (Opposite.op ()) := rfl
theorem Psh_Type_map {P1 P2: Psh Unit} (f: P1 ⟶ P2) : Psh_Type.map f = f.app (Opposite.op ()) := rfl


open CategoryTheory.Functor


theorem Unit_id {X Y: Unit} (f: X ⟶  Y) : f = 𝟙 () :=rfl

theorem Unit_op_id {X Y: Unitᵒᵖ } (f: X ⟶  Y) : f = 𝟙 (Opposite.op ()) :=rfl

def Psh_itself_to_Type_Psh (P: Psh Unit) : P ⟶ Type_Psh.obj (Psh_Type.obj P) where
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

def Type_Psh_to_Psh_itself (P: Psh Unit) : Type_Psh.obj (Psh_Type.obj P) ⟶ P where
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

def Psh_itself_iso_Type_Psh (P: Psh Unit) : P ≅ Type_Psh.obj (Psh_Type.obj P) :=
  NatIso.ofNatTrans_pt_inv (Psh_itself_to_Type_Psh P) (fun _ => 𝟙 _)
  (by intros c;simp[Psh_itself_to_Type_Psh_app P])


def eta_from_Psh_Unit : 𝟭 (Psh Unit) ⟶ Psh_Type ⋙ Type_Psh where
  app P := Psh_itself_to_Type_Psh P


def Type_equiv_Psh_eta' : 𝟭 (CategoryTheory.Psh Unit) ≅
  Psh_Type ⋙ Type_Psh :=
  NatIso.ofNatTrans_pt_inv eta_from_Psh_Unit
  Type_Psh_to_Psh_itself
  (by intros P; ext ; simp only [id_obj, comp_obj, eta_from_Psh_Unit, FunctorToTypes.comp,
    Psh_itself_to_Type_Psh_app P, types_id_apply, Type_Psh_to_Psh_itself_app P, NatTrans.id_app])


-- KM: you can simplify probably simplify this code with NatIso.ofComponents or NatIso.ofNatTrans


def Type_equiv_Psh_epsilpon: 𝟭 Type ≅
  Type_Psh ⋙ Psh_Type  where
    hom := {
      app a := 𝟙 a
       }
    inv := {
      app a := 𝟙 a
    }

def Type_equiv_Psh : CategoryTheory.Psh Unit ≌ Type   :=
 CategoryTheory.Equivalence.mk Psh_Type Type_Psh Type_equiv_Psh_eta' Type_equiv_Psh_epsilpon


noncomputable
def Semigroup_Str (α : Type) [Semigroup α] :
 InterpPsh.Str semigroup_sig Unit :=
 {
      carrier := Type_to_Psh α
      interp_ops o := {
        app _ p :=
          let x : α := p.1
          let y : α := p.2.1
          x * y
      }
      interp_preds := by
        intro p
        cases p
    }


noncomputable
def semigroup_to_model (α : Type) [Semigroup α]
  : semigroup_set_models where
  str := Semigroup_Str α
  valid := by
    simp only [semigroup_thy, assoc, Fin.isValue, List.mem_singleton, InterpPsh.Str.model,
      SubobjectClassifier.prop.eq_1, forall_eq, InterpPsh.Str.interp_fml, InterpPsh.Str.interp_tm,
      Fin.getElem_fin, SubobjectClassifier.eq, Opposite.op_unop]
    rintro _ ⟨a , b , c, _⟩ _ _ _ _
    simp
    apply mul_assoc (G:=α) a b c






def model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul a1 a2:= by
    exact (m.str.interp_ops ()).app ⟨()⟩ ⟨ a1, a2, () ⟩
  mul_assoc := by
    intros a b c
    have := m.valid assoc (by simp only [semigroup_thy, List.mem_singleton]) ⟨()⟩ ⟨ a, b, c , () ⟩ (𝟙 _) ⟨⟩
    simp only [assoc, Fin.isValue, SubobjectClassifier.prop.eq_1, InterpPsh.Str.interp_fml,
      InterpPsh.Str.interp_tm, SubobjectClassifier.eq, Opposite.op_unop, FunctorToTypes.comp,
      ChosenFiniteProducts.lift_app_pt, op_id, FunctorToTypes.map_id_apply] at this
    apply this


end SemigroupExample

section MonoidExample
def monoid_sig : monosig where
  ops := Fin 2
  arity_ops := (fun i => [0 , 2][i])
  preds := Empty
  arity_preds := Empty.rec


abbrev Monoid.mk_mul (t1 t2: tm monoid_sig n) : tm monoid_sig n :=
 .op (1: Fin 2) (fun i => [t1 , t2][i])


abbrev Monoid.mk_mul_left (t1 t2 t3: tm monoid_sig n) := Monoid.mk_mul (Monoid.mk_mul t1 t2) t3

abbrev Monoid.mk_mul_right (t1 t2 t3: tm monoid_sig n) := Monoid.mk_mul t1 (Monoid.mk_mul t2 t3)

def Monoid.assoc : sequent monoid_sig where
  ctx := 3
  premise := .true
  concl := fml.eq (Monoid.mk_mul_left (.var 0) (.var 1) (.var 2)) (Monoid.mk_mul_right (.var 0) (.var 1) (.var 2))


abbrev Monoid.unit n: tm monoid_sig n := .op (0: Fin 2) Fin.elim0

def Monoid.idL : (sequent monoid_sig) where
  ctx := 1
  premise := fml.true
  concl := fml.eq (Monoid.mk_mul (Monoid.unit 1) (.var 0)) (.var 0)

def Monoid.idR : (sequent monoid_sig) where
  ctx := 1
  premise := fml.true
  concl := fml.eq (.var 0) (Monoid.mk_mul (Monoid.unit 1) (.var 0))



def monoid_thy : theory where
  sig := monoid_sig
  axioms := [ Monoid.assoc ,Monoid.idL ,Monoid.idR]

instance : CategoryTheory.Category (Fin 2) := inferInstance
instance : CategoryTheory.Category (Fin n) := inferInstance
instance : PartialOrder (Fin n) := inferInstance

def Monoid_2_models :=
  InterpPsh.Mod monoid_thy (Fin 2)

def invertible (m: tm monoid_sig (n + 1)) := fml.existsQ (fml.eq (Monoid.mk_mul (.var 0) m) m)

def idempotent (m: tm monoid_sig n) := fml.eq (Monoid.mk_mul m m) m

def is_id (m: tm monoid_sig n) := fml.eq m (Monoid.unit n)

def test (m: tm monoid_sig n) : sequent monoid_sig where
  ctx := n
  premise := fml.conj (invertible (tm.ren SyntacticSite.R.in10 m)) (idempotent m)
  concl := is_id m

def Monoid_hom_as_Psh [Monoid M1] [Monoid M2] (h: M1 ⟶ M2) : CategoryTheory.Psh (Fin 2) :=
  let f : CategoryTheory.ComposableArrows Typeᵒᵖ 1 := .mk₁ (Opposite.op h)
  f.leftOp


-- def Monoid_hom_as_Psh [Monoid M1] [Monoid M2] (h: M1 ⟶ M2) : CategoryTheory.Psh (Fin 2) where
--   obj x := (fun i => [M1, M2][i]) (Opposite.unop x)
--   map f := sorry
--   map_id := sorry
--   map_comp := sorry

def Monoid_hom_to_Monoid_2_models [Monoid M1] [Monoid M2] (h: M1 ⟶ M2) : Monoid_2_models where
  str := {
    carrier := Monoid_hom_as_Psh h
    interp_ops := sorry
    interp_preds := sorry
  }
  valid := sorry


def Monoid_2_models_to_Monoid_hom (M : Monoid_2_models):
   M.str.carrier.obj (Opposite.op (1:Fin 2)) ⟶
   M.str.carrier.obj (Opposite.op (0:Fin 2)) := sorry








end MonoidExample
