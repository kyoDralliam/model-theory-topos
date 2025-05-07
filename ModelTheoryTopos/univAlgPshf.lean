import Mathlib.Algebra.Group.Defs
import Mathlib.CategoryTheory.Category.Cat
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic
import ModelTheoryTopos.Category.Presheaf
import ModelTheoryTopos.Category.InterpretGeometricPresheaf
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.CategoryTheory.Opposites


import Mathlib.Algebra.Category.Semigrp.Basic

open CategoryTheory
-- Keep this file as main example

abbrev ot := Opposite.op ()

section TypePshUnitEquiv
def Type_to_Psh (α : Type) :
  CategoryTheory.Psh Unit where
  obj _ := α
  map _ := 𝟙 _

open CategoryTheory



 def Type_Psh : Type  ⥤ CategoryTheory.Psh Unit where
  obj a := Type_to_Psh a
  map f := {app _ := f}

theorem Type_Psh_obj (α : Type) : (Type_Psh.obj α)= Type_to_Psh α := rfl
theorem Type_Psh_map {α β : Type} (f: α → β) : (Type_Psh.map f).app (Opposite.op ())  = f := rfl

def Psh_Type:  CategoryTheory.Psh Unit ⥤ Type where
  obj P := P.obj ot
  map f := f.app ot

theorem Psh_Type_obj (P: Psh Unit) : Psh_Type.obj P = P.obj ot := rfl
theorem Psh_Type_map {P1 P2: Psh Unit} (f: P1 ⟶ P2) : Psh_Type.map f = f.app ot := rfl


open CategoryTheory.Functor


theorem Unit_id {X Y: Unit} (f: X ⟶ Y) : f = 𝟙 () :=rfl

theorem Unit_op_id {X Y: Unitᵒᵖ } (f: X ⟶ Y) : f = 𝟙 ot :=rfl

def Psh_itself_to_Type_Psh (P: Psh Unit) : P ⟶ Type_Psh.obj (Psh_Type.obj P) where
  app _ := 𝟙 _
  naturality := by
    intros X Y f
    simp [Type_Psh_obj, Type_to_Psh, Psh_Type_obj, Unit_op_id, P.map_id ot]

theorem Psh_itself_to_Type_Psh_app (P: Psh Unit) :
  (Psh_itself_to_Type_Psh P).app _ = 𝟙 _ := rfl

def Type_Psh_to_Psh_itself (P: Psh Unit) : Type_Psh.obj (Psh_Type.obj P) ⟶ P where
  app _ := 𝟙 _
  naturality := by
    intro X Y f
    simp [Type_Psh_obj, Type_to_Psh, Psh_Type_obj, Unit_op_id, P.map_id ot]

theorem Type_Psh_to_Psh_itself_app (P: Psh Unit) :
  (Type_Psh_to_Psh_itself P).app _ = 𝟙 _ := rfl

def Psh_itself_iso_Type_Psh (P: Psh Unit) : P ≅ Type_Psh.obj (Psh_Type.obj P) :=
  NatIso.ofNatTrans_pt_inv (Psh_itself_to_Type_Psh P) (fun _ => 𝟙 _)
  (by intros c;simp[Psh_itself_to_Type_Psh_app P])


def eta_from_Psh_Unit : 𝟭 (Psh Unit) ⟶ Psh_Type ⋙ Type_Psh where
  app P := Psh_itself_to_Type_Psh P


def Type_equiv_Psh_eta' : 𝟭 (CategoryTheory.Psh Unit) ≅
  Psh_Type ⋙ Type_Psh :=
  NatIso.ofNatTrans_pt_inv
    eta_from_Psh_Unit
    Type_Psh_to_Psh_itself
    (by
      intros P; ext
      simp only [id_obj, comp_obj, eta_from_Psh_Unit, FunctorToTypes.comp, Psh_itself_to_Type_Psh_app P, types_id_apply, Type_Psh_to_Psh_itself_app P, NatTrans.id_app])

lemma Type_equiv_Psh_eta'.hom : Type_equiv_Psh_eta'.hom = eta_from_Psh_Unit := rfl

lemma Type_equiv_Psh_eta'.inv (P: Psh Unit): Type_equiv_Psh_eta'.inv.app P = Type_Psh_to_Psh_itself P := rfl

#check NatIso.ofComponents
#check NatIso.ofNatTrans
#check NatIso.ofNatTrans_pt_inv
-- KM: you can simplify probably simplify this code with NatIso.ofComponents or NatIso.ofNatTrans


def Type_equiv_Psh_epsilpon: 𝟭 Type ≅ Type_Psh ⋙ Psh_Type  where
    hom := 𝟙 _
    inv := 𝟙 _

def Type_equiv_Psh : CategoryTheory.Psh Unit ≌ Type   :=
 .mk Psh_Type Type_Psh Type_equiv_Psh_eta' Type_equiv_Psh_epsilpon

section TypePshUnitEquiv



section SemigroupExample


-- An empty universe instance,
-- we do not need any "large" disjunctions for the equational theory of semigroups
local
instance empty : SmallUniverse where
  U := Empty
  El := Empty.rec

-- The signature of semigroups
def semigroup_sig : monosig where
  ops := Unit -- A single operation for multiplication
  arity_ops := fun _ => 2 -- multiplication is binary
  preds := Empty -- no predicate
  arity_preds := Empty.rec

abbrev mk_mul (t1 t2: tm semigroup_sig n) : tm semigroup_sig n :=
 .op () (fun i => [t1 , t2][i])

def assoc : @sequent empty semigroup_sig where
  ctx := 3
  premise := .true
  concl :=
    let x := .var 0
    let y := .var 1
    let z := .var 2
    .eq (mk_mul (mk_mul x y) z) (mk_mul x (mk_mul y z))

-- The theory of semigroups
def semigroup_thy : theory where
  sig := semigroup_sig
  axioms := [ assoc ]

-- We automatically obtain a category of models in presheaves over any category
-- in particular over the terminal category
def semigroup_set_models :=
  InterpPsh.Mod semigroup_thy Unit

instance Unit_cat : Category Unit := inferInstance

instance semigrp_cat : Category semigroup_set_models := @InterpPsh.Mod_Category _ _ _ _


-- This category of models over the terminal category is equivalent
-- to the category of semigroups which we show below

-- First, we define a functor from semigroups to models over 1

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
      interp_preds := Empty.rec
    }

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

def Semigrp2Model : Semigrp ⥤ semigroup_set_models where
  obj sg := @semigroup_to_model sg.carrier sg.str
  map {sg1 sg2} h:= {
    map := Type_Psh.map h.hom'.toFun
    ops_comm _ := by
      ext
      apply (h.hom'.map_mul' _ _ ).symm
    preds_comm := Empty.rec
  }


-- Second, we define a functor from models over 1 to semigroups

instance model_to_semigroup (m : semigroup_set_models)
  : Semigroup (m.str.carrier.obj ⟨⟨⟩⟩) where
  mul a1 a2:=  (m.str.interp_ops ()).app ⟨()⟩ ⟨ a1, a2, () ⟩
  mul_assoc a b c := by
    have := m.valid assoc (by simp only [semigroup_thy, List.mem_singleton]) ⟨()⟩ ⟨ a, b, c , () ⟩ (𝟙 _) ⟨⟩
    simp only [assoc, InterpPsh.Str.interp_fml, InterpPsh.Str.interp_tm, SubobjectClassifier.eq, FunctorToTypes.comp,
      ChosenFiniteProducts.lift_app_pt, op_id, FunctorToTypes.map_id_apply ] at this
    exact this

open ChosenFiniteProducts in
def Model2Semigrp: semigroup_set_models ⥤ Semigrp where
  obj := fun m => Semigrp.of (m.str.carrier.obj ⟨⟨⟩⟩)
  map {X Y} f := Semigrp.ofHom {
      toFun := f.map.app ot
      map_mul' x1 x2 := by
        symm
        exact congr_fun (congr_app (f.ops_comm ()) ot) (x1, (x2, ()))
    }

-- Third, we show that the composition of these functors is naturally
-- isomorphic to the identity

def Model2Semigrp_to_Semigrp2Model : Model2Semigrp ⋙ Semigrp2Model ⟶ 𝟭 semigroup_set_models where
  app m := {
      map := Type_Psh_to_Psh_itself m.str.carrier
      ops_comm := by
        intro ()
        ext
        rfl
      preds_comm := Empty.rec
    }

def Model2Semigrp2Model_itself (m : semigroup_set_models) :
  m ⟶ (Model2Semigrp ⋙ Semigrp2Model).obj m where
  map := {
    app _ := 𝟙 _
    naturality {X Y } _ := by
      simp [Unit_op_id, m.str.carrier.map_id ot, (Semigrp2Model.obj (Model2Semigrp.obj m)).str.carrier.map_id ot]
  }
  ops_comm := by
    intro
    ext
    rfl
  preds_comm := Empty.rec

def Model2Semigrp_Semigrp2Model_equiv :
  Model2Semigrp ⋙ Semigrp2Model ≅ 𝟭 semigroup_set_models :=
  NatIso.ofNatTrans_pt_inv Model2Semigrp_to_Semigrp2Model Model2Semigrp2Model_itself

def Semigrp2Model_to_Model2Semigrp : Semigrp2Model ⋙ Model2Semigrp ⟶ 𝟭 Semigrp where
  app m := 𝟙 m

def Semigrp2Model2Semigrp_itself (m : Semigrp) : m ⟶ (Semigrp2Model ⋙ Model2Semigrp ).obj m := 𝟙 m

def Semigrp2Model_Model2Semigrp_equiv :
  Semigrp2Model ⋙Model2Semigrp ≅ 𝟭 Semigrp :=
  NatIso.ofNatTrans_pt_inv Semigrp2Model_to_Model2Semigrp Semigrp2Model2Semigrp_itself

-- Finally we obtain the equivalence

def Semigrp_equiv_model : semigroup_set_models ≌ Semigrp   :=
  .mk Model2Semigrp Semigrp2Model Model2Semigrp_Semigrp2Model_equiv.symm Semigrp2Model_Model2Semigrp_equiv

end SemigroupExample


-- TODO: Do we need to keep what's below ?

section MonoidExample
variable [SmallUniverse]
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

def Monoid_hom_as_Psh {M1 M2:Type} (h: M1 →  M2) : CategoryTheory.Psh (Fin 2) :=
  let f : CategoryTheory.ComposableArrows Typeᵒᵖ 1 := .mk₁ (Opposite.op h)
  f.leftOp


-- def Monoid_hom_as_Psh [Monoid M1] [Monoid M2] (h: M1 ⟶ M2) : CategoryTheory.Psh (Fin 2) where
--   obj x := (fun i => [M1, M2][i]) (Opposite.unop x)
--   map f := sorry
--   map_id := sorry
--   map_comp := sorry
open CategoryTheory MonoidalCategory
#check 𝟙_ (Psh (Fin 2))

def terminal_n_rep : 𝟙_ (Psh (Fin (n + 1))) ≅ yoneda.obj n where
  hom := {
    app k a := by
      simp[yoneda]
      rcases k.unop with ⟨ k,p⟩
      have p':k <= n := by
        simp[Nat.lt_add_one_iff] at p
        assumption
      exact homOfLE p'
  }
  inv := {
    app k a := by
     exact ()
  }

noncomputable
def mk_gs2 {M1 M0:Type} [Monoid M1] [Monoid M0] (m1:M1) (h: M1 →* M0) :
𝟙_ (Psh (Fin 2)) ⟶ Monoid_hom_as_Psh h.toFun :=
 let y := (@CategoryTheory.yonedaEquiv (Fin 2) _ (1:Fin 2) (Monoid_hom_as_Psh h.toFun)).invFun m1
 let y': 𝟙_ (Psh (Fin 2)) ⟶ yoneda.obj 1 := (@terminal_n_rep 1).hom
 y' ≫ y

-- open Group Monoid
-- def mk_gs2 {M1 M2:Type} [Monoid M1] [Monoid M2] (m1:M1) (m2:M2) (h: M1 →* M2) (p: h.toFun m1 = m2) : 𝟙_ (Psh (Fin 2)) ⟶ Monoid_hom_as_Psh h.toFun := sorry
--𝟙_ (Psh (Fin 2)) ⟶

noncomputable
def Monoid_hom_to_Monoid_2_models [Monoid M1] [Monoid M2] (h: M1 →* M2) : Monoid_2_models where
  str := {
    carrier := Monoid_hom_as_Psh h
    interp_ops o := match o with
     | ⟨ 0 ,_ ⟩ => mk_gs2 1 h  --just need h 1 = 1
     | ⟨ 1 ,_ ⟩ => {
       app n := sorry
       naturality := sorry
     }
    interp_preds := sorry
    }
  valid := sorry


def Monoid_2_models_to_Monoid_hom (M : Monoid_2_models):
   M.str.carrier.obj (Opposite.op (1:Fin 2)) ⟶
   M.str.carrier.obj (Opposite.op (0:Fin 2)) := sorry








end MonoidExample
