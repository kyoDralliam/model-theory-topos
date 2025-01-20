import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Whiskering
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic
import ModelTheoryTopos.Category.ChosenFiniteProducts
import ModelTheoryTopos.Category.NatIso
import ModelTheoryTopos.Category.Presheaf

namespace InterpPsh
open CategoryTheory MonoidalCategory ChosenFiniteProducts

structure Str (S : monosig) (C : Type) [Category C]  where
  carrier : Psh C
  interp_ops : forall (o : S.ops), npow carrier (S.arity_ops o) ⟶ carrier
  interp_preds : forall (p : S.preds), npow carrier (S.arity_preds p) ⟶ SubobjectClassifier.prop

variable {C : Type} [Category C]

namespace Str


noncomputable
def interp_tm {S : monosig} (L : Str S C) : tm S n -> (npow L.carrier n ⟶ L.carrier)
  | .var k => nproj _ _ k
  | .op o k => (npair _ _ _ (fun i => L.interp_tm (k i))) ≫ L.interp_ops o

noncomputable
def interp_subst (L : Str S C) {n m : Subst S} (σ : n ⟶ m) : npow L.carrier m ⟶ npow L.carrier n :=
  npair (npow L.carrier m) L.carrier n (fun i => L.interp_tm (σ i))

@[simp]
theorem interp_tm_op {S : monosig} (L : Str S C) {o : S.ops} {k : Fin (S.arity_ops o) -> tm S n}:
  L.interp_tm (.op o k) = L.interp_subst k ≫ L.interp_ops o :=
  rfl

noncomputable
def interp_fml {S : monosig} {n} (L : Str S C) : fml S n -> (npow L.carrier n ⟶ SubobjectClassifier.prop)
| .pred p k => L.interp_subst k ≫ L.interp_preds p
| .true => ⊤
| .false => ⊥
| .conj φ ψ => L.interp_fml φ ⊓ L.interp_fml ψ
| .disj φ ψ => L.interp_fml φ ⊔ L.interp_fml ψ
| .infdisj φ => ⨆ i: Nat, interp_fml L (φ i)
| .existsQ φ => SubobjectClassifier.existπ (L.interp_fml φ)
| .eq t u => lift (L.interp_tm t) (interp_tm L u) ≫ SubobjectClassifier.eq


def model {S : monosig} (L : Str S C) (s : sequent S) : Prop :=
  L.interp_fml s.premise ≤ L.interp_fml s.concl

structure morphism {S : monosig} (L L' : Str S C) where
  map : L.carrier ⟶ L'.carrier
  ops_comm : forall (o : S.ops), nlift_diag _ _ _ map ≫ L'.interp_ops o = L.interp_ops o ≫ map
  preds_comm : forall (p : S.preds), nlift_diag _ _ _ map ≫ L'.interp_preds p  = L.interp_preds p

instance category : {S : monosig} → Category (Str S C) where
  Hom := morphism
  id L := {
    map := 𝟙 L.carrier
    ops_comm := fun o => by simp only [nlift_diag_id, Category.id_comp, Category.comp_id]
    preds_comm := fun p => by simp only [SubobjectClassifier.prop.eq_1, nlift_diag_id,
      Category.id_comp]
    }
  comp f g := {
    map := f.map ≫ g.map
    ops_comm := fun o => by
      rw [<-nlift_diag_comp,Category.assoc, g.ops_comm]
      rw [<-Category.assoc]
      simp only [f.ops_comm, Category.assoc]
    preds_comm := fun p => by
      rw [<-nlift_diag_comp]
      simp only [SubobjectClassifier.prop.eq_1, Category.assoc, g.preds_comm, f.preds_comm]
  }

end Str

structure Mod (T : theory) (C : Type) [Category C] where
  str : Str T.sig C
  valid : forall s, s ∈ T.axioms → str.model s

instance : forall {T : theory} {C : Type} [Category C], Category (Mod T C) where
  Hom M M' := M.str ⟶ M'.str
  id M := 𝟙 M.str
  comp := Str.category.comp



namespace BaseChange
variable {D : Type} [Category D] (F : Functor C D) (T : theory)


open BaseChange.SubobjectClassifier
open BaseChange.ChosenFiniteProducts

noncomputable
def pb_obj (L : Str T.sig D) : Str T.sig C where
  carrier := F.op ⋙ L.carrier
  interp_ops := fun o =>
    let h := L.interp_ops o
    let h' := whiskerLeft F.op h
    (pb_prod_iso F _ _).inv ≫ h'
  interp_preds := fun p =>
    let h := L.interp_preds p
    let h' := whiskerLeft F.op h
    let h'' := h' ≫ pb_prop F
    (pb_prod_iso F _ _).inv ≫ h''

theorem pb_obj_carrier (L : Str T.sig D) :
  (pb_obj F T L).carrier = F.op ⋙ L.carrier := rfl

theorem pb_obj_interp_preds (L : Str T.sig D) (p: T.sig.preds) :
  (pb_obj F T L).interp_preds p =
  (pb_prod_iso F L.carrier (T.sig.arity_preds p)).inv ≫ map_pred F (L.interp_preds p) := by
    simp [pb_obj]

def pb_map (L₁ L₂ : Str T.sig D) (f : L₁ ⟶ L₂) :
  pb_obj F T L₁ ⟶ pb_obj F T L₂ where
  map := whiskerLeft F.op f.map
  ops_comm := by
    intros o
    simp only [pb_obj, SubobjectClassifier.prop.eq_1, nlift_diag, Category.assoc, ←
      CategoryTheory.whiskerLeft_comp, ← f.ops_comm]
    simp only [← Category.assoc, nlift_whisker, CategoryTheory.whiskerLeft_comp]
  preds_comm := by
    intros o
    simp only [pb_obj, SubobjectClassifier.prop, ← f.preds_comm]
    simp only [nlift_diag, ← Category.assoc, nlift_whisker, CategoryTheory.whiskerLeft_comp]

noncomputable
def pullback : Str T.sig D ⥤ Str T.sig C where
  obj := pb_obj F T
  map := pb_map F T _ _



theorem pb_obj_interp_ops (L : Str T.sig D)  (o: T.sig.ops):
  whiskerLeft F.op (L.interp_ops o) =
  (pb_prod_iso F L.carrier (T.sig.arity_ops o)).hom ≫ (pb_obj F T L).interp_ops o := by
  simp only [← Iso.inv_comp_eq,pb_obj, SubobjectClassifier.prop]


theorem pb_obj_interp_ops0 (L : Str T.sig D)  (o: T.sig.ops):
    (pb_prod_iso F L.carrier (T.sig.arity_ops o)).inv ≫ whiskerLeft F.op (L.interp_ops o) =
    (pb_obj F T L).interp_ops o := by
    simp only [Iso.inv_comp_eq,pb_obj, SubobjectClassifier.prop, Iso.hom_inv_id_assoc]




theorem pb_prop_interp_tm (L : Str T.sig D) (n : ℕ ) (t : tm T.sig n) :
  whiskerLeft F.op (L.interp_tm t) =
  (pb_prod_iso F _ n).hom ≫ (pb_obj F T L).interp_tm t := by
    induction t with
    | var _ =>
      simp only [Str.interp_tm, ← nproj_pb_prod, pb_obj, SubobjectClassifier.prop,
        pb_prod_hom]
    | op o a a_ih =>
      simp only [Str.interp_tm, CategoryTheory.whiskerLeft_comp,
      pb_obj_interp_ops,← Category.assoc]
      congr 1
      simp only [← pb_npair_compatible, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply npair_univ
      intro i
      simp_all only [pb_obj, SubobjectClassifier.prop.eq_1, Category.assoc, npair_nproj]

theorem pb_prop_interp_subst (L : Str T.sig D) {n m : Subst T.sig} (σ : n ⟶ m) :
  whiskerLeft F.op (L.interp_subst σ) ≫ (pb_prod_iso F _ n).hom = (pb_prod_iso F _ m).hom ≫ (pb_obj F T L).interp_subst σ := by
  simp only [Str.interp_subst,← pb_npair_compatible, <-npair_natural]
  simp [pb_prop_interp_tm, npair_natural]
  rfl

noncomputable
def pb_prod_precomp_order_iso (L : Str T.sig D) (n : Nat) :=
  SubobjectClassifier.precomp_order_iso (pb_prod_iso F L.carrier n)

theorem pb_prop_interp_fml {n : Nat} (L : Str T.sig D) (φ : fml T.sig n) :
  map_pred F (L.interp_fml φ) = (pb_prod_iso F _ n).hom ≫ (pb_obj F T L).interp_fml φ  := by
    induction φ with
    | @pred m p ts =>
      simp only [Str.interp_fml, <-Category.assoc, <-pb_prop_interp_subst]
      simp [map_pred,CategoryTheory.whiskerLeft_comp, Category.assoc, pb_obj_interp_preds]
    | true =>
      simp only [Str.interp_fml, pb_prop_top]
      rfl
    | false =>
      simp only [Str.interp_fml, pb_prop_bot]
      rfl
    | conj f1 f2 ih1 ih2 =>
      simp only [Str.interp_fml,pb_prop_conj, ih1, ih2]
      rfl
    | disj f1 f2 ih1 ih2 =>
      simp only [Str.interp_fml, pb_prop_disj, ih1, ih2]
      rfl
    | @infdisj n φ ih =>
      simp only [Str.interp_fml, pb_prop_iSup, ih]
      have := OrderIso.map_iSup (pb_prod_precomp_order_iso F T L n) (fun i => (pb_obj F T L).interp_fml (φ i))
      rw [pb_prod_precomp_order_iso, SubobjectClassifier.precomp_order_iso_app] at this
      simp only [this]
      rfl
    | eq t1 t2 =>
      simp only [Str.interp_fml, map_pred_comp, pb_prop_eq, whiskerLeft_lift, pb_prop_interp_tm, ← comp_lift, Category.assoc]
    | existsQ f ih =>
      simp only [Str.interp_fml, pb_prop_existπ, ih, <-Category.assoc, pb_prod_hom, pb_prod_succ']
      rw [<-pb_prod_hom, SubobjectClassifier.precomp_existsπ_iso]
      rfl


def pb_prop_interp_fml' {n : Nat} (L : Str T.sig D) (φ : fml T.sig n) :
  (pb_obj F T L).interp_fml φ =
    (pb_prod_iso F _ n).inv ≫ map_pred F (L.interp_fml φ) := by
    simp only [pb_prop_interp_fml, Iso.inv_hom_id_assoc]


def pb_prop_preserves_interp (L : Str T.sig D) (s : sequent T.sig) (h : L.model s) :
  (pb_obj F T L).model s :=by
    simp only [Str.model, pb_prop_interp_fml']
    exact SubobjectClassifier.le_iso _ _ _ (pb_prop_le F _ _ h)

noncomputable
def pb_model (M: Mod T D ) : Mod T C where
  str := (pullback F T).obj M.str
  valid := by
    intros a ax
    simp only [pullback]
    have := M.valid a ax
    exact (pb_prop_preserves_interp F T M.str a this)

-- TODO: Does not belong here
-- this should boil down to the naturality of pb_prod_iso
theorem nlift_diag_whisker (L₁ L₂ : Psh D)  (n : Nat) (f : (L₁ ⟶ L₂)) :
  nlift_diag (F.op ⋙ L₁) (F.op ⋙ L₂) n (CategoryTheory.whiskerLeft F.op f) =
  (pb_prod_iso F L₁ n).inv ≫ CategoryTheory.whiskerLeft F.op (nlift_diag L₁ L₂ n f) ≫ (pb_prod_iso F L₂ n).hom := by
  simp only [← Category.assoc,← Iso.comp_inv_eq,nlift_diag,nlift_whisker]

def pb_morphism {X Y : Mod T D} (f : X ⟶ Y) : pb_model F T X ⟶ pb_model F T Y where
  map := CategoryTheory.whiskerLeft F.op f.map
  ops_comm := by
    simp only [pb_model, pullback, pb_obj_carrier,
    nlift_diag_whisker, Category.assoc,
    ← pb_obj_interp_ops0, Iso.hom_inv_id_assoc, Category.assoc,
    Iso.cancel_iso_inv_left,
    ← CategoryTheory.whiskerLeft_comp, f.ops_comm, implies_true]
  preds_comm := by
    simp only [pb_model, pullback, pb_obj_carrier, nlift_diag_whisker,
      pb_obj_interp_preds, map_pred]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_inv_left]
    simp only [<-Category.assoc, ←CategoryTheory.whiskerLeft_comp]
    simp only [f.preds_comm, implies_true]

noncomputable
def pullback_Mod : Mod T D ⥤ Mod T C where
  obj M := pb_model F T M
  map f := pb_morphism F T f


theorem subst_interp_tm  (L: Str S C) (n : RenCtx) (m : Subst S) (σ : Fin n → tm S m) (t: tm S n) :
  L.interp_tm (tm.subst σ t) = L.interp_subst σ ≫ L.interp_tm t := by
  induction t with
  | var i =>
    simp only [tm.subst, Str.interp_subst, Str.interp_tm, npair_nproj]
  | op o a a_ih =>
    have h1 : L.interp_subst (fun i => (a i).subst σ) = L.interp_subst σ ≫ L.interp_subst a := by
      apply npair_univ
      simp only [a_ih, Str.interp_subst, Category.assoc, npair_nproj, implies_true]
    simp only [Str.interp_tm_op, ← Category.assoc, <- h1]
    rfl

theorem interp_subst_comp {L : Str S C} {x y z : Subst S} (σ : x ⟶ y) (τ : y ⟶ z) :
L.interp_subst τ ≫ L.interp_subst σ = L.interp_subst (σ ≫ τ) := by
  symm
  apply npair_univ
  simp only [tm.subst_comp_app, subst_interp_tm, Str.interp_subst, Category.assoc, npair_nproj,
  implies_true]



theorem interp_ren_succ (L: Str S C) (m : Subst S) (t: tm S m):
  snd L.carrier (npow L.carrier m) ≫ L.interp_tm t = L.interp_tm (tm.ren Fin.succ t) := by
  simp only [tm.ren_to_subst, subst_interp_tm]
  congr 1
  apply npair_univ'
  simp only [Str.interp_subst, npow, Str.interp_tm, Function.comp, nproj_succ, npair_nproj, implies_true]

theorem interp_lift_subst (L: Str S C) {m n: Subst S} (σ : m ⟶ n) :
  L.interp_subst (lift_subst σ) = 𝟙 _ ⊗ L.interp_subst σ := by
  simp only [Str.interp_subst, id_tensorHom]
  apply npair_univ'
  intro i
  simp only [npair_nproj]
  induction i using Fin.cases
  · simp only [lift_subst, Fin.cases_zero,Str.interp_tm, nproj, Fin.succRecOn_zero, whiskerLeft_fst]
  · simp only [lift_subst, Fin.cases_succ, Function.comp_apply, ← interp_ren_succ, nproj_succ,
    whiskerLeft_snd_assoc, npair_nproj]

theorem interp_lift_subst_snd (L: Str S C) {m n: Subst S} (σ : m ⟶ n) {c} {x : (npow L.carrier (n+1)).obj c}:
  ((L.interp_subst (lift_subst σ)).app c x).2 = (L.interp_subst σ).app c x.2 := by
  simp only [interp_lift_subst, id_tensorHom, ChosenFiniteProducts.whiskerLeft_app]

theorem prod_ext (A B : Type) (a : A) (b : B) (x : A × B) :
  x.1 = a -> x.2 = b -> x = (a,b) := by
  intros eq1 eq2
  cases x
  simp only [Prod.mk.injEq,] at *
  simp only [eq1, eq2, and_self]

theorem prod_ext' (A B : Type) (x y: A × B) :
  x.1 = y.1 -> x.2 = y.2 -> x = y := by
  intros eq1 eq2
  cases x
  simp only at *
  simp only [eq1, eq2, Prod.mk.eta]

theorem subst_interp_fml (L: Str S C) (n : RenCtx) (m : Subst S) (σ : Fin n → tm S m) (φ: fml S n) :
  L.interp_fml (fml.subst σ φ) = L.interp_subst σ ≫ L.interp_fml φ := by
  induction φ generalizing m with
  | pred _ _ =>
    simp only [SubobjectClassifier.prop, Str.interp_fml, ← Category.assoc, interp_subst_comp]
    congr
  | true =>
    simp only [SubobjectClassifier.prop, Str.interp_fml, Str.interp_subst, ← Category.assoc]
    congr 1
  | false =>
    simp only [SubobjectClassifier.prop, Str.interp_fml, ← Category.assoc]
    congr 1
  | conj f1 f2 ih1 ih2 =>
    simp only [Str.interp_fml, fml.subst, ih1, ih2]
    rfl
  | disj f1 f2 ih1 ih2 =>
    simp only [Str.interp_fml, fml.subst, ih1, ih2]
    rfl
  | infdisj _ ih =>
    simp only [Str.interp_fml, fml.subst, ih, SubobjectClassifier.precomp_iSup]
  | @eq n t1 t2 =>
    simp[Str.interp_fml,fml.subst]
    have h : ChosenFiniteProducts.lift (L.interp_tm (tm.subst σ t1)) (L.interp_tm (tm.subst σ t2)) =
    (L.interp_subst σ) ≫ ChosenFiniteProducts.lift (L.interp_tm t1) (L.interp_tm t2) := by
      apply hom_ext <;> simp only [lift_fst, comp_lift] <;> simp only [subst_interp_tm, lift_snd]
    simp only [h, comp_lift, ← Category.assoc]
  | @existsQ n f ih =>
    apply le_antisymm
    · simp only[Str.interp_fml, fml.subst,SubobjectClassifier.existπ]
      simp[ih]
      let sb :=  (npair (npow L.carrier m) L.carrier n fun i ↦ L.interp_tm (σ i))
      let st := (npair (npow L.carrier (m + 1)) L.carrier (n + 1) fun i ↦ L.interp_tm (lift_subst σ i))
      let mm := (snd L.carrier (npow L.carrier m))
      let kk := snd L.carrier (npow L.carrier n)
      have comm: mm ≫ sb = st ≫ kk := by
        simp only [mm, sb, st, kk]
        apply npair_univ'
        simp only [Category.assoc, npair_nproj,← nproj_succ]
        simp only [npair_nproj (n+1) (fun i ↦ L.interp_tm (lift_subst σ i))]
        simp only [lift_subst, Fin.cases_succ, Function.comp_apply]
        intro i
        apply interp_ren_succ
      apply SubobjectClassifier.mate sb st mm kk comm (L.interp_fml f)

    · intros cop ρ
      simp only [SubobjectClassifier.prop, FunctorToTypes.comp]
      intro c' f1
      simp only[Str.interp_fml, SubobjectClassifier.existQ,SubobjectClassifier.existπ, SubobjectClassifier.existQ, SubobjectClassifier.prop,
        snd_app, Opposite.op_unop, forall_exists_index, and_imp]
      intro ρ' h1 h2
      let ρ'' : (L.carrier ⊗ npow L.carrier m).obj (Opposite.op c') := ⟨ρ'.1, (npow L.carrier m).map (Opposite.op f1) ρ⟩
      exists ρ''
      constructor
      · simp
        rfl
      · simp only [ih, SubobjectClassifier.prop, FunctorToTypes.comp]
        have liftsubstρ'' : (L.interp_subst (lift_subst σ)).app _  ρ'' = ρ' := by
          apply prod_ext
          · simp only [Str.interp_subst, lift_subst, Fin.cases_zero, npair_app_pt, Str.interp_tm, nproj,
            Fin.succRecOn_zero, fst_app, ρ'']
          · simp only [interp_lift_subst_snd, ρ'']
            have opeq: (Opposite.op f1) = f1.op := rfl
            rw [opeq]
            let nat := @(L.interp_subst σ).naturality _ _ cop _ f1.op
            rw[← types_comp_apply ((npow L.carrier m).map f1.op) ((L.interp_subst σ).app (Opposite.op c')) ρ, nat]
            rw [types_comp_apply, h1]
        rw [liftsubstρ'']
        assumption


-- theorem interp_fml_true (L: Str S C) (n : RenCtx) :  L.interp_fml (.true (n:=n)) = ⊤ := by
--   simp only [Str.interp_fml]

-- theorem interp_fml_false (L: Str S C) (n : RenCtx) : L.interp_fml (.false (n:=n)) = ⊥ := by
--   simp only [Str.interp_fml]

-- theorem interp_fml_conj (L: Str S C) (n : RenCtx) (φ ψ: fml S n) :
--   Str.interp_fml L (φ.conj ψ) =
--   (Str.interp_fml L φ) ⊓ (Str.interp_fml L ψ) := by
--   simp only [Str.interp_fml]

-- theorem interp_fml_disj (L: Str S C) (n : RenCtx) (φ ψ: fml S n) :
-- Str.interp_fml L (φ.disj ψ) =
-- SubobjectClassifier.complete_lattice_to_prop.sup (Str.interp_fml L φ) (Str.interp_fml L ψ) := by
-- simp only[SubobjectClassifier.complete_lattice_to_prop_sup,Str.interp_fml]

-- theorem SemilatticeInf_Lattice_inf {α : Type u} [Lattice α] (a b:α) : SemilatticeInf.inf a b = Lattice.inf a b := rfl

-- theorem interp_fml_infdisj (L: Str S C) (n : RenCtx) (φ : ℕ → fml S n) :
-- Str.interp_fml L (fml.infdisj φ) =
-- SubobjectClassifier.complete_lattice_to_prop.sSup {Str.interp_fml L (φ i) |( i: ℕ ) } := by
--   sorry--need to fill the sorry for infdisj!

--theorem lift_same_eq_app  (X Y: Psh D) (f: X ⟶ Y)

theorem lift_same_eq (X Y: Psh D) (f: X ⟶ Y): ChosenFiniteProducts.lift f f ≫ SubobjectClassifier.eq = ⊤ := by
  ext dop a
  simp only[SubobjectClassifier.complete_lattice_to_prop]
  simp only [SubobjectClassifier.prop, FunctorToTypes.comp, lift_app_pt]
  ext d' g
  simp only [SubobjectClassifier.top_app, iff_true,SubobjectClassifier.eq, SubobjectClassifier.prop, Opposite.op_unop]

theorem interp_fml_eq_refl (L: Str S C) (n : RenCtx) (t: tm S n) :
  Str.interp_fml L (fml.eq t t) = ⊤ := by
  simp only[Str.interp_fml,lift_same_eq]

theorem disj_elim_lemma (A: Type) [Lattice A] (a b c d: A)
  (h0:a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) ) (h1:a ≤ b ⊔ c) (h2: b ⊓ a ≤ d) (h3: c ⊓ a ≤ d):
  a ≤ d := by
  have p1: a ⊓ (b ⊔ c) = a := by
    have := @le_inf_sup A
    simp only [inf_eq_left, ge_iff_le]
    assumption
  have p6: a ⊓ (b⊔ c) ≤ d := by
    simp only [h0, sup_le_iff]
    exact ⟨by rw[inf_comm a b];assumption,by rw[inf_comm a c];assumption⟩
  rw [p1] at p6
  assumption

theorem interp_subst_fst (L: Str msig D) (t : tm msig n) (φ: (Fml msig).obj (n + 1)) :
  L.interp_fml (φ⟪t∷𝟙 _⟫) = lift (L.interp_tm t) (𝟙 _) ≫ L.interp_fml φ := by
    simp only [ScopedSubstitution.ssubst, Fml, subst_interp_fml, Str.interp_subst]
    congr 1
    simp [npair_succ, subst0, tm.ret_var, Str.interp_tm]
    congr 1
    apply npair_univ'
    intros; simp


theorem interp_tm_eq (L: Str msig D) (t1 t2 : tm msig n) :
  L.interp_fml (fml.eq t1 t2) = ⊤ ↔  L.interp_tm t1 = L.interp_tm t2 := by
  simp only [Str.interp_fml,SubobjectClassifier.lift_eq_eq' (L.interp_tm t1) (L.interp_tm t2)]

theorem interp_tm_eq_app (L: Str msig D) (t1 t2 : tm msig n) (d: Dᵒᵖ) (x: (npow L.carrier n).obj d ):
  let s: Sieve d.unop := (L.interp_fml (fml.eq t1 t2)).app d x
  s = ⊤ ↔  (L.interp_tm t1).app d x = (L.interp_tm t2).app d x := by
  simp only[Str.interp_fml]
  exact SubobjectClassifier.lift_eq_eq (L.interp_tm t1) (L.interp_tm t2) d x

theorem interp_tm_eq_conseq (L: Str msig D) (t1 t2 : tm msig n) ( γ: (Fml msig).obj (n + 1)):
  L.interp_fml (fml.eq t1 t2) = ⊤ → (L.interp_fml  (γ⟪t1∷𝟙 _⟫)) = (L.interp_fml (γ⟪t2∷𝟙 _⟫)) := by
  simp only [interp_subst_fst]
  simp only[interp_tm_eq L t1 t2]
  intro h
  simp only [h]

theorem interp_tm_eq_conseq_app (L: Str msig D) (t1 t2 : tm msig n) ( γ: (Fml msig).obj (n + 1))
    (d: Dᵒᵖ) (x: (npow L.carrier n).obj d ):
  let s: Sieve d.unop := (L.interp_fml (fml.eq t1 t2)).app d x
  s = ⊤ → (L.interp_fml (γ⟪t1∷𝟙 _⟫)).app d x = (L.interp_fml (γ⟪t2∷𝟙 _⟫)).app d x := by
  simp only [interp_subst_fst, FunctorToTypes.comp, lift_app_pt,
    NatTrans.id_app, types_id_apply,interp_tm_eq_app L t1 t2 d x]
  intro h
  rw [h]



theorem soundness {T : theory} {n : RenCtx} (M:Mod T D) (φ ψ: fml T.sig n)
  (h:Hilbert.proof φ ψ): InterpPsh.Str.model M.str (sequent.mk _ φ ψ) := by
  induction h with
  | «axiom» hyp =>
      simp only [Str.model, SubobjectClassifier.prop, ge_iff_le] at *
      simp only [subst_interp_fml, SubobjectClassifier.prop]
      exact SubobjectClassifier.le_precomp _ _ _ (M.valid _ hyp)
  | cut phi2tau tau2psi Mphitau Mtaupsi =>
    simp only [Str.model, SubobjectClassifier.prop] at *
    apply SubobjectClassifier.complete_lattice_to_prop.le_trans <;> assumption
  | var =>
    simp only [Str.model, SubobjectClassifier.prop, le_refl]
  | true_intro =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml, le_top]
  | false_elim a a_ih =>
    rename_i n φ ψ
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml] at *
    apply SubobjectClassifier.complete_lattice_to_prop.le_trans
    assumption
    simp only [SubobjectClassifier.prop, bot_le]
  | conj_intro _ _ _ _ =>
    simp only[InterpPsh.Str.model] at *
    simp only[Str.interp_fml]
    apply SemilatticeInf.le_inf <;> assumption
  | conj_elim_l =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml]
    apply SubobjectClassifier.complete_lattice_to_prop.inf_le_left
  | conj_elim_r =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml]
    apply SubobjectClassifier.complete_lattice_to_prop.inf_le_right
  | disj_intro_l =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml]
    apply SubobjectClassifier.complete_lattice_to_prop.le_sup_left
  | disj_intro_r =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml]
    apply SubobjectClassifier.complete_lattice_to_prop.le_sup_right
  | @disj_elim n f1 f2 f3 f4 f1pf2orf3 f2cf1pf4 f3cf1pf4 h1 h2 h3 =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml] at *
    set a := M.str.interp_fml f1 with a_def
    set b := M.str.interp_fml f2 with b_def
    set c := M.str.interp_fml f3 with c_def
    set d := M.str.interp_fml f4 with d_def
    simp only[← a_def,← b_def,← c_def,← d_def] at *
    apply disj_elim_lemma (npow M.str.carrier n ⟶ SubobjectClassifier.prop) a b c d <;> try assumption
    simp only[SubobjectClassifier.psh_distr]
  | infdisj_intro =>
    simp only [Str.model, SubobjectClassifier.prop, Str.interp_fml]
    apply SubobjectClassifier.complete_lattice_to_prop.le_sSup
    simp
  | infdisj_elim _ _ _ _ => sorry
  | eq_intro =>
    simp only [Str.model, SubobjectClassifier.prop, interp_fml_eq_refl]
    simp only [SubobjectClassifier.prop, Str.interp_fml, le_refl]
  | eq_elim φ γ _ _ _ _ =>
    simp only[InterpPsh.Str.model] at *
    rename_i n f t1 t2 p1 p2 h1 h2
    simp only[Str.interp_fml]
    set a := M.str.interp_fml f with a_def
    set b := M.str.interp_fml (γ⟪t1∷𝟙 _⟫) with b_def
    set c := M.str.interp_fml (φ⟪t1∷𝟙 _⟫) with c_def
    set d := M.str.interp_fml (fml.eq t1 t2) with d_def
    set e := M.str.interp_fml (γ⟪t2∷𝟙 _⟫) with e_def
    set f1 := M.str.interp_fml (φ⟪t2∷𝟙 _⟫) with f1_def
    have := @SubobjectClassifier.Sieve_le_alt _ _ _ (a ⊓ e) f1
    simp only[this]
    intros d0 x0 cjae
    have := @SubobjectClassifier.psh_inf_arrows' _ _ _ a e d0 x0
    simp only [SubobjectClassifier.prop] at cjae
    simp only[this] at cjae
    have := @inf_eq_top_iff _ _ _ a e
    simp only[inf_eq_top_iff] at cjae
    rcases cjae with ⟨ha, he⟩
    have ad:= @SubobjectClassifier.Sieve_le_alt _ _ _ a d
    simp only [SubobjectClassifier.prop, <-d_def, ad] at h1
    have hd := h1 _ _ ha
    have beqe : b.app d0 x0 = e.app d0 x0 := by
      simp only [SubobjectClassifier.prop, b_def, e_def]
      apply interp_tm_eq_conseq_app
      simp only [d_def] at hd
      assumption
    have ceqf1 : c.app d0 x0 = f1.app d0 x0 := by
      simp only [SubobjectClassifier.prop, c_def, f1_def]
      apply interp_tm_eq_conseq_app
      simp only [d_def] at hd
      assumption
    simp only [SubobjectClassifier.prop, ← ceqf1]
    simp only [SubobjectClassifier.prop] at h2
    have abc:= @SubobjectClassifier.Sieve_le_alt _ _ _ (a ⊓ b) c
    simp[Str.interp_fml, <-a_def, <-b_def, abc] at h2
    apply h2
    have := @SubobjectClassifier.psh_inf_arrows' _ _ _ a b d0 x0
    simp only [this, SubobjectClassifier.prop, beqe, inf_eq_top_iff]
    constructor
    · assumption
    · assumption
  | @existsQ_intro n t φ =>
    simp only [Str.model, SubobjectClassifier.prop]
    intros dop x l
    simp only [SubobjectClassifier.prop, l]
    intros d' f h
    simp only [Str.interp_fml, SubobjectClassifier.existπ,
      SubobjectClassifier.existQ_app_arrows, snd_app, Opposite.op_unop,
      SubobjectClassifier.prop]
    simp only[interp_subst_fst] at h
    simp only[CategoryTheory.Sieve.pullback_eq_top_iff_mem] at h
    simp only[← CategoryTheory.Sieve.id_mem_iff_eq_top] at h
    simp only [← SubobjectClassifier.to_prop_naturality] at h
    let a: (M.str.carrier ⊗ npow M.str.carrier n).obj (Opposite.op d') :=
      ((ChosenFiniteProducts.lift (M.str.interp_tm t) (𝟙 _)).app dop ≫ (npow M.str.carrier (n+1)).map (Opposite.op f)) x
    exists a
    constructor
    · simp only [types_comp_apply, lift_app_pt, NatTrans.id_app, types_id_apply,
      npow_suc_map_snd, a] ; rfl
      --snd_app_npow?
    · have hh :((ChosenFiniteProducts.lift (M.str.interp_tm t) (𝟙 (npow M.str.carrier n)) ≫ M.str.interp_fml φ).app (Opposite.op d')
  ((npow M.str.carrier n).map (Opposite.op f) x)) =
      ((M.str.interp_fml φ).app (Opposite.op d') a) := by
        simp only[a]
        have := @types_comp_apply _ _ _
              ((npow M.str.carrier n).map (Opposite.op f))
              ((ChosenFiniteProducts.lift (M.str.interp_tm t) (𝟙 (npow M.str.carrier n)) ≫ M.str.interp_fml φ).app (Opposite.op d'))
        simp only[← this]
        have := @types_comp_apply _ _ _
              (((ChosenFiniteProducts.lift (M.str.interp_tm t) (𝟙 (npow M.str.carrier n))).app dop ≫
    (npow M.str.carrier (n + 1)).map (Opposite.op f)))
                ((M.str.interp_fml φ).app (Opposite.op d'))
        simp only[← this]
        have := (ChosenFiniteProducts.lift (M.str.interp_tm t) (𝟙 (npow M.str.carrier n))).naturality (Opposite.op f)
        simp only [npow,← this,Category.assoc]
        rfl
      simp only [SubobjectClassifier.prop, hh] at h
      assumption
  | @existsQ_elim m ψ0 ψ hp md =>
    simp only [Str.model, fml.ren_to_subst, subst_interp_fml, SubobjectClassifier.prop, Str.interp_fml,
      SubobjectClassifier.existπ] at *
    have := @SubobjectClassifier.existQ_precomp_adj _ _ _ _ (snd M.str.carrier (npow M.str.carrier m))
        (M.str.interp_fml ψ0) (M.str.interp_fml ψ)
    rw[this]
    simp only [SubobjectClassifier.prop, SubobjectClassifier.precomp]
    have : snd M.str.carrier (npow M.str.carrier m) =
            npair (npow M.str.carrier (m + 1)) M.str.carrier m fun i ↦ M.str.interp_tm (tm.var i.succ) := by
            simp only [Str.interp_tm]
            apply npair_univ'
            intro i
            rw[npair_nproj _ (fun i ↦ nproj M.str.carrier (m + 1) i.succ) i,nproj_succ]
    simp only [this, ge_iff_le]
    assumption
  | ren _ _ =>
    simp only [Str.model, SubobjectClassifier.prop, fml.ren_to_subst, subst_interp_fml] at *
    apply SubobjectClassifier.le_precomp
    assumption


-- Second part, (-)^* assembles as a 2-functor
-- T-Mod : Cat^op -> CAT

-- Third part, T-Mod is representable
-- T-Mod(C) ≅ Topos(Set[T], Psh(C))


-- Fourth part, 2-Grothendieck construction
-- 2-category T-Mod    T: theory
-- Objects (C, M)  C : category, M : T-Mod(C)
-- 1-cell  (C, M) ==> (D, N)    F : C ==> D functor, f : M -> F^*N
-- 2-cells (F, f) -> (G, g)   μ : F -> G,  μ_N T-Mod(F^* N, G^* N)

end BaseChange

end InterpPsh
