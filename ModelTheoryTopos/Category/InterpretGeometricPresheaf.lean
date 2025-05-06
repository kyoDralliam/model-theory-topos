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
import ModelTheoryTopos.Misc

namespace InterpPsh
open CategoryTheory MonoidalCategory ChosenFiniteProducts

-- S-Structure over C: interpretation of the operations and predicates of a signature S on a presheaf on C
structure Str (S : monosig) (C : Type) [Category C]  where
  carrier : Psh C
  interp_ops : forall (o : S.ops), npow carrier (S.arity_ops o) ⟶ carrier
  interp_preds : forall (p : S.preds), npow carrier (S.arity_preds p) ⟶ SubobjectClassifier.prop

variable {C : Type} [Category C]

namespace Str

-- Any S-signature L over C induces a right-module for the monad Tm^S
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

-- the next 3 lemmas look a bit too specific
theorem interp_ren_succ (L: Str S C) (m : Subst S) (t: tm S m):
  snd L.carrier (npow L.carrier m) ≫ L.interp_tm t = L.interp_tm (tm.ren Fin.succ t) := by
  simp only [tm.ren_to_subst, subst_interp_tm]
  congr 1
  apply npair_univ'
  intros i
  simp [Str.interp_subst, Str.interp_tm, nproj_succ]
  symm
  apply npair_nproj

theorem interp_lift_subst (L: Str S C) {m n: Subst S} (σ : m ⟶ n) :
  L.interp_subst (lift_subst σ) = 𝟙 _ ⊗ L.interp_subst σ := by
  simp only [Str.interp_subst, id_tensorHom]
  apply npair_univ'
  intro i
  simp only [npair_nproj]
  induction i using Fin.cases
  · simp only [lift_subst, Fin.cases_zero,Str.interp_tm, nproj_zero, Fin.succRecOn_zero]
    symm
    apply whiskerLeft_fst
  · simp only [lift_subst, Fin.cases_succ, Function.comp_apply, ← interp_ren_succ, nproj_succ,
    whiskerLeft_snd_assoc, npair_nproj]

theorem interp_lift_subst_snd (L: Str S C) {m n: Subst S} (σ : m ⟶ n) {c} {x : (npow L.carrier (n+1)).obj c}:
  ((L.interp_subst (lift_subst σ)).app c x).2 = (L.interp_subst σ).app c x.2 := by
  simp only [interp_lift_subst, id_tensorHom, ChosenFiniteProducts.whiskerLeft_app]

-- Morphisms of S-Structure over C
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


variable [SmallUniverse]

-- Interpretation of geometric formula on a S-structure L over C
noncomputable
def interp_fml {S : monosig} {n} (L : Str S C) : fml S n -> (npow L.carrier n ⟶ SubobjectClassifier.prop)
| .pred p k => L.interp_subst k ≫ L.interp_preds p
| .true => ⊤
| .false => ⊥
| .conj φ ψ => L.interp_fml φ ⊓ L.interp_fml ψ
| .disj φ ψ => L.interp_fml φ ⊔ L.interp_fml ψ
| .infdisj a φ => ⨆ i: SmallUniverse.El a, interp_fml L (φ i)
| .existsQ φ => SubobjectClassifier.existπ (L.interp_fml φ)
| .eq t u => lift (L.interp_tm t) (interp_tm L u) ≫ SubobjectClassifier.eq


def model {S : monosig} (L : Str S C) (s : sequent S) : Prop :=
  L.interp_fml s.premise ≤ L.interp_fml s.concl

end Str


-- A model of a geometric theory T over C is an S-structure str over C validating all axioms of T
structure Mod [SmallUniverse] (T : theory) (C : Type) [Category C] where
  str : Str T.sig C
  valid : forall s, s ∈ T.axioms → str.model s

instance Mod_Category: forall [SmallUniverse] {T : theory} {C : Type} [Category C], Category (Mod T C) where
  Hom M M' := M.str ⟶ M'.str
  id M := 𝟙 M.str
  comp := Str.category.comp



namespace BaseChange
variable {D : Type} [Category D] (F : Functor C D) [SmallUniverse] (T : theory)


open SubobjectClassifier.BaseChange
open ChosenFiniteProducts.BaseChange

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


theorem pb_prop_interp_tm (L : Str T.sig D) (n : ℕ ) (t : tm T.sig n) :
  whiskerLeft F.op (L.interp_tm t) =
  (pb_prod_iso F _ n).hom ≫ (pb_obj F T L).interp_tm t := by
    induction t with
    | var _ =>
      simp only [Str.interp_tm, ←nproj_pb_prod, pb_prod_hom]
      rfl
    | op o a a_ih =>
      simp only [Str.interp_tm_op, CategoryTheory.whiskerLeft_comp]
      simp only [pb_obj_interp_ops, ←Category.assoc]
      congr 1
      simp only [Str.interp_subst, ←npair_pb_prod, pb_obj, ←npair_natural, a_ih]

theorem pb_prop_interp_subst (L : Str T.sig D) {n m : Subst T.sig} (σ : n ⟶ m) :
  whiskerLeft F.op (L.interp_subst σ) ≫ (pb_prod_iso F _ n).hom = (pb_prod_iso F _ m).hom ≫ (pb_obj F T L).interp_subst σ := by
  simp only [Str.interp_subst, ←npair_pb_prod]
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
    | @infdisj n a φ ih =>
      simp only [Str.interp_fml, pb_prop_iSup, ih]
      have := OrderIso.map_iSup (pb_prod_precomp_order_iso F T L n) (fun i => (pb_obj F T L).interp_fml (φ i))
      rw [pb_prod_precomp_order_iso, SubobjectClassifier.precomp_order_iso_app] at this
      simp only [this]
      rfl
    | eq t1 t2 =>
      simp only [Str.interp_fml, map_pred_comp, pb_prop_eq, whiskerLeft_lift, pb_prop_interp_tm, ← comp_lift, Category.assoc]
    | existsQ f ih =>
      rename_i k
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

noncomputable
def pullback_Mod : Mod T D ⥤ Mod T C where
  obj M := pb_model F T M
  map f := pb_map _ _ _ _ f

theorem subst_interp_fml (L: Str S C) (n : RenCtx) (m : Subst S) (σ : Fin n → tm S m) (φ: fml S n) :
  L.interp_fml (fml.subst σ φ) = L.interp_subst σ ≫ L.interp_fml φ := by
  induction φ generalizing m with
  | pred _ _ =>
    simp only [SubobjectClassifier.prop, Str.interp_fml, ← Category.assoc, Str.interp_subst_comp]
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
  | infdisj _ _ ih =>
    simp only [Str.interp_fml, fml.subst, ih, SubobjectClassifier.precomp_iSup]
  | @eq n t1 t2 =>
    simp[Str.interp_fml,fml.subst]
    have h : ChosenFiniteProducts.lift (L.interp_tm (tm.subst σ t1)) (L.interp_tm (tm.subst σ t2)) =
    (L.interp_subst σ) ≫ ChosenFiniteProducts.lift (L.interp_tm t1) (L.interp_tm t2) := by
      apply hom_ext <;> simp only [lift_fst, comp_lift] <;> simp only [Str.subst_interp_tm, lift_snd]
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
        apply Str.interp_ren_succ
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
          · simp only [Str.interp_subst, lift_subst, Fin.cases_zero, npair_app_pt, Str.interp_tm, nproj_zero,
            Fin.succRecOn_zero, fst_app, ρ'']
          · simp only [Str.interp_lift_subst_snd, ρ'']
            have opeq: (Opposite.op f1) = f1.op := rfl
            rw [opeq]
            let nat := @(L.interp_subst σ).naturality _ _ cop _ f1.op
            rw[← types_comp_apply ((npow L.carrier m).map f1.op) ((L.interp_subst σ).app (Opposite.op c')) ρ, nat]
            rw [types_comp_apply, h1]
        rw [liftsubstρ'']
        assumption


theorem interp_fml_eq_refl (L: Str S C) (n : RenCtx) (t: tm S n) :
  Str.interp_fml L (fml.eq t t) = ⊤ := by
  simp only[Str.interp_fml, SubobjectClassifier.lift_same_eq]


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


open SubobjectClassifier in
theorem soundness {T : theory} {n : RenCtx} (M:Mod T D) (φ ψ: fml T.sig n)
  (h:Hilbert.proof φ ψ): InterpPsh.Str.model M.str (sequent.mk _ φ ψ) := by
  induction h with
  | «axiom» hyp =>
      simp only [Str.model, prop, ge_iff_le] at *
      simp only [subst_interp_fml, prop]
      exact le_precomp _ _ _ (M.valid _ hyp)
  | cut phi2tau tau2psi Mphitau Mtaupsi =>
    simp only [Str.model, prop] at *
    apply complete_lattice_to_prop.le_trans <;> assumption
  | var =>
    simp only [Str.model, prop]
    apply complete_lattice_to_prop.le_refl
  | true_intro =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.le_top
  | false_elim a a_ih =>
    rename_i n φ ψ
    simp only [Str.model, prop, Str.interp_fml] at *
    apply complete_lattice_to_prop.le_trans
    assumption
    simp only [prop, bot_le]
  | conj_intro _ _ _ _ =>
    simp only[InterpPsh.Str.model] at *
    simp only[Str.interp_fml]
    apply SemilatticeInf.le_inf <;> assumption
  | conj_elim_l =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.inf_le_left
  | conj_elim_r =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.inf_le_right
  | disj_intro_l =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.le_sup_left
  | disj_intro_r =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.le_sup_right
  | @disj_elim n f1 f2 f3 f4 f1pf2orf3 f2cf1pf4 f3cf1pf4 h1 h2 h3 =>
    simp only [Str.model, prop, Str.interp_fml] at *
    set a := M.str.interp_fml f1 with a_def
    set b := M.str.interp_fml f2 with b_def
    set c := M.str.interp_fml f3 with c_def
    set d := M.str.interp_fml f4 with d_def
    simp only[← a_def,← b_def,← c_def,← d_def] at *
    apply CompleteLatticeLemma.disj_elim_helper (npow M.str.carrier n ⟶ prop) a b c d <;> try assumption
    simp only[psh_distr]
  | infdisj_intro =>
    simp only [Str.model, prop, Str.interp_fml]
    apply complete_lattice_to_prop.le_sSup
    simp
  | infdisj_elim _ _ ih₁ ih₂ =>
    simp only [Str.model, prop, Str.interp_fml] at *
    apply CompleteLatticeLemma.inf_disj_elim_helper (α:= _ ⟶ prop) <;> try assumption
    intros; apply psh_inf_sSup_distr
  | eq_intro =>
    simp only [Str.model, prop, interp_fml_eq_refl]
    simp only [prop, Str.interp_fml]
    apply complete_lattice_to_prop.le_refl
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
    have := @Sieve_le_alt _ _ _ (a ⊓ e) f1
    simp only[this]
    intros d0 x0 cjae
    have := @psh_inf_arrows' _ _ _ a e d0 x0
    simp only[this] at cjae
    have := @inf_eq_top_iff _ _ _ a e
    simp only[inf_eq_top_iff] at cjae
    rcases cjae with ⟨ha, he⟩
    have ad:= @Sieve_le_alt _ _ _ a d
    simp only [prop, <-d_def, ad] at h1
    have hd := h1 _ _ ha
    have beqe : b.app d0 x0 = e.app d0 x0 := by
      simp only [prop, b_def, e_def]
      apply interp_tm_eq_conseq_app
      simp only [d_def] at hd
      assumption
    have ceqf1 : c.app d0 x0 = f1.app d0 x0 := by
      simp only [prop, c_def, f1_def]
      apply interp_tm_eq_conseq_app
      simp only [d_def] at hd
      assumption
    simp only [prop, ← ceqf1]
    have abc:= @Sieve_le_alt _ _ _ (a ⊓ b) c
    simp[Str.interp_fml, <-a_def, <-b_def, abc] at h2
    apply h2
    have := @psh_inf_arrows' _ _ _ a b d0 x0
    simp only [this, prop, beqe, inf_eq_top_iff]
    constructor
    · assumption
    · assumption
  | @existsQ_intro n t φ =>
    simp only [Str.model]
    intros dop x l
    simp only [l]
    intros d' f h
    simp only [Str.interp_fml, existπ,
      existQ_app_arrows, snd_app, Opposite.op_unop]
    let opd' := Opposite.op d'
    let opf := Opposite.op f
    let x' := (npow M.str.carrier n).map opf x
    let a := (lift (M.str.interp_tm t) (𝟙 _)).app opd' x'
    exists a ; constructor
    · simp only [types_comp_apply, lift_app_pt, NatTrans.id_app, types_id_apply,
      npow_suc_map_snd, a] ; rfl
    · simp only[interp_subst_fst] at h
      simp only [a]
      simp only[CategoryTheory.Sieve.mem_iff_pullback_eq_top] at h
      simp only[← CategoryTheory.Sieve.id_mem_iff_eq_top] at h
      simp only [← to_prop_naturality] at h
      simp only [NatTrans.comp_app] at h
      apply h
  | @existsQ_elim m ψ0 ψ hp md =>
    simp only [Str.model, fml.ren_to_subst, subst_interp_fml, Str.interp_fml,
      existπ] at *
    have := @existQ_precomp_adj _ _ _ _ (snd M.str.carrier (npow M.str.carrier m))
        (M.str.interp_fml ψ0) (M.str.interp_fml ψ)
    rw[this]
    simp only [SubobjectClassifier.precomp]
    have : snd M.str.carrier (npow M.str.carrier m) =
            npair (npow M.str.carrier (m + 1)) M.str.carrier m fun i ↦ M.str.interp_tm (tm.var i.succ) := by
            simp only [Str.interp_tm]
            apply npair_univ'
            intro i
            rw[npair_nproj _ (fun i ↦ nproj M.str.carrier (m + 1) i.succ) i,nproj_succ]
    simp only [this, ge_iff_le]
    assumption
  | ren _ _ =>
    simp only [Str.model, fml.ren_to_subst, subst_interp_fml] at *
    apply le_precomp
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
