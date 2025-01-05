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
  def interp_fml {S : monosig} (L : Str S C) : fml S n -> (npow L.carrier n ⟶ SubobjectClassifier.prop)
  | .pred p k => (npair _ _ _ (fun i => interp_tm L (k i))) ≫ L.interp_preds p
  | .true => toUnit _ ≫ SubobjectClassifier.top
  | .false => toUnit _ ≫ SubobjectClassifier.bot
  | .conj φ ψ => lift (L.interp_fml φ) (L.interp_fml ψ) ≫ SubobjectClassifier.conj
  | .disj φ ψ => lift (interp_fml L φ) (interp_fml L ψ) ≫ SubobjectClassifier.disj
  | .infdisj φ => sorry
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
      ops_comm := fun o => by simp [nlift_diag_id]
      preds_comm := fun p => by simp [nlift_diag_id]
      }
    comp f g := {
      map := f.map ≫ g.map
      ops_comm := fun o => by
        rw [<-nlift_diag_comp]
        simp [g.ops_comm]
        rw [<-Category.assoc]
        simp [f.ops_comm]
      preds_comm := fun p => by
        rw [<-nlift_diag_comp]
        simp [g.preds_comm, f.preds_comm]
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
    variable (D : Type) [Category D] (F : Functor C D) (T : theory)


    open BaseChange.SubobjectClassifier
    open BaseChange.ChosenFiniteProducts

    noncomputable
    def pb_obj (L : Str T.sig D) : Str T.sig C where
      carrier := F.op ⋙ L.carrier
      interp_ops := fun o =>
        let h := L.interp_ops o
        let h' := whiskerLeft F.op h
        (pb_prod F _ _).inv ≫ h'
      interp_preds := fun p =>
        let h := L.interp_preds p
        let h' := whiskerLeft F.op h
        let h'' := h' ≫ pb_prop F
        (pb_prod F _ _).inv ≫ h''

     theorem pb_obj_carrier (L : Str T.sig D) :(pb_obj D F T L).carrier = F.op ⋙ L.carrier
     :=rfl
    theorem pb_obj_interp_preds (L : Str T.sig D)  (p: T.sig.preds):
       (pb_obj D F T L).interp_preds p =
       (pb_prod F L.carrier (T.sig.arity_preds p)).inv ≫
       whiskerLeft F.op (L.interp_preds p) ≫ pb_prop F := by

       simp[← Iso.inv_comp_eq]
       simp[pb_obj]


    def pb_map (L₁ L₂ : Str T.sig D) (f : L₁ ⟶ L₂) :
      pb_obj D F T L₁ ⟶ pb_obj D F T L₂ where
      map := whiskerLeft F.op f.map
      ops_comm := by
        intros o
        simp[pb_obj,← CategoryTheory.whiskerLeft_comp]
        simp[← f.ops_comm]
        simp[← Category.assoc]
        simp[nlift_diag,nlift_whisker]
      preds_comm := by
        intros o
        simp[pb_obj,← CategoryTheory.whiskerLeft_comp]
        simp[← f.preds_comm]
        simp[← Category.assoc]
        simp[nlift_diag,nlift_whisker]



    noncomputable
    def pullback : Str T.sig D ⥤ Str T.sig C where
      obj := pb_obj D F T
      map := pb_map D F T _ _



    theorem pb_obj_interp_ops (L : Str T.sig D)  (o: T.sig.ops):
       whiskerLeft F.op (L.interp_ops o) =
       (pb_prod F L.carrier (T.sig.arity_ops o)).hom ≫ (pb_obj D F T L).interp_ops o := by

       simp[← Iso.inv_comp_eq]
       simp[pb_obj]


    theorem pb_obj_interp_ops0 (L : Str T.sig D)  (o: T.sig.ops):
       (pb_prod F L.carrier (T.sig.arity_ops o)).inv ≫ whiskerLeft F.op (L.interp_ops o) =
       (pb_obj D F T L).interp_ops o := by
       simp[Iso.inv_comp_eq]
       simp[pb_obj]



    theorem pb_prop_existQ_interp_fml  (f : fml T.sig (m + 1))
     (ih: CategoryTheory.whiskerLeft F.op (L.interp_fml f) ≫ pb_prop F =
          (pb_prod F L.carrier (m + 1)).hom ≫ (pb_obj D F T L).interp_fml f) :
      whiskerLeft F.op (SubobjectClassifier.existπ (L.interp_fml f))  ≫ pb_prop F  =
      (pb_prod F L.carrier m).hom ≫ SubobjectClassifier.existπ ((pb_obj D F T L).interp_fml f) := by
      simp[SubobjectClassifier.existπ]

      simp[pb_prop_existQ]
      simp[ih]

      simp[pb_obj_carrier]
      ext c a
      simp[pb_prod_hom]
      ext Y g
      simp[SubobjectClassifier.existQ_app_arrows]
      constructor
      intros
      · rename_i h
        cases h
        rename_i w h
        cases h
        rename_i h1 h2
        cases w
        rename_i t1 tm
        simp [snd_app] at h1
        let a1:= ((pb_prod F L.carrier m).hom).app _ tm
        exists  ⟨ t1,a1⟩
        simp
        constructor
        · simp[a1]
          simp[h1]
          simp[snd_app]
          simp[pb_prod_hom]
          have := (pb_prod0 F L.carrier m).naturality g.op
          simp at this
          have hh : (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 F L.carrier m).app c a) =
                  ((pb_prod0 F L.carrier m).app (Opposite.op (Opposite.unop c)) ≫ (npow (F.op ⋙ L.carrier) m).map g.op) a :=
                    by
                     simp
          simp only[hh]
          simp only [← this]
          simp
        · simp[a1]
          simp[pb_prod_hom]
          have e : (t1, (pb_prod0 F L.carrier m).app (Opposite.op Y) tm) =
           ((pb_prod0 F L.carrier (m + 1)).app (Opposite.op Y) (t1, tm)) := by
            simp only[pb_prod0_pair]
          simp[e]
          exact h2
      intros
      · rename_i h
        cases h
        rename_i w h
        cases h
        rename_i h1 h2
        cases w
        rename_i t10 tm0
        simp [snd_app] at h1
        let a1:= ((pb_prod F L.carrier m).inv).app _ tm0
        exists  ⟨ t10,a1⟩
        simp[snd_app]
        constructor
        · simp[a1]
          simp[h1]
          have e0:
          (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 F L.carrier m).app c a) =
          (pb_prod F L.carrier m).hom.app (Opposite.op Y)
           ((npow L.carrier m).map (F.map g).op a) := by
           simp[pb_prod_hom]
           have := (pb_prod0 F L.carrier m).naturality g.op
           simp at this
           have hh : (npow (F.op ⋙ L.carrier) m).map g.op ((pb_prod0 F L.carrier m).app c a) =
                  ((pb_prod0 F L.carrier m).app (Opposite.op (Opposite.unop c)) ≫ (npow (F.op ⋙ L.carrier) m).map g.op) a := by simp
           simp only[hh]
           simp only [← this]
           simp
          simp[e0]
        · simp[a1]
          --simp[pb_prod_pb_prod0]
          have e : ((pb_prod0 F L.carrier (m + 1)).app (Opposite.op Y)
        (t10, (pb_prod F L.carrier m).inv.app (Opposite.op Y) tm0)) =
           (t10, tm0) := by
           simp
           simp only[pb_prod0_pair F]
           have e1: (pb_prod0 F L.carrier m).app (Opposite.op Y) ((pb_prod F L.carrier m).inv.app (Opposite.op Y) tm0) =
                    ((pb_prod F L.carrier m).inv ≫ pb_prod0 F L.carrier m).app (Opposite.op Y) tm0 := by
                     simp[pb_prod_hom]

           simp only[e1]
           have e11: (pb_prod F L.carrier m).inv ≫ pb_prod0 F L.carrier m = 𝟙 _ := by
            simp [<-pb_prod_hom]
           simp only[e11]
           simp
          --sorry --may need to define the inverse by induction
          simp[e]
          exact h2





    def pb_prop_interp_tm (L : Str T.sig D)  (n : ℕ ) (t : tm T.sig n) :
      whiskerLeft F.op (L.interp_tm t) =
      (pb_prod F _ n).hom ≫ (pb_obj D F T L).interp_tm t := by
        simp[← CategoryTheory.IsIso.inv_comp_eq]
        induction t with
        | var _ =>
          simp[Str.interp_tm]
          simp[Iso.inv_comp_eq]
          simp[pb_prod_hom]
          simp[nproj_pb_prod0_symm]
          simp[pb_obj]
        | op o a a_ih =>
          simp[Str.interp_tm]
          simp[pb_obj_interp_ops]
          simp[← Category.assoc]
          simp[← pb_obj_interp_ops0]
          simp[← a_ih]
          simp[npair_natural]
          simp[← Category.assoc]
          simp
          simp[pb_obj]
          simp[← Category.assoc]
          simp[pb_npair_compatible]

    def pb_prop_interp_fml {n : Nat} (L : Str T.sig D) (φ : fml T.sig n) :
      whiskerLeft F.op (L.interp_fml φ) ≫ pb_prop F =
      (pb_prod F _ n).hom ≫ (pb_obj D F T L).interp_fml φ  := by
        induction φ with
        | pred p ts =>
           rename_i m
           simp[Str.interp_fml]
           simp[pb_obj_interp_preds]
           simp[← pb_npair_compatible]
           simp[pb_prop_interp_tm]
           simp[npair_natural]
           simp[pb_obj]
        | true =>
          rename_i m
          --simp it does not do anything, why do not report error either?
          simp[Str.interp_fml]
          simp[pb_prop_top]
          simp[← Category.assoc]
          have a: CategoryTheory.whiskerLeft F.op (toUnit (npow L.carrier m)) =
            ((pb_prod F L.carrier m).hom ≫ toUnit (npow (pb_obj D F T L).carrier m)) :=
             by
              apply toUnit_unique
          simp only [a]
        | false =>
          rename_i m
          simp[Str.interp_fml]
          simp[pb_prop_bot ]
          simp[← Category.assoc]
          have a: CategoryTheory.whiskerLeft F.op (toUnit (npow L.carrier m)) =
            ((pb_prod F L.carrier m).hom ≫ toUnit (npow (pb_obj D F T L).carrier m)) :=
             by
              apply toUnit_unique
          simp only [a]
        | conj f1 f2 ih1 ih2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[pb_prop_conj]
          have a:
          CategoryTheory.whiskerLeft F.op (ChosenFiniteProducts.lift (L.interp_fml f1) (L.interp_fml f2)) ≫
          (pb_prop F ⊗ pb_prop F) =
          (pb_prod F L.carrier m).hom ≫
    ChosenFiniteProducts.lift ((pb_obj D F T L).interp_fml f1) ((pb_obj D F T L).interp_fml f2)
          := by
            apply hom_ext
            · simp only[Category.assoc]
              simp only[tensorHom_fst]
              simp only[lift_fst]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_fst]
              simp[ih1]

            · simp only[Category.assoc]
              simp only[tensorHom_snd]
              simp only[lift_snd]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_snd]
              simp[ih2]

          simp[← Category.assoc]
          simp[a]

        | disj f1 f2 ih1 ih2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[pb_prop_disj]
          have a:
          CategoryTheory.whiskerLeft F.op (ChosenFiniteProducts.lift (L.interp_fml f1) (L.interp_fml f2)) ≫
          (pb_prop F ⊗ pb_prop F) =
          (pb_prod F L.carrier m).hom ≫
    ChosenFiniteProducts.lift ((pb_obj D F T L).interp_fml f1) ((pb_obj D F T L).interp_fml f2)
          := by
            apply hom_ext
            · simp only[Category.assoc]
              simp only[tensorHom_fst]
              simp only[lift_fst]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_fst]
              simp[ih1]

            · simp only[Category.assoc]
              simp only[tensorHom_snd]
              simp only[lift_snd]
              simp only[whiskerLeft_lift]
              simp only[← Category.assoc]
              simp only[lift_snd]
              simp[ih2]

          simp[← Category.assoc]
          simp[a]
        | infdisj _ _ => sorry
        | eq t1 t2 =>
          rename_i m
          simp
          simp[Str.interp_fml]
          simp[pb_prop_eq]
          simp[whiskerLeft_lift]
          simp[pb_prop_interp_tm]
          simp[← comp_lift]
        | existsQ f ih =>
          rename_i m
          simp
          simp[Str.interp_fml]
          --simp[SubobjectClassifier.existπ]
          have := pb_prop_existQ_interp_fml D F T f ih
          exact this
         -- simp[SubobjectClassifier.existQ]

    -- def pb_prop_preserves_entailment (φ ψ : SubobjectClassifier.prop (C:=D))

    def pb_prop_interp_fml' {n : Nat} (L : Str T.sig D) (φ : fml T.sig n) :
      (pb_obj D F T L).interp_fml φ =
        (pb_prod F _ n).inv ≫ whiskerLeft F.op (L.interp_fml φ) ≫ pb_prop F := by
        simp[Iso.inv_comp_eq,pb_prop_interp_fml]



    def pb_prop_preserves_interp (L : Str T.sig D) (s : sequent T.sig) :
       L.model s → (pb_obj D F T L).model s := by
      intros h
      simp [Str.model, pb_prop_interp_fml']
      apply SubobjectClassifier.le_iso
      apply pb_prop_le F
      apply h



    instance : Category (Mod T C) where
    Hom M M':= M.str ⟶ M'.str
    id M := 𝟙 M.str
    comp := Str.category.comp

    noncomputable

    def pb_model (M: Mod T D ) : Mod T C where
      str := (pullback D F T).obj M.str
      valid := by
        intros a ax
        simp[pullback]
        have := M.valid a ax
        exact (pb_prop_preserves_interp _ F T M.str a this)

    theorem nlift_diag_whisker (L₁ L₂ : Psh D)  (n : Nat) (f : (L₁ ⟶ L₂)) :
     nlift_diag (F.op ⋙ L₁) (F.op ⋙ L₂) n (CategoryTheory.whiskerLeft F.op f) =
    (pb_prod F L₁ n).inv ≫
    CategoryTheory.whiskerLeft F.op
    (nlift_diag L₁ L₂ n f) ≫
    (pb_prod F L₂ n).hom := by
     simp[← Category.assoc]
     simp only[← Iso.comp_inv_eq]
     simp[nlift_diag]
     simp[nlift_whisker]

    def pb_morphism (X Y : Mod T D) (f : X ⟶ Y) :
     pb_model D F T X ⟶ pb_model D F T Y where
       map := CategoryTheory.whiskerLeft F.op f.map
       ops_comm := by
        simp[pb_model,pullback,pb_obj_carrier]
        simp[nlift_diag_whisker]
        simp[← pb_obj_interp_ops0]
        simp[← CategoryTheory.whiskerLeft_comp]
        simp[f.ops_comm]
       preds_comm := by
        simp[pb_model,pullback,pb_obj_carrier]
        simp[nlift_diag_whisker]
        simp[pb_obj_interp_preds]
        simp[← Category.assoc]
        simp[← CategoryTheory.whiskerLeft_comp]
        simp[f.preds_comm]

    noncomputable
    def pullback_Mod : Mod T D ⥤ Mod T C where
    obj M := pb_model D F T M
    map f := pb_morphism _ F T _ _ f
    /-def model {S : monosig} (L : Str S C) (s : sequent S) : Prop :=
   L.interp_fml s.premise ≤ L.interp_fml s.concl
   structure sequent (m : monosig) where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx

   -/

   --theorem sequent_fields {T : theory} {n : RenCtx} (a : sequent T.sig):
  theorem subst_interp_tm  (L: Str S C) (n : RenCtx) (m : Subst S) (σ : Fin n → tm S m) (t: tm S n) :
   L.interp_tm (tm.subst σ t) =
   npair (npow L.carrier m) L.carrier n (fun i => L.interp_tm (σ i)) ≫ L.interp_tm t := by
     induction t with
     | var _ => sorry
     | op o _ _ => sorry


  theorem subst_interp_fml (L: Str S C) (n : RenCtx) (m : Subst S) (σ : Fin n → tm S m) (φ: fml S n) :
   L.interp_fml (fml.subst σ φ) =
   npair (npow L.carrier m) L.carrier n (fun i => L.interp_tm (σ i)) ≫ L.interp_fml φ := by
    induction φ with
    | pred p _ => sorry
    | true => sorry
    | false => sorry
    | conj _ _ _ _ => sorry
    | disj _ _ _ _ => sorry
    | infdisj _ _ => sorry
    | eq _ _ => sorry
    | existsQ _ _ => sorry


  theorem interp_fml_true (L: Str S C) (n : RenCtx) :  @Str.interp_fml C _ n S L fml.true = ⊤ := by
    simp[Str.interp_fml ,SubobjectClassifier.complete_lattice_to_prop]

  theorem interp_fml_false (L: Str S C) (n : RenCtx) :  @Str.interp_fml C _ n S L fml.false = ⊥ := by
    simp[Str.interp_fml ,SubobjectClassifier.complete_lattice_to_prop]

  theorem interp_fml_conj (L: Str S C) (n : RenCtx) (φ ψ: fml S n) :
    Str.interp_fml L (φ.conj ψ) =
    SubobjectClassifier.complete_lattice_to_prop.inf (Str.interp_fml L φ) (Str.interp_fml L ψ) := by
    simp only[SubobjectClassifier.complete_lattice_to_prop_inf,Str.interp_fml]

  theorem interp_fml_disj (L: Str S C) (n : RenCtx) (φ ψ: fml S n) :
    Str.interp_fml L (φ.disj ψ) =
    SubobjectClassifier.complete_lattice_to_prop.sup (Str.interp_fml L φ) (Str.interp_fml L ψ) := by
    simp only[SubobjectClassifier.complete_lattice_to_prop_sup,Str.interp_fml]

  theorem SemilatticeInf_Lattice_inf {α : Type u} [Lattice α] (a b:α) : SemilatticeInf.inf a b = Lattice.inf a b := rfl

  theorem interp_fml_infdisj (L: Str S C) (n : RenCtx) (φ : ℕ → fml S n) :
    Str.interp_fml L (fml.infdisj φ) =
    SubobjectClassifier.complete_lattice_to_prop.sSup {Str.interp_fml L (φ i) |( i: ℕ ) } := by
     sorry--need to fill the sorry for infdisj!

  --theorem lift_same_eq_app  (X Y: Psh D) (f: X ⟶ Y)

  theorem lift_same_eq (X Y: Psh D) (f: X ⟶ Y): ChosenFiniteProducts.lift f f ≫ SubobjectClassifier.eq = ⊤ := by
    ext dop a
    simp only[SubobjectClassifier.complete_lattice_to_prop]
    simp
    ext d' g
    simp[SubobjectClassifier.top_app]
    simp[SubobjectClassifier.eq]
    congr

    theorem interp_fml_eq_refl (L: Str S C) (n : RenCtx) (t: tm S n) :
    Str.interp_fml L (fml.eq t t) = ⊤ := by
    simp only[Str.interp_fml]
    simp only[lift_same_eq]



  theorem soundness {T : theory} {n : RenCtx} (M:Mod T D) (φ ψ: fml T.sig n)
     (h:Hilbert.proof φ ψ): InterpPsh.Str.model M.str (sequent.mk _ φ ψ) := by
      induction h with
      | «axiom» _ =>
         rename_i a m σ hyp
         have := M.valid a hyp
         simp[InterpPsh.Str.model] at *
         simp[subst_interp_fml]
         apply BaseChange.SubobjectClassifier.prop_le_precomp
         assumption
      | cut phi2tau tau2psi Mphitau Mtaupsi =>
        simp[InterpPsh.Str.model] at *
        apply SubobjectClassifier.complete_lattice_to_prop.le_trans
        assumption
        assumption
      | var =>
        simp[InterpPsh.Str.model]
      | true_intro =>
        simp[InterpPsh.Str.model,interp_fml_true]
      | false_elim a a_ih =>
        rename_i n φ ψ
        simp[InterpPsh.Str.model,interp_fml_false] at *
        --have := (@SubobjectClassifier.complete_lattice_to_prop _ _ (npow M.str.carrier n)).le_trans
        apply SubobjectClassifier.complete_lattice_to_prop.le_trans
        assumption
        simp[bot_le]
      | conj_intro _ _ _ _ =>
        rename_i n a φ ψ pphi ppsi h1 h2
        simp[InterpPsh.Str.model] at *
        simp only[interp_fml_conj]
        apply SubobjectClassifier.complete_lattice_to_prop.le_trans
        have := @SemilatticeInf.le_inf _ _ (M.str.interp_fml a) (M.str.interp_fml φ) (M.str.interp_fml ψ)
        apply this
        · assumption
        · assumption
        simp[SemilatticeInf_Lattice_inf]
      | conj_elim_l =>
        simp[InterpPsh.Str.model,interp_fml_conj]
        apply SubobjectClassifier.complete_lattice_to_prop.inf_le_left
      | conj_elim_r =>
        simp[InterpPsh.Str.model,interp_fml_conj]
        apply SubobjectClassifier.complete_lattice_to_prop.inf_le_right
      | disj_intro_l =>
        simp[InterpPsh.Str.model,interp_fml_disj]
        apply SubobjectClassifier.complete_lattice_to_prop.le_sup_left
      | disj_intro_r =>
        simp[InterpPsh.Str.model,interp_fml_disj]
        apply SubobjectClassifier.complete_lattice_to_prop.le_sup_right
      | disj_elim _ _ _ _ _ _ =>
        rename_i n f1 f2 f3 f4 f1pf2orf3 f2cf1pf4 f3cf1pf4 h1 h2 h3
        simp[InterpPsh.Str.model,interp_fml_conj,interp_fml_disj] at *
        set a := M.str.interp_fml f1 with a_def
        set b := M.str.interp_fml f2 with b_def
        set c := M.str.interp_fml f3 with c_def
        set d := M.str.interp_fml f4 with d_def
        simp[← a_def,← b_def,← c_def,← d_def] at *
        sorry
      | infdisj_intro =>
        simp[InterpPsh.Str.model,interp_fml_infdisj]
        apply SubobjectClassifier.complete_lattice_to_prop.le_sSup
        simp
      | infdisj_elim _ _ _ _ => sorry
      | eq_intro =>
        simp[InterpPsh.Str.model]
        simp[interp_fml_eq_refl,interp_fml_true]
      | eq_elim φ γ _ _ _ _ =>
        simp[InterpPsh.Str.model] at *
        rename_i n f t1 t2 p1 p2 h1 h2
        --use subst interp lemmas
        sorry
      | existsQ_intro φ =>
        rename_i n t
        simp[InterpPsh.Str.model]
        intros dop x l
        simp[l]
        intros d' f h
        simp[SubobjectClassifier.existQ_app_arrows,Str.interp_fml,SubobjectClassifier.existπ]

        sorry
      | existsQ_elim =>
        rename_i n φ
        simp[InterpPsh.Str.model]
        sorry
      | ren _ _ => sorry








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
