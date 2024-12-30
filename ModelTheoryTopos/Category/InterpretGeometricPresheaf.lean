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
        sorry


    def pb_prop_preserves_interp (L : Str T.sig D) (φ : fml T.sig n) :
       L.model s → (pb_obj D F T L).model s := by
      intros h
      simp [Str.model, pb_prop_interp_fml']
      apply SubobjectClassifier.le_iso
      apply pb_prop_le F
      apply h

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
