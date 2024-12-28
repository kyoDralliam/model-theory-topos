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
import ModelTheoryTopos.Category.ChosenFiniteProducts
import ModelTheoryTopos.Category.NatIso


abbrev CategoryTheory.Psh (C:Type) [Category C] := Functor Cᵒᵖ Type

open CategoryTheory MonoidalCategory ChosenFiniteProducts

namespace ChosenFiniteProducts
  variable {C : Type} [Category C]

  -- TODO: rename
  noncomputable
  def f (X : Psh C) (n : Nat) d : (npow X n).obj d ⟶ npow (X.obj d) n :=
    npair _ _ n (fun i => (nproj X n i).app d)

  theorem f_succ : f X (n+1) d = ChosenFiniteProducts.lift (ChosenFiniteProducts.fst _ _) (ChosenFiniteProducts.snd _ _ ≫ f (C:=C) X n d) := by
    simp [f, npair]; apply ChosenFiniteProducts.hom_ext <;> simp [nproj]
    · rfl
    · simp [npair_natural] ;rfl

  theorem f_iso X n d : IsIso (f (C:=C) X n d) := by
    induction n with
      | zero => exists (ChosenFiniteProducts.toUnit _)
      | succ n ih =>
        exists (𝟙 (X.obj d) ⊗ inv (f X n d)) ; constructor
        · rw [f_succ, lift_map] ; apply hom_ext <;> simp <;> rfl
        · simp [f_succ, npow]

  theorem bin_prod_pointwise (X Y : Psh C) c : (X ⊗  Y).obj c = X.obj c ⊗ Y.obj c := rfl

  theorem snd_app (X Y: Psh C)  (c: C)
    (t1: X.obj (Opposite.op c))
    (t2: Y.obj (Opposite.op c)):
    (snd X Y).app (Opposite.op c) (t1, t2) = t2 := rfl

  theorem lift_app (T X Y: Psh C) (f : T ⟶ X) (g : T ⟶ Y) (c : Cᵒᵖ) :
    (lift f g).app c = lift (f.app c) (g.app c) := rfl

  theorem lift_app_pt (T X Y: Psh C) (f : T ⟶ X) (g : T ⟶ Y) (c : Cᵒᵖ) (t : T.obj c):
    (lift f g).app c t = (f.app c t, g.app c t) := rfl

end ChosenFiniteProducts

namespace SubobjectClassifier
  variable {C : Type} [Category C]

  @[simp]
  def prop : Psh C where
    obj X := Sieve X.unop
    map h x := x.pullback h.unop
    map_id := by
      intro
      simp [Sieve.pullback_id]
      rfl
    map_comp := by
      intros
      simp [Sieve.pullback_comp]
      rfl

  def top : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊤ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp

  def bot : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊥ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp [Sieve.ext_iff]
      intros
      constructor <;> apply False.elim

  def conj : prop (C:=C) ⊗ prop  ⟶ prop where
    app X := fun p => (p.1 ⊓ p.2: Sieve X.unop)

  def disj : prop (C:=C) ⊗ prop ⟶ prop where
    app X := fun p => (p.1 ⊔ p.2 : Sieve X.unop)

  def eq {A : Psh C} : A ⊗ A ⟶ prop where
    app X := fun as =>
      {
        arrows :=  fun Y f => A.map f.op as.1 = A.map f.op as.2
        downward_closed := by
          intros _ _ _ eq _
          simp [eq]
      }
    naturality X Y f := by
      funext as
      simp [Sieve.ext_iff]
      intros Z g
      constructor <;> exact id

  def existQ {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) : B ⟶ prop where
    app X := fun b =>
      {
        arrows := fun Y f => exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y)
        downward_closed := by
          intro Y Z f ⟨a, ⟨eq, h⟩⟩ g
          let a' := A.map g.op a
          exists a'
          constructor
          · calc p.app (Opposite.op Z) a' = (A.map g.op ≫ p.app _) a := rfl
            _ = (p.app _ ≫ B.map g.op) a := by rw [p.naturality g.op]
            _ = B.map (g ≫ f).op b := by simp [eq]
          · have eq : φ.app _ a' = prop.map g.op (φ.app _ a) := by
              calc φ.app _ a' = (A.map g.op ≫ φ.app _) a := rfl
              _ = (φ.app _ ≫ prop.map g.op) a := by rw [φ.naturality g.op]
              _ = prop.map g.op (φ.app _ a) := rfl
            simp [eq]
            have := (φ.app _ a).downward_closed h g
            simp at this
            exact this
      }

  theorem existQ_app_arrows {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) (X: Cᵒᵖ) (b: B.obj X) (Y: C) (f: Y ⟶ Opposite.unop X):
    ((existQ p φ).app X b).arrows  f = exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y) := rfl



  -- def existQ {A B : Psh C} (p : A ⟶ B) : B ⟶ prop C where
  --   app X := fun b =>
  --     {
  --       arrows := fun Y f => exists a, p.app (Opposite.op Y) a = B.map f.op b
  --       downward_closed := by
  --         intro Y Z f ⟨a, h⟩ g
  --         exists (A.map g.op a)
  --         calc p.app (Opposite.op Z) (A.map g.op a) = (A.map g.op ≫ p.app _) a := rfl
  --         _ = (p.app _ ≫ B.map g.op) a := by rw [p.naturality g.op]
  --         _ = B.map (g ≫ f).op b := by simp [h]
  --     }

  noncomputable
  def existπ {A B : Psh C} (φ : A ⊗ B ⟶ prop) : B ⟶ prop := existQ (snd A B) φ

end SubobjectClassifier

namespace BaseChange
  variable {C D : Type} [Category C] [Category D] (F : Functor C D)

  namespace ChosenFiniteProducts

    noncomputable
    def pb_prod0 (X : Psh D) (n : Nat) : F.op ⋙ npow X n ⟶ npow (F.op ⋙ X) n :=
      npair _ (F.op ⋙ X) n (fun i => whiskerLeft F.op (nproj X n i))

    def ev (c : Cᵒᵖ) : Psh C ⥤ Type where
      obj := fun X => X.obj c
      map := fun f => f.app c

    theorem ev_map c {X Y : Psh C} (f : X ⟶ Y) : (ev c).map f = f.app c := rfl
    theorem pb_prob0_comm_lemma (X : Psh D) n c :
     ((pb_prod0 F X n).app c) ≫ (ChosenFiniteProducts.f (C:=C) (F.op ⋙ X) n c) = ChosenFiniteProducts.f (C:=D) X n (F.op.obj c) := by
      let h1 := (pb_prod0 F X n).app c
      let h2 := ChosenFiniteProducts.f (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := ChosenFiniteProducts.f X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, ChosenFiniteProducts.f, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod0 F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod0, npair_nproj] at this
        simp [this, ev_map,pb_prod0 ]
      simp[h1,h2,h3,d] at eq
      exact eq

    theorem pb_prod0_succ (X : Psh D) (m : Nat) :
      pb_prod0 F X (m + 1) =
        lift
          (whiskerLeft F.op (ChosenFiniteProducts.fst _ _))
          (whiskerLeft F.op (ChosenFiniteProducts.snd _ _) ≫ pb_prod0 F X m) := by
      simp [pb_prod0, npair]
      congr
      simp [<-npair_natural]
      congr


    theorem pb_prod0_pair (X : Psh D) (m : Nat) (Y: C)
     (t1: (F.op ⋙ X).obj (Opposite.op Y))
     (tm: (F.op ⋙ npow X m).obj (Opposite.op Y)):
    (pb_prod0 F X (m + 1)).app (Opposite.op Y) (t1, tm) =
    (t1, (pb_prod0 F X m).app (Opposite.op Y) tm) := by
      simp [pb_prod0_succ]
      congr
      /-let k0 : (npow X (m + 1)).obj (F.op.obj (Opposite.op Y)) := (t1, tm)
      let h1 := (pb_prod0 F X (m+1)).app (Opposite.op Y)
      let k1 := h1 k0
      let h2 := ChosenFiniteProducts.f (F.op ⋙ X) (m+1) (Opposite.op Y)
      let d := F.op.obj (Opposite.op Y)
      let h3 := ChosenFiniteProducts.f X (m+1) d
      have eq : h1 ≫ h2 = h3 := by
       have a00 := pb_prob0_comm_lemma F X (m+1) (Opposite.op Y)
       simp[h1,h2,h3,d]
       exact a00
      have a1: (pb_prod0 F X (m + 1)).app (Opposite.op Y) (t1, tm) = h1 k0 := by
       simp[h1,k0]

      let a2:= h2 (h1 k0)
      have e0 : h2 (h1 k0) = (h1 ≫ h2) k0 := by simp
      simp only [eq] at e0
      simp only [h3,k0] at e0
      simp only [ChosenFiniteProducts.f_succ] at e0
      have eid: (fst (X.obj d) ((npow X m).obj d)) = (fst (X.obj d) ((npow X m).obj d)) ≫ 𝟙 (X.obj d) := by simp
      rw[eid] at e0
      simp only[CategoryTheory.ChosenFiniteProducts.lift_fst_comp_snd_comp] at e0
      simp at e0

      let h1' := (pb_prod0 F X m).app (Opposite.op Y)
      let h2' := ChosenFiniteProducts.f (F.op ⋙ X) m (Opposite.op Y)

      let h3' := ChosenFiniteProducts.f X m d
      have eq' : h1' ≫ h2' = h3' := by
       have a000 := pb_prob0_comm_lemma F X m (Opposite.op Y)
       simp[h1',h2',h3',d]
       exact a000


      simp only[a1]
      have ff : (h1≫ h2) k0 = h2 (t1, (pb_prod0 F X m).app (Opposite.op Y) tm) := by
       simp[k0]
       simp[e0]
       simp[h2,ChosenFiniteProducts.f_succ]
       have eid' : (fst (X.obj (Opposite.op (F.obj Y))) ((npow (F.op ⋙ X) m).obj (Opposite.op Y))) =
        (fst (X.obj (Opposite.op (F.obj Y))) ((npow (F.op ⋙ X) m).obj (Opposite.op Y)))≫ 𝟙 _ := by simp
       rw[eid']
       simp only[CategoryTheory.ChosenFiniteProducts.lift_fst_comp_snd_comp]
       simp []
       have al: ChosenFiniteProducts.f X m d tm = h3' tm := by
        simp[h3']
       have a: ChosenFiniteProducts.f X m d tm = ChosenFiniteProducts.f (F.op ⋙ X) m (Opposite.op Y) ((pb_prod0 F X m).app (Opposite.op Y) tm) := by
        simp[al]
        simp[← eq']
       simp[a]


       --simp[Prod.mk.inj_iff] why not work? qqqqq
      have iso2 : IsIso h2 := ChosenFiniteProducts.f_iso (F.op ⋙ X) (m+1) (Opposite.op Y)
      have eee: (h2 ≫ inv h2)  = (𝟙 _ )  := by simp
      have eel: (h1 ≫ h2 ≫ inv h2) k0 = inv h2 ((h1 ≫ h2) k0 ) := by
        simp only [← Category.assoc]
        simp
      have ee: (h1 ≫ h2 ≫ inv h2) k0 = (h2 ≫ inv h2) (t1, (pb_prod0 F X m).app (Opposite.op Y) tm):= by
        simp only [eel]
        simp at ff
        simp[ff]
      simp only [eee] at ee
      simp at ee
      exact ee-/



    theorem pb_prob_pointwise_inv (X : Psh D) n c : IsIso ((pb_prod0 F X n).app c) := by
      let h1 := (pb_prod0 F X n).app c
      let h2 := ChosenFiniteProducts.f (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := ChosenFiniteProducts.f X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, ChosenFiniteProducts.f, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod0 F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod0, npair_nproj] at this
        simp [this, ev_map,pb_prod0 ]
      have iso2 : IsIso h2 := ChosenFiniteProducts.f_iso (F.op ⋙ X) n c
      have iso3 : IsIso h3 := ChosenFiniteProducts.f_iso X n d
      have iso12 : IsIso (h1 ≫ h2) := by rewrite [eq] ; assumption
      apply IsIso.of_isIso_comp_right h1 h2

    noncomputable
    def pb_prod (X : Psh D) (n : Nat) : F.op ⋙ npow X n ≅ npow (F.op ⋙ X) n :=
      NatIso.ofNatTrans (pb_prod0 F X n) (pb_prob_pointwise_inv F X n)


    theorem pb_prod_hom (X : Psh D) (n : Nat):
      (pb_prod F X n).hom = (pb_prod0 F X n) := rfl

    noncomputable
    def pb_prod'  (n : Nat) : npow_functor n ⋙ (whiskeringLeft _ _ _).obj F.op ≅  (whiskeringLeft _ _ Type).obj F.op ⋙ npow_functor n :=
      NatIso.ofNatTrans (npow_oplax ((whiskeringLeft _ _ Type).obj F.op)) (by
        intros X
        simp [npow_oplax]
        have:= NatIso.ofNatTrans' (pb_prod0 F X n) (pb_prob_pointwise_inv F X n)
        simp [pb_prod0] at this
        exact this)
      -- NatIso.ofNatTrans (pb_prod0 D F X n) (pb_prob_pointwise_inv D F X n)



    theorem nproj_pb_prod0 (X : Psh D)  (n: ℕ ) (i: Fin n):
   (pb_prod0 F X n)≫ (nproj (F.op ⋙ X) n i) = (whiskerLeft F.op (nproj X n i)):= by
     ext c a
     simp[npair_nproj,pb_prod0]

     theorem nproj_pb_prod0_symm (X : Psh D) (n: ℕ ) (i: Fin n):
    (whiskerLeft F.op (nproj X n i)) = (pb_prod0 F X n)≫ (nproj (F.op ⋙ X) n i) := by
     ext c a
     simp[npair_nproj,pb_prod0]

    instance nlift_whisker0 (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
    CategoryTheory.whiskerLeft F.op
    (nlift L₁ L₂ n k) ≫ (pb_prod F L₂ n).hom =
    (pb_prod F L₁ n).hom ≫ nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (fun i => CategoryTheory.whiskerLeft F.op (k i))
     := by
      apply npair_univ'
      intros i
      simp
      simp[nlift_nproj]
      simp[pb_prod_hom]
      simp[npair_nproj,pb_prod0]
      simp[← Category.assoc]
      simp[npair_nproj]
      simp[← CategoryTheory.whiskerLeft_comp]
      simp[nlift_nproj]

    theorem nlift_whisker  (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
    nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (fun i => CategoryTheory.whiskerLeft F.op (k i)) ≫
    (pb_prod F L₂ n).inv =
    (pb_prod F L₁ n).inv ≫
    CategoryTheory.whiskerLeft F.op
    (nlift L₁ L₂ n k) := by
      --why it does not work if I simplify the goal instead? QQQQQ

      have
      a:= nlift_whisker0 F L₁ L₂ n k
      symm at a
      simp [← CategoryTheory.IsIso.eq_inv_comp] at a
      simp [a]

    theorem pb_npair_compatible (P : Psh D) (n : Nat) (k: Fin n → (X ⟶  P)):
     npair (F.op⋙ X) (F.op⋙ P) n (fun i => whiskerLeft F.op (k i)) ≫ (pb_prod F P  n).inv  =
     whiskerLeft F.op (npair X P n k)
     := by
      simp[Iso.comp_inv_eq]
      apply npair_univ'
      intro i
      simp[npair_nproj]
      simp[pb_prod_hom]
      simp[nproj_pb_prod0]
      simp[← CategoryTheory.whiskerLeft_comp]
      simp[npair_nproj]

    theorem lift_app (X Y Z:Psh C) (f:X⟶ Y) (g:X⟶ Z) (c: Cᵒᵖ )
    (a : X.obj c):
    (ChosenFiniteProducts.lift f g).app c a =
    ⟨f.app c a, g.app c a⟩ := rfl--it should be somewhere in mathlib, cannot find it

    theorem whiskerLeft_lift (X Y Z:Psh D) (f:X⟶ Y) (g:X⟶ Z):
    CategoryTheory.whiskerLeft F.op
    (ChosenFiniteProducts.lift f g) =
    ChosenFiniteProducts.lift
    (CategoryTheory.whiskerLeft F.op f)
    (CategoryTheory.whiskerLeft F.op g) := by
     ext cop a
     simp[CategoryTheory.whiskerLeft_apply]
     simp[lift_app]

  end ChosenFiniteProducts



  namespace SubobjectClassifier

    def pb_prop : F.op ⋙ SubobjectClassifier.prop (C:=D) ⟶ SubobjectClassifier.prop where
      app := fun c x =>
        let x'' : Sieve (F.obj c.unop) := x
        (Sieve.functorPullback F x'' : Sieve _)

    def pb_prop_top :
      whiskerLeft F.op SubobjectClassifier.top ≫ pb_prop F  =
      SubobjectClassifier.top := by
      ext x ⟨⟩
      rfl

    def pb_prop_bot :
      whiskerLeft F.op SubobjectClassifier.bot ≫ pb_prop F  =
      SubobjectClassifier.bot := by
      ext x ⟨⟩
      rfl

    def pb_prop_conj :
      whiskerLeft F.op SubobjectClassifier.conj ≫ pb_prop F  =
      (pb_prop F ⊗ pb_prop F) ≫ SubobjectClassifier.conj := by
      ext x ⟨φ , ψ⟩
      rfl

    def pb_prop_disj :
      whiskerLeft F.op SubobjectClassifier.disj ≫ pb_prop F  =
      (pb_prop F ⊗ pb_prop F) ≫ SubobjectClassifier.disj := by
      ext x ⟨φ , ψ⟩
      rfl

    def pb_prop_eq (X : Psh D) :
      whiskerLeft F.op (SubobjectClassifier.eq (A:=X)) ≫ pb_prop F =
      SubobjectClassifier.eq (A:=F.op ⋙ X) := by
        ext x ⟨a1 , a2⟩
        apply CategoryTheory.Sieve.arrows_ext
        simp[CategoryTheory.whiskerLeft,pb_prop,
             SubobjectClassifier.eq]
        funext c0 f
        simp[Presieve.functorPullback]

    theorem pb_prop_existQ {A B : Psh D} (p: A⟶ B) (φ: A ⟶ SubobjectClassifier.prop):
      whiskerLeft F.op (SubobjectClassifier.existQ p φ)  ≫ pb_prop F =
      SubobjectClassifier.existQ (whiskerLeft F.op p) ((whiskerLeft F.op φ) ≫ pb_prop F) := by
        ext c a
        simp
        ext Y f
        simp[SubobjectClassifier.existQ_app_arrows]
        simp[pb_prop]
        simp[SubobjectClassifier.existQ_app_arrows]

  end SubobjectClassifier

end BaseChange