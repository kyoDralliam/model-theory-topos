import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Order.Hom.CompleteLattice
import ModelTheoryTopos.Misc
import ModelTheoryTopos.Category.CartesianMonoidalCategory
import ModelTheoryTopos.Category.NatIso
import ModelTheoryTopos.Category.Presheaf.Defs


open CategoryTheory MonoidalCategory CategoryTheory.CartesianMonoidalCategory


namespace CartesianMonoidalCategory
  variable {C : Type} [Category C]

  def npow_pt (X : Psh C) (n : Nat) d : (npow X n).obj d ⟶ npow (X.obj d) n :=
    npair _ _ n (fun i => (nproj X n i).app d)

  theorem npow_pt_succ : npow_pt X (n+1) d = lift (fst _ _) (snd _ _ ≫ npow_pt (C:=C) X n d) := by
    simp [npow_pt, npair_succ, nproj_zero, nproj_succ, NatTrans.comp_app, npair_natural]
    congr

  theorem npow_pt_iso X n d : IsIso (npow_pt (C:=C) X n d) := by
    induction n with
      | zero => exists (toUnit _)
      | succ n ih =>
        exists (𝟙 (X.obj d) ⊗ₘ inv (npow_pt X n d)) ; constructor
        · rw [npow_pt_succ, lift_map] ; apply hom_ext <;> simp <;> rfl
        · simp [npow_pt_succ, comp_lift] ; apply hom_ext
          · simp
            apply whiskerLeft_fst
          · have:= whiskerLeft_snd_assoc (C:=Type) (X.obj d) (inv (npow_pt X n d)) (npow_pt X n d)
            simp [this, IsIso.inv_hom_id]

  theorem bin_prod_pointwise (X Y : Psh C) c : (X ⊗ Y).obj c = X.obj c ⊗ Y.obj c := rfl

  @[simp]
  theorem fst_app (X Y: Psh C)  (c: Cᵒᵖ) (t : (X ⊗ Y).obj c) :
    (fst X Y).app c t = t.1 := rfl

  @[simp]
  theorem snd_app (X Y: Psh C)  (c: Cᵒᵖ) (t : (X ⊗ Y).obj c) :
    (snd X Y).app c t = t.2:= rfl


  theorem lift_app (T X Y: Psh C) (f : T ⟶ X) (g : T ⟶ Y) (c : Cᵒᵖ) :
    (lift f g).app c = lift (f.app c) (g.app c) := rfl

  @[simp]
  theorem lift_app_pt (T X Y: Psh C) (f : T ⟶ X) (g : T ⟶ Y) (c : Cᵒᵖ) (t : T.obj c):
    (lift f g).app c t = (f.app c t, g.app c t) := rfl

  @[simp]
  theorem tensorHom_app (X X' Y Y': Psh C) (f : X ⟶ X') (g : Y ⟶ Y') (c: Cᵒᵖ) (t : (X ⊗ Y).obj c) :
    (f ⊗ₘ g).app c t = (f.app c t.1, g.app c t.2) := rfl

  @[simp]
  theorem whiskerLeft_app (X Y Y': Psh C) (g : Y ⟶ Y') (c: Cᵒᵖ) (t : (X ⊗ Y).obj c) :
    (X ◁ g).app c t = (t.1, g.app c t.2) := rfl

  @[simp]
  theorem whiskerRight_app (X X' Y : Psh C) (f : X ⟶ X') (c: Cᵒᵖ) (t : (X ⊗ Y).obj c) :
    (f ▷  Y).app c t = (f.app c t.1, t.2) := rfl

  theorem npair_app (X Y: Psh C) n (k : Fin (n+1) -> (X ⟶ Y)) (c : Cᵒᵖ) :
    (npair X Y (n+1) k).app c = lift ((k 0).app c) ((npair X Y n (k ∘ Fin.succ)).app c) := by
    simp only [npair]
    rfl

  theorem npair_app_pt (X Y: Psh C) n (k : Fin (n+1) -> (X ⟶ Y)) (c : Cᵒᵖ) (t : X.obj c):
    (npair X Y (n+1) k).app c t = ((k 0).app c t, (npair X Y n (k ∘ Fin.succ)).app c t) := by
    simp only [npair_app]
    rfl

  theorem npow_suc_map_fst  (X: Psh C) (c c':Cᵒᵖ ) (f:c ⟶ c') (t: (npow X (n + 1)).obj c): ((npow X (n + 1)).map f t).1 =  X.map f t.1 := rfl
  theorem npow_suc_map_snd  (X: Psh C) (c c':Cᵒᵖ ) (f:c ⟶ c') (t: (npow X (n + 1)).obj c): ((npow X (n + 1)).map f t).2 = (npow X n).map f t.2 := rfl
end CartesianMonoidalCategory

namespace CartesianMonoidalCategory.BaseChange
  variable {C D : Type} [Category C] [Category D] (F : Functor C D)

  open Functor

    def pb_prod_pair (X Y : Psh D) : F.op ⋙ (X ⊗ Y) ⟶ (F.op ⋙ X) ⊗ (F.op ⋙ Y) :=
      lift
        (whiskerLeft F.op (fst _ _))
        (whiskerLeft F.op (snd _ _))

    noncomputable
    def pb_prod_pair_iso (X Y : Psh D) : F.op ⋙ (X ⊗ Y) ≅ (F.op ⋙ X) ⊗ (F.op ⋙ Y) :=
      NatIso.ofNatTrans_pt_inv
        (pb_prod_pair F X Y)
        (fun c xy ↦ xy)

    noncomputable
    def pb_prod (X : Psh D) (n : Nat) : F.op ⋙ npow X n ⟶ npow (F.op ⋙ X) n :=
      npair _ (F.op ⋙ X) n (fun i => whiskerLeft F.op (nproj X n i))

    def ev (c : Cᵒᵖ) : Psh C ⥤ Type where
      obj := fun X => X.obj c
      map := fun f => f.app c

    theorem ev_map c {X Y : Psh C} (f : X ⟶ Y) : (ev c).map f = f.app c := rfl

    theorem pb_prod_comm_lemma (X : Psh D) n c :
     ((pb_prod F X n).app c) ≫ (npow_pt (C:=C) (F.op ⋙ X) n c) =
     npow_pt (C:=D) X n (F.op.obj c) := by
      let h1 := (pb_prod F X n).app c
      let h2 := npow_pt (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := npow_pt X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, npow_pt, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod, npair_nproj] at this
        simp [this, ev_map,pb_prod ]
      simp[h1,h2,h3,d] at eq
      exact eq

    theorem pb_prod_succ (X : Psh D) (m : Nat) :
      pb_prod F X (m + 1) = pb_prod_pair F X _ ≫ (_ ◁ pb_prod F X m) := by
      simp [pb_prod, npair_succ, pb_prod_pair]
      congr
      simp [<-npair_natural]
      congr

    theorem pb_prod_succ' (X : Psh D) (m : Nat) :
      (pb_prod_pair_iso F X (npow X m)).inv ≫ pb_prod F X (m + 1) = ((F.op ⋙ X) ◁ pb_prod F X m) := by
        rw [Iso.inv_comp_eq]
        apply pb_prod_succ

    theorem pb_prob_pointwise_inv (X : Psh D) n c : IsIso ((pb_prod F X n).app c) := by
      let h1 := (pb_prod F X n).app c
      let h2 := npow_pt (F.op ⋙ X) n c
      let d := F.op.obj c
      let h3 := npow_pt X n d
      have eq : h1 ≫ h2 = h3 := by
        simp [h1, h2, h3, npow_pt, d]
        symm
        apply npair_univ
        intros i
        rw [Category.assoc, npair_nproj]
        have := (ev c).map_comp (pb_prod F X n) (nproj _ _ i)
        symm at this
        rw [ev_map, ev_map, pb_prod, npair_nproj] at this
        simp [this, ev_map,pb_prod ]
      have iso2 : IsIso h2 := npow_pt_iso (F.op ⋙ X) n c
      have iso3 : IsIso h3 := npow_pt_iso X n d
      have iso12 : IsIso (h1 ≫ h2) := by rewrite [eq] ; assumption
      apply IsIso.of_isIso_comp_right h1 h2

    noncomputable
    def pb_prod_iso (X : Psh D) (n : Nat) : F.op ⋙ npow X n ≅ npow (F.op ⋙ X) n :=
      NatIso.ofNatTrans (pb_prod F X n) (pb_prob_pointwise_inv F X n)

    theorem pb_prod_hom (X : Psh D) (n : Nat):
      (pb_prod_iso F X n).hom = (pb_prod F X n) := rfl

    theorem nproj_pb_prod (X : Psh D) (n: ℕ ) (i: Fin n):
      (pb_prod F X n)≫ (nproj (F.op ⋙ X) n i) = (whiskerLeft F.op (nproj X n i)):= by
      ext c a
      simp[npair_nproj,pb_prod]

    theorem npair_pb_prod (X Y: Psh D) (n: ℕ) (cone : Fin n → (X ⟶ Y)) :
      npair (F.op⋙ X) (F.op⋙ Y) n (fun i => whiskerLeft F.op (cone i))  =
      whiskerLeft F.op (npair X Y n cone) ≫ (pb_prod_iso F Y n).hom := by
      apply npair_univ
      intros
      simp[pb_prod_hom, nproj_pb_prod]
      simp[←Functor.whiskerLeft_comp]


    instance nlift_whisker0 (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
      whiskerLeft F.op (nlift L₁ L₂ n k) ≫ (pb_prod_iso F L₂ n).hom =
      (pb_prod_iso F L₁ n).hom ≫ nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (whiskerLeft F.op ∘ k)
     := by
      apply npair_univ'
      intros
      simp[nlift_nproj, pb_prod_hom, npair_nproj,pb_prod]
      simp[← Category.assoc, ← Functor.whiskerLeft_comp, nlift_nproj]

    theorem nlift_whisker  (L₁ L₂ : Psh D)  (n : Nat) (k : Fin n → (L₁ ⟶ L₂)):
      nlift (F.op ⋙ L₁) (F.op ⋙ L₂) n (fun i => whiskerLeft F.op (k i)) ≫ (pb_prod_iso F L₂ n).inv =
      (pb_prod_iso F L₁ n).inv ≫ whiskerLeft F.op (nlift L₁ L₂ n k) := by
      simp [Iso.comp_inv_eq]
      simp [Iso.eq_inv_comp]
      symm
      apply nlift_whisker0

    theorem nlift_diag_whisker (L₁ L₂ : Psh D)  (n : Nat) (f : (L₁ ⟶ L₂)) :
      nlift_diag (F.op ⋙ L₁) (F.op ⋙ L₂) n (whiskerLeft F.op f) =
      (pb_prod_iso F L₁ n).inv ≫ whiskerLeft F.op (nlift_diag L₁ L₂ n f) ≫ (pb_prod_iso F L₂ n).hom := by
      simp only [← Category.assoc,← Iso.comp_inv_eq,nlift_diag,nlift_whisker]

    theorem whiskerLeft_lift (X Y Z:Psh D) (f:X⟶ Y) (g:X⟶ Z):
      whiskerLeft F.op (lift f g) =
      lift (whiskerLeft F.op f) (whiskerLeft F.op g) := by
     ext cop a
     simp

end CartesianMonoidalCategory.BaseChange
