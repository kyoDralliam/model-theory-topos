
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category

namespace Iso
open CategoryTheory

theorem hom_app {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ≅ G) {c : C} :
  (Iso.app θ c).hom = θ.hom.app c := rfl

theorem inv_app {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ≅ G) {c : C} :
  (Iso.app θ c).inv = θ.inv.app c := rfl

end Iso

namespace NatIso
open CategoryTheory

noncomputable
def ofNatTrans {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : (F ≅ G) :=
  NatIso.ofComponents (fun c => asIso (θ.app c)) (fun f => θ.naturality f)

noncomputable
def ofNatTrans' {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : IsIso θ :=
  Iso.isIso_hom (ofNatTrans θ h)

def ofNatTrans_pt_inv {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G)
  (inv : forall c, G.obj c ⟶ F.obj c)
  (hom_inv_id: forall c, θ.app c ≫ inv c = 𝟙 _ := by aesop_cat )
  (inv_hom_id : forall c, inv c ≫ θ.app c = 𝟙 _:= by aesop_cat) :
  (F ≅ G) :=
  NatIso.ofComponents
    (fun c => ⟨θ.app c, inv c, hom_inv_id c, inv_hom_id c⟩)
    (fun f => θ.naturality f)

end NatIso
