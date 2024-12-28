
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category


namespace NatIso
open CategoryTheory

noncomputable
def ofNatTrans {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : (F ≅ G) :=
  NatIso.ofComponents (fun c => asIso (θ.app c)) (fun f => θ.naturality f)

noncomputable
def ofNatTrans' {C D} [Category C] [Category D] {F G : C ⥤ D} (θ : F ⟶ G) (h : forall c, IsIso (θ.app c)) : IsIso θ :=
  Iso.isIso_hom (ofNatTrans θ h)

end NatIso
