import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.GaloisConnection

namespace GaloisConnection

  variable {α : Type u} {β : Type v} [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

  instance sSupHomLeft : sSupHom α β where
    toFun := l
    map_sSup' s := by
      simp only [gc.l_sSup, sSup_image]

  instance sInfHomRight : sInfHom β α  where
    toFun := u
    map_sInf' s := by
      simp only [gc.u_sInf, sInf_image]

end GaloisConnection