import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.GaloisConnection.Defs

-- Collection of lemmas that should either be upstreamed in Mathlib or don't have a definite place in the repo

namespace Fin
/-- `castAdd' m i` embeds `i : Fin m` in `Fin (n+m)`. See also `Fin.natAdd` and `Fin.addNat`. -/
@[inline] def castAdd' (n) : Fin m → Fin (n + m) :=
  castLE <| Nat.le_add_left m n

@[simp] theorem castAdd'_castLT (n : Nat) (i : Fin (n + m)) (hi : i.val < m) :
    castAdd' n (castLT i hi) = i := rfl

@[simp] theorem coe_castAdd' (m : Nat) (i : Fin n) : (castAdd' m i : Nat) = i := rfl

theorem castAdd'_lt {m : Nat} (n : Nat) (i : Fin m) : (castAdd' n i : Nat) < m := by simp

/-- Define `f : Π i : Fin (m + n), motive i` by separately handling the cases `i = addNat j n`,
`j : Fin m` and `i = castadd' m j`, `j : Fin n`. -/
@[elab_as_elim] def casesAdd {m n : Nat} {motive : Fin (m + n) → Sort u}
    (left : ∀ i : Fin m, motive (addNat i n)) (right : ∀ i : Fin n, motive (castAdd' m i))
    (i : Fin (m + n)) : motive i :=
  if hi : (i : Nat) < n then (castAdd'_castLT m i hi) ▸ (right (castLT i hi))
  else (addNat_subNat (Nat.le_of_not_lt hi)) ▸ (left _)

@[simp] theorem casesAdd_left {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin m) :
    casesAdd (motive := motive) left right (addNat i n) = left i := by
  have : ¬(addNat i n : Nat) < n := Nat.not_lt.2 (le_coe_addNat ..)
  rw [casesAdd, dif_neg this]; exact eq_of_heq <| (eqRec_heq _ _).trans (by congr 1; simp)

@[simp]
theorem casesAdd_right {m n : Nat} {motive : Fin (m + n) → Sort _} {left right} (i : Fin n) :
    casesAdd (motive := motive) left right (castAdd' m i) = right i := by
  rw [casesAdd, dif_pos (castAdd'_lt _ _)]; rfl

end Fin


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


namespace CompleteLatticeLemma
  variable {α : Type u} [CompleteLattice α]

  theorem inf_disj_elim_helper
    (inf_iSup_distr : forall {I : Type u'} a (b : I → α), a ⊓ (⨆ i, b i) ≤ ⨆ i, a ⊓ b i)
    {I : Type u'} (b : I → α) (h₁ : a ≤ ⨆ i, b i) (h₂ : forall i, b i ⊓ a ≤ c) : a ≤ c := by
    calc
      a ≤ a ⊓ (⨆ i, b i) := by simp [le_sup_left, h₁]
      _ ≤ ⨆ i, (a ⊓ b i) := by apply inf_iSup_distr a b
      _ ≤ ⨆ i, (b i ⊓ a) := by simp [inf_comm]
      _ ≤ c := by simp [sSup_le, h₂]

  theorem disj_elim_helper (A: Type) [Lattice A] (a b c d: A)
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


end CompleteLatticeLemma



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

