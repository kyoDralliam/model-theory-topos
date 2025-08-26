import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation

namespace Matrix

universe u

variable {α : Type u}

section MatrixNotation

@[simp]
theorem vecAppend_empty {n} (v : Fin n → α) : vecAppend rfl v ![] = v := by
  ext
  simp [vecAppend_eq_ite]

def vecLast {α} {n : ℕ} (v : Fin n.succ → α) : α :=
  v (Fin.last n)

def vecInit {α} {n : ℕ} (v : Fin n.succ → α) : Fin n → α :=
  fun i ↦ v ⟨i.1, Nat.lt_succ_of_lt i.2⟩

def vecSnoc {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
  vecAppend rfl t (fun (_ : Fin 1) ↦ h)

@[simp]
lemma snoc_last_init {α} {n : ℕ} (v : Fin n.succ → α) :
  vecSnoc (vecLast v) (vecInit v) = v := by
  ext ⟨x, p⟩
  simp [vecSnoc, vecAppend_eq_ite, vecLast, Fin.last]
  split
  · extract_goal
    rfl
  · grind

@[simp]
lemma vecAppend_init {o n m : ℕ} {p : o = n + m} (v : Fin n → α) (w : Fin (m + 1) → α) :
  vecInit (vecAppend (by grind) v w) = vecAppend p v (vecInit w) := by
  ext ⟨x, p⟩
  simp [vecInit, vecAppend_eq_ite]

-- This should be in another file
@[simp]
lemma Fin.append_last {n m} (v : Fin n → α) (w : Fin (m + 1) → α) :
  Fin.append v w (Fin.last (n + m)) = w (Fin.last m) := by
  simp [Fin.append, Fin.last, Fin.addCases]
  split <;> grind

@[simp]
lemma vecLast_Append {o n m : ℕ} {p : o + 1 = n + (m + 1)}
  (v : Fin n → α) (w : Fin (m + 1) → α) :
  vecLast (vecAppend p v w) = vecLast w := by simp [vecAppend, vecLast]
