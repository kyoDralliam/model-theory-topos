import Mathlib.Data.Matrix.Notation

@[simp]
lemma HEq_prop (A B : Prop) (p : A = B) (a : A) (b : B) : a ≍ b := by
  induction p; rfl
