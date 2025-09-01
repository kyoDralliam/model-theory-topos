import Mathlib.Data.Matrix.Notation


-- a ≍ b iff A <-> B
@[simp]
lemma HEq_prop (A B : Prop) (p : A = B) (a : A) (b : B) : a ≍ b := by
  exact heq_of_eqRec_eq p rfl
