

section EquivalenceClosure
  variable {α : Type} (R : α → α → Type)

  inductive eqv : α → α → Type where
  | rfl : eqv x x
  | sym : eqv x y → eqv y x
  | trans y : eqv x y → eqv y z → eqv x z
  | base : R x y → eqv x y

  structure effectiveQuotient where
    carrier : Type
    quot : α → carrier
    sound : forall x y : α, R x y -> quot x = quot y
    -- full induction principle
    sec : carrier → α
    sec_id : forall w, quot (sec w) = w
    exact : forall x y : α, quot x = quot y -> eqv R x y

end EquivalenceClosure
