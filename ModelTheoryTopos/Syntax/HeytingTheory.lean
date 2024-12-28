
import Mathlib.Data.List.Defs
import ModelTheoryTopos.Syntax.Signature
import ModelTheoryTopos.Syntax.GeometricLogic

namespace HeytingThy

  inductive ops where
    | conj
    | true
    | impl

  def arity_ops : ops -> Nat
    | .conj => 2
    | .impl => 2
    | .true => 0

  def heytingSig : monosig where
    ops := ops
    arity_ops := arity_ops
    preds := Unit
    arity_preds _ := 2

  def htrue : tm heytingSig n := .op .true Fin.elim0
  def hconj (t u : tm heytingSig n) : tm heytingSig n :=
    .op .conj (fun i : Fin 2 => [t, u][i])
  def himpl (t u : tm heytingSig n) : tm heytingSig n :=
    .op .impl (fun i : Fin 2 => [t, u][i])

  def le (t u : tm heytingSig n) : fml heytingSig n :=
    .pred () (fun i : Fin 2 => [t, u][i])

  def le_refl : sequent heytingSig where
    ctx := 1
    concl := le (.var 0) (.var 0)

  -- x, y, z | x <= y /\ y <= z ⊢ x <= z
  def le_trans : sequent heytingSig where
    ctx := 2
    premise := .conj (le (.var 0) (.var 1)) (le (.var 1) (.var 2))
    concl := le (.var 0) (.var 2)

  def le_antisym : sequent heytingSig where
    ctx := 2
    premise := .conj (le (.var 0) (.var 1)) (le (.var 1) (.var 0))
    concl := .eq (.var 0) (.var 1)

  def top : sequent heytingSig where
    ctx := 1
    concl := le (.var 0) htrue

  def hconj_left : sequent heytingSig where
    ctx := 2
    concl := le (hconj (.var 0) (.var 1)) (.var 0)

  def hconj_right : sequent heytingSig where
    ctx := 2
    concl := le (hconj (.var 0) (.var 1)) (.var 1)

  def hconj_univ : sequent heytingSig where
    ctx := 3
    premise := .conj (le (.var 0) (.var 1)) (le (.var 0) (.var 2))
    concl := le (.var 0) (hconj (.var 1) (.var 2))

  def himpl_curry : sequent heytingSig where
    ctx := 3
    premise := le (hconj (.var 0) (.var 1)) (.var 2)
    concl := le (.var 0) (himpl (.var 1) (.var 2))

  def himpl_uncurry : sequent heytingSig where
    ctx := 3
    premise := le (.var 0) (himpl (.var 1) (.var 2))
    concl := le (hconj (.var 0) (.var 1)) (.var 2)

  def heytingThy : theory where
    sig := heytingSig
    axioms :=
      [le_refl, le_trans, le_antisym,
        top,
        hconj_left, hconj_right, hconj_univ,
        himpl_curry, himpl_uncurry ]

end HeytingThy
