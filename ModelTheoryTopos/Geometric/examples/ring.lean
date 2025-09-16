import ModelTheoryTopos.Geometric.Syntax.Derivation

open CategoryTheory Limits Signature
namespace Signature

inductive RingSymbols where
  | plus : RingSymbols
  | zero : RingSymbols
  | neg : RingSymbols
  | mul : RingSymbols
  | one : RingSymbols

notation3 "R" => DerivedSorts.inj ()

def RingSignature : Signature where
  Sorts := Unit
  Functions := {
    Symbols := RingSymbols
    domain f := match f with
    | .plus => .prod ![R, R]
    | .mul => .prod ![R, R]
    | _ => R
    codomain _ := R
  }
  Relations := {
    Symbols := Empty
    domain e := Empty.elim e
  }

instance {xs : RingSignature.Context} : Add (⊢ᵗ[xs] R) where
  add t t' := Term.func RingSymbols.plus (.pair (Fin.cons t <| Fin.cons t' finZeroElim))

instance {xs : RingSignature.Context} : Mul (⊢ᵗ[xs] R) where
  mul t t' := Term.func RingSymbols.mul (.pair (Fin.cons t <| Fin.cons t' finZeroElim))

instance : RingSignature.SmallUniverse where
  type := ℕ

class DecideTrue (p : Prop) [Decidable p] where
  isTrue : p

instance (p : Prop) (h : p) : @DecideTrue p (.isTrue h) :=
  @DecideTrue.mk _ (.isTrue h) h

instance [Decidable p] [DecideTrue p] : Fact p where
  out := DecideTrue.isTrue

instance foo {n : ℕ} {xs : Fin (n + 1) → RingSignature} (i : ℕ) [Fact (i < n + 1)]:
    OfNat (⊢ᵗ[⟨n+1,xs⟩] (xs ⟨i,Fact.out⟩)) i where
  ofNat := .var (xs := ⟨n+1,xs⟩) ⟨i,Fact.out⟩

def RingTheory : RingSignature.Theory where
  axioms := {
    ⟨⟨2, fun _ => R⟩, ⊤', (0 + 1 : ⊢ᵗ[_] R) =' 1 + 0⟩,
    ⟨⟨3, fun _ => R⟩, ⊤', (0 + 1 + 2 : ⊢ᵗ[_] R) =' (0 + (1 + 2))⟩,
    ⟨⟨3, fun _ => R⟩, ⊤', (0 * 1 * 2 : ⊢ᵗ[_] R) =' (0 * (1 * 2))⟩
    -- write all axioms
    }
