import Mathlib.Data.List.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import ModelTheoryTopos.Syntax.Signature


inductive fml (m : monosig) : RenCtx -> Type where
--inductive fml.{u} (m : monosig) : RenCtx -> Type (u+1) where
  | pred : (p : m.preds) -> (Fin (m.arity_preds p) -> tm m n) -> fml m n
  | true : fml m n
  | false : fml m n
  | conj : fml m n -> fml m n -> fml m n
  | disj : fml m n -> fml m n -> fml m n
  | infdisj : (Nat -> fml m n) -> fml m n
--  | infdisj : (A : Type u) -> (A -> fml m n) -> fml m n
  | eq : tm m n -> tm m n -> fml m n
  | existsQ : fml m (n + 1) -> fml m n

def fml.existsn : {n' : Nat} -> fml m (n + n') -> fml m n
| 0, φ => φ
| _+1, φ => existsn φ.existsQ

def fml.conjn (k : ℕ) (fs: Fin k -> fml m n): fml m n :=
  (List.ofFn fs).foldr .conj .true

def fml.eqs (lhs rhs : Fin k -> tm m n) : fml m n :=
  fml.conjn k fun i => .eq (lhs i) (rhs i)


-- x1, .., xn | φ ⊢ ψ
structure sequent (m : monosig) where
  ctx : Nat
  premise : fml m ctx := .true
  concl : fml m ctx


structure theory where
  sig : monosig
  axioms : List (sequent sig)

def fml.ren {n n' : RenCtx} (f : n ⟶ n') : fml m n -> fml m n'
| .pred p k => .pred p (fun i => (k i).ren f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.ren f) (ψ.ren f)
| .disj φ ψ => .disj (φ.ren f) (ψ.ren f)
| .infdisj φ => .infdisj (fun i => (φ i).ren f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).ren f)
| .eq t u => .eq (t.ren f) (u.ren f)
| .existsQ φ => .existsQ (φ.ren (lift f))

def fml.subst {n n' : Subst m} (f : n ⟶ n') : fml m n → fml m n'
| .pred p k => .pred p (fun i => (k i).subst f)
| .true => .true
| .false => .false
| .conj φ ψ => .conj (φ.subst f) (ψ.subst f)
| .disj φ ψ => .disj (φ.subst f) (ψ.subst f)
| .infdisj φ => .infdisj (fun i => (φ i).subst f)
-- | .infdisj A φ => .infdisj A (fun a => (φ a).subst f)
| .eq t u => .eq (t.subst f) (u.subst f)
| .existsQ φ => .existsQ (φ.subst (lift_subst f))

open CategoryTheory

theorem fml.ren_id {n : RenCtx} (f : fml m n)
  : fml.ren (𝟙 n) f = f := by
  induction f with
  | pred => simp [ren] ; funext i ; simp [tm.ren_id]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [ren] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [ren] ; funext i ; apply ih
  | eq t u => simp [ren, tm.ren_id]
  | existsQ φ ih => simp [ren, lift_id, ih]

theorem fml.ren_comp (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  ren (f ≫ g) t = ren g (ren f t) := by
  induction t generalizing n2 n3 with
  | pred => simp [ren] ; funext i ; simp [tm.ren_comp]
  | true | false => simp [ren]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [ren] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [ren] ; funext i ; apply ih
  | eq t u => simp [ren, tm.ren_comp]
  | existsQ φ ih => simp [ren, lift_comp, ih]

theorem lift_subst_id (n : Subst m) : lift_subst (𝟙 n) = 𝟙 (n+1: Subst m) := by
  funext i ; simp [lift_subst, CategoryStruct.id]
  induction i using Fin.cases <;> simp [RelativeMonad.ret, tm.ren]

theorem lift_subst_comp : lift_subst (f ≫ g) = lift_subst f ≫ lift_subst g := by
  funext i ; simp [lift_subst, CategoryStruct.comp]
  induction i using Fin.cases with
    | zero => simp [RelativeMonad.bind, tm.subst, lift_subst]
    | succ i =>
      simp [RelativeMonad.bind, <-tm.ren_subst_comp, <-tm.subst_ren_comp]
      congr; ext x; simp [CategoryStruct.comp, tm.ren_map, lift_subst]
      rfl


theorem fml.subst_id {n : Subst m} (f : fml m n)
  : subst (𝟙 n) f = f := by
  induction f with
  | pred => simp [subst] ; funext i ; simp [tm.subst_id]
  --  ; simp [tm.subst_id]
  | true | false => simp [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [subst] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [subst] ; funext i ; apply ih
  | eq t u => simp [subst, tm.subst_id]
  | existsQ φ ih => simp [subst, lift_subst_id, ih]

theorem fml.subst_comp {n1 n2 n3 : Subst m} (f : n1 ⟶ n2) (g : n2 ⟶ n3) (t : fml m n1):
  subst (f ≫ g) t = subst g (subst f t) := by
  induction t generalizing n2 n3 with
  | pred => simp [subst] ; funext i ; simp [tm.subst_comp]
  | true | false => simp [subst]
  | conj φ ψ ihφ ihψ | disj φ ψ ihφ ihψ =>
    simp [subst] ; constructor <;> simp [ihφ, ihψ]
  | infdisj φ ih => simp [subst] ; funext i ; apply ih
  | eq t u => simp [subst, tm.subst_comp]
  | existsQ φ ih => simp [subst, lift_subst_comp, ih]

def Fml m : Subst m ⥤ Type where
  map := fml.subst
  map_id := by intros ; funext t ; simp [fml.subst_id]
  map_comp := by intros ; funext t ; simp [fml.subst_comp]

-- def fml.subst_fst (t : (Fml m).obj (n+1)) (a : tm m n) : fml m n :=
--   t[a..]

def ListFunctor : Type ⥤ Type where
  map := List.map

def Ctx m : Subst m ⥤ Type := Fml m ⋙ ListFunctor


-- Is there a way to make Ctx transparent enough for typeclass search ?
instance: HAppend (List (fml m n)) ((Ctx m).obj n) (List (fml m n)) where
  hAppend := fun l l' => let l'' : List (fml m n) := l' ; l ++ l''

abbrev FmlCtx (T : theory) n := List (fml T.sig n)

inductive proof {T : theory}: {n : RenCtx} → FmlCtx T n → fml T.sig n → Prop where
  | axiom : s ∈ T.axioms -> proof Γ (s.premise.subst σ) -> proof Γ (s.concl.subst σ)
  -- | cut : (forall φ, φ ∈ Δ -> proof Γ φ) -> proof Δ ψ -> proof Γ ψ
  | var : φ ∈ Γ → proof Γ φ
  | true_intro : proof Γ .true
  | false_elim : proof Γ .false → proof Γ φ
  | conj_intro : proof Γ φ → proof Γ ψ → proof Γ (.conj φ ψ)
  | conj_elim_l : proof Γ (.conj φ  ψ) → proof Γ φ
  | conj_elim_r : proof Γ (.conj φ  ψ) → proof Γ ψ
  | disj_intro_l : proof Γ φ → proof Γ (.disj φ ψ)
  | disj_intro_r : proof Γ ψ → proof Γ (.disj φ ψ)
  | disj_elim : proof Γ (.disj φ ψ) →
    proof (φ :: Γ) ξ → proof (ψ :: Γ) ξ → proof Γ ξ
  | infdisj_intro : proof Γ (φ k) → proof Γ (.infdisj φ)
  | infdisj_elim : proof Γ (.infdisj φ) →
    (forall k, proof (φ k :: Γ) ξ) → proof Γ ξ
  | eq_intro : proof Γ (.eq t t)
  | eq_elim (φ : (Fml _).obj _) (Γ : (Ctx _).obj _) : proof Δ (.eq t u) →
    proof (Δ ++ Γ[t..]) (φ[t..]) →
    proof (Δ ++ Γ[u..]) (φ[u..])
  | existsQ_intro (φ : (Fml _).obj _) : proof Γ (φ[t..]) → proof Γ (.existsQ φ)
  | existsQ_elim : proof Γ (.existsQ φ) →
    proof (List.map (fml.ren Fin.succ) Γ) φ


theorem proof.weaken {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> φ ∈ Γ), proof Γ ψ :=
  by sorry

-- TODO: cut could be made admissible ; requires weakening first
theorem proof.cut {T : theory} n (Δ : FmlCtx T n) ψ (hψ : proof Δ ψ) : forall Γ (hsub : forall φ, φ ∈ Δ -> proof Γ φ), proof Γ ψ := by
  induction hψ with
  | «axiom» _ _ ih =>
    intros ; apply proof.axiom ; assumption ; apply ih ; assumption
  | var hin => intros Γ hsub; apply hsub ; assumption
  | true_intro => intros ; apply true_intro
  | false_elim _ _ => sorry
  | conj_intro _ _ ih₁ ih₂ =>
    intros; apply conj_intro
    · apply ih₁ ; assumption
    · apply ih₂ ; assumption
  | conj_elim_l _ ih => intros; apply conj_elim_l <;> apply ih ; assumption
  | conj_elim_r _ ih => intros; apply conj_elim_r <;> apply ih ; assumption
  | disj_intro_l _ ih => intros; apply disj_intro_l ; apply ih ; assumption
  | disj_intro_r _ ih => intros; apply disj_intro_r ; apply ih ; assumption
  | disj_elim h hl hr ih ihl ihr =>
    intros _ hsub ; apply disj_elim
    · apply ih ; assumption
    · apply ihl ; try assumption
      simp ; constructor <;> try assumption
      · apply var ; simp
      · intros ; apply weaken ; apply hsub ; assumption
        intros ; simp ; right ; assumption
    · apply ihr ; try assumption
      simp ; constructor <;> try assumption
      · apply var ; simp
      · intros ; apply weaken ; apply hsub ; assumption
        intros ; simp ; right ; assumption
  | infdisj_intro _ _ => sorry
  | infdisj_elim _ _ _ _ => sorry
  | eq_intro => sorry
  | eq_elim φ Γ _ _ _ _ => sorry
  | existsQ_intro φ _ _ => sorry
  | existsQ_elim _ _ => sorry


def sequent.derivable (T : theory) (s : sequent T.sig) := proof [s.premise] s.concl

def sequent.of_formulas (Γ : FmlCtx T n) (φ : fml T.sig n) : sequent T.sig where
  ctx := n
  premise := List.foldr .conj .true Γ
  concl := φ

theorem sequent.from_proof : proof Γ φ -> (of_formulas Γ φ).derivable := by
  intros hΓφ
  apply proof.cut _ _ _ hΓφ
  clear hΓφ
  induction Γ with
  | nil => simp
  | cons ψ Γ ih =>
    simp [of_formulas] ; constructor
    · apply proof.conj_elim_l ; apply proof.var ; simp ; rfl
    · intros τ hτ ; apply proof.cut _ _ _ (ih _ hτ) ; simp [of_formulas]
      apply proof.conj_elim_r ; apply proof.var ; simp ; rfl

theorem sequent.to_proof : (of_formulas Γ φ).derivable -> proof Γ φ := by
  intros hs ; apply proof.cut _ _ _ hs
  clear hs
  induction Γ with
  | nil => simp [of_formulas] ; apply proof.true_intro
  | cons ψ Γ ih =>
    simp [of_formulas] ; apply proof.conj_intro
    · apply proof.var ; simp
    · simp at ih ; apply proof.cut _ _ _ ih
      intros ; apply proof.var; simp ; right ; assumption

namespace Hilbert
  inductive proof {T : theory}: {n : RenCtx} → fml T.sig n → fml T.sig n → Prop where
    | axiom : s ∈ T.axioms -> proof (s.premise.subst σ) (s.concl.subst σ)
    | cut : proof φ τ -> proof τ ψ -> proof φ ψ
    | var : proof φ φ
    | true_intro : proof φ .true
    | false_elim : proof φ .false → proof φ ψ
    | conj_intro : proof ν φ → proof ν ψ → proof ν (.conj φ ψ)
    | conj_elim_l : proof (.conj φ  ψ) φ
    | conj_elim_r : proof (.conj φ  ψ) ψ
    | disj_intro_l : proof φ (.disj φ ψ)
    | disj_intro_r : proof ψ (.disj φ ψ)
    | disj_elim : proof δ (.disj φ ψ) →
      proof (φ.conj δ) ξ → proof (ψ.conj δ) ξ → proof δ ξ
    | infdisj_intro : proof (φ k) (.infdisj φ)
    | infdisj_elim : proof δ (.infdisj φ) →
      (forall k, proof (.conj (φ k) δ) ξ) → proof Γ ξ
    | eq_intro : proof .true (.eq t t)
    | eq_elim (φ γ : (Fml _).obj _) : proof δ (.eq t u) →
      proof (δ.conj (γ[t..])) (φ[t..]) →
      proof (δ.conj (γ[u..])) (φ[u..])
    | existsQ_intro (φ : (Fml _).obj _) : proof (φ[t..]) (.existsQ φ)
    | existsQ_elim : proof  phi (fml.ren Fin.succ psi) -> proof (.existsQ phi) psi
      --existsQ_elim : proof (fml.ren Fin.succ (.existsQ φ)) φ
    | ren : proof φ ψ -> proof (fml.ren ρ φ) (fml.ren ρ ψ)

end Hilbert

namespace SyntacticSite


  namespace R
    def in10 : Fin n -> Fin (n + k) := Fin.castAdd k
    def in01 : Fin n -> Fin (k + n) := Fin.natAdd k
    def in101 : Fin (n + k) -> Fin (n + k + k) :=
      Fin.addCases (Fin.castAdd k ∘ Fin.castAdd k) (Fin.natAdd (n + k))
    def in110 : Fin (n + k) -> Fin (n + k + k) := Fin.castAdd k
    def in001 : Fin k -> Fin (n + k + k) := Fin.natAdd (n+k)
    def in010 : Fin k -> Fin (n + k + k) :=
      Fin.castAdd k ∘ Fin.natAdd n
  end R

structure functional {T: theory} {n1 n2 : RenCtx} (φ: fml T.sig n1) (ψ : fml T.sig n2) (θ  : fml T.sig (n1 + n2)) where
 total : Hilbert.proof φ θ.existsn
 range: Hilbert.proof θ ((φ.ren R.in10).conj (ψ.ren R.in01))
 unique : Hilbert.proof ((θ.ren R.in101).conj (θ.ren R.in110)) (fml.eqs (tm.var ∘ R.in010) (tm.var ∘ R.in001))


@[simp]
def fml_equiv {T: theory} {n : RenCtx} (φ ψ: fml T.sig n) := Hilbert.proof φ ψ ∧ Hilbert.proof ψ φ

theorem fml_equiv_Equivalence {T: theory} {n : RenCtx} : Equivalence (@fml_equiv T n) where
  refl := by
    intro φ
    simp
    apply Hilbert.proof.var
  symm := by
    intros φ ψ asm
    simp at *
    simp[asm]
  trans := by
    intro x y z a1 a2
    simp at *
    constructor <;> apply Hilbert.proof.cut (τ:=y) <;> simp [a1, a2]

structure theory_fml (T: theory) where
  ctx: RenCtx
  fml : fml T.sig n


  -- KM: The rest of the definitions in this namespace are not used, are they ?

def theory_fml_equiv (T: theory) : theory_fml T → theory_fml T → Prop := fun
  | .mk c1 f1 => fun
    | .mk c2 f2 =>
       c1 = c2 ∧
       let f11 : fml T.sig c1 := f1
       let f22 : fml T.sig c1 := f2
       fml_equiv f11 f22
      /-
 φ.n = ψ.n ∧
 let f: fml T.sig φ.n := ψ.fml
 fml_equiv φ.fml ψ.fml-/

theorem Hilbert_proof_refl {T: theory} (f :fml T.sig n ): Hilbert.proof f f := by
 have := @Hilbert.proof.var T n f
 assumption


theorem theory_fml_equiv_Equivalence : Equivalence (theory_fml_equiv T) where
  refl := by
    intros x; simp[theory_fml_equiv,fml_equiv,Hilbert_proof_refl]
  symm := sorry /-by
    intros x y asm
    simp[theory_fml_equiv] at *
    cases asm
    rename_i eq p

    have p' : @fml_equiv T y.ctx x.fml y.fml := p
    simp[asm,fml_equiv] at *
    cases asm
    rename_i l r
    constructor
    · assumption
    · assumption-/

  trans := sorry

--why def works whereas definition does not????
def theory_fml_Setoid (T: theory): Setoid (theory_fml T) where
  r := theory_fml_equiv T
  iseqv := theory_fml_equiv_Equivalence

def fml_class {T: theory} {n : RenCtx} := Quotient (theory_fml_Setoid T)


end SyntacticSite
