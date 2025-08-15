import ModelTheoryTopos.Syntax.GeometricLogic.Defs
import ModelTheoryTopos.Syntax.GeometricLogic.Hilbert
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
import ModelTheoryTopos.Syntax.GeometricLogic.SyntacticCategory
import ModelTheoryTopos.EquivalenceClosure



open CategoryTheory


namespace WrigleyTopology
variable [SmallUniverse]

def cover_from_over.represent_renaming {m:theory} (xφ : fmlInCtx m) (σ : Over xφ)
   :fml m.sig (xφ.ctx + σ.left.ctx) :=
      .eqs (k:=xφ.ctx)
        (fun i => .var (R.in10 i)) -- x_i
        (fun i => .var (R.in01 (σ.hom.map i))) -- σ(x_i)


def cover_from_over_body  (xφ : fmlInCtx m) (σ : Over xφ):=
    let yψ := σ.left
    let yψr : fml m.sig (xφ.ctx + yψ.ctx) := yψ.formula.ren R.in01
    fml.conj yψr (cover_from_over.represent_renaming xφ σ)

def cover_from_over (xφ : fmlInCtx m) (σ : Over xφ) : fml m.sig xφ.ctx :=
    fml.existsn (cover_from_over_body  xφ σ)

open SmallUniverse

structure CoveringFamily (xφ : fmlInCtx m) where
    index : U
    maps : El index -> Over xφ
    covering : xφ.formula ⊢ fml.infdisj index (fun i => cover_from_over xφ (maps i))


noncomputable
  def ConveringFamily.pullback  {xφ yψ : fmlInCtx m}  (f: xφ ⟶ yψ) (cf: CoveringFamily yψ):
   CoveringFamily xφ where
     index := cf.index
     maps i := Over.mk (pullback_fst f (cf.maps i).hom)
     covering := sorry

def covering_family_to_presieve {xφ : fmlInCtx m} (σs : CoveringFamily xφ)
    : Presieve xφ :=
    fun _yψ f => ∃ (i : El σs.index), σs.maps i = Over.mk f

lemma covering_family_to_presieve_eval
  {xφ : fmlInCtx m} (σs : CoveringFamily xφ) {yψ : fmlInCtx m} (f: yψ ⟶ xφ)
    : covering_family_to_presieve σs f = ∃ (i : El σs.index), σs.maps i = Over.mk f :=rfl


class SmallUniverse.UniverseClosureProps [SmallUniverse] where
  uUnit : U
  utt : El uUnit
  uSigma (a : U) (b : El a -> U) : U
  elSigmaPair (x : El a) (y : El (b x)) : El (uSigma a b)
  elSigmaPi1 (p : El (uSigma a b)) : El a
  elSigmaPi2 (p : El (uSigma a b)) : El (b (elSigmaPi1 p))
  elSigmaBeta1 (x : El a) (y : El (b x)) : elSigmaPi1 (elSigmaPair (b:=b) x y) = x
  -- elSigmaBeta2 (x : El a) (y : El (b x)) : elSigmaPi2 (elSigmaPair (b:=b) x y) = elSigmaBeta1 x y ▸ iy
  elSigmaEta (p : El (uSigma a b)) : elSigmaPair (elSigmaPi1 p) (elSigmaPi2 p) = p
  --uchoice (A : U)  (X: El A → Type) (P: Π (a: El A), X a → Prop):
  -- (∀ a : El A, ∃ (xa: X a), P a xa ) → ∃f: (Π a: El A, X a), (∀ a: El A, P a (f a))
  uchoice (A : U)  (X: El A → Type) :
  (∀ a : El A, Inhabited (X a) ) → Inhabited (Π a: El A, X a)
  --Nonempty vs Inhabited?


variable [SmallUniverse.UniverseClosureProps]
open SmallUniverse.UniverseClosureProps

def id_covers (xφ : fmlInCtx m) : CoveringFamily xφ where
    index := uUnit
    maps := fun _ => Over.mk (𝟙 xφ)
    covering := by
      apply Hilbert.proof.cut (τ:=cover_from_over xφ (Over.mk (𝟙 xφ)))
      · simp [cover_from_over]
        apply Hilbert.proof.existn_intro (𝟙 _)
        apply Hilbert.proof.conj_intro
        · sorry
        · simp [cover_from_over.represent_renaming,fml.subst_eqs, tm.subst]
          apply Hilbert.proof.eqs
          intro i
          apply Hilbert.any_eq_intro
          sorry
      · apply Hilbert.proof.infdisj_intro (φ:=fun _ => _) utt

def sieves (xφ : fmlInCtx m): Set (Sieve xφ) :=
    {S : Sieve xφ |∃ σ : CoveringFamily xφ, covering_family_to_presieve σ ≤ S}

namespace Stability

variables {m} {xφ yψ zζ: fmlInCtx m} (f: xφ⟶ yψ) (g: zζ ⟶ yψ)

abbrev x2xz : Fin xφ.ctx ⟶ Fin (xφ.ctx + zζ.ctx) := R.in10
abbrev z2xz : Fin zζ.ctx ⟶ Fin (xφ.ctx + zζ.ctx) := R.in01

noncomputable
abbrev ι₁ : Fin xφ.ctx ⟶ Fin (Limits.pushout f.map g.map) := Limits.pushout.inl f.map g.map

noncomputable
abbrev ι₂ : Fin zζ.ctx  ⟶ Fin (Limits.pushout f.map g.map) := Limits.pushout.inr f.map g.map


noncomputable
abbrev z2xzw : Fin zζ.ctx ⟶ Fin (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := R.in10 ∘ R.in01
noncomputable
abbrev x2xzw : Fin xφ.ctx ⟶ Fin (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := R.in10 ∘ R.in10

noncomputable
abbrev x2w' : Fin xφ.ctx ⟶ Fin (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := R.in01 ∘ (Limits.pushout.inl f.map g.map)

noncomputable
abbrev z2w' : Fin zζ.ctx ⟶ Fin (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := R.in01 ∘ (Limits.pushout.inr f.map g.map)

abbrev w2w' : Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := R.in01


structure Rrel (i₁ i₂: Fin (xφ.ctx + zζ.ctx)) where
 i : Fin yψ.ctx
 e10 : i₁ = x2xz (f.map i)
 e01 : i₂ = z2xz (g.map i)


noncomputable
abbrev ιs  : Fin (xφ.ctx + zζ.ctx) ⟶ Fin (Limits.pushout f.map g.map) :=
Fin.casesAdd (ι₁ f g) (ι₂ f g)

structure Srel (u₁ u₂: Fin (xφ.ctx + zζ.ctx)) where
 e : ιs f g u₁ = ιs f g u₂


def gluingEqsLHS (f: xφ ⟶ yψ) (i: Fin yψ.ctx) : tm m.sig (xφ.ctx + zζ.ctx) := tm.var (R.in10 (f.map i))

def gluingEqsRHS (g: zζ ⟶ yψ) (i: Fin yψ.ctx) : tm m.sig (xφ.ctx + zζ.ctx) := tm.var (R.in01 (g.map i))


def gluingEqs (f: xφ⟶ yψ) (g: zζ ⟶ yψ) : fml m.sig (xφ.ctx + zζ.ctx) :=
 fml.eqs (gluingEqsLHS f) (gluingEqsRHS g)

noncomputable
def xQuoEqs (f: xφ⟶ yψ) (g: zζ ⟶ yψ) : fml m.sig ((xφ.ctx + zζ.ctx) + Limits.pushout f.map g.map) :=
 fml.eqs (tm.var ∘ (x2xzw f g)) (tm.var ∘ (x2w' f g))


noncomputable
def zQuoEqs (f: xφ⟶ yψ) (g: zζ ⟶ yψ) : fml m.sig ((xφ.ctx + zζ.ctx) + Limits.pushout f.map g.map) :=
 fml.eqs (tm.var ∘ (z2xzw f g)) (tm.var ∘ (z2w' f g))


/- lemma2: the `exact` field of effectiveQuotient -/

def ReffectiveQuotient.exact
 (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
  (seq: ιs f g ∘ s = id) (l₁ l₂: Fin (xφ.ctx + zζ.ctx))
  (e: ιs f g l₁ = ιs f g l₂):  eqv (Rrel f g) l₁ l₂ :=  by
   sorry
--#check Quotient

noncomputable
def ReffectiveQuotient
  (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
  (seq: ιs f g ∘ s = id)
  : effectiveQuotient (Rrel f g) where
  carrier := Fin (Limits.pushout f.map g.map)
  quot := ιs f g
  sound := sorry
  sec := s
  sec_id := by apply (congr_fun seq)
  exact := by
   apply ReffectiveQuotient.exact
   assumption


/- lemma1: for each l: x + z, we have S ((x+z)_l, (x+z)_{s[ι1,ι2]l})  -/

def sιsSrel
 (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
 (seq: ιs  f g ∘ s = id) (l : Fin (xφ.ctx + zζ.ctx)) :
 Srel f g l (s (ιs f g l)):= sorry


abbrev φ := xφ.formula
abbrev ζ := zζ.formula
abbrev liftφ : fml m.sig (xφ.ctx + zζ.ctx) := fml.ren R.in10 φ
abbrev liftζ : fml m.sig (xφ.ctx + zζ.ctx) := fml.ren R.in01 ζ
noncomputable
abbrev quoφ: fml m.sig (Limits.pushout f.map g.map) := fml.ren (ι₁ f g) φ
noncomputable
abbrev quoζ: fml m.sig (Limits.pushout f.map g.map) := fml.ren (ι₂ f g) ζ
noncomputable
abbrev liftquoφ: fml m.sig (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := fml.ren (x2w' f g) φ
noncomputable
abbrev liftquoζ: fml m.sig (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := fml.ren (z2w' f g) ζ
noncomputable
abbrev Γ: fml m.sig (xφ.ctx + zζ.ctx) := (liftφ.conj (liftζ.conj (gluingEqs f g)))

/- lemma 3: for l : x + z, and any proof of R^* l (s[ι1,ι2]l), we have Γ ⊢ (x+z)_l = (x+z)_{s[ι1,ι2]l}-/

-- lemma eqvRxQuoEqs  (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
--  (seq: ιs  f g ∘ s = id) (l l': Fin (xφ.ctx + zζ.ctx))
--  (e: l' = (s (ιs f g l))) (r : eqv  (Rrel f g)  l l')
--  :
--  Hilbert.proof (Γ f g) (fml.eq (tm.var l) (tm.var (s (ιs f g l)))):= by
--   induction r with
--   | rfl =>
--     rw[e,← Function.comp_apply (g:= s) (f:= ιs f g),seq]
--     apply Hilbert.any_eq_intro
--     rfl
--   | sym h1 h2 =>
--     rename_i l0 l0'
--     sorry
--   | trans y _ _ _ _ => sorry
--   | base _ => sorry

-- def sιsRrel (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
--  (seq: ιs  f g ∘ s = id) (l : Fin (xφ.ctx + zζ.ctx)) :
--  Rrel f g l (s (ιs f g l)) where
--    i := sorry
--    e10 := sorry
--    e01 := sorry not true

lemma eqvRxQuoEqs  (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
 (seq: ιs  f g ∘ s = id) (l l': Fin (xφ.ctx + zζ.ctx))
 (r : eqv (Rrel f g) l l')
 :
 Hilbert.proof (Γ f g) (fml.eq (tm.var l) (tm.var l')):= by
  induction r with
  | rfl =>
    apply Hilbert.any_eq_intro
    rfl
  | sym h1 h2 =>
    rename_i l0 l0'
    sorry
  | trans y _ _ _ _ => sorry
  | base r =>
    rename_i l0 l0'
    cases' r with i e10 e01
    simp[e10,e01]
    --this is just one of the conjuncts in Γ
    sorry




/- lemma 4: Prove Γ ⊢ (⋀_{j ∈ x} x_j = w_{ι₁ j}) [w_l := (x+z)_{s l}] -/

lemma ΓsubstxQuoEqs (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
 (seq: ιs  f g ∘ s = id) (j: Fin xφ.ctx):
 Hilbert.proof (Γ f g)
  (fml.subst (substn (tm.var ∘ s))
    (fml.eq (tm.var (x2w' f g j)) (tm.var (w2w' f g (ι₁ f g j))))) := sorry


lemma xφcoveringWitness (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
 (seq: ιs  f g ∘ s = id):
 let φ := xφ.formula
 let liftφ : fml m.sig (xφ.ctx + zζ.ctx) := fml.ren R.in10 φ
 let quoφ: fml m.sig (Limits.pushout f.map g.map) := fml.ren (ι₁ f g) φ
 let liftquoφ: fml m.sig (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := fml.ren (x2w' f g) φ
 Hilbert.proof (liftφ.conj (gluingEqs f g))
 (fml.subst (substn (tm.var ∘ s)) (liftquoφ.conj (xQuoEqs f g))) := sorry



lemma coveringWitness (s:  Fin (Limits.pushout f.map g.map) ⟶ Fin (xφ.ctx + zζ.ctx))
 (seq: ιs  f g ∘ s = id):
 let φ := xφ.formula
 let ζ := zζ.formula
 let liftφ : fml m.sig (xφ.ctx + zζ.ctx) := fml.ren R.in10 φ
 let liftζ : fml m.sig (xφ.ctx + zζ.ctx) := fml.ren R.in01 ζ
 let quoφ: fml m.sig (Limits.pushout f.map g.map) := fml.ren (ι₁ f g) φ
 let quoζ: fml m.sig (Limits.pushout f.map g.map) := fml.ren (ι₂ f g) ζ
 let liftquoφ: fml m.sig (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := fml.ren (x2w' f g) φ
 let liftquoζ: fml m.sig (xφ.ctx + zζ.ctx + Limits.pushout f.map g.map) := fml.ren (z2w' f g) ζ
 Hilbert.proof (liftφ.conj (liftζ.conj (gluingEqs f g)))
 (fml.subst (substn (tm.var ∘ s)) ((liftquoφ.conj liftquoζ).conj (xQuoEqs f g))) := sorry


theorem stability {yψ xφ: fmlInCtx m} {S: Sieve yψ} (f: xφ⟶ yψ) :
 S ∈ sieves yψ → Sieve.pullback f S ∈ sieves xφ := by

 sorry


end Stability


namespace Transitivity

theorem transitivity  ⦃xφ : fmlInCtx m⦄ ⦃S : Sieve xφ⦄
(h_S:  S ∈ sieves xφ ) (R : Sieve xφ)
   (h_R: ∀ ⦃yψ : fmlInCtx m⦄ ⦃f : yψ ⟶ xφ⦄, S.arrows f → Sieve.pullback f R ∈ sieves yψ) : R ∈ sieves xφ := sorry

end Transitivity


instance SyntacticTopology [SmallUniverse.UniverseClosureProps] : GrothendieckTopology (fmlInCtx m) where
    sieves := WrigleyTopology.sieves
    top_mem' := by
      intro xφ
      exists (id_covers xφ)
      intros yψ f h
      constructor --Q: Why does it work?
    pullback_stable' := by
     apply Stability.stability
    transitive' := by
      apply Transitivity.transitivity


end WrigleyTopology
