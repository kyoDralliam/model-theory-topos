
import ModelTheoryTopos.Syntax.GeometricLogic.Defs
import ModelTheoryTopos.Syntax.GeometricLogic.Hilbert
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.Grothendieck

open CategoryTheory

-- TODO : move to the appropriate place once fully finished
class SmallUniverse.UniverseClosureProps [SmallUniverse] where
  uUnit : U
  utt : El uUnit

namespace R
abbrev in10 (i : Fin n) : Fin (n + k) := i.addNat k
abbrev in01 (i : Fin n) : Fin (k + n) := i.castAdd' k
abbrev in101 : Fin (n + k) -> Fin (n + k + k) :=
  Fin.casesAdd (in10 ∘ in10) in01
abbrev in110 : Fin (n + k) -> Fin (n + k + k) := in10
abbrev in001 : Fin k -> Fin (n + k + k) := in01
abbrev in010 : Fin k -> Fin (n + k + k) := in10 ∘ in01
abbrev in100 : Fin n -> Fin (n + k + k) := in10 ∘ in10
end R



lemma lift₁_zero {n n' : RenCtx} (f : n ⟶ n'):
 lift₁ f 0 = 0 := by
  simp[lift₁]

lemma lift₁_succ {n n' : RenCtx} (f : n ⟶ n') (i: Fin n):
 lift₁ f (Fin.succ i) = Fin.succ (f i) := by
  simp[lift₁]



def liftn {n1 n2 n : RenCtx} (f : n1 ⟶ n2) : (n1+n) ⟶ (n2+n) :=
  Fin.casesAdd (R.in10 ∘ f) R.in01


lemma liftn_left {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n1):
 liftn (n:=n) f (@R.in10 n1 n i) = @R.in10 n2 n (f i) := by
  simp[liftn]

lemma liftn_right {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n) :
 liftn (n:=n) f (@R.in01 n n1 i) = @R.in01 n n2 i := by
  simp[liftn]

theorem liftn_zero {n1 n2 : RenCtx} (f : n1 ⟶ n2) : liftn (n :=0) f = f := by
  have p : ∀ x, liftn (n :=0) f x = f x := by
    fapply Fin.casesAdd
    · intro i
      apply liftn_left
    intro i; exact Fin.elim0 i
  funext
  apply p



lemma addNat_succ :
  (@R.in10 n1 (n2 + 1) i) =  Fin.succ (@R.in10 n1 n2 i) := by
  simp[Fin.addNat]
  rfl

#check Fin.succ
lemma castAdd'_succ {n m} (i: Fin m):
 Fin.castAdd' n i.succ = (Fin.castAdd' n i).succ := by
 simp[Fin.castAdd']


lemma lift₁_liftn {n n' : RenCtx} (f : n ⟶ n') :
  lift₁ f = @liftn n n' 1 f := by
  have p: ∀ i : Fin (n+1), lift₁ f i = @liftn _ _ 1 f i := by
   apply @Fin.casesAdd
   · intro i
     have e: (i.addNat 1) = @R.in10 n 1 i := rfl
     simp only[e,liftn_left]
     simp[addNat_succ,lift₁]
   · intro i
     simp[liftn_right,lift₁]
     have e: i = 0 := by
      ext : 1
      simp_all only [Fin.val_eq_zero, Fin.isValue]
     have e' : (Fin.castAdd' n 0) = (0: Fin (n + 1)) := rfl
     simp[e,e']
     rfl
  funext i
  apply p

lemma liftn_add {n1 n2 m1 m2 : RenCtx} (f : n1 ⟶ n2) (i: Fin n1):
 liftn (liftn f (n:=m1)) (n:=m2) (R.in10 (R.in10 i))=
 Fin.cast ((Nat.add_assoc n2 m1 m2).symm)
  (liftn f (n:= m1 + m2) (R.in10 i)):= by
  simp[liftn_left]
  simp[Fin.cast]
  ext
  simp[Fin.addNat]
  simp[Nat.add_assoc]

lemma lift1_liftn_left {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n1) :
  lift₁ (liftn f) (R.in10 (R.in10 i)) = @liftn _ _ (n+ 1) f (R.in10 i) := by
  simp only[lift₁_liftn,liftn_add,Fin.cast,liftn_left]
  simp[Fin.addNat,Nat.add_assoc]

  --(n2 + n) + 1
lemma liftn_liftn_right {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin n) :
  lift₁ (liftn f) (R.in10 (R.in01 i)) = @liftn _ _ (n+ 1) f (R.in01 (R.in10 i)) := by
  simp only[lift₁_liftn,liftn_add,Fin.cast,liftn_left,liftn_right]
  simp[Fin.addNat,Fin.castAdd']
  simp[castAdd'_succ]

lemma liftn_liftn_zero {n1 n2 n : RenCtx} (f : n1 ⟶ n2) (i: Fin 1) :
  lift₁ (liftn f) (R.in01 (R.in01 i)) = @liftn _ _ (n+ 1) f (R.in01 (R.in01 i)) := by
  simp only[lift₁_liftn,liftn_add,Fin.cast,liftn_left,liftn_right]
  rfl




lemma liftn_alt0 {n1 n2 n : RenCtx} (f : n1 ⟶ n2) :
  ∀ x, lift₁ (liftn f) x = @liftn _ _ (n+ 1) f x:= by
  apply @Fin.casesAdd n1 (n+ 1)
  · intro i
    apply lift1_liftn_left
  · apply Fin.casesAdd
    · apply liftn_liftn_right
    · apply liftn_liftn_zero

lemma liftn_alt {n1 n2 n : RenCtx} (f : n1 ⟶ n2) :
   lift₁ (liftn f) = @liftn _ _ (n+ 1) f :=
   by
   funext x
   apply liftn_alt0





namespace Joshua
  variable [SmallUniverse]

/-
theorem R.in01_natAdd : R.in01 i = Fin.natAdd m i := by
  simp[Fin.natAdd]

  sorry
  -/



theorem ren_existsn {n1 n2 n m} (f: n1 ⟶ n2) (φ : fml m (n1 + n)):
 fml.ren f (fml.existsn φ) = fml.existsn (fml.ren (liftn f) φ) := by
 induction n with
 | zero =>
   simp[fml.existsn,liftn]
   congr
 | succ n ih =>
   simp[fml.existsn,liftn,fml.ren,ih,liftn_alt]



  /-the category of formulas of context consists of:
    obj: a context, i.e. a natural number, and a formula in this context

    map: a map from xφ to yψ is a map σ from y to x, such that φ ⊢ ψ[σ y_i/y_i]
    e.g. φ1 ∧ φ2 ⊢ φ1, the inclusion from variables in φ1 into the one in φ1 and φ2 gives a map φ1 ∧ φ2 to φ1

  -/

  structure fmlInCtx (m : theory) where
    ctx : RenCtx
    formula : fml m.sig ctx

  structure fmlMap (xφ yψ : fmlInCtx m) where
    map : yψ.ctx ⟶ xφ.ctx
    preserves_formula : xφ.formula ⊢ yψ.formula.ren map

  def idMap (xφ : fmlInCtx m) : fmlMap xφ xφ where
    map := 𝟙 xφ.ctx
    preserves_formula := by
      simp [fml.ren_id]
      apply Hilbert.proof.var

  def compMap {xφ yψ zξ : fmlInCtx m}  (g : fmlMap xφ yψ) (f : fmlMap yψ zξ)
    : fmlMap xφ zξ where
    map := f.map ≫ g.map
    preserves_formula := by
      simp [fml.ren_comp]
      apply Hilbert.proof.cut g.preserves_formula f.preserves_formula.ren

  instance : Category (fmlInCtx m) where
    Hom := fmlMap
    id := idMap
    comp := compMap


  /-Given a theory m, formula-in-context xφ and a map σ over xφ,
    turn it into a formula
    in the signature of m, under the context of x.
    if the map is yψ ---σ---> xφ
    it contains the information how to map {y | ψ} to {x | φ}, this is a map of finite sets
    regard ψ as a formula in the context x,y
    with x mapped to the first half, captured by R10, and y mapped to the second half

    construct a list of k equations, using the constructor eqs, rather than constructing a conjunction of equations
    here k is the number of items in x, because we want to specify which item in the domain
    does x_i correspond to.

    formula is effectively ∃y. ψ ∧ x_i = σ (x_i)
    saying each of such tuple x has some tuple y satisfying property ψ that is mapped to it.
  -/
  def cover_from_over (xφ : fmlInCtx m) (σ : Over xφ) : fml m.sig xφ.ctx :=
    let yψ := σ.left
    let r : Fin xφ.ctx → Fin yψ.ctx := σ.hom.map
    let yψr : fml m.sig (xφ.ctx + yψ.ctx) := yψ.formula.ren R.in01
    let represent_renaming : fml m.sig (xφ.ctx + yψ.ctx) :=
      .eqs (k:=xφ.ctx)
        (fun i => .var (R.in10 i)) -- x_i
        (fun i => .var (R.in01 (r i))) -- σ(x_i)
    .existsn (n':=yψ.ctx) (.conj yψr represent_renaming)

  -- given a map f : {x | φ} → {y | ψ}, "pulls back" a map over {y | ψ} to a map over {x | φ}
  -- Beware, it does not correspond to the pullback in the underlying category fmlInCtx; need to uncomment the var_eqs to get the pullback

  /- Given a map zξ ---σ---> yφ, so have ξ ⊢ φ[σ y_i/y_i]
           a map xφ ---ρ---> yψ so have φ ⊢ ψ[ρ y_i/y_i]
    want a map to xφ
     {x,z | φ ∧ ξ}---p2--->{z | ξ}
       |                      |
       p1                     σ
       |                      |
       v                      v
      {x | φ} -----ρ-----> {y | ψ}
  -/
  def pb_over (xφ yψ : fmlInCtx m) (f : xφ ⟶ yψ) (σ : Over yψ) : Over xφ :=
    let zξ := σ.left
    let φ' := xφ.formula.ren R.in10
    let ξ' := zξ.formula.ren R.in01
    let r : Fin yψ.ctx → Fin zξ.ctx := σ.hom.map
    let var_eqs : fml m.sig (xφ.ctx + zξ.ctx) :=
      fml.eqs (k:=yψ.ctx) (fun i => .var (R.in10 (f.map i))) (fun i => .var (R.in01 (r i)))
    let xzφξ : fmlInCtx m := {
        ctx := xφ.ctx + zξ.ctx
        formula := .conj (φ'.conj ξ') var_eqs
      }
    let f : xzφξ ⟶ xφ := {
      map := R.in10
      preserves_formula := by
        simp [xzφξ]
        apply Hilbert.proof.cut
        apply Hilbert.proof.conj_elim_l
        apply Hilbert.proof.conj_elim_l
    }
    Over.mk f

  open SmallUniverse

  /-A covering family on a formula-in-context xφ consists of
    -Something in a small universe that indexing the family, acting the role of the indexing set
    -for each element i of the "indexing set", a map to xφ
     i.e. a bunch of maps y_i's ψ_i ---σ_i---> xφ
    -A geometric proof that φ ⊢ ∨ ∃ y_i's. ψ_i ∧ σ_i (x_j) = x_j
    -/
  structure CoveringFamily (xφ : fmlInCtx m) where
    index : U
    maps : El index -> Over xφ
    covering : xφ.formula ⊢ fml.infdisj index (fun i => cover_from_over xφ (maps i))


  /-
  def presieve_to_covering_family  {xφ : fmlInCtx m} (S : Presieve xφ) : CoveringFamily xφ where
    index := sorry
    maps := sorry
    covering := sorry
    not eligible because of size
  -/

  /-pullback of a covering family is a covering family
   given a covering family cf over yφ,
   i.e. a indexing set in the smallUniverse U, called I := cf.index
   a family of maps indexing by I

   The family over xφ is indexed also by I
   i ↦ x,z_i. φ ∧ ξ_i
   Recall
     {x,z_i | φ ∧ ξ_i}---p2--->{z_i | ξ_i}
       |                            |
       p1                           σ
       |                            |
       v                            v
      {x | φ} --------f--------> {y | ψ}

      want xφ ⊢ ∨ i, ∃ x, z_i. φ ∧ ξ_i
      (here the z_i is a tuple! NOT a single var name)
      have xφ ⊢ yψ[f y_j/y_j]
      yψ ⊢ ∨ i. ∃z_i. ξ_i ∧ y_j = σ y_j
      by conjI and trans
  -/

 theorem Hilbert.conj_copy [SmallUniverse] {T: theory} (φ ψ : fml T.sig n) :
 Hilbert.proof φ ψ → Hilbert.proof φ (fml.conj φ ψ) := by
   sorry

  def pb_ConveringFamily  {xφ yψ : fmlInCtx m}  (f: xφ ⟶ yψ) (cf: CoveringFamily yψ):
   CoveringFamily xφ where
     index := cf.index
     maps i := pb_over xφ yψ f (cf.maps i)
     covering := by
     -- xφ ⊢ ∨ i. ∃ x, z_i. (φ ∧ ξ_i) ∧ x_i = p1 (x_i)  under xφ.ctx
     -- xφ ⊢ yψ[f y_j/y_j]
     -- yψ[f y_j/y_j] ⊢ (∨ i . ∃ z_i. ξ_i ∧ y_j = σ y_j)[f y_j/y_j]
     -- (∨ i . ∃ z_i. ξ_i ∧ y_j = σ y_j)[f y_j/y_j]
     -- ? ⊢ ?
     --  ∨ i. ∃ x, z_i. (φ ∧ ξ_i) ∧ x_i = p1 (x_i)

      simp[cover_from_over]
      have p:= Hilbert.proof.ren (ρ :=f.map) cf.covering
      have xφyψ := f.preserves_formula
      have xφ_to_ren := Hilbert.proof.cut xφyψ p
      simp[fml.ren] at xφ_to_ren p
      have xφ_to_xφ_ren := Hilbert.conj_copy _ _ xφ_to_ren
      apply Hilbert.proof.cut xφ_to_xφ_ren





      have fp:= f.preserves_formula
      --let p' := Hilbert.proof.infdisj_elim p
      --apply (Hilbert.proof.cut fp)

      --apply Hilbert.proof.conj_intro
      sorry


  /-The information contained in a CoveringFamily structure on xφ
    is a family of maps to xφ, such that xφ is covered by this family.
    This information can turned into a presieve, containing precisely arrows of this
    family. i.e. forget the information that there is a proof from xφ to some of the family.-/

  def covering_family_to_presieve {xφ : fmlInCtx m} (σs : CoveringFamily xφ)
    : Presieve xφ :=
    fun _yψ f => ∃ (i : El σs.index), σs.maps i = Over.mk f

  lemma covering_family_to_presieve_eval
  {xφ : fmlInCtx m} (σs : CoveringFamily xφ) {yψ : fmlInCtx m} (f: yψ ⟶ xφ)
    : covering_family_to_presieve σs f = ∃ (i : El σs.index), σs.maps i = Over.mk f :=rfl


  -- lemma in_covering_family_to_presieve
  -- {xφ : fmlInCtx m} (σs : CoveringFamily xφ) {yψ : fmlInCtx m} (f: yψ ⟶ xφ)
  --   : f ∈ covering_family_to_presieve σs yψ ↔ sorry := sorry

  /- why cannot I write membership f ∈ covering_family_to_presieve σs? -/
  lemma presieve_of_pb_ConveringFamily
  {xφ yψ : fmlInCtx m}  (f: xφ ⟶ yψ) (cf: CoveringFamily yψ)
  {zξ: fmlInCtx m} (g: zξ ⟶ xφ):
  covering_family_to_presieve (pb_ConveringFamily f cf) g = sorry := sorry

  --∃ (i : El cf.index), g = (pb_over _ _ f sorry).hom := sorry


  variable [UniverseClosureProps]
  open UniverseClosureProps

  /-UniverseClosureProps is a small universe that contains a nonempty set uUnit,
    the term utt witnesses nonemptiness of uUnit. -/

  def id_covers (xφ : fmlInCtx m) : CoveringFamily xφ where
    index := uUnit
    maps := fun _ => Over.mk (𝟙 xφ)
    covering := by
      apply Hilbert.proof.cut (τ:=cover_from_over xφ (Over.mk (𝟙 xφ)))
      · simp [cover_from_over, fml.ren]
        apply Hilbert.proof.existn_intro (𝟙 _)
        apply Hilbert.proof.conj_intro
        · sorry
        · simp [fml.subst_eqs, tm.subst]
          apply Hilbert.proof.eqs
          intro i
          apply Hilbert.any_eq_intro
          sorry
      · apply Hilbert.proof.infdisj_intro (φ:=fun _ => _) utt


  class SmallUniverse.UniverseClosureProps [SmallUniverse] where
  uUnit : U
  utt : El uUnit
  uSigma (a : U) (b : El a -> U) : U
  elSigma  : El (uSigma a b) ≅ Σ (x : El a), El (b x)

  class SmallUniverse.UniverseClosureProps' [SmallUniverse] where
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

  def isCov {xφ : fmlInCtx m} (S: Sieve xφ ) :=
     ∃ σ : CoveringFamily xφ, covering_family_to_presieve σ ≤ S

  lemma pullback_isCov {xφ yψ: fmlInCtx m} (f:yψ ⟶  xφ ) (S: Sieve xφ )
   (h: isCov S) : isCov (Sieve.pullback f S) := by
    simp[isCov]
    sorry

  open Joshua.SmallUniverse.UniverseClosureProps' in
  def CoveringFamily_Union [SmallUniverse.UniverseClosureProps']
   {xφ: fmlInCtx m} (C: CoveringFamily xφ)
   (Cs: Π i: El C.index, CoveringFamily (C.maps i).left) :
   CoveringFamily xφ where
     index :=
      let sel := fun i => (Cs i).index
      uSigma C.index sel
     maps i:=
      let i1 := elSigmaPi1 i
      let i2 := elSigmaPi2 i
      let Onxφ := C.maps i1
      let Γc := Onxφ.left
      let onΓc := (Cs i1).maps i2
      (Over.map Onxφ.hom).obj onΓc

    --  CategoryTheory.Over.map
    --           (C.maps (SmallUniverse.UniverseClosureProps'.elSigmaPi1 i )).hom
    --           sorry
     covering := by
      simp
      have h := C.covering
      apply Hilbert.proof.cut h
      --have h' :=

      sorry

  --lemma transitive_isCov

  --#check Nonempty
  instance [SmallUniverse.UniverseClosureProps'] : GrothendieckTopology (fmlInCtx m) where
    sieves xφ  :=   {S : Sieve xφ |∃ σ : CoveringFamily xφ, covering_family_to_presieve σ ≤ S}
    --A sieve S on xφ is a covering sieve ↔
    --exists a covering family of xφ such that the presieve generated by the covering family is contained in S
      --pass through the construction of presieves so we can write the order ≤
    top_mem' := by
      intro xφ
      exists (id_covers xφ)
      intros yψ f h
      constructor --Q: Why does it work?
    pullback_stable' := by
      intro xφ yψ S_xφ f h
      cases' h with cf h
      exists (pb_ConveringFamily f cf)
      intros zξ g h
      simp[Sieve.pullback]
      convert_to S_xφ.arrows (g ≫ f)

      --simp [covering_family_to_presieve_eval] at h
      sorry
    /- if S is a covering sieve on xφ, i.e. contains a covering family
       to xφ. and R is a sieve on xφ such that for any yψ ---f---> xφ in S,
       we have the pullback of R along f, i.e. a sieve on yψ, contains a
       covering family on yψ.
       Want that R contains a covering family on xφ
    -/
    transitive' := by
     intro xφ S h1 R h2
     cases' h1 with cf hle
     let A:= cf.index
     have p0: Inhabited (Π a: El A, (CoveringFamily (cf.maps a).left)) := by
      apply Joshua.SmallUniverse.UniverseClosureProps'.uchoice
      intro a
      constructor
      let ca := (cf.maps a).hom
      simp at ca
      have sa := @h2 _ ((cf.maps a).hom) --ca
       (by apply hle
           simp[covering_family_to_presieve]
           exists a
           ) --Q: refinement! Why is ca not working! and should be a lemma
      let S1 := (Sieve.pullback (cf.maps a).hom R)
      --how to extract the information that S1 contains a covering family, as in sa?
      rw[Set.mem_setOf_eq] at sa
      --rw[Set.mem_setOf_eq] at h2
      --simp at sa
      exact {
        index := by

         sorry
        maps := sorry
        covering := sorry
      }
     have p0: Π a: El A, CoveringFamily (cf.maps a).left := p0.default
     have c: El A → U := fun a => (p0 a).index
     exists {
       index := Joshua.SmallUniverse.UniverseClosureProps'.uSigma A c
       maps := sorry
       covering := sorry
     }
     sorry

end Joshua

namespace SyntacticSite

#check substn


--theorem in10_substn (φ: fml m k): fml.ren (@R.in01 n k) φ  =  fml.subst (substn (@R.in01 n k)) φ := sorry

--theorem in10_substn_in01 (φ: fml m k): fml.ren (@R.in01 n k) φ =
structure functional [SmallUniverse] {T: theory} {n1 n2 : RenCtx} (φ: fml T.sig n1) (ψ : fml T.sig n2) (θ  : fml T.sig (n1 + n2)) where
 total : Hilbert.proof φ θ.existsn
 range: Hilbert.proof θ ((φ.ren R.in10).conj (ψ.ren R.in01))
 unique : Hilbert.proof ((θ.ren R.in101).conj (θ.ren R.in110)) (fml.eqs (tm.var ∘ R.in010) (tm.var ∘ R.in001))


/-namespace Example

  def phi : fml S 1 := fml.existsQ (.eq (.var 0) (.var 1))

  def psi : (Fml S).obj 2 := .eq (.var (0 : Fin 2)) (.var (1 : Fin 2))

  def proof_phi : Hilbert.proof (T:=T) .true phi := by
    simp only [phi]
    apply Hilbert.proof.cut (τ:=psi[(.var 0)..])
    · apply Hilbert.proof.eq_intro
    · apply Hilbert.proof.existsQ_intro

end Example


-/



def id_rep [SmallUniverse] {T: theory} {n : RenCtx} (φ: fml T.sig n) : fml T.sig (n+n) :=
 (φ.ren R.in10).conj
 (fml.eqs (tm.var ∘ R.in10) (tm.var ∘ R.in01))


theorem Hilbert.eqs_elim [SmallUniverse] {T: theory} {n' n : Subst T.sig}  (δ : fml T.sig n')  (φ γ: fml T.sig (n'+n)) (ts1 ts2:  n ⟶  n'):
 Hilbert.proof δ (.eqs ts1 ts2) →
 Hilbert.proof (δ.conj (.subst (substn ts1) γ)) (.subst (substn ts1) φ) →
 Hilbert.proof (δ.conj (.subst (substn ts2) γ)) (.subst (substn ts2) φ) := by
     induction n  with
     | zero =>
       simp only[substn0, fml.subst_id]
       intros h1 h2
       assumption
     | succ n1 ih =>
       intros h1 h2
       simp only [Nat.succ_eq_add_one, substnsucc'] at *
       simp only [fml.subst_comp] at *
       apply ih _ _ (ts1 ∘ Fin.succ) (ts2 ∘ Fin.succ)
       · simp only [Hilbert.proof.eqs_iff, Nat.succ_eq_add_one, Function.comp_apply] at *
         intro i
         apply h1
       · simp only [← fml.subst_comp,
         Nat.succ_eq_add_one] at *
           --have := @substnsucc'
         --have := @substnsucc'
         simp only[← substnsucc'] at *
         simp only[← substnsucc'']
         simp only[substnsucc] at *
         simp only [fml.subst_comp] at *
         set γ' := (fml.subst (lift_subst (substn (ts1 ∘ Fin.succ))) γ)
         set φ' := (fml.subst (lift_subst (substn (ts1 ∘ Fin.succ))) φ)
         have h10 : Hilbert.proof δ (fml.eq (ts1 (0:Fin n1.succ)) ( ts2 (0:Fin n1.succ))) := by
           simp only [Hilbert.proof.eqs_iff] at h1
           exact h1 0
         have := Hilbert.eq_elim_subst0 h10 h2
         set si := (scons (ts2 (0:Fin n1.succ)) (ts1 ∘ Fin.succ))
         have t20 : si (0:Fin n1.succ) = ts2 (0:Fin n1.succ) := by
           simp only [Nat.succ_eq_add_one, Fin.cases_zero, si]
         simp only [t20, si]
         have geq: γ' = (fml.subst (lift_subst (substn (si ∘ Fin.succ))) γ) := by
          simp only [Nat.succ_eq_add_one, γ', si]
          congr --????? how?????
         have peq: φ' = (fml.subst (lift_subst (substn (si ∘ Fin.succ))) φ) := by
          simp only [Nat.succ_eq_add_one, φ', γ', si]
          congr
         simp only [← geq, ← peq, γ', φ', si]
         assumption


namespace S
  def in10 {n k : Subst S} : n  ⟶ n + k := tm.var ∘ R.in10
  def in01 {n k : Subst S} : k  ⟶ n + k := tm.var ∘ R.in01

  -- #check fun S (n k : Subst S) => @in10 S n k ++ @in10 S n k ++ @in01 S n k
end S

theorem substn_section [SmallUniverse] {T: theory} {k n : Subst T.sig} (φ : fml T.sig k) (σ :  k ⟶ n) :
  (φ.ren R.in01).subst (substn σ) = φ.subst σ := by
  simp [fml.ren_to_subst, <-fml.subst_comp, R.in01]
  congr
  funext i
  simp [tm.subst_comp_app, tm.subst, substn]

theorem Hilbert.eqs_elim' [SmallUniverse] {T: theory} {k n : Subst T.sig} (δ : fml T.sig n)  (φ ψ: fml T.sig k) (σ τ:  k ⟶ n)
  (h : Hilbert.proof δ (.eqs σ τ)):
  Hilbert.proof (δ.conj (ψ.subst σ)) (φ.subst σ) →
  Hilbert.proof (δ.conj (ψ.subst τ)) (φ.subst τ) := by
  rw [<-substn_section ψ σ, <-substn_section φ σ,
    <-substn_section ψ τ, <-substn_section φ τ]
  apply Hilbert.eqs_elim δ _ _ σ τ h

theorem Hilbert_eqs_intro [SmallUniverse] {T: theory} {n k: RenCtx} (φ: fml T.sig n) (σ: Fin k → tm T.sig n):
 φ ⊢ fml.eqs σ σ := sorry

theorem Hilbert_eq_symm [SmallUniverse] {T: theory} {n k: RenCtx} (t1 t2:  tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → φ ⊢ fml.eq t2 t1 :=

   sorry

theorem Hilbert_eqs_symm [SmallUniverse] {T: theory} {n k: RenCtx} (σ1 σ2: Fin k → tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eqs σ1 σ2 → φ ⊢ fml.eqs σ2 σ1 :=
  sorry

theorem Hilbert.conj_add_true [SmallUniverse] {T: theory} (φ ψ : fml T.sig n) :
 Hilbert.proof φ ψ ↔ Hilbert.proof (φ.conj .true) ψ := by
  constructor
  · intro h
    apply Hilbert.proof.cut _ h
    exact Hilbert.proof.conj_elim_l
  · intro h
    apply Hilbert.proof.cut _ h
    apply Hilbert.proof.conj_intro
    · exact Hilbert.proof.var
    · exact Hilbert.proof.true_intro




-- namespace Example

--   def phi : fml S 1 := fml.existsQ (.eq (.var 0) (.var 1))

--   def psi : (Fml S).obj 2 := .eq (.var (0 : Fin 2)) (.var (1 : Fin 2))

--   def proof_phi : Hilbert.proof (T:=T) .true phi := by
--     simp only [phi]
--     apply Hilbert.proof.cut (τ:=psi[(.var 0)..])
--     · apply Hilbert.proof.eq_intro
--     · apply Hilbert.proof.existsQ_intro

-- end Example
-- theorem substn_left {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n'):
--   substn σ (Fin.addNat a n) = .var a := by
--    simp only [substn, Fin.casesAdd_left]
--    rfl

-- theorem substn_right {m} {n n' : Subst m} (σ : n ⟶ n') (a: Fin n):
--   substn σ (Fin.castAdd' n' a ) = σ a := by
--    simp only [substn, Fin.casesAdd_right]

-- TODO: this should us fml.subst_id, fml.ren_to_subst and fml.subst_comp
theorem tm.subst_ren_id [SmallUniverse] {T: theory} {n: RenCtx} (t: tm T.sig n):
 (.subst (substn fun i ↦ tm.var i) (tm.ren R.in10 t)) = t := by
   induction t with
   | var a => simp only [tm.ren, R.in10, tm.subst, substn_left]
   | op o σ ih =>
    simp only [tm.ren, tm.subst, tm.op.injEq, heq_eq_eq, true_and]
    ext
    simp only [ih]

-- theorem tm.subst_ren_id' {T: theory} {n k: RenCtx} (t: tm T.sig n):
--  (.subst (substn fun i ↦ foo i) (tm.ren (@R.in10 n k) t)) = t := sorry

theorem Subst_comp_o {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  ( tm.var ∘ f) ≫ g = g ∘ f := rfl

theorem Subst_comp_o' {S: monosig} {n m k: Subst S}  (f : Fin n -> Fin k) (g : k ⟶ m) :
  (fun i => tm.var (f i)) ≫ g = g ∘ f := rfl


-- TODO: this should be a straightforward application of fml.ren_id and fml.ren_comp
theorem fml.subst_ren_id [SmallUniverse] {T: theory} {n: Subst T.sig} (φ: fml T.sig n):
 (fml.subst (substn fun i ↦ tm.var i) (fml.ren R.in10 φ)) = φ := by
      simp[fml.ren_to_subst,<-fml.subst_comp]
      have := @SyntacticSite.Subst_comp_o' T.sig _ _ _ (@R.in10 n n) (substn tm.var)
      let v : emb.obj n → tm T.sig n:= @tm.var T.sig n
      have h0: (fun i ↦ tm.var i) = @tm.var T.sig n:= rfl
      simp [emb]
      simp only[h0]
      simp[this]
      have := @fml.subst_id _ T.sig n
      let ff : n ⟶ n := ((@substn T.sig n n tm.var) ∘  (@R.in10 n n) )
      have h : ff = 𝟙 n := by
       funext
       simp[ff,substn_left,R.in10]
       rfl
      simp[ff] at h
      simp[h]
      apply this




theorem fun_map_comp : (fun i ↦ g (f i)) = fun i => (g ∘ f) i := rfl
theorem fun_map_comp' : (fun i ↦ g (f i)) =(g ∘ f) := rfl



theorem subst_comp_var: (tm.subst σ) ∘ .var = σ := rfl

theorem in110_01_010 : (@R.in110 n k) ∘ R.in01 = R.in010 := rfl
theorem in110_10_100 : (@R.in110 n k) ∘ R.in10 = R.in100 := rfl
theorem in101_10_100 : (@R.in101 n k) ∘ R.in10 = R.in100 := by
  ext i
  simp only [Function.comp_apply, Fin.casesAdd_left, Fin.coe_addNat]
theorem in101_10_010 : (@R.in101 n k) ∘ R.in01 = R.in001 := by
  ext i
  simp only [Function.comp_apply, Fin.casesAdd_right, Fin.coe_castAdd']

theorem Hilbert_eq_trans [SmallUniverse] {T: theory} {n : RenCtx} (t1 t2 t3: tm T.sig n) (φ ψ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → ψ ⊢ fml.eq t2 t3 → φ.conj ψ ⊢ fml.eq t1 t3 := sorry

theorem Hilbert_eq_trans' [SmallUniverse] {T: theory} {n : RenCtx} (t1 t2 t3: tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eq t1 t2 → φ ⊢ fml.eq t2 t3 → φ ⊢ fml.eq t1 t3 := sorry

theorem Hilbert_eqs_trans' [SmallUniverse] {T: theory} {n k: RenCtx} (σ1 σ2 σ3: Fin k →  tm T.sig n) (φ: fml T.sig n):
  φ ⊢ fml.eqs σ1 σ2 → φ ⊢ fml.eqs σ2 σ3→ φ ⊢ fml.eqs σ1 σ3 := sorry



theorem Hilbert_conj_1 [SmallUniverse] {T: theory} {n: RenCtx} (δ φ ψ: fml T.sig n):
 δ ⊢ φ.conj ψ → δ ⊢ φ := by
   intro h
   have := @Hilbert.proof.cut _ T n δ (φ.conj ψ)
   apply this h
   exact Hilbert.proof.conj_elim_l

theorem Hilbert_conj_2 [SmallUniverse] {T: theory} {n: RenCtx} (δ φ ψ: fml T.sig n):
 δ ⊢ φ.conj ψ → δ ⊢ ψ := by
   intro h
   have := @Hilbert.proof.cut _ T n δ (φ.conj ψ)
   apply this h
   exact Hilbert.proof.conj_elim_r



theorem id_rep_functional [SmallUniverse] {T: theory} {n : RenCtx} (φ: fml T.sig n) :
  functional φ φ (id_rep φ) where
    total := by
      apply Hilbert.proof.existn_intro (fun i => tm.var i)
      rw[id_rep,fml.subst,fml.subst_eqs]
      apply Hilbert.proof.conj_intro
      · simp only [fml.subst_ren_id]; apply Hilbert.proof.var
      · apply Hilbert.proof.eqs
        intro i
        simp [R.in10,R.in01,tm.subst,substn_left,substn_right]--some simp lemmas maybe
        apply Hilbert.any_eq_intro
        rfl
    range := by
      simp[id_rep]
      apply Hilbert.proof.conj_intro
      · apply Hilbert.proof.conj_elim_l
      ·  simp only[fml.ren_to_subst]
         simp only[fun_map_comp']
         set σ  :=  (tm.var ∘ R.in10)
         set τ := (tm.var ∘ R.in01)
         set δ := (fml.subst σ φ).conj (fml.eqs σ τ)
         have h1 : δ ⊢ fml.eqs σ τ := by
           simp only[δ]
           exact Hilbert.proof.conj_elim_r
         have := @Hilbert.eqs_elim' _ T n (n+n) δ φ .true σ τ h1
         simp[fml.subst,← Hilbert.conj_add_true] at this
         apply this
         simp only[δ]
         exact Hilbert.proof.conj_elim_l
    unique := by
     simp only [fml.ren_to_subst, fun_map_comp']
     simp only[id_rep,fml.subst] --does Lean have match abbrev which will not require copy-and-paste?
     simp only[fml.subst_eqs,fun_map_comp']
     simp[← Function.comp_assoc]
     simp[subst_comp_var]
     simp[Function.comp_assoc]
     simp[in110_10_100,in110_01_010,in101_10_100,in101_10_010]
     apply Hilbert_eqs_trans' _ (tm.var ∘ R.in100)
     · apply Hilbert_eqs_symm
       apply Hilbert_conj_2 _ (fml.subst (tm.var ∘ R.in110) (fml.ren R.in10 φ))
       apply Hilbert_conj_2 _ ((fml.subst (tm.var ∘ R.in101) (fml.ren R.in10 φ)).conj (fml.eqs (tm.var ∘ R.in100) (tm.var ∘ R.in001)))
       apply Hilbert.proof.var
     · apply Hilbert_conj_2 _ (fml.subst (tm.var ∘ R.in101) (fml.ren R.in10 φ))
       apply Hilbert_conj_1 _ _ ((fml.subst (tm.var ∘ R.in110) (fml.ren R.in10 φ)).conj (fml.eqs (tm.var ∘ R.in100) (tm.var ∘ R.in010)))
       apply Hilbert.proof.var



@[simp]
def fml_equiv [SmallUniverse] {T: theory} {n : RenCtx} (φ ψ: fml T.sig n) := Hilbert.proof φ ψ ∧ Hilbert.proof ψ φ

theorem fml_equiv_Equivalence [SmallUniverse] {T: theory} {n : RenCtx} : Equivalence (@fml_equiv _ T n) where
  refl := by
    intro φ
    simp
    apply Hilbert.proof.var
  symm := by
    intros φ ψ asm
    simp only [fml_equiv] at *
    simp only [asm, and_self]
  trans := by
    intro x y z a1 a2
    simp only [fml_equiv] at *
    constructor <;> apply Hilbert.proof.cut (τ:=y) <;> simp [a1, a2]

structure theory_fml [SmallUniverse] (T: theory) where
  ctx: RenCtx
  fml : fml T.sig n


end SyntacticSite
