
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

namespace Joshua
  variable [SmallUniverse]

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
  def pb_over (xφ yψ : fmlInCtx m) (f : xφ ⟶ yψ) (σ : Over yψ) : Over xφ :=
    let zξ := σ.left
    let φ' := xφ.formula.ren R.in10
    let ξ' := zξ.formula.ren R.in01
    -- let r : Fin yψ.ctx → Fin zξ.ctx := σ.hom.map
    -- let var_eqs := fml.eqs (k:=yψ.ctx) (fun i => .var (R.in10 (f.map i))) (fun i => .var (R.in01 (r i)))
    let xzφξ : fmlInCtx m := {
        ctx := xφ.ctx + zξ.ctx
        formula := (φ'.conj ξ') --.conj var_eqs
      }
    let f : xzφξ ⟶ xφ := {
      map := R.in10
      preserves_formula := by
        simp [xzφξ]
        apply Hilbert.proof.conj_elim_l
    }
    Over.mk f

  open SmallUniverse

  structure CoveringFamily (xφ : fmlInCtx m) where
    index : U
    maps : El index -> Over xφ
    covering : xφ.formula ⊢ fml.infdisj index (fun i => cover_from_over xφ (maps i))

  def covering_family_to_presieve {xφ : fmlInCtx m} (σs : CoveringFamily xφ)
    : Presieve xφ :=
    fun _yψ f => ∃ (i : El σs.index), σs.maps i = Over.mk f




  variable [UniverseClosureProps]
  open UniverseClosureProps

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


  instance : GrothendieckTopology (fmlInCtx m) where
    sieves xφ S := ∃ σ : CoveringFamily xφ, covering_family_to_presieve σ ≤ S
    top_mem' := by
      intro xφ
      exists (id_covers xφ)
      intros yψ f h
      constructor
    pullback_stable' := sorry
    transitive' := sorry

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