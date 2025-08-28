import ModelTheoryTopos.Geometric.Syntax.Formula

open CategoryTheory Limits

inductive Foo : (n : Nat) → Type where
  | foo (x : Nat × Nat) : Foo x.fst → Foo x.snd


def test {n} (x : Foo n) : Type :=
  match n, x with
  | _, .foo x f => sorry -- x.snd is not available

namespace Signature

variable {S : Signature} [κ : SmallUniverse S] [T : S.Theory]

inductive Derivation : {xs : S.Context} → FormulaContext xs → Formula xs → Type* where
  | axiom {xs} {Γ : FormulaContext xs} {φ : S.Sequent} {σ : xs ⟶ φ.ctx}
      (φinT : φ ∈ T) (D : Derivation Γ (φ.premise.subst σ)) : Derivation Γ (φ.concl.subst σ)
  | var {xs} (Γ : S.FormulaContext xs) (i : Fin Γ.length) : Derivation Γ (Γ.nth i)
  | true_intro {xs} {Γ : FormulaContext xs} : Derivation Γ ⊤'
  | false_elim {xs} {Γ : FormulaContext xs} {φ : Formula xs} (D_false : Derivation Γ ⊥') :
      Derivation Γ φ
  | conj_intro {Γ φ ψ} (D_left : Derivation Γ φ) (D_right : Derivation Γ ψ) : Derivation Γ (φ ∧' ψ)
  | conj_elim_l {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ φ
  | conj_elim_r {Γ φ ψ} (D_conj : Derivation Γ (φ ∧' ψ)) : Derivation Γ ψ
  | disj_intro {xs Γ} {I : Set κ} (φᵢ : I → S.Formula xs) (i : I) (D : Derivation Γ (φᵢ i)) :
      Derivation Γ (⋁' φᵢ)
  | disj_elim {xs Γ ψ} {I : Set κ} {φᵢ : I → S.Formula xs} (D_disj : Derivation Γ (⋁' φᵢ))
    (Dᵢ : (i : I) → Derivation (Γ.cons (φᵢ i)) ψ) : Derivation Γ ψ
  | eq_intro {Γ t} : Derivation Γ (.eq t t)
  | eq_elim {xs A t1 t2} {Γ Γ' : S.FormulaContext xs} (φ : S.Formula (A ∶ xs))
    (D_eq : Derivation Γ (t1 =' t2)) (D : Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.cons_Id t1))) :
    Derivation (Γ' ++ Γ) (φ.subst (Context.Hom.cons_Id t2))
  | eq_proj_pair {xs n} {Aᵢ : (i : Fin n) → S} (tᵢ : (i : Fin n) → ⊢ᵗ[xs] (Aᵢ i)) {i : Fin n} {Γ} :
      Derivation Γ ((Term.pair tᵢ).proj i =' tᵢ i)
  | eq_pair_proj {xs n} {Aᵢ : Fin n → DerivedSorts S.Sorts} (t : ⊢ᵗ[xs] .prod Aᵢ) {Γ} :
      Derivation Γ (Term.pair (fun i ↦ t.proj i) =' t)
  | exists_intro {xs A} {Γ : S.FormulaContext xs} (φ : S.Formula (A ∶ xs)) (t : S.Term xs A)
      (D : Derivation Γ (φ.subst (Context.Hom.cons_Id t))) : Derivation Γ (∃' φ)
  | exists_elim {xs A} {Γ : S.FormulaContext xs} {φ : S.Formula (A ∶ xs)}
      (D_exists : Derivation Γ (∃' φ)) {ψ}
      (D : Derivation ((Γ.subst (xs.π A)).cons φ) (ψ.subst (xs.π A))) :
      Derivation Γ ψ

scoped notation:25 Γ " ⊢ᵈ[ " xs:51 " ] " φ:50  => Derivation (xs := xs) Γ φ
scoped notation:25 Γ " ⊢ᵈ " φ:50  => Derivation Γ φ

variable {xs : S.Context} {Δ Γ : FormulaContext xs} {φ : Formula xs}

variable (Δ Γ) in
def FormulaContext.Hom : Type _ :=
  (i : Fin Γ.length) → Δ ⊢ᵈ Γ.nth i

def FormulaContext.Hom.Id (Γ : FormulaContext xs) : Γ.Hom Γ := .var Γ

def FormulaContext.Hom.cons (ξ : Δ.Hom Γ) (D : Δ ⊢ᵈ φ) : Δ.Hom (Γ.cons φ) :=
  Fin.cases D ξ

variable (Δ φ) in
def FormulaContext.Hom.π : (Δ.cons φ).Hom Δ :=
  fun i ↦ .var (Δ.cons φ) i.succ

instance : Quiver (FormulaContext xs) where
  Hom := FormulaContext.Hom

/- I'm not sure why Lean is complaining -/
-- def Derivation.subst (D : Derivation Γ φ) : (Δ : FormulaContext xs) → Δ.Hom Γ → Derivation Δ φ := fun Δ ξ ↦
--   match xs, Γ, φ, D, Δ, ξ with
--   | .(xs), .(Γ), .(Formula.subst σ _), @«axiom» S κ T .(xs) .(Γ) φ σ φinT D, Δ, ξ => by
--       refine .axiom (T := T) φinT ?_
--       #check Derivation.subst D
--       -- (Derivation.subst _ _ ξ)

noncomputable def Derivation.wkTm {xs} {Γ : FormulaContext xs} {φ : Formula xs}
    (D : Γ ⊢ᵈ φ) {ys} (ρ : ys ⟶ xs) : Derivation (T := T) (Γ.subst ρ) (φ.subst ρ) :=
  sorry

noncomputable def Derivation.wkFml {xs} {Γ : FormulaContext xs} {φ : Formula xs}
    (D : Γ ⊢ᵈ φ) {Δ : FormulaContext xs} (ξ : forall ψ, ψ ∈ Γ -> ψ ∈ Δ) : Derivation (T := T) Δ φ := by
  induction D with
  | «axiom» φinT D ih => exact .axiom (T := T) φinT (ih ξ)
  | var Γ i =>
      have : Γ.nth i ∈ Γ := sorry
      -- obtain ⟨i,h⟩ := ξ _ this
      sorry
  | true_intro => exact .true_intro
  | false_elim D_false ih => exact false_elim (ih ξ)
  | conj_intro D_left D_right ih_left ih_right => exact conj_intro (ih_left ξ) (ih_right ξ)
  | conj_elim_l D_conj ih => exact conj_elim_l (ih ξ)
  | conj_elim_r D_conj ih => exact conj_elim_r (ih ξ)
  | disj_intro φᵢ i d ih => exact disj_intro φᵢ i (ih ξ)
  | disj_elim D_disj d'ᵢ ih ihᵢ => sorry
  | eq_intro => exact eq_intro
  | @eq_elim _ _ t1 t2 Γ Γ' φ D_eq d ih_eq ih => sorry
  | eq_proj_pair tᵢ => exact eq_proj_pair tᵢ
  | eq_pair_proj t => exact eq_pair_proj t
  | exists_intro φ t d ih => exact exists_intro φ t (ih ξ)
  | @exists_elim _ _ Γ φ D_exists ih =>

      sorry

-- def Derivation.subst' {xs} {Γ : FormulaContext xs} {φ : Formula xs} (D : Γ ⊢ᵈ φ) :
--     (ys : S.Context) → (σ : ys ⟶ xs) → (Δ : FormulaContext ys) → (ξ : Δ ⟶ (Γ.subst σ)) →
--     Derivation (T := T) Δ (φ.subst σ) :=
--   match D, xs, Γ, φ with
--   | @«axiom» _ _ _ .(xs) .(Γ) ψ σ φinT D, .(xs), .(Γ), .(ψ.concl.subst σ) => sorry
--   -- | .(xs), .(Γ), _, @«axiom» _ _ _ .(xs) .(Γ) φ σ φinT D => sorry
--   | .(xs), .(Γ), _, @var _ _ _ xs Γ i => sorry
--   | .(xs), .(Γ), _, @true_intro _ _ _ xs Γ => sorry
--   | .(xs), .(Γ), .(φ), @false_elim _ _ _ xs Γ φ D_false => sorry
--   | .(xs), .(Γ), _, @conj_intro _ _ _ xs Γ _ _ D_left D_right => sorry
--   | .(xs), .(Γ), _, @conj_elim_l _ _ _  xs Γ _ D_conj ih => sorry
--   | .(xs), .(Γ), _, @conj_elim_r _ _ _ xs Γ _ D_conj ih => sorry
--   | .(xs), .(Γ), _, @disj_intro _ _ _ xs Γ φᵢ i D ih => sorry
--   | .(xs), .(Γ), _, @disj_elim _ _ _ xs Γ _ D_disj Dᵢ D_disj_ih Dᵢ_ih => sorry
--   | .(xs), .(Γ), _, @eq_intro _ _ _ xs A Γ t => sorry
--   | .(xs), _, _, @eq_elim _ _ _ xs A t1 t2 Γ Γ' φ D_eq D  => sorry
--   | .(xs), .(Γ), _, @eq_proj_pair _ _ _ xs n Aᵢ tᵢ i Γ => sorry
--   | .(xs), .(Γ), _, @eq_pair_proj _ _ _ xs n Aᵢ t Γ => sorry
--   | .(xs), .(Γ), _, @exists_intro _ _ _ xs A Γ φ t _ => sorry
--   -- | _, _, _, @exists_elim => sorry
--   | _, _, _, @exists_elim _ _ _ _ _ _ _ D_exists _ D => sorry
--   -- | .(xs), .(Γ), _, @exists_elim _ _ _ .(xs) A .(Γ) _ D_exists _ D => sorry


-- (ξ i).subst' (A ∶ ys) (ys.π A) ((Δ.subst (ys.π A)).cons (Formula.subst ((Context.consFunctor A).map σ) φ))
      -- (FormulaContext.Hom.π (Δ.subst (ys.π A)) (Formula.subst ((Context.consFunctor A).map σ) φ))

def Derivation.subst' {xs} {Γ : FormulaContext xs} {φ : Formula xs} (D : Γ ⊢ᵈ φ) :
    (ys : S.Context) → (σ : ys ⟶ xs) → (Δ : FormulaContext ys) → (ξ : Δ ⟶ (Γ.subst σ)) →
    Derivation (T := T) Δ (φ.subst σ) :=
  match Γ, φ, D with
  | .(Γ), .(Formula.subst σ (Sequent.concl ψ)), @«axiom» _ _ _ .(xs) Γ ψ σ φinT D => fun ys σ' Δ ξ ↦
      (Formula.subst_comp ψ.concl σ' σ) ▸ Derivation.axiom φinT
        (Formula.subst_comp ψ.premise σ' σ ▸ Derivation.subst' D ys σ' Δ ξ)
  | .(Γ), .(Γ.nth i), @var _ _ _ .(xs) Γ i => fun ys σ Δ ξ ↦ ξ i
  | .(Γ), .(⊤'), @true_intro _ _ _ .(xs) Γ => fun ys σ Δ ξ ↦ .true_intro
  | .(Γ), .(φ), @false_elim _ _ _ .(xs) Γ φ D_false => fun ys σ Δ ξ ↦
      .false_elim (Derivation.subst' D_false _ _ _ ξ)
  | .(Γ), _, @conj_intro _ _ _ .(xs) Γ φ ψ D_left D_right => fun ys σ Δ ξ ↦
      conj_intro (Derivation.subst' D_left _ _ _ ξ) (Derivation.subst' D_right _ _ _ ξ)
  | .(Γ), _, @conj_elim_l _ _ _  .(xs) Γ φ ψ D_conj => fun ys σ Δ ξ ↦
      conj_elim_l (Derivation.subst' D_conj _ _ _ ξ)
  | .(Γ), _, @conj_elim_r _ _ _ .(xs) Γ φ ψ D_conj => fun ys σ Δ ξ ↦
      conj_elim_r (Derivation.subst' D_conj _ _ _ ξ)
  | .(Γ), _, @disj_intro _ _ _ .(xs) Γ I φᵢ i D => fun ys σ Δ ξ ↦
      disj_intro (fun i ↦ (φᵢ i).subst σ) i (Derivation.subst' D _ _ _ ξ)
  | .(Γ), .(ψ), @disj_elim _ _ _ .(xs) Γ ψ I φᵢ D_disj Dᵢ  => fun ys σ Δ ξ ↦
      by
      apply disj_elim (Derivation.subst' D_disj _ _ _ ξ) fun i ↦ ?_
      apply Derivation.subst' (Dᵢ i)
      intro j
      cases j using Fin.cases with
          | zero => exact Derivation.var _ 0
          | succ k =>

            sorry
            -- let arst := Derivation.subst' (ξ k) ys (𝟙 ys) (Δ.cons (Formula.subst σ (φᵢ i)))
            -- simp at arst
            -- let fwp := arst (FormulaContext.Hom.π Δ (Formula.subst σ (φᵢ i)))
            -- exact fwp
  | .(Γ), _, @eq_intro _ _ _ .(xs) A Γ t => fun ys σ Δ ξ ↦
      sorry
  | .(Γ' ++ Γ), _, @eq_elim _ _ _ .(xs) A t1 t2 Γ Γ' φ D_eq D  => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @eq_proj_pair _ _ _ .(xs) n Aᵢ tᵢ i Γ => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @eq_pair_proj _ _ _ .(xs) n Aᵢ t Γ => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @exists_intro _ _ _ .(xs) A Γ φ t D => fun ys σ Δ ξ ↦
      sorry
  | .(Γ), _, @exists_elim _ _ _ .(xs) A Γ φ D_exists ψ D => fun ys σ Δ ξ ↦
      by
      let foo := Derivation.subst' D_exists _ _ _ ξ
      apply exists_elim foo
      have : Formula.subst (ys.π A) (Formula.subst σ ψ) =
        Formula.subst ((Context.consFunctor A).map σ) (Formula.subst (xs.π A) ψ) := sorry
      rw [this]
      apply Derivation.subst' D
      rw [FormulaContext.subst_cons]
      apply FormulaContext.Hom.cons
      · rw [FormulaContext.subst_comp]
        have foo : ((Context.consFunctor A).map σ ≫ xs.π A) = ys.π A ≫ σ := sorry
        rw [foo]
        intro i
        have : (Γ.subst (ys.π A ≫ σ)).nth i = Formula.subst (ys.π A) ((Γ.subst σ).nth i) := sorry
        rw [this]
        exact Derivation.subst' (ξ i) (A ∶ ys) (ys.π A) _
          (FormulaContext.Hom.π (Δ.subst (ys.π A)) (Formula.subst ((Context.consFunctor A).map σ) φ))
      · exact Derivation.var _ 0
  termination_by sizeOf Γ -- Placeholder to typecheck
  decreasing_by all_goals sorry

-- noncomputable def Derivation.subst'' {xs} {Γ : FormulaContext xs} {φ : Formula xs}
--     (D : Γ ⊢ᵈ φ) : (ys : S.Context) → (σ : ys ⟶ xs) → (Δ : FormulaContext ys) → (ξ : Δ ⟶ (Γ.subst σ)) →
--     Derivation (T := T) Δ (φ.subst σ) := by
--   induction D with
--   | «axiom» φinT D ih =>
--       intro ys σ' Δ ξ
--       let foo := ih ys σ' Δ
--       sorry
--   | var Γ i => exact ξ i
--   | true_intro => exact .true_intro
--   | false_elim D_false ih => sorry --exact false_elim (ih ξ)
--   | conj_intro D_left D_right ih_left ih_right => sorry --exact conj_intro (ih_left _) (ih_right ξ)
--   | conj_elim_l D_conj ih => sorry --exact conj_elim_l (ih ξ)
--   | conj_elim_r D_conj ih => sorry --exact conj_elim_r (ih ξ)
--   | disj_intro φᵢ i d ih => sorry --exact disj_intro φᵢ i (ih ξ)
--   | disj_elim D_disj d'ᵢ ih ihᵢ => sorry
--       -- refine disj_elim (ih ξ) fun i ↦ ihᵢ i ?_
--       -- intro j
--       -- cases j using Fin.cases with
--       -- | zero => exact Derivation.var _ 0
--       -- | succ i =>
--       --     exact Derivation.wkFml (Γ := Δ) (ξ i) (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--   | eq_intro => exact eq_intro
--   | @eq_elim xs A t1 t2 Γ Γ' φ D_eq d ih_eq ih =>
--       -- let arst := eq_elim ()
--       sorry
--   | eq_proj_pair tᵢ => sorry --exact eq_proj_pair tᵢ
--   | eq_pair_proj t => sorry --exact eq_pair_proj t
--   | exists_intro φ t d ih => sorry --exact exists_intro φ t (ih ξ)
--   | @exists_elim xs A Γ φ D_exists ψ D ih_exists ih_D =>
--       apply exists_elim (ih_exists σ ξ) (ψ := ψ.subst σ)
--       have : (ψ.subst σ).subst (ys.π A) =
--         (ψ.subst (xs.π A)).subst (Context.Hom.cons (ys.π A ≫ σ) (ys.var A)) := sorry
--       rw [this]
--       let foo := ih_D
--       -- let (FormulaContext.subst (xs.π A) Γ)
--       let arst : ((FormulaContext.subst (xs.π A) Δ).cons φ) ⟶ (FormulaContext.subst (xs.π A) Γ) :=  by
--         intro i
--         apply Derivation.wkFml (Γ := FormulaContext.subst (xs.π A) Δ)
--         simp at i
--         · cases i using Fin.cases with
--           | zero => sorry
--           | succ i => sorry
--         · exact (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--       sorry

      -- apply exists_elim (ih_exists ξ)
      -- apply ih_D
      -- let arst : ((FormulaContext.subst (xs.π A) Δ).cons φ) ⟶ (FormulaContext.subst (xs.π A) Γ) :=  by
      --   intro i
      --   apply Derivation.wkFml (Γ := FormulaContext.subst (xs.π A) Δ)
      --   simp at i
      --   · cases i using Fin.cases with
      --     | zero => sorry
      --     | succ i => sorry
      --   · exact (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
      -- sorry

-- noncomputable def Derivation.subst {xs} {Γ : FormulaContext xs} {φ : Formula xs}
--     (D : Γ ⊢ᵈ φ) (ys : S.Context) (σ : ys ⟶ xs) {Δ : FormulaContext ys} (ξ : Δ.Hom (Γ.subst σ)) :
--     Derivation (T := T) Δ (φ.subst σ) := by
--   induction D with
--   | «axiom» φinT D ih => sorry --exact .axiom (T := T) φinT (ih ξ)
--   | var Γ i => exact ξ i
--   | true_intro => exact .true_intro
--   | false_elim D_false ih => sorry --exact false_elim (ih ξ)
--   | conj_intro D_left D_right ih_left ih_right => sorry --exact conj_intro (ih_left _) (ih_right ξ)
--   | conj_elim_l D_conj ih => sorry --exact conj_elim_l (ih ξ)
--   | conj_elim_r D_conj ih => sorry --exact conj_elim_r (ih ξ)
--   | disj_intro φᵢ i d ih => sorry --exact disj_intro φᵢ i (ih ξ)
--   | disj_elim D_disj d'ᵢ ih ihᵢ => sorry
--       -- refine disj_elim (ih ξ) fun i ↦ ihᵢ i ?_
--       -- intro j
--       -- cases j using Fin.cases with
--       -- | zero => exact Derivation.var _ 0
--       -- | succ i =>
--       --     exact Derivation.wkFml (Γ := Δ) (ξ i) (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--   | eq_intro => exact eq_intro
--   | @eq_elim xs A t1 t2 Γ Γ' φ D_eq d ih_eq ih =>
--       -- let arst := eq_elim ()
--       sorry
--   | eq_proj_pair tᵢ => sorry --exact eq_proj_pair tᵢ
--   | eq_pair_proj t => sorry --exact eq_pair_proj t
--   | exists_intro φ t d ih => sorry --exact exists_intro φ t (ih ξ)
--   | @exists_elim xs A Γ φ D_exists ψ D ih_exists ih_D =>
--       apply exists_elim (ih_exists σ ξ) (ψ := ψ.subst σ)
--       have : (ψ.subst σ).subst (ys.π A) =
--         (ψ.subst (xs.π A)).subst (Context.Hom.cons (ys.π A ≫ σ) (ys.var A)) := sorry
--       rw [this]
--       let foo := ih_D
--       sorry
--       -- apply exists_elim (ih_exists ξ)
--       -- apply ih_D
--       -- let arst : ((FormulaContext.subst (xs.π A) Δ).cons φ) ⟶ (FormulaContext.subst (xs.π A) Γ) :=  by
--       --   intro i
--       --   apply Derivation.wkFml (Γ := FormulaContext.subst (xs.π A) Δ)
--       --   simp at i
--       --   · cases i using Fin.cases with
--       --     | zero => sorry
--       --     | succ i => sorry
--       --   · exact (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--       -- sorry

-- noncomputable def Derivation.subst'' {xs} {Γ : FormulaContext xs} {φ : Formula xs}
--     (D : Γ ⊢ᵈ φ) {Δ : FormulaContext xs} (ξ : Δ.Hom Γ) : Derivation (T := T) Δ φ := by
--   induction D with
--   | «axiom» φinT D ih => exact .axiom (T := T) φinT (ih ξ)
--   | var Γ i => exact ξ i
--   | true_intro => exact .true_intro
--   | false_elim D_false ih => exact false_elim (ih ξ)
--   | conj_intro D_left D_right ih_left ih_right => exact conj_intro (ih_left ξ) (ih_right ξ)
--   | conj_elim_l D_conj ih => exact conj_elim_l (ih ξ)
--   | conj_elim_r D_conj ih => exact conj_elim_r (ih ξ)
--   | disj_intro φᵢ i d ih => exact disj_intro φᵢ i (ih ξ)
--   | disj_elim D_disj d'ᵢ ih ihᵢ =>
--       refine disj_elim (ih ξ) fun i ↦ ihᵢ i ?_
--       intro j
--       cases j using Fin.cases with
--       | zero => exact Derivation.var _ 0
--       | succ i =>
--           exact Derivation.wkFml (Γ := Δ) (ξ i) (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--   | eq_intro => exact eq_intro
--   | @eq_elim xs A t1 t2 Γ Γ' φ D_eq d ih_eq ih =>
--       let Δ_t1_eq_t2 :=
--         ih_eq (Δ := Δ) fun i ↦ FormulaContext.append_nth_r (κ := κ) Γ ▸ ξ ⟨Γ'.length + i, _⟩
--       let goal : FormulaContext.nil xs ++ Δ ⊢ᵈ φ.subst (Context.Hom.cons_Id t2) :=
--         eq_elim φ
--           (ih_eq (Δ := Δ) fun i ↦ FormulaContext.append_nth_r (κ := κ) Γ ▸ ξ ⟨Γ'.length + i, _⟩)
--           (FormulaContext.nil_append (κ := κ) _ ▸ ih ξ)
--       convert goal; simp
--   | eq_proj_pair tᵢ => exact eq_proj_pair tᵢ
--   | eq_pair_proj t => exact eq_pair_proj t
--   | exists_intro φ t d ih => exact exists_intro φ t (ih ξ)
--   | @exists_elim xs A Γ φ D_exists ψ D ih_exists ih_D =>
--       apply exists_elim (ih_exists ξ)
--       apply ih_D
--       let arst : ((FormulaContext.subst (xs.π A) Δ).cons φ) ⟶ (FormulaContext.subst (xs.π A) Γ) :=  by
--         intro i
--         apply Derivation.wkFml (Γ := FormulaContext.subst (xs.π A) Δ)
--         simp at i
--         · cases i using Fin.cases with
--           | zero => sorry
--           | succ i => sorry
--         · exact (fun φ ⟨i, h⟩ ↦ ⟨i.succ, h⟩)
--       sorry

instance {xs} : Category (FormulaContext (κ := κ) xs) where
  id Γ i := .var Γ i
  comp ξ ξ' i := sorry
  id_comp σ := by funext; sorry
  assoc := sorry

end Signature
