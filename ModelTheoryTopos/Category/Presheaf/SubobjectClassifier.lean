import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Order.Hom.CompleteLattice
import ModelTheoryTopos.Misc
import ModelTheoryTopos.Category.CartesianMonoidalCategory
import ModelTheoryTopos.Category.NatIso
import ModelTheoryTopos.Category.Presheaf.Defs
import ModelTheoryTopos.Category.Presheaf.CartesianMonoidalCategory


open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace Sieve

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
variable {X Y Z : C} (f : Y ⟶ X)

@[simp]
def entails (S R : Sieve X) : Sieve X where
  arrows Y f := forall Z (h : Z ⟶ Y), S (h ≫ f) → R (h ≫ f)
  downward_closed := by
    intros Y Z f h g Z' g'
    rw [<- Category.assoc]
    exact (h _ _)

end Sieve


namespace SubobjectClassifier
  variable {C : Type} [Category C]

  @[simp]
  def prop : Psh C where
    obj X := Sieve X.unop
    map h x := x.pullback h.unop
    map_id := by
      intro
      simp only [unop_id, Sieve.pullback_id]
      rfl
    map_comp := by
      intros
      simp only [unop_comp, Sieve.pullback_comp]
      rfl

  def entail : prop (C:=C) ⊗ prop ⟶ prop where
    app X := fun p => (Sieve.entails p.1 p.2 : Sieve X.unop)
    naturality X Y f := by
      ext p
      apply Sieve.arrows_ext
      funext Z g
      ext
      constructor <;> intros h Z' g'
      · rw [<- Category.assoc]
        apply h Z' g'
      · have := h Z' g'
        rw [<-Category.assoc] at this
        exact this

  abbrev top₀ : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊤ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp only [prop, types_comp_apply, Sieve.pullback_top]

  abbrev bot₀ : 𝟙_ (Psh C) ⟶ prop where
    app X := fun _ => (⊥ : Sieve X.unop)
    naturality X Y f := by
      funext
      simp only [prop, types_comp_apply, Sieve.ext_iff, Sieve.pullback_apply]
      intros
      constructor <;> exact False.elim

  def conj : prop (C:=C) ⊗ prop  ⟶ prop where
    app X := fun p => (p.1 ⊓ p.2: Sieve X.unop)

  def disj : prop (C:=C) ⊗ prop ⟶ prop where
    app X := fun p => (p.1 ⊔ p.2 : Sieve X.unop)

  def eq {A : Psh C} : A ⊗ A ⟶ prop where
    app X := fun as =>
      {
        arrows :=  fun Y f => A.map f.op as.1 = A.map f.op as.2
        downward_closed := by
          intros _ _ _ eq _
          simp only [Opposite.op_unop, op_comp, FunctorToTypes.map_comp_apply, eq]
      }
    naturality X Y f := by
      funext as
      simp only [prop, Opposite.op_unop, types_comp_apply, Sieve.ext_iff, Sieve.pullback_apply,
        op_comp, Quiver.Hom.op_unop, FunctorToTypes.map_comp_apply]
      intros Z g
      constructor <;> exact id


  theorem eq_app {A : Psh C} (c:Cᵒᵖ ) (a: (A ⊗ A).obj c) (c': C) (f:c'⟶ c.unop):
   (SubobjectClassifier.eq.app c a).arrows f ↔ A.map f.op a.1 = A.map f.op a.2 := by
    rfl

  -- p^* : (B ⟶ prop) -> (A ⟶ prop)
  abbrev precomp {A B : Psh C} (p : A ⟶ B) (ψ : B ⟶ prop) : A ⟶ prop := p ≫ ψ

  def existQ {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) : B ⟶ prop where
    app X := fun b =>
      {
        arrows := fun Y f => exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y)
        downward_closed := by
          intro Y Z f ⟨a, ⟨eq, h⟩⟩ g
          let a' := A.map g.op a
          exists a'
          constructor
          · calc p.app (Opposite.op Z) a' = (A.map g.op ≫ p.app _) a := rfl
            _ = (p.app _ ≫ B.map g.op) a := by rw [p.naturality g.op]
            _ = B.map (g ≫ f).op b := by simp only [types_comp_apply, eq, Opposite.op_unop,
              op_comp, FunctorToTypes.map_comp_apply]
          · have eq : φ.app _ a' = prop.map g.op (φ.app _ a) := by
              calc φ.app _ a' = (A.map g.op ≫ φ.app _) a := rfl
              _ = (φ.app _ ≫ prop.map g.op) a := by rw [φ.naturality g.op]
              _ = prop.map g.op (φ.app _ a) := rfl
            simp only [prop, eq, Quiver.Hom.unop_op, Sieve.pullback_apply, Category.id_comp]
            have := (φ.app _ a).downward_closed h g
            simp only [prop, Category.comp_id] at this
            exact this
      }


  theorem existQ_app_arrows {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) (X: Cᵒᵖ) (b: B.obj X) (Y: C) (f: Y ⟶ Opposite.unop X):
    ((existQ p φ).app X b).arrows  f = exists a, p.app (Opposite.op Y) a = B.map f.op b ∧ (φ.app _ a).arrows (𝟙 Y) := rfl


  noncomputable
  def existπ {A B : Psh C} (φ : A ⊗ B ⟶ prop) : B ⟶ prop := existQ (snd A B) φ

  abbrev sSup₀ {X : Psh C} (P : Set (X ⟶ prop)) : X ⟶ prop where
    app Γ x := (⨆ p ∈ P, p.app Γ x : Sieve Γ.unop)
      -- let P' : Set (Sieve Γ.unop) := { (p.app Γ x : Sieve Γ.unop) | (p : X ⟶ prop) (_h : P p) }
      -- (SupSet.sSup P' : Sieve Γ.unop)
    naturality := by
      intros Γ Δ g
      funext x
      rw [Sieve.ext_iff]
      intros Ξ f ; constructor <;> simp [iSup]
      · intros p hp hf
        exists p ; constructor ; assumption
        rw [<-types_comp_apply (X.map g) (p.app Δ), p.naturality g] at hf
        simp only [types_comp_apply, Sieve.pullback_apply] at hf
        exact hf
      · intros p hp hf
        exists p ; constructor ; assumption
        rw [<-types_comp_apply (X.map g) (p.app Δ), p.naturality g]
        simp only [types_comp_apply, Sieve.pullback_apply]
        exact hf

  abbrev sInf₀ {X : Psh C} (P : Set (X ⟶ prop)) : X ⟶ prop where
    app Γ x :=
      let P' : Set (Sieve Γ.unop) := { (p.app Γ x : Sieve Γ.unop) | (p : X ⟶ prop) (_h : P p) }
      (InfSet.sInf P' : Sieve Γ.unop)
    naturality := by
      intros Γ Δ g
      funext x
      rw [Sieve.ext_iff]
      intros Ξ f ; constructor
      · simp only [prop, exists_prop, types_comp_apply, Sieve.sInf_apply, Set.mem_setOf_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Sieve.pullback_apply] ; intros hf p hp
        have := hf p hp
        rw [<-types_comp_apply (X.map g) (p.app Δ), p.naturality g] at this
        simp only [types_comp_apply, Sieve.pullback_apply] at this
        exact this
      · simp only [prop, exists_prop, types_comp_apply, Sieve.pullback_apply, Sieve.sInf_apply,
        Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] ; intros hf p hp
        rw [<-types_comp_apply (X.map g) (p.app Δ), p.naturality g]
        simp only [types_comp_apply, Sieve.pullback_apply]
        exact hf _ hp

  section

  variable {X : Psh C}

  instance: LE (X ⟶ prop) where
    le f g := forall Γ (x : X.obj Γ),
      let lhs : Sieve Γ.unop := f.app Γ x
      lhs ≤ (g.app Γ x : Sieve Γ.unop)

  instance: Top (X ⟶ prop) where
    top := toUnit _ ≫ top₀

  instance: Bot (X ⟶ prop) where
    bot := toUnit _ ≫ bot₀

  instance: PartialOrder (X ⟶ prop) where
    le_refl := by intros f Γ x ; apply le_refl
    le_trans := by
      intros f g h fg gh Γ x ;
     -- exact le_trans (gh _ _) (fg _ _)
      eapply le_trans
      · exact fg _ _
      · exact gh _ _
    le_antisymm := by
      intros f g fg gf ; ext Γ x ; simp only [prop] ; apply le_antisymm <;> simp_all [LE.le, prop]

  instance: SemilatticeSup (X ⟶ prop) where
    sup φ ψ := lift φ ψ ≫ disj
    le_sup_left := by simp [LE.le]; intros ; simp [disj] ; left; assumption
    le_sup_right := by simp [LE.le]; intros ; simp [disj] ; right; assumption
    sup_le := by
      intros _ _ _ h1 h2 c x
      simp only [prop, disj, FunctorToTypes.comp, lift_app_pt, sup_le_iff,
        h1 c x, h2 c x, and_self]

  -- set_option trace.profiler true in
  noncomputable
  instance: SemilatticeInf (X ⟶ prop) where
    inf φ ψ := lift φ ψ ≫ conj
    inf_le_left := by simp only [prop, LE.le, lift, conj, Functor.Monoidal.tensorObj_obj,
      FunctorToTypes.comp, Sieve.inter_apply, and_imp] ; intros ; assumption
    inf_le_right := by simp [LE.le, conj]
    le_inf := by
      intros _ _ _ h1 h2 c x
      simp[conj, h1 c x, h2 c x]

  instance: SupSet (X ⟶ prop) where
    sSup := sSup₀ -- Not sure whether this is good practice to have a name in the middle

  instance: InfSet (X ⟶ prop) where
    sInf := sInf₀

  instance: CompleteSemilatticeSup (X ⟶ prop) where
    le_sSup := by
      intros s a h
      simp only[sSup]
      intros c x
      apply le_biSup (α:=Sieve c.unop) (fun p => p.app c x) h
    sSup_le := by
      intros s a h
      simp only[sSup]
      intros c x
      simp [iSup_le_iff]
      intros i hi
      apply (h i hi c x)

  instance: CompleteSemilatticeInf (X ⟶ prop) where
    le_sInf := by
      intros s a h
      simp only[sInf]
      intros c x
      apply @le_sInf (Sieve (c.unop)) _ _ (a.app c x)
      simp; intros ; apply h ; assumption
    sInf_le := by
      intros s a h
      intros c x
      apply @sInf_le (Sieve (c.unop)) _ _ (a.app c x)
      simp
      exists a

    -- set_option trace.profiler true in
    noncomputable
    instance complete_lattice_to_prop {X : Psh C} : CompleteLattice (X ⟶ prop) where
      le_top := by simp only [prop, LE.le, Top.top, FunctorToTypes.comp]; intros; constructor
      bot_le := by simp only [prop, LE.le, Bot.bot, FunctorToTypes.comp]; rintro x c xc c' f ⟨⟩
  end


  --sup φ ψ := ChosenFiniteProducts.lift φ ψ ≫ disj
  theorem psh_top {X: Psh C} :  ⊤ = toUnit X ≫ top₀ := rfl

  theorem top_app {X : Psh C} (c: Cᵒᵖ) (x: X.obj c) (c' : C) (f : c' ⟶ c.unop)
    : ((⊤ : X ⟶ prop).app c x).arrows f := by
    simp only [Top.top, FunctorToTypes.comp, top₀]; constructor



  theorem psh_bot {X: Psh C} :  ⊥ = toUnit X ≫ bot₀  := rfl

  theorem psh_sup {X: Psh C} (φ ψ: X ⟶ SubobjectClassifier.prop) : φ ⊔ ψ = lift φ ψ ≫ SubobjectClassifier.disj := rfl

  theorem psh_sup_arrows {X: Psh C} (φ ψ: X ⟶ SubobjectClassifier.prop) (c: Cᵒᵖ) (x: X.obj c):
   ((φ ⊔ ψ).app c x) = ((lift φ ψ ≫ SubobjectClassifier.disj).app c x):= rfl

  --theorem disj_lift
  theorem psh_sup_arrows' {X: Psh C} (φ ψ: X ⟶ SubobjectClassifier.prop) (c: Cᵒᵖ) (x: X.obj c):
    let s1 : Sieve c.unop := φ.app c x
    let s2 : Sieve c.unop := ψ.app c x
    ((φ ⊔ ψ).app c x) = s1 ⊔ s2 := rfl

  theorem psh_inf {X: Psh C} (φ ψ: X ⟶ SubobjectClassifier.prop) : φ ⊓ ψ = lift φ ψ ≫ SubobjectClassifier.conj := rfl

  theorem psh_inf_arrows' {X: Psh C} (φ ψ: X ⟶ SubobjectClassifier.prop) (c: Cᵒᵖ) (x: X.obj c):
    let s1 : Sieve c.unop := φ.app c x
    let s2 : Sieve c.unop := ψ.app c x
    ((φ ⊓ ψ).app c x) = s1 ⊓ s2 := rfl

  theorem psh_sSup_arrows {X : Psh C} (s : Set (X ⟶ prop)) (c : Cᵒᵖ) (x : X.obj c) :
    (sSup s).app c x = (⨆ φ ∈ s, φ.app c x : Sieve c.unop) := rfl

  theorem psh_iSup_arrows {X : Psh C} (φ : I → (X ⟶ prop)) (c : Cᵒᵖ) (x : X.obj c) :
    (⨆ i, φ i).app c x = (⨆ i, (φ i).app c x : Sieve c.unop) := by
    calc
      (⨆ i, φ i).app c x = (sSup (Set.range φ)).app c x := by simp [iSup]
      _ = (⨆ ψ ∈ (Set.range φ), ψ.app c x : Sieve c.unop) := by simp [psh_sSup_arrows _ c x]
      _ = (⨆ i, (φ i).app c x : Sieve c.unop) := by rw [iSup_range (α:=Sieve c.unop) (g:=fun ψ => ψ.app c x) (f:=φ)]


  theorem to_prop_top {X: Psh C} (f: X⟶ SubobjectClassifier.prop): f = ⊤ ↔
   ∀(c: Cᵒᵖ ) (x: X.obj c), f.app c x = (⊤ : Sieve c.unop) := by
     simp only[psh_top]
     constructor
     · intro h
       simp[h]
     · intro h
       ext c x
       simp[h, Top.top]


  theorem Sieve_eq {c: C} (s1 s2: Sieve c): s1 = s2 ↔ s1.arrows = s2.arrows := by
    constructor
    · intros a ; simp[a]
    · intros a; ext ; simp[a]

  theorem Sieve_eq' {c: C} (s1 s2: Sieve c): s1 = s2 ↔
  ∀(c': C) (f:c'⟶ c), s1.arrows f = s2.arrows f := by
    simp[Sieve_eq]
    constructor
    · intros a ; simp[a]
    · intros a; funext; simp[a]

  theorem lift_eq_eq {X A : Psh C} (t1 t2:X ⟶ A) (c: Cᵒᵖ) (x: X.obj c):
    (lift t1 t2 ≫ eq).app c x = (⊤ : Sieve c.unop) ↔ t1.app c x= t2.app c x := by
     simp[Sieve_eq',eq_app]
     constructor
     · intro h ; let h1:= h c.unop (𝟙 c.unop);simp at h1; assumption
     · intro h ; simp[h]


  theorem Psh_hom_eq {X Y: Psh C} (f g: X⟶ Y) : f = g ↔
   ∀(c: Cᵒᵖ )(x: X.obj c), f.app c x = g.app c x := by
    constructor
    · intro h; simp[h]
    · intro h; ext c x; simp[h]


  theorem lift_eq_eq' {X A : Psh C} (t1 t2:X ⟶ A):
    (lift t1 t2 ≫ eq) = ⊤ ↔ t1 = t2:= by
     simp only[to_prop_top]
     simp only[Psh_hom_eq]
     simp only[lift_eq_eq]

  theorem sieve_distr {c: C} (s1 s2 s3: Sieve c) : s1 ⊓ (s2 ⊔ s3) = (s1 ⊓ s2) ⊔ (s1 ⊓ s3) := by
   apply le_antisymm
   · intros c' f
     simp
     intros h1 h2
     cases h2
     · left; constructor; assumption ; assumption
     · right; constructor; assumption ; assumption
   intros c' f
   simp
   rintro (⟨_,_⟩ | ⟨_, _⟩)
   · constructor ; assumption ; left ; assumption
   · constructor; assumption; right; assumption


  theorem psh_distr {X: Psh C} (a b c: X ⟶ SubobjectClassifier.prop) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
   ext c0 x
   simp only[psh_inf_arrows',psh_sup_arrows',sieve_distr]

  theorem sieve_inf_sSup_distr (X : C) :
    ∀ (a : Sieve X) (s : I → Sieve X), a ⊓ (⨆ i, s i) ≤ ⨆ i, a ⊓ s i := by
    intros a b X' f
    simp [iSup]

  -- theorem sieve_inf_sSup_distr (X : C) :
  --   ∀ (a : Sieve X) (s : Set (Sieve X)), a ⊓ SupSet.sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
  --   intros a b X' f
  --   simp
  --   intros ha c hcb hc
  --   simp [iSup]
  --   exists c, (a ⊓ c)

  theorem psh_inf_sSup_distr {X : Psh C} (a : X ⟶ prop) (b : I → (X ⟶ prop)) :
    a ⊓ (⨆ i, b i) ≤ ⨆ i, a ⊓ b i := by
    intros c x
    simp [psh_inf_arrows' a, psh_iSup_arrows _ c x, sieve_inf_sSup_distr]

  theorem complete_lattice_to_prop_top (X:Psh C) : (@SubobjectClassifier.complete_lattice_to_prop C _ X).top =
    toUnit _ ≫ top₀ := rfl

  theorem complete_lattice_to_prop_inf (X:Psh C) (φ ψ: X ⟶ prop): (@SubobjectClassifier.complete_lattice_to_prop C _ X).inf φ ψ  =
    lift φ ψ ≫ conj := rfl

  theorem complete_lattice_to_prop_sup (X:Psh C) (φ ψ: X ⟶ prop): (@SubobjectClassifier.complete_lattice_to_prop C _ X).sup φ ψ  =
    lift φ ψ ≫ disj := rfl

  theorem to_prop_naturality {X: Psh C}(φ :X ⟶ prop) (c: Cᵒᵖ) (x: X.obj c) {c': C} (f: c' ⟶ c.unop):
   φ.app (Opposite.op c') (X.map (Opposite.op f) x) =
   CategoryTheory.Sieve.pullback f (φ.app c x) := by
   have := φ.naturality (Opposite.op f)
   have l : φ.app (Opposite.op c') (X.map (Opposite.op f) x) =
           (X.map (Opposite.op f) ≫ φ.app (Opposite.op c')) x := by
    simp
   have r : Sieve.pullback f (φ.app c x) =
            (φ.app c ≫ prop.map (Opposite.op f)) x := by
    simp
   simp only[l,r]
   simp only[this]


  theorem Sieve_le_alt1 {X: Psh C}(f g:X ⟶ prop)
   (h:∀ (c: Cᵒᵖ) (x: X.obj c),
    let s1 : Sieve c.unop := (f.app c x)
    let s2 : Sieve c.unop := (g.app c x)
    s1 = ⊤ → s2 = ⊤): f ≤ g:= by
    intros cop x lhs c' f1 asm
    simp[lhs] at asm
    have a : CategoryTheory.Sieve.pullback f1 lhs = ⊤ := by
     simp[← CategoryTheory.Sieve.id_mem_iff_eq_top]
     simp[lhs]
     assumption
    let sf : Sieve c':= f.app (Opposite.op c') (X.map (Opposite.op f1) x)
    have a': sf = ⊤ := by
     simp[sf]
     have : CategoryTheory.Sieve.pullback f1 (f.app cop x) = ⊤ := by
      simp[← CategoryTheory.Sieve.id_mem_iff_eq_top]
      assumption
     simp[← to_prop_naturality] at this
     assumption
    let sg : Sieve c':= g.app (Opposite.op c') (X.map (Opposite.op f1) x)
    have a'': sg = ⊤ := by
     apply h
     simp[sf] at a'
     assumption
    simp[sg] at a''
    have a''': CategoryTheory.Sieve.pullback f1 (g.app cop x) = ⊤ := by
     simp[← to_prop_naturality] --prove the next step as simpler form
     assumption
    ---simp only[@to_prop_naturality _ _ _ f1] at a'' why???
    simp[← CategoryTheory.Sieve.id_mem_iff_eq_top] at a'''
    assumption

  theorem Sieve_le_alt2 {X: Psh C}(f g:X ⟶ prop) (h: f ≤ g):
   (∀ (c: Cᵒᵖ) (x: X.obj c),
    let s1 : Sieve c.unop := (f.app c x)
    let s2 : Sieve c.unop := (g.app c x)
    s1 = ⊤ → s2 = ⊤):= by
   simp [← CategoryTheory.Sieve.id_mem_iff_eq_top]
   intros
   apply h
   assumption

  theorem Sieve_le_alt {X: Psh C}(f g:X ⟶ prop):  f ≤ g ↔ ∀ (c: Cᵒᵖ) (x: X.obj c),
    let s1 : Sieve c.unop := (f.app c x)
    let s2 : Sieve c.unop := (g.app c x)
    s1 = ⊤ → s2 = ⊤ := by
    constructor
    · apply Sieve_le_alt2
    · apply Sieve_le_alt1

  abbrev le_to_prop_id {X: Psh C}(f g:X ⟶ prop) :=
    ∀ (c: Cᵒᵖ) (x: X.obj c), (f.app c x).arrows (𝟙 c.unop) → (g.app c x).arrows (𝟙 c.unop)

  theorem le_to_prop_le_to_prop_id {X: Psh C}(f g:X ⟶ prop) :
    f ≤ g ↔ le_to_prop_id f g := by
    simp [le_to_prop_id, CategoryTheory.Sieve.id_mem_iff_eq_top]
    apply Sieve_le_alt


  def existQ_precomp_adj {A B : Psh C} (p : A ⟶ B) :
    GaloisConnection (existQ p) (precomp p) := by
    simp only[GaloisConnection, le_to_prop_le_to_prop_id]
    intros φ ψ
    constructor
    · intros l _ x _
      apply l
      exists x
      simp
      assumption
    · rintro l _ _ ⟨ _, ⟨h1, _⟩⟩
      simp at h1
      subst h1
      apply l
      assumption


  def mate {B B' A A' : Psh C} (g : A ⟶ B) (g' : A' ⟶ B') (m : A' ⟶ A) (k : B' ⟶ B)
    (h : m ≫ g = g' ≫ k) (φ : B' ⟶ prop) : existQ m (precomp g' φ) ≤ precomp g (existQ k φ) := by
    calc existQ m (precomp g' φ) ≤  existQ m (precomp g' (precomp k (existQ k φ))) := by
          apply GaloisConnection.monotone_l (existQ_precomp_adj _)
          apply GaloisConnection.monotone_u (existQ_precomp_adj _)
          apply GaloisConnection.le_u_l (existQ_precomp_adj _)
      _ ≤ existQ m (precomp (g' ≫ k) (existQ k φ)) := by
        apply le_refl
      _ ≤ existQ m (precomp (m ≫ g) (existQ k φ)) := by
        rw [h]
      _ ≤ existQ m (precomp m (precomp g (existQ k φ))) := by
        apply le_refl
      _ ≤ precomp g (existQ k φ) := by
        apply GaloisConnection.l_u_le (existQ_precomp_adj _)

  theorem le_precomp {X Y : Psh C} (φ : Y ⟶ X) (f g : X ⟶ prop) :
    f ≤ g -> φ ≫ f ≤ φ ≫ g := by
    intros fg Γ x
    apply fg

  theorem le_iso {X Y : Psh C} (φ : X ≅ Y) (f g : X ⟶ prop) :
    f ≤ g -> φ.inv ≫ f ≤ φ.inv ≫ g := by
    apply le_precomp

  theorem iso_hom_precomp_monotone {X Y : Psh C} (φ : X ≅ Y) : Monotone (precomp φ.hom) := by
    apply le_precomp

  theorem iso_inv_precomp_monotone {X Y : Psh C} (φ : X ≅ Y) : Monotone (precomp φ.inv) := by
    apply le_iso

  open OrderIso in
  def precomp_order_iso {X Y : Psh C} (φ : X ≅ Y) : (Y ⟶ prop) ≃o (X ⟶ prop) :=
    let f : (X ⟶ prop) →o (Y ⟶ prop) := ⟨precomp φ.inv, iso_inv_precomp_monotone φ⟩
    let g : (Y ⟶ prop) →o (X ⟶ prop) := ⟨precomp φ.hom, iso_hom_precomp_monotone φ⟩
    OrderIso.ofHomInv g f (by ext ; simp [f, g]) (by ext ; simp [f, g])

  theorem precomp_order_iso_app {X Y : Psh C} (φ : X ≅ Y) (f : Y ⟶ prop):
    (precomp_order_iso φ) f = φ.hom ≫ f := by rfl

  theorem precomp_order_iso_toFun {X Y : Psh C} (φ : X ≅ Y) (f : Y ⟶ prop):
    (precomp_order_iso φ).toFun f = φ.hom ≫ f := by rfl

  theorem precomp_order_iso_invFun {X Y : Psh C} (φ : X ≅ Y) (f : X ⟶ prop):
    (precomp_order_iso φ).invFun f = φ.inv ≫ f := by rfl

  def Sieve.ext' (c : Cᵒᵖ) {R S : Sieve c.unop} (h : ∀ ⦃c'⦄ (f : c ⟶ c'), R f.unop ↔ S f.unop) : R = S := by
    apply Sieve.ext
    intros Y f
    apply h ⟨f⟩

  /- another simple instance of Beck-Chevalley done by hand
    (applied to the pullback-square corresponding to the cospan θ : B' -> B <- A : p) -/
  theorem precomp_existQ_iso {A B B' : Psh C} (p : A ⟶ B) (θ : B' ≅ B) (φ : A ⟶ prop) :
    θ.hom ≫ existQ p φ = existQ (p ≫ θ.inv) φ := by
    ext c b'
    apply Sieve.ext' ; intros Y f
    simp [existQ]
    have := congrFun (θ.hom.naturality f) b'
    simp only [types_comp_apply] at this
    rw [<-this]
    constructor
    · rintro ⟨a, ⟨eq,_⟩⟩
      exists a
      constructor
      · rw [eq, <-Iso.app_hom, <-Iso.app_inv]
        simp?
      · assumption
    · rintro ⟨a, ⟨eq,_⟩⟩
      exists a
      constructor
      · rw [<-eq, <-Iso.app_hom, <-Iso.app_inv]
        simp?
      · assumption

  theorem existQ_iso {A A' B : Psh C} (p : A' ⟶ B) (θ : A' ≅ A) (φ : A ⟶ prop) :
    existQ (θ.inv ≫ p) φ = existQ p (θ.hom ≫ φ) := by
    ext c b
    apply Sieve.ext' ; intros Y f
    simp [existQ]
    constructor
    · rintro ⟨a, ⟨eq,_⟩⟩
      exists (θ.inv.app Y a)
      constructor; assumption
      simp? ; assumption
    · rintro ⟨a, ⟨eq,_⟩⟩
      exists (θ.hom.app Y a)
      constructor; simp? ; assumption
      assumption


  theorem precomp_existsπ_iso {A B B' : Psh C} (θ : B' ≅ B) (φ : A ⊗ B ⟶ prop) :
    θ.hom ≫ existπ φ = existπ (A ◁ θ.hom ≫ φ) := by
    rw [existπ, precomp_existQ_iso]
    have : snd A B ≫ θ.inv = A ◁ θ.inv ≫ snd A B' :=  by simp
    let θ' : A ⊗ B' ≅ A ⊗ B := ⟨A ◁ θ.hom, A ◁ θ.inv, by simp , by simp⟩
    simp only [existπ, this]
    rw [existQ_iso _ θ']

  def forallQ {A B : Psh C} (p : A ⟶ B) (φ : A ⟶ prop) : B ⟶ prop where
    app c b := {
      arrows Y f := forall (Z : C) (g : Z ⟶ Y) (a : A.obj (Opposite.op Z)),
        p.app _ a = B.map (f.op ≫ g.op) b -> (φ.app _ a).arrows (𝟙 _)
      downward_closed := by
        intros Y' Y f h fY Z g a eq
        apply h Z (g ≫ fY) a
        simp [eq]
    }

  def precomp_forallQ_adj {A B : Psh C} (p : A ⟶ B) :
    GaloisConnection (precomp p) (forallQ p) := by
    simp only[GaloisConnection, le_to_prop_le_to_prop_id]
    intros φ ψ
    constructor
    · intros l _ x h Z g a eq
      apply l
      simp [precomp, eq]
      have := congrFun (φ.naturality g.op) x
      simp at this
      simp [this]
      have := (φ.app _ x).downward_closed h g
      simp at this
      assumption
    · intros l _ x h
      apply l _ (p.app _ x) h _ (𝟙 _)
      simp

noncomputable
  local instance precomp_sSupHom {A B : Psh C} (p : A ⟶ B) : sSupHom (B ⟶ prop) (A ⟶ prop) :=
    GaloisConnection.sSupHomLeft (precomp_forallQ_adj p)

  def precomp_iSup {A B : Psh C} (p : A ⟶ B) {I} (f : I -> (B ⟶ prop)) :
    p ≫ (⨆ i, f i) = ⨆ i, p ≫ (f i) := by
    calc p ≫ ⨆ i, f i = (precomp_sSupHom p) (⨆ i, f i) := by rfl
                    _ = ⨆ i, (precomp_sSupHom p) (f i) := by
                          apply map_iSup (precomp_sSupHom p) f
                    _  = ⨆ i, p ≫ f i  := by rfl

  theorem lift_same_eq (X Y: Psh C) (f: X ⟶ Y): lift f f ≫ eq = ⊤ := by
    rw [lift_eq_eq']


end SubobjectClassifier


namespace SubobjectClassifier.BaseChange
  variable {C D : Type} [Category C] [Category D] (F : Functor C D)
  open Functor


    def pb_prop : F.op ⋙ SubobjectClassifier.prop (C:=D) ⟶ SubobjectClassifier.prop where
      app := fun c x =>
        let x'' : Sieve (F.obj c.unop) := x
        (Sieve.functorPullback F x'' : Sieve _)

    theorem pb_prop_le {X : Psh D} (φ ψ : X ⟶ SubobjectClassifier.prop) :
      φ ≤ ψ → (whiskerLeft F.op φ ≫ pb_prop F) ≤ (whiskerLeft F.op ψ ≫ pb_prop F) := by
      intros h Ξ x lhs Δ f
      apply h _ x (F.map f)

    @[simp]
    def map_pred {X : Psh D} (φ : X ⟶ SubobjectClassifier.prop) :
      (F.op ⋙ X) ⟶ SubobjectClassifier.prop :=
        whiskerLeft F.op φ ≫ pb_prop F

    theorem map_pred_comp {X Y: Psh D} (f : X ⟶ Y) (φ : Y ⟶ SubobjectClassifier.prop) :
      map_pred F (f ≫ φ) = whiskerLeft F.op f ≫ map_pred F φ := by
      simp only [map_pred, Functor.whiskerLeft_comp]
      rfl

    def map_pred_mon {X : Psh D} : (X ⟶ SubobjectClassifier.prop) →o ((F.op ⋙ X) ⟶ SubobjectClassifier.prop) where
      toFun φ := map_pred F φ
      monotone' x y := by apply pb_prop_le

    def pb_prop_top {X : Psh D} : map_pred (X:=X) F ⊤ = ⊤ := by
      ext x
      rfl

    def pb_prop_bot {X : Psh D} : map_pred (X:=X) F ⊥ = ⊥ := by
      ext x
      rfl

    def pb_prop_conj : map_pred F (φ ⊓ ψ) = map_pred F φ ⊓ map_pred F ψ := by
      ext x
      rfl

    def pb_prop_disj : map_pred F (φ ⊔ ψ) = map_pred F φ ⊔ map_pred F ψ := by
      ext x
      rfl

    def pb_prop_eq (X : Psh D) :
      map_pred F (SubobjectClassifier.eq (A:=X)) = (SubobjectClassifier.eq (A:=F.op ⋙ X)) := by
        ext x ⟨a1 , a2⟩
        apply CategoryTheory.Sieve.arrows_ext
        simp [pb_prop, SubobjectClassifier.eq]
        funext c0 f
        simp[Presieve.functorPullback]

    theorem pb_prop_existQ {A B : Psh D} (p: A⟶ B) (φ: A ⟶ SubobjectClassifier.prop):
      map_pred F (SubobjectClassifier.existQ p φ) =
      SubobjectClassifier.existQ (whiskerLeft F.op p) (map_pred F φ) := by
        ext c a
        simp
        ext Y f
        simp[SubobjectClassifier.existQ_app_arrows]
        simp[pb_prop]
        simp[SubobjectClassifier.existQ_app_arrows]

    theorem pb_prop_existπ {A B : Psh D} (φ: A ⊗ B ⟶ SubobjectClassifier.prop):
      map_pred F (SubobjectClassifier.existπ φ) =
      SubobjectClassifier.existπ ((BaseChange.pb_prod_pair_iso F A B).inv ≫ map_pred F φ) := by
        rw [SubobjectClassifier.existπ, pb_prop_existQ]
        rfl

    open SubobjectClassifier in
    theorem pb_prop_iSup {X : Psh D} {I} (f : I -> (X ⟶ SubobjectClassifier.prop)) :
      map_pred F (⨆ i : I, f i) = ⨆ i : I, (map_pred F (f i)) := by
      ext c x
      set d := Opposite.op (F.obj c.unop)
      simp [SubobjectClassifier.psh_iSup_arrows _ _ x]
      rw [SubobjectClassifier.psh_iSup_arrows f d x]
      simp [pb_prop]
      apply Sieve.ext ; intros c' g ; simp; constructor
      · rintro ⟨i, ⟨⟨i0, hi⟩, hg⟩⟩
        exists (Sieve.functorPullback F i) ; simp ; constructor <;> try assumption
        exists i0 ; simp at hi ; rw [<-hi]
      · rintro ⟨i, ⟨⟨i0, hi⟩, hg⟩⟩
        simp [iSup]
        simp at hi ; rw [<-hi] at hg
        exists i0

end SubobjectClassifier.BaseChange
