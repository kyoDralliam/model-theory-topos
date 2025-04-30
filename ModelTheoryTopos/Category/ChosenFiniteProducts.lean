import Mathlib.Data.List.GetD
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory

#search "List.replicate length."


namespace List

  abbrev In (l : List α) := Fin l.length

  abbrev In.here (a : α) l : In (a :: l) := (0 : Fin (l.length + 1))
  abbrev In.there (a : α) (h : In l) : In (a :: l) := h.succ

  def In.recOn (P : forall {l : List α}, In l → Sort u)
    (hhere : forall a l, P (In.here a l))
    (hthere : forall a l (h : In l), P h -> P (In.there a h)) :
    forall {l} (h : In l), P h := by
    intro l
    induction l
    case nil =>
      apply finZeroElim
    case cons hd tl ih =>
      apply Fin.cases
      · apply hhere
      · intro i
        apply hthere
        apply ih


  def In.recOn_here : (In.here a l).recOn P hhere hthere = hhere a l := by
    simp [recOn, here, Fin.cases_zero]

  def In.recOn_there
    : (In.there a h).recOn P hhere hthere = hthere a _ h (h.recOn P hhere hthere) := by
    simp [recOn, there, Fin.cases_succ]

  def replicate_In {a : α} (k : Fin n) : In (replicate n a) :=
    k.cast (symm (List.length_replicate (n:=n)))

  def replicate_In_zero {a : α}
    : replicate_In (n:=n+1) (a:=a) 0 = In.here a (replicate n a) := by
    simp [replicate_In]

  def replicate_In_succ {a : α} (k : Fin n)
    : replicate_In (n:=n+1) (a:=a) k.succ = In.there a (replicate_In k) := by
    simp [replicate_In]

  def get_replicate {a : α} (k : In (replicate n a)) : (replicate n a)[k] = a := by
    simp

end List

namespace CategoryTheory.ChosenFiniteProducts
  open MonoidalCategory

  section NarryProducts

  variable {D : Type u} [Category D] [ChosenFiniteProducts D]

  def finprod (l : List D) : D := l.foldr tensorObj (𝟙_ D)

  -- def nproj (l : List D) (k : Fin l.length) : (finprod l ⟶ l[k]) := sorry
  def finproj (l : List D) (k : l.In) : (finprod l ⟶ l[k]) :=
    k.recOn (fun {l} k => finprod l ⟶ l[k])
      (fun a l => fst a (finprod l))
      (fun a l h ih => snd a (finprod l) ≫ ih)

  theorem finproj_here (a : D) (l : List D) :
    finproj (a :: l) (List.In.here a l) = fst _ _ := by
    simp only [finproj, List.In.recOn_here, finprod]

  theorem finproj_there (a : D) (l : List D) (k : l.In) :
    finproj (a :: l) (k.there a) = snd _ _ ≫ (finproj l k) := by
    simp only [finproj, List.In.recOn_there]

  def finpair (x : D) : forall (l : List D) (_cone : forall (k : l.In), x ⟶ l[k]), x ⟶ finprod l
    | [] => fun _ => toUnit x
    | a :: l => fun cone =>
      lift (cone (List.In.here a l))
        (finpair x l (fun k => cone (k.there a)))

  theorem finpair_nil (x : D) {cone : forall k : [].In, x ⟶ [][k]}:
    finpair x [] cone = toUnit x := by
    simp only [finpair]

  theorem finpair_cons (x : D) {a : D} {l : List D} {cone : forall k : (a :: l).In, x ⟶ (a :: l)[k]}:
    finpair x (a :: l) cone = lift (cone (List.In.here a l)) (finpair x l (fun k => cone (k.there a))) := by
    simp only [finpair]

  theorem finpair_finproj {x : D} {l : List D} (k : l.In) : forall (cone : forall (k : l.In), x ⟶ l[k]),
    finpair x l cone ≫ finproj l k = cone k := by
    apply k.recOn fun {l} k => forall cone, finpair x l cone ≫ finproj l k = cone k
    · intros a l cone
      simp only [finpair_cons, finproj_here]
      apply lift_fst
    · intros a l h ih cone
      simp [finpair_cons, List.In.here, finproj_there, ih]

  theorem finpair_univ {x : D} {l : List D} :
    forall (cone : forall k : l.In, x ⟶ l[k]) (f : x ⟶  finprod l) (h : forall k : l.In, cone k = f ≫ finproj l k),
    finpair x l cone = f := by
    induction l
    case nil =>
      intros
      apply toUnit_unique
    case cons a l ih =>
      intros cone f hf
      simp only [finpair_cons]
      apply hom_ext
      · simp [List.In.here]
        apply hf
      · simp [List.In.there, List.In.here]
        apply ih
        intros k
        simp [hf, finproj_there]


  def npow (x : D) (n : Nat) : D := finprod (List.replicate n x)

  def npow_zero (x : D) : npow x 0 = 𝟙_ D := rfl
  def npow_succ (x : D) : npow x (n+1) = x ⊗ npow x n := rfl

  def replicate_iso (x : D) (k : (List.replicate n x).In) : (List.replicate n x)[k] ≅ x :=
    eqToIso (List.get_replicate (a:=x) k)

  def nproj (x : D) (n : Nat) (k : Fin n) : (npow x n ⟶ x) :=
    finproj (List.replicate n x) (List.replicate_In k) ≫ (replicate_iso x (List.replicate_In k)).1

  theorem nproj_zero (x : D) :
    nproj x (n+1) 0 = fst _ _ := by
    simp [nproj, List.replicate, replicate_iso, List.replicate_In, finproj_here]

  theorem nproj_succ (x : D) (i : Fin n) :
    nproj x (n+1) i.succ = snd _ _ ≫ (nproj x n i) := by
    simp [npow, nproj, List.replicate, replicate_iso, List.replicate_In, finproj_there]

  def npair (x y : D) (n : Nat) (cone : Fin n → (x ⟶ y)) : x ⟶ npow y n :=
    finpair x (List.replicate n y) (fun k => cone (k.cast (List.length_replicate (n:=n))) ≫ (replicate_iso y k).2)

  def npair_zero (x y : D) (cone : Fin 0 -> (x ⟶ y)) :
    npair x y 0 cone = toUnit x := by
    simp [npair, finpair_nil]

  def npair_succ (x y : D) (cone : Fin (n+1) -> (x ⟶ y)) :
    npair x y (n+1) cone = lift (cone 0) (npair x y n (fun i => cone i.succ)) := by
    simp [npair, List.replicate, finpair_cons, replicate_iso]

  theorem npair_univ {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (f : x ⟶ npow y n)
    (h : forall i : Fin n, k i = f ≫ nproj y n i) :
    npair x y n k = f := by
    simp only [npair]
    apply finpair_univ
    intros k
    simp [h]
    congr
    simp [nproj, List.replicate_In, Iso.hom_inv_id]


  theorem to_npow_npair  {x y : D} (n : Nat)  (f : x ⟶ npow y n) :
   npair x y n (fun i => f ≫ nproj y n i )= f := by
     apply npair_univ
     intros i
     simp only


  theorem npair_univ' {x y : D} (n : Nat) (f g: x ⟶ npow y n)
    (h : forall i : Fin n, f ≫ nproj y n i = g ≫ nproj y n i) : f = g := by
     have a : f = npair x y n (fun i => f ≫ nproj y n i ):=
          by rw[to_npow_npair]
     rw[a]
     apply npair_univ
     intros i
     rw [h]


  @[simp]
  theorem npair_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    npair x y n k ≫ nproj y n i = k i := by
    simp [npair, nproj, <-Category.assoc, finpair_finproj]
    simp [List.replicate_In]


  theorem npair_natural (x y z: D) (n : Nat) (f : x ⟶ y) (k : Fin n → (y ⟶ z))  :
    npair x z n (fun i => f ≫ k i) = f ≫ npair y z n k := by
    apply npair_univ
    intro i
    simp

  def nlift (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : npow x n ⟶ npow y n :=
    npair (npow x n) y n (fun i => nproj x n i ≫ k i)

  theorem nlift_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    nlift x y n k ≫ nproj y n i = nproj x n i ≫ k i := by
    simp [nlift]

  theorem nlift_npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) :
   nlift x y n k = npair (npow x n) y n (fun i => nproj x n i ≫ k i) := by rfl

  theorem nlift_npair_nproj (x  : D) (n : Nat) :
    nlift x x n (fun i => 𝟙 x) = npair (npow x n) x n (fun i => nproj x n i) := by
    apply npair_univ'
    intros i
    simp only [nlift_nproj, Category.comp_id, npair_nproj]

  def nlift_diag (x y : D) (n : Nat) (f : x ⟶ y) : npow x n ⟶ npow y n :=
    nlift x y n (fun _ => f)

  theorem nlift_diag_id (x : D) : nlift_diag x x n (𝟙 x) = 𝟙 (npow x n) := by
    simp [nlift_diag, nlift]
    apply npair_univ
    intros ; simp

  theorem nlift_comp (x y z : D) (n : Nat) (k : Fin n → (x ⟶ y)) (l : Fin n → (y ⟶ z)) :
    nlift x y n k ≫ nlift y z n l = nlift x z n (fun i => k i ≫ l i) := by
    simp [nlift]
    symm
    apply npair_univ
    intros i; simp ; simp [<-Category.assoc, npair_nproj]

  theorem nlift_diag_comp (x y z : D) (f: x ⟶ y) (g : y ⟶ z) :
    nlift_diag x y n f ≫ nlift_diag y z n g = nlift_diag x z n (f ≫ g) :=
    nlift_comp x y z n (fun _ => f) (fun _ => g)

  def npow_functor (n : Nat) : D ⥤ D where
    obj := fun x => npow x n
    map := nlift_diag _ _ n
    map_id :=  nlift_diag_id
    map_comp := by intros; symm; exact nlift_diag_comp _ _ _ _ _

  theorem nproj_natural (x y : D) (n : Nat) (f : x ⟶ y) (i : Fin n) :
    (npow_functor n).map f ≫ nproj y n i = nproj x n i ≫ f := by
    simp only [npow_functor, nlift_diag, nlift_nproj]

  theorem npair_natural' (x y y': D) (n : Nat) (g : y ⟶ y') (k : Fin n → (x ⟶ y))  :
    npair x y' n (fun i => k i ≫ g) = npair x y n k ≫ (npow_functor n).map g := by
    apply npair_univ
    intros i
    simp only [Category.assoc, nproj_natural]
    rw [<-Category.assoc, npair_nproj]

  end NarryProducts


  section NaryProductBaseChange

  variable {C D : Type u} [Category C] [Category D] [ChosenFiniteProducts C] [ChosenFiniteProducts D] (F : C ⥤ D)

  def npow_oplax : npow_functor n ⋙ F ⟶ F ⋙ npow_functor n where
    app := fun X => npair (F.obj (npow X n)) (F.obj X) n (fun i => F.map (nproj X n i))
    naturality := by
      intros X Y f
      simp only [npow_functor, Functor.comp_obj, Functor.comp_map]
      have natl := npair_natural _ _ (F.obj Y) n (F.map ((npow_functor n).map f))
      have natr := npair_natural' (F.obj (npow X n)) _ _ n (F.map f)
      have := nproj_natural X Y n f
      simp only[npow_functor] at natl natr this
      rw [<- natl, <-natr]
      congr; ext i
      rw [<-F.map_comp,<-F.map_comp, this]

  end NaryProductBaseChange

end CategoryTheory.ChosenFiniteProducts
