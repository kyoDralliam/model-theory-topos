import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.ChosenFiniteProducts.Cat
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory


namespace CategoryTheory.ChosenFiniteProducts
  open MonoidalCategory

  section NarryProducts

  variable {D : Type u} [Category D] [ChosenFiniteProducts D]

  def npow (x : D) : Nat -> D
    | 0 => 𝟙_ D
    | n+1 => x  ⊗ (npow x n)

  def nproj (x : D) (n : Nat) (k : Fin n) : (npow x n ⟶ x) :=
    k.succRecOn
      (fun _ => fst x _)
      (fun _ _ ih => snd _ _ ≫ ih)

  def npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : x ⟶ npow y n :=
    match n with
    | 0 => toUnit x
    | n+1 => lift (k 0) (npair x y n (fun i => k (i+1)))

  theorem npair_univ {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (f : x ⟶ npow y n)
    (h : forall i : Fin n, k i = f ≫ nproj y n i) :
    npair x y n k = f := by
    induction n with
      | zero => apply toUnit_unique
      | succ n ih =>
        simp [npair] ; apply hom_ext <;> simp
        · have := h 0
          simp [nproj] at this
          assumption
        · rw [ih]
          intros i
          have hi := h i.succ
          simp [nproj] at hi
          rw [hi, Category.assoc]
          congr
  --new: to_npow_pair npair_univ'(maybe a better name would be npair_ext)
  --nproj_succ nlift_nproj nlift_npair
  theorem to_npow_npair  {x y : D} (n : Nat)  (f : x ⟶ npow y n) :
   npair x y n (fun i => f ≫ nproj y n i )= f := by
     apply npair_univ
     intros i
     simp


  theorem npair_univ' {x y : D} (n : Nat) (f g: x ⟶ npow y n)
    (h : forall i : Fin n, f ≫ nproj y n i = g ≫ nproj y n i) : f = g := by
     have a : f = npair x y n (fun i => f ≫ nproj y n i ):=
          by simp[to_npow_npair]
     rw[a]
     apply npair_univ
     intros i
     simp[h]

  theorem nproj_succ  (x : D) (n : Nat) (i : Fin n) :
    nproj x (n+1) i.succ = snd _ _ ≫ (nproj x n i) := by
   simp[nproj ]


  theorem npair_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    npair x y n k ≫ nproj y n i = k i := by
      induction n with
       | zero => exact (Fin.elim0 i)
       | succ n ih =>
         induction i using Fin.cases with
         | zero =>
           simp[nproj,npair]
         | succ i =>
           simp[npair]
           simp[nproj_succ]
           simp[ih]



  theorem npair_natural (x y z: D) (n : Nat) (f : x ⟶ y) (k : Fin n → (y ⟶ z))  :
    npair x z n (fun i => f ≫ k i) = f ≫ npair y z n k := by
    induction n with
      | zero => apply toUnit_unique
      | succ n ih =>
        simp [npair, ih]

  def nlift (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) : npow x n ⟶ npow y n :=
    match n with
    | 0 => 𝟙 (𝟙_ D)
    | n+1 => k 0 ⊗ nlift x y n (fun i => k (i+1))
    -- npair (npow x n) y n (fun i => nproj x n i ≫ k i)

  /-noncomputable
    def pb_prod0 (X : Psh D) (n : Nat) : F.op ⋙ npow X n ⟶ npow (F.op ⋙ X) n :=
      npair _ (F.op ⋙ X) n (fun i => whiskerLeft F.op (nproj X n i))
   -/


  theorem nlift_nproj {x y : D} (n : Nat) (k : Fin n → (x ⟶ y)) (i : Fin n) :
    nlift x y n k ≫ nproj y n i = nproj x n i ≫ k i := by
      induction n with
       | zero => exact (Fin.elim0 i)
       | succ n ih =>
         induction i using Fin.cases with
         | zero =>
           simp[nlift,nproj]
         | succ i =>
           simp[nproj_succ]
           simp[nlift]
           simp[ih]

  theorem nlift_npair (x y : D) (n : Nat) (k : Fin n → (x ⟶ y)) :
   nlift x y n k = npair (npow x n) y n (fun i => nproj x n i ≫ k i) := by
    apply npair_univ'
    intros i
    simp[npair_nproj]
    simp[nlift_nproj]

  theorem nlift_npair_nproj (x  : D) (n : Nat) :
   nlift x x n (fun i => 𝟙 x) = npair (npow x n) x n (fun i => nproj x n i) := by
    apply npair_univ'
    intros i
    simp[npair_nproj]
    simp[nlift_nproj]


  def nlift_diag (x y : D) (n : Nat) (f : x ⟶ y) : npow x n ⟶ npow y n :=
    nlift x y n (fun _ => f)

  theorem nlift_diag_id (x : D) : nlift_diag x x n (𝟙 x) = 𝟙 (npow x n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [nlift_diag, nlift]
      simp [nlift_diag] at ih
      rw [ih]
      simp [npow]

  theorem nlift_comp (x y z : D) (n : Nat) (k : Fin n → (x ⟶ y)) (l : Fin n → (y ⟶ z)) :
    nlift x y n k ≫ nlift y z n l = nlift x z n (fun i => k i ≫ l i) := by
    induction n with
    | zero =>
      simp [nlift]
      apply toUnit_unique
    | succ n ih =>
      simp [nlift]
      have := ih (fun i => k (i+1)) (fun i => l (i+1))
      rw [<-tensor_comp, ih]

  theorem nlift_diag_comp (x y z : D) (f: x ⟶ y) (g : y ⟶ z) :
    nlift_diag x y n f ≫ nlift_diag y z n g = nlift_diag x z n (f ≫ g) :=
    nlift_comp x y z n (fun _ => f) (fun _ => g)

  def npow_functor (n : Nat) : D ⥤ D where
    obj := fun x => npow x n
    map := nlift_diag _ _ n
    map_id := by apply nlift_diag_id
    map_comp := by intros; symm; apply nlift_diag_comp

  -- TODO : get Yiming's version

  theorem nproj_natural (x y : D) (n : Nat) (f : x ⟶ y) (i : Fin n) :
    (npow_functor n).map f ≫ nproj y n i = nproj x n i ≫ f := by
    simp [npow_functor, nlift_diag, nlift_nproj]

  theorem npair_natural' (x y y': D) (n : Nat) (g : y ⟶ y') (k : Fin n → (x ⟶ y))  :
    npair x y' n (fun i => k i ≫ g) = npair x y n k ≫ (npow_functor n).map g := by
    apply npair_univ
    intros i
    simp [nproj_natural]
    rw [<-Category.assoc, npair_nproj]

  end NarryProducts


  section NaryProductBaseChange

  variable {C D : Type u} [Category C] [Category D] [ChosenFiniteProducts C] [ChosenFiniteProducts D] (F : C ⥤ D)

  def npow_oplax : npow_functor n ⋙ F ⟶ F ⋙ npow_functor n where
    app := fun X => npair (F.obj (npow X n)) (F.obj X) n (fun i => F.map (nproj X n i))
    naturality := by
      intros X Y f
      simp [npow_functor]
      have natl := npair_natural _ _ (F.obj Y) n (F.map ((npow_functor n).map f))
      have natr := npair_natural' (F.obj (npow X n)) _ _ n (F.map f)
      have := nproj_natural X Y n f
      simp [npow_functor] at natl natr this
      rw [<- natl, <-natr]
      congr; ext i
      rw [<-F.map_comp,<-F.map_comp, this]

  end NaryProductBaseChange

end CategoryTheory.ChosenFiniteProducts