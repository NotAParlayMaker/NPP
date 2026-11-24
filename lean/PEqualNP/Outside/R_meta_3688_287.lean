import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Pin both inputs of each isolated matching pair, then relabel the remaining matching as the diagonal.
-- With q off-diagonal edges, at most 2q labels remain. Each removed pair must pay for two gates.
theorem PEqualNP.Outside.R_meta_3688_287
    (restrictPairs : ∀ (n r : ℕ) (E : Finset (Fin n × Fin n)) (S : Finset (Fin r × Fin r))
      (f : Fin r ↪ Fin n) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      0 < r → (∀ i,(i,σ i) ∈ E) →
      (∀ i j,(i,j) ∈ S ↔ (f i,σ (f j)) ∈ E) →
      IsAO2 (n+n) C → (∀ x,circuitFun (n+n) C x = decide
        (∃ i j,(i,j) ∈ E ∧ x (Fin.castAdd n i)=true ∧ x (Fin.natAdd n j)=true)) →
      ∃ D : Circuit, Monotone2 D ∧ 2*(n-r)+D.size ≤ C.size ∧
        ∀ x,circuitFun (r+r) D x = decide
          (∃ i j,(i,j) ∈ S ∧ x (Fin.castAdd r i)=true ∧ x (Fin.natAdd r j)=true))
    (activeCore : ∀ (r : ℕ) (S : Finset (Fin r × Fin r)) (D : Circuit),
      0 < r → r ≤ 2*(S.card-r) → (∀ i,(i,i) ∈ S) →
      (∀ i,∃ j,i≠j ∧ ((i,j)∈S ∨ (j,i)∈S)) →
      (∀ a b u v, a≠b → u≠v → ¬ ((a,u)∈S ∧ (a,v)∈S ∧ (b,u)∈S ∧ (b,v)∈S)) →
      Monotone2 D → (∀ x,circuitFun (r+r) D x = decide
        (∃ i j,(i,j)∈S ∧ x (Fin.castAdd r i)=true ∧ x (Fin.natAdd r j)=true)) →
      S.card+r ≤ D.size+1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E σ C more _ square mat ao sem
  have compress {n : ℕ} (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
      (mat : ∀ i,(i,σ i)∈E) (more : n<E.card) :
      ∃ (r : ℕ) (f : Fin r ↪ Fin n) (S : Finset (Fin r × Fin r)),
        0<r ∧ r≤n ∧ r≤2*(S.card-r) ∧ E.card=S.card+(n-r) ∧
        (∀ a b,(a,b)∈S ↔ (f a,σ (f b))∈E) ∧
        ∀ a,∃ b,a≠b ∧ ((a,b)∈S ∨ (b,a)∈S) := by
    classical
    let X := E.filter fun e => e.2 ≠ σ e.1
    let A := X.image Prod.fst ∪ X.image (fun e => σ.symm e.2)
    let r := A.card
    let f := A.orderEmbOfFin (show A.card=r from rfl)
    have inA (a : Fin r) : f a∈A := A.orderEmbOfFin_mem .. 
    have onto {a : Fin n} (m : a∈A) : ∃ i,f i=a := by
      have h : a∈Set.range f := by simpa [f] using m
      exact h
    let S := Finset.univ.filter fun e : Fin r × Fin r => (f e.1,σ (f e.2))∈E
    have mem (a b) : (a,b)∈S ↔ (f a,σ (f b))∈E := by simp [S]
    let Y := S.filter fun e => e.2≠e.1
    have diagonal {m : ℕ} (T : Finset (Fin m × Fin m)) (π : Equiv.Perm (Fin m)) (d : ∀ i,(i,π i)∈T) :
        T.card=(T.filter (fun e => e.2≠π e.1)).card+m := by
      have eq : T.filter (fun e => e.2=π e.1) = Finset.univ.image (fun i : Fin m => (i,π i)) := by
        ext ⟨a,b⟩
        simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and,Prod.mk.injEq]
        constructor
        · rintro ⟨_,rfl⟩; exact ⟨a,rfl,rfl⟩
        · rintro ⟨i,rfl,rfl⟩; exact ⟨d i,rfl⟩
      have cnt := Finset.card_filter_add_card_filter_not (s := T) (fun e => e.2=π e.1)
      rw [eq,Finset.card_image_of_injective _ (fun _ _ e => congrArg Prod.fst e)] at cnt
      simp only [Finset.card_univ,Fintype.card_fin] at cnt
      change m + (T.filter (fun e => e.2≠π e.1)).card = T.card at cnt
      omega
    have d1 : E.card=X.card+n := diagonal E σ mat
    have d2 : S.card=Y.card+r := diagonal S (Equiv.refl _) (fun a => (mem _ _).mpr (mat _))
    let g (e : Fin r × Fin r) := (f e.1,σ (f e.2))
    have inj : Function.Injective g := by
      intro a b eq
      exact Prod.ext (f.injective (congrArg Prod.fst eq)) (f.injective (σ.injective (congrArg Prod.snd eq)))
    have image : Y.image g = X := by
      ext ⟨a,b⟩
      constructor
      · rintro m
        obtain ⟨⟨u,v⟩,hin,h⟩ := Finset.mem_image.mp m
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        obtain ⟨edge,ne⟩ := Finset.mem_filter.mp hin
        exact Finset.mem_filter.mpr ⟨(mem _ _).mp edge,fun eq => ne (f.injective (σ.injective eq))⟩
      · intro m
        obtain ⟨u,hu⟩ := onto (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst m))
        obtain ⟨v,hv⟩ := onto (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e => σ.symm e.2) m))
        obtain ⟨edge,off⟩ := Finset.mem_filter.mp m
        have e2 : σ (f v)=b := by rw [hv,σ.apply_symm_apply]
        refine Finset.mem_image.mpr ⟨(u,v),Finset.mem_filter.mpr ⟨(mem u v).mpr (by simpa [hu,e2] using edge),?_⟩,Prod.ext hu e2⟩
        change v≠u
        intro eq; exact off (by change b≠_ at off; change b=σ a; rw [← e2,eq,hu])
    have eq := congrArg Finset.card image
    rw [Finset.card_image_of_injective _ inj] at eq
    have rle : r≤n := by simpa [r] using A.card_le_univ
    have r2 : r≤2*X.card := by
      have card := Finset.card_union_le (X.image Prod.fst) (X.image fun e => σ.symm e.2)
      have c1 := Finset.card_image_le (f := Prod.fst) (s := X)
      have c2 := Finset.card_image_le (f := fun e => σ.symm e.2) (s := X)
      change r ≤ _ at card
      omega
    have rpos : 0<r := by
      obtain ⟨e,me⟩ := Finset.card_pos.mp (show 0<X.card by omega)
      exact Finset.card_pos.mpr ⟨e.1,Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst me)⟩
    refine ⟨r,f.toEmbedding,S,rpos,rle,by omega,by omega,mem,?_⟩
    intro a
    rcases Finset.mem_union.mp (inA a) with m|m
    · obtain ⟨⟨i,j⟩,me,hi⟩ := Finset.mem_image.mp m
      obtain ⟨b,hb⟩ := onto (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e => σ.symm e.2) me))
      have e2 : σ (f b)=j := by rw [hb,σ.apply_symm_apply]
      obtain ⟨ed,ne⟩ := Finset.mem_filter.mp me
      change i=f a at hi
      exact ⟨b,fun eq => ne (by rw [hi,eq,← e2]),Or.inl ((mem a b).mpr (by simpa [← hi,e2] using ed))⟩
    · obtain ⟨⟨i,j⟩,me,hj⟩ := Finset.mem_image.mp m
      obtain ⟨b,hb⟩ := onto (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst me))
      have e2 : σ (f a)=j := by rw [← hj,σ.apply_symm_apply]
      obtain ⟨ed,ne⟩ := Finset.mem_filter.mp me
      change f b=i at hb
      exact ⟨b,fun eq => ne (by rw [← hb,← eq,e2]),Or.inr ((mem b a).mpr (by simpa [hb,e2] using ed))⟩
  obtain ⟨r,f,S,pos,rle,dense,sz,mem,seen⟩ := compress E σ mat more
  obtain ⟨D,md,paid,ev⟩ := restrictPairs n r E S f σ C pos mat mem ao sem
  have sq (a b u v) (ab : a≠b) (uv : u≠v) :
      ¬ ((a,u)∈S ∧ (a,v)∈S ∧ (b,u)∈S ∧ (b,v)∈S) := by
    rintro ⟨a1,a2,b1,b2⟩
    exact square _ _ _ _ (f.injective.ne ab) (σ.injective.ne (f.injective.ne uv))
      ⟨(mem _ _).mp a1,(mem _ _).mp a2,(mem _ _).mp b1,(mem _ _).mp b2⟩
  have h := activeCore r S D pos dense (fun i => (mem _ _).mpr (mat _)) seen sq md ev
  omega
