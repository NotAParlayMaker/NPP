import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1872_397
    (normalize : ∀ (n : ℕ) (C : Circuit) (a b : ℕ), Monotone2 C → ReadsBack n C →
    a < n + C.size → b < n + C.size →
    (∀ w ∈ ({a,b} : Finset ℕ), ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      (C.wires x).getD w false ≠ (C.wires y).getD w false) →
    ∃ (D : Circuit) (u v : ℕ), TopForm.IsAO2 n D ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size ≤ C.size ∧
      u < n + D.size ∧ v < n + D.size ∧ ∀ x : List Bool, x.length = n →
        ((D.wires x).getD u false = (C.wires x).getD a false) ∧
        ((D.wires x).getD v false = (C.wires x).getD b false))
    (binaryCore : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   IsAO2 26 x1 → (∀ g ∈ x1.gates, g.inputs.Nodup) →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b hM hB ha hb
  dsimp only
  intro hCover hReject haOnly hbOnly
  let P (p l : Fin 13) := (List.ofFn fun i : Fin 13 => decide (i = p)) ++
    List.ofFn fun j : Fin 13 => decide (j = l)
  have len (p l : Fin 13) : (P p l).length = 26 := by simp [P]
  obtain ⟨pa,la,hpa,hwa,hwb⟩ := haOnly
  obtain ⟨pb,lb,hpb,hzb,hza⟩ := hbOnly
  have hVar : ∀ w ∈ ({a,b} : Finset ℕ), ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧
      (C.wires x).getD w false ≠ (C.wires y).getD w false := by
    intro w hw
    rcases (show w = a ∨ w = b from by simpa using hw) with rfl | rfl
    · refine ⟨P pa la,P pb lb,len _ _,len _ _,?_⟩
      rw [show (C.wires (P pa la)).getD w false = true from hwa,
        show (C.wires (P pb lb)).getD w false = false from hza]
      decide
    · refine ⟨P pb lb,P pa la,len _ _,len _ _,?_⟩
      rw [show (C.wires (P pb lb)).getD w false = true from hzb,
        show (C.wires (P pa la)).getD w false = false from hwb]
      decide
  obtain ⟨D,u,v,hAO,hDistinct,hSize,hu,hv,hSame⟩ := normalize 26 C a b hM hB ha hb hVar
  have hLower := binaryCore D u v hAO hDistinct hu hv
  dsimp only at hLower
  apply Nat.le_trans _ hSize
  apply hLower
  · intro p l hi
    have h := hSame (P p l) (len p l)
    dsimp only [P] at h
    rw [h.1,h.2]
    exact hCover p l hi
  · intro Q hQ
    let x := (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun j : Fin 13 =>
      decide (∀ r ∈ Q, r - j ∉ ({0,1,3,9} : Finset (Fin 13)))
    have h := hSame x (by simp [x])
    dsimp only [x] at h
    rw [h.1,h.2]
    exact hReject Q hQ
  · refine ⟨pa,la,?_,?_,?_⟩
    · exact hpa
    · exact (hSame (P pa la) (len pa la)).1.trans hwa
    · exact (hSame (P pa la) (len pa la)).2.trans hwb
  · refine ⟨pb,lb,?_,?_,?_⟩
    · exact hpb
    · exact (hSame (P pb lb) (len pb lb)).2.trans hzb
    · exact (hSame (P pb lb) (len pb lb)).1.trans hza
