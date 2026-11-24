import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2436_417
  (samples : ∃ (j : Fin 42) (a b : Fin 43) (D : Circuit),
      (j = 1 ∨ j = 21 ∨ j = 22) ∧ a < b ∧ (a,b) ≠ (0,j.castSucc) ∧
      (b = Fin.last 42 → a ≠ 0 ∧ a ≠ j.castSucc) ∧
      (∀ i : Fin 42, ([0,j.val,a.val,b.val] : List ℕ).count i.val = 1 → ∃ g ∈ D.gates, i.val ∈ g.inputs) ∧
      Monotone2 D ∧ NestedCover.ReadsBack 44 D ∧ D.size ≤ 122 ∧
      let F := fun (x : Fin 42 → Bool) => ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true
      let f := fun (x : Fin 42 → Bool) => have y : Fin 43 → Bool := fun (i : Fin (42+1)) => Fin.lastCases (x 0 || x j) x i; D.eval (List.ofFn fun (i : Fin (43+1)) => Fin.lastCases (y a || y b) y i)
      (∀ x, (F x ∧ ∀ z < x, ¬ F z) ∨ (¬ F x ∧ ∀ z > x, F z) → (f x = true ↔ F x)))
  (physical : ∀ (j : Fin 42) (a b : Fin 43) (D : Circuit), Monotone2 D → Monotone (fun (x : Fin 42 → Bool) => have y : Fin 43 → Bool := fun (i : Fin (42+1)) => Fin.lastCases (x 0 || x j) x i; D.eval (List.ofFn fun (i : Fin (43+1)) => Fin.lastCases (y a || y b) y i)))
  (boundary : ∀ (F : (Fin 42 → Bool) → Prop) (f : (Fin 42 → Bool) → Bool), Monotone f → (∀ x, (F x ∧ ∀ z < x, ¬ F z) ∨ (¬ F x ∧ ∀ z > x, F z) → (f x = true ↔ F x)) → ∀ x, f x = true ↔ F x) :
   ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     x2 < x3 ∧       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧           (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x4 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧                 x4.size ≤ (122 : ℕ) ∧                   ∀ (x5 : Fin (42 : ℕ) → Bool),                     have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;                     x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨j,a,b,D,h⟩ := samples
  refine ⟨j,a,b,D,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,?_⟩
  have hm := h.2.2.2.2.2.1
  have ht := h.2.2.2.2.2.2.2.2
  with_reducible exact boundary (fun (x : Fin 42 → Bool) => ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true) (fun (x : Fin 42 → Bool) => have y : Fin 43 → Bool := fun (i : Fin (42+1)) => Fin.lastCases (x 0 || x j) x i; D.eval (List.ofFn fun (i : Fin (43+1)) => Fin.lastCases (y a || y b) y i)) (physical j a b D hm) ht
