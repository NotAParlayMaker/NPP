import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership PEqualNP.NotPremium

-- Each bit 14*min(a,b)+max(a,b) selects one of the thirteen negative-row orbits under the flag stabilizer.
-- The owning gate is pivotal at (0,7). Its sources are shared raw endpoints or preceding OR gates.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1985_519
  (prepare : let F := fun x : Fin 14 → Bool => ∃ a b : Fin 14, (a.val < 7 ↔ 7 ≤ b.val) ∧
        (a.val+b.val)%7 ∈ ([0,1,3] : List ℕ) ∧ x a = true ∧ x b = true
      let W := fun (D : Circuit) (j : ℕ) (a b : Fin 14) =>
        (160025510407 : ℕ).testBit (14 * min a.val b.val + max a.val b.val) = true ∧ Owns 14 D j a b ∧
        circuitFun 14 ⟨replaceByConst D.gates j false,D.output⟩ (pairInput (0 : Fin 14) 7) = false ∧
        ∀ w ∈ (NestedCover.gateAt D j).inputs,
          ((w = a.val ∨ w = b.val) ∧ (w = 0 ∨ w = 7)) ∨
          (14 ≤ w ∧ w < 14+j ∧ (NestedCover.gateAt D (w-14)).op = GateOp.or)
      ∀ C : Circuit, Monotone2 C → (∀ x, circuitFun 14 C x = true ↔ F x) → C.size < 27 →
      ∃ (D : Circuit) (j : ℕ) (a b : Fin 14), Monotone2 D ∧ D.size ≤ C.size ∧
        (∀ x, circuitFun 14 D x = true ↔ F x) ∧ W D j a b)
  (bound : let F := fun x : Fin 14 → Bool => ∃ a b : Fin 14, (a.val < 7 ↔ 7 ≤ b.val) ∧
        (a.val+b.val)%7 ∈ ([0,1,3] : List ℕ) ∧ x a = true ∧ x b = true
      let W := fun (D : Circuit) (j : ℕ) (a b : Fin 14) =>
        (160025510407 : ℕ).testBit (14 * min a.val b.val + max a.val b.val) = true ∧ Owns 14 D j a b ∧
        circuitFun 14 ⟨replaceByConst D.gates j false,D.output⟩ (pairInput (0 : Fin 14) 7) = false ∧
        ∀ w ∈ (NestedCover.gateAt D j).inputs,
          ((w = a.val ∨ w = b.val) ∧ (w = 0 ∨ w = 7)) ∨
          (14 ≤ w ∧ w < 14+j ∧ (NestedCover.gateAt D (w-14)).op = GateOp.or)
      ∀ (D : Circuit) (j : ℕ) (a b : Fin 14), Monotone2 D →
        (∀ x, circuitFun 14 D x = true ↔ F x) → W D j a b → 27 ≤ D.size) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  intro C hm _ _ hc
  by_contra! small
  let E: List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  have geometry : ∀ u v : Fin 14,
      ((u.val < 7 ↔ 7 ≤ v.val) ∧ (u.val+v.val)%7 ∈ ([0,1,3] : List ℕ)) ↔
      ((u.val,v.val) ∈ E ∨ (v.val,u.val) ∈ E) := by decide +kernel
  have good (x : Fin 14 → Bool) : circuitFun 14 C x = true ↔
      ∃ a b : Fin 14, (a.val < 7 ↔ 7 ≤ b.val) ∧ (a.val+b.val)%7 ∈ ([0,1,3] : List ℕ) ∧
        x a = true ∧ x b = true := by
    constructor
    · intro h
      obtain ⟨a,b,hedge,ha,hb⟩ := (hc x).mp h
      obtain ⟨hside,hdiff⟩ := (geometry a b).mpr (Or.inl hedge)
      exact ⟨a,b,hside,hdiff,ha,hb⟩
    · rintro ⟨a,b,hside,hdiff,ha,hb⟩
      apply (hc x).mpr
      rcases (geometry a b).mp ⟨hside,hdiff⟩ with hab | hba
      · exact ⟨a,b,hab,ha,hb⟩
      · exact ⟨b,a,hba,hb,ha⟩
  obtain ⟨D,j,a,b,hd,hle,hdgood,hw⟩ := prepare C hm good small
  exact (Nat.not_le_of_gt small) ((bound D j a b hd hdgood hw).trans hle)
