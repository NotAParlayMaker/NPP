import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Color each of the ten open neighborhoods by a factor that rejects it.
-- Relabeling the graph and interchanging the factors leaves eighteen color profiles.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_2375_1 :
    (∀ (C : Circuit) (u v k : ℕ), k ∈ ([0, 1, 3, 5, 7, 11, 42, 50] : List ℕ) → FanInTwo C → C.size ≤ 18 →
        let row := fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val
        let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
        (∀ i : Fin 10, w (row i) (if k.testBit i.val then v else u) = false) →
        (∀ b : Bool, ∃ x, w x u = b ∧ w x v = !b) →
        (∀ x, (w x u = true ∧ w x v = true) ↔
          ∃ i j : Fin 10, row i j = true ∧ x i = true ∧ x j = true) → False) →
    (∀ (C : Circuit) (u v k : ℕ), k ∈ ([15, 43, 45, 51, 54, 116] : List ℕ) → FanInTwo C → C.size ≤ 18 →
        let row := fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val
        let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
        (∀ i : Fin 10, w (row i) (if k.testBit i.val then v else u) = false) →
        (∀ b : Bool, ∃ x, w x u = b ∧ w x v = !b) →
        (∀ x, (w x u = true ∧ w x v = true) ↔
          ∃ i j : Fin 10, row i j = true ∧ x i = true ∧ x j = true) → False) →
    (∀ (C : Circuit) (u v k : ℕ), k ∈ ([31, 47, 62, 109] : List ℕ) → FanInTwo C → C.size ≤ 18 →
        let row := fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val
        let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
        (∀ i : Fin 10, w (row i) (if k.testBit i.val then v else u) = false) →
        (∀ b : Bool, ∃ x, w x u = b ∧ w x v = !b) →
        (∀ x, (w x u = true ∧ w x v = true) ↔
          ∃ i j : Fin 10, row i j = true ∧ x i = true ∧ x j = true) → False) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  let F := fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let row := fun (i j : Fin 10) => (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD i.val 0).testBit j.val
  -- A bit marks the color of a vertex neighborhood. The three groups have at most
  -- three, exactly four, and exactly five marked neighborhoods, respectively.
  let repData : Array ℕ := #[0, 1, 3, 5, 7, 11, 42, 50, 15, 43, 45, 51, 54, 116, 31, 47, 62, 109]
  let rep := fun k : Fin 18 => repData[k.val]!
  let bts := fun (k : Fin 18) (i : Fin 10) => (rep k).testBit i.val
  have member : ∀ k, rep k ∈ ([0, 1, 3, 5, 7, 11, 42, 50] : List ℕ) ∨ rep k ∈ ([15, 43, 45, 51, 54, 116] : List ℕ) ∨ rep k ∈ ([31, 47, 62, 109] : List ℕ) := by decide
  let a : Equiv.Perm (Fin 10) := ⟨![2, 3, 4, 9, 7, 1, 8, 0, 6, 5], ![7, 5, 0, 1, 2, 9, 8, 4, 6, 3], by decide, by decide⟩
  have aAdj : ∀ i j, row (a i) (a j) = row i j := by decide
  let b : Equiv.Perm (Fin 10) := ⟨![0, 4, 3, 8, 5, 1, 9, 2, 6, 7], ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6], by decide, by decide⟩
  have bAdj : ∀ i j, row (b i) (b j) = row i j := by decide
  let move := fun word : List Bool => word.foldr
    (fun bit (tail : Equiv.Perm (Fin 10)) => (if bit then b else a).trans tail) (Equiv.refl _)
  have preserve : ∀ (ws : List Bool) (i j : Fin 10), row (move ws i) (move ws j) = row i j := by
    intro ws
    induction ws with
    | nil => intro i j; rfl
    | cons bit ws ih =>
      intro i j
      cases bit
      · exact (ih (a i) (a j)).trans (aAdj i j)
      · exact (ih (b i) (b j)).trans (bAdj i j)
  let mix := fun (s x : Bool) => if s then !x else x
  let toggle := fun (f : Fin 10 → Bool) (j i : Fin 10) => if i = j then !(f i) else f i
  have compMix (s t x : Bool) : mix t (mix s x) = mix (s.xor t) x := by cases s <;> cases t <;> cases x <;> rfl
  have negMix (s x : Bool) : (!(mix s x)) = mix s (!x) := by cases s <;> cases x <;> rfl
  -- Each transition toggles one vertex of one representative. The certificate
  -- selects the resulting representative, a word in a and b, and a color swap.
  let words : Array ℕ := #[1, 2, 3, 4, 6, 5, 7, 8, 12, 10, 14, 9, 13, 11, 15, 24, 20, 28, 18, 26, 22, 30, 17, 25, 21, 29, 19, 27, 23, 31, 40, 56, 44, 60, 34, 50, 42, 58, 38, 54, 46, 62, 41, 57, 45, 61, 35, 51, 39, 55, 88, 120, 76, 108, 92, 124, 82, 114, 90, 122, 70, 102, 78, 110, 89, 121, 93, 125, 83, 115, 71, 103, 152, 216, 184, 248, 140, 204, 156, 220, 178, 242, 186, 250, 166, 230, 142, 206, 157, 221, 179, 243, 167, 231, 280, 408, 312, 440, 332, 460, 284, 412, 358, 486, 334, 462, 285, 413, 359, 487, 664, 920, 668, 924, 718, 974, 669, 925, 1436, 1948]
  let cert : Array ℕ := #[1, 513, 33, 129, 97, 257, 641, 225, 321, 289, 0, 2, 3, 67, 66, 194, 451, 227, 195, 771, 513, 1, 4, 5, 516, 740, 452, 2949, 3045, 453, 33, 4, 1, 1893, 1861, 1157, 519, 1189, 582, 614, 418, 3, 2, 8, 488, 2440, 523, 2472, 1353, 1385, 547, 67, 8, 2, 520, 9, 521, 492, 74, 1868, 9, 131, 905, 739, 76, 547, 332, 1196, 1641, 77, 11, 355, 12, 76, 739, 515, 460, 1164, 204, 940, 548, 1893, 5, 4, 14, 15, 5423, 5359, 1359, 5360, 6, 2309, 15, 740, 5583, 5, 4496, 4976, 1647, 4913, 901, 15, 2309, 1157, 1007, 1893, 17, 1199, 591, 1009, 7, 356, 5327, 5583, 740, 516, 4495, 5551, 4271, 4911, 5327, 998, 7, 16, 2981, 485, 5137, 4944, 913, 1393, 4497, 5137, 198, 4337, 326, 550, 998, 4177, 5041, 5457, 552, 3144, 520, 488, 8, 5320, 5384, 5352, 6696, 6664, 905, 10, 9, 2440, 5320, 8, 5417, 5928, 4395, 5356, 5320, 1001, 76, 12, 905, 552, 6380, 5513, 4393, 5612, 812, 5417, 1644, 2956, 6060, 556, 10, 4780, 5705, 4141]
  let entry := fun (k : Fin 18) (j : Fin 10) => cert[k.val * 10 + j.val]!
  let next := fun (k : Fin 18) (j : Fin 10) => Fin.ofNat 18 (entry k j % 32)
  let swap := fun (k : Fin 18) (j : Fin 10) => (entry k j).testBit 12
  let code := fun (k : Fin 18) (j : Fin 10) => words[(entry k j / 32) % 128]!
  let path := fun (k : Fin 18) (j : Fin 10) => (List.range (code k j).log2).map (code k j).testBit
  have transition : ∀ (k : Fin 18) (j i : Fin 10), bts (next k j) i =
      mix (swap k j) (toggle (bts k) j (move (path k j) i)) := by decide
  let good := fun f : Fin 10 → Bool => ∃ (k : Fin 18) (p : Equiv.Perm (Fin 10)) (s : Bool),
    (∀ i j, row (p i) (p j) = row i j) ∧ ∀ i, bts k i = mix s (f (p i))
  have base : good (fun _ => false) := by
    refine ⟨0, Equiv.refl _, false, fun _ _ => rfl, ?_⟩
    decide
  have extend (f) (hf : good f) (j : Fin 10) : good (toggle f j) := by
    obtain ⟨k, p, s, adjP, bitsP⟩ := hf
    let h := p.symm j
    let q := move (path k h)
    refine ⟨next k h, q.trans p, s.xor (swap k h), ?_, ?_⟩
    · intro i l
      exact (adjP (q i) (q l)).trans (preserve _ i l)
    · intro i
      have slide (v : Fin 10) : toggle (bts k) h v = mix s (toggle f j (p v)) := by
        by_cases z : p v = j
        · have z' : v = h := p.eq_symm_apply.mpr z
          simp only [toggle, z', ite_true, bitsP, h, Equiv.apply_symm_apply]
          exact negMix s (f j)
        · have z' : v ≠ h := fun hz => z (p.eq_symm_apply.mp hz)
          simp only [toggle, z, z', ite_false, bitsP]
      exact (transition k h i).trans ((congrArg (mix (swap k h)) (slide (q i))).trans (compMix _ _ _))
  -- Every coloring is reached from the empty one by toggling its marked vertices.
  have cover (col : Fin 10 → Bool) : good col := by
    have allSets (S : Finset (Fin 10)) : good (fun i => decide (i ∈ S)) := by
      induction S using Finset.induction_on with
      | empty => simpa only [Finset.notMem_empty, decide_false] using base
      | insert j S hj ih =>
        have eq : (fun i => decide (i ∈ insert j S)) = toggle (fun i => decide (i ∈ S)) j := by
          funext i
          by_cases h : i = j
          · subst i; simp [toggle, hj]
          · simp [toggle, h]
        rw [eq]
        exact extend (fun i => decide (i ∈ S)) ih j
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.decide_coe] using
      allSets (Finset.univ.filter fun i => col i = true)
  have edgeIff (x : Fin 10 → Bool) : F x = true ↔
      ∃ i j : Fin 10, row i j = true ∧ x i = true ∧ x j = true := by
    constructor
    · intro h
      simp only [F, Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact ⟨0, 1, by decide, h.1, h.2⟩
      · exact ⟨1, 2, by decide, h.1, h.2⟩
      · exact ⟨2, 3, by decide, h.1, h.2⟩
      · exact ⟨3, 4, by decide, h.1, h.2⟩
      · exact ⟨4, 0, by decide, h.1, h.2⟩
      · exact ⟨0, 5, by decide, h.1, h.2⟩
      · exact ⟨1, 6, by decide, h.1, h.2⟩
      · exact ⟨2, 7, by decide, h.1, h.2⟩
      · exact ⟨3, 8, by decide, h.1, h.2⟩
      · exact ⟨4, 9, by decide, h.1, h.2⟩
      · exact ⟨5, 7, by decide, h.1, h.2⟩
      · exact ⟨7, 9, by decide, h.1, h.2⟩
      · exact ⟨9, 6, by decide, h.1, h.2⟩
      · exact ⟨6, 8, by decide, h.1, h.2⟩
      · exact ⟨8, 5, by decide, h.1, h.2⟩
    · rintro ⟨i, j, he, hi, hj⟩
      have pairs : ∀ a b : Fin 10, row a b = true → (a,b) ∈ ([(0,1), (1,0), (1,2), (2,1), (2,3), (3,2), (3,4), (4,3), (4,0), (0,4), (0,5), (5,0), (1,6), (6,1), (2,7), (7,2), (3,8), (8,3), (4,9), (9,4), (5,7), (7,5), (7,9), (9,7), (9,6), (6,9), (6,8), (8,6), (8,5), (5,8)] : List (Fin 10 × Fin 10)) := by decide
      have hlist := pairs i j he
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlist
      rcases hlist with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [F, hi, hj]
  have emptyRow : ∀ i : Fin 10, F (row i) = false := by decide
  -- Relabel the input indices in every gate and leave the internal wires in place.
  have renameInputs (C : Circuit) (ok : FanInTwo C) (p : Fin 10 → Fin 10) :
    ∃ (D : Circuit) (r : ℕ → ℕ), FanInTwo D ∧ D.size = C.size ∧
      ∀ (x : Fin 10 → Bool) (i : ℕ), (D.wires (List.ofFn x)).getD (r i) false =
        (C.wires (List.ofFn (x ∘ p))).getD i false := by
    let r := fun i : ℕ => if h : i < 10 then (p ⟨i, h⟩).val else i
    let rename := fun g : Gate => Gate.mk g.op (g.inputs.map r)
    let D := Circuit.mk (C.gates.map rename) (r C.output)
    refine ⟨D, r, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      simpa [rename] using ok old hold
    · change (C.gates.map rename).length = C.gates.length
      exact List.length_map rename
    intro x
    have read (tail : List Bool) (i : ℕ) :
        (List.ofFn x ++ tail).getD (r i) false = (List.ofFn (x ∘ p) ++ tail).getD i false := by
      by_cases hi : i < 10
      · have hr : r i = (p ⟨i, hi⟩).val := dite_eq_left hi
        rw [hr, List.getD_append _ _ _ _ (by simp),
          List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simp),
          List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn]; rfl
      · have hr : r i = i := dite_eq_right hi
        rw [hr, List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
        simp
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have run (gs : List Gate) (tail : List Bool) : ∃ vs : List Bool,
        (gs.map rename).foldl step (List.ofFn x ++ tail) = List.ofFn x ++ vs ∧
        gs.foldl step (List.ofFn (x ∘ p) ++ tail) = List.ofFn (x ∘ p) ++ vs := by
      induction gs generalizing tail with
      | nil => exact ⟨tail, rfl, rfl⟩
      | cons g gs ih =>
        let v := g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ p) ++ tail).getD i false)
        have valEq : (rename g).op.eval ((rename g).inputs.map fun i => (List.ofFn x ++ tail).getD i false) = v := by
          simp only [rename, List.map_map, Function.comp_def, read, v]
        have a : step (List.ofFn x ++ tail) (rename g) = List.ofFn x ++ (tail ++ [v]) := by
          simp only [step, valEq, List.append_assoc]
        have b : step (List.ofFn (x ∘ p) ++ tail) g = List.ofFn (x ∘ p) ++ (tail ++ [v]) := by
          simp only [step, v, List.append_assoc]
        simpa only [List.map_cons, List.foldl_cons, a, b] using ih (tail ++ [v])
    obtain ⟨vs, a, b⟩ := run C.gates []
    simp only [List.append_nil] at a b
    intro i
    change ((C.gates.map rename).foldl step (List.ofFn x)).getD (r i) false =
      (C.gates.foldl step (List.ofFn (x ∘ p))).getD i false
    rw [a, b, read]
  intro few four five g tail u v firstOK tailOK budget
  let C := Circuit.mk (g :: tail.gates) 0
  let w := fun (x : Fin 10 → Bool) (i : ℕ) => (C.wires (List.ofFn x)).getD i false
  change (∃ x, w x u = true ∧ w x v = false) → (∃ x, w x u = false ∧ w x v = true) →
    (∀ x, F x = true → w x u = true ∧ w x v = true) →
    ∃ x, F x = false ∧ w x u = true ∧ w x v = true
  intro onlyU onlyV major
  by_contra miss
  have exactPair (x) : (w x u = true ∧ w x v = true) ↔ F x = true := by
    refine ⟨?_, major x⟩
    intro h
    cases e : F x with
    | false => exact False.elim (miss ⟨x, e, h⟩)
    | true => rfl
  have ok : FanInTwo C := by
    intro a ha
    rcases List.mem_cons.mp ha with h | h
    · exact firstOK _ (by simp [h])
    · exact tailOK _ h
  have sz : C.size ≤ 18 := by
    change tail.gates.length ≤ 17 at budget
    change (g :: tail.gates).length ≤ 18
    simp only [List.length_cons]
    omega
  -- If both factors reject a neighborhood, choose the first one to color it.
  obtain ⟨k, P, swp, ar, orbit⟩ := cover (fun i => w (row i) u)
  let Q := P.symm
  have lr (i : Fin 10) : Q (P i) = i := P.symm_apply_apply i
  have rl (i : Fin 10) : P (Q i) = i := P.apply_symm_apply i
  have arQ (i j : Fin 10) : row (Q i) (Q j) = row i j := by
    simpa only [rl] using (ar (Q i) (Q j)).symm
  have rows (i) : row i ∘ Q = row (P i) := by
    funext j
    simpa only [Function.comp_apply, rl] using (ar i (Q j)).symm
  obtain ⟨D, r, valid, size, same⟩ := renameInputs C ok Q
  let ww := fun (x : Fin 10 → Bool) (i : ℕ) => (D.wires (List.ofFn x)).getD i false
  have run (x i) : ww x (r i) = w (x ∘ Q) i := same x i
  let U := if swp then r v else r u
  let V := if swp then r u else r v
  have sign (i : Fin 10) : ww (row i) (if (rep k).testBit i.val then V else U) = false := by
    have h : (rep k).testBit i.val = (if swp then !(w (row (P i)) u) else w (row (P i)) u) := orbit i
    have excluded : ¬(w (row (P i)) u = true ∧ w (row (P i)) v = true) := by
      intro both
      have e := (exactPair _).mp both
      rw [emptyRow] at e
      contradiction
    cases sw : swp <;> cases bit : w (row (P i)) u <;> cases other : w (row (P i)) v <;>
      simp_all only [U, V, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, true_and, and_true, not_true_eq_false]
  have back (x : Fin 10 → Bool) : (x ∘ P) ∘ Q = x := by funext i; simp only [Function.comp_apply, rl]
  have distinct (b : Bool) : ∃ x, ww x U = b ∧ ww x V = !b := by
    obtain ⟨x, hx, hx'⟩ := onlyU
    obtain ⟨y, hy, hy'⟩ := onlyV
    cases sw : swp <;> cases b
    · exact ⟨y ∘ P, by simp [U, sw, run, back, hy], by simp [V, sw, run, back, hy']⟩
    · exact ⟨x ∘ P, by simp [U, sw, run, back, hx], by simp [V, sw, run, back, hx']⟩
    · exact ⟨x ∘ P, by simp [U, sw, run, back, hx'], by simp [V, sw, run, back, hx]⟩
    · exact ⟨y ∘ P, by simp [U, sw, run, back, hy'], by simp [V, sw, run, back, hy]⟩
  have computes (x : Fin 10 → Bool) : (ww x U = true ∧ ww x V = true) ↔
      ∃ i j : Fin 10, row i j = true ∧ x i = true ∧ x j = true := by
    have h : (ww x U = true ∧ ww x V = true) ↔ (w (x ∘ Q) u = true ∧ w (x ∘ Q) v = true) := by
      cases sw : swp <;> simp only [U, V, sw, Bool.false_eq_true, ite_false, ite_true, run, and_comm]
    rw [h, exactPair, edgeIff]
    constructor
    · rintro ⟨i, j, edge, hi, hj⟩
      exact ⟨Q i, Q j, (arQ i j).trans edge, hi, hj⟩
    · rintro ⟨i, j, edge, hi, hj⟩
      exact ⟨P i, P j, (ar i j).trans edge, by simpa only [Function.comp_apply, lr] using hi,
        by simpa only [Function.comp_apply, lr] using hj⟩
  have small : D.size ≤ 18 := size.trans_le sz
  rcases member k with h | h | h
  · exact few D U V (rep k) h valid small sign distinct computes
  · exact four D U V (rep k) h valid small sign distinct computes
  · exact five D U V (rep k) h valid small sign distinct computes
