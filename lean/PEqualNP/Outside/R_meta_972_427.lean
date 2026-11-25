import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- Normalize Monotone2 to binary Nodup IsAO2, then split on IsSingleRead.
-- Any double re-read edge is moved to the canonical flag (0, 13) by a PGL(3, 3) collineation.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_972_427
    (normalizeAO2 :
      ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit),
        (∃ a b : Fin n → Bool, f a = false ∧ f b = true) →
        Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
        ∃ D : Circuit, IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.size ≤ C.size ∧
          ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x)
    (singleReadLower :
      let edges : List (ℕ × ℕ) :=
        [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
         (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
         (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
         (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
         (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
         (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
         (12, 14), (12, 15), (12, 17), (12, 23)]
      ∀ D : Circuit, IsAO2 26 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) →
        IsSingleRead D 26 (fun i => decide (13 ≤ i)) edges → 64 ≤ D.size)
    (doubleRereadAtZero :
      let edges : List (ℕ × ℕ) :=
        [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
         (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
         (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
         (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
         (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
         (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
         (12, 14), (12, 15), (12, 17), (12, 23)]
      ∀ D : Circuit, IsAO2 26 D → (∀ g ∈ D.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) →
        lineSingle D 26 (fun i => decide (13 ≤ i)) 0 13 = false →
        lineSingle D 26 (fun i => !decide (13 ≤ i)) 0 13 = false → 64 ≤ D.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro C hMono hComp
  let edges : List (ℕ × ℕ) :=
    [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25),
     (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24),
     (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24),
     (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22),
     (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20),
     (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24),
     (12, 14), (12, 15), (12, 17), (12, 23)]
  let f : (Fin 26 → Bool) → Bool := fun x =>
    decide (∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)
  have hfNonConst : ∃ a b : Fin 26 → Bool, f a = false ∧ f b = true := by
    refine ⟨fun _ => false, fun _ => true, ?_, ?_⟩
    · apply decide_eq_false
      rintro ⟨u, v, _, hu, _⟩
      exact Bool.noConfusion hu
    · apply decide_eq_true
      exact ⟨0, 13, by decide, rfl, rfl⟩
  have hCeq : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = f x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [hComp x]
    exact (decide_eq_true_iff).symm
  obtain ⟨D, hDAO, hDnd, hDsz, hDeq⟩ := normalizeAO2 26 f C hfNonConst hMono hCeq
  have hDcomp : ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
    intro x
    rw [hDeq x]
    exact decide_eq_true_iff
  let isL : ℕ → Bool := fun i => decide (13 ≤ i)
  cases hdr : doubleReread D 26 isL edges with
  | nil =>
    exact (singleReadLower D hDAO hDnd hDcomp hdr).trans hDsz
  | cons e rest =>
    have heMemDR : e ∈ doubleReread D 26 isL edges := by rw [hdr]; simp
    unfold doubleReread at heMemDR
    rw [List.mem_filter] at heMemDR
    obtain ⟨heEdge, heBoth⟩ := heMemDR
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at heBoth
    obtain ⟨heL, heP⟩ := heBoth
    -- Build explicit PGL(3, 3) collineation sigma mapping e = (u, v) to (0, 13)
    let isEdge (a b : ℕ) : Bool :=
      decide (a < 13) && decide (13 ≤ b) && decide (b < 26) &&
        (let s := (a + (b - 13)) % 13
         s == 0 || s == 1 || s == 3 || s == 9)
    have hEdgeIff : ∀ a < 26, ∀ b < 26, (a, b) ∈ edges ↔ isEdge a b = true := by
      have chk : ((List.range 26).all fun a => (List.range 26).all fun b =>
          edges.contains (a, b) == isEdge a b) = true := by decide +kernel
      intro a ha b hb
      have h1 := beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp chk a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb))
      rw [← List.contains_iff_mem, h1]
    let tauTbl : List ℕ :=
      [1, 0, 2, 3, 8, 5, 7, 6, 4, 9, 12, 11, 10,
       13, 25, 16, 15, 17, 18, 23, 20, 22, 21, 19, 24, 14]
    let applyTau (i : ℕ) : ℕ := tauTbl.getD i i
    let shift (l i : ℕ) : ℕ := if i < 13 then (i + l) % 13 else 13 + ((i - 13) + 13 - l % 13) % 13
    let frob (m i : ℕ) : ℕ := if i < 13 then (m * i) % 13 else 13 + (m * (i - 13)) % 13
    have hTauOK : (∀ i < 26, applyTau i < 26) ∧ (∀ i < 26, isL (applyTau i) = isL i) ∧
        (∀ i < 26, applyTau (applyTau i) = i) ∧
        (∀ a < 26, ∀ b < 26, isEdge (applyTau a) (applyTau b) = isEdge a b) := by
      have chk1 : ((List.range 26).all fun i => decide (applyTau i < 26)) = true := by decide +kernel
      have chk2 : ((List.range 26).all fun i => isL (applyTau i) == isL i) = true := by decide +kernel
      have chk3 : ((List.range 26).all fun i => applyTau (applyTau i) == i) = true := by decide +kernel
      have chk4 : ((List.range 26).all fun a => (List.range 26).all fun b =>
          isEdge (applyTau a) (applyTau b) == isEdge a b) = true := by decide +kernel
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi; exact of_decide_eq_true (List.all_eq_true.mp chk1 i (List.mem_range.mpr hi))
      · intro i hi; exact beq_iff_eq.mp (List.all_eq_true.mp chk2 i (List.mem_range.mpr hi))
      · intro i hi; exact beq_iff_eq.mp (List.all_eq_true.mp chk3 i (List.mem_range.mpr hi))
      · intro a ha b hb
        exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp chk4 a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb))
    have hFrobOK : ∀ m ∈ ([1, 3, 9] : List ℕ),
        (∀ i < 26, frob m i < 26) ∧ (∀ i < 26, isL (frob m i) = isL i) ∧
        (∀ i < 26, ∀ j < 26, frob m i = frob m j → i = j) ∧
        (∀ a < 26, ∀ b < 26, isEdge (frob m a) (frob m b) = isEdge a b) := by
      have chk1 : (([1, 3, 9] : List ℕ).all fun m => (List.range 26).all fun i => decide (frob m i < 26)) = true := by decide +kernel
      have chk2 : (([1, 3, 9] : List ℕ).all fun m => (List.range 26).all fun i => isL (frob m i) == isL i) = true := by decide +kernel
      have chk3 : (([1, 3, 9] : List ℕ).all fun m => (List.range 26).all fun i => (List.range 26).all fun j =>
          !(frob m i == frob m j) || (i == j)) = true := by decide +kernel
      have chk4 : (([1, 3, 9] : List ℕ).all fun m => (List.range 26).all fun a => (List.range 26).all fun b =>
          isEdge (frob m a) (frob m b) == isEdge a b) = true := by decide +kernel
      intro m hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp chk1 m hm) i (List.mem_range.mpr hi))
      · intro i hi
        exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp chk2 m hm) i (List.mem_range.mpr hi))
      · intro i hi j hj hij
        have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp chk3 m hm) i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
        rw [hij, beq_self_eq_true] at h
        exact beq_iff_eq.mp h
      · intro a ha b hb
        exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp chk4 m hm) a (List.mem_range.mpr ha)) b (List.mem_range.mpr hb))
    have hShiftOK : ∀ l < 13,
        (∀ i < 26, shift l i < 26) ∧ (∀ i < 26, isL (shift l i) = isL i) ∧
        (∀ i < 26, ∀ j < 26, shift l i = shift l j → i = j) ∧
        (∀ a < 26, ∀ b < 26, isEdge (shift l a) (shift l b) = isEdge a b) := by
      intro l hl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi; dsimp only [shift]; split_ifs <;> omega
      · intro i hi; dsimp only [shift, isL]; split_ifs <;> simp <;> omega
      · intro i hi j hj hij
        dsimp only [shift] at hij
        by_cases hi13 : i < 13 <;> by_cases hj13 : j < 13 <;>
          simp only [hi13, hj13, ite_true, ite_false] at hij <;> omega
      · intro a ha b hb
        by_cases ha13 : a < 13
        · by_cases hb13 : b < 13
          · have h1 : ¬ 13 ≤ shift l b := by dsimp only [shift]; simp only [hb13, ite_true]; omega
            have h2 : ¬ 13 ≤ b := by omega
            dsimp only [isEdge]; simp [h1, h2]
          · have hsa13 : shift l a < 13 := by dsimp only [shift]; simp only [ha13, ite_true]; omega
            have hsbGe : 13 ≤ shift l b := by dsimp only [shift]; simp only [hb13, ite_false]; omega
            have hsbLt : shift l b < 26 := by dsimp only [shift]; simp only [hb13, ite_false]; omega
            have hSum : (shift l a + (shift l b - 13)) % 13 = (a + (b - 13)) % 13 := by
              dsimp only [shift]
              simp only [ha13, hb13, ite_true, ite_false]
              have hsub : 13 + (b - 13 + 13 - l % 13) % 13 - 13 = (b - 13 + 13 - l % 13) % 13 := by omega
              rw [hsub]
              omega
            dsimp only [isEdge]
            simp only [ha13, hsa13, hsbGe, hsbLt, show 13 ≤ b by omega, hb, decide_true, Bool.true_and, hSum]
        · have h1 : ¬ shift l a < 13 := by dsimp only [shift]; simp only [ha13, ite_false]; omega
          dsimp only [isEdge]; simp [ha13, h1]
    let collin (u v i : ℕ) : ℕ :=
      let l := v - 13
      let d := (u + l) % 13
      let m := if d = 3 then 9 else if d = 9 then 3 else 1
      let j := frob m (shift l i)
      if d = 0 then j else applyTau j
    have hEdgeEndpoints : ∀ p ∈ edges,
        p.1 < 13 ∧ 13 ≤ p.2 ∧ p.2 < 26 ∧ collin p.1 p.2 p.1 = 0 ∧ collin p.1 p.2 p.2 = 13 := by
      have chk : edges.all (fun p => decide (
          p.1 < 13 ∧ 13 ≤ p.2 ∧ p.2 < 26 ∧ collin p.1 p.2 p.1 = 0 ∧ collin p.1 p.2 p.2 = 13)) = true := by
        decide +kernel
      intro p hp
      exact of_decide_eq_true (List.all_eq_true.mp chk p hp)
    obtain ⟨he1Lt13, he2Ge13, he2Lt, hMap0, hMap13⟩ := hEdgeEndpoints e heEdge
    have he1Lt : e.1 < 26 := by omega
    let l0 : ℕ := e.2 - 13
    have hl0 : l0 < 13 := by omega
    let d0 : ℕ := (e.1 + l0) % 13
    let m0 : ℕ := if d0 = 3 then 9 else if d0 = 9 then 3 else 1
    have hm0Mem : m0 ∈ ([1, 3, 9] : List ℕ) := by dsimp only [m0]; split_ifs <;> simp
    obtain ⟨hShLt, hShIsL, hShInj, hShEdg⟩ := hShiftOK l0 hl0
    obtain ⟨hFrLt, hFrIsL, hFrInj, hFrEdg⟩ := hFrobOK m0 hm0Mem
    obtain ⟨hTaLt, hTaIsL, hTaInv, hTaEdg⟩ := hTauOK
    have hLt : ∀ i < 26, collin e.1 e.2 i < 26 := by
      intro i hi
      dsimp only [collin]
      change (if d0 = 0 then frob m0 (shift l0 i) else applyTau (frob m0 (shift l0 i))) < 26
      split_ifs
      · exact hFrLt _ (hShLt i hi)
      · exact hTaLt _ (hFrLt _ (hShLt i hi))
    have hIsL : ∀ i < 26, isL (collin e.1 e.2 i) = isL i := by
      intro i hi
      dsimp only [collin]
      change isL (if d0 = 0 then frob m0 (shift l0 i) else applyTau (frob m0 (shift l0 i))) = isL i
      split_ifs
      · rw [hFrIsL _ (hShLt i hi), hShIsL i hi]
      · rw [hTaIsL _ (hFrLt _ (hShLt i hi)), hFrIsL _ (hShLt i hi), hShIsL i hi]
    have hInj26 : ∀ i < 26, ∀ j < 26, collin e.1 e.2 i = collin e.1 e.2 j → i = j := by
      intro i hi j hj hij
      dsimp only [collin] at hij
      change (if d0 = 0 then frob m0 (shift l0 i) else applyTau (frob m0 (shift l0 i))) =
        (if d0 = 0 then frob m0 (shift l0 j) else applyTau (frob m0 (shift l0 j))) at hij
      split_ifs at hij
      · exact hShInj i hi j hj (hFrInj _ (hShLt i hi) _ (hShLt j hj) hij)
      · have h1 := congrArg applyTau hij
        rw [hTaInv _ (hFrLt _ (hShLt i hi)), hTaInv _ (hFrLt _ (hShLt j hj))] at h1
        exact hShInj i hi j hj (hFrInj _ (hShLt i hi) _ (hShLt j hj) h1)
    have hEdg : ∀ a < 26, ∀ b < 26, (collin e.1 e.2 a, collin e.1 e.2 b) ∈ edges ↔ (a, b) ∈ edges := by
      intro a ha b hb
      rw [hEdgeIff _ (hLt a ha) _ (hLt b hb), hEdgeIff a ha b hb]
      dsimp only [collin]
      change isEdge (if d0 = 0 then frob m0 (shift l0 a) else applyTau (frob m0 (shift l0 a)))
        (if d0 = 0 then frob m0 (shift l0 b) else applyTau (frob m0 (shift l0 b))) = true ↔ isEdge a b = true
      split_ifs
      · rw [hFrEdg _ (hShLt a ha) _ (hShLt b hb), hShEdg a ha b hb]
      · rw [hTaEdg _ (hFrLt _ (hShLt a ha)) _ (hFrLt _ (hShLt b hb)),
          hFrEdg _ (hShLt a ha) _ (hShLt b hb), hShEdg a ha b hb]
    let mapW (i : ℕ) : ℕ := if i < 26 then collin e.1 e.2 i else i
    let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map mapW⟩
    let D' : Circuit := ⟨D.gates.map mapG, mapW D.output⟩
    have hMapInj : ∀ a b : ℕ, mapW a = mapW b → a = b := by
      intro a b hab
      by_cases ha : a < 26 <;> by_cases hb : b < 26
      · simp only [mapW, ha, hb, ite_true] at hab
        exact hInj26 a ha b hb hab
      · simp only [mapW, ha, hb, ite_true, ite_false] at hab
        have := hLt a ha
        omega
      · simp only [mapW, ha, hb, ite_true, ite_false] at hab
        have := hLt b hb
        omega
      · simp only [mapW, ha, hb, ite_false] at hab
        exact hab
    have hD'sz : D'.size = D.size := by
      change (D.gates.map mapG).length = D.gates.length
      exact List.length_map mapG
    have hD'AO : IsAO2 26 D' := by
      obtain ⟨hAndOr, hBack, hLen2⟩ := hDAO
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [D', List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact hAndOr g0 hg0
      · intro j hj w hw
        have hj0 : j < D.gates.length := by simpa only [D', List.length_map] using hj
        have hget : D'.gates.getD j ⟨GateOp.or, []⟩ = mapG (D.gates.getD j ⟨GateOp.or, []⟩) := by
          dsimp only [D']
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj0),
            List.getElem_map, List.getD_eq_getElem _ _ hj0]
        change w ∈ (D'.gates.getD j ⟨GateOp.or, []⟩).inputs at hw
        rw [hget] at hw
        simp only [mapG, List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        have hw0lt : w0 < 26 + j := hBack j hj0 w0 hw0
        by_cases h26 : w0 < 26
        · simp only [mapW, h26, ite_true]
          have := hLt w0 h26
          omega
        · simp only [mapW, h26, ite_false]
          exact hw0lt
      · intro g hg
        simp only [D', List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        change (g0.inputs.map mapW).length = 2
        rw [List.length_map]
        exact hLen2 g0 hg0
    have hD'nd : ∀ g ∈ D'.gates, g.inputs.Nodup := by
      intro g hg
      simp only [D', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact (hDnd g0 hg0).map hMapInj
    -- Generic foldl simulation under mapW
    have getDSnocNe : ∀ {α : Type} (w : List α) (v d : α) (i : ℕ), i ≠ w.length →
        (w ++ [v]).getD i d = w.getD i d := by
      intro α w v d i hi
      by_cases hlt : i < w.length
      · exact List.getD_append _ _ _ _ hlt
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have simFold : ∀ {α : Type} (d : α) (evalG : GateOp → List α → α)
        (ls : List Gate) (u1 u2 : List α),
        u1.length = u2.length → 26 ≤ u1.length →
        (∀ i, u1.getD i d = u2.getD (mapW i) d) →
        ∀ i, (ls.foldl (fun w g => w ++ [evalG g.op (g.inputs.map fun j => w.getD j d)]) u1).getD i d =
          ((ls.map mapG).foldl (fun w g => w ++ [evalG g.op (g.inputs.map fun j => w.getD j d)]) u2).getD (mapW i) d := by
      intro α d evalG ls
      induction ls with
      | nil => intro u1 u2 _ _ h i; exact h i
      | cons g rest ih =>
        intro u1 u2 hl h26 h
        have hgv : evalG g.op (g.inputs.map fun j => u1.getD j d) =
            evalG (mapG g).op ((mapG g).inputs.map fun j => u2.getD j d) := by
          simp only [mapG, List.map_map]
          congr 1
          apply List.map_congr_left
          intro j _
          exact h j
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        refine ih _ _ (by simp [hl]) (by simp; omega) ?_
        intro i
        rw [hgv]
        by_cases hil : i = u1.length
        · have hmw : mapW i = u2.length := by
            simp only [mapW, show ¬ i < 26 by omega, ite_false]; omega
          rw [hmw, hil]; simp
        · have hmw : mapW i ≠ u2.length := by
            by_cases hlt : i < 26
            · simp only [mapW, hlt, ite_true]
              have := hLt i hlt
              omega
            · simp only [mapW, hlt, ite_false]; omega
          rw [getDSnocNe _ _ _ _ hil, getDSnocNe _ _ _ _ hmw, h i]
    -- Show D' computes the same PG(2, 3) incidence function
    have hSurj26 : ∀ k < 26, ∃ i < 26, collin e.1 e.2 i = k := by
      intro k hk
      let f26 : Fin 26 → Fin 26 := fun x => ⟨collin e.1 e.2 x.val, hLt x.val x.isLt⟩
      have hfInj : Function.Injective f26 := fun a b hab =>
        Fin.ext (hInj26 a.val a.isLt b.val b.isLt (congrArg Fin.val hab))
      obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hfInj) ⟨k, hk⟩
      exact ⟨x.val, x.isLt, congrArg Fin.val hx⟩
    have hD'comp : ∀ x : Fin 26 → Bool, D'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
      intro x
      let x' : Fin 26 → Bool := fun i => x ⟨collin e.1 e.2 i.val, hLt i.val i.isLt⟩
      have hbase : ∀ i, (List.ofFn x').getD i false = (List.ofFn x).getD (mapW i) false := by
        intro i
        by_cases hlt : i < 26
        · have hlt2 := hLt i hlt
          simp only [mapW, hlt, ite_true, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt2,
            dite_true, Option.getD_some, x']
        · simp only [mapW, hlt, ite_false]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hev := simFold false GateOp.eval D.gates (List.ofFn x') (List.ofFn x)
        (by simp) (by simp) hbase D.output
      have hD'eq : D'.eval (List.ofFn x) = D.eval (List.ofFn x') := by
        unfold Circuit.eval Circuit.wires
        exact hev.symm
      rw [hD'eq, hDcomp x']
      constructor
      · rintro ⟨u, v, huv, hu, hv⟩
        exact ⟨⟨collin e.1 e.2 u.val, hLt u.val u.isLt⟩, ⟨collin e.1 e.2 v.val, hLt v.val v.isLt⟩,
          (hEdg u.val u.isLt v.val v.isLt).mpr huv, hu, hv⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨u0, hu0lt, hu0eq⟩ := hSurj26 u.val u.isLt
        obtain ⟨v0, hv0lt, hv0eq⟩ := hSurj26 v.val v.isLt
        refine ⟨⟨u0, hu0lt⟩, ⟨v0, hv0lt⟩, ?_, ?_, ?_⟩
        · exact (hEdg u0 hu0lt v0 hv0lt).mp (by rwa [hu0eq, hv0eq])
        · dsimp only [x']; convert hu using 2; exact Fin.ext hu0eq
        · dsimp only [x']; convert hv using 2; exact Fin.ext hv0eq
    -- Show lineSingle invariance for both isL and !isL
    have hLineSingleEq : ∀ (mark : ℕ → Bool), (∀ i < 26, mark (collin e.1 e.2 i) = mark i) →
        lineSingle D' 26 mark 0 13 = lineSingle D 26 mark e.1 e.2 := by
      intro mark hMark
      let lpEval : GateOp → List (Bool × Bool) → Bool × Bool := fun op ins =>
        match op with
        | GateOp.or => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
            (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)
      let bitsD : List Bool := (List.range 26).map fun i => i == e.1 || i == e.2
      let bitsD' : List Bool := (List.range 26).map fun i => i == 0 || i == 13
      let initD : List (Bool × Bool) := bitsD.zipIdx.map fun (b, i) => if mark i then (false, b) else (b, false)
      let initD' : List (Bool × Bool) := bitsD'.zipIdx.map fun (b, i) => if mark i then (false, b) else (b, false)
      have hInitLen : initD.length = 26 := by simp [initD, bitsD]
      have hInitLen' : initD'.length = 26 := by simp [initD', bitsD']
      have hBaseLP : ∀ i, initD.getD i (false, false) = initD'.getD (mapW i) (false, false) := by
        intro i
        by_cases hlt : i < 26
        · have hlt2 := hLt i hlt
          simp only [mapW, hlt, ite_true]
          rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
          simp only [initD, initD', bitsD, bitsD', List.getElem_map, List.getElem_zipIdx,
            List.getElem_range, zero_add]
          rw [hMark i hlt]
          have hbit : (i == e.1 || i == e.2) = (collin e.1 e.2 i == 0 || collin e.1 e.2 i == 13) := by
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, beq_iff_eq]
            constructor
            · rintro (rfl | rfl)
              · exact Or.inl hMap0
              · exact Or.inr hMap13
            · rintro (h0 | h13)
              · exact Or.inl (hInj26 i hlt e.1 he1Lt (h0.trans hMap0.symm))
              · exact Or.inr (hInj26 i hlt e.2 he2Lt (h13.trans hMap13.symm))
          rw [hbit]
        · simp only [mapW, hlt, ite_false]
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hSimLP := simFold (false, false) lpEval D.gates initD initD'
        (by omega) (by omega) hBaseLP D.output
      unfold lineSingle linearParts
      exact congrArg Prod.snd hSimLP.symm
    have hL0 : lineSingle D' 26 isL 0 13 = false :=
      (hLineSingleEq isL hIsL).trans heL
    have hP0 : lineSingle D' 26 (fun i => !isL i) 0 13 = false :=
      (hLineSingleEq (fun i => !isL i) (fun i hi => congrArg (!·) (hIsL i hi))).trans heP
    have h64 : 64 ≤ D'.size := doubleRereadAtZero D' hD'AO hD'nd hD'comp hL0 hP0
    rw [hD'sz] at h64
    exact h64.trans hDsz
