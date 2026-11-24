import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2836_47
    (hPair0 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 0 || x 4, x 0 || x 3] ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
            x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hPair4 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval [x 0, x 1, x 2, x 3, x 5, x 6, x 7, x 8, x 0 || x 4, x 4 || x 1] ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
            x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hTrip2 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 4 || x 2]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
            x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hTripRest : ∀ (k : Fin 9), (k = 1 ∨ k = 3 ∨ k = 6) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 4 || x k]) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
              x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C F hfan hsz hcases
  have hszC : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  have hevC : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (w : List Bool), D.eval w =
      (D.gates.foldl (fun s g => s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]) w).getD
        D.output false := fun _ _ => rfl
  have hfanC : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D =
      (∀ g ∈ D.gates,
        g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
          PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
        g.inputs.length ≤ 2) := fun _ => rfl
  let step := fun (s : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    s ++ [g.op.eval (g.inputs.map fun i => s.getD i false)]
  let run := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (s : List Bool) => gs.foldl step s
  have step_len : ∀ (s : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate),
      (step s g).length = s.length + 1 := by intro s g; simp [step]
  let dropWire := fun (p i : ℕ) => if i < p then i else if i = p then 23 else i - 1
  let dropGate := fun (p : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
    PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map (dropWire p))
  let dropCirc := fun (p : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.CircuitLowerBounds.Circuit.mk (D.gates.map (dropGate p)) (dropWire p D.output)
  have drop_fan : ∀ (p : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.FanInTwo (dropCirc p D) := by
    intro p D hf
    rw [hfanC] at hf ⊢
    intro g hg
    simp only [dropCirc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨hop, hlen⟩ := hf g0 hg0
    exact ⟨hop, by simpa [dropGate] using hlen⟩
  have drop_sz : ∀ (p : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      D.size ≤ 13 → (dropCirc p D).size ≤ 13 := by
    intro p D hs
    rw [hszC] at hs ⊢
    simpa [dropCirc] using hs
  have drop_read : ∀ (p : ℕ) (wFull wShort : List Bool),
      wFull.length = wShort.length + 1 → p ≤ wShort.length → wShort.length ≤ 23 →
      (∀ i : ℕ, i < p → wShort.getD i false = wFull.getD i false) →
      wFull.getD p false = false →
      (∀ i : ℕ, p < i → i < wFull.length → wShort.getD (i - 1) false = wFull.getD i false) →
      ∀ i : ℕ, wShort.getD (dropWire p i) false = wFull.getD i false := by
    intro p wFull wShort hlen hp h23 hlt heq hgt i
    dsimp only [dropWire]
    by_cases hi1 : i < p
    · simp only [hi1, ↓reduceIte]; exact hlt i hi1
    · simp only [hi1, ↓reduceIte]
      by_cases hi2 : i = p
      · simp only [hi2, ↓reduceIte]
        rw [List.getD_eq_default _ _ h23, heq]
      · simp only [hi2, ↓reduceIte]
        by_cases hi3 : i < wFull.length
        · exact hgt i (by omega) hi3
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have drop_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p : ℕ) (wFull wShort : List Bool),
      wFull.length = wShort.length + 1 → p ≤ wShort.length →
      wShort.length + gs.length ≤ 23 →
      (∀ i : ℕ, i < p → wShort.getD i false = wFull.getD i false) →
      wFull.getD p false = false →
      (∀ i : ℕ, p < i → i < wFull.length → wShort.getD (i - 1) false = wFull.getD i false) →
      ∀ i : ℕ, (run (gs.map (dropGate p)) wShort).getD (dropWire p i) false =
        (run gs wFull).getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro p wFull wShort hlen hp h23 hlt heq hgt i
      exact drop_read p wFull wShort hlen hp (by omega) hlt heq hgt i
    | cons g gs ih =>
      intro p wFull wShort hlen hp h23 hlt heq hgt
      change ∀ i : ℕ,
        (run (gs.map (dropGate p)) (step wShort (dropGate p g))).getD (dropWire p i) false =
        (run gs (step wFull g)).getD i false
      have hrd := drop_read p wFull wShort hlen hp (by simp at h23; omega) hlt heq hgt
      have hval : (dropGate p g).op.eval ((dropGate p g).inputs.map fun i => wShort.getD i false) =
          g.op.eval (g.inputs.map fun i => wFull.getD i false) := by
        dsimp only [dropGate]
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hrd a
      have hs_eq : step wShort (dropGate p g) =
          wShort ++ [g.op.eval (g.inputs.map fun i => wFull.getD i false)] := by
        dsimp only [step]; rw [hval]
      rw [hs_eq]
      dsimp only [step]
      generalize g.op.eval (g.inputs.map fun i => wFull.getD i false) = v
      apply ih p (wFull ++ [v]) (wShort ++ [v])
      · simp [hlen]
      · simp; omega
      · simp at h23 ⊢; omega
      · intro i hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hlt i hi
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact heq
      · intro i hip hif
        simp only [List.length_append, List.length_singleton] at hif
        by_cases hltF : i < wFull.length
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hltF]
          exact hgt i hip hltF
        · have hi_eq : i = wFull.length := by omega
          have hi1_eq : i - 1 = wShort.length := by omega
          rw [hi1_eq, hi_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _),
            Nat.sub_self, Nat.sub_self]
  let perm := fun i : ℕ => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i
  have perm_lt9 : ∀ j : ℕ, j < 9 → perm j < 9 := by
    intro j hj; interval_cases j <;> decide
  have perm_ge9 : ∀ j : ℕ, 9 ≤ j → perm j = j := by
    intro j hj
    dsimp only [perm]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have perm_lt : ∀ n j : ℕ, 9 ≤ n → j < n → perm j < n := by
    intro n j hn hj
    by_cases h9 : j < 9
    · have := perm_lt9 j h9; omega
    · rw [perm_ge9 j (by omega)]; exact hj
  have hF_perm : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b5 || b5 && b8 || b8 && b3 || b3 && b4 || b4 && b0 || b0 && b1 ||
        b5 && b7 || b8 && b6 || b3 && b2 || b1 && b6 || b7 && b2 || b2 && b1) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  let permGate := fun g : PEqualNP.CircuitLowerBounds.Gate =>
    PEqualNP.CircuitLowerBounds.Gate.mk g.op (g.inputs.map perm)
  let permCirc := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
    PEqualNP.CircuitLowerBounds.Circuit.mk (D.gates.map permGate) (perm D.output)
  have perm_fan : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → PEqualNP.MetaComplexity.FanInTwo (permCirc D) := by
    intro D hf
    rw [hfanC] at hf ⊢
    intro g hg
    simp only [permCirc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨hop, hlen⟩ := hf g0 hg0
    exact ⟨hop, by simpa [permGate] using hlen⟩
  have perm_sz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      D.size ≤ 13 → (permCirc D).size ≤ 13 := by
    intro D hs
    rw [hszC] at hs ⊢
    simpa [permCirc] using hs
  have perm_run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (perm j) false = W.getD j false) →
      ∀ j : ℕ, (run (gs.map permGate) W').getD (perm j) false = (run gs W).getD j false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ hW j; exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      change ∀ j : ℕ,
        (run (gs.map permGate) (step W' (permGate g))).getD (perm j) false =
        (run gs (step W g)).getD j false
      have hv : (permGate g).op.eval ((permGate g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        dsimp only [permGate]
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hW a
      have hs' : step W' (permGate g) =
          W' ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := by
        dsimp only [step]; rw [hv]
      rw [hs']
      apply ih
      · rw [step_len]; simp [hl]
      · rw [step_len]; omega
      · intro j
        dsimp only [step]
        generalize g.op.eval (g.inputs.map fun i => W.getD i false) = v
        by_cases hj : j < W.length
        · have hj' : perm j < W'.length := by rw [← hl]; exact perm_lt W.length j h9 hj
          rw [List.getD_append _ _ _ _ hj', List.getD_append _ _ _ _ hj]
          exact hW j
        · rw [perm_ge9 j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
              List.getElem?_append_right (le_refl _), ← hl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have perm_eval : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 9 → Bool) (ys : List Bool),
      ys.length = 2 →
      (permCirc D).eval (List.ofFn x ++ ys) =
        D.eval (List.ofFn (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++ ys) := by
    intro D x ys hys
    rw [hevC, hevC]
    dsimp only [permCirc]
    exact perm_run D.gates
      (List.ofFn (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++ ys)
      (List.ofFn x ++ ys) (by simp) (by simp) (by
        intro j
        by_cases hj : j < 9
        · interval_cases j <;> rfl
        · rw [perm_ge9 j (by omega)]
          by_cases hj11 : j < 11
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by simp; omega),
              List.getElem?_append_right (by simp; omega)]
            simp
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp [hys]; omega),
              List.getElem?_eq_none (by simp [hys]; omega)])
      D.output
  have killPair4 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1]) = F x) →
      False := by
    intro D hf hs hev
    obtain ⟨x, hx⟩ := hPair4 (dropCirc 4 D) (drop_fan 4 D hf) (drop_sz 4 D hs)
    apply hx
    have hlenD : D.gates.length ≤ 13 := by rwa [← hszC]
    rw [hevC]
    dsimp only [dropCirc]
    have hd := drop_run D.gates 4
      (List.ofFn (Function.update x 4 false) ++ [x 0 || x 4, x 4 || x 1])
      [x 0, x 1, x 2, x 3, x 5, x 6, x 7, x 8, x 0 || x 4, x 4 || x 1]
      (by simp) (by simp) (by simp; omega)
      (by intro i hi; interval_cases i <;> rfl)
      rfl
      (by intro i hip hif; simp at hif; interval_cases i <;> rfl)
      D.output
    change (run (D.gates.map (dropGate 4)) _).getD (dropWire 4 D.output) false = F x
    rw [hd]
    have hx' := hev x
    rw [hevC] at hx'
    exact hx'
  have killTrip : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (k : Fin 9),
      (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6) →
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false, x 0 || x 4 || x k]) = F x) →
      False := by
    intro D k hk hf hs hev
    have hev_short : ∀ x : Fin 9 → Bool,
        (dropCirc 9 D).eval (List.ofFn x ++ [x 0 || x 4 || x k]) = F x := by
      intro x
      have hlenD : D.gates.length ≤ 13 := by rwa [← hszC]
      rw [hevC]
      dsimp only [dropCirc]
      have hd := drop_run D.gates 9
        (List.ofFn x ++ [false, x 0 || x 4 || x k])
        (List.ofFn x ++ [x 0 || x 4 || x k])
        (by simp) (by simp) (by simp; omega)
        (by intro i hi; interval_cases i <;> rfl)
        rfl
        (by
          intro i hip hif
          simp at hif
          have hi10 : i = 10 := by omega
          rw [hi10]
          rfl)
        D.output
      change (run (D.gates.map (dropGate 9)) _).getD (dropWire 9 D.output) false = F x
      rw [hd]
      have hx' := hev x
      rw [hevC] at hx'
      exact hx'
    rcases hk with rfl | rfl | rfl | rfl
    · obtain ⟨x, hx⟩ := hTripRest 1 (Or.inl rfl) (dropCirc 9 D) (drop_fan 9 D hf) (drop_sz 9 D hs)
      exact hx (hev_short x)
    · obtain ⟨x, hx⟩ := hTrip2 (dropCirc 9 D) (drop_fan 9 D hf) (drop_sz 9 D hs)
      exact hx (hev_short x)
    · obtain ⟨x, hx⟩ := hTripRest 3 (Or.inr (Or.inl rfl)) (dropCirc 9 D) (drop_fan 9 D hf) (drop_sz 9 D hs)
      exact hx (hev_short x)
    · obtain ⟨x, hx⟩ := hTripRest 6 (Or.inr (Or.inr rfl)) (dropCirc 9 D) (drop_fan 9 D hf) (drop_sz 9 D hs)
      exact hx (hev_short x)
  rcases hcases with h1 | h2 | h3 | ⟨k, hk0, hk4, h4⟩
  · obtain ⟨x, hx⟩ := hPair0 (dropCirc 0 C) (drop_fan 0 C hfan) (drop_sz 0 C hsz)
    apply hx
    have hlenC : C.gates.length ≤ 13 := by rwa [← hszC]
    rw [hevC]
    dsimp only [dropCirc]
    have hd := drop_run C.gates 0
      (List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3])
      [x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 0 || x 4, x 0 || x 3]
      (by simp) (by simp) (by simp; omega)
      (by intro i hi; omega)
      rfl
      (by intro i hip hif; simp at hif; interval_cases i <;> rfl)
      C.output
    change (run (C.gates.map (dropGate 0)) _).getD (dropWire 0 C.output) false = F x
    rw [hd]
    have hx' := h1 x
    rw [hevC] at hx'
    exact hx'
  · exact killPair4 C hfan hsz h2
  · refine killPair4 (permCirc C) (perm_fan C hfan) (perm_sz C hsz) ?_
    intro x
    let z : Fin 9 → Bool := fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)
    have hupd : List.ofFn (fun i => Function.update x 4 false (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) =
        List.ofFn (Function.update z 4 false) := by
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      simp only [List.length_ofFn] at hi1
      simp only [List.getElem_ofFn]
      interval_cases i <;> rfl
    rw [perm_eval C (Function.update x 4 false) [x 0 || x 4, x 4 || x 1] rfl, hupd]
    have hz := h3 z
    dsimp only [z] at hz
    exact hz.trans (hF_perm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8))
  · obtain ⟨kv, klt⟩ := k
    interval_cases kv
    · exact hk0 rfl
    · exact killTrip C 1 (Or.inl rfl) hfan hsz h4
    · exact killTrip C 2 (Or.inr (Or.inl rfl)) hfan hsz h4
    · exact killTrip C 3 (Or.inr (Or.inr (Or.inl rfl))) hfan hsz h4
    · exact hk4 rfl
    · refine killTrip (permCirc C) 1 (Or.inl rfl) (perm_fan C hfan) (perm_sz C hsz) ?_
      intro x
      rw [perm_eval C x [false, x 0 || x 4 || x 1] rfl]
      exact (h4 (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i))).trans
        (hF_perm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8))
    · exact killTrip C 6 (Or.inr (Or.inr (Or.inr rfl))) hfan hsz h4
    · refine killTrip (permCirc C) 6 (Or.inr (Or.inr (Or.inr rfl))) (perm_fan C hfan) (perm_sz C hsz) ?_
      intro x
      rw [perm_eval C x [false, x 0 || x 4 || x 6] rfl]
      exact (h4 (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i))).trans
        (hF_perm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8))
    · refine killTrip (permCirc C) 2 (Or.inr (Or.inl rfl)) (perm_fan C hfan) (perm_sz C hsz) ?_
      intro x
      rw [perm_eval C x [false, x 0 || x 4 || x 2] rfl]
      exact (h4 (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i))).trans
        (hF_perm (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8))
