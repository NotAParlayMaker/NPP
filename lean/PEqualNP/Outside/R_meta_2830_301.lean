import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2830_301
    (h1 : ∀ (C : Circuit), Monotone2 C →
      (∃ g, C.gates[0]? = some g ∧ g.op = GateOp.and ∧
        ∀ a b, g.inputs = [a, b] → a ≤ b ∧
          (a < min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∨
           (a = min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∧
            b ≤ max (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b)))) →
      (∀ m ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = true) →
      (∀ m ∈ [(42 : ℕ), 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = false) →
      15 ≤ C.size)
    (h2 : ∀ (C : Circuit), Monotone2 C →
      (∃ g, C.gates[0]? = some g ∧ g.op = GateOp.or ∧
        ∀ a b, g.inputs = [a, b] → a ≤ b ∧ a = 0 ∧ b ≤ 4 ∧
          (a < min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∨
           (a = min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∧
            b ≤ max (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b)))) →
      (∀ m ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = true) →
      (∀ m ∈ [(42 : ℕ), 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = false) →
      15 ≤ C.size)
    (h3 : ∀ (C : Circuit), Monotone2 C →
      (∃ g, C.gates[0]? = some g ∧ g.op = GateOp.or ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≤ b ∧ a = 2 ∧
          (a < min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∨
           (a = min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∧
            b ≤ max (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b)))) →
      (∀ m ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = true) →
      (∀ m ∈ [(42 : ℕ), 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = false) →
      15 ≤ C.size)
    (h4 : ∀ (C : Circuit), Monotone2 C →
      (∃ g, C.gates[0]? = some g ∧ g.op = GateOp.or ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≤ b ∧ ((a = 0 ∧ 5 ≤ b) ∨ a = 1 ∨ 3 ≤ a) ∧
          (a < min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∨
           (a = min (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b) ∧
            b ≤ max (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] a a) (List.getD [1, 0, 5, 8, 6, 2, 4, 7, 3] b b)))) →
      (∀ m ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = true) →
      (∀ m ∈ [(42 : ℕ), 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402],
        C.eval ((List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]) = false) →
      15 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → (15 : ℕ) ≤ x1.size := by
  intro C hmono hyes hno
  let sig : List ℕ := [1, 0, 5, 8, 6, 2, 4, 7, 3]
  let s (j : ℕ) : ℕ := List.getD sig j j
  let posL : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
  let negL : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
  let inp (m : ℕ) : List Bool := (List.ofFn fun i : Fin 9 => m.testBit ↑i) ++ [m.testBit 0 || m.testBit 1]
  let step (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩
  have hsz_eq : ∀ D : Circuit, D.size = D.gates.length := fun _ => rfl
  have hev_eq : ∀ (D : Circuit) (x : List Bool), D.eval x = (D.gates.foldl step x).getD D.output false := fun _ _ => rfl
  have hlt : ∀ j < 9, s j < 9 := fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp (show (List.range 9).all (fun i => decide (s i < 9)) = true from by decide +kernel) j (List.mem_range.mpr hj))
  have hge : ∀ j, 9 ≤ j → s j = j := by
    intro j hj; dsimp only [s, sig]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
  have hinv9 : ∀ j < 9, s (s j) = j := fun j hj =>
    of_decide_eq_true (List.all_eq_true.mp (show (List.range 9).all (fun i => decide (s (s i) = i)) = true from by decide +kernel) j (List.mem_range.mpr hj))
  have hinv : ∀ j, s (s j) = j := by
    intro j
    by_cases hj : j < 9
    · exact hinv9 j hj
    · rw [hge j (by omega), hge j (by omega)]
  have hand_swap : ∀ (x y : Bool), GateOp.and.eval [x, y] = GateOp.and.eval [y, x] := by
    intro x y; cases x <;> cases y <;> rfl
  have hor_swap : ∀ (x y : Bool), GateOp.or.eval [x, y] = GateOp.or.eval [y, x] := by
    intro x y; cases x <;> cases y <;> rfl
  have hpre : ∀ (gs : List Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j, W'.getD (s j) false = W.getD j false) →
      ∀ j, ((gs.map mapGate).foldl step W').getD (s j) false = (gs.foldl step W).getD j false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ hW j; exact hW j
    | cons g gs ih =>
      intro W W' hlen h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · have hev : (mapGate g).op.eval ((mapGate g).inputs.map fun i => W'.getD i false) =
            g.op.eval (g.inputs.map fun i => W.getD i false) := by
          dsimp only [mapGate]
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        dsimp only [step]
        rw [hev]
        generalize g.op.eval (g.inputs.map fun i => W.getD i false) = v
        by_cases hj : j < W.length
        · have hj' : s j < W'.length := by
            by_cases h9j : j < 9
            · have := hlt j h9j; omega
            · rw [hge j (by omega)]; omega
          have hWj := hW j
          generalize s j = r at hj' hWj ⊢
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left hj', List.getElem?_append_left hj]
          simpa only [List.getD_eq_getElem?_getD] using hWj
        · rw [hge j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hlen,
                List.getElem?_append_right (le_refl _), ← hlen,
                List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  let permMask (m : ℕ) : ℕ :=
    (if m.testBit 0 then 2 else 0) ||| (if m.testBit 1 then 1 else 0) |||
    (if m.testBit 2 then 32 else 0) ||| (if m.testBit 3 then 256 else 0) |||
    (if m.testBit 4 then 64 else 0) ||| (if m.testBit 5 then 4 else 0) |||
    (if m.testBit 6 then 16 else 0) ||| (if m.testBit 7 then 128 else 0) |||
    (if m.testBit 8 then 8 else 0)
  have hpos_perm : ∀ m ∈ posL, permMask m ∈ posL ∧ ∀ j < 10, (inp m).getD (s j) false = (inp (permMask m)).getD j false := by
    intro m hm
    have hall : posL.all (fun m => decide (permMask m ∈ posL) &&
        (List.range 10).all (fun j => (inp m).getD (s j) false == (inp (permMask m)).getD j false)) = true := by
      decide +kernel
    have h1 := List.all_eq_true.mp hall m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h1
    exact h1
  have hneg_perm : ∀ m ∈ negL, permMask m ∈ negL ∧ ∀ j < 10, (inp m).getD (s j) false = (inp (permMask m)).getD j false := by
    intro m hm
    have hall : negL.all (fun m => decide (permMask m ∈ negL) &&
        (List.range 10).all (fun j => (inp m).getD (s j) false == (inp (permMask m)).getD j false)) = true := by
      decide +kernel
    have h1 := List.all_eq_true.mp hall m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h1
    exact h1
  have hdispatch : ∀ D : Circuit, Monotone2 D →
      (∃ g, D.gates[0]? = some g ∧
        ∀ a b, g.inputs = [a, b] → a ≤ b ∧
          (a < min (s a) (s b) ∨ (a = min (s a) (s b) ∧ b ≤ max (s a) (s b)))) →
      (∀ m ∈ posL, D.eval (inp m) = true) →
      (∀ m ∈ negL, D.eval (inp m) = false) →
      15 ≤ D.size := by
    intro D hDm hex hDy hDn
    rcases hex with ⟨g, hg0, hgc⟩
    have hgm := hDm g (List.mem_of_getElem? hg0)
    rcases hgm.1 with hop | hop
    · exact h1 D hDm ⟨g, hg0, hop, hgc⟩ hDy hDn
    · cases hins : g.inputs with
      | nil => exact h2 D hDm ⟨g, hg0, hop, fun _ _ h => by simp [hins] at h⟩ hDy hDn
      | cons a t =>
        cases t with
        | nil => exact h2 D hDm ⟨g, hg0, hop, fun _ _ h => by simp [hins] at h⟩ hDy hDn
        | cons b t2 =>
          cases t2 with
          | nil =>
            have hgab := hgc a b hins
            by_cases ha0 : a = 0
            · by_cases hb4 : b ≤ 4
              · exact h2 D hDm ⟨g, hg0, hop, fun a' b' h => by rw [hins] at h; injection h with h1' h2'; injection h2' with h3' _; subst h1' h3'; exact ⟨hgab.1, ha0, hb4, hgab.2⟩⟩ hDy hDn
              · exact h4 D hDm ⟨g, hg0, hop, a, b, hins, hgab.1, Or.inl ⟨ha0, by omega⟩, hgab.2⟩ hDy hDn
            · by_cases ha2 : a = 2
              · exact h3 D hDm ⟨g, hg0, hop, a, b, hins, hgab.1, ha2, hgab.2⟩ hDy hDn
              · exact h4 D hDm ⟨g, hg0, hop, a, b, hins, hgab.1, by omega, hgab.2⟩ hDy hDn
          | cons c t3 => exact h2 D hDm ⟨g, hg0, hop, fun _ _ h => by simp [hins] at h⟩ hDy hDn
  have hswap_step : ∀ (op : GateOp) (x y : ℕ) (w : List Bool), (op = GateOp.and ∨ op = GateOp.or) →
      step w ⟨op, [y, x]⟩ = step w ⟨op, [x, y]⟩ := by
    intro op x y w hop
    simp only [step, List.map_cons, List.map_nil]
    rcases hop with rfl | rfl
    · rw [hand_swap]
    · rw [hor_swap]
  rcases C with ⟨gates, out⟩
  cases gates with
  | nil =>
    exfalso
    by_cases ho : out < 10
    · have hbad : (List.range 10).all (fun o =>
          posL.any (fun m => !(inp m).getD o false) || negL.any (fun m => (inp m).getD o false)) = true := by
        decide +kernel
      have h1 := List.all_eq_true.mp hbad out (List.mem_range.mpr ho)
      simp only [Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h1
      rcases h1 with ⟨m, hm, hmf⟩ | ⟨m, hm, hmt⟩
      · have := hyes m hm; rw [hev_eq] at this; simp only [List.foldl_nil] at this; rw [hmf] at this; exact Bool.noConfusion this
      · have := hno m hm; rw [hev_eq] at this; simp only [List.foldl_nil] at this; rw [hmt] at this; exact Bool.noConfusion this
    · have h3 := hyes 3 (by simp)
      rw [hev_eq] at h3; simp only [List.foldl_nil] at h3
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at h3
      exact Bool.noConfusion h3
  | cons g gs =>
    have hgm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := hmono g (by simp)
    rcases g with ⟨op, ins⟩
    cases ins with
    | nil => exact hdispatch ⟨⟨op, []⟩ :: gs, out⟩ hmono ⟨⟨op, []⟩, by simp, fun _ _ h => by cases h⟩ hyes hno
    | cons a0 t =>
      cases t with
      | nil => exact hdispatch ⟨⟨op, [a0]⟩ :: gs, out⟩ hmono ⟨⟨op, [a0]⟩, by simp, fun _ _ h => by cases h⟩ hyes hno
      | cons b0 t2 =>
        cases t2 with
        | cons c0 t3 => exact hdispatch ⟨⟨op, a0 :: b0 :: c0 :: t3⟩ :: gs, out⟩ hmono ⟨⟨op, a0 :: b0 :: c0 :: t3⟩, by simp, fun _ _ h => by cases h⟩ hyes hno
        | nil =>
          have hpair : ∀ (a b : ℕ) (D : Circuit),
              D = ⟨⟨op, [a, b]⟩ :: gs, out⟩ → a ≤ b → Monotone2 D →
              (∀ m ∈ posL, D.eval (inp m) = true) → (∀ m ∈ negL, D.eval (inp m) = false) →
              15 ≤ D.size := by
            intro a b D hDeq hab hDm hDy hDn
            subst hDeq
            by_cases hcan : a < min (s a) (s b) ∨ (a = min (s a) (s b) ∧ b ≤ max (s a) (s b))
            · exact hdispatch _ hDm ⟨⟨op, [a, b]⟩, by simp, fun x y h => by injection h with hx ht; injection ht with hy _; subst hx hy; exact ⟨hab, hcan⟩⟩ hDy hDn
            · have hmap_canon : ∀ (x y : ℕ), x ≤ y →
                  (x = s a ∧ y = s b ∨ x = s b ∧ y = s a) →
                  let C2 : Circuit := ⟨⟨op, [x, y]⟩ :: gs.map mapGate, s out⟩
                  (∀ m ∈ posL, C2.eval (inp m) = true) ∧ (∀ m ∈ negL, C2.eval (inp m) = false) ∧
                  Monotone2 C2 ∧ C2.size = (⟨⟨op, [a, b]⟩ :: gs, out⟩ : Circuit).size ∧
                  (x < min (s x) (s y) ∨ (x = min (s x) (s y) ∧ y ≤ max (s x) (s y))) := by
                intro x y hxy hcase
                refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · intro m hm
                  obtain ⟨hpm, hjm⟩ := hpos_perm m hm
                  rw [hev_eq]
                  simp only [List.foldl_cons]
                  have hsw : step (inp m) ⟨op, [x, y]⟩ = step (inp m) (mapGate ⟨op, [a, b]⟩) := by
                    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact hswap_step op (s a) (s b) (inp m) hgm.1
                  rw [hsw]
                  have hp := hpre (⟨op, [a, b]⟩ :: gs) (inp (permMask m)) (inp m) (by simp [inp]) (by simp [inp]) (fun j => by
                    by_cases hj10 : j < 10
                    · exact hjm j hj10
                    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                          List.getElem?_eq_none (by simp [inp]; omega), List.getElem?_eq_none (by simp [inp]; omega)]) out
                  simp only [List.map_cons, List.foldl_cons] at hp
                  rw [hp]; exact hDy _ hpm
                · intro m hm
                  obtain ⟨hpm, hjm⟩ := hneg_perm m hm
                  rw [hev_eq]
                  simp only [List.foldl_cons]
                  have hsw : step (inp m) ⟨op, [x, y]⟩ = step (inp m) (mapGate ⟨op, [a, b]⟩) := by
                    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · rfl
                    · exact hswap_step op (s a) (s b) (inp m) hgm.1
                  rw [hsw]
                  have hp := hpre (⟨op, [a, b]⟩ :: gs) (inp (permMask m)) (inp m) (by simp [inp]) (by simp [inp]) (fun j => by
                    by_cases hj10 : j < 10
                    · exact hjm j hj10
                    · rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                          List.getElem?_eq_none (by simp [inp]; omega), List.getElem?_eq_none (by simp [inp]; omega)]) out
                  simp only [List.map_cons, List.foldl_cons] at hp
                  rw [hp]; exact hDn _ hpm
                · intro q hq
                  simp only [List.mem_cons, List.mem_map] at hq
                  rcases hq with rfl | ⟨q0, hq0, rfl⟩
                  · exact ⟨hgm.1, by simp⟩
                  · exact ⟨(hDm q0 (by simp [hq0])).1, by simpa [mapGate] using (hDm q0 (by simp [hq0])).2⟩
                · rw [hsz_eq, hsz_eq]; simp
                · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · rw [hinv a, hinv b, min_eq_left hab, max_eq_right hab]
                    rw [min_eq_left hxy, max_eq_right hxy] at hcan; omega
                  · rw [hinv a, hinv b, min_eq_right hab, max_eq_left hab]
                    rw [min_eq_right hxy, max_eq_left hxy] at hcan; omega
              by_cases hsab : s a ≤ s b
              · obtain ⟨hy2, hn2, hm2, hsz2, hcan2⟩ := hmap_canon (s a) (s b) hsab (Or.inl ⟨rfl, rfl⟩)
                rw [← hsz2]
                exact hdispatch _ hm2 ⟨⟨op, [s a, s b]⟩, by simp, fun x y h => by injection h with hx ht; injection ht with hy _; subst hx hy; exact ⟨hsab, hcan2⟩⟩ hy2 hn2
              · obtain ⟨hy2, hn2, hm2, hsz2, hcan2⟩ := hmap_canon (s b) (s a) (by omega) (Or.inr ⟨rfl, rfl⟩)
                rw [← hsz2]
                exact hdispatch _ hm2 ⟨⟨op, [s b, s a]⟩, by simp, fun x y h => by injection h with hx ht; injection ht with hy _; subst hx hy; exact ⟨by omega, hcan2⟩⟩ hy2 hn2
          by_cases hab0 : a0 ≤ b0
          · exact hpair a0 b0 _ rfl hab0 hmono hyes hno
          · have hsz1 : (⟨⟨op, [b0, a0]⟩ :: gs, out⟩ : Circuit).size = (⟨⟨op, [a0, b0]⟩ :: gs, out⟩ : Circuit).size := by
              rw [hsz_eq, hsz_eq]; rfl
            rw [← hsz1]
            apply hpair b0 a0 _ rfl (by omega)
            · intro q hq; simp only [List.mem_cons] at hq
              rcases hq with rfl | hq
              · exact ⟨hgm.1, by simp⟩
              · exact hmono q (by simp [hq])
            · intro m hm; rw [hev_eq]; simp only [List.foldl_cons]; rw [hswap_step op a0 b0 (inp m) hgm.1, ← List.foldl_cons]; exact hyes m hm
            · intro m hm; rw [hev_eq]; simp only [List.foldl_cons]; rw [hswap_step op a0 b0 (inp m) hgm.1, ← List.foldl_cons]; exact hno m hm
