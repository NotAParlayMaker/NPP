import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5685_2
    (hT : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 →
      x1.size ≤ (18 : ℕ) → ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
        have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;
        x1.eval (x7 ++ [Bool.true]) ≠ x6.2)
    (hE : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 →
      x1.size ≤ (18 : ℕ) → ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
        have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;
        x1.eval (x7 ++ [x6.1.testBit 0 && x6.1.testBit 1]) ≠ x6.2) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],           have x7 : List Bool := List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7;           x1.eval (x7 ++ [(List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x2).all id]) ≠ x6.2) := by
  intro C x2 hM hS hL
  have snoc : ∀ (u : List Bool) (b : Bool) (i : ℕ), (u ++ [b]).getD i false =
      if i < u.length then u.getD i false else if i = u.length then b else false := by
    intro u b i
    by_cases h1 : i < u.length
    · rw [if_pos h1, List.getD_append _ _ _ _ h1]
    · rw [if_neg h1, List.getD_append_right _ _ _ _ (by omega)]
      by_cases h2 : i = u.length
      · subst h2; simp
      · rw [if_neg h2]
        rw [List.getD_eq_default _ _ (by simp; omega)]
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ u u' : List Bool, u.length = u'.length →
      (∀ i, u.getD i false = true → u'.getD i false = true) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u').length ∧
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u').getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ u u' h1 h2; exact ⟨h1, h2⟩
    | cons g gs ih =>
      intro hops u u' h1 h2
      simp only [List.foldl_cons]
      have hb : g.op.eval (g.inputs.map fun i => u.getD i false) = true →
          g.op.eval (g.inputs.map fun i => u'.getD i false) = true := by
        rcases hops g (List.mem_cons_self ..) with hop | hop
        · rw [hop]; simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨j, hj, rfl⟩
          exact h2 j (hall _ ⟨j, hj, rfl⟩)
        · rw [hop]; simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨j, hj, rfl⟩, hv⟩
          exact ⟨_, ⟨j, hj, rfl⟩, h2 j hv⟩
      apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
      · simp [h1]
      · intro i
        rw [snoc, snoc, ← h1]
        split_ifs
        · exact h2 i
        · exact hb
        · exact id
  have mono : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (w w' : List Bool), w.length = w'.length →
      (∀ i, w.getD i false = true → w'.getD i false = true) →
      C.eval w = true → C.eval w' = true := by
    intro C hM w w' hl hle h
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h ⊢
    exact (key C.gates (fun g hg => by
      rcases (hM g hg).1 with hop | hop
      · exact Or.inl hop
      · exact Or.inr hop) w w' hl hle).2 _ h
  have hren : ∀ (ρ : ℕ → ℕ) (B : ℕ), (∀ i, 11 ≤ i → ρ i = i) →
      (∀ i, i < 11 → ρ i < 11 ∨ B ≤ ρ i) →
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool), w.length = w'.length →
        11 ≤ w.length → w.length + gs.length ≤ B →
        (∀ i, w'.getD (ρ i) false = w.getD i false) →
        ∀ i, ((gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (ρ i) false
          = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
              i false := by
    intro ρ B hρ hB gs
    induction gs with
    | nil => intro w w' _ _ _ h; simpa using h
    | cons g rest ih =>
      intro w w' hl h11 hlen h
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp; omega
      · simp at hlen ⊢; omega
      · have hv : g.op.eval ((g.inputs.map ρ).map fun i => w'.getD i false)
            = g.op.eval (g.inputs.map fun i => w.getD i false) := by
          rw [List.map_map]; congr 1; apply List.map_congr_left; intro i _; exact h i
        intro i
        rw [hv]
        rcases lt_trichotomy i w.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ hi]
          by_cases hi11 : i < 11
          · rcases hB i hi11 with h1 | h1
            · rw [List.getD_append _ _ _ _ (by omega)]; exact h i
            · have e1 : (w' ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD (ρ i)
                  false = false := List.getD_eq_default _ _ (by simp at hlen ⊢; omega)
              have e2 : w'.getD (ρ i) false = false :=
                List.getD_eq_default _ _ (by simp at hlen; omega)
              rw [e1, ← h i, e2]
          · rw [hρ i (by omega), List.getD_append _ _ _ _ (by omega)]
            have := h i; rwa [hρ i (by omega)] at this
        · subst hi
          rw [hρ _ h11, hl, List.getD_append_right _ _ _ _ le_rfl,
            List.getD_append_right _ _ _ _ (by omega)]
          simp [hl]
        · rw [hρ i (by omega), List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  let R : (ℕ → ℕ) → PEqualNP.CircuitLowerBounds.Circuit := fun σ =>
    ⟨C.gates.map fun g => ⟨g.op, g.inputs.map fun i => if i < 11 then σ i else i⟩,
      if C.output < 11 then σ C.output else C.output⟩
  have hRM : ∀ σ, PEqualNP.MetaComplexity.Monotone2 (R σ) := by
    intro σ g hg
    simp only [R, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hM g0 hg0
    exact ⟨h1, by simpa using h2⟩
  have hRS : ∀ σ, (R σ).size ≤ 18 := by
    intro σ
    simpa [R, PEqualNP.CircuitLowerBounds.Circuit.size] using hS
  have hRE : ∀ σ : ℕ → ℕ, (∀ i, i < 11 → σ i < 11 ∨ 11 + C.gates.length ≤ σ i) →
      ∀ x x' : List Bool, x.length = 11 → x'.length = 11 →
      (∀ i, i < 11 → x'.getD (σ i) false = x.getD i false) → (R σ).eval x' = C.eval x := by
    intro σ hσ x x' hx hx' hxx
    have := hren (fun i => if i < 11 then σ i else i) (11 + C.gates.length)
      (by intro i hi; simp; omega) (by intro i hi; simp [hi]; exact hσ i hi)
      C.gates x x' (by rw [hx, hx']) (by omega) (by omega)
      (by
        intro i
        by_cases hi : i < 11
        · simp only [hi, ite_true]; exact hxx i hi
        · simp only [hi, ite_false]
          rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
      C.output
    exact this
  have gb : ∀ (m : ℕ) (t : Bool) (i : ℕ),
      ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [t]).getD i false =
        if i < 10 then m.testBit i else if i = 10 then t else false := by
    intro m t i
    by_cases h : i < 10
    · rw [List.getD_append _ _ _ _ (by simpa using h), if_pos h,
        List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    · rw [if_neg h]
      by_cases h' : i = 10
      · subst h'; simp
      · rw [if_neg h', List.getD_eq_default _ _ (by simp; omega)]
  have gb0 : ∀ (m : ℕ) (i : ℕ), (List.ofFn fun k : Fin 10 => m.testBit ↑k).getD i false =
      if i < 10 then m.testBit i else false := by
    intro m i
    by_cases h : i < 10
    · rw [if_pos h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    · rw [if_neg h, List.getD_eq_default _ _ (by simp; omega)]
  have hlen : ∀ (m : ℕ) (t : Bool), ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [t]).length = 11 := by
    intro m t; simp
  have hcase : (∃ s, (s ≤ 10 ∨ 11 + C.gates.length ≤ s) ∧ ∀ m : ℕ,
        (List.map (fun x8 => (List.ofFn fun k : Fin 10 => m.testBit ↑k).getD x8 false) x2).all id
          = ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [true]).getD s false) ∨
      (∃ a b, a < 10 ∧ b < 10 ∧ a ≠ b ∧ ∀ m : ℕ,
        (List.map (fun x8 => (List.ofFn fun k : Fin 10 => m.testBit ↑k).getD x8 false) x2).all id
          = (m.testBit a && m.testBit b)) := by
    have n1 : ¬ (11 + C.gates.length < 10) := by omega
    have n2 : ¬ (11 + C.gates.length = 10) := by omega
    rcases x2 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · left; exact ⟨10, by omega, fun m => by simp [gb]⟩
    · left
      by_cases ha : a < 10
      · exact ⟨a, by omega, fun m => by simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, gb, gb0]; simp [gb, gb0, ha]⟩
      · exact ⟨11 + C.gates.length, by omega, fun m => by simp [gb, gb0, ha, n1, n2]⟩
    · by_cases ha : a < 10
      · by_cases hb : b < 10
        · by_cases hab : a = b
          · subst hab
            left; exact ⟨a, by omega, fun m => by simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, gb, gb0]; simp [gb, gb0, ha]⟩
          · right; exact ⟨a, b, ha, hb, hab, fun m => by simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, gb, gb0]; simp [gb0, ha, hb]⟩
        · left
          exact ⟨11 + C.gates.length, by omega, fun m => by simp [gb, gb0, hb, n1, n2]⟩
      · left
        exact ⟨11 + C.gates.length, by omega, fun m => by simp [gb, gb0, ha, n1, n2]⟩
    · simp at hL
  rcases hcase with ⟨s, hs, hy⟩ | ⟨a, b, ha, hb, hab, hy⟩
  ·
    have hσ : ∀ i, i < 11 → (fun i => if i = 10 then s else i) i < 11 ∨
        11 + C.gates.length ≤ (fun i => if i = 10 then s else i) i := by
      intro i hi
      by_cases h : i = 10
      · simp only [h, ite_true]; omega
      · simp only [h, ite_false]; omega
    obtain ⟨⟨m, e⟩, hm, hne⟩ := hT (R fun i => if i = 10 then s else i) (hRM _) (hRS _)
    refine ⟨(m, e), hm, ?_⟩
    dsimp only at hne ⊢
    rw [← hRE _ hσ _ _ (hlen m _) (hlen m true) ?_]
    · exact hne
    · intro i hi
      by_cases h : i = 10
      · subst h; simp only [ite_true]; rw [← hy m, gb]; simp
      · simp only [h, ite_false]; rw [gb, gb]; simp [h]
  ·
    have hB : ((List.range 10).all fun a => (List.range 10).all fun b => a == b ||
        ([((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)] : List (ℕ × Bool)).all (fun q => decide (q.2 = true → (q.1.testBit a && q.1.testBit b) = false)) ||
        (([(0, 1, 1, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]), (0, 4, 1, [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]), (0, 5, 1, [0, 4, 3, 8, 5, 1, 9, 2, 6, 7]), (1, 0, 1, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]), (1, 2, 1, [4, 0, 1, 2, 3, 9, 5, 6, 7, 8]), (1, 6, 1, [4, 0, 5, 7, 9, 3, 1, 8, 2, 6]), (2, 1, 1, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]), (2, 3, 1, [3, 4, 0, 1, 2, 8, 9, 5, 6, 7]), (2, 7, 1, [3, 4, 0, 5, 8, 2, 9, 1, 7, 6]), (3, 2, 1, [3, 2, 1, 0, 4, 8, 7, 6, 5, 9]), (3, 4, 1, [2, 3, 4, 0, 1, 7, 8, 9, 5, 6]), (3, 8, 1, [3, 8, 5, 0, 4, 2, 6, 7, 1, 9]), (4, 0, 1, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5]), (4, 3, 1, [4, 3, 2, 1, 0, 9, 8, 7, 6, 5]), (4, 9, 1, [4, 3, 8, 5, 0, 9, 2, 6, 7, 1])] ++ [(5, 0, 1, [1, 2, 3, 8, 6, 0, 7, 4, 5, 9]), (5, 7, 1, [4, 3, 2, 7, 9, 0, 8, 1, 5, 6]), (5, 8, 1, [4, 3, 8, 6, 9, 0, 2, 5, 1, 7]), (6, 1, 1, [2, 1, 6, 8, 3, 7, 0, 9, 5, 4]), (6, 8, 1, [3, 4, 9, 6, 8, 2, 0, 7, 1, 5]), (6, 9, 1, [3, 4, 9, 7, 2, 8, 0, 6, 5, 1]), (7, 2, 1, [3, 2, 1, 6, 8, 4, 7, 0, 9, 5]), (7, 5, 1, [2, 3, 4, 9, 7, 1, 8, 0, 6, 5]), (7, 9, 1, [3, 8, 5, 7, 2, 4, 6, 0, 9, 1]), (8, 3, 1, [3, 8, 6, 1, 2, 4, 5, 9, 0, 7]), (8, 5, 1, [2, 3, 8, 5, 7, 1, 4, 6, 0, 9]), (8, 6, 1, [3, 2, 7, 5, 8, 4, 1, 9, 0, 6]), (9, 4, 1, [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]), (9, 6, 1, [3, 2, 7, 9, 4, 8, 1, 5, 6, 0]), (9, 7, 1, [3, 8, 6, 9, 4, 2, 5, 1, 7, 0])] : List (ℕ × ℕ × ℕ × List ℕ))).any fun p => p.1 == a && p.2.1 == b &&
        p.2.2.1 == 1 && p.2.2.2.getD a 0 == 0 &&
        p.2.2.2.getD b 0 == p.2.2.1 && (List.range 10).all (fun i => decide (p.2.2.2.getD i 0 < 10)) &&
        ([((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)] : List (ℕ × Bool)).all fun q =>
          decide ((((List.range 10).map fun i =>
              if q.1.testBit (p.2.2.2.getD i 0) then 2 ^ i else 0).sum, q.2) ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)]) &&
          (List.range 10).all fun i => (((List.range 10).map fun i =>
              if q.1.testBit (p.2.2.2.getD i 0) then 2 ^ i else 0).sum).testBit i ==
            q.1.testBit (p.2.2.2.getD i 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc, or_assoc] at hB
    rcases (hB a ha b hb).resolve_left hab with hq | ⟨⟨a', b', c, π⟩, -, -, -, hc, hpa, hpb, hp10, hpts⟩
    ·
      have hσ : ∀ i, i < 11 → (fun i => if i = 10 then 11 + C.gates.length else i) i < 11 ∨
          11 + C.gates.length ≤ (fun i => if i = 10 then 11 + C.gates.length else i) i := by
        intro i hi
        by_cases h : i = 10
        · simp only [h, ite_true]; omega
        · simp only [h, ite_false]; omega
      obtain ⟨⟨m, e⟩, hm, hne⟩ := hT (R fun i => if i = 10 then 11 + C.gates.length else i)
        (hRM _) (hRS _)
      dsimp only at hne
      have hF : (R fun i => if i = 10 then 11 + C.gates.length else i).eval
          ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [true]) =
          C.eval ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [false]) := by
        apply hRE _ hσ _ _ (hlen m _) (hlen m true)
        intro i hi
        by_cases h : i = 10
        · subst h; simp only [ite_true]; rw [gb, gb]; simp
          rw [if_neg (show ¬ (11 + C.gates.length < 10) by omega)]; omega
        · simp only [h, ite_false]; rw [gb, gb]; simp [h]
      rw [hF] at hne
      have hq1 := hq (m, e) hm
      dsimp only at hq1
      refine ⟨(m, e), hm, ?_⟩
      dsimp only
      rw [hy m]
      cases he : e with
      | true =>
        rw [he] at hne hq1
        rw [hq1 rfl]; exact hne
      | false =>
        rw [he] at hne
        have ht : C.eval ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [false]) = true := by
          simpa using hne
        have := mono C hM ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [false])
          ((List.ofFn fun k : Fin 10 => m.testBit ↑k) ++ [m.testBit a && m.testBit b])
          (by simp) (by
            intro i hi
            rw [gb] at hi ⊢
            by_cases h1 : i < 10
            · rw [if_pos h1] at hi ⊢; exact hi
            · rw [if_neg h1] at hi ⊢
              by_cases h2 : i = 10
              · rw [if_pos h2] at hi; exact absurd hi Bool.false_ne_true
              · rw [if_neg h2] at hi; exact absurd hi Bool.false_ne_true) ht
        rw [this]; decide
    dsimp only at hc hpa hpb hp10 hpts
    have hEN : ∃ x6 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
        (R fun i => if i < 10 then π.getD i 0 else i).eval
          ((List.ofFn fun (x7 : Fin (10 : ℕ)) => x6.1.testBit ↑x7) ++
            [x6.1.testBit 0 && x6.1.testBit c]) ≠ x6.2 := by
      subst hc
      exact hE _ (hRM _) (hRS _)
    obtain ⟨⟨m', e⟩, hm', hne⟩ := hEN
    obtain ⟨hmem, hbits⟩ := hpts (m', e) hm'
    dsimp only at hmem hbits hne
    refine ⟨_, hmem, ?_⟩
    dsimp only
    have hσ : ∀ i, i < 11 → (fun i => if i < 10 then π.getD i 0 else i) i < 11 ∨
        11 + C.gates.length ≤ (fun i => if i < 10 then π.getD i 0 else i) i := by
      intro i hi
      left
      by_cases h : i < 10
      · simp only [h, ite_true]; have := hp10 i h; omega
      · simp only [h, ite_false]; omega
    rw [← hRE _ hσ _ _ (hlen _ _) (hlen m' _) ?_]
    · exact hne
    · intro i hi
      by_cases h : i < 10
      · simp only [h, ite_true]
        rw [gb, gb, if_pos (hp10 i h), if_pos h, hbits i h]
      · have h10 : i = 10 := by omega
        subst h10
        simp only [ite_false, show ¬ (10 < 10) from by omega]
        rw [gb, gb, hy, if_neg (by omega), if_pos rfl, if_neg (by omega), if_pos rfl,
          hbits a ha, hbits b hb, hpa, hpb]
