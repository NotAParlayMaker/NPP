import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1640

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

lemma getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

lemma foldl_step_getD_gate (G : List Gate) (w : List Bool) (idx : ℕ) (hidx : idx < G.length) :
    (G.foldl step w).getD (w.length + idx) false =
      (G[idx]).op.eval ((G[idx]).inputs.map fun i => ((G.take idx).foldl step w).getD i false) := by
  have hsplit : G = G.take idx ++ G[idx] :: G.drop (idx + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by
    simp only [step, List.length_append, List.length_singleton, foldl_step_length,
      List.length_take, Nat.min_eq_left hidx.le]
    omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by
    simp only [foldl_step_length, List.length_take, Nat.min_eq_left hidx.le]
    omega)]
  simp [foldl_step_length, Nat.min_eq_left hidx.le]

lemma foldl_take_getD (G : List Gate) (w : List Bool) (idx i : ℕ)
    (hi : i < ((G.take idx).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take idx).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop idx G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

lemma gate_value (G : List Gate) (w : List Bool) (idx : ℕ) (hidx : idx < G.length) :
    (G.foldl step w).getD (w.length + idx) false =
      (G[idx]).op.eval ((G[idx]).inputs.map fun i =>
        if i < w.length + idx then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w idx hidx]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take idx).foldl step w).length = w.length + idx := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left hidx.le]
  by_cases h : i < w.length + idx
  · rw [ite_eq_left h]
    exact (foldl_take_getD G w idx i (by rw [hlen]; exact h)).symm
  · rw [ite_eq_right h]
    exact getD_of_length_le _ _ (by rw [hlen]; omega)

lemma eval_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (v : Fin N) :
    Circuit.eval ⟨gates, (v : ℕ)⟩ (List.ofFn x) = x v := by
  unfold Circuit.eval
  rw [wires_eq, foldl_step_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma eval_big {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = false := by
  unfold Circuit.eval
  rw [wires_eq]
  apply getD_of_length_le
  rw [foldl_step_length, List.length_ofFn]
  exact hw

lemma eval_gate {N : ℕ} (gates : List Gate)
    (hlt : ∀ (i : Fin gates.length), ∀ e ∈ (gates.get i).inputs, e < N + (i : ℕ))
    (x : Fin N → Bool) (i : Fin gates.length) :
    Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn x) =
      (gates.get i).op.eval ((gates.get i).inputs.map fun e =>
        Circuit.eval ⟨gates, e⟩ (List.ofFn x)) := by
  unfold Circuit.eval
  simp only [wires_eq]
  have h := gate_value gates (List.ofFn x) i.val i.isLt
  rw [List.length_ofFn] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro e he
  have he_lt : e < N + (i : ℕ) := hlt i e he
  rw [ite_eq_left he_lt]

def OrReach (N : ℕ) (gates : List Gate) (start target : ℕ) : Prop :=
  ∀ S : Set ℕ, start ∈ S →
    (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = GateOp.or →
      ∀ e ∈ (gates.get i).inputs, e ∈ S) →
    target ∈ S

def RimCarry {N : ℕ} (L0 T0 : Finset (Fin N)) (gates : List Gate) (a : Fin gates.length) : Prop :=
  (gates.get a).op = GateOp.and ∧
  Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0))) = false ∧
  ∃ r2 ∈ L0 \ T0,
    Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0 ∨ v = r2))) = true

lemma walk {N : ℕ} (L0 T0 : Finset (Fin N)) (gates : List Gate) (ch : Fin gates.length → ℕ)
    (hG : ∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2)
    (hlt : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hch : ∀ a : Fin gates.length, RimCarry L0 T0 gates a →
      ch a ∈ (gates.get a).inputs ∧
      Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0))) = false)
    (r : Fin N) (hr : r ∈ L0 \ T0) :
    ∀ w : ℕ,
      Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0))) = false →
      Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0 ∨ v = r))) = true →
      OrReach N gates w (r : ℕ) ∨
        ∃ a : Fin gates.length, RimCarry L0 T0 gates a ∧ OrReach N gates (ch a) (r : ℕ) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwf hwt
    by_cases hwn : w < N
    · let v : Fin N := ⟨w, hwn⟩
      have hvf : Circuit.eval ⟨gates, (v : ℕ)⟩ (List.ofFn (fun u : Fin N => decide (u ∉ L0))) = false := hwf
      have hvt : Circuit.eval ⟨gates, (v : ℕ)⟩ (List.ofFn (fun u : Fin N => decide (u ∉ L0 ∨ u = r))) = true := hwt
      rw [eval_input] at hvf hvt
      have hvL : v ∈ L0 := by
        by_contra hnot
        exact Bool.false_ne_true (hvf.symm.trans (decide_eq_true hnot))
      rcases of_decide_eq_true hvt with hnot | hvr
      · exact False.elim (hnot hvL)
      · have hwr : w = (r : ℕ) := congrArg Fin.val hvr
        rw [hwr]
        exact Or.inl (fun _ hs _ => hs)
    · by_cases hwbig : N + gates.length ≤ w
      · rw [eval_big gates _ w hwbig] at hwt
        exact False.elim (Bool.false_ne_true hwt)
      · have hidx : w - N < gates.length := by omega
        let i : Fin gates.length := ⟨w - N, hidx⟩
        have hweq : w = N + (i : ℕ) := by dsimp [i]; omega
        rw [hweq] at hwf hwt ⊢
        obtain ⟨hop, _⟩ := hG (gates.get i) (List.get_mem gates i)
        rcases hop with hand | hor
        · have hrim : RimCarry L0 T0 gates i := ⟨hand, hwf, ⟨r, hr, hwt⟩⟩
          obtain ⟨hchin, hchf⟩ := hch i hrim
          have hch_lt : ch i < w := by rw [hweq]; exact hlt i (ch i) hchin
          have hcht : Circuit.eval ⟨gates, ch i⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0 ∨ v = r))) = true := by
            rw [eval_gate gates hlt _ i, hand] at hwt
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hwt
            exact hwt _ ⟨ch i, hchin, rfl⟩
          rcases ih (ch i) hch_lt hchf hcht with hreach | hex
          · exact Or.inr ⟨i, hrim, hreach⟩
          · exact Or.inr hex
        · rw [eval_gate gates hlt _ i, hor] at hwt
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwt
          obtain ⟨_, ⟨e, hein, rfl⟩, het⟩ := hwt
          have he_lt : e < w := by rw [hweq]; exact hlt i e hein
          have hef : Circuit.eval ⟨gates, e⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0))) = false := by
            rw [eval_gate gates hlt _ i, hor] at hwf
            simp only [GateOp.eval] at hwf
            by_contra hne
            have het0 : Circuit.eval ⟨gates, e⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0))) = true :=
              Bool.eq_true_of_ne_false hne
            have hany : ((gates.get i).inputs.map fun u =>
                Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L0)))).any id = true := by
              simp only [List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨e, hein, het0⟩, rfl⟩
            exact Bool.false_ne_true (hwf.symm.trans hany)
          rcases ih e he_lt hef het with hreach | hex
          · refine Or.inl (fun S hS hstep => hreach S ?_ hstep)
            exact hstep i hS hor e hein
          · exact Or.inr hex

end PEqualNP.Outside.L_meta_1640

theorem PEqualNP.Outside.L_meta_1640 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (ch : Fin gates.length → ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) →
    (∀ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) → ch a ∈ (gates.get a).inputs ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, ch a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) →
    (∀ r ∈ L i0 \ T0, (∀ S : Set ℕ, o ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S) ∨
      ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true) ∧ (∀ S : Set ℕ, ch a ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (r : ℕ) ∈ S)) ∧
    (∀ a : Fin gates.length, o = N + (a : ℕ) → (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧ ∃ r2 ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r2))) = true)) := by
  intro q m N L i0 T0 _ _ hmq _ hLcard _ _ hTsub hTcard gates o ch hG _ hlt hof hot hch
  refine ⟨fun r hr => PEqualNP.Outside.L_meta_1640.walk (L i0) T0 gates ch hG hlt hch r hr o hof (hot r hr), ?_⟩
  intro a hoa hand
  have hcard_sdiff : 0 < (L i0 \ T0).card := by
    have hs := Finset.card_sdiff_add_card_eq_card hTsub
    rw [hTcard, hLcard i0] at hs
    omega
  obtain ⟨r2, hr2⟩ := Finset.card_pos.mp hcard_sdiff
  exact ⟨hand, hoa ▸ hof, ⟨r2, hr2, hoa ▸ hot r2 hr2⟩⟩
