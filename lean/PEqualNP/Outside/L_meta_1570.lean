import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1570

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma pair_separates : ∀ t : Fin 13, t ≠ 0 →
    (0 ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))) ∨
    (1 ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13))) := by decide

lemma line_separates : ∀ t : Fin 13, t ≠ 0 →
    ∃ v ∈ ({0, 1, 3, 9} : Finset (Fin 13)),
      v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by decide


end PEqualNP.Outside.L_meta_1570

open PEqualNP.Outside.L_meta_1570 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1570 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    13 ≤ o 0 ∧ o 0 < 13 + gates.length ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true ∧
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ ∀ t : Fin 13, t ≠ 0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true := by
  intro L hL gates o hAO hback hfun
  have h0 : Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 0))) = true := by
    have h := hfun 0 (fun v : Fin 13 => decide (v = 0)) (Or.inl (by decide))
    simpa [hL 0] using h
  have h1 : Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v = 1))) = true := by
    have h := hfun 0 (fun v : Fin 13 => decide (v = 1)) (Or.inr (Or.inl (by decide)))
    simpa [hL 0] using h
  have hlo : 13 ≤ o 0 := by
    by_contra hh
    have hw : o 0 < 13 := by omega
    let a : Fin 13 := ⟨o 0, hw⟩
    have ha0 : a = 0 := by
      apply of_decide_eq_true
      change val ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) a.val = true at h0
      rwa [val_ofFn] at h0
    have ha1 : a = 1 := by
      apply of_decide_eq_true
      change val ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 1))) a.val = true at h1
      rwa [val_ofFn] at h1
    exact (by decide : (0 : Fin 13) ≠ 1) (ha0.symm.trans ha1)
  have hhi : o 0 < 13 + gates.length := by
    by_contra hh
    have hf := val_ge (n := 13) (C := ⟨gates, o 0⟩)
      (x := List.ofFn (fun v : Fin 13 => decide (v = 0))) (by simp)
      (u := o 0) (le_of_not_gt hh)
    change val ⟨gates, o 0⟩ (List.ofFn (fun v : Fin 13 => decide (v = 0))) (o 0) = true at h0
    rw [hf] at h0
    cases h0
  have hc0 : Circuit.eval ⟨gates, o 0⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false := by
    have h := hfun 0 (fun v : Fin 13 => decide (v ∉ L 0))
      (Or.inr (Or.inr (by intro v hv; simp [hv])))
    simpa using h
  refine ⟨hlo, hhi, h0, h1, hc0, ?_⟩
  intro t ht
  have hdom : decide ((0 : Fin 13) ∉ L t) = true ∨
      decide ((1 : Fin 13) ∉ L t) = true ∨
      ∀ v : Fin 13, v ∉ L 0 → decide (v ∉ L t) = true := by
    rcases pair_separates t ht with hp | hp
    · left
      have hnot : (0 : Fin 13) ∉ L t := by simpa only [hL t] using hp
      simp [hnot]
    · right; left
      have hnot : (1 : Fin 13) ∉ L t := by simpa only [hL t] using hp
      simp [hnot]
  have h := hfun 0 (fun v : Fin 13 => decide (v ∉ L t)) hdom
  have hex : ∃ v ∈ L 0, decide (v ∉ L t) = true := by
    obtain ⟨v, hv0, hvt⟩ := line_separates t ht
    refine ⟨v, ?_, ?_⟩
    · simpa [hL 0] using hv0
    · have hnot : v ∉ L t := by simpa only [hL t] using hvt
      simp [hnot]
  exact h.trans (by simpa only [decide_eq_true_eq] using hex)
