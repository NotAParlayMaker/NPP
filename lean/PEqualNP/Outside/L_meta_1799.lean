import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1799

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem pre : ∀ (gs : List Gate) (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl stp W).getD i false = W.getD i false := by
  intro gs
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    rw [List.foldl_cons, ih (stp W g) i (by simp [stp]; omega)]
    simp only [stp, getD_snoc]
    rw [if_neg (by omega)]

theorem gate_val : ∀ (gs : List Gate) (W : List Bool) (j : ℕ) (g : Gate), gs[j]? = some g →
    (∀ i ∈ g.inputs, i < W.length + j) →
    (gs.foldl stp W).getD (W.length + j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stp W).getD i false) := by
  intro gs
  induction gs with
  | nil => intro W j g h; simp at h
  | cons g0 gs ih =>
    intro W j g h hin
    rw [List.foldl_cons]
    cases j with
    | zero =>
      simp at h
      subst h
      have key : ∀ i ∈ g0.inputs,
          (gs.foldl stp (stp W g0)).getD i false = W.getD i false := by
        intro i hi
        have hi2 := hin i hi
        rw [pre _ _ _ (by simp [stp]; omega)]
        simp only [stp, getD_snoc]
        rw [if_neg (by omega)]
      rw [List.map_congr_left key, Nat.add_zero, pre _ _ _ (by simp [stp])]
      simp [stp, getD_snoc]
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      have := ih (stp W g0) j g h2 (by
        intro i hi
        have hi2 := hin i hi
        simp [stp]
        omega)
      have e : W.length + (j + 1) = (stp W g0).length + j := by
        simp [stp]
        omega
      rw [e]
      exact this

theorem ri_len (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

theorem ri_mono (P L : ℕ) (w : Fin L) (p1 p2 : Fin P → Bool)
    (h : ∀ p, p1 p = true → p2 p = true) (i : ℕ) :
    (restrictInput P L w p1).getD i false = true →
      (restrictInput P L w p2).getD i false = true := by
  unfold restrictInput
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_or_ge i P with hi | hi
  · rw [List.getElem?_append_left (by simpa using hi),
      List.getElem?_append_left (by simpa using hi)]
    rw [List.getElem?_eq_getElem (by simpa using hi),
      List.getElem?_eq_getElem (by simpa using hi)]
    simp only [List.getElem_ofFn, Option.getD_some]
    exact h _
  · rw [List.getElem?_append_right (by simpa using hi),
      List.getElem?_append_right (by simpa using hi)]
    simp only [List.length_ofFn]
    exact id

theorem main (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (hC : IsMonotoneCircuit C)
    (j a b : ℕ) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < P + L + j) (hb : b < P + L + j)
    (w : Fin L) (y : Fin P) (hlow : IsLow P L inc C (P + L + j) w)
    (hy : y ∈ aliveSet P L C (P + L + j) w) :
    (IsLow P L inc C a w ∧ y ∈ aliveSet P L C a w) ∨
      (IsLow P L inc C b w ∧ y ∈ aliveSet P L C b w) := by
  have gv : ∀ pts : Fin P → Bool, wireVal C (restrictInput P L w pts) (P + L + j) =
      op.eval [wireVal C (restrictInput P L w pts) a, wireVal C (restrictInput P L w pts) b] := by
    intro pts
    have := gate_val C.gates (restrictInput P L w pts) j _ hg (by
      intro i hi
      rw [ri_len]
      simp at hi
      rcases hi with rfl | rfl <;> assumption)
    rw [ri_len] at this
    exact this
  have mn : ∀ (p1 p2 : Fin P → Bool), (∀ p, p1 p = true → p2 p = true) → ∀ i,
      wireVal C (restrictInput P L w p1) i = true →
      wireVal C (restrictInput P L w p2) i = true := by
    intro p1 p2 h i
    exact mono C.gates _ _ (by rw [ri_len, ri_len]) hC (ri_mono P L w p1 p2 h) i
  have hy' : wireVal C (restrictInput P L w (fun q => decide (q = y))) (P + L + j) = true := by
    exact (Finset.mem_filter.mp hy).2
  have al : ∀ g, wireVal C (restrictInput P L w (fun q => decide (q = y))) g = true →
      y ∈ aliveSet P L C g w := by
    intro g h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [gv] at hy'
  rcases hop with rfl | rfl
  · simp [GateOp.eval] at hy'
    by_cases la : IsLow P L inc C a w
    · exact Or.inl ⟨la, al a hy'.1⟩
    · by_cases lb : IsLow P L inc C b w
      · exact Or.inr ⟨lb, al b hy'.2⟩
      · exfalso
        simp only [IsLow, not_forall] at la lb
        obtain ⟨p1, h1, n1⟩ := la
        obtain ⟨p2, h2, n2⟩ := lb
        have k1 := mn p1 (fun p => p1 p || p2 p) (fun p hp => by simp [hp]) a h1
        have k2 := mn p2 (fun p => p1 p || p2 p) (fun p hp => by simp [hp]) b h2
        have hh := hlow (fun p => p1 p || p2 p) (by
          rw [gv]
          simp [GateOp.eval, k1, k2])
        simp only [lineSum, decide_eq_true_eq] at hh n1 n2
        obtain ⟨p, hp, hq⟩ := hh
        rw [Bool.or_eq_true] at hq
        rcases hq with h | h
        · exact n1 ⟨p, hp, h⟩
        · exact n2 ⟨p, hp, h⟩
  · simp [GateOp.eval] at hy'
    have la : IsLow P L inc C a w := fun pts h => hlow pts (by
      rw [gv]
      simp [GateOp.eval, h])
    have lb : IsLow P L inc C b w := fun pts h => hlow pts (by
      rw [gv]
      simp [GateOp.eval, h])
    rcases hy' with h | h
    · exact Or.inl ⟨la, al a h⟩
    · exact Or.inr ⟨lb, al b h⟩

end PEqualNP.Outside.L_meta_1799

theorem PEqualNP.Outside.L_meta_1799 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp), (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) → C.gates[j]? = some ⟨op, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ (w : Fin L) (y : Fin P), PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → y ∈ PEqualNP.LowMerge.aliveSet P L C (P + L + j) w → (PEqualNP.LowMerge.IsLow P L inc C a w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C a w) ∨ (PEqualNP.LowMerge.IsLow P L inc C b w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C b w) := by
  intro P L inc C hC j a b op hop hg ha hb w y hlow hy
  exact PEqualNP.Outside.L_meta_1799.main P L inc C hC j a b op hop hg ha hb w y hlow hy
