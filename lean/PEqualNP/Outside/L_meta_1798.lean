import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1798_aux

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

theorem getD_snoc (u : List Bool) (b : Bool) (i : ℕ) :
    (u ++ [b]).getD i false = if i < u.length then u.getD i false else if i = u.length then b else false := by
  rcases lt_trichotomy i u.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < u.length := by omega
    have h2 : i ≠ u.length := by omega
    simp only [h1, h2, ite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_len (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [ih, F]; omega

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, w <+: gs.foldl F w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    exact (List.prefix_append w _).trans (ih _)

theorem getD_prefix {u v : List Bool} (h : u <+: v) {i : ℕ} (hi : i < u.length) :
    v.getD i false = u.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hfg : ∀ i, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    intro h x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hfg i (h (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, hfg i hx⟩

theorem fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ u v : List Bool, u.length = v.length → (∀ i, u.getD i false = true → v.getD i false = true) →
      ∀ i, (gs.foldl F u).getD i false = true → (gs.foldl F v).getD i false = true := by
  induction gs with
  | nil => intro u v _ h; simpa using h
  | cons g gs ih =>
    intro u v hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [F, hl]
    · intro i
      simp only [F, getD_snoc, hl]
      split_ifs with h1 h2
      · rw [← hl] at h1; exact h i
      · exact eval_mono g.op (hg g List.mem_cons_self) g.inputs _ _ h
      · simp

theorem restrict_mono (P L : ℕ) (w : Fin L) (p1 p2 : Fin P → Bool) (h : ∀ p, p1 p = true → p2 p = true) :
    ∀ i, (PEqualNP.LowMerge.restrictInput P L w p1).getD i false = true →
      (PEqualNP.LowMerge.restrictInput P L w p2).getD i false = true := by
  intro i
  simp only [PEqualNP.LowMerge.restrictInput, List.getD_eq_getElem?_getD]
  by_cases hi : i < P
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by simpa using hi)]
    simp [hi]
    exact h _
  · have h1 : (List.ofFn p1).length ≤ i := by simp; omega
    have h2 : (List.ofFn p2).length ≤ i := by simp; omega
    rw [List.getElem?_append_right h1, List.getElem?_append_right h2]
    simp

end PEqualNP.Outside.L_meta_1798_aux

open PEqualNP.Outside.L_meta_1798_aux in
theorem PEqualNP.Outside.L_meta_1798 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ w : Fin L, PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → PEqualNP.LowMerge.IsLow P L inc C a w ∨ PEqualNP.LowMerge.IsLow P L inc C b w := by
  intro P L inc C hC j a b hj ha hb w hlow
  have hjl : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hsplit : C.gates = C.gates.take j ++ ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ :: C.gates.drop (j + 1) := by
    have h0 := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hjl] at h0
    have h3 : C.gates[j] = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ := by
      rw [List.getElem?_eq_getElem hjl] at hj
      exact Option.some.inj hj
    rw [h3] at h0
    exact h0.symm
  have key : ∀ pts : Fin P → Bool,
      PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) (P + L + j) =
        (PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) a &&
          PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) b) := by
    intro pts
    have hx : (PEqualNP.LowMerge.restrictInput P L w pts).length = P + L := by
      simp [PEqualNP.LowMerge.restrictInput]
    set x := PEqualNP.LowMerge.restrictInput P L w pts
    set w' := (C.gates.take j).foldl F x with hw'
    have hlw : w'.length = P + L + j := by
      rw [hw', fold_len, hx, List.length_take]; omega
    have hwires : C.wires x = (C.gates.drop (j + 1)).foldl F (F w' ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩) := by
      rw [wires_eq]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpre := fold_prefix (C.gates.drop (j + 1)) (F w' ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩)
    have hpre2 : w' <+: (C.gates.drop (j + 1)).foldl F (F w' ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩) :=
      (List.prefix_append w' _).trans hpre
    simp only [PEqualNP.LowMerge.wireVal, hwires]
    rw [getD_prefix hpre (by simp [F, hlw]), getD_prefix hpre2 (by omega), getD_prefix hpre2 (by omega)]
    simp [F, hlw, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hmono : ∀ (p1 p2 : Fin P → Bool), (∀ p, p1 p = true → p2 p = true) → ∀ g,
      PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w p1) g = true →
      PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w p2) g = true := by
    intro p1 p2 h g
    simp only [PEqualNP.LowMerge.wireVal, wires_eq]
    apply fold_mono C.gates hC
    · simp [PEqualNP.LowMerge.restrictInput]
    · exact restrict_mono P L w p1 p2 h
  by_contra hc
  rw [not_or] at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [PEqualNP.LowMerge.IsLow, not_forall] at h1 h2
  obtain ⟨q1, hq1, hs1⟩ := h1
  obtain ⟨q2, hq2, hs2⟩ := h2
  have ha' := hmono q1 (fun p => q1 p || q2 p) (fun p hp => by simp [hp]) a hq1
  have hb' := hmono q2 (fun p => q1 p || q2 p) (fun p hp => by simp [hp]) b hq2
  have hg := hlow (fun p => q1 p || q2 p) (by rw [key, ha', hb']; rfl)
  simp only [PEqualNP.LowMerge.lineSum, decide_eq_true_eq] at hg hs1 hs2
  obtain ⟨p, hp1, hp2⟩ := hg
  rcases Bool.or_eq_true_iff.mp hp2 with h | h
  · exact hs1 ⟨p, hp1, h⟩
  · exact hs2 ⟨p, hp1, h⟩
