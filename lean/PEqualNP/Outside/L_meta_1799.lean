import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1799_aux

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i < w.length then w.getD i false else if i = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rcases hk : i - w.length with _ | k
    · omega
    · simp

theorem len_run (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl]; rw [ih]; simp; omega

theorem keep_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl]
    rw [ih _ (by simp; omega), getD_snoc, if_pos hi]

theorem mono_run (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hl : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false = true → w2.getD i false = true) (i : ℕ) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hw i
  | cons g gs ih =>
    simp only [List.foldl]
    apply ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · intro k hk
      rw [getD_snoc] at hk ⊢
      rw [← hl]
      split_ifs at hk ⊢ with h1 h2
      · exact hw k hk
      · rcases hm g List.mem_cons_self with h | h
        · rw [h] at hk ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hk ⊢
          exact fun x hx => hw x (hk x hx)
        · rw [h] at hk ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hk ⊢
          obtain ⟨x, hx, h⟩ := hk
          exact ⟨x, hx, hw x h⟩

theorem gate_val (C : Circuit) (x : List Bool) (j a b : ℕ) (op : GateOp)
    (hg : C.gates[j]? = some ⟨op, [a, b]⟩) (ha : a < x.length + j) (hb : b < x.length + j) :
    wireVal C x (x.length + j) = op.eval [wireVal C x a, wireVal C x b] := by
  have hj : j < C.gates.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hsplit : C.gates = C.gates.take j ++ ⟨op, [a, b]⟩ :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    congr 1
    rw [List.drop_eq_getElem_cons hj]
    congr 1
    rw [List.getElem?_eq_getElem hj] at hg
    simpa using hg
  set F := (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
  set W := (C.gates.take j).foldl F x with hW
  have hWl : W.length = x.length + j := by
    rw [hW, len_run]; simp; omega
  have hwires : C.wires x = (C.gates.drop (j + 1)).foldl F (W ++ [op.eval [W.getD a false, W.getD b false]]) := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    rfl
  have hread : ∀ i, i < x.length + j → wireVal C x i = W.getD i false := by
    intro i hi
    unfold wireVal
    rw [hwires, keep_run _ _ _ (by simp; omega), getD_snoc, if_pos (by omega)]
  rw [hread a ha, hread b hb]
  unfold wireVal
  rw [hwires, keep_run _ _ _ (by simp; omega), getD_snoc, if_neg (by omega), if_pos hWl.symm]

theorem restrict_len (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

theorem restrict_mono (P L : ℕ) (w : Fin L) (p1 p2 : Fin P → Bool)
    (h : ∀ p, p1 p = true → p2 p = true) (i : ℕ) :
    (restrictInput P L w p1).getD i false = true → (restrictInput P L w p2).getD i false = true := by
  unfold restrictInput
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < P
  · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_ofFn, hi]
    exact h _
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp

theorem wire_mono (P L : ℕ) (C : Circuit) (hm : IsMonotoneCircuit C) (w : Fin L)
    (p1 p2 : Fin P → Bool) (h : ∀ p, p1 p = true → p2 p = true) (g : ℕ) :
    wireVal C (restrictInput P L w p1) g = true → wireVal C (restrictInput P L w p2) g = true := by
  unfold wireVal Circuit.wires
  exact mono_run C.gates hm _ _ (by rw [restrict_len, restrict_len]) (restrict_mono P L w p1 p2 h) g

end PEqualNP.Outside.L_meta_1799_aux

open PEqualNP.Outside.L_meta_1799_aux in
theorem PEqualNP.Outside.L_meta_1799 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp), (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) → C.gates[j]? = some ⟨op, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ (w : Fin L) (y : Fin P), PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → y ∈ PEqualNP.LowMerge.aliveSet P L C (P + L + j) w → (PEqualNP.LowMerge.IsLow P L inc C a w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C a w) ∨ (PEqualNP.LowMerge.IsLow P L inc C b w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C b w) := by
  intro P L inc C hm j a b op hop hg ha hb w y hlow hy
  have hv : ∀ pts, PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) (P + L + j)
      = op.eval [PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) a,
                 PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) b] := by
    intro pts
    have := gate_val C (PEqualNP.LowMerge.restrictInput P L w pts) j a b op hg
      (by rw [restrict_len]; exact ha) (by rw [restrict_len]; exact hb)
    rw [restrict_len] at this
    exact this
  simp only [PEqualNP.LowMerge.aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  simp only [PEqualNP.LowMerge.pointLineInput] at hy ⊢
  rw [hv] at hy
  rcases hop with rfl | rfl
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at hy
    by_contra hc
    have hna : ¬ PEqualNP.LowMerge.IsLow P L inc C a w := fun h => hc (Or.inl ⟨h, hy.1⟩)
    have hnb : ¬ PEqualNP.LowMerge.IsLow P L inc C b w := fun h => hc (Or.inr ⟨h, hy.2⟩)
    simp only [PEqualNP.LowMerge.IsLow, not_forall] at hna hnb
    obtain ⟨p1, h1, h1'⟩ := hna
    obtain ⟨p2, h2, h2'⟩ := hnb
    have hu := hlow (fun p => p1 p || p2 p)
    rw [hv] at hu
    have ea := wire_mono P L C hm w p1 (fun p => p1 p || p2 p) (by intro p hp; simp [hp]) a h1
    have eb := wire_mono P L C hm w p2 (fun p => p1 p || p2 p) (by intro p hp; simp [hp]) b h2
    have := hu (by simp [PEqualNP.CircuitLowerBounds.GateOp.eval, ea, eb])
    simp only [PEqualNP.LowMerge.lineSum, decide_eq_true_eq] at this h1' h2'
    obtain ⟨p, hp, hq⟩ := this
    rcases Bool.or_eq_true_iff.mp hq with hq | hq
    · exact h1' ⟨p, hp, hq⟩
    · exact h2' ⟨p, hp, hq⟩
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at hy
    have lowOf : ∀ c, (∀ pts, PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) c = true →
        PEqualNP.LowMerge.wireVal C (PEqualNP.LowMerge.restrictInput P L w pts) (P + L + j) = true) →
        PEqualNP.LowMerge.IsLow P L inc C c w := fun c hc pts hp => hlow pts (hc pts hp)
    rcases hy with hy | hy
    · left; refine ⟨lowOf a ?_, hy⟩
      intro pts hp; rw [hv]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hp]
    · right; refine ⟨lowOf b ?_, hy⟩
      intro pts hp; rw [hv]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hp]
