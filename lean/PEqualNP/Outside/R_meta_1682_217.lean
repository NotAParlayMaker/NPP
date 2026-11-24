import Mathlib.Data.Finset.Card
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1682_217
    (h_and_inc :
      let inc : Fin 13 → Fin 13 → Bool := fun p w =>
        let d := p - w
        d == 0 || d == 1 || d == 3 || d == 9
      ∀ d : ℕ, (d = 0 ∨ d = 1) →
        ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
          C.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [d, 13] } ∧
          (∀ p w : Fin 13, inc p w = true →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == p) (fun z => z == w)) = true) ∧
          (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == a || q == b || q == c)
                (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false) ∧
          (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
                (fun z => z == u || z == v || z == w)) = false))
    (h_or_same :
      let inc : Fin 13 → Fin 13 → Bool := fun p w =>
        let d := p - w
        d == 0 || d == 1 || d == 3 || d == 9
      ∀ d : ℕ, (d = 1 ∨ d = 2) →
        ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
          C.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, d] } ∧
          (∀ p w : Fin 13, inc p w = true →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == p) (fun z => z == w)) = true) ∧
          (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == a || q == b || q == c)
                (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false) ∧
          (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
                (fun z => z == u || z == v || z == w)) = false))
    (h_or_inc :
      let inc : Fin 13 → Fin 13 → Bool := fun p w =>
        let d := p - w
        d == 0 || d == 1 || d == 3 || d == 9
      ∀ d : ℕ, (d = 0 ∨ d = 1) →
        ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
          C.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [d, 13] } ∧
          (∀ p w : Fin 13, inc p w = true →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == p) (fun z => z == w)) = true) ∧
          (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == a || q == b || q == c)
                (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false) ∧
          (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
                (fun z => z == u || z == v || z == w)) = false))
    (h_or_noninc :
      let inc : Fin 13 → Fin 13 → Bool := fun p w =>
        let d := p - w
        d == 0 || d == 1 || d == 3 || d == 9
      ∀ d : ℕ, (d = 2 ∨ d = 4 ∨ d = 7) →
        ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧
          C.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [d, 13] } ∧
          (∀ p w : Fin 13, inc p w = true →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == p) (fun z => z == w)) = true) ∧
          (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun q => q == a || q == b || q == c)
                (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false) ∧
          (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
            PEqualNP.MetaComplexity.circuitFun (13 + 13) C
              (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
                (fun z => z == u || z == v || z == w)) = false)) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  intro hex
  rcases hex with ⟨C0, hmono0, hsize0, hpos0, hneg0⟩
  let inc : Fin 13 → Fin 13 → Bool := fun p w =>
    let d := p - w
    d == 0 || d == 1 || d == 3 || d == 9
  -- Finite PG(2,3) facts proved with clean context
  have h_inc_mul : ∀ m : Fin 13, (m = 1 ∨ m = 3 ∨ m = 9) →
      ∀ p w : Fin 13, inc (m * p) (m * w) = inc p w := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_inc_dual : ∀ p w : Fin 13, inc (-w) (-p) = inc p w := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_tri_closed0 : ∀ b c v : Fin 13,
      (∀ w : Fin 13, ¬ (inc 0 w = true ∧ inc b w = true ∧ inc c w = true)) →
      v ≠ 0 → v ≠ b → v ≠ c →
      ∃ w : Fin 13, inc 0 w = false ∧ inc b w = false ∧ inc c w = false ∧ inc v w = true := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_tri_nonconc0 : ∀ b c v : Fin 13,
      (∀ w : Fin 13, ¬ (inc 0 w = true ∧ inc b w = true ∧ inc c w = true)) →
      ∃ w : Fin 13, inc 0 w = false ∧ inc b w = false ∧ inc c w = false ∧ inc v w = false := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_dual_close0 : ∀ v w z : Fin 13,
      (∀ p : Fin 13, ¬ (inc p 0 = true ∧ inc p v = true ∧ inc p w = true)) →
      (∀ p : Fin 13, inc p 0 = false → inc p v = false → inc p w = false → inc p z = false) →
      z = 0 ∨ z = v ∨ z = w := by
    intro v w z hnc hcl
    by_contra hne
    have hne' : z ≠ 0 ∧ z ≠ v ∧ z ≠ w := by
      refine ⟨fun h => hne (Or.inl h), fun h => hne (Or.inr (Or.inl h)), fun h => hne (Or.inr (Or.inr h))⟩
    have hnc' : ∀ q : Fin 13, ¬ (inc 0 q = true ∧ inc (-v) q = true ∧ inc (-w) q = true) := by
      intro q h; apply hnc (-q)
      have h0 := h_inc_dual (-q) 0; simp only [neg_zero, neg_neg] at h0
      have hv := h_inc_dual (-q) v; simp only [neg_neg] at hv
      have hw := h_inc_dual (-q) w; simp only [neg_neg] at hw
      rw [← h0, ← hv, ← hw]; exact h
    rcases h_tri_closed0 (-v) (-w) (-z) hnc'
      (fun h => hne'.1 (by simpa using congrArg (- ·) h))
      (fun h => hne'.2.1 (neg_injective h))
      (fun h => hne'.2.2 (neg_injective h)) with ⟨q, h0, hv, hw, hz⟩
    have h0' : inc (-q) 0 = false := by have := h_inc_dual (-q) 0; simp only [neg_zero, neg_neg] at this; rw [← this]; exact h0
    have hv' : inc (-q) v = false := by have := h_inc_dual (-q) v; simp only [neg_neg] at this; rw [← this]; exact hv
    have hw' : inc (-q) w = false := by have := h_inc_dual (-q) w; simp only [neg_neg] at this; rw [← this]; exact hw
    have hz' : inc (-q) z = true := by have := h_inc_dual (-q) z; simp only [neg_neg] at this; rw [← this]; exact hz
    have hcontra := hcl (-q) h0' hv' hw'
    rw [hcontra] at hz'; exact Bool.noConfusion hz'
  have h_dual_noncol0 : ∀ v w z : Fin 13,
      (∀ p : Fin 13, ¬ (inc p 0 = true ∧ inc p v = true ∧ inc p w = true)) →
      ∃ p : Fin 13, inc p 0 = false ∧ inc p v = false ∧ inc p w = false ∧ inc p z = false := by
    intro v w z hnc
    have hnc' : ∀ q : Fin 13, ¬ (inc 0 q = true ∧ inc (-v) q = true ∧ inc (-w) q = true) := by
      intro q h; apply hnc (-q)
      have h0 := h_inc_dual (-q) 0; simp only [neg_zero, neg_neg] at h0
      have hv := h_inc_dual (-q) v; simp only [neg_neg] at hv
      have hw := h_inc_dual (-q) w; simp only [neg_neg] at hw
      rw [← h0, ← hv, ← hw]; exact h
    rcases h_tri_nonconc0 (-v) (-w) (-z) hnc' with ⟨q, h0, hv, hw, hz⟩
    refine ⟨-q, ?_, ?_, ?_, ?_⟩
    · have := h_inc_dual (-q) 0; simp only [neg_zero, neg_neg] at this; rw [← this]; exact h0
    · have := h_inc_dual (-q) v; simp only [neg_neg] at this; rw [← this]; exact hv
    · have := h_inc_dual (-q) w; simp only [neg_neg] at this; rw [← this]; exact hw
    · have := h_inc_dual (-q) z; simp only [neg_neg] at this; rw [← this]; exact hz
  have h_orb_all : ∀ x : Fin 13, ∃ m : Fin 13, (m = 1 ∨ m = 3 ∨ m = 9) ∧
      (m * x = 0 ∨ m * x = 1 ∨ m * x = 2 ∨ m * x = 4 ∨ m * x = 7) := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_orb_inc : ∀ x : Fin 13, inc x 0 = true → ∃ m : Fin 13, (m = 1 ∨ m = 3 ∨ m = 9) ∧
      (m * x = 0 ∨ m * x = 1) := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_orb_same : ∀ x : Fin 13, x ≠ 0 → ∃ m : Fin 13, (m = 1 ∨ m = 3 ∨ m = 9) ∧
      ((m * x = 1 ∨ m * x = 2) ∨ (m * (-x) = 1 ∨ m * (-x) = 2)) := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_noncol012 : ∀ w : Fin 13, ¬ (inc 0 w = true ∧ inc 1 w = true ∧ inc 2 w = true) := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0; decide
  have h_inc_iff : ∀ p w : Fin 13,
      (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) ↔ inc p w = true := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0
    intro p w
    constructor
    · intro h
      rcases h with ⟨dd, hdd, hp⟩
      have hsub : p - w = dd := by rw [hp, add_comm, add_sub_cancel_right]
      have hdd' : dd = 0 ∨ dd = 1 ∨ dd = 3 ∨ dd = 9 := by simpa using hdd
      change (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9) = true
      rw [hsub]
      rcases hdd' with rfl | rfl | rfl | rfl <;> rfl
    · intro h
      have hsub : p - w = 0 ∨ p - w = 1 ∨ p - w = 3 ∨ p - w = 9 := by
        change (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9) = true at h
        simpa [Bool.or_eq_true, beq_iff_eq, or_assoc] using h
      refine ⟨p - w, ?_, ?_⟩
      · rcases hsub with h0 | h1 | h3 | h9
        · rw [h0]; simp
        · rw [h1]; simp
        · rw [h3]; simp
        · rw [h9]; simp
      · rw [add_comm, sub_add_cancel]
  have h_inc_shift : ∀ p w t : Fin 13, inc (p + t) (w + t) = inc p w := by
    intro p w t
    change (((p + t - (w + t) == 0 || p + t - (w + t) == 1) || p + t - (w + t) == 3) ||
      p + t - (w + t) == 9) =
      (((p - w == 0 || p - w == 1) || p - w == 3) || p - w == 9)
    have hsub : p + t - (w + t) = p - w := add_sub_add_right_eq_sub p w t
    rw [hsub]
  -- Existential 3-state gate-list simplifier (no local let peStep)
  have h_pe_ind :
      let simStep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      let sem : List Bool → ℕ → Bool := fun w' c =>
        if c = 0 then false else if c = 1 then true else w'.getD (c - 2) false
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ (gs0 : List PEqualNP.CircuitLowerBounds.Gate) (m0 : List ℕ),
        (∀ g ∈ gs0, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ c ∈ m0, c < 26 + gs0.length + 2) →
        ∃ (gs1 : List PEqualNP.CircuitLowerBounds.Gate) (m1 : List ℕ),
          gs1.length ≤ gs0.length + gs.length ∧
          (∀ g ∈ gs1, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
            Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) ∧
          m1.length = m0.length + gs.length ∧
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = w0.getD k false) →
            (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = (gs.foldl simStep w0).getD k false)) ∧
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = true → w0.getD k false = true) →
            (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = true → (gs.foldl simStep w0).getD k false = true)) := by
    clear h_and_inc h_or_same h_or_inc h_or_noninc C0 hmono0 hsize0 hpos0 hneg0
      inc h_inc_mul h_inc_dual h_tri_closed0 h_tri_nonconc0 h_dual_close0 h_dual_noncol0
      h_orb_all h_orb_inc h_orb_same h_noncol012 h_inc_iff h_inc_shift
    intro simStep sem
    have h_simStep_len : ∀ w g, (simStep w g).length = w.length + 1 := by
      intro w g; simp [simStep]
    have h_foldl_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl simStep w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g rest ih => intro w; rw [List.foldl_cons, ih, h_simStep_len, List.length_cons]; omega
    have h_sem_app : ∀ w' b c, c < w'.length + 2 → sem (w' ++ [b]) c = sem w' c := by
      intro w' b c hc
      by_cases h0 : c = 0
      · simp [sem, h0]
      · by_cases h1 : c = 1
        · simp [sem, h1]
        · simp only [sem, h0, h1, ↓reduceIte]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
          exact List.getElem_append_left (by omega)
    have h_sem_last : ∀ w' b, sem (w' ++ [b]) (w'.length + 2) = b := by
      intro w' b
      have h0 : w'.length + 2 ≠ 0 := by omega
      have h1 : w'.length + 2 ≠ 1 := by omega
      simp only [sem, h0, h1, ↓reduceIte]
      have hsub : w'.length + 2 - 2 = w'.length := by omega
      rw [hsub, List.getD_eq_getElem _ _ (by simp)]
      simp
    have h_and2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
      intro a b; cases a <;> cases b <;> rfl
    have h_or2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
      intro a b; cases a <;> cases b <;> rfl
    have h_and1 : ∀ a : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a] = a := by
      intro a; cases a <;> rfl
    have h_or1 : ∀ a : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a] = a := by
      intro a; cases a <;> rfl
    intro gs
    induction gs with
    | nil =>
      intro _ gs0 m0 hgs0 _
      refine ⟨gs0, m0, by simp, hgs0, by simp, ?_, ?_⟩
      · intro x w0 _ _ heq k; exact heq k
      · intro x w0 _ _ hle k; exact hle k
    | cons g rest ih =>
      intro hgs gs0 m0 hgs0 hm0
      have hg := hgs g (List.mem_cons_self ..)
      have hrest : ∀ g' ∈ rest, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
          Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      have h_finish_noop : ∀ (newC : ℕ), newC < 26 + gs0.length + 2 →
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = w0.getD k false) →
            sem (gs0.foldl simStep x) newC = g.op.eval (g.inputs.map fun i => w0.getD i false)) →
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = true → w0.getD k false = true) →
            sem (gs0.foldl simStep x) newC = true → g.op.eval (g.inputs.map fun i => w0.getD i false) = true) →
          ∃ (gs1 : List PEqualNP.CircuitLowerBounds.Gate) (m1 : List ℕ),
            gs1.length ≤ gs0.length + (g :: rest).length ∧
            (∀ g' ∈ gs1, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
              Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2) ∧
            m1.length = m0.length + (g :: rest).length ∧
            (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
              (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = w0.getD k false) →
              (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = ((g :: rest).foldl simStep w0).getD k false)) ∧
            (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
              (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = true → w0.getD k false = true) →
              (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = true → ((g :: rest).foldl simStep w0).getD k false = true)) := by
        intro newC hnewC heq_new hle_new
        have hm1_lt : ∀ c ∈ m0 ++ [newC], c < 26 + gs0.length + 2 := by
          intro c hc
          simp only [List.mem_append, List.mem_singleton] at hc
          rcases hc with hc | rfl
          · exact hm0 c hc
          · exact hnewC
        rcases ih hrest gs0 (m0 ++ [newC]) hgs0 hm1_lt with ⟨gs1, m1, hlen1, hmono1, hm1len, heq1, hle1⟩
        refine ⟨gs1, m1, by simp; omega, hmono1, by simp at hm1len ⊢; omega, ?_, ?_⟩
        · intro x w0 hx hw0 heq k
          rw [List.foldl_cons]
          refine heq1 x (simStep w0 g) hx (by rw [h_simStep_len]; simp; omega) ?_ k
          intro j
          by_cases hj : j < m0.length
          · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj,
              ← List.getD_eq_getElem m0 0 hj, heq j]
            simp only [simStep]
            rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega)]
            rw [List.getD_eq_getElem w0 false (by omega)]
          · by_cases hj2 : j = m0.length
            · subst hj2
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_singleton]
              simp only [simStep]
              rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_right (by omega)]
              have hsub : m0.length - w0.length = 0 := by omega
              simp only [hsub, List.getElem_singleton]
              exact heq_new x w0 hx hw0 heq
            · rw [List.getD_eq_default _ _ (by simp; omega)]
              simp only [simStep]
              rw [List.getD_eq_default _ _ (by simp; omega)]
              rfl
        · intro x w0 hx hw0 hle k
          rw [List.foldl_cons]
          refine hle1 x (simStep w0 g) hx (by rw [h_simStep_len]; simp; omega) ?_ k
          intro j ht
          by_cases hj : j < m0.length
          · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj,
              ← List.getD_eq_getElem m0 0 hj] at ht
            simp only [simStep]
            rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega),
              ← List.getD_eq_getElem w0 false (by omega)]
            exact hle j ht
          · by_cases hj2 : j = m0.length
            · subst hj2
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)] at ht
              simp only [Nat.sub_self, List.getElem_singleton] at ht
              simp only [simStep]
              rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_right (by omega)]
              have hsub : m0.length - w0.length = 0 := by omega
              simp only [hsub, List.getElem_singleton]
              exact hle_new x w0 hx hw0 hle ht
            · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
              exact Bool.noConfusion ht
      have h_finish_emit : ∀ (op' : PEqualNP.CircuitLowerBounds.GateOp) (c0 c1 : ℕ),
          op' ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
            Set PEqualNP.CircuitLowerBounds.GateOp) →
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = w0.getD k false) →
            op'.eval [(gs0.foldl simStep x).getD (c0 - 2) false, (gs0.foldl simStep x).getD (c1 - 2) false] =
              g.op.eval (g.inputs.map fun i => w0.getD i false)) →
          (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
            (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = true → w0.getD k false = true) →
            op'.eval [(gs0.foldl simStep x).getD (c0 - 2) false, (gs0.foldl simStep x).getD (c1 - 2) false] = true →
              g.op.eval (g.inputs.map fun i => w0.getD i false) = true) →
          ∃ (gs1 : List PEqualNP.CircuitLowerBounds.Gate) (m1 : List ℕ),
            gs1.length ≤ gs0.length + (g :: rest).length ∧
            (∀ g' ∈ gs1, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
              Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2) ∧
            m1.length = m0.length + (g :: rest).length ∧
            (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
              (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = w0.getD k false) →
              (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = ((g :: rest).foldl simStep w0).getD k false)) ∧
            (∀ (x w0 : List Bool), x.length = 26 → w0.length = m0.length →
              (∀ k : ℕ, sem (gs0.foldl simStep x) (m0.getD k 0) = true → w0.getD k false = true) →
              (∀ k : ℕ, sem (gs1.foldl simStep x) (m1.getD k 0) = true → ((g :: rest).foldl simStep w0).getD k false = true)) := by
        intro op' c0 c1 hop' heq_new hle_new
        let gs_next := gs0 ++ [{ op := op', inputs := [c0 - 2, c1 - 2] }]
        let m_next := m0 ++ [26 + gs0.length + 2]
        have hgs_next : ∀ g' ∈ gs_next, g'.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
            Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g'.inputs.length ≤ 2 := by
          intro g' hg'
          simp only [gs_next, List.mem_append, List.mem_singleton] at hg'
          rcases hg' with hg' | rfl
          · exact hgs0 g' hg'
          · exact ⟨hop', by simp⟩
        have hm_next : ∀ c ∈ m_next, c < 26 + gs_next.length + 2 := by
          intro c hc
          simp only [m_next, gs_next, List.mem_append, List.mem_singleton, List.length_append, List.length_singleton] at hc ⊢
          rcases hc with hc | rfl
          · have := hm0 c hc; omega
          · omega
        rcases ih hrest gs_next m_next hgs_next hm_next with ⟨gs1, m1, hlen1, hmono1, hm1len, heq1, hle1⟩
        refine ⟨gs1, m1, by simp [gs_next] at hlen1 ⊢; omega, hmono1, by simp [m_next] at hm1len ⊢; omega, ?_, ?_⟩
        · intro x w0 hx hw0 heq k
          rw [List.foldl_cons]
          refine heq1 x (simStep w0 g) hx (by rw [h_simStep_len]; simp [m_next]; omega) ?_ k
          have hfold : gs_next.foldl simStep x =
              (gs0.foldl simStep x) ++ [op'.eval [(gs0.foldl simStep x).getD (c0 - 2) false,
                (gs0.foldl simStep x).getD (c1 - 2) false]] := by
            simp only [gs_next, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
          have hlenw : (gs0.foldl simStep x).length = 26 + gs0.length := by rw [h_foldl_len, hx]
          intro j
          rw [hfold]
          by_cases hj : j < m0.length
          · simp only [m_next]
            rw [List.getD_eq_getElem (m0 ++ [_]) 0 (by simp; omega), List.getElem_append_left hj]
            have hcm := hm0 m0[j] (List.getElem_mem hj)
            rw [h_sem_app _ _ _ (by omega), ← List.getD_eq_getElem m0 0 hj, heq j]
            simp only [simStep]
            rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega)]
            rw [List.getD_eq_getElem w0 false (by omega)]
          · by_cases hj2 : j = m0.length
            · subst hj2
              simp only [m_next]
              rw [List.getD_eq_getElem (m0 ++ [_]) 0 (by simp), List.getElem_append_right (Nat.le_refl _)]
              simp only [Nat.sub_self, List.getElem_singleton]
              rw [← hlenw, h_sem_last]
              simp only [simStep]
              rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_right (by omega)]
              have hsub : m0.length - w0.length = 0 := by omega
              simp only [hsub, List.getElem_singleton]
              exact heq_new x w0 hx hw0 heq
            · simp only [m_next]
              rw [List.getD_eq_default (m0 ++ [_]) 0 (by simp; omega)]
              simp only [simStep]
              rw [List.getD_eq_default (w0 ++ [_]) false (by simp; omega)]
              rfl
        · intro x w0 hx hw0 hle k
          rw [List.foldl_cons]
          refine hle1 x (simStep w0 g) hx (by rw [h_simStep_len]; simp [m_next]; omega) ?_ k
          have hfold : gs_next.foldl simStep x =
              (gs0.foldl simStep x) ++ [op'.eval [(gs0.foldl simStep x).getD (c0 - 2) false,
                (gs0.foldl simStep x).getD (c1 - 2) false]] := by
            simp only [gs_next, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
          have hlenw : (gs0.foldl simStep x).length = 26 + gs0.length := by rw [h_foldl_len, hx]
          intro j ht
          rw [hfold] at ht
          by_cases hj : j < m0.length
          · simp only [m_next] at ht
            rw [List.getD_eq_getElem (m0 ++ [_]) 0 (by simp; omega), List.getElem_append_left hj] at ht
            have hcm := hm0 m0[j] (List.getElem_mem hj)
            rw [h_sem_app _ _ _ (by omega), ← List.getD_eq_getElem m0 0 hj] at ht
            simp only [simStep]
            rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega),
              ← List.getD_eq_getElem w0 false (by omega)]
            exact hle j ht
          · by_cases hj2 : j = m0.length
            · subst hj2
              simp only [m_next] at ht
              rw [List.getD_eq_getElem (m0 ++ [_]) 0 (by simp), List.getElem_append_right (Nat.le_refl _)] at ht
              simp only [Nat.sub_self, List.getElem_singleton] at ht
              rw [← hlenw, h_sem_last] at ht
              simp only [simStep]
              rw [List.getD_eq_getElem (w0 ++ [_]) false (by simp; omega), List.getElem_append_right (by omega)]
              have hsub : m0.length - w0.length = 0 := by omega
              simp only [hsub, List.getElem_singleton]
              exact hle_new x w0 hx hw0 hle ht
            · simp only [m_next] at ht
              rw [List.getD_eq_default (m0 ++ [_]) 0 (by simp; omega)] at ht
              exact Bool.noConfusion ht
      have hgetD_lt : ∀ k : ℕ, m0.getD k 0 < 26 + gs0.length + 2 := by
        intro k
        by_cases hk : k < m0.length
        · rw [List.getD_eq_getElem _ _ hk]; exact hm0 _ (List.getElem_mem hk)
        · rw [List.getD_eq_default _ _ (by omega)]; omega
      have hg_op : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hg.1
      have hg_len : g.inputs.length ≤ 2 := hg.2
      cases hin : g.inputs with
      | nil =>
        rcases hg_op with hop | hop
        · exact h_finish_noop 1 (by omega)
            (fun _ _ _ _ _ => by rw [hop, hin]; rfl)
            (fun _ _ _ _ _ _ => by rw [hop, hin]; rfl)
        · exact h_finish_noop 0 (by omega)
            (fun _ _ _ _ _ => by rw [hop, hin]; rfl)
            (fun _ _ _ _ _ ht => Bool.noConfusion ht)
      | cons a tl =>
        cases tl with
        | nil =>
          refine h_finish_noop (m0.getD a 0) (hgetD_lt a) ?_ ?_
          · intro x w0 _ _ heq
            rw [hin, List.map_cons, List.map_nil]
            rcases hg_op with hop | hop
            · rw [hop, h_and1]; exact heq a
            · rw [hop, h_or1]; exact heq a
          · intro x w0 _ _ hle ht
            rw [hin, List.map_cons, List.map_nil]
            rcases hg_op with hop | hop
            · rw [hop, h_and1]; exact hle a ht
            · rw [hop, h_or1]; exact hle a ht
        | cons b tl2 =>
          cases tl2 with
          | cons _ _ => rw [hin] at hg_len; simp at hg_len
          | nil =>
            let c0 := m0.getD a 0
            let c1 := m0.getD b 0
            rcases hg_op with hop | hop
            · by_cases hz : c0 = 0 ∨ c1 = 0
              · refine h_finish_noop 0 (by omega) ?_ (fun _ _ _ _ _ ht => Bool.noConfusion ht)
                intro x w0 _ _ heq
                rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                rcases hz with h0 | h0
                · have ha := heq a; change sem _ c0 = _ at ha; rw [h0] at ha; rw [← ha]; rfl
                · have hb := heq b; change sem _ c1 = _ at hb; rw [h0] at hb; rw [← hb]; simp [sem]
              · have hc0_ne0 : c0 ≠ 0 := fun h => hz (Or.inl h)
                have hc1_ne0 : c1 ≠ 0 := fun h => hz (Or.inr h)
                by_cases h1a : c0 = 1
                · refine h_finish_noop c1 (hgetD_lt b) ?_ ?_
                  · intro x w0 _ _ heq
                    rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                    have ha := heq a; change sem _ c0 = _ at ha; rw [h1a] at ha
                    have hb := heq b; change sem _ c1 = _ at hb
                    rw [← ha, ← hb]; rfl
                  · intro x w0 _ _ hle ht
                    rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                    have ha : w0.getD a false = true := hle a (by change sem _ c0 = true; rw [h1a]; rfl)
                    have hb : w0.getD b false = true := hle b ht
                    rw [ha, hb]; rfl
                · by_cases h1b : c1 = 1
                  · refine h_finish_noop c0 (hgetD_lt a) ?_ ?_
                    · intro x w0 _ _ heq
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                      have ha := heq a; change sem _ c0 = _ at ha
                      have hb := heq b; change sem _ c1 = _ at hb; rw [h1b] at hb
                      rw [← ha, ← hb]; simp [sem]
                    · intro x w0 _ _ hle ht
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                      have ha : w0.getD a false = true := hle a ht
                      have hb : w0.getD b false = true := hle b (by change sem _ c1 = true; rw [h1b]; rfl)
                      rw [ha, hb]; rfl
                  · refine h_finish_emit PEqualNP.CircuitLowerBounds.GateOp.and c0 c1 (by simp) ?_ ?_
                    · intro x w0 _ _ heq
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2, h_and2]
                      have ha := heq a; change sem _ c0 = _ at ha
                      have hb := heq b; change sem _ c1 = _ at hb
                      simp only [sem, hc0_ne0, h1a, hc1_ne0, h1b, ↓reduceIte] at ha hb
                      rw [ha, hb]
                    · intro x w0 _ _ hle ht
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_and2]
                      rw [h_and2, Bool.and_eq_true] at ht
                      have ha : w0.getD a false = true := hle a (by
                        change sem _ c0 = true; simp only [sem, hc0_ne0, h1a, ↓reduceIte]; exact ht.1)
                      have hb : w0.getD b false = true := hle b (by
                        change sem _ c1 = true; simp only [sem, hc1_ne0, h1b, ↓reduceIte]; exact ht.2)
                      rw [ha, hb]; rfl
            · by_cases ho : c0 = 1 ∨ c1 = 1
              · refine h_finish_noop 1 (by omega) ?_ ?_
                · intro x w0 _ _ heq
                  rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                  rcases ho with h1 | h1
                  · have ha := heq a; change sem _ c0 = _ at ha; rw [h1] at ha; rw [← ha]; rfl
                  · have hb := heq b; change sem _ c1 = _ at hb; rw [h1] at hb; rw [← hb]; simp [sem]
                · intro x w0 _ _ hle _
                  rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                  rcases ho with h1 | h1
                  · have ha : w0.getD a false = true := hle a (by change sem _ c0 = true; rw [h1]; rfl)
                    rw [ha]; rfl
                  · have hb : w0.getD b false = true := hle b (by change sem _ c1 = true; rw [h1]; rfl)
                    rw [hb]; simp
              · have hc0_ne1 : c0 ≠ 1 := fun h => ho (Or.inl h)
                have hc1_ne1 : c1 ≠ 1 := fun h => ho (Or.inr h)
                by_cases h0a : c0 = 0
                · refine h_finish_noop c1 (hgetD_lt b) ?_ ?_
                  · intro x w0 _ _ heq
                    rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                    have ha := heq a; change sem _ c0 = _ at ha; rw [h0a] at ha
                    have hb := heq b; change sem _ c1 = _ at hb
                    rw [← ha, ← hb]; rfl
                  · intro x w0 _ _ hle ht
                    rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                    have hb : w0.getD b false = true := hle b ht
                    rw [hb]; simp
                · by_cases h0b : c1 = 0
                  · refine h_finish_noop c0 (hgetD_lt a) ?_ ?_
                    · intro x w0 _ _ heq
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                      have ha := heq a; change sem _ c0 = _ at ha
                      have hb := heq b; change sem _ c1 = _ at hb; rw [h0b] at hb
                      rw [← ha, ← hb]; simp [sem]
                    · intro x w0 _ _ hle ht
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                      have ha : w0.getD a false = true := hle a ht
                      rw [ha]; rfl
                  · refine h_finish_emit PEqualNP.CircuitLowerBounds.GateOp.or c0 c1 (by simp) ?_ ?_
                    · intro x w0 _ _ heq
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2, h_or2]
                      have ha := heq a; change sem _ c0 = _ at ha
                      have hb := heq b; change sem _ c1 = _ at hb
                      simp only [sem, h0a, hc0_ne1, h0b, hc1_ne1, ↓reduceIte] at ha hb
                      rw [ha, hb]
                    · intro x w0 _ _ hle ht
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or2]
                      rw [h_or2, Bool.or_eq_true] at ht
                      rcases ht with ht | ht
                      · have ha : w0.getD a false = true := hle a (by
                          change sem _ c0 = true; simp only [sem, h0a, hc0_ne1, ↓reduceIte]; exact ht)
                        rw [ha]; rfl
                      · have hb : w0.getD b false = true := hle b (by
                          change sem _ c1 = true; simp only [sem, h0b, hc1_ne1, ↓reduceIte]; exact ht)
                        rw [hb]; simp
  let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
    PEqualNP.MetaComplexity.Monotone2 C ∧
    (∀ p w : Fin 13, inc p w = true →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun q => q == p) (fun z => z == w)) = true) ∧
    (∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun q => q == a || q == b || q == c)
          (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false) ∧
    (∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
          (fun z => z == u || z == v || z == w)) = false)
  have hGood0 : Good C0 := by
    have h_app_eq : ∀ (P : Finset (Fin 13)) (px wx : Fin 13 → Bool),
        (∀ p : Fin 13, p ∈ P ↔ px p = true) →
        (∀ w : Fin 13, (∀ p ∈ P, inc p w = false) ↔ wx w = true) →
        (fun kk : Fin (13 + 13) => decide (
          (∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨
          (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧
            (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) =
        Fin.append px wx := by
      intro P px wx hpx hwx
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        rw [Fin.append_left]
        have hiff : ((∃ pp ∈ P, Fin.castAdd 13 i = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, Fin.castAdd 13 i = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)))) ↔
            px i = true := by
          constructor
          · intro h
            rcases h with ⟨pp, hpp, heq⟩ | ⟨ww, heq, _⟩
            · have hi : i = pp := Fin.castAdd_injective 13 13 heq
              rw [hi]; exact (hpx pp).mp hpp
            · exfalso
              have hv := congrArg Fin.val heq
              simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · intro hi; exact Or.inl ⟨i, (hpx i).mpr hi, rfl⟩
        cases hval : px i
        · refine decide_eq_false ?_
          intro h; have ht := hiff.mp h; rw [hval] at ht; exact Bool.noConfusion ht
        · exact decide_eq_true (hiff.mpr hval)
      · intro j
        rw [Fin.append_right]
        have hiff : ((∃ pp ∈ P, Fin.natAdd 13 j = Fin.castAdd 13 pp) ∨
            (∃ ww : Fin 13, Fin.natAdd 13 j = Fin.natAdd 13 ww ∧
              (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd)))) ↔
            wx j = true := by
          constructor
          · intro h
            rcases h with ⟨pp, _, heq⟩ | ⟨ww, heq, hww⟩
            · exfalso
              have hv := congrArg Fin.val heq
              simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
            · have hj : j = ww := Fin.natAdd_injective 13 13 heq
              rw [hj]
              apply (hwx ww).mp
              intro pp hpp
              cases hpw : inc pp ww
              · rfl
              · exfalso; exact hww pp hpp ((h_inc_iff pp ww).mpr hpw)
          · intro hj
            refine Or.inr ⟨j, rfl, fun pp hpp hinc => ?_⟩
            have hf := (hwx j).mpr hj pp hpp
            have ht := (h_inc_iff pp j).mp hinc
            rw [hf] at ht; exact Bool.noConfusion ht
        cases hval : wx j
        · refine decide_eq_false ?_
          intro h; have ht := hiff.mp h; rw [hval] at ht; exact Bool.noConfusion ht
        · exact decide_eq_true (hiff.mpr hval)
    refine ⟨hmono0, ?_, ?_, ?_⟩
    · intro p w hpw
      have hfun : (fun k : Fin (13 + 13) => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) =
          Fin.append (fun q => q == p) (fun z => z == w) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro i
          rw [Fin.append_left]
          by_cases hi : i = p
          · subst hi; simp
          · have h1 : ¬ (Fin.castAdd 13 i = Fin.castAdd 13 p ∨ Fin.castAdd 13 i = Fin.natAdd 13 w) := by
              intro h; rcases h with h1 | h2
              · exact hi (Fin.castAdd_injective 13 13 h1)
              · have hv := congrArg Fin.val h2
                simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
            rw [decide_eq_false h1]; simp [hi]
        · intro j
          rw [Fin.append_right]
          by_cases hj : j = w
          · subst hj; simp
          · have h1 : ¬ (Fin.natAdd 13 j = Fin.castAdd 13 p ∨ Fin.natAdd 13 j = Fin.natAdd 13 w) := by
              intro h; rcases h with h1 | h2
              · have hv := congrArg Fin.val h1
                simp only [Fin.val_natAdd, Fin.val_castAdd] at hv; omega
              · exact hj (Fin.natAdd_injective 13 13 h2)
            rw [decide_eq_false h1]; simp [hj]
      rw [← hfun]
      exact hpos0 p w ((h_inc_iff p w).mpr hpw)
    · intro a b c hnoncol
      have hnoncol0 : ∀ w : Fin 13,
          ¬ (inc 0 w = true ∧ inc (b - a) w = true ∧ inc (c - a) w = true) := by
        intro w h; rcases h with ⟨h0, hb, hc⟩
        apply hnoncol (w + a)
        have h1 := h_inc_shift 0 w a; rw [zero_add] at h1
        have h2 := h_inc_shift (b - a) w a; rw [sub_add_cancel] at h2
        have h3 := h_inc_shift (c - a) w a; rw [sub_add_cancel] at h3
        exact ⟨h1.trans h0, h2.trans hb, h3.trans hc⟩
      let P : Finset (Fin 13) := {a, b, c}
      have hPclosed : ∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd) := by
        intro v hv
        simp only [P, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
        have hv0 : v - a ≠ 0 := by intro h; exact hv.1 (sub_eq_zero.mp h)
        have hvb : v - a ≠ b - a := by intro h; exact hv.2.1 (by have := congrArg (· + a) h; simpa using this)
        have hvc : v - a ≠ c - a := by intro h; exact hv.2.2 (by have := congrArg (· + a) h; simpa using this)
        rcases h_tri_closed0 (b - a) (c - a) (v - a) hnoncol0 hv0 hvb hvc with ⟨w, h0, hb, hc, hvw⟩
        refine ⟨w + a, ?_, ?_⟩
        · intro pp hpp hinc
          have ht := (h_inc_iff pp (w + a)).mp hinc
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hpp
          rcases hpp with hpp | hpp | hpp
          · rw [hpp] at ht
            have h1 := h_inc_shift 0 w a; rw [zero_add] at h1
            rw [h1, h0] at ht; exact Bool.noConfusion ht
          · rw [hpp] at ht
            have h2 := h_inc_shift (b - a) w a; rw [sub_add_cancel] at h2
            rw [h2, hb] at ht; exact Bool.noConfusion ht
          · rw [hpp] at ht
            have h3 := h_inc_shift (c - a) w a; rw [sub_add_cancel] at h3
            rw [h3, hc] at ht; exact Bool.noConfusion ht
        · apply (h_inc_iff v (w + a)).mpr
          have h4 := h_inc_shift (v - a) w a; rw [sub_add_cancel] at h4
          exact h4.trans hvw
      have hPnoncol : ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd) := by
        intro h; rcases h with ⟨w3, hw3⟩
        exact hnoncol w3 ⟨(h_inc_iff a w3).mp (hw3 a (by simp [P])),
          (h_inc_iff b w3).mp (hw3 b (by simp [P])),
          (h_inc_iff c w3).mp (hw3 c (by simp [P]))⟩
      have hPnonconc : ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) →
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) := by
        intro h; rcases h with ⟨v4, hv4⟩
        rcases h_tri_nonconc0 (b - a) (c - a) (v4 - a) hnoncol0 with ⟨w, h0, hb, hc, hvw⟩
        have hmiss : ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = (w + a) + dd) := by
          intro pp hpp hinc
          have ht := (h_inc_iff pp (w + a)).mp hinc
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hpp
          rcases hpp with hpp | hpp | hpp
          · rw [hpp] at ht
            have h1 := h_inc_shift 0 w a; rw [zero_add] at h1
            rw [h1, h0] at ht; exact Bool.noConfusion ht
          · rw [hpp] at ht
            have h2 := h_inc_shift (b - a) w a; rw [sub_add_cancel] at h2
            rw [h2, hb] at ht; exact Bool.noConfusion ht
          · rw [hpp] at ht
            have h3 := h_inc_shift (c - a) w a; rw [sub_add_cancel] at h3
            rw [h3, hc] at ht; exact Bool.noConfusion ht
        have hinc := (h_inc_iff v4 (w + a)).mp (hv4 (w + a) hmiss)
        have h4 := h_inc_shift (v4 - a) w a; rw [sub_add_cancel] at h4
        rw [h4, hvw] at hinc; exact Bool.noConfusion hinc
      have hres := hneg0 P hPclosed ⟨hPnoncol, hPnonconc⟩
      have heq := h_app_eq P (fun q => q == a || q == b || q == c)
        (fun w => !(inc a w) && !(inc b w) && !(inc c w))
        (by intro p; simp only [P, Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq, or_assoc])
        (by
          intro w
          simp only [P, Finset.mem_insert, Finset.mem_singleton, Bool.and_eq_true, Bool.not_eq_true', and_assoc]
          constructor
          · intro h; exact ⟨h a (Or.inl rfl), h b (Or.inr (Or.inl rfl)), h c (Or.inr (Or.inr rfl))⟩
          · intro h p hp; rcases hp with rfl | rfl | rfl
            · exact h.1
            · exact h.2.1
            · exact h.2.2)
      rw [← heq]; exact hres
    · intro u v w hnonconc
      have hnonconc0 : ∀ p : Fin 13,
          ¬ (inc p 0 = true ∧ inc p (v - u) = true ∧ inc p (w - u) = true) := by
        intro p h; rcases h with ⟨h0, hv, hw⟩
        apply hnonconc (p + u)
        have h1 := h_inc_shift p 0 u; rw [zero_add] at h1
        have h2 := h_inc_shift p (v - u) u; rw [sub_add_cancel] at h2
        have h3 := h_inc_shift p (w - u) u; rw [sub_add_cancel] at h3
        exact ⟨h1.trans h0, h2.trans hv, h3.trans hw⟩
      let P : Finset (Fin 13) :=
        Finset.univ.filter (fun p : Fin 13 => !(inc p u) && !(inc p v) && !(inc p w))
      have hmemP : ∀ p : Fin 13, p ∈ P ↔ inc p u = false ∧ inc p v = false ∧ inc p w = false := by
        intro p
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
          Bool.and_eq_true, Bool.not_eq_true', and_assoc]
      have hmissW : ∀ z : Fin 13, (∀ p ∈ P, inc p z = false) ↔ z = u ∨ z = v ∨ z = w := by
        intro z
        constructor
        · intro hz
          have hz0 : ∀ p : Fin 13, inc p 0 = false → inc p (v - u) = false →
              inc p (w - u) = false → inc p (z - u) = false := by
            intro p h0 hv hw
            have hpP : p + u ∈ P := by
              apply (hmemP (p + u)).mpr
              have h1 := h_inc_shift p 0 u; rw [zero_add] at h1
              have h2 := h_inc_shift p (v - u) u; rw [sub_add_cancel] at h2
              have h3 := h_inc_shift p (w - u) u; rw [sub_add_cancel] at h3
              exact ⟨h1.trans h0, h2.trans hv, h3.trans hw⟩
            have h4 := h_inc_shift p (z - u) u; rw [sub_add_cancel] at h4
            exact h4.symm.trans (hz (p + u) hpP)
          have hdisj := h_dual_close0 (v - u) (w - u) (z - u) hnonconc0 hz0
          rcases hdisj with h1 | h2 | h3
          · exact Or.inl (sub_eq_zero.mp h1)
          · right; left; have := congrArg (· + u) h2; simpa using this
          · right; right; have := congrArg (· + u) h3; simpa using this
        · intro hz p hp
          have hp' := (hmemP p).mp hp
          rcases hz with rfl | rfl | rfl
          · exact hp'.1
          · exact hp'.2.1
          · exact hp'.2.2
      have hPclosed : ∀ q : Fin 13, q ∉ P → ∃ w2 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = w2 + dd) := by
        intro q hq
        have hq' : ¬ (inc q u = false ∧ inc q v = false ∧ inc q w = false) := by
          intro h; exact hq ((hmemP q).mpr h)
        cases hqu : inc q u
        · cases hqv : inc q v
          · cases hqw : inc q w
            · exfalso; exact hq' ⟨hqu, hqv, hqw⟩
            · refine ⟨w, fun pp hpp hinc => ?_, (h_inc_iff q w).mpr hqw⟩
              have ht := (h_inc_iff pp w).mp hinc
              rw [((hmemP pp).mp hpp).2.2] at ht; exact Bool.noConfusion ht
          · refine ⟨v, fun pp hpp hinc => ?_, (h_inc_iff q v).mpr hqv⟩
            have ht := (h_inc_iff pp v).mp hinc
            rw [((hmemP pp).mp hpp).2.1] at ht; exact Bool.noConfusion ht
        · refine ⟨u, fun pp hpp hinc => ?_, (h_inc_iff q u).mpr hqu⟩
          have ht := (h_inc_iff pp u).mp hinc
          rw [((hmemP pp).mp hpp).1] at ht; exact Bool.noConfusion ht
      have hPnoncol : ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd) := by
        intro h; rcases h with ⟨w3, hw3⟩
        rcases h_dual_noncol0 (v - u) (w - u) (w3 - u) hnonconc0 with ⟨p, h0, hv, hw, hpz⟩
        have hpP : p + u ∈ P := by
          apply (hmemP (p + u)).mpr
          have h1 := h_inc_shift p 0 u; rw [zero_add] at h1
          have h2 := h_inc_shift p (v - u) u; rw [sub_add_cancel] at h2
          have h3 := h_inc_shift p (w - u) u; rw [sub_add_cancel] at h3
          exact ⟨h1.trans h0, h2.trans hv, h3.trans hw⟩
        have ht := (h_inc_iff (p + u) w3).mp (hw3 (p + u) hpP)
        have h4 := h_inc_shift p (w3 - u) u; rw [sub_add_cancel] at h4
        rw [h4, hpz] at ht; exact Bool.noConfusion ht
      have hPnonconc : ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13,
          (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) →
          (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) := by
        intro h; rcases h with ⟨v4, hv4⟩
        have hmiss_of : ∀ z : Fin 13, (z = u ∨ z = v ∨ z = w) →
            ∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = z + dd) := by
          intro z hz pp hpp hinc
          have hf := (hmissW z).mpr hz pp hpp
          have ht := (h_inc_iff pp z).mp hinc
          rw [hf] at ht; exact Bool.noConfusion ht
        exact hnonconc v4 ⟨(h_inc_iff v4 u).mp (hv4 u (hmiss_of u (Or.inl rfl))),
          (h_inc_iff v4 v).mp (hv4 v (hmiss_of v (Or.inr (Or.inl rfl)))),
          (h_inc_iff v4 w).mp (hv4 w (hmiss_of w (Or.inr (Or.inr rfl))))⟩
      have hres := hneg0 P hPclosed ⟨hPnoncol, hPnonconc⟩
      have heq := h_app_eq P (fun p => !(inc p u) && !(inc p v) && !(inc p w))
        (fun z => z == u || z == v || z == w)
        (by intro p; simp only [P, Finset.mem_filter, Finset.mem_univ, true_and])
        (by intro z; rw [hmissW z]; simp only [Bool.or_eq_true, beq_iff_eq, or_assoc])
      rw [← heq]; exact hres
  clear hpos0 hneg0 hmono0 h_tri_closed0 h_tri_nonconc0 h_dual_close0 h_dual_noncol0 h_inc_iff
  -- Pass to a minimum-size Good circuit C
  classical
  have hexk : ∃ k : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit, Good C ∧ C.size = k :=
    ⟨C0.size, C0, hGood0, rfl⟩
  let kmin : ℕ := Nat.find hexk
  have hkmin_spec : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, Good C ∧ C.size = kmin :=
    Nat.find_spec hexk
  have hkmin_le63 : kmin ≤ 63 := Nat.le_trans (Nat.find_min' hexk ⟨C0, hGood0, rfl⟩) hsize0
  have hkmin_min : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, Good D → kmin ≤ D.size := by
    intro D hD; exact Nat.find_min' hexk ⟨D, hD, rfl⟩
  clear C0 hsize0 hGood0
  rcases hkmin_spec with ⟨C, hGoodC, hCsize⟩
  have hCmono : PEqualNP.MetaComplexity.Monotone2 C := hGoodC.1
  have hCpos : ∀ p w : Fin 13, inc p w = true →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun q => q == p) (fun z => z == w)) = true := hGoodC.2.1
  have hCtri : ∀ a b c : Fin 13, (∀ w : Fin 13, ¬ (inc a w = true ∧ inc b w = true ∧ inc c w = true)) →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun q => q == a || q == b || q == c)
          (fun w => !(inc a w) && !(inc b w) && !(inc c w))) = false := hGoodC.2.2.1
  have hCdual : ∀ u v w : Fin 13, (∀ p : Fin 13, ¬ (inc p u = true ∧ inc p v = true ∧ inc p w = true)) →
      PEqualNP.MetaComplexity.circuitFun (13 + 13) C
        (Fin.append (fun p => !(inc p u) && !(inc p v) && !(inc p w))
          (fun z => z == u || z == v || z == w)) = false := hGoodC.2.2.2
  let simStep : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let sem : List Bool → ℕ → Bool := fun w' c =>
    if c = 0 then false else if c = 1 then true else w'.getD (c - 2) false
  have h_and_eval2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have h_or_eval2 : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl
  have h_and_eval1 : ∀ a : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a] = a := by
    intro a; cases a <;> rfl
  have h_or_eval1 : ∀ a : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a] = a := by
    intro a; cases a <;> rfl
  have hCne : C.gates ≠ [] := by
    intro hnil
    have hev : ∀ px wx : Fin 13 → Bool,
        PEqualNP.MetaComplexity.circuitFun (13 + 13) C (Fin.append px wx) =
          (List.ofFn (Fin.append px wx)).getD C.output false := by
      intro px wx
      change ((C.gates.foldl simStep (List.ofFn (Fin.append px wx))).getD C.output false) = _
      rw [hnil]; rfl
    by_cases hout : C.output < 26
    · by_cases hp : C.output < 13
      · let p : Fin 13 := ⟨C.output, hp⟩
        have htrue := hCpos (p + 1) (p + 1) (by
          have h1 := h_inc_shift 0 0 (p + 1); rw [zero_add] at h1; rw [h1]; rfl)
        rw [hev] at htrue
        have hget : (List.ofFn (Fin.append (fun q : Fin 13 => q == p + 1)
            (fun z : Fin 13 => z == p + 1))).getD C.output false = (p == p + 1) := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
          have hfin : (⟨C.output, hout⟩ : Fin (13 + 13)) = Fin.castAdd 13 p := by ext; rfl
          rw [hfin, Fin.append_left]
        rw [hget] at htrue
        have hne : p ≠ p + 1 := by
          intro heq
          have h0 : (0 : Fin 13) = 1 := by have := congrArg (· - p) heq; simpa using this
          exact absurd h0 (by decide)
        simp [hne] at htrue
      · let w : Fin 13 := ⟨C.output - 13, by omega⟩
        have htrue := hCpos (w + 1) (w + 1) (by
          have h1 := h_inc_shift 0 0 (w + 1); rw [zero_add] at h1; rw [h1]; rfl)
        rw [hev] at htrue
        have hget : (List.ofFn (Fin.append (fun q : Fin 13 => q == w + 1)
            (fun z : Fin 13 => z == w + 1))).getD C.output false = (w == w + 1) := by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
          have hfin : (⟨C.output, hout⟩ : Fin (13 + 13)) = Fin.natAdd 13 w := by
            ext; simp only [Fin.val_natAdd, w]; omega
          rw [hfin, Fin.append_right]
        rw [hget] at htrue
        have hne : w ≠ w + 1 := by
          intro heq
          have h0 : (0 : Fin 13) = 1 := by have := congrArg (· - w) heq; simpa using this
          exact absurd h0 (by decide)
        simp [hne] at htrue
    · have htrue := hCpos 0 0 (by rfl)
      rw [hev] at htrue
      rw [List.getD_eq_default _ _ (by simp; omega)] at htrue
      exact Bool.noConfusion htrue
  cases hgates : C.gates with
  | nil => exact False.elim (hCne hgates)
  | cons g0 rest =>
    have hg0_mono : g0.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g0.inputs.length ≤ 2 :=
      hCmono g0 (by rw [hgates]; exact List.mem_cons_self ..)
    have hrest_mono : ∀ g ∈ rest, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} :
        Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hCmono g (by rw [hgates]; exact List.mem_cons_of_mem _ hg)
    have h_kill_g0 : ∀ (r0 : ℕ), r0 < 28 →
        (∀ p w : Fin 13, inc p w = true →
          let x := List.ofFn (Fin.append (fun q => q == p) (fun z => z == w))
          sem x r0 = g0.op.eval (g0.inputs.map fun i => x.getD i false)) →
        (∀ x : List Bool, x.length = 26 →
          sem x r0 = true → g0.op.eval (g0.inputs.map fun i => x.getD i false) = true) →
        False := by
      intro r0 hr0 heq_pos hle_all
      let m0 : List ℕ := (List.range 26).map (· + 2) ++ [r0]
      have hm0_len : m0.length = 27 := by simp [m0]
      have hm0_lt : ∀ c ∈ m0, c < 26 + ([] : List PEqualNP.CircuitLowerBounds.Gate).length + 2 := by
        intro c hc
        simp only [m0, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hc
        rcases hc with ⟨i, hi, rfl⟩ | rfl
        · simp; omega
        · simp; omega
      rcases h_pe_ind rest hrest_mono [] m0 (by simp) hm0_lt with
        ⟨gs1, m1, hgs1_len, hgs1_mono, _, heq1, hle1⟩
      let outC := m1.getD C.output 0
      have hbase_eq : ∀ p w : Fin 13, inc p w = true →
          let x := List.ofFn (Fin.append (fun q => q == p) (fun z => z == w))
          ∀ k : ℕ, sem x (m0.getD k 0) = (simStep x g0).getD k false := by
        intro p w hpw x k
        have hxlen : x.length = 26 := by simp [x]
        by_cases hk : k < 26
        · have hm0k : m0.getD k 0 = k + 2 := by
            rw [List.getD_eq_getElem _ _ (by omega)]; simp only [m0]
            rw [List.getElem_append_left (by simp; omega)]; simp
          rw [hm0k]
          have h0 : k + 2 ≠ 0 := by omega
          have h1 : k + 2 ≠ 1 := by omega
          simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel, simStep]
          rw [List.getD_eq_getElem (x ++ [_]) false (by simp; omega), List.getElem_append_left (by omega)]
          rw [List.getD_eq_getElem x false (by omega)]
        · by_cases hk2 : k = 26
          · subst hk2
            have hm0k : m0.getD 26 0 = r0 := by
              rw [List.getD_eq_getElem _ _ (by omega)]; simp only [m0]
              rw [List.getElem_append_right (by simp)]; simp
            rw [hm0k]; simp only [simStep]
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
            have hsub : 26 - x.length = 0 := by omega
            simp only [hsub, List.getElem_singleton]
            exact heq_pos p w hpw
          · rw [List.getD_eq_default _ _ (by omega)]
            simp only [simStep]; rw [List.getD_eq_default _ _ (by simp; omega)]; rfl
      have hbase_le : ∀ x : List Bool, x.length = 26 →
          ∀ k : ℕ, sem x (m0.getD k 0) = true → (simStep x g0).getD k false = true := by
        intro x hxlen k ht
        by_cases hk : k < 26
        · have hm0k : m0.getD k 0 = k + 2 := by
            rw [List.getD_eq_getElem _ _ (by omega)]; simp only [m0]
            rw [List.getElem_append_left (by simp; omega)]; simp
          rw [hm0k] at ht
          have h0 : k + 2 ≠ 0 := by omega
          have h1 : k + 2 ≠ 1 := by omega
          simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel] at ht
          simp only [simStep]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by omega),
            ← List.getD_eq_getElem x false (by omega)]
          exact ht
        · by_cases hk2 : k = 26
          · subst hk2
            have hm0k : m0.getD 26 0 = r0 := by
              rw [List.getD_eq_getElem _ _ (by omega)]; simp only [m0]
              rw [List.getElem_append_right (by simp)]; simp
            rw [hm0k] at ht; simp only [simStep]
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
            have hsub : 26 - x.length = 0 := by omega
            simp only [hsub, List.getElem_singleton]
            exact hle_all x hxlen ht
          · rw [List.getD_eq_default _ _ (by omega)] at ht; exact Bool.noConfusion ht
      have hCeval_eq : ∀ x : Fin (13 + 13) → Bool,
          PEqualNP.MetaComplexity.circuitFun (13 + 13) C x =
            (rest.foldl simStep (simStep (List.ofFn x) g0)).getD C.output false := by
        intro x
        change ((C.gates.foldl simStep (List.ofFn x)).getD C.output false) = _
        rw [hgates, List.foldl_cons]
      by_cases hout0 : outC = 0
      · have htrue := hCpos 0 0 (by rfl)
        rw [hCeval_eq] at htrue
        let x0 := List.ofFn (Fin.append (fun q : Fin 13 => q == 0) (fun z : Fin 13 => z == 0))
        have heq := heq1 x0 (simStep x0 g0) (by simp [x0]) (by simp [simStep, x0, hm0_len])
          (hbase_eq 0 0 (by rfl)) C.output
        change sem _ outC = _ at heq
        rw [hout0, htrue] at heq; exact Bool.noConfusion heq
      · by_cases hout1 : outC = 1
        · have hfalse := hCtri 0 1 2 h_noncol012
          rw [hCeval_eq] at hfalse
          let xtri := List.ofFn (Fin.append (fun q : Fin 13 => q == 0 || q == 1 || q == 2)
            (fun w : Fin 13 => !(inc 0 w) && !(inc 1 w) && !(inc 2 w)))
          have hle := hle1 xtri (simStep xtri g0) (by simp [xtri]) (by simp [simStep, xtri, hm0_len])
            (hbase_le xtri (by simp [xtri])) C.output
          have ht : sem (gs1.foldl simStep xtri) outC = true := by rw [hout1]; rfl
          have htrue := hle ht
          rw [hfalse] at htrue; exact Bool.noConfusion htrue
        · let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := gs1, output := outC - 2 }
          have hDgood : Good D := by
            refine ⟨hgs1_mono, ?_, ?_, ?_⟩
            · intro p w hpw
              let x := List.ofFn (Fin.append (fun q : Fin 13 => q == p) (fun z : Fin 13 => z == w))
              have heq := heq1 x (simStep x g0) (by simp [x]) (by simp [simStep, x, hm0_len])
                (hbase_eq p w hpw) C.output
              change sem (gs1.foldl simStep x) outC = _ at heq
              simp only [sem, hout0, hout1, ↓reduceIte] at heq
              change (gs1.foldl simStep x).getD (outC - 2) false = true
              rw [heq, ← hCeval_eq]; exact hCpos p w hpw
            · intro a b c hnoncol
              let f := Fin.append (fun q : Fin 13 => q == a || q == b || q == c)
                (fun w : Fin 13 => !(inc a w) && !(inc b w) && !(inc c w))
              let x := List.ofFn f
              cases hval : PEqualNP.MetaComplexity.circuitFun (13 + 13) D f
              · rfl
              · exfalso
                have hle := hle1 x (simStep x g0) (by simp [x]) (by simp [simStep, x, hm0_len])
                  (hbase_le x (by simp [x])) C.output
                have ht : sem (gs1.foldl simStep x) outC = true := by
                  simp only [sem, hout0, hout1, ↓reduceIte]; exact hval
                have htrue := hle ht
                rw [← hCeval_eq f, hCtri a b c hnoncol] at htrue
                exact Bool.noConfusion htrue
            · intro u v w hnonconc
              let f := Fin.append (fun p : Fin 13 => !(inc p u) && !(inc p v) && !(inc p w))
                (fun z : Fin 13 => z == u || z == v || z == w)
              let x := List.ofFn f
              cases hval : PEqualNP.MetaComplexity.circuitFun (13 + 13) D f
              · rfl
              · exfalso
                have hle := hle1 x (simStep x g0) (by simp [x]) (by simp [simStep, x, hm0_len])
                  (hbase_le x (by simp [x])) C.output
                have ht : sem (gs1.foldl simStep x) outC = true := by
                  simp only [sem, hout0, hout1, ↓reduceIte]; exact hval
                have htrue := hle ht
                rw [← hCeval_eq f, hCdual u v w hnonconc] at htrue
                exact Bool.noConfusion htrue
          have hDlt : D.size < kmin := by
            have h1 : D.size = gs1.length := rfl
            have h2 : C.size = rest.length + 1 := by
              change C.gates.length = rest.length + 1; rw [hgates]; simp
            have h3 : gs1.length ≤ rest.length := by simpa using hgs1_len
            omega
          have hge := hkmin_min D hDgood
          omega
    -- Step 1: Analyze g0 using h_kill_g0
    have hg0_op : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g0.op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hg0_mono.1
    have hg0_len : g0.inputs.length ≤ 2 := hg0_mono.2
    have h_g0_form : ∃ (a b : ℕ), g0.inputs = [a, b] ∧ a < 26 ∧ b < 26 ∧ a ≠ b := by
      cases hin : g0.inputs with
      | nil =>
        rcases hg0_op with hop | hop
        · exfalso; exact h_kill_g0 1 (by omega)
            (fun _ _ _ => by rw [hop, hin]; rfl) (fun _ _ _ => by rw [hop, hin]; rfl)
        · exfalso; exact h_kill_g0 0 (by omega)
            (fun _ _ _ => by rw [hop, hin]; rfl) (fun _ _ ht => Bool.noConfusion ht)
      | cons a tl =>
        cases tl with
        | nil =>
          exfalso
          by_cases ha : a < 26
          · exact h_kill_g0 (a + 2) (by omega)
              (fun p w _ => by
                have h0 : a + 2 ≠ 0 := by omega
                have h1 : a + 2 ≠ 1 := by omega
                simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel, hin, List.map_cons, List.map_nil]
                rcases hg0_op with hop | hop
                · rw [hop, h_and_eval1]
                · rw [hop, h_or_eval1])
              (fun x _ ht => by
                have h0 : a + 2 ≠ 0 := by omega
                have h1 : a + 2 ≠ 1 := by omega
                simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel] at ht
                rw [hin, List.map_cons, List.map_nil]
                rcases hg0_op with hop | hop
                · rw [hop, h_and_eval1]; exact ht
                · rw [hop, h_or_eval1]; exact ht)
          · exact h_kill_g0 0 (by omega)
              (fun p w _ => by
                simp only [sem, ↓reduceIte, hin, List.map_cons, List.map_nil]
                have hdef : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                    (fun z : Fin 13 => z == w))).getD a false = false :=
                  List.getD_eq_default _ _ (by simp; omega)
                rw [hdef]
                rcases hg0_op with hop | hop <;> (rw [hop]; rfl))
              (fun _ _ ht => Bool.noConfusion ht)
        | cons b tl2 =>
          cases tl2 with
          | cons _ _ => rw [hin] at hg0_len; simp at hg0_len
          | nil =>
            have ha : a < 26 := by
              by_contra ha
              rcases hg0_op with hop | hop
              · exact h_kill_g0 0 (by omega)
                  (fun p w _ => by
                    simp only [sem, ↓reduceIte, hin, List.map_cons, List.map_nil, hop, h_and_eval2]
                    have hdef : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                        (fun z : Fin 13 => z == w))).getD a false = false :=
                      List.getD_eq_default _ _ (by simp; omega)
                    rw [hdef]; rfl)
                  (fun _ _ ht => Bool.noConfusion ht)
              · by_cases hb : b < 26
                · exact h_kill_g0 (b + 2) (by omega)
                    (fun p w _ => by
                      have h0 : b + 2 ≠ 0 := by omega
                      have h1 : b + 2 ≠ 1 := by omega
                      simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel, hin,
                        List.map_cons, List.map_nil, hop, h_or_eval2]
                      have hdef : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                          (fun z : Fin 13 => z == w))).getD a false = false :=
                        List.getD_eq_default _ _ (by simp; omega)
                      rw [hdef]; rfl)
                    (fun x _ ht => by
                      have h0 : b + 2 ≠ 0 := by omega
                      have h1 : b + 2 ≠ 1 := by omega
                      simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel] at ht
                      rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or_eval2, ht]; simp)
                · exact h_kill_g0 0 (by omega)
                    (fun p w _ => by
                      simp only [sem, ↓reduceIte, hin, List.map_cons, List.map_nil, hop, h_or_eval2]
                      have hda : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                          (fun z : Fin 13 => z == w))).getD a false = false :=
                        List.getD_eq_default _ _ (by simp; omega)
                      have hdb : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                          (fun z : Fin 13 => z == w))).getD b false = false :=
                        List.getD_eq_default _ _ (by simp; omega)
                      rw [hda, hdb]; rfl)
                    (fun _ _ ht => Bool.noConfusion ht)
            have hb : b < 26 := by
              by_contra hb
              rcases hg0_op with hop | hop
              · exact h_kill_g0 0 (by omega)
                  (fun p w _ => by
                    simp only [sem, ↓reduceIte, hin, List.map_cons, List.map_nil, hop, h_and_eval2]
                    have hdef : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                        (fun z : Fin 13 => z == w))).getD b false = false :=
                      List.getD_eq_default _ _ (by simp; omega)
                    rw [hdef]; simp)
                  (fun _ _ ht => Bool.noConfusion ht)
              · exact h_kill_g0 (a + 2) (by omega)
                  (fun p w _ => by
                    have h0 : a + 2 ≠ 0 := by omega
                    have h1 : a + 2 ≠ 1 := by omega
                    simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel, hin,
                      List.map_cons, List.map_nil, hop, h_or_eval2]
                    have hdef : (List.ofFn (Fin.append (fun q : Fin 13 => q == p)
                        (fun z : Fin 13 => z == w))).getD b false = false :=
                      List.getD_eq_default _ _ (by simp; omega)
                    rw [hdef]; simp)
                  (fun x _ ht => by
                    have h0 : a + 2 ≠ 0 := by omega
                    have h1 : a + 2 ≠ 1 := by omega
                    simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel] at ht
                    rw [hin, List.map_cons, List.map_cons, List.map_nil, hop, h_or_eval2, ht]; rfl)
            have hab : a ≠ b := by
              intro heq; subst heq
              exact h_kill_g0 (a + 2) (by omega)
                (fun p w _ => by
                  have h0 : a + 2 ≠ 0 := by omega
                  have h1 : a + 2 ≠ 1 := by omega
                  simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel, hin, List.map_cons, List.map_nil]
                  rcases hg0_op with hop | hop
                  · rw [hop, h_and_eval2, Bool.and_self]
                  · rw [hop, h_or_eval2, Bool.or_self])
                (fun x _ ht => by
                  have h0 : a + 2 ≠ 0 := by omega
                  have h1 : a + 2 ≠ 1 := by omega
                  simp only [sem, h0, h1, ↓reduceIte, Nat.add_sub_cancel] at ht
                  rw [hin, List.map_cons, List.map_cons, List.map_nil]
                  rcases hg0_op with hop | hop
                  · rw [hop, h_and_eval2, ht]; rfl
                  · rw [hop, h_or_eval2, ht]; rfl)
            exact ⟨a, b, rfl, ha, hb, hab⟩
    rcases h_g0_form with ⟨a, b, hg0_in, ha26, hb26, hab⟩
    have h_get_append_lt : ∀ (px wx : Fin 13 → Bool) (k : ℕ) (hk : k < 13),
        (List.ofFn (Fin.append px wx)).getD k false = px ⟨k, hk⟩ := by
      intro px wx k hk
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      have hfin : (⟨k, by omega⟩ : Fin (13 + 13)) = Fin.castAdd 13 ⟨k, hk⟩ := by ext; rfl
      rw [hfin, Fin.append_left]
    have h_get_append_ge : ∀ (px wx : Fin 13 → Bool) (k : ℕ) (hk1 : 13 ≤ k) (hk2 : k < 26),
        (List.ofFn (Fin.append px wx)).getD k false = wx ⟨k - 13, by omega⟩ := by
      intro px wx k hk1 hk2
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      have hfin : (⟨k, hk2⟩ : Fin (13 + 13)) = Fin.natAdd 13 ⟨k - 13, by omega⟩ := by
        ext; simp only [Fin.val_natAdd]; omega
      rw [hfin, Fin.append_right]
    have h_swap_g0 : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (op : PEqualNP.CircuitLowerBounds.GateOp)
        (u v : ℕ) (tl : List PEqualNP.CircuitLowerBounds.Gate),
        (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        Good D → D.size ≤ 63 →
        D.gates = { op := op, inputs := [u, v] } :: tl →
        ∃ D' : PEqualNP.CircuitLowerBounds.Circuit,
          Good D' ∧ D'.size ≤ 63 ∧ D'.gates.head? = some { op := op, inputs := [v, u] } := by
      intro D op u v tl hop hGD hDs hDg
      let D' : PEqualNP.CircuitLowerBounds.Circuit :=
        { gates := { op := op, inputs := [v, u] } :: tl, output := D.output }
      have hev : ∀ x : Fin (13 + 13) → Bool,
          PEqualNP.MetaComplexity.circuitFun (13 + 13) D' x =
            PEqualNP.MetaComplexity.circuitFun (13 + 13) D x := by
        intro x
        change ((({ op := op, inputs := [v, u] } :: tl).foldl simStep (List.ofFn x)).getD D.output false) =
          ((D.gates.foldl simStep (List.ofFn x)).getD D.output false)
        rw [hDg, List.foldl_cons, List.foldl_cons]
        have hs : simStep (List.ofFn x) { op := op, inputs := [v, u] } =
            simStep (List.ofFn x) { op := op, inputs := [u, v] } := by
          simp only [simStep, List.map_cons, List.map_nil]
          rcases hop with rfl | rfl
          · rw [h_and_eval2, h_and_eval2, Bool.and_comm]
          · rw [h_or_eval2, h_or_eval2, Bool.or_comm]
        rw [hs]
      refine ⟨D', ⟨?_, ?_, ?_, ?_⟩, ?_, rfl⟩
      · intro g hg
        simp only [D', List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨by rcases hop with rfl | rfl <;> simp, by simp⟩
        · exact hGD.1 g (by rw [hDg]; exact List.mem_cons_of_mem _ hg)
      · intro p w hpw; rw [hev]; exact hGD.2.1 p w hpw
      · intro a1 b1 c1 hnc; rw [hev]; exact hGD.2.2.1 a1 b1 c1 hnc
      · intro u1 v1 w1 hnc; rw [hev]; exact hGD.2.2.2 u1 v1 w1 hnc
      · change ({ op := op, inputs := [v, u] } :: tl).length ≤ 63
        have hlen : D.gates.length ≤ 63 := hDs
        rw [hDg] at hlen; simpa using hlen
    let mapWire : (Fin 26 → Fin 26) → ℕ → ℕ := fun π k =>
      if h : k < 26 then (π ⟨k, h⟩).val else k
    let mapGate : (Fin 26 → Fin 26) → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun π g => { op := g.op, inputs := g.inputs.map (mapWire π) }
    let permCircuit : (Fin 26 → Fin 26) → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Circuit :=
      fun π D => { gates := D.gates.map (mapGate π), output := mapWire π D.output }
    have h_perm_eval : ∀ (π : Fin 26 → Fin 26) (D : PEqualNP.CircuitLowerBounds.Circuit)
        (x : Fin (13 + 13) → Bool),
        PEqualNP.MetaComplexity.circuitFun (13 + 13) (permCircuit π D) x =
          PEqualNP.MetaComplexity.circuitFun (13 + 13) D (fun i => x (π i)) := by
      have h_pw : ∀ (π : Fin 26 → Fin 26) (gs : List PEqualNP.CircuitLowerBounds.Gate)
          (w1 w2 : List Bool), w1.length = w2.length → 26 ≤ w1.length →
          (∀ k : ℕ, k < 26 → w1.getD (mapWire π k) false = w2.getD k false) →
          (∀ k : ℕ, 26 ≤ k → w1.getD k false = w2.getD k false) →
          ∀ k : ℕ, ((gs.map (mapGate π)).foldl simStep w1).getD (mapWire π k) false =
            (gs.foldl simStep w2).getD k false := by
        intro π gs
        induction gs with
        | nil =>
          intro w1 w2 _ _ hlt hge k
          simp only [List.map_nil, List.foldl_nil]
          by_cases hk : k < 26
          · exact hlt k hk
          · have hm : mapWire π k = k := by simp [mapWire, hk]
            rw [hm]; exact hge k (by omega)
        | cons g tl ih =>
          intro w1 w2 hlen h26 hlt hge
          simp only [List.map_cons, List.foldl_cons]
          have heval_g : (mapGate π g).op.eval ((mapGate π g).inputs.map fun i => w1.getD i false) =
              g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            simp only [mapGate, List.map_map]
            congr 1; apply List.map_congr_left
            intro i _
            by_cases hi : i < 26
            · exact hlt i hi
            · have hm : mapWire π i = i := by simp [mapWire, hi]
              simp only [Function.comp_apply, hm]; exact hge i (by omega)
          refine ih (simStep w1 (mapGate π g)) (simStep w2 g)
            (by simp [simStep, hlen]) (by simp [simStep]; omega) ?_ ?_
          · intro k hk
            have hmk : mapWire π k < 26 := by simp [mapWire, hk]
            simp only [simStep]
            rw [List.getD_eq_getElem (w1 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega),
              ← List.getD_eq_getElem w1 false (by omega)]
            rw [List.getD_eq_getElem (w2 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega),
              ← List.getD_eq_getElem w2 false (by omega)]
            exact hlt k hk
          · intro k hk
            by_cases hkl : k < w1.length
            · simp only [simStep]
              rw [List.getD_eq_getElem (w1 ++ [_]) false (by simp; omega), List.getElem_append_left hkl,
                ← List.getD_eq_getElem w1 false hkl]
              rw [List.getD_eq_getElem (w2 ++ [_]) false (by simp; omega), List.getElem_append_left (by omega),
                ← List.getD_eq_getElem w2 false (by omega)]
              exact hge k hk
            · by_cases hke : k = w1.length
              · subst hke; simp only [simStep]
                rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
                simp only [Nat.sub_self, List.getElem_singleton]
                rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
                have hsub : w1.length - w2.length = 0 := by omega
                simp only [hsub, List.getElem_singleton]; exact heval_g
              · simp only [simStep]
                rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      intro π D x
      change (((D.gates.map (mapGate π)).foldl simStep (List.ofFn x)).getD (mapWire π D.output) false) =
        ((D.gates.foldl simStep (List.ofFn (fun i => x (π i)))).getD D.output false)
      refine h_pw π D.gates (List.ofFn x) (List.ofFn (fun i => x (π i))) (by simp) (by simp) ?_ ?_ D.output
      · intro k hk
        have hmk : mapWire π k = (π ⟨k, hk⟩).val := by simp [mapWire, hk]
        rw [hmk, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      · intro k hk
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    let affMap : Fin 13 → Fin 13 → Fin 26 → Fin 26 := fun m t k =>
      if h : k.val < 13 then Fin.castAdd 13 (m * ⟨k.val, h⟩ + t)
      else Fin.natAdd 13 (m * ⟨k.val - 13, by omega⟩ + t)
    have h_aff_good : ∀ (m t : Fin 13), (m = 1 ∨ m = 3 ∨ m = 9) →
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit, Good D → D.size ≤ 63 →
        Good (permCircuit (affMap m t) D) ∧ (permCircuit (affMap m t) D).size ≤ 63 := by
      intro m t hm D hGD hDs
      let mi : Fin 13 := if m = 1 then 1 else if m = 3 then 9 else 3
      have hmul_inv : ∀ x : Fin 13, m * (mi * x) = x := by
        rcases hm with rfl | rfl | rfl
        · intro x; simp [mi]
        · intro x; change 3 * (9 * x) = x; rw [← mul_assoc]; have : (3 : Fin 13) * 9 = 1 := by decide
          rw [this, one_mul]
        · intro x; change 9 * (3 * x) = x; rw [← mul_assoc]; have : (9 : Fin 13) * 3 = 1 := by decide
          rw [this, one_mul]
      have hmul_inv2 : ∀ x : Fin 13, mi * (m * x) = x := by
        rcases hm with rfl | rfl | rfl
        · intro x; simp [mi]
        · intro x; change 9 * (3 * x) = x; rw [← mul_assoc]; have : (9 : Fin 13) * 3 = 1 := by decide
          rw [this, one_mul]
        · intro x; change 3 * (9 * x) = x; rw [← mul_assoc]; have : (3 : Fin 13) * 9 = 1 := by decide
          rw [this, one_mul]
      have h_aff_pull : ∀ (px wx : Fin 13 → Bool),
          (fun i : Fin (13 + 13) => Fin.append px wx (affMap m t i)) =
            Fin.append (fun q => px (m * q + t)) (fun z => wx (m * z + t)) := by
        intro px wx; funext i
        refine Fin.addCases ?_ ?_ i
        · intro q; rw [Fin.append_left]
          have hlt : (Fin.castAdd 13 q).val < 13 := q.isLt
          have hmap : affMap m t (Fin.castAdd 13 q) = Fin.castAdd 13 (m * q + t) := by
            simp only [affMap, hlt, ↓reduceDIte]; rfl
          rw [hmap, Fin.append_left]
        · intro z; rw [Fin.append_right]
          have hge : ¬ (Fin.natAdd 13 z).val < 13 := by simp
          have hmap : affMap m t (Fin.natAdd 13 z) = Fin.natAdd 13 (m * z + t) := by
            simp only [affMap, hge, ↓reduceDIte]; congr 1; ext; simp
          rw [hmap, Fin.append_right]
      have h_eq_pull : ∀ (a x : Fin 13), (m * x + t == a) = (x == mi * (a - t)) := by
        intro a x; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        constructor
        · intro h; have h1 : m * x = a - t := by rw [← h, add_sub_cancel_right]
          have h2 := congrArg (mi * ·) h1; rw [hmul_inv2] at h2; exact h2
        · intro h; rw [h, hmul_inv, sub_add_cancel]
      have h_inc_pull : ∀ (a w : Fin 13), inc a (m * w + t) = inc (mi * (a - t)) w := by
        intro a w; rw [← h_inc_mul m hm (mi * (a - t)) w, hmul_inv]
        have h1 := h_inc_shift (a - t) (m * w) t; rw [sub_add_cancel] at h1; exact h1
      have h_inc_pull2 : ∀ (p u : Fin 13), inc (m * p + t) u = inc p (mi * (u - t)) := by
        intro p u; rw [← h_inc_mul m hm p (mi * (u - t)), hmul_inv]
        have h1 := h_inc_shift (m * p) (u - t) t; rw [sub_add_cancel] at h1; exact h1
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro g hg
        simp only [permCircuit, List.mem_map] at hg
        rcases hg with ⟨g', hg', rfl⟩
        have hm' := hGD.1 g' hg'; exact ⟨hm'.1, by simp [mapGate, hm'.2]⟩
      · intro p w hpw
        rw [h_perm_eval, h_aff_pull]
        have hfun : Fin.append (fun q => m * q + t == p) (fun z => m * z + t == w) =
            Fin.append (fun q => q == mi * (p - t)) (fun z => z == mi * (w - t)) := by
          congr 1 <;> funext x <;> exact h_eq_pull _ x
        rw [hfun]; apply hGD.2.1
        rw [← h_inc_mul m hm, hmul_inv, hmul_inv]
        have h1 := h_inc_shift (p - t) (w - t) t
        rw [sub_add_cancel, sub_add_cancel] at h1; exact h1.symm.trans hpw
      · intro a1 b1 c1 hnc
        rw [h_perm_eval, h_aff_pull]
        have hfun : Fin.append (fun q => m * q + t == a1 || m * q + t == b1 || m * q + t == c1)
            (fun w => !(inc a1 (m * w + t)) && !(inc b1 (m * w + t)) && !(inc c1 (m * w + t))) =
            Fin.append (fun q => q == mi * (a1 - t) || q == mi * (b1 - t) || q == mi * (c1 - t))
            (fun w => !(inc (mi * (a1 - t)) w) && !(inc (mi * (b1 - t)) w) && !(inc (mi * (c1 - t)) w)) := by
          congr 1
          · funext q; rw [h_eq_pull, h_eq_pull, h_eq_pull]
          · funext w; rw [h_inc_pull, h_inc_pull, h_inc_pull]
        rw [hfun]; apply hGD.2.2.1
        intro w h; apply hnc (m * w + t); rw [h_inc_pull, h_inc_pull, h_inc_pull]; exact h
      · intro u1 v1 w1 hnc
        rw [h_perm_eval, h_aff_pull]
        have hfun : Fin.append (fun p => !(inc (m * p + t) u1) && !(inc (m * p + t) v1) && !(inc (m * p + t) w1))
            (fun z => m * z + t == u1 || m * z + t == v1 || m * z + t == w1) =
            Fin.append (fun p => !(inc p (mi * (u1 - t))) && !(inc p (mi * (v1 - t))) && !(inc p (mi * (w1 - t))))
            (fun z => z == mi * (u1 - t) || z == mi * (v1 - t) || z == mi * (w1 - t)) := by
          congr 1
          · funext p; rw [h_inc_pull2, h_inc_pull2, h_inc_pull2]
          · funext z; rw [h_eq_pull, h_eq_pull, h_eq_pull]
        rw [hfun]; apply hGD.2.2.2
        intro p h; apply hnc (m * p + t); rw [h_inc_pull2, h_inc_pull2, h_inc_pull2]; exact h
      · change (D.gates.map (mapGate (affMap m t))).length ≤ 63; have hDs' : D.gates.length ≤ 63 := hDs; simpa using hDs'
    let dualMap : Fin 26 → Fin 26 := fun k =>
      if h : k.val < 13 then Fin.natAdd 13 (-⟨k.val, h⟩)
      else Fin.castAdd 13 (-⟨k.val - 13, by omega⟩)
    have h_dual_good : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, Good D → D.size ≤ 63 →
        Good (permCircuit dualMap D) ∧ (permCircuit dualMap D).size ≤ 63 := by
      intro D hGD hDs
      have h_dual_pull : ∀ (px wx : Fin 13 → Bool),
          (fun i : Fin (13 + 13) => Fin.append px wx (dualMap i)) =
            Fin.append (fun q => wx (-q)) (fun z => px (-z)) := by
        intro px wx; funext i
        refine Fin.addCases ?_ ?_ i
        · intro q; rw [Fin.append_left]
          have hlt : (Fin.castAdd 13 q).val < 13 := q.isLt
          have hmap : dualMap (Fin.castAdd 13 q) = Fin.natAdd 13 (-q) := by
            simp only [dualMap, hlt, ↓reduceDIte]; rfl
          rw [hmap, Fin.append_right]
        · intro z; rw [Fin.append_right]
          have hge : ¬ (Fin.natAdd 13 z).val < 13 := by simp
          have hmap : dualMap (Fin.natAdd 13 z) = Fin.castAdd 13 (-z) := by
            simp only [dualMap, hge, ↓reduceDIte]; congr 1; ext; simp
          rw [hmap, Fin.append_left]
      have h_neg_beq : ∀ (a x : Fin 13), (-x == a) = (x == -a) := by
        intro a x; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]
        exact neg_eq_iff_eq_neg
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro g hg
        simp only [permCircuit, List.mem_map] at hg
        rcases hg with ⟨g', hg', rfl⟩
        have hm' := hGD.1 g' hg'; exact ⟨hm'.1, by simp [mapGate, hm'.2]⟩
      · intro p w hpw
        rw [h_perm_eval, h_dual_pull]
        have hfun : Fin.append (fun q => -q == w) (fun z => -z == p) =
            Fin.append (fun q => q == -w) (fun z => z == -p) := by
          congr 1 <;> funext x <;> exact h_neg_beq _ x
        rw [hfun]; apply hGD.2.1; rw [h_inc_dual]; exact hpw
      · intro a1 b1 c1 hnc
        rw [h_perm_eval, h_dual_pull]
        have hfun : Fin.append (fun q => !(inc a1 (-q)) && !(inc b1 (-q)) && !(inc c1 (-q)))
            (fun z => -z == a1 || -z == b1 || -z == c1) =
            Fin.append (fun q => !(inc q (-a1)) && !(inc q (-b1)) && !(inc q (-c1)))
            (fun z => z == -a1 || z == -b1 || z == -c1) := by
          congr 1
          · funext q
            have h1 := h_inc_dual q (-a1); rw [neg_neg] at h1
            have h2 := h_inc_dual q (-b1); rw [neg_neg] at h2
            have h3 := h_inc_dual q (-c1); rw [neg_neg] at h3
            rw [h1, h2, h3]
          · funext z; rw [h_neg_beq, h_neg_beq, h_neg_beq]
        rw [hfun]; apply hGD.2.2.2
        intro p h; apply hnc (-p)
        have h1 := h_inc_dual p (-a1); rw [neg_neg] at h1
        have h2 := h_inc_dual p (-b1); rw [neg_neg] at h2
        have h3 := h_inc_dual p (-c1); rw [neg_neg] at h3
        rw [h1, h2, h3]; exact h
      · intro u1 v1 w1 hnc
        rw [h_perm_eval, h_dual_pull]
        have hfun : Fin.append (fun q => -q == u1 || -q == v1 || -q == w1)
            (fun z => !(inc (-z) u1) && !(inc (-z) v1) && !(inc (-z) w1)) =
            Fin.append (fun q => q == -u1 || q == -v1 || q == -w1)
            (fun z => !(inc (-u1) z) && !(inc (-v1) z) && !(inc (-w1) z)) := by
          congr 1
          · funext q; rw [h_neg_beq, h_neg_beq, h_neg_beq]
          · funext z
            have h1 := h_inc_dual (-u1) z; rw [neg_neg] at h1
            have h2 := h_inc_dual (-v1) z; rw [neg_neg] at h2
            have h3 := h_inc_dual (-w1) z; rw [neg_neg] at h3
            rw [h1, h2, h3]
        rw [hfun]; apply hGD.2.2.1
        intro w h; apply hnc (-w)
        have h1 := h_inc_dual (-u1) w; rw [neg_neg] at h1
        have h2 := h_inc_dual (-v1) w; rw [neg_neg] at h2
        have h3 := h_inc_dual (-w1) w; rw [neg_neg] at h3
        rw [h1, h2, h3]; exact h
      · change (D.gates.map (mapGate dualMap)).length ≤ 63; have hDs' : D.gates.length ≤ 63 := hDs; simpa using hDs'
    have h_norm_cross : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (p w : Fin 13)
        (m : Fin 13), (m = 1 ∨ m = 3 ∨ m = 9) →
        ∀ D : PEqualNP.CircuitLowerBounds.Circuit, Good D → D.size ≤ 63 →
        D.gates.head? = some { op := op, inputs := [p.val, 13 + w.val] } →
        ∃ D' : PEqualNP.CircuitLowerBounds.Circuit,
          Good D' ∧ D'.size ≤ 63 ∧
          D'.gates.head? = some { op := op, inputs := [(m * (p - w)).val, 13] } := by
      intro op p w m hm D hGD hDs hhead
      let D' := permCircuit (affMap m (-(m * w))) D
      have hres := h_aff_good m (-(m * w)) hm D hGD hDs
      refine ⟨D', hres.1, hres.2, ?_⟩
      cases hDg : D.gates with
      | nil => rw [hDg] at hhead; simp at hhead
      | cons g1 tl =>
        rw [hDg] at hhead; simp only [List.head?_cons] at hhead
        have hg1 : g1 = { op := op, inputs := [p.val, 13 + w.val] } := Option.some.inj hhead
        simp only [D', permCircuit, hDg, List.map_cons, List.head?_cons, hg1, mapGate,
          List.map_cons, List.map_nil]
        simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]
        constructor
        · have hp26 : p.val < 26 := by omega
          have hp13 : p.val < 13 := p.isLt
          simp only [mapWire, hp26, ↓reduceDIte, affMap, hp13, Fin.val_castAdd]
          have hsub : m * p + -(m * w) = m * (p - w) := by rw [← sub_eq_add_neg, mul_sub]
          exact congrArg Fin.val hsub
        · have hw26 : 13 + w.val < 26 := by omega
          have hw13 : ¬ (13 + w.val < 13) := by omega
          simp only [mapWire, hw26, ↓reduceDIte, affMap, hw13, Fin.val_natAdd]
          have hfin : (⟨13 + w.val - 13, by omega⟩ : Fin 13) = w := by ext; simp
          rw [hfin, add_neg_cancel]; rfl
    have hCsize63 : C.size ≤ 63 := by omega
    have hCg0 : C.gates = { op := g0.op, inputs := [a, b] } :: rest := by
      rw [hgates]; cases g0; simp only at hg0_in; rw [hg0_in]
    rcases hg0_op with hop | hop
    · by_cases ha13 : a < 13
      · by_cases hb13 : b < 13
        · exfalso
          exact h_kill_g0 0 (by omega)
            (fun p w _ => by
              simp only [sem, ↓reduceIte, hg0_in, List.map_cons, List.map_nil, hop, h_and_eval2]
              rw [h_get_append_lt _ _ a ha13, h_get_append_lt _ _ b hb13]
              by_cases hap : (⟨a, ha13⟩ : Fin 13) = p
              · have hbp : (⟨b, hb13⟩ : Fin 13) ≠ p := by
                  intro h; apply hab
                  have h1 := congrArg Fin.val hap; have h2 := congrArg Fin.val h; dsimp only at h1 h2; omega
                simp [hbp]
              · simp [hap])
            (fun _ _ ht => Bool.noConfusion ht)
        · let p0 : Fin 13 := ⟨a, ha13⟩
          let w0 : Fin 13 := ⟨b - 13, by omega⟩
          by_cases hinc0 : inc p0 w0 = true
          · have hinc_sub : inc (p0 - w0) 0 = true := by
              have h := h_inc_shift (p0 - w0) 0 w0; rw [sub_add_cancel, zero_add] at h
              exact h.symm.trans hinc0
            rcases h_orb_inc (p0 - w0) hinc_sub with ⟨m, hm, hd⟩
            have hheadC : C.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p0.val, 13 + w0.val] } := by
              rw [hCg0, hop]; simp only [List.head?_cons, p0, w0]; simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]; omega
            rcases h_norm_cross PEqualNP.CircuitLowerBounds.GateOp.and p0 w0 m hm C hGoodC hCsize63 hheadC
              with ⟨D', hGD', hDs', hDh'⟩
            rcases hd with hd0 | hd1
            · rw [hd0] at hDh'
              exact h_and_inc 0 (Or.inl rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
            · rw [hd1] at hDh'
              exact h_and_inc 1 (Or.inr rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
          · exfalso
            exact h_kill_g0 0 (by omega)
              (fun p w hpw => by
                simp only [sem, ↓reduceIte, hg0_in, List.map_cons, List.map_nil, hop, h_and_eval2]
                rw [h_get_append_lt _ _ a ha13, h_get_append_ge _ _ b (by omega) hb26]
                by_cases hap : p0 = p
                · by_cases hbw : w0 = w
                  · exfalso; rw [hap, hbw] at hinc0; exact hinc0 hpw
                  · simp [w0, hbw]
                · simp [p0, hap])
              (fun _ _ ht => Bool.noConfusion ht)
      · by_cases hb13 : b < 13
        · let p0 : Fin 13 := ⟨b, hb13⟩
          let w0 : Fin 13 := ⟨a - 13, by omega⟩
          by_cases hinc0 : inc p0 w0 = true
          · have hinc_sub : inc (p0 - w0) 0 = true := by
              have h := h_inc_shift (p0 - w0) 0 w0; rw [sub_add_cancel, zero_add] at h
              exact h.symm.trans hinc0
            rcases h_orb_inc (p0 - w0) hinc_sub with ⟨m, hm, hd⟩
            rcases h_swap_g0 C PEqualNP.CircuitLowerBounds.GateOp.and a b rest (Or.inl rfl) hGoodC hCsize63
              (by rw [hCg0, hop]) with ⟨Cs, hGCs, hCss, hCsh⟩
            have hheadCs : Cs.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [p0.val, 13 + w0.val] } := by
              rw [hCsh]; simp only [p0, w0]; simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]; omega
            rcases h_norm_cross PEqualNP.CircuitLowerBounds.GateOp.and p0 w0 m hm Cs hGCs hCss hheadCs
              with ⟨D', hGD', hDs', hDh'⟩
            rcases hd with hd0 | hd1
            · rw [hd0] at hDh'
              exact h_and_inc 0 (Or.inl rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
            · rw [hd1] at hDh'
              exact h_and_inc 1 (Or.inr rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
          · exfalso
            exact h_kill_g0 0 (by omega)
              (fun p w hpw => by
                simp only [sem, ↓reduceIte, hg0_in, List.map_cons, List.map_nil, hop, h_and_eval2]
                rw [h_get_append_ge _ _ a (by omega) ha26, h_get_append_lt _ _ b hb13]
                by_cases hbw : w0 = w
                · by_cases hap : p0 = p
                  · exfalso; rw [hap, hbw] at hinc0; exact hinc0 hpw
                  · simp [p0, hap]
                · simp [w0, hbw])
              (fun _ _ ht => Bool.noConfusion ht)
        · exfalso
          exact h_kill_g0 0 (by omega)
            (fun p w _ => by
              simp only [sem, ↓reduceIte, hg0_in, List.map_cons, List.map_nil, hop, h_and_eval2]
              rw [h_get_append_ge _ _ a (by omega) ha26, h_get_append_ge _ _ b (by omega) hb26]
              by_cases haw : (⟨a - 13, by omega⟩ : Fin 13) = w
              · have hbw : (⟨b - 13, by omega⟩ : Fin 13) ≠ w := by
                  intro h; apply hab
                  have h1 := congrArg Fin.val haw; have h2 := congrArg Fin.val h; dsimp only at h1 h2; omega
                simp [hbw]
              · simp [haw])
            (fun _ _ ht => Bool.noConfusion ht)
    · have h_handle_or_pts : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (p1 p2 : Fin 13),
          p1 ≠ p2 → Good D → D.size ≤ 63 →
          D.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p1.val, p2.val] } →
          False := by
        intro D p1 p2 hp12 hGD hDs hhead
        have hdiff_ne : p2 - p1 ≠ 0 := by intro h; exact hp12 (sub_eq_zero.mp h).symm
        rcases h_orb_same (p2 - p1) hdiff_ne with ⟨m, hm, horb⟩
        have h_go : ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (q1 q2 : Fin 13),
            Good E → E.size ≤ 63 →
            E.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [q1.val, q2.val] } →
            (m * (q2 - q1) = 1 ∨ m * (q2 - q1) = 2) → False := by
          intro E q1 q2 hGE hEs hEhead hmd
          let E' := permCircuit (affMap m (-(m * q1))) E
          have hres := h_aff_good m (-(m * q1)) hm E hGE hEs
          have hE'head : E'.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, (m * (q2 - q1)).val] } := by
            cases hEg : E.gates with
            | nil => rw [hEg] at hEhead; simp at hEhead
            | cons g1 tl =>
              rw [hEg] at hEhead; simp only [List.head?_cons] at hEhead
              have hg1 : g1 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [q1.val, q2.val] } :=
                Option.some.inj hEhead
              simp only [E', permCircuit, hEg, List.map_cons, List.head?_cons, hg1, mapGate,
                List.map_cons, List.map_nil]
              simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]
              constructor
              · have h1 : q1.val < 26 := by omega
                have h2 : q1.val < 13 := q1.isLt
                simp only [mapWire, h1, ↓reduceDIte, affMap, h2, Fin.val_castAdd]
                rw [add_neg_cancel]; rfl
              · have h1 : q2.val < 26 := by omega
                have h2 : q2.val < 13 := q2.isLt
                simp only [mapWire, h1, ↓reduceDIte, affMap, h2, Fin.val_castAdd]
                have hsub : m * q2 + -(m * q1) = m * (q2 - q1) := by rw [← sub_eq_add_neg, mul_sub]
                exact congrArg Fin.val hsub
          rcases hmd with hd1 | hd2
          · rw [hd1] at hE'head
            exact h_or_same 1 (Or.inl rfl) ⟨E', hres.1.1, hres.2, hE'head, hres.1.2.1, hres.1.2.2.1, hres.1.2.2.2⟩
          · rw [hd2] at hE'head
            exact h_or_same 2 (Or.inr rfl) ⟨E', hres.1.1, hres.2, hE'head, hres.1.2.1, hres.1.2.2.1, hres.1.2.2.2⟩
        rcases horb with hdir | hrev
        · exact h_go D p1 p2 hGD hDs hhead hdir
        · cases hDg : D.gates with
          | nil => rw [hDg] at hhead; simp at hhead
          | cons g1 tl =>
            rw [hDg] at hhead; simp only [List.head?_cons] at hhead
            have hg1 : g1 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p1.val, p2.val] } :=
              Option.some.inj hhead
            rcases h_swap_g0 D PEqualNP.CircuitLowerBounds.GateOp.or p1.val p2.val tl (Or.inr rfl)
              hGD hDs (by rw [hDg, hg1]) with ⟨Ds, hGDs, hDss, hDsh⟩
            have hneg : -(p2 - p1) = p1 - p2 := neg_sub p2 p1
            rw [hneg] at hrev
            exact h_go Ds p2 p1 hGDs hDss hDsh hrev
      have h_handle_or_cross : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (p0 w0 : Fin 13),
          Good D → D.size ≤ 63 →
          D.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p0.val, 13 + w0.val] } →
          False := by
        intro D p0 w0 hGD hDs hhead
        rcases h_orb_all (p0 - w0) with ⟨m, hm, hd⟩
        rcases h_norm_cross PEqualNP.CircuitLowerBounds.GateOp.or p0 w0 m hm D hGD hDs hhead
          with ⟨D', hGD', hDs', hDh'⟩
        rcases hd with h0 | h1 | h2 | h4 | h7
        · rw [h0] at hDh'
          exact h_or_inc 0 (Or.inl rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
        · rw [h1] at hDh'
          exact h_or_inc 1 (Or.inr rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
        · rw [h2] at hDh'
          exact h_or_noninc 2 (Or.inl rfl) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
        · rw [h4] at hDh'
          exact h_or_noninc 4 (Or.inr (Or.inl rfl)) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
        · rw [h7] at hDh'
          exact h_or_noninc 7 (Or.inr (Or.inr rfl)) ⟨D', hGD'.1, hDs', hDh', hGD'.2.1, hGD'.2.2.1, hGD'.2.2.2⟩
      by_cases ha13 : a < 13
      · by_cases hb13 : b < 13
        · exact h_handle_or_pts C ⟨a, ha13⟩ ⟨b, hb13⟩
            (fun h => hab (congrArg Fin.val h)) hGoodC hCsize63 (by rw [hCg0, hop]; rfl)
        · exact h_handle_or_cross C ⟨a, ha13⟩ ⟨b - 13, by omega⟩ hGoodC hCsize63
            (by rw [hCg0, hop]; simp only [List.head?_cons]; simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]; omega)
      · by_cases hb13 : b < 13
        · rcases h_swap_g0 C PEqualNP.CircuitLowerBounds.GateOp.or a b rest (Or.inr rfl)
            hGoodC hCsize63 (by rw [hCg0, hop]) with ⟨Cs, hGCs, hCss, hCsh⟩
          exact h_handle_or_cross Cs ⟨b, hb13⟩ ⟨a - 13, by omega⟩ hGCs hCss
            (by rw [hCsh]; simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]; omega)
        · let Cd := permCircuit dualMap C
          have hres := h_dual_good C hGoodC hCsize63
          let w1 : Fin 13 := ⟨a - 13, by omega⟩
          let w2 : Fin 13 := ⟨b - 13, by omega⟩
          have hw12 : -w1 ≠ -w2 := by
            intro h
            have h1 := neg_injective h
            apply hab
            have h2 := congrArg Fin.val h1
            simp only [w1, w2] at h2; omega
          have hCdhead : Cd.gates.head? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(-w1).val, (-w2).val] } := by
            simp only [Cd, permCircuit, hCg0, hop, List.map_cons, List.head?_cons, mapGate,
              List.map_cons, List.map_nil]
            simp only [Option.some.injEq, PEqualNP.CircuitLowerBounds.Gate.mk.injEq, List.cons.injEq, and_true, true_and]
            constructor
            · simp only [mapWire, ha26, ↓reduceDIte, dualMap, ha13, Fin.val_castAdd, w1]
            · simp only [mapWire, hb26, ↓reduceDIte, dualMap, hb13, Fin.val_castAdd, w2]
          exact h_handle_or_pts Cd (-w1) (-w2) hw12 hres.1 hres.2 hCdhead
