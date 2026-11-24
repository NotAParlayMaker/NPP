import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5266_566
    (hMixedStar : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)),
        (∀ e ∈ S, e ∈ Ustar G C ∧
          ∃ u v : Fin n, e = s(u, v) ∧
          ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b c : Fin 2, b ≠ c ∧
            u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
            wireVal n C (opnd C g b) (pairInput u u) = true ∧
            (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
              wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
            v ∈ orIn n C (opnd C g c) ∧
            ∃ z ∈ orIn n C (opnd C g c), ¬ G.Adj u z ∧ G.Adj p z) →
        S.card ≤ k * (C.size + 1))
    (hSingletonJunk : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)),
        (∀ e ∈ S, e ∈ Ustar G C ∧
          ∃ u v : Fin n, e = s(u, v) ∧
          ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b c : Fin 2, b ≠ c ∧
            u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
            wireVal n C (opnd C g b) (pairInput u u) = true ∧
            (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
              wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
            ∃ h ∈ junk G C, OrReaches n C (opnd C g c) h ∧
              gateVal n C h (pairInput v v) = true) →
        S.card ≤ k * (C.size + 1))
    (hNestedPairJunk : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ S : Finset (Sym2 (Fin n)),
        (∀ e ∈ S, e ∈ Ustar G C ∧
          ∃ u v : Fin n, e = s(u, v) ∧
          ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
            u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
            gateVal n C g (pairInput u v) = true ∧
            wireVal n C (opnd C g b) (pairInput u u) = false ∧
            wireVal n C (opnd C g b) (pairInput v v) = false ∧
            ∃ h ∈ junk G C, OrReaches n C (opnd C g b) h ∧
              gateVal n C h (pairInput u v) = true) →
        S.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x3 x7 \ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11 ∧ ∀ x12 ∈ PEqualNP.TopForm.side x7 x11 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x7 x11 (1 : Fin (2 : ℕ)), x12 ∉ x10}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨k1, hk1⟩ := hMixedStar
  obtain ⟨k2, hk2⟩ := hSingletonJunk
  obtain ⟨k3, hk3⟩ := hNestedPairJunk
  refine ⟨6 + k1 + k2 + k3, ?_⟩
  intro n G _ hGirth hNe C hLeast hTop
  let E_target := {x10 ∈ Ustar G C |
    (¬∃ (x11 : Fin n) (x12 : Fin n), x10 = s(x11, x12) ∧ ∃ x13 < C.gates.length, ∃ (x14 : Fin 2),
      2 ≤ (orIn n C (n + x13)).card ∧ (∀ x15 ∈ orIn n C (n + x13), G.Adj x11 x15) ∧
      orIn n C (opnd C x13 x14) = {x12}) ∧
    ∃ x11 ∈ tops G C \ centreless G C, x10 ∈ gammaE G C x11 ∧
      ∀ x12 ∈ side C x11 0 ∪ side C x11 1, x12 ∉ x10}
  let E1 := {e ∈ Ustar G C |
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
      u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
      wireVal n C (opnd C g b) (pairInput u u) = true ∧
      (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
        wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
      v ∈ orIn n C (opnd C g (1 - b)) ∧
      ∃ z ∈ orIn n C (opnd C g (1 - b)), ¬ G.Adj u z ∧ G.Adj p z}
  have mem_filter_any : ∀ {α : Type} (s : Finset α) (p : α → Prop) (inst : DecidablePred p) (a : α),
      a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := fun _ _ _ _ => Finset.mem_filter
  have hE1_mem : ∀ e : Sym2 (Fin n), e ∈ E1 ↔ e ∈ Ustar G C ∧
      ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
        u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
        wireVal n C (opnd C g b) (pairInput u u) = true ∧
        (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
          wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
        v ∈ orIn n C (opnd C g (1 - b)) ∧
        ∃ z ∈ orIn n C (opnd C g (1 - b)), ¬ G.Adj u z ∧ G.Adj p z :=
    fun e => mem_filter_any (Ustar G C) _ _ e
  let E2 := {e ∈ Ustar G C |
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
      u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
      wireVal n C (opnd C g b) (pairInput u u) = true ∧
      (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
        wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
      ∃ h ∈ junk G C, OrReaches n C (opnd C g (1 - b)) h ∧ gateVal n C h (pairInput v v) = true}
  have hE2_mem : ∀ e : Sym2 (Fin n), e ∈ E2 ↔ e ∈ Ustar G C ∧
      ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
        u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
        wireVal n C (opnd C g b) (pairInput u u) = true ∧
        (∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
          wireVal n C (opnd C g b) (pairInput x x) = true → x = u) ∧
        ∃ h ∈ junk G C, OrReaches n C (opnd C g (1 - b)) h ∧ gateVal n C h (pairInput v v) = true :=
    fun e => mem_filter_any (Ustar G C) _ _ e
  let E3 := {e ∈ Ustar G C |
    ∃ u v : Fin n, e = s(u, v) ∧ ∃ g ∈ junk G C, ∃ p ∈ wmax G C g, ∃ b : Fin 2,
      u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p ∧
      gateVal n C g (pairInput u v) = true ∧
      wireVal n C (opnd C g b) (pairInput u u) = false ∧
      wireVal n C (opnd C g b) (pairInput v v) = false ∧
      ∃ h ∈ junk G C, OrReaches n C (opnd C g b) h ∧ gateVal n C h (pairInput u v) = true}
  have hE1 : E1.card ≤ k1 * (C.size + 1) := hk1 n G hGirth hNe C hLeast hTop E1 (fun e he => by
    obtain ⟨heU, u, v, heq, g, hg, p, hp, b, rest⟩ := (hE1_mem e).mp he
    refine ⟨heU, u, v, heq, g, hg, p, hp, b, 1 - b, ?_, rest⟩
    fin_cases b
    · change (0 : Fin 2) ≠ 1; exact Fin.zero_ne_one
    · change (1 : Fin 2) ≠ 0; exact Fin.zero_ne_one.symm)
  have hE2 : E2.card ≤ k2 * (C.size + 1) := hk2 n G hGirth hNe C hLeast hTop E2 (fun e he => by
    obtain ⟨heU, u, v, heq, g, hg, p, hp, b, rest⟩ := (hE2_mem e).mp he
    refine ⟨heU, u, v, heq, g, hg, p, hp, b, 1 - b, ?_, rest⟩
    fin_cases b
    · change (0 : Fin 2) ≠ 1; exact Fin.zero_ne_one
    · change (1 : Fin 2) ≠ 0; exact Fin.zero_ne_one.symm)
  have hE3 : E3.card ≤ k3 * (C.size + 1) := hk3 n G hGirth hNe C hLeast hTop E3 (fun e he => Finset.mem_filter.mp he)
  have hAO : IsAO2 n C := hLeast.1
  -- Section 1: Girth >= 5 graph lemmas
  have hNoTri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → False := by
    intro a b c hab hbc hca
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hca
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, Ne.symm e1]
      · simp [e1, e2, Ne.symm e3]
    have h5 := hGirth a _ hcyc
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h5
    omega
  have hNoC4 : ∀ a b c d : Fin n,
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False := by
    intro a b c d hab hbc hcd hda hac hbd
    have e1 := G.ne_of_adj hab
    have e2 := G.ne_of_adj hbc
    have e3 := G.ne_of_adj hcd
    have e4 := G.ne_of_adj hda
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd
        (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e2, e3, e4, hbd, Ne.symm hac, Ne.symm e1]
      · simp [e1, e2, hbd, hac, Ne.symm e1, Ne.symm e4]
    have h5 := hGirth a _ hcyc
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h5
    omega
  have hEdgeSep : ∀ p q u v : Fin n, G.Adj p q → G.Adj u v →
      u ≠ p → u ≠ q → v ≠ p → v ≠ q →
      (¬ G.Adj u p ∧ ¬ G.Adj v p) ∨ (¬ G.Adj u q ∧ ¬ G.Adj v q) := by
    intro p q u v hpq huv hup huq hvp hvq
    by_contra hnot
    rw [not_or, not_and_or, not_and_or] at hnot
    rcases hnot with ⟨hp, hq⟩
    have hup' : ¬ G.Adj u p → G.Adj v p := fun h => by
      rcases hp with h1 | h1
      · exact False.elim (h1 h)
      · exact Classical.not_not.mp h1
    have huq' : ¬ G.Adj u q → G.Adj v q := fun h => by
      rcases hq with h1 | h1
      · exact False.elim (h1 h)
      · exact Classical.not_not.mp h1
    by_cases hadj_up : G.Adj u p <;> by_cases hadj_uq : G.Adj u q
    · exact hNoTri u p q hadj_up hpq hadj_uq.symm
    · have hadj_vq := huq' hadj_uq
      exact hNoC4 u p q v hadj_up hpq hadj_vq.symm huv.symm huq hvp.symm
    · have hadj_vp := hup' hadj_up
      exact hNoC4 v p q u hadj_vp hpq hadj_uq.symm huv hvq hup.symm
    · have hadj_vp := hup' hadj_up
      have hadj_vq := huq' hadj_uq
      exact hNoTri v p q hadj_vp hpq hadj_vq.symm
  -- Section 2: Circuit evaluation and monotonicity
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by
    intro b1 b2; cases b1 <;> cases b2 <;> rfl
  let wstep : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wstep_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl wstep w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      have hl : (wstep w g).length = w.length + 1 := by
        simp only [wstep, List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have wstep_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl wstep w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have hi' : i < (wstep w g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (wstep w g) i hi']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have gate_eval_raw : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (gs.foldl wstep w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl wstep w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro w j hj; simp at hj
    | cons g gs ih =>
      intro w j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : w.length < (wstep w g).length := by
          simp only [wstep, List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, wstep_lt gs (wstep w g) w.length hlt]
        have hlast : (wstep w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        by_cases hi : i < w.length
        · rw [if_pos hi, wstep_lt gs (wstep w g) i (by
            simp only [wstep, List.length_append, List.length_singleton]; omega)]
          simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [if_neg hi]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i),
            Option.getD_none]
      | succ j =>
        have hj' : j < gs.length := by
          simp only [List.length_cons] at hj; omega
        have key := ih (wstep w g) j hj'
        have hl : (wstep w g).length = w.length + 1 := by
          simp only [wstep, List.length_append, List.length_singleton]
        rw [hl, show w.length + 1 + j = w.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have wire_input : ∀ (x : Fin n → Bool) (i : Fin n),
      wireVal n C i.val x = x i := by
    intro x i
    change (C.gates.foldl wstep (List.ofFn x)).getD i.val false = x i
    rw [wstep_lt C.gates (List.ofFn x) i.val (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
      Fin.eta]
  have wire_beyond : ∀ (x : Fin n → Bool) (w : ℕ), n + C.gates.length ≤ w →
      wireVal n C w x = false := by
    intro x w hw
    change (C.gates.foldl wstep (List.ofFn x)).getD w false = false
    have hlen : (C.gates.foldl wstep (List.ofFn x)).length = n + C.gates.length := by
      rw [wstep_len, List.length_ofFn]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (C.gates.foldl wstep (List.ofFn x)).length ≤ w),
      Option.getD_none]
  have hgate : ∀ (j : ℕ) (hj : j < C.gates.length), gateAt C j = C.gates[j] := by
    intro j hj
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have gate_inputs_pair : ∀ j : ℕ, j < C.gates.length →
      (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
      opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
      ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
    intro j hj
    have hmem : gateAt C j ∈ C.gates := by
      rw [hgate j hj]; exact List.getElem_mem hj
    have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := hAO.1 (gateAt C j) hmem
    have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
    have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
      cases h0 : (gateAt C j).inputs with
      | nil => simp [h0] at hlen
      | cons a l1 =>
        cases h1 : l1 with
        | nil => simp [h0, h1] at hlen
        | cons b l2 =>
          cases h2 : l2 with
          | nil =>
            have h01 : opnd C j 0 = a := by
              change ((gateAt C j).inputs).getD 0 0 = a
              rw [h0]; rfl
            have h11 : opnd C j 1 = b := by
              change ((gateAt C j).inputs).getD 1 0 = b
              rw [h0, h1]; rfl
            rw [h01, h11]
          | cons c l3 => simp [h0, h1, h2] at hlen
    refine ⟨hin, hrb _ ?_, hrb _ ?_, hop⟩
    · rw [hin]; exact List.mem_cons_self
    · rw [hin]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have gateVal_eval_pair : ∀ (j : ℕ), j < C.gates.length → ∀ (x : Fin n → Bool),
      gateVal n C j x = (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
    intro j hj x
    change (C.gates.foldl wstep (List.ofFn x)).getD (n + j) false = _
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    have hraw := gate_eval_raw C.gates (List.ofFn x) j hj
    rw [hlen] at hraw
    rw [hraw, ← hgate j hj]
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    rw [hin]
    simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1]
    rfl
  have gateVal_and : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ x : Fin n → Bool,
      gateVal n C j x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
    intro j hj hop x
    rw [gateVal_eval_pair j hj x, hop, eval_and]
  have gateVal_or : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.or →
      ∀ x : Fin n → Bool,
      gateVal n C j x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
    intro j hj hop x
    rw [gateVal_eval_pair j hj x, hop, eval_or]
  have wireVal_mono : ∀ (w : ℕ) (x y : Fin n → Bool),
      (∀ i : Fin n, x i = true → y i = true) →
      wireVal n C w x = true → wireVal n C w y = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x y hxy hwx
      by_cases hwn : w < n
      · let i : Fin n := ⟨w, hwn⟩
        rw [show w = i.val from rfl, wire_input] at hwx ⊢
        exact hxy i hwx
      · by_cases hwlt : w < n + C.gates.length
        · let j := w - n
          have hj : j < C.gates.length := by omega
          have hwj : w = n + j := by omega
          rw [hwj] at hwx ⊢
          change gateVal n C j x = true at hwx
          change gateVal n C j y = true
          obtain ⟨_, h0, h1, hop⟩ := gate_inputs_pair j hj
          rcases hop with hand | hor
          · rw [gateVal_and j hj hand x, Bool.and_eq_true] at hwx
            rw [gateVal_and j hj hand y, Bool.and_eq_true]
            exact ⟨ih (opnd C j 0) (by omega) x y hxy hwx.1,
              ih (opnd C j 1) (by omega) x y hxy hwx.2⟩
          · rw [gateVal_or j hj hor x, Bool.or_eq_true] at hwx
            rw [gateVal_or j hj hor y, Bool.or_eq_true]
            rcases hwx with hx0 | hx1
            · exact Or.inl (ih (opnd C j 0) (by omega) x y hxy hx0)
            · exact Or.inr (ih (opnd C j 1) (by omega) x y hxy hx1)
        · rw [wire_beyond x w (by omega)] at hwx
          cases hwx
  -- Section 3: orSets, cones, OrReaches, InCone, orIn
  have orStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (orStep n cs g).length = cs.length + 1 := by
        dsimp only [orStep]
        simp only [List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have orStep_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      have hi' : i < (orStep n cs g).length := by
        dsimp only [orStep]
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (orStep n cs g) i hi']
      dsimp only [orStep]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have orSets_raw : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (orStep n) cs).getD (cs.length + j) [] =
        (cs.length + j) :: (if gs[j].op = GateOp.or then
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) cs).getD (w - n) []) else []) := by
    intro gs
    induction gs with
    | nil => intro cs j hj; simp at hj
    | cons g gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : cs.length < (orStep n cs g).length := by
          dsimp only [orStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, orStep_lt gs (orStep n cs g) cs.length hlt]
        have hlast : (orStep n cs g).getD cs.length [] =
            cs.length :: (if g.op = GateOp.or then
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
                (fun w => cs.getD (w - n) []) else []) := by
          dsimp only [orStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        congr 1
        by_cases hor : g.op = GateOp.or
        · rw [if_pos hor, if_pos hor]
          refine List.flatMap_congr fun w hw => ?_
          rw [List.mem_filter] at hw
          have hwn : w - n < cs.length := by
            have := of_decide_eq_true hw.2; omega
          have hwn' : w - n < (orStep n cs g).length := by
            dsimp only [orStep]
            simp only [List.length_append, List.length_singleton]; omega
          rw [orStep_lt gs (orStep n cs g) (w - n) hwn']
          dsimp only [orStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
        · rw [if_neg hor, if_neg hor]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (orStep n cs g) j hj'
        have hl : (orStep n cs g).length = cs.length + 1 := by
          dsimp only [orStep]
          simp only [List.length_append, List.length_singleton]
        rw [hl, show cs.length + 1 + j = cs.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have orSets_len : (orSets n C).length = C.gates.length := by
    change (C.gates.foldl (orStep n) []).length = C.gates.length
    rw [orStep_len, List.length_nil, Nat.zero_add]
  have orSets_getD : ∀ j : ℕ, j < C.gates.length →
      (orSets n C).getD j [] =
        j :: (if (gateAt C j).op = GateOp.or then
          ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
            (fun w => (orSets n C).getD (w - n) []) else []) := by
    intro j hj
    change (C.gates.foldl (orStep n) []).getD j [] = _
    have hraw := orSets_raw C.gates [] j hj
    rw [List.length_nil, Nat.zero_add, ← hgate j hj] at hraw
    exact hraw
  have coneStep_len : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g gs ih =>
      intro cs
      rw [List.foldl_cons, ih]
      have hl : (coneStep n cs g).length = cs.length + 1 := by
        dsimp only [coneStep]
        simp only [List.length_append, List.length_singleton]
      rw [hl, List.length_cons]; omega
  have coneStep_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
    intro gs
    induction gs with
    | nil => intro cs i _; rfl
    | cons g gs ih =>
      intro cs i hi
      have hi' : i < (coneStep n cs g).length := by
        dsimp only [coneStep]
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.foldl_cons, ih (coneStep n cs g) i hi']
      dsimp only [coneStep]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have cones_raw : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ) (hj : j < gs.length),
      (gs.foldl (coneStep n) cs).getD (cs.length + j) [] =
        (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + j)))).flatMap
          (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
    intro gs
    induction gs with
    | nil => intro cs j hj; simp at hj
    | cons g gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have hlt : cs.length < (coneStep n cs g).length := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [Nat.add_zero, coneStep_lt gs (coneStep n cs g) cs.length hlt]
        have hlast : (coneStep n cs g).getD cs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) []) := by
          dsimp only [coneStep]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        rw [List.getElem_cons_zero, hlast]
        refine List.flatMap_congr fun w hw => ?_
        rw [List.mem_filter] at hw
        have hwn : w - n < cs.length := by
          have := of_decide_eq_true hw.2; omega
        have hwn' : w - n < (coneStep n cs g).length := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]; omega
        rw [coneStep_lt gs (coneStep n cs g) (w - n) hwn']
        dsimp only [coneStep]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      | succ j =>
        have hj' : j < gs.length := by simp only [List.length_cons] at hj; omega
        have key := ih (coneStep n cs g) j hj'
        have hl : (coneStep n cs g).length = cs.length + 1 := by
          dsimp only [coneStep]
          simp only [List.length_append, List.length_singleton]
        rw [hl, show cs.length + 1 + j = cs.length + (j + 1) by omega] at key
        rw [List.getElem_cons_succ]
        exact key
  have cones_getD : ∀ j : ℕ, j < C.gates.length →
      (cones n C).getD j [] =
        ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
          (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
    intro j hj
    change (C.gates.foldl (coneStep n) []).getD j [] = _
    have hraw := cones_raw C.gates [] j hj
    rw [List.length_nil, Nat.zero_add, ← hgate j hj] at hraw
    exact hraw
  have orReaches_lt : ∀ w g : ℕ, OrReaches n C w g →
      w < n + C.gates.length ∧ g < C.gates.length ∧ g ≤ w - n := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g hrec
      obtain ⟨hnw, hmem⟩ := hrec
      by_cases hlt : w - n < C.gates.length
      · have hwj : w = n + (w - n) := by omega
        rw [orSets_getD (w - n) hlt, List.mem_cons] at hmem
        rcases hmem with rfl | hmem'
        · exact ⟨by omega, hlt, le_rfl⟩
        · split_ifs at hmem' with hor
          · rw [List.mem_flatMap] at hmem'
            obtain ⟨w', hw'f, hw'm⟩ := hmem'
            rw [List.mem_filter] at hw'f
            have hw'_b := of_decide_eq_true hw'f.2
            have hrec : OrReaches n C w' g := ⟨hw'_b.1, hw'm⟩
            have hsub := ih w' (by omega) g hrec
            omega
          · simp at hmem'
      · exfalso
        have hlen : (orSets n C).length ≤ w - n := by rw [orSets_len]; omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen, Option.getD_none,
          List.not_mem_nil] at hmem
  have orReaches_self : ∀ j : ℕ, j < C.gates.length → OrReaches n C (n + j) j := by
    intro j hj
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left, orSets_getD j hj]
    exact List.mem_cons_self
  have orReaches_step_or : ∀ (j : ℕ), j < C.gates.length → (gateAt C j).op = GateOp.or →
      ∀ (b : Fin 2) (g : ℕ), OrReaches n C (opnd C j b) g → OrReaches n C (n + j) g := by
    intro j hj hor b g hrec
    have hlt := (orReaches_lt (opnd C j b) g hrec).1
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
    have hmem_in : opnd C j b ∈ (gateAt C j).inputs := by
      rw [hin]; fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hlt_j : opnd C j b < n + j := by
      fin_cases b <;> assumption
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left, orSets_getD j hj, List.mem_cons]
    right
    rw [if_pos hor, List.mem_flatMap]
    refine ⟨opnd C j b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hrec.1, hlt_j⟩⟩, hrec.2⟩
  have orReaches_cases : ∀ (j : ℕ), j < C.gates.length → ∀ g : ℕ,
      OrReaches n C (n + j) g →
      g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g) := by
    intro j hj g hrec
    obtain ⟨_, hmem⟩ := hrec
    rw [Nat.add_sub_cancel_left, orSets_getD j hj, List.mem_cons] at hmem
    rcases hmem with rfl | hmem'
    · exact Or.inl rfl
    · split_ifs at hmem' with hor
      · right
        refine ⟨hor, ?_⟩
        rw [List.mem_flatMap] at hmem'
        obtain ⟨w', hw'f, hw'm⟩ := hmem'
        rw [List.mem_filter] at hw'f
        have hw'_b := of_decide_eq_true hw'f.2
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, List.mem_cons, List.mem_singleton] at hw'f
        rcases hw'f.1 with rfl | rfl
        · exact ⟨0, hw'_b.1, hw'm⟩
        · exact ⟨1, hw'_b.1, hw'm⟩
      · simp at hmem'
  have orReaches_val : ∀ (w g : ℕ) (x : Fin n → Bool),
      OrReaches n C w g → gateVal n C g x = true → wireVal n C w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g x hrec hgx
      have hwlt := (orReaches_lt w g hrec).1
      have hwn : n ≤ w := hrec.1
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hrec ⊢
      rcases orReaches_cases j hj g hrec with rfl | ⟨hor, b, hrec'⟩
      · exact hgx
      · change gateVal n C j x = true
        rw [gateVal_or j hj hor x, Bool.or_eq_true]
        have hlt_b : opnd C j b < w := by
          obtain ⟨_, h0, h1, _⟩ := gate_inputs_pair j hj
          fin_cases b
          · change opnd C j 0 < w; omega
          · change opnd C j 1 < w; omega
        have hvb := ih (opnd C j b) hlt_b g x hrec' hgx
        fin_cases b
        · exact Or.inl hvb
        · exact Or.inr hvb
  have orReaches_inCone_aux : ∀ (w g : ℕ), OrReaches n C w g →
      w < n + C.gates.length ∧ (g = w - n ∨ InCone n C g (w - n)) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g hrec
      have hwlt := (orReaches_lt w g hrec).1
      have hwn : n ≤ w := hrec.1
      let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      refine ⟨hwlt, ?_⟩
      change g = j ∨ InCone n C g j
      rw [hwj] at hrec
      rcases orReaches_cases j hj g hrec with rfl | ⟨hor, b, hrec'⟩
      · exact Or.inl rfl
      · right
        obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair j hj
        have hlt_b : opnd C j b < n + j := by
          fin_cases b <;> assumption
        have ihb := ih (opnd C j b) (by omega) g hrec'
        have hbn : n ≤ opnd C j b := hrec'.1
        have hmem_in : opnd C j b ∈ (gateAt C j).inputs := by
          rw [hin]; fin_cases b
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        change g ∈ (cones n C).getD j []
        rw [cones_getD j hj, List.mem_flatMap]
        refine ⟨opnd C j b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hbn, hlt_b⟩⟩, ?_⟩
        rw [List.mem_cons]
        rcases ihb.2 with rfl | hc
        · exact Or.inl rfl
        · exact Or.inr hc
  have orReaches_inCone : ∀ (a : ℕ), a < C.gates.length → ∀ (b : Fin 2) (g : ℕ),
      OrReaches n C (opnd C a b) g → InCone n C g a := by
    intro a ha b g hrec
    obtain ⟨hin, h0, h1, _⟩ := gate_inputs_pair a ha
    have hbn : n ≤ opnd C a b := hrec.1
    have hba : opnd C a b < n + a := by fin_cases b <;> assumption
    have hmem_in : opnd C a b ∈ (gateAt C a).inputs := by
      rw [hin]; fin_cases b
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hsub := (orReaches_inCone_aux (opnd C a b) g hrec).2
    change g ∈ (cones n C).getD a []
    rw [cones_getD a ha, List.mem_flatMap]
    refine ⟨opnd C a b, List.mem_filter.mpr ⟨hmem_in, decide_eq_true ⟨hbn, hba⟩⟩, ?_⟩
    rw [List.mem_cons]
    exact hsub
  have orIn_val : ∀ (w : ℕ) (i : Fin n) (x : Fin n → Bool),
      i ∈ orIn n C w → x i = true → wireVal n C w x = true := by
    intro w i x hi hx
    dsimp only [orIn] at hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with heq | ⟨k, hk, hrec, _, hkin⟩
    · rw [← heq, wire_input x i]; exact hx
    · refine orReaches_val w k x hrec ?_
      obtain ⟨_, _, _, hop⟩ := gate_inputs_pair k hk
      obtain ⟨hin, _, _, _⟩ := gate_inputs_pair k hk
      rw [gateVal_or k hk (by assumption), Bool.or_eq_true]
      rw [hin, List.mem_cons, List.mem_singleton] at hkin
      rcases hkin with heq0 | heq1
      · left; rw [← heq0, wire_input x i]; exact hx
      · right; rw [← heq1, wire_input x i]; exact hx
  have orIn_input : ∀ i : Fin n, orIn n C i.val = {i} := by
    intro i
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · dsimp only [orIn]; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, Or.inl rfl⟩
    · intro j hj
      dsimp only [orIn] at hj
      rw [Finset.mem_filter] at hj
      rcases hj.2 with hji | ⟨k, _, hrec, _, _⟩
      · exact Fin.ext hji
      · exfalso; have := hrec.1; omega
  have orIn_and_eq : ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.and →
      orIn n C (n + j) = ∅ := by
    intro j hj hand
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    dsimp only [orIn] at hi
    rw [Finset.mem_filter] at hi
    rcases hi.2 with hnj | ⟨k, hk, hrec, hkor, _⟩
    · have := i.isLt; omega
    · rcases orReaches_cases j hj k hrec with rfl | ⟨hjor, _⟩
      · rw [hand] at hkor; cases hkor
      · rw [hand] at hjor; cases hjor
  have orIn_or_eq : ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.or →
      orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
    intro j hj hor
    ext i
    dsimp only [orIn]
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, hij | ⟨k, hk, hrec, hkor, hkin⟩⟩
      · have := i.isLt; omega
      · rcases orReaches_cases j hj k hrec with hkj | ⟨_, b, hrec'⟩
        · rw [hkj] at hkin
          obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
          rw [hin, List.mem_cons, List.mem_singleton] at hkin
          rcases hkin with h0 | h1
          · exact Or.inl ⟨Finset.mem_univ i, Or.inl h0⟩
          · exact Or.inr ⟨Finset.mem_univ i, Or.inl h1⟩
        · fin_cases b
          · exact Or.inl ⟨Finset.mem_univ i, Or.inr ⟨k, hk, hrec', hkor, hkin⟩⟩
          · exact Or.inr ⟨Finset.mem_univ i, Or.inr ⟨k, hk, hrec', hkor, hkin⟩⟩
    · rintro (⟨_, h0 | ⟨k, hk, hrec, hkor, hkin⟩⟩ | ⟨_, h1 | ⟨k, hk, hrec, hkor, hkin⟩⟩)
      · refine ⟨Finset.mem_univ i, Or.inr ⟨j, hj, orReaches_self j hj, hor, ?_⟩⟩
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, h0]; exact List.mem_cons_self
      · exact ⟨Finset.mem_univ i, Or.inr ⟨k, hk, orReaches_step_or j hj hor 0 k hrec, hkor, hkin⟩⟩
      · refine ⟨Finset.mem_univ i, Or.inr ⟨j, hj, orReaches_self j hj, hor, ?_⟩⟩
        obtain ⟨hin, _, _, _⟩ := gate_inputs_pair j hj
        rw [hin, h1]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact ⟨Finset.mem_univ i, Or.inr ⟨k, hk, orReaches_step_or j hj hor 1 k hrec, hkor, hkin⟩⟩
  have extract_and_from_wire : ∀ (w : ℕ), w < n + C.gates.length → ∀ x : Fin n → Bool,
      wireVal n C w x = true → (∀ i ∈ orIn n C w, x i = false) →
      ∃ g < C.gates.length, OrReaches n C w g ∧ (gateAt C g).op = GateOp.and ∧
        gateVal n C g x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw x hwx hor_false
      by_cases hwn : w < n
      · exfalso
        let i : Fin n := ⟨w, hwn⟩
        have him : i ∈ orIn n C w := by rw [show w = i.val from rfl, orIn_input i]; exact Finset.mem_singleton_self i
        have hxi := hor_false i him
        rw [show w = i.val from rfl, wire_input x i] at hwx
        rw [hwx] at hxi; cases hxi
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : w = n + j := by omega
        obtain ⟨_, h0, h1, hop⟩ := gate_inputs_pair j hj
        rcases hop with hand | hor
        · refine ⟨j, hj, ?_, hand, ?_⟩
          · rw [hwj]; exact orReaches_self j hj
          · change wireVal n C (n + j) x = true; rw [← hwj]; exact hwx
        · have hgx : gateVal n C j x = true := by
            change wireVal n C (n + j) x = true; rw [← hwj]; exact hwx
          rw [gateVal_or j hj hor x, Bool.or_eq_true] at hgx
          have hsub : orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) :=
            orIn_or_eq j hj hor
          rw [← hwj] at hsub
          rcases hgx with hb0 | hb1
          · obtain ⟨g, hg, hrec, hga, hgv⟩ := ih (opnd C j 0) (by omega) (by omega) x hb0 (fun i hi => by
              apply hor_false i
              rw [hsub]; exact Finset.mem_union_left _ hi)
            exact ⟨g, hg, by rw [hwj]; exact orReaches_step_or j hj hor 0 g hrec, hga, hgv⟩
          · obtain ⟨g, hg, hrec, hga, hgv⟩ := ih (opnd C j 1) (by omega) (by omega) x hb1 (fun i hi => by
              apply hor_false i
              rw [hsub]; exact Finset.mem_union_right _ hi)
            exact ⟨g, hg, by rw [hwj]; exact orReaches_step_or j hj hor 1 g hrec, hga, hgv⟩
  have branching_or_descent : ∀ (w : ℕ), w < n + C.gates.length → ∀ u v : Fin n,
      v ∈ orIn n C w → 2 ≤ (orIn n C w).card → (∀ z ∈ orIn n C w, G.Adj u z) →
      ∃ h < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
        (∀ z ∈ orIn n C (n + h), G.Adj u z) ∧ orIn n C (opnd C h b) = {v} := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw u v hv hcard hadj
      by_cases hwn : w < n
      · exfalso
        have h1 : (orIn n C w).card = 1 := by
          rw [show w = (⟨w, hwn⟩ : Fin n).val from rfl, orIn_input ⟨w, hwn⟩, Finset.card_singleton]
        omega
      · let j := w - n
        have hj : j < C.gates.length := by omega
        have hwj : w = n + j := by omega
        obtain ⟨_, h0, h1, hop⟩ := gate_inputs_pair j hj
        rcases hop with hand | hor
        · exfalso
          rw [hwj, orIn_and_eq j hj hand, Finset.card_empty] at hcard; omega
        · have heq := orIn_or_eq j hj hor
          rw [← hwj] at heq
          have hv' : v ∈ orIn n C (opnd C j 0) ∨ v ∈ orIn n C (opnd C j 1) := by
            rw [heq, Finset.mem_union] at hv; exact hv
          have check_branch : ∀ b : Fin 2, v ∈ orIn n C (opnd C j b) →
              ∃ h < C.gates.length, ∃ b' : Fin 2, 2 ≤ (orIn n C (n + h)).card ∧
                (∀ z ∈ orIn n C (n + h), G.Adj u z) ∧ orIn n C (opnd C h b') = {v} := by
            intro b hvb
            by_cases hbc : (orIn n C (opnd C j b)).card ≤ 1
            · refine ⟨j, hj, b, ?_, ?_, ?_⟩
              · rw [← hwj]; exact hcard
              · rw [← hwj]; exact hadj
              · exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hvb, fun y hy => Finset.card_le_one.mp hbc y hy v hvb⟩
            · have hlt_b : opnd C j b < w := by
                fin_cases b
                · change opnd C j 0 < w; omega
                · change opnd C j 1 < w; omega
              have hsub : orIn n C (opnd C j b) ⊆ orIn n C w := by
                rw [heq]
                fin_cases b
                · exact Finset.subset_union_left
                · exact Finset.subset_union_right
              exact ih (opnd C j b) hlt_b (by omega) u v hvb (by omega) (fun z hz => hadj z (hsub hz))
          rcases hv' with hv0 | hv1
          · exact check_branch 0 hv0
          · exact check_branch 1 hv1
  have graphFun_pair_iff : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u v a = true) ||
      decide (∃ a b : Fin n, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true ↔ G.Adj u v
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u ∨ a = v := of_decide_eq_true ha
      have hb' : b = u ∨ b = v := of_decide_eq_true hb
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact False.elim (G.ne_of_adj hab rfl)
      · exact hab
      · exact hab.symm
      · exact False.elim (G.ne_of_adj hab rfl)
    · intro huv
      exact ⟨u, v, huv, decide_eq_true (Or.inl rfl), decide_eq_true (Or.inr rfl)⟩
  have graphFun_triple : ∀ x y p : Fin n,
      graphFun G ∅ (fun w => decide (w = x ∨ w = y ∨ w = p)) = true →
      ¬ G.Adj x p → ¬ G.Adj y p → G.Adj x y := by
    intro x y p hgf hxp hyp
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a = x ∨ a = y ∨ a = p) = true) ||
      decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = x ∨ a = y ∨ a = p) = true ∧
        decide (b = x ∨ b = y ∨ b = p) = true)) = true at hgf
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq] at hgf
    obtain ⟨a, b, hab, ha, hb⟩ := hgf
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact False.elim (G.ne_of_adj hab rfl)
    · exact hab
    · exact False.elim (hxp hab)
    · exact hab.symm
    · exact False.elim (G.ne_of_adj hab rfl)
    · exact False.elim (hyp hab)
    · exact False.elim (hxp hab.symm)
    · exact False.elim (hyp hab.symm)
    · exact False.elim (G.ne_of_adj hab rfl)
  have three_of_two_lt : ∀ {α : Type} [DecidableEq α] {S : Finset α}, 2 < S.card →
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    intro α _ S hS
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    have h1 : 1 < (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp h1
    rw [Finset.mem_erase] at hb hc
    exact ⟨a, ha, b, hb.2, c, hc.2, hb.1.symm, hc.1.symm, hbc⟩
  -- Section 4: Star structure and direct counts (2 + 4) * C.size
  let Sset (g : ℕ) (p : Fin n) (b : Fin 2) : Finset (Fin n) :=
    Finset.univ.filter fun x => x ≠ p ∧ ¬ G.Adj x p ∧ wireVal n C (opnd C g b) (pairInput x x) = true
  have hCrossAdj : ∀ g ∈ junk G C, ∀ p ∈ wmax G C g,
      ∀ x ∈ Sset g p 0, ∀ y ∈ Sset g p 1, G.Adj x y := by
    intro g hg p hp x hx y hy
    dsimp only [junk, gatesWhere] at hg
    rw [Finset.mem_filter] at hg
    have hg_lt : g < C.gates.length := Finset.mem_range.mp hg.1
    have hg_and : (gateAt C g).op = GateOp.and := hg.2.1
    rw [Finset.mem_filter] at hx hy
    let z : Fin n → Bool := fun w => decide (w = x ∨ w = y ∨ w = p)
    have h0 : wireVal n C (opnd C g 0) z = true :=
      wireVal_mono (opnd C g 0) (pairInput x x) z (fun i hi => by
        have hix : i = x := (of_decide_eq_true hi).elim id id
        exact decide_eq_true (Or.inl hix)) hx.2.2.2
    have h1 : wireVal n C (opnd C g 1) z = true :=
      wireVal_mono (opnd C g 1) (pairInput y y) z (fun i hi => by
        have hiy : i = y := (of_decide_eq_true hi).elim id id
        exact decide_eq_true (Or.inr (Or.inl hiy))) hy.2.2.2
    have hgz : gateVal n C g z = true := by
      rw [gateVal_and g hg_lt hg_and z, Bool.and_eq_true]; exact ⟨h0, h1⟩
    dsimp only [wmax] at hp
    rw [Finset.mem_filter] at hp
    have hgf := hp.2 z hgz (decide_eq_true (Or.inr (Or.inr rfl)))
    exact graphFun_triple x y p hgf hx.2.2.1 hy.2.2.1
  have hStarSide : ∀ g ∈ junk G C, ∀ p ∈ wmax G C g,
      (Sset g p 0).card ≤ 1 ∨ (Sset g p 1).card ≤ 1 := by
    intro g hg p hp
    by_contra hnot
    rw [not_or] at hnot
    obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Sset g p 0).card)
    obtain ⟨y1, hy1, y2, hy2, hyne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Sset g p 1).card)
    exact hNoC4 x1 y1 x2 y2 (hCrossAdj g hg p hp x1 hx1 y1 hy1)
      (hCrossAdj g hg p hp x2 hx2 y1 hy1).symm
      (hCrossAdj g hg p hp x2 hx2 y2 hy2)
      (hCrossAdj g hg p hp x1 hx1 y2 hy2).symm
      hxne hyne
  let IsoPairs (g : ℕ) : Finset (Fin n × Fin n) :=
    (Finset.univ ×ˢ Finset.univ).filter fun uv =>
      g ∈ junk G C ∧ G.Adj uv.1 uv.2 ∧ ∃ p ∈ wmax G C g, Sset g p 0 = {uv.1} ∧ Sset g p 1 = {uv.2}
  have hIsoShare : ∀ g : ℕ, ∀ a ∈ IsoPairs g, ∀ b ∈ IsoPairs g, a.1 = b.1 ∨ a.2 = b.2 := by
    intro g a ha b hb
    rcases a with ⟨u1, v1⟩
    rcases b with ⟨u2, v2⟩
    rw [Finset.mem_filter] at ha hb
    obtain ⟨hg, _, p1, hp1, hs0_1, hs1_1⟩ := ha.2
    obtain ⟨_, hadj2, p2, _, hs0_2, hs1_2⟩ := hb.2
    have hg_and : (gateAt C g).op = GateOp.and := by
      dsimp only [junk, gatesWhere] at hg; rw [Finset.mem_filter] at hg; exact hg.2.1
    have hg_lt : g < C.gates.length := by
      dsimp only [junk, gatesWhere] at hg; rw [Finset.mem_filter] at hg; exact Finset.mem_range.mp hg.1
    have hu1 : u1 ∈ Sset g p1 0 := by rw [hs0_1]; exact Finset.mem_singleton_self u1
    have hv1 : v1 ∈ Sset g p1 1 := by rw [hs1_1]; exact Finset.mem_singleton_self v1
    have hu2 : u2 ∈ Sset g p2 0 := by rw [hs0_2]; exact Finset.mem_singleton_self u2
    have hv2 : v2 ∈ Sset g p2 1 := by rw [hs1_2]; exact Finset.mem_singleton_self v2
    rw [Finset.mem_filter] at hu1 hv1 hu2 hv2
    by_contra hnot
    rw [not_or] at hnot
    have hu2_not : u2 ∉ Sset g p1 0 := by rw [hs0_1, Finset.mem_singleton]; exact Ne.symm hnot.1
    have hv2_not : v2 ∉ Sset g p1 1 := by rw [hs1_1, Finset.mem_singleton]; exact Ne.symm hnot.2
    have hu2_nb : u2 = p1 ∨ G.Adj u2 p1 := by
      by_contra hn
      rw [not_or] at hn
      exact hu2_not (Finset.mem_filter.mpr ⟨Finset.mem_univ u2, hn.1, hn.2, hu2.2.2.2⟩)
    have hv2_nb : v2 = p1 ∨ G.Adj v2 p1 := by
      by_contra hn
      rw [not_or] at hn
      exact hv2_not (Finset.mem_filter.mpr ⟨Finset.mem_univ v2, hn.1, hn.2, hv2.2.2.2⟩)
    dsimp only [wmax] at hp1
    rw [Finset.mem_filter] at hp1
    rcases hu2_nb with rfl | hu2a <;> rcases hv2_nb with rfl | hv2a
    · exact G.ne_of_adj hadj2 rfl
    · have h0 : wireVal n C (opnd C g 0) (pairInput u2 v1) = true :=
        wireVal_mono (opnd C g 0) (pairInput u2 u2) (pairInput u2 v1) (fun i hi => by
          have hi' : i = u2 := (of_decide_eq_true hi).elim id id
          exact decide_eq_true (Or.inl hi')) hu2.2.2.2
      have h1 : wireVal n C (opnd C g 1) (pairInput u2 v1) = true :=
        wireVal_mono (opnd C g 1) (pairInput v1 v1) (pairInput u2 v1) (fun i hi => by
          have hi' : i = v1 := (of_decide_eq_true hi).elim id id
          exact decide_eq_true (Or.inr hi')) hv1.2.2.2
      have hgv : gateVal n C g (pairInput u2 v1) = true := by
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨h0, h1⟩
      have hgf := hp1.2 (pairInput u2 v1) hgv (decide_eq_true (Or.inl rfl))
      rw [graphFun_pair_iff] at hgf
      exact hv1.2.2.1 hgf.symm
    · have h0 : wireVal n C (opnd C g 0) (pairInput u1 v2) = true :=
        wireVal_mono (opnd C g 0) (pairInput u1 u1) (pairInput u1 v2) (fun i hi => by
          have hi' : i = u1 := (of_decide_eq_true hi).elim id id
          exact decide_eq_true (Or.inl hi')) hu1.2.2.2
      have h1 : wireVal n C (opnd C g 1) (pairInput u1 v2) = true :=
        wireVal_mono (opnd C g 1) (pairInput v2 v2) (pairInput u1 v2) (fun i hi => by
          have hi' : i = v2 := (of_decide_eq_true hi).elim id id
          exact decide_eq_true (Or.inr hi')) hv2.2.2.2
      have hgv : gateVal n C g (pairInput u1 v2) = true := by
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨h0, h1⟩
      have hgf := hp1.2 (pairInput u1 v2) hgv (decide_eq_true (Or.inr rfl))
      rw [graphFun_pair_iff] at hgf
      exact hu1.2.2.1 hgf
    · exact hNoTri u2 v2 p1 hadj2 hv2a hu2a.symm
  have hIsoStarR : ∀ g : ℕ, ∀ u v1 v2 v3 : Fin n,
      (u, v1) ∈ IsoPairs g → (u, v2) ∈ IsoPairs g → (u, v3) ∈ IsoPairs g →
      v1 = v2 ∨ v1 = v3 ∨ v2 = v3 := by
    intro g u v1 v2 v3 h1 h2 h3
    by_contra hnot
    rw [not_or, not_or] at hnot
    rw [Finset.mem_filter] at h1 h2 h3
    obtain ⟨_, _, p1, _, hs0_1, hs1_1⟩ := h1.2
    obtain ⟨_, hadj2, p2, _, _, hs1_2⟩ := h2.2
    obtain ⟨_, hadj3, p3, _, _, hs1_3⟩ := h3.2
    have hu : u ∈ Sset g p1 0 := by rw [hs0_1]; exact Finset.mem_singleton_self u
    have hv2 : v2 ∈ Sset g p2 1 := by rw [hs1_2]; exact Finset.mem_singleton_self v2
    have hv3 : v3 ∈ Sset g p3 1 := by rw [hs1_3]; exact Finset.mem_singleton_self v3
    rw [Finset.mem_filter] at hu hv2 hv3
    have hv2_not : v2 ∉ Sset g p1 1 := by rw [hs1_1, Finset.mem_singleton]; exact Ne.symm hnot.1
    have hv3_not : v3 ∉ Sset g p1 1 := by rw [hs1_1, Finset.mem_singleton]; exact Ne.symm hnot.2.1
    have hv2_p : v2 ≠ p1 := fun h => by rw [h] at hadj2; exact hu.2.2.1 hadj2
    have hv3_p : v3 ≠ p1 := fun h => by rw [h] at hadj3; exact hu.2.2.1 hadj3
    have hv2a : G.Adj v2 p1 := by
      by_contra hn
      exact hv2_not (Finset.mem_filter.mpr ⟨Finset.mem_univ v2, hv2_p, hn, hv2.2.2.2⟩)
    have hv3a : G.Adj v3 p1 := by
      by_contra hn
      exact hv3_not (Finset.mem_filter.mpr ⟨Finset.mem_univ v3, hv3_p, hn, hv3.2.2.2⟩)
    exact hNoC4 u v2 p1 v3 hadj2 hv2a hv3a.symm hadj3.symm hu.2.1 hnot.2.2
  have hIsoStarL : ∀ g : ℕ, ∀ u1 u2 u3 v : Fin n,
      (u1, v) ∈ IsoPairs g → (u2, v) ∈ IsoPairs g → (u3, v) ∈ IsoPairs g →
      u1 = u2 ∨ u1 = u3 ∨ u2 = u3 := by
    intro g u1 u2 u3 v h1 h2 h3
    by_contra hnot
    rw [not_or, not_or] at hnot
    rw [Finset.mem_filter] at h1 h2 h3
    obtain ⟨_, _, p1, _, hs0_1, hs1_1⟩ := h1.2
    obtain ⟨_, hadj2, p2, _, hs0_2, _⟩ := h2.2
    obtain ⟨_, hadj3, p3, _, hs0_3, _⟩ := h3.2
    have hv : v ∈ Sset g p1 1 := by rw [hs1_1]; exact Finset.mem_singleton_self v
    have hu2 : u2 ∈ Sset g p2 0 := by rw [hs0_2]; exact Finset.mem_singleton_self u2
    have hu3 : u3 ∈ Sset g p3 0 := by rw [hs0_3]; exact Finset.mem_singleton_self u3
    rw [Finset.mem_filter] at hv hu2 hu3
    have hu2_not : u2 ∉ Sset g p1 0 := by rw [hs0_1, Finset.mem_singleton]; exact Ne.symm hnot.1
    have hu3_not : u3 ∉ Sset g p1 0 := by rw [hs0_1, Finset.mem_singleton]; exact Ne.symm hnot.2.1
    have hu2_p : u2 ≠ p1 := fun h => by rw [h] at hadj2; exact hv.2.2.1 hadj2.symm
    have hu3_p : u3 ≠ p1 := fun h => by rw [h] at hadj3; exact hv.2.2.1 hadj3.symm
    have hu2a : G.Adj u2 p1 := by
      by_contra hn
      exact hu2_not (Finset.mem_filter.mpr ⟨Finset.mem_univ u2, hu2_p, hn, hu2.2.2.2⟩)
    have hu3a : G.Adj u3 p1 := by
      by_contra hn
      exact hu3_not (Finset.mem_filter.mpr ⟨Finset.mem_univ u3, hu3_p, hn, hu3.2.2.2⟩)
    exact hNoC4 v u2 p1 u3 hadj2.symm hu2a hu3a.symm hadj3 hv.2.1 hnot.2.2
  have hIsoCard : ∀ g : ℕ, (IsoPairs g).card ≤ 2 := by
    intro g
    by_contra hnot
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := three_of_two_lt (by omega : 2 < (IsoPairs g).card)
    rcases a with ⟨u1, v1⟩
    rcases b with ⟨u2, v2⟩
    rcases c with ⟨u3, v3⟩
    rcases hIsoShare g (u1, v1) ha (u2, v2) hb with hu12_eq | hv12_eq
    · dsimp only at hu12_eq
      subst hu12_eq
      have hv12 : v1 ≠ v2 := fun h => hab (by rw [h])
      rcases hIsoShare g (u1, v1) ha (u3, v3) hc with hu13_eq | hv13_eq
      · dsimp only at hu13_eq
        subst hu13_eq
        rcases hIsoStarR g u1 v1 v2 v3 ha hb hc with h | h | h
        · exact hv12 h
        · exact hac (by rw [h])
        · exact hbc (by rw [h])
      · dsimp only at hv13_eq
        subst hv13_eq
        rcases hIsoShare g (u1, v2) hb (u3, v1) hc with hu | hv
        · dsimp only at hu
          rw [← hu] at hc
          rcases hIsoStarR g u1 v1 v2 v1 ha hb hc with h | h | h
          · exact hv12 h
          · exact hac (by rw [hu, h])
          · exact hbc (by rw [hu, h])
        · dsimp only at hv
          exact hv12 hv.symm
    · dsimp only at hv12_eq
      subst hv12_eq
      have hu12 : u1 ≠ u2 := fun h => hab (by rw [h])
      rcases hIsoShare g (u1, v1) ha (u3, v3) hc with hu13_eq | hv13_eq
      · dsimp only at hu13_eq
        subst hu13_eq
        rcases hIsoShare g (u2, v1) hb (u1, v3) hc with hu | hv
        · dsimp only at hu
          exact hu12 hu.symm
        · dsimp only at hv
          rw [← hv] at hc
          rcases hIsoStarL g u1 u2 u1 v1 ha hb hc with h | h | h
          · exact hu12 h
          · exact hac (by rw [hv, h])
          · exact hbc (by rw [hv, h])
      · dsimp only at hv13_eq
        subst hv13_eq
        rcases hIsoStarL g u1 u2 u3 v1 ha hb hc with h | h | h
        · exact hu12 h
        · exact hac (by rw [h])
        · exact hbc (by rw [h])
  let IsoAll : Finset (Sym2 (Fin n)) :=
    (Finset.range C.gates.length).biUnion fun g => (IsoPairs g).image fun uv => s(uv.1, uv.2)
  have hIsoAllCard : IsoAll.card ≤ 2 * C.size := by
    calc
      IsoAll.card ≤ ∑ g ∈ Finset.range C.gates.length, ((IsoPairs g).image fun uv => s(uv.1, uv.2)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ g ∈ Finset.range C.gates.length, (IsoPairs g).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ _g ∈ Finset.range C.gates.length, 2 :=
        Finset.sum_le_sum fun g _ => hIsoCard g
      _ = 2 * C.size := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]; rfl
  let SingOrEdges (g : ℕ) (b : Fin 2) : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧ g ∈ junk G C ∧
      ∃ p ∈ wmax G C g, Sset g p b = {u} ∧ v ∈ Sset g p (1 - b) ∧ orIn n C (opnd C g (1 - b)) = {v}
  have hSingOrCard : ∀ (g : ℕ) (b : Fin 2), (SingOrEdges g b).card ≤ 2 := by
    intro g b
    by_contra hnot
    obtain ⟨e1, he1, e2, he2, e3, he3, h12, h13, h23⟩ :=
      three_of_two_lt (by omega : 2 < (SingOrEdges g b).card)
    rw [Finset.mem_filter] at he1 he2 he3
    obtain ⟨he1G, u1, v1, rfl, _, p1, _, hs_u1, hv1_S, hv1_or⟩ := he1
    obtain ⟨he2G, u2, v2, he2eq, _, p2, _, hs_u2, _, hv2_or⟩ := he2
    obtain ⟨he3G, u3, v3, he3eq, _, p3, _, hs_u3, _, hv3_or⟩ := he3
    have hv12 : v1 = v2 := Finset.singleton_injective (hv1_or.symm.trans hv2_or)
    have hv13 : v1 = v3 := Finset.singleton_injective (hv1_or.symm.trans hv3_or)
    subst hv12; subst hv13
    have hadj1 : G.Adj u1 v1 := SimpleGraph.mem_edgeFinset.mp he1G
    have hadj2 : G.Adj u2 v1 := by rw [he2eq] at he2G; exact SimpleGraph.mem_edgeFinset.mp he2G
    have hadj3 : G.Adj u3 v1 := by rw [he3eq] at he3G; exact SimpleGraph.mem_edgeFinset.mp he3G
    have hu12 : u1 ≠ u2 := fun h => h12 (by rw [he2eq, h])
    have hu13 : u1 ≠ u3 := fun h => h13 (by rw [he3eq, h])
    have hu23 : u2 ≠ u3 := fun h => h23 (by rw [he2eq, he3eq, h])
    rw [Finset.mem_filter] at hv1_S
    have hu2_S : u2 ∈ Sset g p2 b := by rw [hs_u2]; exact Finset.mem_singleton_self u2
    have hu3_S : u3 ∈ Sset g p3 b := by rw [hs_u3]; exact Finset.mem_singleton_self u3
    rw [Finset.mem_filter] at hu2_S hu3_S
    have hu2_not : u2 ∉ Sset g p1 b := by rw [hs_u1, Finset.mem_singleton]; exact hu12.symm
    have hu3_not : u3 ∉ Sset g p1 b := by rw [hs_u1, Finset.mem_singleton]; exact hu13.symm
    have hu2_p : u2 ≠ p1 := fun h => by rw [h] at hadj2; exact hv1_S.2.2.1 hadj2.symm
    have hu3_p : u3 ≠ p1 := fun h => by rw [h] at hadj3; exact hv1_S.2.2.1 hadj3.symm
    have hu2a : G.Adj u2 p1 := by
      by_contra hn
      exact hu2_not (Finset.mem_filter.mpr ⟨Finset.mem_univ u2, hu2_p, hn, hu2_S.2.2.2⟩)
    have hu3a : G.Adj u3 p1 := by
      by_contra hn
      exact hu3_not (Finset.mem_filter.mpr ⟨Finset.mem_univ u3, hu3_p, hn, hu3_S.2.2.2⟩)
    exact hNoC4 v1 u2 p1 u3 hadj2.symm hu2a hu3a.symm hadj3 hv1_S.2.1 hu23
  let SingOrAll : Finset (Sym2 (Fin n)) :=
    (Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2))).biUnion fun gb =>
      SingOrEdges gb.1 gb.2
  have hSingOrAllCard : SingOrAll.card ≤ 4 * C.size := by
    calc
      SingOrAll.card ≤ ∑ gb ∈ Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)),
          (SingOrEdges gb.1 gb.2).card := Finset.card_biUnion_le
      _ ≤ ∑ _gb ∈ Finset.range C.gates.length ×ˢ (Finset.univ : Finset (Fin 2)), 2 :=
        Finset.sum_le_sum fun gb _ => hSingOrCard gb.1 gb.2
      _ = 4 * C.size := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
        change C.gates.length * 2 * 2 = 4 * C.gates.length
        omega
  -- Section 5: Master cover into IsoAll ∪ SingOrAll ∪ the 3 child finsets
  have hsub : E_target ⊆ IsoAll ∪ (SingOrAll ∪ (E1 ∪ (E2 ∪ E3))) := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heU, hNoBranch, a, ha_diff, ha_gam, ha_disj⟩ := he
    have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heU).1
    rw [Finset.mem_sdiff] at ha_diff
    obtain ⟨ha_top, ha_nc⟩ := ha_diff
    dsimp only [gammaE] at ha_gam
    rw [Finset.mem_filter] at ha_gam
    obtain ⟨_, u, v, rfl, ha_val⟩ := ha_gam
    have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp heE
    dsimp only [centreless] at ha_nc
    rw [Finset.mem_filter, not_and, not_or] at ha_nc
    have hs_ne := ha_nc ha_top
    obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.mpr hs_ne.1
    obtain ⟨p1, hp1⟩ := Finset.nonempty_iff_ne_empty.mpr hs_ne.2
    dsimp only [tops, gatesWhere] at ha_top
    rw [Finset.mem_filter] at ha_top
    have ha_lt : a < C.gates.length := Finset.mem_range.mp ha_top.1
    have ha_and : (gateAt C a).op = GateOp.and := ha_top.2.1
    have ha_below : BelowF G C a := ha_top.2.2
    have hp01_adj : G.Adj p0 p1 := by
      have hw0 : wireVal n C (opnd C a 0) (pairInput p0 p1) = true :=
        orIn_val (opnd C a 0) p0 (pairInput p0 p1) hp0 (decide_eq_true (Or.inl rfl))
      have hw1 : wireVal n C (opnd C a 1) (pairInput p0 p1) = true :=
        orIn_val (opnd C a 1) p1 (pairInput p0 p1) hp1 (decide_eq_true (Or.inr rfl))
      have hga : gateVal n C a (pairInput p0 p1) = true := by
        rw [gateVal_and a ha_lt ha_and, Bool.and_eq_true]; exact ⟨hw0, hw1⟩
      exact (graphFun_pair_iff p0 p1).mp (ha_below (pairInput p0 p1) hga)
    have hdisj_pt : ∀ w ∈ side C a 0 ∪ side C a 1, w ≠ u ∧ w ≠ v := by
      intro w hw
      have hnw := ha_disj w hw
      rw [Sym2.mem_iff, not_or] at hnw
      exact hnw
    have hp0_uv := hdisj_pt p0 (Finset.mem_union_left _ hp0)
    have hp1_uv := hdisj_pt p1 (Finset.mem_union_right _ hp1)
    have hsep := hEdgeSep p0 p1 u v hp01_adj huv hp0_uv.1.symm hp1_uv.1.symm hp0_uv.2.symm hp1_uv.2.symm
    have hs_side : ∃ s : Fin 2, ∃ p ∈ side C a s, u ≠ p ∧ ¬ G.Adj u p ∧ v ≠ p ∧ ¬ G.Adj v p := by
      rcases hsep with ⟨hu0, hv0⟩ | ⟨hu1, hv1⟩
      · exact ⟨0, p0, hp0, hp0_uv.1.symm, hu0, hp0_uv.2.symm, hv0⟩
      · exact ⟨1, p1, hp1, hp1_uv.1.symm, hu1, hp1_uv.2.symm, hv1⟩
    obtain ⟨s, p, hp_side, hup, huap, hvp, hvap⟩ := hs_side
    have ha_val' := ha_val
    rw [gateVal_and a ha_lt ha_and, Bool.and_eq_true] at ha_val'
    have hother_val : wireVal n C (opnd C a (1 - s)) (pairInput u v) = true := by
      fin_cases s
      · exact ha_val'.2
      · exact ha_val'.1
    have hother_or : ∀ i ∈ orIn n C (opnd C a (1 - s)), (pairInput u v) i = false := by
      intro i hi
      have him : i ∈ side C a 0 ∪ side C a 1 := by
        fin_cases s
        · exact Finset.mem_union_right _ hi
        · exact Finset.mem_union_left _ hi
      have hni := hdisj_pt i him
      change decide (i = u ∨ i = v) = false
      exact decide_eq_false (fun h => h.elim hni.1 hni.2)
    have hother_lt : opnd C a (1 - s) < n + C.gates.length := by
      obtain ⟨_, h0, h1, _⟩ := gate_inputs_pair a ha_lt
      fin_cases s
      · change opnd C a 1 < n + C.gates.length; omega
      · change opnd C a 0 < n + C.gates.length; omega
    obtain ⟨g, hg_lt, hg_rec, hg_and, hg_val⟩ :=
      extract_and_from_wire (opnd C a (1 - s)) hother_lt (pairInput u v) hother_val hother_or
    have hg_cone : InCone n C g a := orReaches_inCone a ha_lt (1 - s) g hg_rec
    have hg_not_below : ¬ BelowF G C g := fun hb =>
      hTop g hg_lt a ha_lt hg_and hb ha_and hg_cone
    have hg_junk : g ∈ junk G C := by
      dsimp only [junk, gatesWhere]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr hg_lt, hg_and, hg_lt, ?_⟩
      by_contra hnot
      exact hg_not_below (fun x hx =>
        Bool.eq_true_of_not_eq_false (fun hfalse => hnot ⟨x, hx, hfalse⟩))
    have hp_wmax : p ∈ wmax G C g := by
      dsimp only [wmax]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ p, fun x hgx hxp => ha_below x ?_⟩
      rw [gateVal_and a ha_lt ha_and, Bool.and_eq_true]
      have hps : wireVal n C (opnd C a s) x = true := orIn_val (opnd C a s) p x hp_side hxp
      have hpo : wireVal n C (opnd C a (1 - s)) x = true := orReaches_val (opnd C a (1 - s)) g x hg_rec hgx
      fin_cases s
      · exact ⟨hps, hpo⟩
      · exact ⟨hpo, hps⟩
    have hg_single_u : gateVal n C g (pairInput u u) = false := by
      by_contra hnot
      have htu : gateVal n C g (pairInput u u) = true := by
        cases hf : gateVal n C g (pairInput u u)
        · exact False.elim (hnot hf)
        · rfl
      have hup_val : gateVal n C g (pairInput u p) = true := by
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true] at htu
        have hmono : ∀ i : Fin n, pairInput u u i = true → pairInput u p i = true := fun i hi =>
          decide_eq_true (Or.inl ((of_decide_eq_true hi).elim id id))
        obtain ⟨_, hg0, hg1, _⟩ := gate_inputs_pair g hg_lt
        exact ⟨wireVal_mono (opnd C g 0) _ _ hmono htu.1, wireVal_mono (opnd C g 1) _ _ hmono htu.2⟩
      dsimp only [wmax] at hp_wmax
      rw [Finset.mem_filter] at hp_wmax
      have hgf := hp_wmax.2 (pairInput u p) hup_val (decide_eq_true (Or.inr rfl))
      rw [graphFun_pair_iff] at hgf
      exact huap hgf
    have hg_single_v : gateVal n C g (pairInput v v) = false := by
      by_contra hnot
      have htv : gateVal n C g (pairInput v v) = true := by
        cases hf : gateVal n C g (pairInput v v)
        · exact False.elim (hnot hf)
        · rfl
      have hvp_val : gateVal n C g (pairInput v p) = true := by
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true] at htv
        have hmono : ∀ i : Fin n, pairInput v v i = true → pairInput v p i = true := fun i hi =>
          decide_eq_true (Or.inl ((of_decide_eq_true hi).elim id id))
        exact ⟨wireVal_mono (opnd C g 0) _ _ hmono htv.1, wireVal_mono (opnd C g 1) _ _ hmono htv.2⟩
      dsimp only [wmax] at hp_wmax
      rw [Finset.mem_filter] at hp_wmax
      have hgf := hp_wmax.2 (pairInput v p) hvp_val (decide_eq_true (Or.inr rfl))
      rw [graphFun_pair_iff] at hgf
      exact hvap hgf
    by_cases hnest : ∃ b : Fin 2,
        wireVal n C (opnd C g b) (pairInput u u) = false ∧
        wireVal n C (opnd C g b) (pairInput v v) = false
    · obtain ⟨b, hbu, hbv⟩ := hnest
      have hb_uv : wireVal n C (opnd C g b) (pairInput u v) = true := by
        have hv := hg_val
        rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true] at hv
        fin_cases b
        · exact hv.1
        · exact hv.2
      have hb_or : ∀ i ∈ orIn n C (opnd C g b), (pairInput u v) i = false := by
        intro i hi
        by_contra hnot
        have hit : pairInput u v i = true := by
          cases hf : pairInput u v i
          · exact False.elim (hnot hf)
          · rfl
        rcases of_decide_eq_true hit with rfl | rfl
        · have := orIn_val (opnd C g b) i (pairInput i i) hi (decide_eq_true (Or.inl rfl))
          rw [this] at hbu; cases hbu
        · have := orIn_val (opnd C g b) i (pairInput i i) hi (decide_eq_true (Or.inl rfl))
          rw [this] at hbv; cases hbv
      have hb_lt : opnd C g b < n + C.gates.length := by
        obtain ⟨_, hg0, hg1, _⟩ := gate_inputs_pair g hg_lt
        fin_cases b
        · change opnd C g 0 < n + C.gates.length; omega
        · change opnd C g 1 < n + C.gates.length; omega
      obtain ⟨h, hh_lt, hh_rec, hh_and, hh_val⟩ :=
        extract_and_from_wire (opnd C g b) hb_lt (pairInput u v) hb_uv hb_or
      have hh_cone : InCone n C h g := orReaches_inCone g hg_lt b h hh_rec
      have hh_not_below : ¬ BelowF G C h := fun hb =>
        hTop h hh_lt g hg_lt hh_and hb hg_and hh_cone
      have hh_junk : h ∈ junk G C := by
        dsimp only [junk, gatesWhere]
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr hh_lt, hh_and, hh_lt, ?_⟩
        by_contra hnot
        exact hh_not_below (fun x hx =>
          Bool.eq_true_of_not_eq_false (fun hfalse => hnot ⟨x, hx, hfalse⟩))
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨heU, u, v, rfl, g, hg_junk, p, hp_wmax, b, hup, huap, hvp, hvap, hg_val, hbu, hbv,
            h, hh_junk, hh_rec, hh_val⟩))))
    · push Not at hnest
      have hbool_or : ∀ b : Fin 2,
          wireVal n C (opnd C g b) (pairInput u u) = true ∨
          wireVal n C (opnd C g b) (pairInput v v) = true := by
        intro b
        by_cases hbu : wireVal n C (opnd C g b) (pairInput u u) = true
        · exact Or.inl hbu
        · have hbu_f : wireVal n C (opnd C g b) (pairInput u u) = false := by
            cases hf : wireVal n C (opnd C g b) (pairInput u u)
            · rfl
            · exact False.elim (hbu hf)
          have hbv_ne := hnest b hbu_f
          right
          cases hf : wireVal n C (opnd C g b) (pairInput v v)
          · exact False.elim (hbv_ne hf)
          · rfl
      have hs0 := hbool_or 0
      have hs1 := hbool_or 1
      have hgu_and : ¬ (wireVal n C (opnd C g 0) (pairInput u u) = true ∧
          wireVal n C (opnd C g 1) (pairInput u u) = true) := by
        intro hconj
        obtain ⟨h0, h1⟩ := hconj
        have ht : gateVal n C g (pairInput u u) = true := by
          rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨h0, h1⟩
        rw [ht] at hg_single_u; cases hg_single_u
      have hgv_and : ¬ (wireVal n C (opnd C g 0) (pairInput v v) = true ∧
          wireVal n C (opnd C g 1) (pairInput v v) = true) := by
        intro hconj
        obtain ⟨h0, h1⟩ := hconj
        have ht : gateVal n C g (pairInput v v) = true := by
          rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨h0, h1⟩
        rw [ht] at hg_single_v; cases hg_single_v
      have hcross : (u ∈ Sset g p 0 ∧ v ∈ Sset g p 1) ∨ (v ∈ Sset g p 0 ∧ u ∈ Sset g p 1) := by
        rcases hs0 with h0u | h0v <;> rcases hs1 with h1u | h1v
        · exact False.elim (hgu_and ⟨h0u, h1u⟩)
        · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, hup, huap, h0u⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvp, hvap, h1v⟩⟩
        · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvp, hvap, h0v⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ u, hup, huap, h1u⟩⟩
        · exact False.elim (hgv_and ⟨h0v, h1v⟩)
      have handle_crossing : ∀ u' v' : Fin n, s(u, v) = s(u', v') →
          u' ≠ p → ¬ G.Adj u' p → v' ≠ p → ¬ G.Adj v' p →
          G.Adj u' v' →
          (∀ h < C.gates.length, ∀ c : Fin 2,
            2 ≤ (orIn n C (n + h)).card → (∀ z ∈ orIn n C (n + h), G.Adj u' z) →
            orIn n C (opnd C h c) ≠ {v'}) →
          u' ∈ Sset g p 0 → v' ∈ Sset g p 1 →
          s(u, v) ∈ IsoAll ∪ (SingOrAll ∪ (E1 ∪ (E2 ∪ E3))) := by
        intro u' v' he_eq hu'p hu'ap hv'p hv'ap hu'v' hNoB' hu'_S hv'_S
        rcases hStarSide g hg_junk p hp_wmax with hs0_le | hs1_le
        · have hs0_sing : Sset g p 0 = {u'} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨hu'_S, fun y hy => Finset.card_le_one.mp hs0_le y hy u' hu'_S⟩
          by_cases hs1_le' : (Sset g p 1).card ≤ 1
          · have hs1_sing : Sset g p 1 = {v'} :=
              Finset.eq_singleton_iff_unique_mem.mpr ⟨hv'_S, fun y hy => Finset.card_le_one.mp hs1_le' y hy v' hv'_S⟩
            apply Finset.mem_union_left
            rw [he_eq, Finset.mem_biUnion]
            refine ⟨g, Finset.mem_range.mpr hg_lt, Finset.mem_image.mpr ⟨(u', v'), ?_, rfl⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ u', Finset.mem_univ v'⟩,
              hg_junk, hu'v', p, hp_wmax, hs0_sing, hs1_sing⟩
          · have h1m0 : (1 - (0 : Fin 2) : Fin 2) = 1 := rfl
            have hu'_val : wireVal n C (opnd C g 0) (pairInput u' u') = true := by
              rw [Finset.mem_filter] at hu'_S; exact hu'_S.2.2.2
            have hu'_uniq : ∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
                wireVal n C (opnd C g 0) (pairInput x x) = true → x = u' := by
              intro x hxp hxap hxv
              have hx_S : x ∈ Sset g p 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxp, hxap, hxv⟩
              rw [hs0_sing, Finset.mem_singleton] at hx_S
              exact hx_S
            by_cases hvor : v' ∈ orIn n C (opnd C g 1)
            · by_cases hor_le : (orIn n C (opnd C g 1)).card ≤ 1
              · have hor_sing : orIn n C (opnd C g 1) = {v'} :=
                  Finset.eq_singleton_iff_unique_mem.mpr
                    ⟨hvor, fun y hy => Finset.card_le_one.mp hor_le y hy v' hvor⟩
                apply Finset.mem_union_right
                apply Finset.mem_union_left
                rw [Finset.mem_biUnion]
                refine ⟨(g, 0), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hg_lt, Finset.mem_univ 0⟩,
                  Finset.mem_filter.mpr ⟨heE, u', v', he_eq, hg_junk,
                    p, hp_wmax, hs0_sing, hv'_S, hor_sing⟩⟩
              · have hnot_all : ¬ ∀ z ∈ orIn n C (opnd C g 1), G.Adj u' z := by
                  intro hall
                  have hor1_lt : opnd C g 1 < n + C.gates.length := by
                    obtain ⟨_, _, hg1, _⟩ := gate_inputs_pair g hg_lt; omega
                  obtain ⟨h, hh_lt, c, hbc1, hbc2, hbc3⟩ :=
                    branching_or_descent (opnd C g 1) hor1_lt u' v' hvor (by omega) hall
                  exact hNoB' h hh_lt c hbc1 hbc2 hbc3
                push Not at hnot_all
                obtain ⟨z, hz_or, hz_na⟩ := hnot_all
                have hzp_adj : G.Adj p z := by
                  let y : Fin n → Bool := fun w => decide (w = u' ∨ w = z ∨ w = p)
                  have hy0 : wireVal n C (opnd C g 0) y = true :=
                    wireVal_mono (opnd C g 0) (pairInput u' u') y (fun i hi => by
                      have hi' : i = u' := (of_decide_eq_true hi).elim id id
                      exact decide_eq_true (Or.inl hi')) hu'_val
                  have hy1 : wireVal n C (opnd C g 1) y = true :=
                    orIn_val (opnd C g 1) z y hz_or (decide_eq_true (Or.inr (Or.inl rfl)))
                  have hgy : gateVal n C g y = true := by
                    rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨hy0, hy1⟩
                  dsimp only [wmax] at hp_wmax
                  rw [Finset.mem_filter] at hp_wmax
                  have hgf := hp_wmax.2 y hgy (decide_eq_true (Or.inr (Or.inr rfl)))
                  change (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a = u' ∨ a = z ∨ a = p) = true) ||
                    decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = u' ∨ a = z ∨ a = p) = true ∧
                      decide (b = u' ∨ b = z ∨ b = p) = true)) = true at hgf
                  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
                    decide_eq_true_eq] at hgf
                  obtain ⟨a, b, hab, ha, hb⟩ := hgf
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact False.elim (G.ne_of_adj hab rfl)
                  · exact False.elim (hz_na hab)
                  · exact False.elim (hu'ap hab)
                  · exact False.elim (hz_na hab.symm)
                  · exact False.elim (G.ne_of_adj hab rfl)
                  · exact hab.symm
                  · exact False.elim (hu'ap hab.symm)
                  · exact hab
                  · exact False.elim (G.ne_of_adj hab rfl)
                exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
                  ((hE1_mem _).mpr ⟨heU, u', v', he_eq, g, hg_junk, p, hp_wmax, 0,
                    hu'p, hu'ap, hv'p, hv'ap, hu'_val, hu'_uniq, hvor, z, hz_or, hz_na, hzp_adj⟩)))
            · have hv'_or_false : ∀ i ∈ orIn n C (opnd C g 1), (pairInput v' v') i = false := by
                intro i hi
                change decide (i = v' ∨ i = v') = false
                exact decide_eq_false (fun h => hvor (by rcases h with rfl | rfl <;> exact hi))
              have hv'_val : wireVal n C (opnd C g 1) (pairInput v' v') = true := by
                rw [Finset.mem_filter] at hv'_S; exact hv'_S.2.2.2
              have hor1_lt : opnd C g 1 < n + C.gates.length := by
                obtain ⟨_, _, hg1, _⟩ := gate_inputs_pair g hg_lt; omega
              obtain ⟨h, hh_lt, hh_rec, hh_and, hh_val⟩ :=
                extract_and_from_wire (opnd C g 1) hor1_lt (pairInput v' v') hv'_val hv'_or_false
              have hh_cone : InCone n C h g := orReaches_inCone g hg_lt 1 h hh_rec
              have hh_not_below : ¬ BelowF G C h := fun hb =>
                hTop h hh_lt g hg_lt hh_and hb hg_and hh_cone
              have hh_junk : h ∈ junk G C := by
                dsimp only [junk, gatesWhere]
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_range.mpr hh_lt, hh_and, hh_lt, ?_⟩
                by_contra hnot
                exact hh_not_below (fun x hx =>
                  Bool.eq_true_of_not_eq_false (fun hfalse => hnot ⟨x, hx, hfalse⟩))
              exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_union_left _ ((hE2_mem _).mpr
                  ⟨heU, u', v', he_eq, g, hg_junk, p, hp_wmax, 0, hu'p, hu'ap, hv'p, hv'ap,
                    hu'_val, hu'_uniq, h, hh_junk, hh_rec, hh_val⟩))))
        · have hs1_sing : Sset g p 1 = {v'} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨hv'_S, fun y hy => Finset.card_le_one.mp hs1_le y hy v' hv'_S⟩
          have hv'_val : wireVal n C (opnd C g 1) (pairInput v' v') = true := by
            rw [Finset.mem_filter] at hv'_S; exact hv'_S.2.2.2
          have hv'_uniq : ∀ x : Fin n, x ≠ p → ¬ G.Adj x p →
              wireVal n C (opnd C g 1) (pairInput x x) = true → x = v' := by
            intro x hxp hxap hxv
            have hx_S : x ∈ Sset g p 1 := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxp, hxap, hxv⟩
            rw [hs1_sing, Finset.mem_singleton] at hx_S
            exact hx_S
          by_cases hs0_le' : (Sset g p 0).card ≤ 1
          · have hs0_sing : Sset g p 0 = {u'} :=
              Finset.eq_singleton_iff_unique_mem.mpr ⟨hu'_S, fun y hy => Finset.card_le_one.mp hs0_le' y hy u' hu'_S⟩
            apply Finset.mem_union_left
            rw [he_eq, Finset.mem_biUnion]
            refine ⟨g, Finset.mem_range.mpr hg_lt, Finset.mem_image.mpr ⟨(u', v'), ?_, rfl⟩⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ u', Finset.mem_univ v'⟩,
              hg_junk, hu'v', p, hp_wmax, hs0_sing, hs1_sing⟩
          · by_cases huor : u' ∈ orIn n C (opnd C g 0)
            · by_cases hor_le : (orIn n C (opnd C g 0)).card ≤ 1
              · have hor_sing : orIn n C (opnd C g 0) = {u'} :=
                  Finset.eq_singleton_iff_unique_mem.mpr
                    ⟨huor, fun y hy => Finset.card_le_one.mp hor_le y hy u' huor⟩
                apply Finset.mem_union_right
                apply Finset.mem_union_left
                rw [Finset.mem_biUnion]
                refine ⟨(g, 1), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hg_lt, Finset.mem_univ 1⟩,
                  Finset.mem_filter.mpr ⟨heE, v', u',
                    he_eq.trans Sym2.eq_swap, hg_junk, p, hp_wmax, hs1_sing, hu'_S, hor_sing⟩⟩
              · have hnot_all : ¬ ∀ z ∈ orIn n C (opnd C g 0), G.Adj v' z := by
                  intro hall
                  have hor0_lt : opnd C g 0 < n + C.gates.length := by
                    obtain ⟨_, hg0, _, _⟩ := gate_inputs_pair g hg_lt; omega
                  obtain ⟨h, hh_lt, c, hbc1, hbc2, hbc3⟩ :=
                    branching_or_descent (opnd C g 0) hor0_lt v' u' huor (by omega) hall
                  exact hNoBranch ⟨v', u', he_eq.trans Sym2.eq_swap, h, hh_lt, c, hbc1, hbc2, hbc3⟩
                push Not at hnot_all
                obtain ⟨z, hz_or, hz_na⟩ := hnot_all
                have hzp_adj : G.Adj p z := by
                  let y : Fin n → Bool := fun w => decide (w = v' ∨ w = z ∨ w = p)
                  have hy1 : wireVal n C (opnd C g 1) y = true :=
                    wireVal_mono (opnd C g 1) (pairInput v' v') y (fun i hi => by
                      have hi' : i = v' := (of_decide_eq_true hi).elim id id
                      exact decide_eq_true (Or.inl hi')) hv'_val
                  have hy0 : wireVal n C (opnd C g 0) y = true :=
                    orIn_val (opnd C g 0) z y hz_or (decide_eq_true (Or.inr (Or.inl rfl)))
                  have hgy : gateVal n C g y = true := by
                    rw [gateVal_and g hg_lt hg_and, Bool.and_eq_true]; exact ⟨hy0, hy1⟩
                  dsimp only [wmax] at hp_wmax
                  rw [Finset.mem_filter] at hp_wmax
                  have hgf := hp_wmax.2 y hgy (decide_eq_true (Or.inr (Or.inr rfl)))
                  change (decide (∃ a ∈ (∅ : Finset (Fin n)), decide (a = v' ∨ a = z ∨ a = p) = true) ||
                    decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = v' ∨ a = z ∨ a = p) = true ∧
                      decide (b = v' ∨ b = z ∨ b = p) = true)) = true at hgf
                  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
                    decide_eq_true_eq] at hgf
                  obtain ⟨a, b, hab, ha, hb⟩ := hgf
                  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                  · exact False.elim (G.ne_of_adj hab rfl)
                  · exact False.elim (hz_na hab)
                  · exact False.elim (hv'ap hab)
                  · exact False.elim (hz_na hab.symm)
                  · exact False.elim (G.ne_of_adj hab rfl)
                  · exact hab.symm
                  · exact False.elim (hv'ap hab.symm)
                  · exact hab
                  · exact False.elim (G.ne_of_adj hab rfl)
                exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
                  ((hE1_mem _).mpr ⟨heU, v', u', he_eq.trans Sym2.eq_swap,
                    g, hg_junk, p, hp_wmax, 1, hv'p, hv'ap, hu'p, hu'ap,
                    hv'_val, hv'_uniq, huor, z, hz_or, hz_na, hzp_adj⟩)))
            · have hu'_or_false : ∀ i ∈ orIn n C (opnd C g 0), (pairInput u' u') i = false := by
                intro i hi
                change decide (i = u' ∨ i = u') = false
                exact decide_eq_false (fun h => huor (by rcases h with rfl | rfl <;> exact hi))
              have hu'_val : wireVal n C (opnd C g 0) (pairInput u' u') = true := by
                rw [Finset.mem_filter] at hu'_S; exact hu'_S.2.2.2
              have hor0_lt : opnd C g 0 < n + C.gates.length := by
                obtain ⟨_, hg0, _, _⟩ := gate_inputs_pair g hg_lt; omega
              obtain ⟨h, hh_lt, hh_rec, hh_and, hh_val⟩ :=
                extract_and_from_wire (opnd C g 0) hor0_lt (pairInput u' u') hu'_val hu'_or_false
              have hh_cone : InCone n C h g := orReaches_inCone g hg_lt 0 h hh_rec
              have hh_not_below : ¬ BelowF G C h := fun hb =>
                hTop h hh_lt g hg_lt hh_and hb hg_and hh_cone
              have hh_junk : h ∈ junk G C := by
                dsimp only [junk, gatesWhere]
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_range.mpr hh_lt, hh_and, hh_lt, ?_⟩
                by_contra hnot
                exact hh_not_below (fun x hx =>
                  Bool.eq_true_of_not_eq_false (fun hfalse => hnot ⟨x, hx, hfalse⟩))
              exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_union_left _ ((hE2_mem _).mpr
                  ⟨heU, v', u', he_eq.trans Sym2.eq_swap, g, hg_junk, p, hp_wmax, 1,
                    hv'p, hv'ap, hu'p, hu'ap, hv'_val, hv'_uniq, h, hh_junk, hh_rec, hh_val⟩))))
      rcases hcross with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
      · exact handle_crossing u v rfl hup huap hvp hvap huv
          (fun h hh c h1 h2 h3 => hNoBranch ⟨u, v, rfl, h, hh, c, h1, h2, h3⟩) hu0 hv1
      · exact handle_crossing v u Sym2.eq_swap hvp hvap hup huap huv.symm
          (fun h hh c h1 h2 h3 => hNoBranch ⟨v, u, Sym2.eq_swap, h, hh, c, h1, h2, h3⟩) hv0 hu1
  have hcard : E_target.card ≤ IsoAll.card + (SingOrAll.card + (E1.card + (E2.card + E3.card))) :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
          ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
            (Finset.card_union_le _ _) _)) _)) _))
  change E_target.card ≤ (6 + k1 + k2 + k3) * (C.size + 1)
  rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega
