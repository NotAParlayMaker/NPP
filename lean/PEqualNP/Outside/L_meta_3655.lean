import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3655_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 }

def Gf (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool := (a0 && b0) || ((a0 && b4) || ((a0 && b6) || ((a1 && b0) || ((a1 && b1) || ((a1 && b5) || ((a2 && b1) || ((a2 && b2) || ((a2 && b6) || ((a3 && b0) || ((a3 && b2) || ((a3 && b3) || ((a4 && b1) || ((a4 && b3) || ((a4 && b4) || ((a5 && b2) || ((a5 && b4) || ((a5 && b5) || ((a6 && b3) || ((a6 && b5) || ((a6 && b6)))))))))))))))))))))

def chk (w : List Bool) (g : Bool) : Bool := (w.getD 46 false == g) && [35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46].all (fun j => !(w.getD j false) || g)

theorem chk_out (w : List Bool) (g : Bool) (h : chk w g = true) : w.getD 46 false = g := by
  unfold chk at h
  rw [Bool.and_eq_true] at h
  exact beq_iff_eq.mp h.1

theorem chk_bel (w : List Bool) (g : Bool) (h : chk w g = true) (j : ℕ) (hj : j ∈ [35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]) (hw : w.getD j false = true) : g = true := by
  unfold chk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 j hj
  rw [hw] at h2
  simpa using h2

set_option maxHeartbeats 4000000 in
theorem K : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, chk (circ.wires [a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6]) (Gf a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) = true := by
  intro a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
  simp only [chk, circ, Circuit.wires, List.foldl, List.map, GateOp.eval, List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
  revert b0 b1 b2 b3 b4 b5 b6
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> decide +kernel

theorem Kx (x : Fin 14 → Bool) : chk (circ.wires (List.ofFn x)) (Gf (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)) = true := by
  have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by
    simp [List.ofFn_succ]
  rw [h]
  exact K (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)

theorem gF (x : Fin 14 → Bool) : graphFun (SimpleGraph.fromRel (fun u v : Fin 14 => ∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)) ∅ x = decide (∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) := by
  unfold PEqualNP.MetaComplexity.NestedCover.graphFun
  have h : (∃ u v, (SimpleGraph.fromRel (fun u v : Fin 14 => ∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)).Adj u v ∧ x u = true ∧ x v = true) ↔ (∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) := by
    simp only [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨u, v, ⟨_, ⟨p, l, h, rfl, rfl⟩ | ⟨p, l, h, rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨p, l, h, hu, hv⟩
      · exact ⟨p, l, h, hv, hu⟩
    · rintro ⟨p, l, h, hu, hv⟩
      refine ⟨Fin.castAdd 7 p, Fin.natAdd 7 l, ⟨?_, Or.inl ⟨p, l, h, rfl, rfl⟩⟩, hu, hv⟩
      intro hne
      have := congrArg Fin.val hne
      simp at this
      omega
  have e : ¬ (∃ a ∈ (∅ : Finset (Fin 14)), x a = true) := by simp
  rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact ⟨fun t => t.elim (fun q => absurd q e) h.mp, fun t => Or.inr (h.mpr t)⟩

theorem eq2 (xa ya : Fin 7 → Bool) : decide (∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ xa p = true ∧ ya l = true) = Gf (xa 0) (xa 1) (xa 2) (xa 3) (xa 4) (xa 5) (xa 6) (ya 0) (ya 1) (ya 2) (ya 3) (ya 4) (ya 5) (ya 6) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨p, l, h, hx, hy⟩
    fin_cases p <;> fin_cases l
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [Gf, hx, hy]
    · simp at hx hy
      simp [Gf, hx, hy]
  · intro h
    simp only [Gf, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨0, 0, by decide, hx, hy⟩
    · exact ⟨0, 4, by decide, hx, hy⟩
    · exact ⟨0, 6, by decide, hx, hy⟩
    · exact ⟨1, 0, by decide, hx, hy⟩
    · exact ⟨1, 1, by decide, hx, hy⟩
    · exact ⟨1, 5, by decide, hx, hy⟩
    · exact ⟨2, 1, by decide, hx, hy⟩
    · exact ⟨2, 2, by decide, hx, hy⟩
    · exact ⟨2, 6, by decide, hx, hy⟩
    · exact ⟨3, 0, by decide, hx, hy⟩
    · exact ⟨3, 2, by decide, hx, hy⟩
    · exact ⟨3, 3, by decide, hx, hy⟩
    · exact ⟨4, 1, by decide, hx, hy⟩
    · exact ⟨4, 3, by decide, hx, hy⟩
    · exact ⟨4, 4, by decide, hx, hy⟩
    · exact ⟨5, 2, by decide, hx, hy⟩
    · exact ⟨5, 4, by decide, hx, hy⟩
    · exact ⟨5, 5, by decide, hx, hy⟩
    · exact ⟨6, 3, by decide, hx, hy⟩
    · exact ⟨6, 5, by decide, hx, hy⟩
    · exact ⟨6, 6, by decide, hx, hy⟩

theorem bel (j : ℕ) (hj : 14 + j ∈ [35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]) : BelowF (SimpleGraph.fromRel (fun u v : Fin 14 => ∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)) circ j := by
  intro x hx
  rw [gF x]
  refine (eq2 (fun p => x (Fin.castAdd 7 p)) (fun l => x (Fin.natAdd 7 l))).trans ?_
  exact chk_bel _ _ (Kx x) (14 + j) hj hx

theorem pt1 (z : Fin 14 → Bool) : circuitFun 14 circ z = decide (∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) := by
  have e : decide (∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) = Gf (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10) (z 11) (z 12) (z 13) := eq2 (fun p => z (Fin.castAdd 7 p)) (fun l => z (Fin.natAdd 7 l))
  have k : (circ.wires (List.ofFn z)).getD 46 false = Gf (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10) (z 11) (z 12) (z 13) := chk_out _ _ (Kx z)
  rw [e]
  exact k

def x0 : Fin 14 → Bool := fun i => decide (7 ≤ i.val)

theorem nx0 : graphFun (SimpleGraph.fromRel (fun u v : Fin 14 => ∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)) ∅ x0 = false := by
  rw [gF x0]
  exact (eq2 (fun p => x0 (Fin.castAdd 7 p)) (fun l => x0 (Fin.natAdd 7 l))).trans (by decide)

theorem lfp : IsLiftFixedPoint (SimpleGraph.fromRel (fun u v : Fin 14 => ∃ p l : Fin 7, (p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7) ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)) circ := by
  intro hL
  obtain ⟨h, hh, b, hc, hop, hnb, himp⟩ := hL
  have hh2 : h < 33 := hh
  interval_cases h <;> fin_cases b <;> first | (cases hop; done) | exact hnb (bel _ (by decide)) | exact absurd (himp.1 x0 (by decide +kernel)) (by rw [nx0]; simp)

end PEqualNP.Outside.L_meta_3655_aux

open PEqualNP.Outside.L_meta_3655_aux in
theorem PEqualNP.Outside.L_meta_3655 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 } → (∀ z : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C z = decide (∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧ z (Fin.castAdd 7 p3) = true ∧ z (Fin.natAdd 7 l3) = true)) ∧ (PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) C 21 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ub vb : Fin 14 => ∃ pb lb : Fin 7, (pb.val = lb.val ∨ pb.val = (lb.val + 1) % 7 ∨ pb.val = (lb.val + 3) % 7) ∧ ub = Fin.castAdd 7 pb ∧ vb = Fin.natAdd 7 lb)) C 23 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun uc vc : Fin 14 => ∃ pc lc : Fin 7, (pc.val = lc.val ∨ pc.val = (lc.val + 1) % 7 ∨ pc.val = (lc.val + 3) % 7) ∧ uc = Fin.castAdd 7 pc ∧ vc = Fin.natAdd 7 lc)) C 24) ∧ PEqualNP.Core.IsLiftFixedPoint (SimpleGraph.fromRel (fun ud vd : Fin 14 => ∃ pd ld : Fin 7, (pd.val = ld.val ∨ pd.val = (ld.val + 1) % 7 ∨ pd.val = (ld.val + 3) % 7) ∧ ud = Fin.castAdd 7 pd ∧ vd = Fin.natAdd 7 ld)) C ∧ PEqualNP.ReadK.doubleReread C 14 (fun w => decide (7 ≤ w)) ((List.finRange 7).flatMap (fun p5 => ((List.finRange 7).filter (fun l5 => decide (p5.val = l5.val ∨ p5.val = (l5.val + 1) % 7 ∨ p5.val = (l5.val + 3) % 7))).map (fun l6 => (p5.val, 7 + l6.val)))) = [(0, 11)] := by
  intro C hC
  subst hC
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z
    exact pt1 z
  · exact bel 21 (by decide)
  · exact bel 23 (by decide)
  · exact bel 24 (by decide)
  · exact lfp
  · decide +kernel
