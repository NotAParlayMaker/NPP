import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3655

open PEqualNP.CircuitLowerBounds

def gates : List Gate :=
  [⟨.or, [7, 8]⟩,
   ⟨.or, [14, 12]⟩,
   ⟨.and, [1, 15]⟩,
   ⟨.or, [8, 9]⟩,
   ⟨.or, [17, 13]⟩,
   ⟨.and, [2, 18]⟩,
   ⟨.or, [7, 9]⟩,
   ⟨.or, [20, 10]⟩,
   ⟨.and, [3, 21]⟩,
   ⟨.or, [8, 10]⟩,
   ⟨.or, [23, 11]⟩,
   ⟨.and, [4, 24]⟩,
   ⟨.or, [9, 11]⟩,
   ⟨.or, [26, 12]⟩,
   ⟨.and, [5, 27]⟩,
   ⟨.or, [10, 12]⟩,
   ⟨.or, [29, 13]⟩,
   ⟨.and, [6, 30]⟩,
   ⟨.and, [0, 7]⟩,
   ⟨.and, [0, 13]⟩,
   ⟨.or, [7, 11]⟩,
   ⟨.and, [0, 34]⟩,
   ⟨.or, [11, 13]⟩,
   ⟨.and, [0, 36]⟩,
   ⟨.and, [35, 37]⟩,
   ⟨.or, [16, 19]⟩,
   ⟨.or, [39, 22]⟩,
   ⟨.or, [40, 25]⟩,
   ⟨.or, [41, 28]⟩,
   ⟨.or, [42, 31]⟩,
   ⟨.or, [43, 32]⟩,
   ⟨.or, [44, 33]⟩,
   ⟨.or, [45, 38]⟩]

def circ : Circuit := ⟨gates, 46⟩

def Fb (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : Bool :=
  (b0 && b7) || (b0 && b11) || (b0 && b13) || (b1 && b7) || (b1 && b8) || (b1 && b12) || (b2 && b8) || (b2 && b9) || (b2 && b13) || (b3 && b7) || (b3 && b9) || (b3 && b10) || (b4 && b8) || (b4 && b10) || (b4 && b11) || (b5 && b9) || (b5 && b11) || (b5 && b12) || (b6 && b10) || (b6 && b12) || (b6 && b13)

lemma fb_iff (z : Fin 14 → Bool) :
    decide (∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧
      z (Fin.castAdd 7 p3) = true ∧ z (Fin.natAdd 7 l3) = true) = Fb (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10) (z 11) (z 12) (z 13) := by
  simp [Fin.exists_fin_succ, Fb, Bool.or_assoc]

lemma adj_iff (x : Fin 14 → Bool) :
    (∃ u v : Fin 14, (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)).Adj u v ∧ x u = true ∧ x v = true) ↔
    ∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧
      x (Fin.castAdd 7 p3) = true ∧ x (Fin.natAdd 7 l3) = true := by
  constructor
  · rintro ⟨u, v, ⟨-, (⟨pa, la, hi, rfl, rfl⟩ | ⟨pa, la, hi, rfl, rfl⟩)⟩, hu, hv⟩
    · exact ⟨pa, la, hi, hu, hv⟩
    · exact ⟨pa, la, hi, hv, hu⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨Fin.castAdd 7 p, Fin.natAdd 7 l, ⟨?_, Or.inl ⟨p, l, hi, rfl, rfl⟩⟩, hp, hl⟩
    intro h
    have h2 := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
    omega

open PEqualNP.MetaComplexity.NestedCover in
lemma gf (x : Fin 14 → Bool) :
    graphFun (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) ∅ x = Fb (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13) := by
  rw [← fb_iff x]
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  exact decide_eq_decide.mpr (adj_iff x)

lemma ofFn14 (x : Fin 14 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by
  simp [List.ofFn_succ]

lemma evalK (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) :
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] = Fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 := by
  simp [Circuit.eval, Circuit.wires, circ, gates, GateOp.eval, Fb]
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
  decide +kernel

lemma below_of (j : ℕ)
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
      (!((circ.wires [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13]).getD (14 + j) false) || Fb b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13) = true) :
    PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ j := by
  intro x hx
  rw [gf]
  unfold PEqualNP.EdgeOwnership.gateVal at hx
  rw [ofFn14] at hx
  have h5 := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) (x 11) (x 12) (x 13)
  rw [hx] at h5
  simpa using h5

lemma below21 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 21 :=
  below_of 21 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below23 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 23 :=
  below_of 23 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below24 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 24 :=
  below_of 24 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below25 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 25 :=
  below_of 25 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below26 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 26 :=
  below_of 26 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below27 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 27 :=
  below_of 27 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below28 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 28 :=
  below_of 28 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below29 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 29 :=
  below_of 29 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below30 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 30 :=
  below_of 30 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below31 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 31 :=
  below_of 31 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma below32 : PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ 32 :=
  below_of 32 (by
    intro b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    simp only [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, circ, gates, List.foldl_cons, List.map_cons, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, List.map_nil, List.any_cons, id_eq, List.any_nil, Bool.or_false, List.cons_append, List.nil_append, Nat.lt_add_one, Nat.one_lt_ofNat, List.all_cons, List.all_nil, Bool.and_true, Nat.ofNat_pos, List.foldl_nil, Fb]
    revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
    decide +kernel)

lemma not_imp (w : ℕ) (k : Fin 14)
    (h1 : (circ.wires (List.ofFn fun i : Fin 14 => decide (i = k))).getD w false = true)
    (h2 : Fb (decide ((0 : Fin 14) = k)) (decide ((1 : Fin 14) = k)) (decide ((2 : Fin 14) = k)) (decide ((3 : Fin 14) = k)) (decide ((4 : Fin 14) = k)) (decide ((5 : Fin 14) = k)) (decide ((6 : Fin 14) = k)) (decide ((7 : Fin 14) = k)) (decide ((8 : Fin 14) = k)) (decide ((9 : Fin 14) = k)) (decide ((10 : Fin 14) = k)) (decide ((11 : Fin 14) = k)) (decide ((12 : Fin 14) = k)) (decide ((13 : Fin 14) = k)) = false) :
    ¬ PEqualNP.Core.IsImpWire (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ w := by
  rintro ⟨hall, -⟩
  have h3 := hall (fun i => decide (i = k)) h1
  rw [gf] at h3
  have h4 : Fb (decide ((0 : Fin 14) = k)) (decide ((1 : Fin 14) = k)) (decide ((2 : Fin 14) = k)) (decide ((3 : Fin 14) = k)) (decide ((4 : Fin 14) = k)) (decide ((5 : Fin 14) = k)) (decide ((6 : Fin 14) = k)) (decide ((7 : Fin 14) = k)) (decide ((8 : Fin 14) = k)) (decide ((9 : Fin 14) = k)) (decide ((10 : Fin 14) = k)) (decide ((11 : Fin 14) = k)) (decide ((12 : Fin 14) = k)) (decide ((13 : Fin 14) = k)) = true := h3
  rw [h2] at h4
  exact Bool.false_ne_true h4

lemma lift : PEqualNP.Core.IsLiftFixedPoint (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) circ := by
  rintro ⟨h, hh, b, -, hor, hnb, himp⟩
  have hh' : h < 33 := hh
  interval_cases h <;> fin_cases b
  · exact not_imp _ 7 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 8 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 7 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 12 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 8 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 9 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 8 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 13 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 7 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 9 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 7 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 10 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 8 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 10 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 8 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 11 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 9 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 11 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 9 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 12 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 10 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 12 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 10 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 13 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 7 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 11 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact not_imp _ 11 (by decide +kernel) (by decide +kernel) himp
  · exact not_imp _ 13 (by decide +kernel) (by decide +kernel) himp
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · simp [PEqualNP.MetaComplexity.NestedCover.gateAt, circ, gates] at hor
  · exact hnb below25
  · exact hnb below25
  · exact hnb below26
  · exact hnb below26
  · exact hnb below27
  · exact hnb below27
  · exact hnb below28
  · exact hnb below28
  · exact hnb below29
  · exact hnb below29
  · exact hnb below30
  · exact hnb below30
  · exact hnb below31
  · exact hnb below31
  · exact hnb below32
  · exact hnb below32

end PEqualNP.Outside.L_meta_3655

theorem PEqualNP.Outside.L_meta_3655 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 } → (∀ z : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C z = decide (∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧ z (Fin.castAdd 7 p3) = true ∧ z (Fin.natAdd 7 l3) = true)) ∧ (PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) C 21 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ub vb : Fin 14 => ∃ pb lb : Fin 7, (pb.val = lb.val ∨ pb.val = (lb.val + 1) % 7 ∨ pb.val = (lb.val + 3) % 7) ∧ ub = Fin.castAdd 7 pb ∧ vb = Fin.natAdd 7 lb)) C 23 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun uc vc : Fin 14 => ∃ pc lc : Fin 7, (pc.val = lc.val ∨ pc.val = (lc.val + 1) % 7 ∨ pc.val = (lc.val + 3) % 7) ∧ uc = Fin.castAdd 7 pc ∧ vc = Fin.natAdd 7 lc)) C 24) ∧ PEqualNP.Core.IsLiftFixedPoint (SimpleGraph.fromRel (fun ud vd : Fin 14 => ∃ pd ld : Fin 7, (pd.val = ld.val ∨ pd.val = (ld.val + 1) % 7 ∨ pd.val = (ld.val + 3) % 7) ∧ ud = Fin.castAdd 7 pd ∧ vd = Fin.natAdd 7 ld)) C ∧ PEqualNP.ReadK.doubleReread C 14 (fun w => decide (7 ≤ w)) ((List.finRange 7).flatMap (fun p5 => ((List.finRange 7).filter (fun l5 => decide (p5.val = l5.val ∨ p5.val = (l5.val + 1) % 7 ∨ p5.val = (l5.val + 3) % 7))).map (fun l6 => (p5.val, 7 + l6.val)))) = [(0, 11)] := by
  intro C hC
  subst hC
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z
    rw [PEqualNP.Outside.L_meta_3655.fb_iff]
    show PEqualNP.Outside.L_meta_3655.circ.eval (List.ofFn z) = _
    rw [PEqualNP.Outside.L_meta_3655.ofFn14]
    exact PEqualNP.Outside.L_meta_3655.evalK (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7) (z 8) (z 9) (z 10) (z 11) (z 12) (z 13)
  · exact PEqualNP.Outside.L_meta_3655.below21
  · exact PEqualNP.Outside.L_meta_3655.below23
  · exact PEqualNP.Outside.L_meta_3655.below24
  · exact PEqualNP.Outside.L_meta_3655.lift
  · decide +kernel
