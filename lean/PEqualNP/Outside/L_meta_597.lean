import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_597_aux

open CircuitLowerBounds MetaComplexity

private abbrev T := BitVec 11
-- The first six rows are the edges in statement order. The remaining rows
-- are the independent sets 13, 14, 23, 24, and the singleton 0.
private def ins : List T := [1051,197,774,360,688]
private def target : T := 63
-- A dominating wire accepts more edge rows and rejects more independent rows.
private def dom (x y : T) : Bool :=
  ((x ^^^ 1984) &&& (y ^^^ 1984)) == (x ^^^ 1984)

private theorem dom_iff (x y : T) : dom x y ↔
    ∀ i : Fin 11, (x[i.val] ^^ (1984 : T)[i.val]) = true →
      (y[i.val] ^^ (1984 : T)[i.val]) = true := by
  simp only [dom, beq_iff_eq]
  constructor
  · intro h i
    have H := congrArg (fun v : T => v[i.val]) h
    simp only [BitVec.getElem_and, BitVec.getElem_xor] at H
    revert H
    generalize (x[↑i] ^^ (1984 : T)[↑i]) = a
    generalize (y[↑i] ^^ (1984 : T)[↑i]) = b
    cases a <;> cases b <;> decide
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    specialize h ⟨i,hi⟩
    simp only [BitVec.getElem_and, BitVec.getElem_xor]
    revert h
    generalize (x[i] ^^ (1984 : T)[i]) = a
    generalize (y[i] ^^ (1984 : T)[i]) = b
    cases a <;> cases b <;> decide

private theorem dtrans {a b c : T} (h : dom a b) (j : dom b c) : dom a c :=
  (dom_iff ..).2 (fun i => ((dom_iff ..).1 j i) ∘ ((dom_iff ..).1 h i))

private theorem dops {a b c d : T} (h : dom a b) (j : dom c d) :
    dom (a &&& c) (b &&& d) ∧ dom (a ||| c) (b ||| d) := by
  have finite : ∀ a b c d f : Bool, ((a ^^ f) = true → (b ^^ f) = true) →
      ((c ^^ f) = true → (d ^^ f) = true) →
      (((a && c) ^^ f) = true → ((b && d) ^^ f) = true) ∧
      (((a || c) ^^ f) = true → ((b || d) ^^ f) = true) := by decide
  constructor <;> apply (dom_iff ..).2 <;> intro i <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or]
  · exact (finite _ _ _ _ _ ((dom_iff ..).1 h i) ((dom_iff ..).1 j i)).1
  · exact (finite _ _ _ _ _ ((dom_iff ..).1 h i) ((dom_iff ..).1 j i)).2

private def cov (s : List T) (x : T) := s.any (dom x)
private theorem cmono {s : List T} {x y : T} (h : dom x y) (j : cov s y) : cov s x := by
  obtain ⟨z,hz,hzy⟩ := List.any_eq_true.mp j
  exact List.any_eq_true.mpr ⟨z,hz,dtrans h hzy⟩

-- Each state lists maximal wire columns. Its downward closure contains both
-- constants, excludes the target, and absorbs every free conjunction.
private def basic (s : List T) := !cov s target && cov s 0 && cov s 2047 &&
  s.all fun x => s.all fun y => cov s (x &&& y)

-- A paid disjunction moves to a child covering all old wires and its result.
private def good : ℕ → List T → Prop
  | 0, s => basic s = true
  | n+1, s => basic s = true ∧ ∀ x ∈ s, ∀ y ∈ s,
      ∃ t, good n t ∧ (∀ z ∈ s, cov t z = true) ∧ cov t (x ||| y) = true

private theorem base {n s} (h : good n s) : basic s := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

private theorem build {n s} {cs : List (List T)}
    (hc : ∀ t ∈ cs, good n t)
    (hv : basic s && (cs.all fun t => s.all (cov t)) &&
      (s.all fun x => s.all fun y => cs.any fun t => cov t (x ||| y))) :
    good (n+1) s := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hv
  refine ⟨hv.1.1, ?_⟩
  intro x hx y hy
  obtain ⟨t,ht,hz⟩ := hv.2 x hx y hy
  exact ⟨t,hc t ht,hv.1.2 t ht,hz⟩

-- Assemble the child proofs for each node of the finite certificate.
private theorem ccons {n t} {cs : List (List T)} (ht : good n t)
    (hs : ∀ s ∈ cs, good n s) : ∀ s ∈ t :: cs, good n s := by
  simpa only [List.forall_mem_cons] using And.intro ht hs

private def w0_0 : List T := [31, 47, 55, 59, 61, 62, 127]
set_option maxHeartbeats 10000000 in
private theorem h0_0 : good 0 w0_0 := by
  change basic w0_0 = true
  decide +kernel
private def w0_1 : List T := [31, 47, 55, 59, 61, 62, 191]
set_option maxHeartbeats 10000000 in
private theorem h0_1 : good 0 w0_1 := by
  change basic w0_1 = true
  decide +kernel
private def w0_2 : List T := [31, 47, 55, 59, 61, 62, 319]
set_option maxHeartbeats 10000000 in
private theorem h0_2 : good 0 w0_2 := by
  change basic w0_2 = true
  decide +kernel
private def w0_3 : List T := [31, 47, 55, 59, 61, 62, 575]
set_option maxHeartbeats 10000000 in
private theorem h0_3 : good 0 w0_3 := by
  change basic w0_3 = true
  decide +kernel
private def w0_4 : List T := [31, 47, 55, 59, 61, 62, 1087]
set_option maxHeartbeats 10000000 in
private theorem h0_4 : good 0 w0_4 := by
  change basic w0_4 = true
  decide +kernel
private def w1_0 : List T := [15, 23, 27, 29, 30, 32, 95, 111, 176, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_0 : good 1 w1_0 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_1 : List T := [8, 23, 39, 51, 53, 54, 104, 119, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_1 : good 1 w1_1 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_2 : List T := [7, 27, 29, 30, 40, 48, 127]
set_option maxHeartbeats 10000000 in
private theorem h1_2 : good 1 w1_2 := by
  exact build (cs := [w0_0]) (ccons h0_0 (by simp)) (by decide +kernel)
private def w1_3 : List T := [15, 23, 27, 29, 30, 32, 95, 104, 183, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_3 : good 1 w1_3 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_4 : List T := [15, 27, 29, 30, 40, 95, 111, 184, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_4 : good 1 w1_4 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_5 : List T := [7, 27, 29, 30, 40, 48, 95, 1063, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_5 : good 1 w1_5 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_6 : List T := [11, 23, 29, 30, 36, 48, 111, 119, 125, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_6 : good 1 w1_6 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_7 : List T := [6, 27, 43, 51, 58, 127]
set_option maxHeartbeats 10000000 in
private theorem h1_7 : good 1 w1_7 := by
  exact build (cs := [w0_0]) (ccons h0_0 (by simp)) (by decide +kernel)
private def w1_8 : List T := [15, 27, 29, 30, 40, 95, 175, 187, 189, 190, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_8 : good 1 w1_8 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_9 : List T := [23, 27, 29, 30, 48, 95, 311, 315, 317, 318, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_9 : good 1 w1_9 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_10 : List T := [23, 27, 29, 30, 48, 119, 123, 125, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_10 : good 1 w1_10 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_11 : List T := [13, 14, 23, 27, 35, 48, 127]
set_option maxHeartbeats 10000000 in
private theorem h1_11 : good 1 w1_11 := by
  exact build (cs := [w0_0]) (ccons h0_0 (by simp)) (by decide +kernel)
private def w1_12 : List T := [7, 11, 29, 30, 44, 48, 111, 125, 126, 1047, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_12 : good 1 w1_12 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_13 : List T := [6, 27, 43, 51, 58, 95, 111, 119, 126, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_13 : good 1 w1_13 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_14 : List T := [11, 19, 29, 30, 36, 56, 111, 119, 125, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_14 : good 1 w1_14 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_15 : List T := [7, 11, 19, 29, 30, 36, 40, 48, 1087]
set_option maxHeartbeats 10000000 in
private theorem h1_15 : good 1 w1_15 := by
  exact build (cs := [w0_4]) (ccons h0_4 (by simp)) (by decide +kernel)
private def w1_16 : List T := [7, 27, 29, 30, 40, 48, 95, 295, 315, 317, 318, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_16 : good 1 w1_16 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_17 : List T := [15, 23, 27, 29, 30, 32, 95, 107, 180, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_17 : good 1 w1_17 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_18 : List T := [15, 27, 43, 95, 111, 187, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_18 : good 1 w1_18 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_19 : List T := [23, 29, 30, 52, 119, 125, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_19 : good 1 w1_19 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_20 : List T := [7, 19, 29, 30, 40, 52, 1055, 1071, 1079, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_20 : good 1 w1_20 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_21 : List T := [15, 27, 29, 30, 40, 191]
set_option maxHeartbeats 10000000 in
private theorem h1_21 : good 1 w1_21 := by
  exact build (cs := [w0_1]) (ccons h0_1 (by simp)) (by decide +kernel)
private def w1_22 : List T := [11, 29, 30, 44, 56, 111, 125, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_22 : good 1 w1_22 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_23 : List T := [27, 29, 30, 56, 95, 315, 317, 318, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_23 : good 1 w1_23 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_24 : List T := [27, 29, 30, 56, 123, 125, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_24 : good 1 w1_24 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_25 : List T := [3, 30, 46, 54, 58, 71, 126, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_25 : good 1 w1_25 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_26 : List T := [23, 27, 29, 30, 48, 319]
set_option maxHeartbeats 10000000 in
private theorem h1_26 : good 1 w1_26 := by
  exact build (cs := [w0_2]) (ccons h0_2 (by simp)) (by decide +kernel)
private def w1_27 : List T := [11, 14, 23, 29, 37, 48, 111, 119, 125, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_27 : good 1 w1_27 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_28 : List T := [6, 29, 45, 53, 60, 125, 1055, 1071, 1079, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_28 : good 1 w1_28 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_29 : List T := [7, 13, 21, 27, 30, 34, 40, 48, 95, 1063, 1069, 1077, 1083, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_29 : good 1 w1_29 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_30 : List T := [6, 29, 45, 53, 60, 1087]
set_option maxHeartbeats 10000000 in
private theorem h1_30 : good 1 w1_30 := by
  exact build (cs := [w0_4]) (ccons h0_4 (by simp)) (by decide +kernel)
private def w1_31 : List T := [15, 23, 27, 29, 30, 32, 95, 106, 181, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_31 : good 1 w1_31 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_32 : List T := [7, 13, 27, 30, 42, 48, 95, 1063, 1069, 1083, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_32 : good 1 w1_32 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_33 : List T := [23, 27, 30, 50, 127]
set_option maxHeartbeats 10000000 in
private theorem h1_33 : good 1 w1_33 := by
  exact build (cs := [w0_0]) (ccons h0_0 (by simp)) (by decide +kernel)
private def w1_34 : List T := [7, 21, 27, 30, 40, 50, 95, 1063, 1077, 1083, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_34 : good 1 w1_34 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_35 : List T := [15, 23, 27, 29, 30, 32, 95, 104, 567, 623, 635, 637, 638, 767]
set_option maxHeartbeats 10000000 in
private theorem h1_35 : good 1 w1_35 := by
  exact build (cs := [w0_0, w0_1, w0_3]) (ccons h0_0 (ccons h0_1 (ccons h0_3 (by simp)))) (by decide +kernel)
private def w1_36 : List T := [5, 30, 46, 54, 60, 1055, 1071, 1079, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_36 : good 1 w1_36 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_37 : List T := [11, 13, 23, 30, 38, 48, 111, 119, 126, 1051, 1053, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_37 : good 1 w1_37 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_38 : List T := [5, 30, 46, 54, 60, 1087]
set_option maxHeartbeats 10000000 in
private theorem h1_38 : good 1 w1_38 := by
  exact build (cs := [w0_4]) (ccons h0_4 (by simp)) (by decide +kernel)
private def w1_39 : List T := [15, 23, 27, 29, 30, 32, 95, 105, 182, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_39 : good 1 w1_39 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_40 : List T := [27, 29, 57, 123, 125, 287, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_40 : good 1 w1_40 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_41 : List T := [15, 23, 27, 30, 34, 95, 106, 183, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_41 : good 1 w1_41 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_42 : List T := [13, 23, 27, 30, 34, 48, 109, 119, 123, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_42 : good 1 w1_42 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_43 : List T := [11, 23, 25, 30, 36, 50, 111, 119, 125, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_43 : good 1 w1_43 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_44 : List T := [15, 19, 29, 30, 36, 40, 175, 183, 189, 190, 1051, 1183, 1211, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_44 : good 1 w1_44 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_45 : List T := [27, 29, 57, 287, 303, 311, 315, 317, 318, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_45 : good 1 w1_45 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_46 : List T := [23, 27, 30, 50, 119, 123, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_46 : good 1 w1_46 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_47 : List T := [15, 29, 30, 44, 175, 189, 190, 1055, 1207, 1211, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_47 : good 1 w1_47 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_48 : List T := [27, 29, 57, 125, 287, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_48 : good 1 w1_48 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_49 : List T := [15, 23, 29, 37, 111, 181, 247, 253, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_49 : good 1 w1_49 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_50 : List T := [11, 13, 23, 30, 38, 48, 107, 109, 119, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_50 : good 1 w1_50 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_51 : List T := [9, 30, 46, 58, 60, 77, 126, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_51 : good 1 w1_51 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_52 : List T := [23, 27, 30, 50, 95, 123, 182, 255]
set_option maxHeartbeats 10000000 in
private theorem h1_52 : good 1 w1_52 := by
  exact build (cs := [w0_0, w0_1]) (ccons h0_0 (ccons h0_1 (by simp))) (by decide +kernel)
private def w1_53 : List T := [27, 30, 58, 95, 190, 1083, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_53 : good 1 w1_53 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_54 : List T := [27, 30, 58, 95, 318, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_54 : good 1 w1_54 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_55 : List T := [39, 43, 45, 46, 48, 111, 1079, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_55 : good 1 w1_55 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_56 : List T := [14, 23, 27, 29, 33, 48, 319]
set_option maxHeartbeats 10000000 in
private theorem h1_56 : good 1 w1_56 := by
  exact build (cs := [w0_2]) (ccons h0_2 (by simp)) (by decide +kernel)
private def w1_57 : List T := [39, 46, 54, 1055, 1071, 1079, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_57 : good 1 w1_57 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_58 : List T := [15, 29, 45, 111, 189, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_58 : good 1 w1_58 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_59 : List T := [15, 23, 29, 30, 36, 109, 182, 239, 247, 253, 254, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_59 : good 1 w1_59 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_60 : List T := [15, 27, 29, 30, 40, 95, 559, 571, 573, 574, 631, 895]
set_option maxHeartbeats 10000000 in
private theorem h1_60 : good 1 w1_60 := by
  exact build (cs := [w0_0, w0_2, w0_3]) (ccons h0_0 (ccons h0_2 (ccons h0_3 (by simp)))) (by decide +kernel)
private def w1_61 : List T := [7, 30, 46, 54, 1087]
set_option maxHeartbeats 10000000 in
private theorem h1_61 : good 1 w1_61 := by
  exact build (cs := [w0_4]) (ccons h0_4 (by simp)) (by decide +kernel)
private def w1_62 : List T := [15, 23, 27, 29, 30, 32, 104, 183, 239, 251, 253, 254, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_62 : good 1 w1_62 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_63 : List T := [23, 30, 54, 119, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_63 : good 1 w1_63 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_64 : List T := [1, 30, 46, 54, 58, 60, 101, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_64 : good 1 w1_64 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_65 : List T := [39, 43, 45, 46, 48, 1087]
set_option maxHeartbeats 10000000 in
private theorem h1_65 : good 1 w1_65 := by
  exact build (cs := [w0_4]) (ccons h0_4 (by simp)) (by decide +kernel)
private def w1_66 : List T := [23, 27, 30, 50, 95, 123, 310, 383]
set_option maxHeartbeats 10000000 in
private theorem h1_66 : good 1 w1_66 := by
  exact build (cs := [w0_0, w0_2]) (ccons h0_0 (ccons h0_2 (by simp))) (by decide +kernel)
private def w1_67 : List T := [15, 23, 27, 29, 30, 32, 95, 105, 566, 639]
set_option maxHeartbeats 10000000 in
private theorem h1_67 : good 1 w1_67 := by
  exact build (cs := [w0_0, w0_3]) (ccons h0_0 (ccons h0_3 (by simp))) (by decide +kernel)
private def w1_68 : List T := [15, 27, 29, 41, 191]
set_option maxHeartbeats 10000000 in
private theorem h1_68 : good 1 w1_68 := by
  exact build (cs := [w0_1]) (ccons h0_1 (by simp)) (by decide +kernel)
private def w1_69 : List T := [6, 27, 43, 51, 58, 159, 175, 183, 190, 1083, 1213, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_69 : good 1 w1_69 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_70 : List T := [5, 27, 43, 51, 57, 287, 303, 311, 317, 1083, 1342, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_70 : good 1 w1_70 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_71 : List T := [15, 27, 30, 42, 111, 186, 251, 254, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_71 : good 1 w1_71 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_72 : List T := [23, 29, 53, 119, 125, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_72 : good 1 w1_72 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_73 : List T := [13, 23, 30, 38, 52, 109, 119, 126, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_73 : good 1 w1_73 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_74 : List T := [23, 27, 29, 49, 319]
set_option maxHeartbeats 10000000 in
private theorem h1_74 : good 1 w1_74 := by
  exact build (cs := [w0_2]) (ccons h0_2 (by simp)) (by decide +kernel)
private def w1_75 : List T := [9, 30, 46, 58, 60, 109, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_75 : good 1 w1_75 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_76 : List T := [23, 27, 29, 49, 95, 315, 565, 823, 829, 895]
set_option maxHeartbeats 10000000 in
private theorem h1_76 : good 1 w1_76 := by
  exact build (cs := [w0_0, w0_2, w0_3]) (ccons h0_0 (ccons h0_2 (ccons h0_3 (by simp)))) (by decide +kernel)
private def w1_77 : List T := [39, 43, 45, 49, 111, 117, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_77 : good 1 w1_77 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w1_78 : List T := [15, 27, 29, 30, 40, 575]
set_option maxHeartbeats 10000000 in
private theorem h1_78 : good 1 w1_78 := by
  exact build (cs := [w0_3]) (ccons h0_3 (by simp)) (by decide +kernel)
private def w1_79 : List T := [39, 43, 45, 49, 117, 303, 1083, 1143, 1149, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_79 : good 1 w1_79 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_80 : List T := [39, 40, 51, 53, 54, 311, 1071, 1083, 1085, 1086, 1311, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_80 : good 1 w1_80 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_81 : List T := [23, 27, 51, 127]
set_option maxHeartbeats 10000000 in
private theorem h1_81 : good 1 w1_81 := by
  exact build (cs := [w0_0]) (ccons h0_0 (by simp)) (by decide +kernel)
private def w1_82 : List T := [15, 30, 46, 111, 190, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h1_82 : good 1 w1_82 := by
  exact build (cs := [w0_0, w0_1, w0_4]) (ccons h0_0 (ccons h0_1 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_83 : List T := [39, 43, 46, 50, 111, 310, 1083, 1335, 1342, 1407]
set_option maxHeartbeats 10000000 in
private theorem h1_83 : good 1 w1_83 := by
  exact build (cs := [w0_0, w0_2, w0_4]) (ccons h0_0 (ccons h0_2 (ccons h0_4 (by simp)))) (by decide +kernel)
private def w1_84 : List T := [39, 40, 51, 53, 54, 119, 1071, 1083, 1085, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h1_84 : good 1 w1_84 := by
  exact build (cs := [w0_0, w0_4]) (ccons h0_0 (ccons h0_4 (by simp))) (by decide +kernel)
private def w2_0 : List T := [7, 8, 19, 21, 22, 32, 87, 104, 176, 1051, 1053, 1054, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_0 : good 2 w2_0 := by
  exact build (cs := [w1_0, w1_1, w1_2, w1_3, w1_4, w1_5]) (ccons h1_0 (ccons h1_1 (ccons h1_2 (ccons h1_3 (ccons h1_4 (ccons h1_5 (by simp))))))) (by decide +kernel)
private def w2_1 : List T := [4, 11, 19, 26, 32, 77, 85, 92, 176, 262, 343, 350, 360, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_1 : good 2 w2_1 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_6, w1_7, w1_8, w1_9, w1_10]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_6 (ccons h1_7 (ccons h1_8 (ccons h1_9 (ccons h1_10 (by simp)))))))))) (by decide +kernel)
private def w2_2 : List T := [3, 12, 16, 32, 69, 84, 176, 262, 327, 360, 1051, 1117, 1294, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_2 : good 2 w2_2 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_8, w1_9, w1_10, w1_11, w1_12]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_12 (by simp)))))))))) (by decide +kernel)
private def w2_3 : List T := [6, 8, 19, 35, 48, 104, 119, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_3 : good 2 w2_3 := by
  exact build (cs := [w1_1, w1_7, w1_11, w1_13]) (ccons h1_1 (ccons h1_7 (ccons h1_11 (ccons h1_13 (by simp))))) (by decide +kernel)
private def w2_4 : List T := [3, 8, 21, 22, 36, 48, 71, 104, 1051, 1053, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_4 : good 2 w2_4 := by
  exact build (cs := [w1_1, w1_6, w1_12, w1_14, w1_15]) (ccons h1_1 (ccons h1_6 (ccons h1_12 (ccons h1_14 (ccons h1_15 (by simp)))))) (by decide +kernel)
private def w2_5 : List T := [4, 11, 26, 40, 77, 92, 176, 262, 327, 350, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_5 : good 2 w2_5 := by
  exact build (cs := [w1_2, w1_5, w1_7, w1_8, w1_12, w1_15, w1_16]) (ccons h1_2 (ccons h1_5 (ccons h1_7 (ccons h1_8 (ccons h1_12 (ccons h1_15 (ccons h1_16 (by simp)))))))) (by decide +kernel)
private def w2_6 : List T := [4, 11, 19, 26, 32, 77, 85, 92, 176, 262, 343, 350, 363, 493, 503, 510, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_6 : good 2 w2_6 := by
  exact build (cs := [w1_0, w1_2, w1_6, w1_7, w1_9, w1_10, w1_13, w1_17, w1_18]) (ccons h1_0 (ccons h1_2 (ccons h1_6 (ccons h1_7 (ccons h1_9 (ccons h1_10 (ccons h1_13 (ccons h1_17 (ccons h1_18 (by simp)))))))))) (by decide +kernel)
private def w2_7 : List T := [4, 19, 26, 32, 85, 92, 176, 262, 343, 350, 359, 366, 503, 510, 1051, 1117, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_7 : good 2 w2_7 := by
  exact build (cs := [w1_0, w1_2, w1_4, w1_6, w1_7, w1_9, w1_10, w1_13, w1_19]) (ccons h1_0 (ccons h1_2 (ccons h1_4 (ccons h1_6 (ccons h1_7 (ccons h1_9 (ccons h1_10 (ccons h1_13 (ccons h1_19 (by simp)))))))))) (by decide +kernel)
private def w2_8 : List T := [4, 19, 26, 48, 85, 92, 262, 375, 382, 1051, 1117, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_8 : good 2 w2_8 := by
  exact build (cs := [w1_2, w1_7, w1_9, w1_10, w1_13, w1_19]) (ccons h1_2 (ccons h1_7 (ccons h1_9 (ccons h1_10 (ccons h1_13 (ccons h1_19 (by simp))))))) (by decide +kernel)
private def w2_9 : List T := [6, 8, 19, 32, 87, 104, 179, 247, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_9 : good 2 w2_9 := by
  exact build (cs := [w1_1, w1_3, w1_7, w1_8, w1_13]) (ccons h1_1 (ccons h1_3 (ccons h1_7 (ccons h1_8 (ccons h1_13 (by simp)))))) (by decide +kernel)
private def w2_10 : List T := [3, 8, 21, 22, 32, 104, 180, 1039, 1051, 1053, 1054, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_10 : good 2 w2_10 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_17, w1_19, w1_20, w1_21]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_17 (ccons h1_19 (ccons h1_20 (ccons h1_21 (by simp)))))))) (by decide +kernel)
private def w2_11 : List T := [4, 11, 26, 40, 77, 92, 184, 262, 350, 491, 493, 510, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_11 : good 2 w2_11 := by
  exact build (cs := [w1_4, w1_7, w1_8, w1_13, w1_22, w1_23, w1_24]) (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_22 (ccons h1_23 (ccons h1_24 (by simp)))))))) (by decide +kernel)
private def w2_12 : List T := [4, 11, 16, 32, 69, 84, 176, 270, 327, 333, 360, 1051, 1109, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_12 : good 2 w2_12 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_6, w1_8, w1_9, w1_10, w1_11, w1_18]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_6 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_18 (by simp))))))))))) (by decide +kernel)
private def w2_13 : List T := [3, 8, 22, 48, 71, 310, 360, 1051, 1111, 1117, 1118, 1331, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_13 : good 2 w2_13 := by
  exact build (cs := [w1_1, w1_9, w1_16, w1_23, w1_25, w1_26]) (ccons h1_1 (ccons h1_9 (ccons h1_16 (ccons h1_23 (ccons h1_25 (ccons h1_26 (by simp))))))) (by decide +kernel)
private def w2_14 : List T := [8, 19, 21, 22, 48, 100, 104, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_14 : good 2 w2_14 := by
  exact build (cs := [w1_1, w1_10, w1_15, w1_24]) (ccons h1_1 (ccons h1_10 (ccons h1_15 (ccons h1_24 (by simp))))) (by decide +kernel)
private def w2_15 : List T := [3, 6, 26, 40, 48, 71, 94, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_15 : good 2 w2_15 := by
  exact build (cs := [w1_5, w1_13, w1_15, w1_20, w1_25]) (ccons h1_5 (ccons h1_13 (ccons h1_15 (ccons h1_20 (ccons h1_25 (by simp)))))) (by decide +kernel)
private def w2_16 : List T := [5, 11, 16, 32, 77, 84, 176, 263, 334, 360, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_16 : good 2 w2_16 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_8, w1_9, w1_10, w1_18, w1_27]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_18 (ccons h1_27 (by simp)))))))))) (by decide +kernel)
private def w2_17 : List T := [2, 13, 21, 24, 32, 92, 176, 262, 360, 1051, 1117, 1287, 1294, 1302, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_17 : good 2 w2_17 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_8, w1_9, w1_10, w1_11, w1_28]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_28 (by simp)))))))))) (by decide +kernel)
private def w2_18 : List T := [5, 6, 8, 19, 34, 87, 104, 176, 1038, 1051, 1119, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_18 : good 2 w2_18 := by
  exact build (cs := [w1_1, w1_11, w1_18, w1_29]) (ccons h1_1 (ccons h1_11 (ccons h1_18 (ccons h1_29 (by simp))))) (by decide +kernel)
private def w2_19 : List T := [6, 8, 21, 37, 48, 104, 117, 1047, 1051, 1053, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_19 : good 2 w2_19 := by
  exact build (cs := [w1_1, w1_27, w1_28, w1_30]) (ccons h1_1 (ccons h1_27 (ccons h1_28 (ccons h1_30 (by simp))))) (by decide +kernel)
private def w2_20 : List T := [2, 13, 24, 40, 92, 176, 262, 1051, 1117, 1294, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_20 : good 2 w2_20 := by
  exact build (cs := [w1_2, w1_5, w1_8, w1_14, w1_15, w1_16, w1_18, w1_28]) (ccons h1_2 (ccons h1_5 (ccons h1_8 (ccons h1_14 (ccons h1_15 (ccons h1_16 (ccons h1_18 (ccons h1_28 (by simp))))))))) (by decide +kernel)
private def w2_21 : List T := [5, 11, 16, 32, 77, 84, 176, 263, 334, 362, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_21 : good 2 w2_21 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_18, w1_27, w1_31, w1_32]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_18 (ccons h1_27 (ccons h1_31 (ccons h1_32 (by simp))))))))) (by decide +kernel)
private def w2_22 : List T := [2, 5, 9, 12, 17, 24, 32, 77, 85, 92, 176, 262, 365, 501, 508, 1051, 1117, 1287, 1294, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_22 : good 2 w2_22 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_11, w1_18, w1_27, w1_28, w1_30]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_18 (ccons h1_27 (ccons h1_28 (ccons h1_30 (by simp)))))))))) (by decide +kernel)
private def w2_23 : List T := [2, 21, 28, 48, 262, 373, 380, 1051, 1117, 1310, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_23 : good 2 w2_23 := by
  exact build (cs := [w1_2, w1_9, w1_10, w1_14, w1_28, w1_30, w1_33]) (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_14 (ccons h1_28 (ccons h1_30 (ccons h1_33 (by simp)))))))) (by decide +kernel)
private def w2_24 : List T := [7, 8, 19, 32, 87, 104, 178, 1038, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_24 : good 2 w2_24 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_18, w1_33, w1_34]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_18 (ccons h1_33 (ccons h1_34 (by simp))))))) (by decide +kernel)
private def w2_25 : List T := [2, 8, 21, 32, 104, 518, 693, 1051, 1053, 1551, 1566, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_25 : good 2 w2_25 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_28, w1_30, w1_31, w1_35]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_28 (ccons h1_30 (ccons h1_31 (ccons h1_35 (by simp))))))))) (by decide +kernel)
private def w2_26 : List T := [2, 13, 24, 40, 92, 184, 262, 493, 508, 1051, 1117, 1294, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_26 : good 2 w2_26 := by
  exact build (cs := [w1_4, w1_8, w1_14, w1_18, w1_23, w1_24, w1_28, w1_30]) (ccons h1_4 (ccons h1_8 (ccons h1_14 (ccons h1_18 (ccons h1_23 (ccons h1_24 (ccons h1_28 (ccons h1_30 (by simp))))))))) (by decide +kernel)
private def w2_27 : List T := [5, 11, 16, 32, 84, 176, 263, 269, 270, 360, 1051, 1109, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_27 : good 2 w2_27 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_8, w1_9, w1_10, w1_18, w1_27]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_18 (ccons h1_27 (by simp)))))))))) (by decide +kernel)
private def w2_28 : List T := [5, 8, 22, 48, 310, 360, 1051, 1053, 1054, 1111, 1331, 1333, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_28 : good 2 w2_28 := by
  exact build (cs := [w1_1, w1_9, w1_16, w1_23, w1_26, w1_36]) (ccons h1_1 (ccons h1_9 (ccons h1_16 (ccons h1_23 (ccons h1_26 (ccons h1_36 (by simp))))))) (by decide +kernel)
private def w2_29 : List T := [5, 6, 10, 12, 18, 24, 32, 78, 86, 92, 360, 688, 878, 1014, 1020, 1031, 1037, 1051, 1119, 1903, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_29 : good 2 w2_29 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_18, w1_27, w1_35, w1_36]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_18 (ccons h1_27 (ccons h1_35 (ccons h1_36 (by simp))))))))) (by decide +kernel)
private def w2_30 : List T := [5, 6, 28, 40, 48, 1063, 1083, 1086, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_30 : good 2 w2_30 := by
  exact build (cs := [w1_5, w1_15, w1_30, w1_32, w1_34, w1_36]) (ccons h1_5 (ccons h1_15 (ccons h1_30 (ccons h1_32 (ccons h1_34 (ccons h1_36 (by simp))))))) (by decide +kernel)
private def w2_31 : List T := [6, 11, 19, 26, 32, 77, 87, 94, 104, 176, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_31 : good 2 w2_31 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_7, w1_8, w1_10, w1_37]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_7 (ccons h1_8 (ccons h1_10 (ccons h1_37 (by simp))))))))) (by decide +kernel)
private def w2_32 : List T := [3, 14, 22, 26, 32, 71, 94, 104, 176, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_32 : good 2 w2_32 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_8, w1_10, w1_11, w1_25]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_8 (ccons h1_10 (ccons h1_11 (ccons h1_25 (by simp))))))))) (by decide +kernel)
private def w2_33 : List T := [1, 8, 22, 38, 48, 69, 104, 118, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_33 : good 2 w2_33 := by
  exact build (cs := [w1_1, w1_25, w1_37, w1_38]) (ccons h1_1 (ccons h1_25 (ccons h1_37 (ccons h1_38 (by simp))))) (by decide +kernel)
private def w2_34 : List T := [6, 11, 19, 26, 32, 77, 87, 94, 105, 176, 235, 237, 247, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_34 : good 2 w2_34 := by
  exact build (cs := [w1_0, w1_2, w1_7, w1_10, w1_13, w1_18, w1_37, w1_39]) (ccons h1_0 (ccons h1_2 (ccons h1_7 (ccons h1_10 (ccons h1_13 (ccons h1_18 (ccons h1_37 (ccons h1_39 (by simp))))))))) (by decide +kernel)
private def w2_35 : List T := [3, 6, 26, 32, 71, 94, 110, 176, 254, 1051, 1119, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_35 : good 2 w2_35 := by
  exact build (cs := [w1_0, w1_2, w1_7, w1_10, w1_13, w1_25]) (ccons h1_0 (ccons h1_2 (ccons h1_7 (ccons h1_10 (ccons h1_13 (ccons h1_25 (by simp))))))) (by decide +kernel)
private def w2_36 : List T := [3, 6, 26, 48, 71, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_36 : good 2 w2_36 := by
  exact build (cs := [w1_2, w1_7, w1_10, w1_13, w1_25]) (ccons h1_2 (ccons h1_7 (ccons h1_10 (ccons h1_13 (ccons h1_25 (by simp)))))) (by decide +kernel)
private def w2_37 : List T := [1, 8, 22, 32, 104, 182, 197, 1038, 1051, 1118, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_37 : good 2 w2_37 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_25, w1_39]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_25 (ccons h1_39 (by simp))))))) (by decide +kernel)
private def w2_38 : List T := [3, 6, 26, 40, 69, 94, 184, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_38 : good 2 w2_38 := by
  exact build (cs := [w1_4, w1_7, w1_8, w1_13, w1_24, w1_25]) (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_24 (ccons h1_25 (by simp))))))) (by decide +kernel)
private def w2_39 : List T := [4, 19, 25, 26, 32, 93, 176, 262, 343, 350, 360, 1051, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_39 : good 2 w2_39 := by
  exact build (cs := [w1_0, w1_3, w1_5, w1_6, w1_7, w1_9, w1_10, w1_26, w1_40]) (ccons h1_0 (ccons h1_3 (ccons h1_5 (ccons h1_6 (ccons h1_7 (ccons h1_9 (ccons h1_10 (ccons h1_26 (ccons h1_40 (by simp)))))))))) (by decide +kernel)
private def w2_40 : List T := [6, 11, 19, 26, 34, 77, 87, 94, 106, 176, 235, 237, 247, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_40 : good 2 w2_40 := by
  exact build (cs := [w1_7, w1_11, w1_13, w1_18, w1_37, w1_41, w1_42]) (ccons h1_7 (ccons h1_11 (ccons h1_13 (ccons h1_18 (ccons h1_37 (ccons h1_41 (ccons h1_42 (by simp)))))))) (by decide +kernel)
private def w2_41 : List T := [6, 9, 21, 28, 36, 77, 104, 176, 1031, 1051, 1054, 1103, 1117, 1175, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_41 : good 2 w2_41 := by
  exact build (cs := [w1_6, w1_15, w1_19, w1_28, w1_37, w1_43, w1_44]) (ccons h1_6 (ccons h1_15 (ccons h1_19 (ccons h1_28 (ccons h1_37 (ccons h1_43 (ccons h1_44 (by simp)))))))) (by decide +kernel)
private def w2_42 : List T := [2, 4, 25, 41, 49, 56, 93, 262, 365, 373, 380, 1051, 1145, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_42 : good 2 w2_42 := by
  exact build (cs := [w1_7, w1_13, w1_28, w1_40, w1_45]) (ccons h1_7 (ccons h1_13 (ccons h1_28 (ccons h1_40 (ccons h1_45 (by simp)))))) (by decide +kernel)
private def w2_43 : List T := [4, 11, 19, 26, 32, 85, 92, 104, 518, 599, 606, 690, 747, 759, 766, 1051, 1117, 1631, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_43 : good 2 w2_43 := by
  exact build (cs := [w1_3, w1_7, w1_8, w1_13, w1_35, w1_43, w1_46]) (ccons h1_3 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_35 (ccons h1_43 (ccons h1_46 (by simp)))))))) (by decide +kernel)
private def w2_44 : List T := [2, 13, 21, 28, 32, 104, 518, 692, 1051, 1117, 1551, 1566, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_44 : good 2 w2_44 := by
  exact build (cs := [w1_3, w1_8, w1_17, w1_19, w1_20, w1_21, w1_28, w1_35, w1_41]) (ccons h1_3 (ccons h1_8 (ccons h1_17 (ccons h1_19 (ccons h1_20 (ccons h1_21 (ccons h1_28 (ccons h1_35 (ccons h1_41 (by simp)))))))))) (by decide +kernel)
private def w2_45 : List T := [11, 12, 25, 40, 93, 185, 270, 335, 509, 1051, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_45 : good 2 w2_45 := by
  exact build (cs := [w1_8, w1_18, w1_21, w1_40, w1_45, w1_47, w1_48]) (ccons h1_8 (ccons h1_18 (ccons h1_21 (ccons h1_40 (ccons h1_45 (ccons h1_47 (ccons h1_48 (by simp)))))))) (by decide +kernel)
private def w2_46 : List T := [5, 11, 12, 25, 32, 85, 92, 176, 271, 349, 360, 509, 1051, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_46 : good 2 w2_46 := by
  exact build (cs := [w1_0, w1_3, w1_8, w1_18, w1_21, w1_26, w1_47, w1_48, w1_49]) (ccons h1_0 (ccons h1_3 (ccons h1_8 (ccons h1_18 (ccons h1_21 (ccons h1_26 (ccons h1_47 (ccons h1_48 (ccons h1_49 (by simp)))))))))) (by decide +kernel)
private def w2_47 : List T := [4, 18, 25, 32, 77, 176, 278, 349, 360, 1051, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_47 : good 2 w2_47 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_6, w1_8, w1_9, w1_10, w1_26, w1_33, w1_40]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_6 (ccons h1_8 (ccons h1_9 (ccons h1_10 (ccons h1_26 (ccons h1_33 (ccons h1_40 (by simp)))))))))))) (by decide +kernel)
private def w2_48 : List T := [9, 26, 28, 32, 77, 286, 360, 560, 806, 894, 1051, 1117, 1375, 1903, 1911, 1915, 1917, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_48 : good 2 w2_48 := by
  exact build (cs := [w1_9, w1_26, w1_35, w1_37, w1_45, w1_50, w1_51]) (ccons h1_9 (ccons h1_26 (ccons h1_35 (ccons h1_37 (ccons h1_45 (ccons h1_50 (ccons h1_51 (by simp)))))))) (by decide +kernel)
private def w2_49 : List T := [12, 25, 26, 32, 176, 205, 286, 360, 438, 477, 510, 1051, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_49 : good 2 w2_49 := by
  exact build (cs := [w1_3, w1_8, w1_9, w1_21, w1_44, w1_45, w1_47, w1_52, w1_53]) (ccons h1_3 (ccons h1_8 (ccons h1_9 (ccons h1_21 (ccons h1_44 (ccons h1_45 (ccons h1_47 (ccons h1_52 (ccons h1_53 (by simp)))))))))) (by decide +kernel)
private def w2_50 : List T := [6, 13, 21, 28, 32, 100, 104, 176, 1055, 1132, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_50 : good 2 w2_50 := by
  exact build (cs := [w1_10, w1_15, w1_28, w1_47, w1_50]) (ccons h1_10 (ccons h1_15 (ccons h1_28 (ccons h1_47 (ccons h1_50 (by simp)))))) (by decide +kernel)
private def w2_51 : List T := [2, 4, 9, 24, 40, 48, 77, 92, 262, 1083, 1117, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_51 : good 2 w2_51 := by
  exact build (cs := [w1_5, w1_13, w1_15, w1_20, w1_30, w1_48, w1_51, w1_54]) (ccons h1_5 (ccons h1_13 (ccons h1_15 (ccons h1_20 (ccons h1_30 (ccons h1_48 (ccons h1_51 (ccons h1_54 (by simp))))))))) (by decide +kernel)
private def w2_52 : List T := [4, 10, 19, 25, 33, 93, 105, 176, 241, 248, 262, 343, 359, 365, 366, 503, 508, 1051, 1273, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_52 : good 2 w2_52 := by
  exact build (cs := [w1_7, w1_11, w1_13, w1_27, w1_45, w1_49]) (ccons h1_7 (ccons h1_11 (ccons h1_13 (ccons h1_27 (ccons h1_45 (ccons h1_49 (by simp))))))) (by decide +kernel)
private def w2_53 : List T := [1, 14, 22, 36, 69, 104, 176, 1051, 1054, 1103, 1117, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_53 : good 2 w2_53 := by
  exact build (cs := [w1_6, w1_15, w1_19, w1_25, w1_27, w1_44]) (ccons h1_6 (ccons h1_15 (ccons h1_19 (ccons h1_25 (ccons h1_27 (ccons h1_44 (by simp))))))) (by decide +kernel)
private def w2_54 : List T := [1, 6, 26, 42, 69, 94, 110, 178, 246, 252, 1051, 1067, 1119, 1135, 1203, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_54 : good 2 w2_54 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_25, w1_36]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_25 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_55 : List T := [6, 11, 17, 26, 32, 79, 85, 94, 104, 176, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_55 : good 2 w2_55 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_5, w1_7, w1_8, w1_37, w1_47]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_5 (ccons h1_7 (ccons h1_8 (ccons h1_37 (ccons h1_47 (by simp))))))))) (by decide +kernel)
private def w2_56 : List T := [1, 14, 22, 24, 32, 69, 104, 180, 1051, 1054, 1103, 1117, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_56 : good 2 w2_56 := by
  exact build (cs := [w1_3, w1_8, w1_17, w1_19, w1_20, w1_21, w1_25, w1_49]) (ccons h1_3 (ccons h1_8 (ccons h1_17 (ccons h1_19 (ccons h1_20 (ccons h1_21 (ccons h1_25 (ccons h1_49 (by simp))))))))) (by decide +kernel)
private def w2_57 : List T := [3, 6, 26, 40, 71, 94, 186, 254, 1051, 1119, 1195, 1203, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_57 : good 2 w2_57 := by
  exact build (cs := [w1_7, w1_8, w1_13, w1_25, w1_47]) (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_25 (ccons h1_47 (by simp)))))) (by decide +kernel)
private def w2_58 : List T := [5, 14, 22, 28, 32, 100, 104, 176, 1055, 1132, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_58 : good 2 w2_58 := by
  exact build (cs := [w1_10, w1_15, w1_36, w1_47, w1_49]) (ccons h1_10 (ccons h1_15 (ccons h1_36 (ccons h1_47 (ccons h1_49 (by simp)))))) (by decide +kernel)
private def w2_59 : List T := [2, 5, 12, 25, 33, 93, 105, 176, 241, 248, 262, 365, 501, 508, 1051, 1273, 1287, 1294, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_59 : good 2 w2_59 := by
  exact build (cs := [w1_11, w1_18, w1_27, w1_28, w1_30, w1_45]) (ccons h1_11 (ccons h1_18 (ccons h1_27 (ccons h1_28 (ccons h1_30 (ccons h1_45 (by simp))))))) (by decide +kernel)
private def w2_60 : List T := [1, 6, 12, 26, 34, 69, 94, 110, 176, 246, 252, 1051, 1059, 1119, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_60 : good 2 w2_60 := by
  exact build (cs := [w1_11, w1_18, w1_25, w1_36]) (ccons h1_11 (ccons h1_18 (ccons h1_25 (ccons h1_36 (by simp))))) (by decide +kernel)
private def w2_61 : List T := [1, 6, 28, 44, 48, 69, 124, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_61 : good 2 w2_61 := by
  exact build (cs := [w1_12, w1_25, w1_28, w1_30]) (ccons h1_12 (ccons h1_25 (ccons h1_28 (ccons h1_30 (by simp))))) (by decide +kernel)
private def w2_62 : List T := [6, 13, 21, 24, 32, 92, 104, 176, 237, 245, 252, 1031, 1038, 1046, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_62 : good 2 w2_62 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_8, w1_10, w1_11, w1_12, w1_30, w1_37]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_8 (ccons h1_10 (ccons h1_11 (ccons h1_12 (ccons h1_30 (ccons h1_37 (by simp)))))))))) (by decide +kernel)
private def w2_63 : List T := [1, 14, 26, 32, 69, 94, 104, 178, 238, 246, 252, 1051, 1119, 1187, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_63 : good 2 w2_63 := by
  exact build (cs := [w1_3, w1_8, w1_18, w1_25, w1_36]) (ccons h1_3 (ccons h1_8 (ccons h1_18 (ccons h1_25 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_64 : List T := [5, 6, 28, 40, 188, 1039, 1051, 1053, 1054, 1199, 1203, 1205, 1214, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_64 : good 2 w2_64 := by
  exact build (cs := [w1_8, w1_21, w1_28, w1_30, w1_36]) (ccons h1_8 (ccons h1_21 (ccons h1_28 (ccons h1_30 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_65 : List T := [4, 19, 25, 26, 48, 93, 262, 343, 350, 381, 1051, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_65 : good 2 w2_65 := by
  exact build (cs := [w1_2, w1_7, w1_9, w1_10, w1_19, w1_26, w1_40, w1_48]) (ccons h1_2 (ccons h1_7 (ccons h1_9 (ccons h1_10 (ccons h1_19 (ccons h1_26 (ccons h1_40 (ccons h1_48 (by simp))))))))) (by decide +kernel)
private def w2_66 : List T := [8, 19, 21, 32, 176, 279, 357, 360, 501, 1051, 1117, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_66 : good 2 w2_66 := by
  exact build (cs := [w1_0, w1_1, w1_9, w1_26, w1_40, w1_48]) (ccons h1_0 (ccons h1_1 (ccons h1_9 (ccons h1_26 (ccons h1_40 (ccons h1_48 (by simp))))))) (by decide +kernel)
private def w2_67 : List T := [8, 19, 22, 48, 87, 310, 360, 1051, 1117, 1118, 1331, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_67 : good 2 w2_67 := by
  exact build (cs := [w1_1, w1_9, w1_16, w1_23, w1_26, w1_54]) (ccons h1_1 (ccons h1_9 (ccons h1_16 (ccons h1_23 (ccons h1_26 (ccons h1_54 (by simp))))))) (by decide +kernel)
private def w2_68 : List T := [2, 4, 25, 40, 48, 93, 262, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_68 : good 2 w2_68 := by
  exact build (cs := [w1_5, w1_13, w1_15, w1_20, w1_30, w1_48, w1_54]) (ccons h1_5 (ccons h1_13 (ccons h1_15 (ccons h1_20 (ccons h1_30 (ccons h1_48 (ccons h1_54 (by simp)))))))) (by decide +kernel)
private def w2_69 : List T := [3, 6, 8, 50, 71, 104, 118, 1051, 1059, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_69 : good 2 w2_69 := by
  exact build (cs := [w1_1, w1_7, w1_13, w1_25]) (ccons h1_1 (ccons h1_7 (ccons h1_13 (ccons h1_25 (by simp))))) (by decide +kernel)
private def w2_70 : List T := [6, 8, 21, 52, 104, 117, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_70 : good 2 w2_70 := by
  exact build (cs := [w1_1, w1_19, w1_28, w1_30]) (ccons h1_1 (ccons h1_19 (ccons h1_28 (ccons h1_30 (by simp))))) (by decide +kernel)
private def w2_71 : List T := [2, 12, 21, 25, 32, 93, 176, 262, 365, 501, 508, 1051, 1287, 1294, 1302, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_71 : good 2 w2_71 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_11, w1_19, w1_28, w1_30, w1_33, w1_40]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_19 (ccons h1_28 (ccons h1_30 (ccons h1_33 (ccons h1_40 (by simp))))))))))) (by decide +kernel)
private def w2_72 : List T := [1, 22, 26, 32, 69, 94, 176, 362, 510, 1051, 1119, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_72 : good 2 w2_72 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_11, w1_19, w1_25, w1_31]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_19 (ccons h1_25 (ccons h1_31 (by simp))))))))) (by decide +kernel)
private def w2_73 : List T := [6, 8, 19, 35, 87, 103, 104, 178, 247, 1051, 1119, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_73 : good 2 w2_73 := by
  exact build (cs := [w1_1, w1_7, w1_13, w1_18]) (ccons h1_1 (ccons h1_7 (ccons h1_13 (ccons h1_18 (by simp))))) (by decide +kernel)
private def w2_74 : List T := [6, 8, 21, 37, 104, 180, 245, 1055, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_74 : good 2 w2_74 := by
  exact build (cs := [w1_1, w1_28, w1_30, w1_49]) (ccons h1_1 (ccons h1_28 (ccons h1_30 (ccons h1_49 (by simp))))) (by decide +kernel)
private def w2_75 : List T := [5, 11, 25, 33, 85, 105, 176, 249, 263, 269, 270, 335, 349, 365, 509, 1051, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_75 : good 2 w2_75 := by
  exact build (cs := [w1_11, w1_18, w1_27, w1_40, w1_45, w1_48, w1_49]) (ccons h1_11 (ccons h1_18 (ccons h1_27 (ccons h1_40 (ccons h1_45 (ccons h1_48 (ccons h1_49 (by simp)))))))) (by decide +kernel)
private def w2_76 : List T := [8, 19, 21, 33, 48, 104, 113, 279, 373, 1051, 1117, 1145, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_76 : good 2 w2_76 := by
  exact build (cs := [w1_1, w1_11, w1_40, w1_45, w1_48]) (ccons h1_1 (ccons h1_11 (ccons h1_40 (ccons h1_45 (ccons h1_48 (by simp)))))) (by decide +kernel)
private def w2_77 : List T := [3, 5, 8, 33, 48, 295, 360, 1051, 1053, 1303, 1310, 1331, 1333, 1334, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_77 : good 2 w2_77 := by
  exact build (cs := [w1_1, w1_45, w1_55, w1_56]) (ccons h1_1 (ccons h1_45 (ccons h1_55 (ccons h1_56 (by simp))))) (by decide +kernel)
private def w2_78 : List T := [3, 5, 8, 18, 20, 33, 48, 295, 310, 360, 1051, 1053, 1311, 1331, 1333, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_78 : good 2 w2_78 := by
  exact build (cs := [w1_1, w1_45, w1_56, w1_57]) (ccons h1_1 (ccons h1_45 (ccons h1_56 (ccons h1_57 (by simp))))) (by decide +kernel)
private def w2_79 : List T := [6, 33, 40, 48, 101, 108, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_79 : good 2 w2_79 := by
  exact build (cs := [w1_13, w1_30, w1_55, w1_57]) (ccons h1_13 (ccons h1_30 (ccons h1_55 (ccons h1_57 (by simp))))) (by decide +kernel)
private def w2_80 : List T := [6, 11, 19, 26, 34, 77, 87, 94, 107, 176, 237, 247, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_80 : good 2 w2_80 := by
  exact build (cs := [w1_7, w1_11, w1_13, w1_18, w1_37, w1_42, w1_52]) (ccons h1_7 (ccons h1_11 (ccons h1_13 (ccons h1_18 (ccons h1_37 (ccons h1_42 (ccons h1_52 (by simp)))))))) (by decide +kernel)
private def w2_81 : List T := [1, 6, 26, 34, 48, 69, 94, 110, 118, 124, 1051, 1059, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_81 : good 2 w2_81 := by
  exact build (cs := [w1_7, w1_11, w1_13, w1_25, w1_36]) (ccons h1_7 (ccons h1_11 (ccons h1_13 (ccons h1_25 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_82 : List T := [6, 8, 19, 34, 87, 104, 179, 247, 1051, 1119, 1130, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_82 : good 2 w2_82 := by
  exact build (cs := [w1_1, w1_7, w1_13, w1_18, w1_41]) (ccons h1_1 (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_41 (by simp)))))) (by decide +kernel)
private def w2_83 : List T := [1, 8, 22, 34, 104, 166, 178, 180, 197, 246, 1051, 1054, 1130, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_83 : good 2 w2_83 := by
  exact build (cs := [w1_1, w1_25, w1_36, w1_38, w1_41, w1_52]) (ccons h1_1 (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_41 (ccons h1_52 (by simp))))))) (by decide +kernel)
private def w2_84 : List T := [1, 6, 26, 42, 69, 94, 178, 184, 238, 246, 252, 1051, 1067, 1119, 1203, 1210, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_84 : good 2 w2_84 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_25, w1_36, w1_53]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_25 (ccons h1_36 (ccons h1_53 (by simp))))))) (by decide +kernel)
private def w2_85 : List T := [7, 8, 19, 34, 87, 104, 176, 1038, 1051, 1119, 1130, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_85 : good 2 w2_85 := by
  exact build (cs := [w1_1, w1_11, w1_18, w1_29, w1_41]) (ccons h1_1 (ccons h1_11 (ccons h1_18 (ccons h1_29 (ccons h1_41 (by simp)))))) (by decide +kernel)
private def w2_86 : List T := [1, 14, 26, 34, 69, 94, 106, 176, 238, 246, 252, 1051, 1059, 1119, 1131, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_86 : good 2 w2_86 := by
  exact build (cs := [w1_11, w1_18, w1_25, w1_36, w1_53]) (ccons h1_11 (ccons h1_18 (ccons h1_25 (ccons h1_36 (ccons h1_53 (by simp)))))) (by decide +kernel)
private def w2_87 : List T := [1, 8, 22, 34, 104, 182, 197, 1051, 1054, 1130, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_87 : good 2 w2_87 := by
  exact build (cs := [w1_1, w1_25, w1_38, w1_41, w1_52, w1_53]) (ccons h1_1 (ccons h1_25 (ccons h1_38 (ccons h1_41 (ccons h1_52 (ccons h1_53 (by simp))))))) (by decide +kernel)
private def w2_88 : List T := [5, 8, 22, 34, 48, 104, 118, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_88 : good 2 w2_88 := by
  exact build (cs := [w1_1, w1_36, w1_38, w1_42]) (ccons h1_1 (ccons h1_36 (ccons h1_38 (ccons h1_42 (by simp))))) (by decide +kernel)
private def w2_89 : List T := [1, 6, 26, 34, 40, 48, 69, 94, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_89 : good 2 w2_89 := by
  exact build (cs := [w1_13, w1_25, w1_29, w1_38]) (ccons h1_13 (ccons h1_25 (ccons h1_29 (ccons h1_38 (by simp))))) (by decide +kernel)
private def w2_90 : List T := [6, 9, 21, 28, 36, 109, 176, 245, 252, 1047, 1051, 1054, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_90 : good 2 w2_90 := by
  exact build (cs := [w1_6, w1_19, w1_28, w1_30, w1_37, w1_43, w1_49, w1_58, w1_59]) (ccons h1_6 (ccons h1_19 (ccons h1_28 (ccons h1_30 (ccons h1_37 (ccons h1_43 (ccons h1_49 (ccons h1_58 (ccons h1_59 (by simp)))))))))) (by decide +kernel)
private def w2_91 : List T := [1, 10, 22, 28, 36, 69, 110, 176, 246, 252, 1051, 1119, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_91 : good 2 w2_91 := by
  exact build (cs := [w1_6, w1_19, w1_25, w1_27, w1_38, w1_49]) (ccons h1_6 (ccons h1_19 (ccons h1_25 (ccons h1_27 (ccons h1_38 (ccons h1_49 (by simp))))))) (by decide +kernel)
private def w2_92 : List T := [6, 8, 21, 36, 104, 181, 1039, 1051, 1053, 1054, 1183, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_92 : good 2 w2_92 := by
  exact build (cs := [w1_1, w1_28, w1_30, w1_44, w1_49]) (ccons h1_1 (ccons h1_28 (ccons h1_30 (ccons h1_44 (ccons h1_49 (by simp)))))) (by decide +kernel)
private def w2_93 : List T := [1, 8, 22, 36, 50, 69, 104, 118, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_93 : good 2 w2_93 := by
  exact build (cs := [w1_1, w1_25, w1_38, w1_43]) (ccons h1_1 (ccons h1_25 (ccons h1_38 (ccons h1_43 (by simp))))) (by decide +kernel)
private def w2_94 : List T := [1, 6, 28, 36, 40, 69, 184, 252, 1051, 1054, 1103, 1117, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_94 : good 2 w2_94 := by
  exact build (cs := [w1_14, w1_25, w1_28, w1_30, w1_44]) (ccons h1_14 (ccons h1_25 (ccons h1_28 (ccons h1_30 (ccons h1_44 (by simp)))))) (by decide +kernel)
private def w2_95 : List T := [7, 8, 21, 22, 36, 104, 176, 1051, 1053, 1054, 1103, 1175, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_95 : good 2 w2_95 := by
  exact build (cs := [w1_1, w1_6, w1_12, w1_15, w1_44]) (ccons h1_1 (ccons h1_6 (ccons h1_12 (ccons h1_15 (ccons h1_44 (by simp)))))) (by decide +kernel)
private def w2_96 : List T := [1, 8, 22, 36, 69, 104, 182, 1051, 1054, 1103, 1117, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_96 : good 2 w2_96 := by
  exact build (cs := [w1_1, w1_25, w1_38, w1_44, w1_59]) (ccons h1_1 (ccons h1_25 (ccons h1_38 (ccons h1_44 (ccons h1_59 (by simp)))))) (by decide +kernel)
private def w2_97 : List T := [5, 6, 28, 36, 40, 48, 1087]
set_option maxHeartbeats 10000000 in
private theorem h2_97 : good 2 w2_97 := by
  exact build (cs := [w1_15, w1_30, w1_38]) (ccons h1_15 (ccons h1_30 (ccons h1_38 (by simp)))) (by decide +kernel)
private def w2_98 : List T := [6, 11, 16, 40, 77, 78, 176, 235, 237, 238, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_98 : good 2 w2_98 := by
  exact build (cs := [w1_2, w1_4, w1_7, w1_8, w1_12, w1_13, w1_24, w1_55]) (ccons h1_2 (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_12 (ccons h1_13 (ccons h1_24 (ccons h1_55 (by simp))))))))) (by decide +kernel)
private def w2_99 : List T := [4, 11, 25, 26, 40, 93, 688, 747, 749, 757, 762, 764, 774, 862, 1022, 1051, 1787, 1789, 1887, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_99 : good 2 w2_99 := by
  exact build (cs := [w1_2, w1_7, w1_8, w1_12, w1_13, w1_24, w1_40, w1_60]) (ccons h1_2 (ccons h1_7 (ccons h1_8 (ccons h1_12 (ccons h1_13 (ccons h1_24 (ccons h1_40 (ccons h1_60 (by simp))))))))) (by decide +kernel)
private def w2_100 : List T := [11, 13, 16, 40, 176, 263, 270, 1051, 1117, 1273, 1359, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_100 : good 2 w2_100 := by
  exact build (cs := [w1_2, w1_5, w1_8, w1_15, w1_18, w1_21, w1_40, w1_45, w1_55]) (ccons h1_2 (ccons h1_5 (ccons h1_8 (ccons h1_15 (ccons h1_18 (ccons h1_21 (ccons h1_40 (ccons h1_45 (ccons h1_55 (by simp)))))))))) (by decide +kernel)
private def w2_101 : List T := [1, 12, 26, 40, 69, 176, 286, 1051, 1101, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_101 : good 2 w2_101 := by
  exact build (cs := [w1_2, w1_5, w1_8, w1_12, w1_15, w1_16, w1_25, w1_40]) (ccons h1_2 (ccons h1_5 (ccons h1_8 (ccons h1_12 (ccons h1_15 (ccons h1_16 (ccons h1_25 (ccons h1_40 (by simp))))))))) (by decide +kernel)
private def w2_102 : List T := [1, 10, 12, 16, 40, 69, 270, 560, 814, 1051, 1052, 1117, 1310, 1375, 1846, 1851, 1919]
set_option maxHeartbeats 10000000 in
private theorem h2_102 : good 2 w2_102 := by
  exact build (cs := [w1_16, w1_23, w1_25, w1_36, w1_38, w1_45, w1_55, w1_60]) (ccons h1_16 (ccons h1_23 (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_45 (ccons h1_55 (ccons h1_60 (by simp))))))))) (by decide +kernel)
private def w2_103 : List T := [1, 26, 28, 40, 176, 197, 286, 430, 438, 440, 508, 1051, 1245, 1467, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_103 : good 2 w2_103 := by
  exact build (cs := [w1_8, w1_16, w1_21, w1_25, w1_36, w1_45]) (ccons h1_8 (ccons h1_16 (ccons h1_21 (ccons h1_25 (ccons h1_36 (ccons h1_45 (by simp))))))) (by decide +kernel)
private def w2_104 : List T := [1, 20, 26, 48, 69, 286, 360, 1051, 1109, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_104 : good 2 w2_104 := by
  exact build (cs := [w1_2, w1_5, w1_9, w1_10, w1_19, w1_25, w1_26, w1_40]) (ccons h1_2 (ccons h1_5 (ccons h1_9 (ccons h1_10 (ccons h1_19 (ccons h1_25 (ccons h1_26 (ccons h1_40 (by simp))))))))) (by decide +kernel)
private def w2_105 : List T := [3, 8, 22, 38, 48, 71, 104, 118, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_105 : good 2 w2_105 := by
  exact build (cs := [w1_1, w1_25, w1_37, w1_61]) (ccons h1_1 (ccons h1_25 (ccons h1_37 (ccons h1_61 (by simp))))) (by decide +kernel)
private def w2_106 : List T := [6, 11, 17, 26, 32, 79, 85, 94, 104, 176, 239, 245, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_106 : good 2 w2_106 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_7, w1_8, w1_13, w1_37, w1_47]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_37 (ccons h1_47 (by simp))))))))) (by decide +kernel)
private def w2_107 : List T := [3, 8, 22, 32, 104, 182, 199, 1038, 1051, 1118, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_107 : good 2 w2_107 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_25, w1_52]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_25 (ccons h1_52 (by simp))))))) (by decide +kernel)
private def w2_108 : List T := [7, 8, 21, 22, 32, 104, 176, 228, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_108 : good 2 w2_108 := by
  exact build (cs := [w1_1, w1_10, w1_15, w1_47, w1_49, w1_62]) (ccons h1_1 (ccons h1_10 (ccons h1_15 (ccons h1_47 (ccons h1_49 (ccons h1_62 (by simp))))))) (by decide +kernel)
private def w2_109 : List T := [4, 11, 17, 26, 32, 77, 85, 92, 104, 518, 591, 606, 690, 751, 757, 766, 1051, 1117, 1631, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_109 : good 2 w2_109 := by
  exact build (cs := [w1_3, w1_7, w1_8, w1_13, w1_35, w1_43, w1_47]) (ccons h1_3 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_35 (ccons h1_43 (ccons h1_47 (by simp)))))))) (by decide +kernel)
private def w2_110 : List T := [4, 19, 25, 26, 32, 93, 104, 688, 765, 774, 855, 862, 1051, 1787, 1887, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_110 : good 2 w2_110 := by
  exact build (cs := [w1_0, w1_3, w1_6, w1_7, w1_10, w1_35, w1_40, w1_48]) (ccons h1_0 (ccons h1_3 (ccons h1_6 (ccons h1_7 (ccons h1_10 (ccons h1_35 (ccons h1_40 (ccons h1_48 (by simp))))))))) (by decide +kernel)
private def w2_111 : List T := [11, 13, 25, 32, 93, 176, 271, 360, 509, 1051, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_111 : good 2 w2_111 := by
  exact build (cs := [w1_0, w1_8, w1_18, w1_21, w1_26, w1_47, w1_48, w1_58]) (ccons h1_0 (ccons h1_8 (ccons h1_18 (ccons h1_21 (ccons h1_26 (ccons h1_47 (ccons h1_48 (ccons h1_58 (by simp))))))))) (by decide +kernel)
private def w2_112 : List T := [6, 19, 26, 48, 119, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_112 : good 2 w2_112 := by
  exact build (cs := [w1_2, w1_7, w1_10, w1_13, w1_19, w1_63]) (ccons h1_2 (ccons h1_7 (ccons h1_10 (ccons h1_13 (ccons h1_19 (ccons h1_63 (by simp))))))) (by decide +kernel)
private def w2_113 : List T := [1, 6, 26, 40, 69, 94, 184, 229, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_113 : good 2 w2_113 := by
  exact build (cs := [w1_4, w1_7, w1_8, w1_13, w1_22, w1_24, w1_64]) (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_22 (ccons h1_24 (ccons h1_64 (by simp)))))))) (by decide +kernel)
private def w2_114 : List T := [8, 19, 21, 32, 104, 176, 245, 263, 278, 343, 1051, 1117, 1275, 1277, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_114 : good 2 w2_114 := by
  exact build (cs := [w1_0, w1_1, w1_2, w1_3, w1_4, w1_48]) (ccons h1_0 (ccons h1_1 (ccons h1_2 (ccons h1_3 (ccons h1_4 (ccons h1_48 (by simp))))))) (by decide +kernel)
private def w2_115 : List T := [11, 13, 16, 32, 104, 176, 237, 263, 270, 1051, 1117, 1275, 1277, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_115 : good 2 w2_115 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_6, w1_8, w1_10, w1_11, w1_18, w1_48, w1_55]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_6 (ccons h1_8 (ccons h1_10 (ccons h1_11 (ccons h1_18 (ccons h1_48 (ccons h1_55 (by simp))))))))))) (by decide +kernel)
private def w2_116 : List T := [1, 8, 38, 48, 101, 104, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_116 : good 2 w2_116 := by
  exact build (cs := [w1_1, w1_37, w1_55, w1_64, w1_65]) (ccons h1_1 (ccons h1_37 (ccons h1_55 (ccons h1_64 (ccons h1_65 (by simp)))))) (by decide +kernel)
private def w2_117 : List T := [3, 6, 8, 18, 32, 104, 135, 182, 231, 1038, 1051, 1173, 1182, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_117 : good 2 w2_117 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_39, w1_47, w1_52, w1_57]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_39 (ccons h1_47 (ccons h1_52 (ccons h1_57 (by simp))))))))) (by decide +kernel)
private def w2_118 : List T := [2, 13, 17, 24, 32, 85, 92, 176, 262, 365, 501, 508, 1051, 1117, 1287, 1294, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_118 : good 2 w2_118 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_11, w1_18, w1_28, w1_30, w1_58]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_11 (ccons h1_18 (ccons h1_28 (ccons h1_30 (ccons h1_58 (by simp)))))))))) (by decide +kernel)
private def w2_119 : List T := [4, 11, 19, 26, 32, 85, 92, 105, 178, 235, 243, 250, 262, 343, 350, 503, 510, 1051, 1117, 1275, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_119 : good 2 w2_119 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_33, w1_39, w1_43, w1_46, w1_66]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_33 (ccons h1_39 (ccons h1_43 (ccons h1_46 (ccons h1_66 (by simp))))))))) (by decide +kernel)
private def w2_120 : List T := [2, 9, 21, 28, 32, 77, 105, 518, 692, 749, 757, 764, 1051, 1117, 1559, 1566, 1631, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_120 : good 2 w2_120 := by
  exact build (cs := [w1_17, w1_19, w1_28, w1_30, w1_39, w1_49, w1_52, w1_58, w1_67]) (ccons h1_17 (ccons h1_19 (ccons h1_28 (ccons h1_30 (ccons h1_39 (ccons h1_49 (ccons h1_52 (ccons h1_58 (ccons h1_67 (by simp)))))))))) (by decide +kernel)
private def w2_121 : List T := [11, 13, 25, 41, 93, 185, 271, 509, 1051, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_121 : good 2 w2_121 := by
  exact build (cs := [w1_18, w1_40, w1_45, w1_48, w1_58, w1_68]) (ccons h1_18 (ccons h1_40 (ccons h1_45 (ccons h1_48 (ccons h1_58 (ccons h1_68 (by simp))))))) (by decide +kernel)
private def w2_122 : List T := [4, 18, 25, 32, 77, 176, 278, 349, 361, 509, 1051, 1375, 1387, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_122 : good 2 w2_122 := by
  exact build (cs := [w1_0, w1_2, w1_6, w1_9, w1_10, w1_17, w1_26, w1_33, w1_40, w1_48]) (ccons h1_0 (ccons h1_2 (ccons h1_6 (ccons h1_9 (ccons h1_10 (ccons h1_17 (ccons h1_26 (ccons h1_33 (ccons h1_40 (ccons h1_48 (by simp))))))))))) (by decide +kernel)
private def w2_123 : List T := [2, 4, 9, 16, 32, 77, 262, 361, 560, 806, 877, 1044, 1051, 1117, 1302, 1375, 1919]
set_option maxHeartbeats 10000000 in
private theorem h2_123 : good 2 w2_123 := by
  exact build (cs := [w1_9, w1_26, w1_37, w1_45, w1_50, w1_55, w1_66, w1_67]) (ccons h1_9 (ccons h1_26 (ccons h1_37 (ccons h1_45 (ccons h1_50 (ccons h1_55 (ccons h1_66 (ccons h1_67 (by simp))))))))) (by decide +kernel)
private def w2_124 : List T := [4, 11, 19, 24, 32, 77, 85, 92, 176, 262, 343, 367, 503, 508, 1051, 1117, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_124 : good 2 w2_124 := by
  exact build (cs := [w1_0, w1_2, w1_6, w1_7, w1_9, w1_13, w1_18, w1_49]) (ccons h1_0 (ccons h1_2 (ccons h1_6 (ccons h1_7 (ccons h1_9 (ccons h1_13 (ccons h1_18 (ccons h1_49 (by simp))))))))) (by decide +kernel)
private def w2_125 : List T := [4, 19, 25, 26, 32, 149, 156, 176, 221, 262, 361, 407, 414, 438, 493, 503, 510, 1051, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_125 : good 2 w2_125 := by
  exact build (cs := [w1_9, w1_26, w1_39, w1_45, w1_52, w1_59, w1_69]) (ccons h1_9 (ccons h1_26 (ccons h1_39 (ccons h1_45 (ccons h1_52 (ccons h1_59 (ccons h1_69 (by simp)))))))) (by decide +kernel)
private def w2_126 : List T := [6, 13, 21, 28, 32, 109, 176, 245, 252, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_126 : good 2 w2_126 := by
  exact build (cs := [w1_10, w1_28, w1_30, w1_49, w1_50, w1_58, w1_59]) (ccons h1_10 (ccons h1_28 (ccons h1_30 (ccons h1_49 (ccons h1_50 (ccons h1_58 (ccons h1_59 (by simp)))))))) (by decide +kernel)
private def w2_127 : List T := [2, 4, 25, 41, 49, 69, 262, 349, 365, 373, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_127 : good 2 w2_127 := by
  exact build (cs := [w1_13, w1_30, w1_48, w1_70]) (ccons h1_13 (ccons h1_30 (ccons h1_48 (ccons h1_70 (by simp))))) (by decide +kernel)
private def w2_128 : List T := [6, 11, 19, 24, 32, 79, 87, 92, 106, 176, 239, 247, 252, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_128 : good 2 w2_128 := by
  exact build (cs := [w1_0, w1_2, w1_7, w1_13, w1_18, w1_37, w1_41, w1_49]) (ccons h1_0 (ccons h1_2 (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_37 (ccons h1_41 (ccons h1_49 (by simp))))))))) (by decide +kernel)
private def w2_129 : List T := [4, 11, 19, 25, 32, 93, 104, 177, 233, 248, 262, 335, 343, 362, 495, 503, 508, 1051, 1273, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_129 : good 2 w2_129 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_31, w1_41, w1_45, w1_49]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_31 (ccons h1_41 (ccons h1_45 (ccons h1_49 (by simp)))))))) (by decide +kernel)
private def w2_130 : List T := [1, 14, 22, 28, 32, 69, 106, 180, 238, 246, 252, 1051, 1054, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_130 : good 2 w2_130 := by
  exact build (cs := [w1_17, w1_19, w1_25, w1_31, w1_38, w1_49, w1_53]) (ccons h1_17 (ccons h1_19 (ccons h1_25 (ccons h1_31 (ccons h1_38 (ccons h1_49 (ccons h1_53 (by simp)))))))) (by decide +kernel)
private def w2_131 : List T := [3, 6, 26, 42, 71, 94, 186, 254, 1051, 1119, 1131, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_131 : good 2 w2_131 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_25, w1_53, w1_71]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_25 (ccons h1_53 (ccons h1_71 (by simp))))))) (by decide +kernel)
private def w2_132 : List T := [1, 26, 28, 48, 69, 286, 294, 366, 374, 380, 1051, 1117, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_132 : good 2 w2_132 := by
  exact build (cs := [w1_9, w1_25, w1_26, w1_36, w1_37, w1_45]) (ccons h1_9 (ccons h1_25 (ccons h1_26 (ccons h1_36 (ccons h1_37 (ccons h1_45 (by simp))))))) (by decide +kernel)
private def w2_133 : List T := [1, 26, 28, 32, 176, 197, 286, 290, 362, 438, 494, 508, 1051, 1245, 1459, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_133 : good 2 w2_133 := by
  exact build (cs := [w1_9, w1_25, w1_26, w1_36, w1_41, w1_45]) (ccons h1_9 (ccons h1_25 (ccons h1_26 (ccons h1_36 (ccons h1_41 (ccons h1_45 (by simp))))))) (by decide +kernel)
private def w2_134 : List T := [5, 10, 22, 28, 32, 102, 106, 108, 176, 246, 252, 1055, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_134 : good 2 w2_134 := by
  exact build (cs := [w1_10, w1_36, w1_38, w1_49, w1_71]) (ccons h1_10 (ccons h1_36 (ccons h1_38 (ccons h1_49 (ccons h1_71 (by simp)))))) (by decide +kernel)
private def w2_135 : List T := [1, 6, 26, 42, 48, 69, 94, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_135 : good 2 w2_135 := by
  exact build (cs := [w1_13, w1_25, w1_32, w1_38]) (ccons h1_13 (ccons h1_25 (ccons h1_32 (ccons h1_38 (by simp))))) (by decide +kernel)
private def w2_136 : List T := [1, 6, 28, 52, 69, 124, 1051, 1054, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_136 : good 2 w2_136 := by
  exact build (cs := [w1_19, w1_25, w1_28, w1_30]) (ccons h1_19 (ccons h1_25 (ccons h1_28 (ccons h1_30 (by simp))))) (by decide +kernel)
private def w2_137 : List T := [1, 26, 28, 32, 176, 197, 286, 300, 430, 438, 440, 508, 1051, 1245, 1467, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_137 : good 2 w2_137 := by
  exact build (cs := [w1_9, w1_16, w1_23, w1_25, w1_26, w1_36, w1_45, w1_47]) (ccons h1_9 (ccons h1_16 (ccons h1_23 (ccons h1_25 (ccons h1_26 (ccons h1_36 (ccons h1_45 (ccons h1_47 (by simp))))))))) (by decide +kernel)
private def w2_138 : List T := [1, 6, 26, 50, 69, 94, 110, 118, 124, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_138 : good 2 w2_138 := by
  exact build (cs := [w1_7, w1_13, w1_25, w1_33, w1_36]) (ccons h1_7 (ccons h1_13 (ccons h1_25 (ccons h1_33 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_139 : List T := [5, 19, 25, 48, 263, 278, 285, 343, 381, 1051, 1310, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_139 : good 2 w2_139 := by
  exact build (cs := [w1_2, w1_9, w1_10, w1_26, w1_40, w1_48, w1_70, w1_72]) (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_26 (ccons h1_40 (ccons h1_48 (ccons h1_70 (ccons h1_72 (by simp))))))))) (by decide +kernel)
private def w2_140 : List T := [1, 26, 28, 48, 69, 286, 310, 366, 380, 1051, 1117, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_140 : good 2 w2_140 := by
  exact build (cs := [w1_9, w1_23, w1_25, w1_26, w1_36, w1_45, w1_63]) (ccons h1_9 (ccons h1_23 (ccons h1_25 (ccons h1_26 (ccons h1_36 (ccons h1_45 (ccons h1_63 (by simp)))))))) (by decide +kernel)
private def w2_141 : List T := [5, 6, 28, 48, 124, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_141 : good 2 w2_141 := by
  exact build (cs := [w1_10, w1_24, w1_28, w1_30, w1_36]) (ccons h1_10 (ccons h1_24 (ccons h1_28 (ccons h1_30 (ccons h1_36 (by simp)))))) (by decide +kernel)
private def w2_142 : List T := [2, 4, 25, 56, 93, 262, 380, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_142 : good 2 w2_142 := by
  exact build (cs := [w1_13, w1_30, w1_48, w1_54]) (ccons h1_13 (ccons h1_30 (ccons h1_48 (ccons h1_54 (by simp))))) (by decide +kernel)
private def w2_143 : List T := [4, 11, 17, 26, 32, 77, 85, 92, 104, 178, 235, 241, 250, 262, 335, 350, 495, 501, 510, 1051, 1117, 1275, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_143 : good 2 w2_143 := by
  exact build (cs := [w1_3, w1_7, w1_8, w1_13, w1_43, w1_47, w1_66]) (ccons h1_3 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_43 (ccons h1_47 (ccons h1_66 (by simp)))))))) (by decide +kernel)
private def w2_144 : List T := [6, 13, 21, 28, 32, 104, 180, 237, 245, 252, 1039, 1051, 1054, 1117, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_144 : good 2 w2_144 := by
  exact build (cs := [w1_3, w1_8, w1_17, w1_19, w1_21, w1_28, w1_30, w1_41, w1_73]) (ccons h1_3 (ccons h1_8 (ccons h1_17 (ccons h1_19 (ccons h1_21 (ccons h1_28 (ccons h1_30 (ccons h1_41 (ccons h1_73 (by simp)))))))))) (by decide +kernel)
private def w2_145 : List T := [2, 4, 9, 48, 69, 268, 294, 365, 1044, 1051, 1109, 1310, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_145 : good 2 w2_145 := by
  exact build (cs := [w1_9, w1_26, w1_37, w1_45, w1_50, w1_55, w1_66, w1_73]) (ccons h1_9 (ccons h1_26 (ccons h1_37 (ccons h1_45 (ccons h1_50 (ccons h1_55 (ccons h1_66 (ccons h1_73 (by simp))))))))) (by decide +kernel)
private def w2_146 : List T := [2, 4, 25, 41, 49, 56, 93, 121, 262, 381, 1051, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_146 : good 2 w2_146 := by
  exact build (cs := [w1_7, w1_28, w1_40, w1_45, w1_48]) (ccons h1_7 (ccons h1_28 (ccons h1_40 (ccons h1_45 (ccons h1_48 (by simp)))))) (by decide +kernel)
private def w2_147 : List T := [8, 19, 21, 32, 104, 263, 278, 689, 757, 791, 1051, 1117, 1359, 1374, 1787, 1789, 1887, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_147 : good 2 w2_147 := by
  exact build (cs := [w1_1, w1_3, w1_35, w1_40, w1_48]) (ccons h1_1 (ccons h1_3 (ccons h1_35 (ccons h1_40 (ccons h1_48 (by simp)))))) (by decide +kernel)
private def w2_148 : List T := [5, 8, 19, 32, 279, 360, 561, 807, 819, 821, 822, 887, 1051, 1295, 1309, 1310, 1375, 1903, 1915, 1917, 1918, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_148 : good 2 w2_148 := by
  exact build (cs := [w1_1, w1_35, w1_45, w1_70, w1_74]) (ccons h1_1 (ccons h1_35 (ccons h1_45 (ccons h1_70 (ccons h1_74 (by simp)))))) (by decide +kernel)
private def w2_149 : List T := [4, 11, 19, 32, 77, 85, 104, 518, 545, 599, 623, 689, 759, 1051, 1117, 1631, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_149 : good 2 w2_149 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_35, w1_49]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_35 (ccons h1_49 (by simp)))))) (by decide +kernel)
private def w2_150 : List T := [4, 11, 19, 25, 26, 32, 157, 262, 360, 399, 407, 414, 689, 951, 1007, 1022, 1051, 1503, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_150 : good 2 w2_150 := by
  exact build (cs := [w1_3, w1_21, w1_35, w1_44, w1_45, w1_62, w1_69]) (ccons h1_3 (ccons h1_21 (ccons h1_35 (ccons h1_44 (ccons h1_45 (ccons h1_62 (ccons h1_69 (by simp)))))))) (by decide +kernel)
private def w2_151 : List T := [6, 8, 21, 32, 104, 181, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_151 : good 2 w2_151 := by
  exact build (cs := [w1_1, w1_28, w1_30, w1_47, w1_49, w1_62]) (ccons h1_1 (ccons h1_28 (ccons h1_30 (ccons h1_47 (ccons h1_49 (ccons h1_62 (by simp))))))) (by decide +kernel)
private def w2_152 : List T := [3, 6, 26, 50, 71, 126, 1051, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_152 : good 2 w2_152 := by
  exact build (cs := [w1_7, w1_13, w1_25, w1_33, w1_46]) (ccons h1_7 (ccons h1_13 (ccons h1_25 (ccons h1_33 (ccons h1_46 (by simp)))))) (by decide +kernel)
private def w2_153 : List T := [1, 8, 22, 32, 69, 360, 562, 806, 820, 886, 1051, 1054, 1119, 1651, 1903, 1911, 1915, 1917, 1918, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_153 : good 2 w2_153 := by
  exact build (cs := [w1_1, w1_25, w1_35, w1_38, w1_66]) (ccons h1_1 (ccons h1_25 (ccons h1_35 (ccons h1_38 (ccons h1_66 (by simp)))))) (by decide +kernel)
private def w2_154 : List T := [5, 8, 22, 32, 104, 178, 246, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_154 : good 2 w2_154 := by
  exact build (cs := [w1_1, w1_36, w1_38, w1_46, w1_47, w1_59, w1_62]) (ccons h1_1 (ccons h1_36 (ccons h1_38 (ccons h1_46 (ccons h1_47 (ccons h1_59 (ccons h1_62 (by simp)))))))) (by decide +kernel)
private def w2_155 : List T := [1, 6, 26, 40, 50, 69, 94, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_155 : good 2 w2_155 := by
  exact build (cs := [w1_13, w1_25, w1_34, w1_38]) (ccons h1_13 (ccons h1_25 (ccons h1_34 (ccons h1_38 (by simp))))) (by decide +kernel)
private def w2_156 : List T := [3, 8, 21, 22, 32, 104, 519, 692, 1051, 1053, 1054, 1551, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_156 : good 2 w2_156 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_17, w1_19, w1_20, w1_21, w1_35]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_17 (ccons h1_19 (ccons h1_20 (ccons h1_21 (ccons h1_35 (by simp))))))))) (by decide +kernel)
private def w2_157 : List T := [1, 8, 22, 32, 69, 104, 550, 564, 630, 1051, 1054, 1119, 1647, 1655, 1659, 1661, 1662, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_157 : good 2 w2_157 := by
  exact build (cs := [w1_1, w1_25, w1_35, w1_36, w1_38, w1_67, w1_73]) (ccons h1_1 (ccons h1_25 (ccons h1_35 (ccons h1_36 (ccons h1_38 (ccons h1_67 (ccons h1_73 (by simp)))))))) (by decide +kernel)
private def w2_158 : List T := [1, 14, 22, 28, 32, 69, 104, 548, 622, 692, 758, 764, 1051, 1054, 1119, 1647, 1783, 1787, 1789, 1790, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_158 : good 2 w2_158 := by
  exact build (cs := [w1_19, w1_25, w1_35, w1_38, w1_49, w1_60]) (ccons h1_19 (ccons h1_25 (ccons h1_35 (ccons h1_38 (ccons h1_49 (ccons h1_60 (by simp))))))) (by decide +kernel)
private def w2_159 : List T := [1, 6, 28, 40, 52, 69, 1054, 1070, 1078, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_159 : good 2 w2_159 := by
  exact build (cs := [w1_20, w1_25, w1_30]) (ccons h1_20 (ccons h1_25 (ccons h1_30 (by simp)))) (by decide +kernel)
private def w2_160 : List T := [5, 6, 28, 40, 188, 1039, 1051, 1053, 1054, 1215]
set_option maxHeartbeats 10000000 in
private theorem h2_160 : good 2 w2_160 := by
  exact build (cs := [w1_21, w1_30, w1_38]) (ccons h1_21 (ccons h1_30 (ccons h1_38 (by simp)))) (by decide +kernel)
private def w2_161 : List T := [1, 6, 28, 44, 69, 184, 252, 1051, 1054, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_161 : good 2 w2_161 := by
  exact build (cs := [w1_22, w1_25, w1_28, w1_30, w1_47]) (ccons h1_22 (ccons h1_25 (ccons h1_28 (ccons h1_30 (ccons h1_47 (by simp)))))) (by decide +kernel)
private def w2_162 : List T := [6, 9, 26, 40, 77, 94, 184, 237, 254, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_162 : good 2 w2_162 := by
  exact build (cs := [w1_4, w1_7, w1_8, w1_13, w1_22, w1_24, w1_75]) (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_13 (ccons h1_22 (ccons h1_24 (ccons h1_75 (by simp)))))))) (by decide +kernel)
private def w2_163 : List T := [4, 11, 25, 26, 40, 93, 696, 765, 774, 862, 1051, 1787, 1887, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_163 : good 2 w2_163 := by
  exact build (cs := [w1_4, w1_7, w1_8, w1_22, w1_24, w1_40, w1_48, w1_60]) (ccons h1_4 (ccons h1_7 (ccons h1_8 (ccons h1_22 (ccons h1_24 (ccons h1_40 (ccons h1_48 (ccons h1_60 (by simp))))))))) (by decide +kernel)
private def w2_164 : List T := [1, 12, 26, 40, 69, 184, 286, 510, 1051, 1101, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_164 : good 2 w2_164 := by
  exact build (cs := [w1_4, w1_8, w1_22, w1_23, w1_24, w1_25, w1_40]) (ccons h1_4 (ccons h1_8 (ccons h1_22 (ccons h1_23 (ccons h1_24 (ccons h1_25 (ccons h1_40 (by simp)))))))) (by decide +kernel)
private def w2_165 : List T := [1, 26, 28, 40, 69, 286, 568, 814, 818, 820, 886, 892, 1051, 1117, 1375, 1850, 1919]
set_option maxHeartbeats 10000000 in
private theorem h2_165 : good 2 w2_165 := by
  exact build (cs := [w1_23, w1_25, w1_36, w1_38, w1_45, w1_60, w1_75]) (ccons h1_23 (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_45 (ccons h1_60 (ccons h1_75 (by simp)))))))) (by decide +kernel)
private def w2_166 : List T := [12, 25, 26, 40, 184, 205, 286, 446, 477, 1051, 1467, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_166 : good 2 w2_166 := by
  exact build (cs := [w1_8, w1_21, w1_23, w1_45, w1_47, w1_53]) (ccons h1_8 (ccons h1_21 (ccons h1_23 (ccons h1_45 (ccons h1_47 (ccons h1_53 (by simp))))))) (by decide +kernel)
private def w2_167 : List T := [5, 6, 28, 40, 108, 184, 252, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_167 : good 2 w2_167 := by
  exact build (cs := [w1_24, w1_28, w1_30, w1_36, w1_47]) (ccons h1_24 (ccons h1_28 (ccons h1_30 (ccons h1_36 (ccons h1_47 (by simp)))))) (by decide +kernel)
private def w2_168 : List T := [2, 4, 8, 49, 85, 360, 629, 774, 1051, 1117, 1403, 1919]
set_option maxHeartbeats 10000000 in
private theorem h2_168 : good 2 w2_168 := by
  exact build (cs := [w1_1, w1_7, w1_13, w1_28, w1_40, w1_76]) (ccons h1_1 (ccons h1_7 (ccons h1_13 (ccons h1_28 (ccons h1_40 (ccons h1_76 (by simp))))))) (by decide +kernel)
private def w2_169 : List T := [4, 19, 25, 26, 48, 93, 113, 377, 629, 774, 855, 862, 893, 1051, 1403, 1919]
set_option maxHeartbeats 10000000 in
private theorem h2_169 : good 2 w2_169 := by
  exact build (cs := [w1_2, w1_7, w1_10, w1_19, w1_40, w1_48, w1_76]) (ccons h1_2 (ccons h1_7 (ccons h1_10 (ccons h1_19 (ccons h1_40 (ccons h1_48 (ccons h1_76 (by simp)))))))) (by decide +kernel)
private def w2_170 : List T := [4, 11, 25, 32, 85, 104, 524, 605, 688, 765, 782, 839, 1051, 1787, 1887, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_170 : good 2 w2_170 := by
  exact build (cs := [w1_0, w1_2, w1_3, w1_6, w1_8, w1_10, w1_18, w1_40, w1_48, w1_60]) (ccons h1_0 (ccons h1_2 (ccons h1_3 (ccons h1_6 (ccons h1_8 (ccons h1_10 (ccons h1_18 (ccons h1_40 (ccons h1_48 (ccons h1_60 (by simp))))))))))) (by decide +kernel)
private def w2_171 : List T := [7, 8, 17, 32, 84, 360, 548, 560, 629, 806, 871, 1037, 1051, 1103, 1118, 1631, 1903, 1911, 1915, 1917, 1918, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_171 : good 2 w2_171 := by
  exact build (cs := [w1_1, w1_35, w1_37, w1_60, w1_76, w1_77, w1_78]) (ccons h1_1 (ccons h1_35 (ccons h1_37 (ccons h1_60 (ccons h1_76 (ccons h1_77 (ccons h1_78 (by simp)))))))) (by decide +kernel)
private def w2_172 : List T := [3, 4, 8, 17, 18, 32, 104, 149, 518, 647, 694, 743, 757, 1051, 1180, 1245, 1694, 1791]
set_option maxHeartbeats 10000000 in
private theorem h2_172 : good 2 w2_172 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_35, w1_47, w1_52, w1_69]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_35 (ccons h1_47 (ccons h1_52 (ccons h1_69 (by simp))))))))) (by decide +kernel)
private def w2_173 : List T := [2, 4, 40, 49, 117, 262, 1083, 1149, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_173 : good 2 w2_173 := by
  exact build (cs := [w1_13, w1_30, w1_48, w1_79, w1_80]) (ccons h1_13 (ccons h1_30 (ccons h1_48 (ccons h1_79 (ccons h1_80 (by simp)))))) (by decide +kernel)
private def w2_174 : List T := [5, 8, 16, 35, 104, 176, 263, 359, 1051, 1131, 1275, 1293, 1294, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_174 : good 2 w2_174 := by
  exact build (cs := [w1_1, w1_11, w1_18, w1_55, w1_70]) (ccons h1_1 (ccons h1_11 (ccons h1_18 (ccons h1_55 (ccons h1_70 (by simp)))))) (by decide +kernel)
private def w2_175 : List T := [3, 6, 8, 16, 37, 99, 102, 104, 176, 263, 359, 1051, 1053, 1054, 1131, 1133, 1134, 1275, 1277, 1278, 1303, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_175 : good 2 w2_175 := by
  exact build (cs := [w1_1, w1_27, w1_49, w1_55, w1_58, w1_65, w1_80]) (ccons h1_1 (ccons h1_27 (ccons h1_49 (ccons h1_55 (ccons h1_58 (ccons h1_65 (ccons h1_80 (by simp)))))))) (by decide +kernel)
private def w2_176 : List T := [5, 11, 16, 32, 77, 176, 263, 359, 363, 365, 366, 1051, 1117, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_176 : good 2 w2_176 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_10, w1_18, w1_27, w1_49, w1_55]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_10 (ccons h1_18 (ccons h1_27 (ccons h1_49 (ccons h1_55 (by simp))))))))) (by decide +kernel)
private def w2_177 : List T := [5, 8, 19, 32, 104, 179, 263, 343, 503, 1051, 1275, 1375, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_177 : good 2 w2_177 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_18, w1_70, w1_81]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_18 (ccons h1_70 (ccons h1_81 (by simp))))))) (by decide +kernel)
private def w2_178 : List T := [7, 8, 21, 32, 104, 693, 743, 1039, 1051, 1053, 1054, 1503, 1775, 1787, 1789, 1790, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_178 : good 2 w2_178 := by
  exact build (cs := [w1_1, w1_3, w1_8, w1_21, w1_35, w1_49, w1_72, w1_80]) (ccons h1_1 (ccons h1_3 (ccons h1_8 (ccons h1_21 (ccons h1_35 (ccons h1_49 (ccons h1_72 (ccons h1_80 (by simp))))))))) (by decide +kernel)
private def w2_179 : List T := [7, 11, 16, 32, 79, 360, 688, 879, 1051, 1119, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_179 : good 2 w2_179 := by
  exact build (cs := [w1_0, w1_2, w1_9, w1_18, w1_27, w1_35, w1_49, w1_55]) (ccons h1_0 (ccons h1_2 (ccons h1_9 (ccons h1_18 (ccons h1_27 (ccons h1_35 (ccons h1_49 (ccons h1_55 (by simp))))))))) (by decide +kernel)
private def w2_180 : List T := [5, 8, 19, 32, 176, 263, 277, 278, 360, 439, 1051, 1309, 1310, 1359, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_180 : good 2 w2_180 := by
  exact build (cs := [w1_3, w1_9, w1_21, w1_62, w1_70, w1_80]) (ccons h1_3 (ccons h1_9 (ccons h1_21 (ccons h1_62 (ccons h1_70 (ccons h1_80 (by simp))))))) (by decide +kernel)
private def w2_181 : List T := [3, 5, 40, 48, 263, 1083, 1309, 1310, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_181 : good 2 w2_181 := by
  exact build (cs := [w1_5, w1_15, w1_48, w1_55, w1_70, w1_80]) (ccons h1_5 (ccons h1_15 (ccons h1_48 (ccons h1_55 (ccons h1_70 (ccons h1_80 (by simp))))))) (by decide +kernel)
private def w2_182 : List T := [1, 14, 26, 42, 69, 94, 178, 184, 238, 246, 252, 1051, 1067, 1119, 1210, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_182 : good 2 w2_182 := by
  exact build (cs := [w1_18, w1_25, w1_36, w1_53]) (ccons h1_18 (ccons h1_25 (ccons h1_36 (ccons h1_53 (by simp))))) (by decide +kernel)
private def w2_183 : List T := [11, 13, 14, 16, 32, 79, 104, 176, 1051, 1119, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_183 : good 2 w2_183 := by
  exact build (cs := [w1_0, w1_2, w1_5, w1_8, w1_18, w1_47, w1_55]) (ccons h1_0 (ccons h1_2 (ccons h1_5 (ccons h1_8 (ccons h1_18 (ccons h1_47 (ccons h1_55 (by simp)))))))) (by decide +kernel)
private def w2_184 : List T := [3, 14, 26, 40, 71, 94, 186, 254, 1051, 1119, 1195, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_184 : good 2 w2_184 := by
  exact build (cs := [w1_8, w1_18, w1_25, w1_47]) (ccons h1_8 (ccons h1_18 (ccons h1_25 (ccons h1_47 (by simp))))) (by decide +kernel)
private def w2_185 : List T := [1, 4, 26, 40, 48, 69, 286, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_185 : good 2 w2_185 := by
  exact build (cs := [w1_5, w1_15, w1_20, w1_25, w1_48, w1_54]) (ccons h1_5 (ccons h1_15 (ccons h1_20 (ccons h1_25 (ccons h1_48 (ccons h1_54 (by simp))))))) (by decide +kernel)
private def w2_186 : List T := [1, 20, 26, 48, 69, 286, 382, 1051, 1109, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_186 : good 2 w2_186 := by
  exact build (cs := [w1_2, w1_6, w1_9, w1_10, w1_19, w1_25, w1_40]) (ccons h1_2 (ccons h1_6 (ccons h1_9 (ccons h1_10 (ccons h1_19 (ccons h1_25 (ccons h1_40 (by simp)))))))) (by decide +kernel)
private def w2_187 : List T := [5, 8, 22, 38, 48, 104, 118, 1055, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_187 : good 2 w2_187 := by
  exact build (cs := [w1_1, w1_36, w1_38, w1_50]) (ccons h1_1 (ccons h1_36 (ccons h1_38 (ccons h1_50 (by simp))))) (by decide +kernel)
private def w2_188 : List T := [1, 4, 42, 48, 69, 294, 300, 366, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_188 : good 2 w2_188 := by
  exact build (cs := [w1_25, w1_36, w1_38, w1_55, w1_70, w1_77]) (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_55 (ccons h1_70 (ccons h1_77 (by simp))))))) (by decide +kernel)
private def w2_189 : List T := [5, 14, 16, 32, 296, 560, 814, 1031, 1051, 1053, 1054, 1295, 1559, 1855]
set_option maxHeartbeats 10000000 in
private theorem h2_189 : good 2 w2_189 := by
  exact build (cs := [w1_26, w1_38, w1_65, w1_78]) (ccons h1_26 (ccons h1_38 (ccons h1_65 (ccons h1_78 (by simp))))) (by decide +kernel)
private def w2_190 : List T := [3, 6, 26, 40, 71, 94, 554, 622, 698, 766, 1051, 1119, 1647, 1783, 1787, 1789, 2047]
set_option maxHeartbeats 10000000 in
private theorem h2_190 : good 2 w2_190 := by
  exact build (cs := [w1_7, w1_13, w1_18, w1_25, w1_60, w1_71]) (ccons h1_7 (ccons h1_13 (ccons h1_18 (ccons h1_25 (ccons h1_60 (ccons h1_71 (by simp))))))) (by decide +kernel)
private def w2_191 : List T := [5, 14, 22, 28, 32, 110, 176, 246, 252, 1055, 1135, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_191 : good 2 w2_191 := by
  exact build (cs := [w1_10, w1_36, w1_38, w1_49, w1_82]) (ccons h1_10 (ccons h1_36 (ccons h1_38 (ccons h1_49 (ccons h1_82 (by simp)))))) (by decide +kernel)
private def w2_192 : List T := [1, 6, 8, 50, 104, 182, 197, 1051, 1147, 1182, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_192 : good 2 w2_192 := by
  exact build (cs := [w1_1, w1_25, w1_38, w1_52, w1_53, w1_69]) (ccons h1_1 (ccons h1_25 (ccons h1_38 (ccons h1_52 (ccons h1_53 (ccons h1_69 (by simp))))))) (by decide +kernel)
private def w2_193 : List T := [1, 20, 26, 48, 69, 286, 306, 378, 438, 510, 1051, 1109, 1375, 1403, 1535]
set_option maxHeartbeats 10000000 in
private theorem h2_193 : good 2 w2_193 := by
  exact build (cs := [w1_9, w1_25, w1_26, w1_45, w1_52, w1_63]) (ccons h1_9 (ccons h1_25 (ccons h1_26 (ccons h1_45 (ccons h1_52 (ccons h1_63 (by simp))))))) (by decide +kernel)
private def w2_194 : List T := [5, 8, 22, 32, 104, 182, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_194 : good 2 w2_194 := by
  exact build (cs := [w1_1, w1_36, w1_38, w1_47, w1_59, w1_62, w1_63]) (ccons h1_1 (ccons h1_36 (ccons h1_38 (ccons h1_47 (ccons h1_59 (ccons h1_62 (ccons h1_63 (by simp)))))))) (by decide +kernel)
private def w2_195 : List T := [1, 6, 42, 50, 174, 182, 197, 1083, 1182, 1279]
set_option maxHeartbeats 10000000 in
private theorem h2_195 : good 2 w2_195 := by
  exact build (cs := [w1_25, w1_36, w1_38, w1_53, w1_57, w1_69]) (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_53 (ccons h1_57 (ccons h1_69 (by simp))))))) (by decide +kernel)
private def w2_196 : List T := [1, 14, 22, 28, 32, 133, 176, 296, 430, 438, 444, 1051, 1175, 1181, 1310, 1471]
set_option maxHeartbeats 10000000 in
private theorem h2_196 : good 2 w2_196 := by
  exact build (cs := [w1_21, w1_26, w1_38, w1_56]) (ccons h1_21 (ccons h1_26 (ccons h1_38 (ccons h1_56 (by simp))))) (by decide +kernel)
private def w2_197 : List T := [1, 6, 44, 48, 69, 1054, 1070, 1078, 1083, 1151]
set_option maxHeartbeats 10000000 in
private theorem h2_197 : good 2 w2_197 := by
  exact build (cs := [w1_25, w1_30, w1_55]) (ccons h1_25 (ccons h1_30 (ccons h1_55 (by simp)))) (by decide +kernel)
private def w2_198 : List T := [2, 4, 41, 48, 109, 262, 372, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_198 : good 2 w2_198 := by
  exact build (cs := [w1_13, w1_30, w1_48, w1_79, w1_83]) (ccons h1_13 (ccons h1_30 (ccons h1_48 (ccons h1_79 (ccons h1_83 (by simp)))))) (by decide +kernel)
private def w2_199 : List T := [1, 4, 42, 48, 69, 302, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_199 : good 2 w2_199 := by
  exact build (cs := [w1_25, w1_36, w1_38, w1_54, w1_55, w1_70, w1_79]) (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_54 (ccons h1_55 (ccons h1_70 (ccons h1_79 (by simp)))))))) (by decide +kernel)
private def w2_200 : List T := [1, 4, 40, 50, 69, 310, 1083, 1310, 1326, 1407]
set_option maxHeartbeats 10000000 in
private theorem h2_200 : good 2 w2_200 := by
  exact build (cs := [w1_25, w1_36, w1_38, w1_54, w1_70, w1_83, w1_84]) (ccons h1_25 (ccons h1_36 (ccons h1_38 (ccons h1_54 (ccons h1_70 (ccons h1_83 (ccons h1_84 (by simp)))))))) (by decide +kernel)
private def w3_0 : List T := [3, 4, 8, 16, 32, 84, 176, 197, 262, 360, 1051, 1237, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_0 : good 3 w3_0 := by
  exact build (cs := [w2_0, w2_1, w2_2, w2_3, w2_4, w2_5, w2_6, w2_7, w2_8, w2_9, w2_10, w2_11, w2_12, w2_13, w2_14, w2_15]) (ccons h2_0 (ccons h2_1 (ccons h2_2 (ccons h2_3 (ccons h2_4 (ccons h2_5 (ccons h2_6 (ccons h2_7 (ccons h2_8 (ccons h2_9 (ccons h2_10 (ccons h2_11 (ccons h2_12 (ccons h2_13 (ccons h2_14 (ccons h2_15 (by simp))))))))))))))))) (by decide +kernel)
private def w3_1 : List T := [2, 5, 8, 16, 32, 84, 360, 688, 774, 1051, 1109, 1373, 1871, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_1 : good 3 w3_1 := by
  exact build (cs := [w2_0, w2_4, w2_14, w2_16, w2_17, w2_18, w2_19, w2_20, w2_21, w2_22, w2_23, w2_24, w2_25, w2_26, w2_27, w2_28, w2_29, w2_30]) (ccons h2_0 (ccons h2_4 (ccons h2_14 (ccons h2_16 (ccons h2_17 (ccons h2_18 (ccons h2_19 (ccons h2_20 (ccons h2_21 (ccons h2_22 (ccons h2_23 (ccons h2_24 (ccons h2_25 (ccons h2_26 (ccons h2_27 (ccons h2_28 (ccons h2_29 (ccons h2_30 (by simp))))))))))))))))))) (by decide +kernel)
private def w3_2 : List T := [1, 6, 8, 16, 32, 84, 104, 176, 197, 1051, 1118, 1279]
set_option maxHeartbeats 10000000 in
private theorem h3_2 : good 3 w3_2 := by
  exact build (cs := [w2_0, w2_3, w2_9, w2_14, w2_15, w2_31, w2_32, w2_33, w2_34, w2_35, w2_36, w2_37, w2_38]) (ccons h2_0 (ccons h2_3 (ccons h2_9 (ccons h2_14 (ccons h2_15 (ccons h2_31 (ccons h2_32 (ccons h2_33 (ccons h2_34 (ccons h2_35 (ccons h2_36 (ccons h2_37 (ccons h2_38 (by simp)))))))))))))) (by decide +kernel)
private def w3_3 : List T := [2, 4, 9, 24, 32, 197, 348, 360, 688, 774, 1051, 1501, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_3 : good 3 w3_3 := by
  exact build (cs := [w2_1, w2_6, w2_17, w2_22, w2_31, w2_34, w2_39, w2_40, w2_41, w2_42, w2_43, w2_44, w2_45, w2_46, w2_47, w2_48, w2_49, w2_50, w2_51]) (ccons h2_1 (ccons h2_6 (ccons h2_17 (ccons h2_22 (ccons h2_31 (ccons h2_34 (ccons h2_39 (ccons h2_40 (ccons h2_41 (ccons h2_42 (ccons h2_43 (ccons h2_44 (ccons h2_45 (ccons h2_46 (ccons h2_47 (ccons h2_48 (ccons h2_49 (ccons h2_50 (ccons h2_51 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_4 : List T := [1, 4, 10, 16, 32, 76, 197, 340, 360, 688, 774, 846, 1051, 1229, 1372, 1501, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_4 : good 3 w3_4 := by
  exact build (cs := [w2_1, w2_6, w2_7, w2_8, w2_15, w2_16, w2_32, w2_34, w2_45, w2_48, w2_49, w2_52, w2_53, w2_54, w2_55, w2_56, w2_57, w2_58]) (ccons h2_1 (ccons h2_6 (ccons h2_7 (ccons h2_8 (ccons h2_15 (ccons h2_16 (ccons h2_32 (ccons h2_34 (ccons h2_45 (ccons h2_48 (ccons h2_49 (ccons h2_52 (ccons h2_53 (ccons h2_54 (ccons h2_55 (ccons h2_56 (ccons h2_57 (ccons h2_58 (by simp))))))))))))))))))) (by decide +kernel)
private def w3_5 : List T := [1, 2, 12, 16, 32, 197, 340, 360, 688, 774, 1051, 1372, 1501, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_5 : good 3 w3_5 := by
  exact build (cs := [w2_2, w2_17, w2_22, w2_23, w2_29, w2_30, w2_32, w2_45, w2_46, w2_48, w2_49, w2_50, w2_59, w2_60, w2_61, w2_62, w2_63, w2_64]) (ccons h2_2 (ccons h2_17 (ccons h2_22 (ccons h2_23 (ccons h2_29 (ccons h2_30 (ccons h2_32 (ccons h2_45 (ccons h2_46 (ccons h2_48 (ccons h2_49 (ccons h2_50 (ccons h2_59 (ccons h2_60 (ccons h2_61 (ccons h2_62 (ccons h2_63 (ccons h2_64 (by simp))))))))))))))))))) (by decide +kernel)
private def w3_6 : List T := [2, 4, 8, 17, 32, 176, 197, 262, 340, 360, 469, 1051, 1100, 1229, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_6 : good 3 w3_6 := by
  exact build (cs := [w2_0, w2_1, w2_3, w2_4, w2_6, w2_7, w2_9, w2_10, w2_14, w2_17, w2_39, w2_42, w2_45, w2_49, w2_65, w2_66, w2_67, w2_68]) (ccons h2_0 (ccons h2_1 (ccons h2_3 (ccons h2_4 (ccons h2_6 (ccons h2_7 (ccons h2_9 (ccons h2_10 (ccons h2_14 (ccons h2_17 (ccons h2_39 (ccons h2_42 (ccons h2_45 (ccons h2_49 (ccons h2_65 (ccons h2_66 (ccons h2_67 (ccons h2_68 (by simp))))))))))))))))))) (by decide +kernel)
private def w3_7 : List T := [1, 4, 8, 18, 32, 84, 197, 262, 342, 360, 688, 1051, 1116, 1245, 1374, 1503, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_7 : good 3 w3_7 := by
  exact build (cs := [w2_0, w2_1, w2_3, w2_4, w2_5, w2_6, w2_7, w2_8, w2_9, w2_10, w2_11, w2_13, w2_14, w2_15, w2_29, w2_32, w2_69]) (ccons h2_0 (ccons h2_1 (ccons h2_3 (ccons h2_4 (ccons h2_5 (ccons h2_6 (ccons h2_7 (ccons h2_8 (ccons h2_9 (ccons h2_10 (ccons h2_11 (ccons h2_13 (ccons h2_14 (ccons h2_15 (ccons h2_29 (ccons h2_32 (ccons h2_69 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_8 : List T := [1, 2, 8, 20, 32, 197, 360, 688, 774, 1051, 1116, 1245, 1814, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_8 : good 3 w3_8 := by
  exact build (cs := [w2_0, w2_13, w2_14, w2_17, w2_19, w2_23, w2_25, w2_30, w2_32, w2_33, w2_37, w2_48, w2_62, w2_64, w2_70, w2_71, w2_72]) (ccons h2_0 (ccons h2_13 (ccons h2_14 (ccons h2_17 (ccons h2_19 (ccons h2_23 (ccons h2_25 (ccons h2_30 (ccons h2_32 (ccons h2_33 (ccons h2_37 (ccons h2_48 (ccons h2_62 (ccons h2_64 (ccons h2_70 (ccons h2_71 (ccons h2_72 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_9 : List T := [2, 4, 8, 16, 33, 69, 176, 262, 357, 360, 1051, 1109, 1375, 1391, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_9 : good 3 w3_9 := by
  exact build (cs := [w2_3, w2_19, w2_42, w2_52, w2_59, w2_73, w2_74, w2_75, w2_76, w2_77, w2_78, w2_79]) (ccons h2_3 (ccons h2_19 (ccons h2_42 (ccons h2_52 (ccons h2_59 (ccons h2_73 (ccons h2_74 (ccons h2_75 (ccons h2_76 (ccons h2_77 (ccons h2_78 (ccons h2_79 (by simp))))))))))))) (by decide +kernel)
private def w3_10 : List T := [1, 6, 8, 16, 34, 84, 104, 176, 197, 1051, 1118, 1130, 1279]
set_option maxHeartbeats 10000000 in
private theorem h3_10 : good 3 w3_10 := by
  exact build (cs := [w2_3, w2_18, w2_33, w2_40, w2_54, w2_60, w2_69, w2_80, w2_81, w2_82, w2_83, w2_84, w2_85, w2_86, w2_87, w2_88, w2_89]) (ccons h2_3 (ccons h2_18 (ccons h2_33 (ccons h2_40 (ccons h2_54 (ccons h2_60 (ccons h2_69 (ccons h2_80 (ccons h2_81 (ccons h2_82 (ccons h2_83 (ccons h2_84 (ccons h2_85 (ccons h2_86 (ccons h2_87 (ccons h2_88 (ccons h2_89 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_11 : List T := [1, 6, 8, 20, 36, 69, 104, 176, 1046, 1051, 1052, 1103, 1117, 1118, 1279]
set_option maxHeartbeats 10000000 in
private theorem h3_11 : good 3 w3_11 := by
  exact build (cs := [w2_4, w2_19, w2_33, w2_41, w2_53, w2_61, w2_70, w2_90, w2_91, w2_92, w2_93, w2_94, w2_95, w2_96, w2_97]) (ccons h2_4 (ccons h2_19 (ccons h2_33 (ccons h2_41 (ccons h2_53 (ccons h2_61 (ccons h2_70 (ccons h2_90 (ccons h2_91 (ccons h2_92 (ccons h2_93 (ccons h2_94 (ccons h2_95 (ccons h2_96 (ccons h2_97 (by simp)))))))))))))))) (by decide +kernel)
private def w3_12 : List T := [1, 2, 4, 16, 40, 76, 197, 688, 774, 1051, 1229, 1372, 1501, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_12 : good 3 w3_12 := by
  exact build (cs := [w2_5, w2_15, w2_20, w2_30, w2_42, w2_54, w2_61, w2_64, w2_97, w2_98, w2_99, w2_100, w2_101, w2_102, w2_103]) (ccons h2_5 (ccons h2_15 (ccons h2_20 (ccons h2_30 (ccons h2_42 (ccons h2_54 (ccons h2_61 (ccons h2_64 (ccons h2_97 (ccons h2_98 (ccons h2_99 (ccons h2_100 (ccons h2_101 (ccons h2_102 (ccons h2_103 (by simp)))))))))))))))) (by decide +kernel)
private def w3_13 : List T := [1, 2, 4, 8, 48, 69, 84, 262, 360, 1051, 1109, 1407]
set_option maxHeartbeats 10000000 in
private theorem h3_13 : good 3 w3_13 := by
  exact build (cs := [w2_3, w2_4, w2_8, w2_13, w2_14, w2_15, w2_23, w2_42, w2_69, w2_70, w2_76, w2_104]) (ccons h2_3 (ccons h2_4 (ccons h2_8 (ccons h2_13 (ccons h2_14 (ccons h2_15 (ccons h2_23 (ccons h2_42 (ccons h2_69 (ccons h2_70 (ccons h2_76 (ccons h2_104 (by simp))))))))))))) (by decide +kernel)
private def w3_14 : List T := [3, 6, 8, 16, 32, 84, 104, 176, 199, 1051, 1118, 1279]
set_option maxHeartbeats 10000000 in
private theorem h3_14 : good 3 w3_14 := by
  exact build (cs := [w2_0, w2_3, w2_9, w2_15, w2_31, w2_32, w2_35, w2_36, w2_55, w2_57, w2_80, w2_105, w2_106, w2_107, w2_108]) (ccons h2_0 (ccons h2_3 (ccons h2_9 (ccons h2_15 (ccons h2_31 (ccons h2_32 (ccons h2_35 (ccons h2_36 (ccons h2_55 (ccons h2_57 (ccons h2_80 (ccons h2_105 (ccons h2_106 (ccons h2_107 (ccons h2_108 (by simp)))))))))))))))) (by decide +kernel)
private def w3_15 : List T := [2, 4, 9, 24, 32, 205, 340, 360, 476, 688, 774, 1051, 1501, 1878, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_15 : good 3 w3_15 := by
  exact build (cs := [w2_1, w2_6, w2_17, w2_22, w2_31, w2_34, w2_39, w2_40, w2_41, w2_42, w2_44, w2_45, w2_47, w2_48, w2_49, w2_50, w2_51, w2_55, w2_109, w2_110, w2_111]) (ccons h2_1 (ccons h2_6 (ccons h2_17 (ccons h2_22 (ccons h2_31 (ccons h2_34 (ccons h2_39 (ccons h2_40 (ccons h2_41 (ccons h2_42 (ccons h2_44 (ccons h2_45 (ccons h2_47 (ccons h2_48 (ccons h2_49 (ccons h2_50 (ccons h2_51 (ccons h2_55 (ccons h2_109 (ccons h2_110 (ccons h2_111 (by simp)))))))))))))))))))))) (by decide +kernel)
private def w3_16 : List T := [2, 4, 8, 17, 32, 85, 176, 262, 360, 1051, 1117, 1359, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_16 : good 3 w3_16 := by
  exact build (cs := [w2_0, w2_1, w2_3, w2_4, w2_6, w2_7, w2_9, w2_10, w2_14, w2_17, w2_39, w2_42, w2_45, w2_65, w2_66, w2_67, w2_68]) (ccons h2_0 (ccons h2_1 (ccons h2_3 (ccons h2_4 (ccons h2_6 (ccons h2_7 (ccons h2_9 (ccons h2_10 (ccons h2_14 (ccons h2_17 (ccons h2_39 (ccons h2_42 (ccons h2_45 (ccons h2_65 (ccons h2_66 (ccons h2_67 (ccons h2_68 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_17 : List T := [1, 2, 4, 8, 16, 32, 104, 176, 229, 262, 1051, 1100, 1275, 1277, 1358, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_17 : good 3 w3_17 := by
  exact build (cs := [w2_3, w2_9, w2_19, w2_34, w2_40, w2_62, w2_70, w2_79, w2_112, w2_113, w2_114, w2_115, w2_116, w2_117]) (ccons h2_3 (ccons h2_9 (ccons h2_19 (ccons h2_34 (ccons h2_40 (ccons h2_62 (ccons h2_70 (ccons h2_79 (ccons h2_112 (ccons h2_113 (ccons h2_114 (ccons h2_115 (ccons h2_116 (ccons h2_117 (by simp))))))))))))))) (by decide +kernel)
private def w3_18 : List T := [2, 4, 9, 16, 32, 197, 361, 460, 688, 774, 997, 1004, 1051, 1501, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_18 : good 3 w3_18 := by
  exact build (cs := [w2_6, w2_22, w2_34, w2_42, w2_65, w2_71, w2_80, w2_90, w2_118, w2_119, w2_120, w2_121, w2_122, w2_123, w2_124, w2_125, w2_126, w2_127]) (ccons h2_6 (ccons h2_22 (ccons h2_34 (ccons h2_42 (ccons h2_65 (ccons h2_71 (ccons h2_80 (ccons h2_90 (ccons h2_118 (ccons h2_119 (ccons h2_120 (ccons h2_121 (ccons h2_122 (ccons h2_123 (ccons h2_124 (ccons h2_125 (ccons h2_126 (ccons h2_127 (by simp))))))))))))))))))) (by decide +kernel)
private def w3_19 : List T := [1, 4, 10, 16, 32, 76, 176, 197, 262, 362, 1051, 1116, 1245, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_19 : good 3 w3_19 := by
  exact build (cs := [w2_6, w2_7, w2_8, w2_21, w2_40, w2_52, w2_54, w2_72, w2_86, w2_91, w2_124, w2_128, w2_129, w2_130, w2_131, w2_132, w2_133, w2_134, w2_135]) (ccons h2_6 (ccons h2_7 (ccons h2_8 (ccons h2_21 (ccons h2_40 (ccons h2_52 (ccons h2_54 (ccons h2_72 (ccons h2_86 (ccons h2_91 (ccons h2_124 (ccons h2_128 (ccons h2_129 (ccons h2_130 (ccons h2_131 (ccons h2_132 (ccons h2_133 (ccons h2_134 (ccons h2_135 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_20 : List T := [1, 2, 4, 8, 16, 32, 176, 197, 262, 364, 1051, 1108, 1237, 1374, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_20 : good 3 w3_20 := by
  exact build (cs := [w2_7, w2_8, w2_22, w2_23, w2_35, w2_42, w2_54, w2_61, w2_75, w2_79, w2_90, w2_91, w2_126, w2_132, w2_136, w2_137]) (ccons h2_7 (ccons h2_8 (ccons h2_22 (ccons h2_23 (ccons h2_35 (ccons h2_42 (ccons h2_54 (ccons h2_61 (ccons h2_75 (ccons h2_79 (ccons h2_90 (ccons h2_91 (ccons h2_126 (ccons h2_132 (ccons h2_136 (ccons h2_137 (by simp))))))))))))))))) (by decide +kernel)
private def w3_21 : List T := [1, 2, 4, 24, 48, 69, 262, 380, 1051, 1407]
set_option maxHeartbeats 10000000 in
private theorem h3_21 : good 3 w3_21 := by
  exact build (cs := [w2_8, w2_23, w2_36, w2_42, w2_65, w2_112, w2_132, w2_136, w2_138, w2_139, w2_140, w2_141, w2_142]) (ccons h2_8 (ccons h2_23 (ccons h2_36 (ccons h2_42 (ccons h2_65 (ccons h2_112 (ccons h2_132 (ccons h2_136 (ccons h2_138 (ccons h2_139 (ccons h2_140 (ccons h2_141 (ccons h2_142 (by simp)))))))))))))) (by decide +kernel)
private def w3_22 : List T := [2, 4, 9, 16, 32, 176, 197, 262, 360, 493, 1051, 1535]
set_option maxHeartbeats 10000000 in
private theorem h3_22 : good 3 w3_22 := by
  exact build (cs := [w2_6, w2_22, w2_26, w2_34, w2_40, w2_42, w2_45, w2_46, w2_52, w2_62, w2_90, w2_106, w2_122, w2_125, w2_126, w2_127, w2_143, w2_144, w2_145]) (ccons h2_6 (ccons h2_22 (ccons h2_26 (ccons h2_34 (ccons h2_40 (ccons h2_42 (ccons h2_45 (ccons h2_46 (ccons h2_52 (ccons h2_62 (ccons h2_90 (ccons h2_106 (ccons h2_122 (ccons h2_125 (ccons h2_126 (ccons h2_127 (ccons h2_143 (ccons h2_144 (ccons h2_145 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_23 : List T := [2, 4, 8, 17, 32, 197, 360, 469, 689, 774, 1013, 1051, 1501, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_23 : good 3 w3_23 := by
  exact build (cs := [w2_9, w2_25, w2_42, w2_45, w2_82, w2_92, w2_127, w2_129, w2_146, w2_147, w2_148, w2_149, w2_150, w2_151]) (ccons h2_9 (ccons h2_25 (ccons h2_42 (ccons h2_45 (ccons h2_82 (ccons h2_92 (ccons h2_127 (ccons h2_129 (ccons h2_146 (ccons h2_147 (ccons h2_148 (ccons h2_149 (ccons h2_150 (ccons h2_151 (by simp))))))))))))))) (by decide +kernel)
private def w3_24 : List T := [1, 4, 8, 18, 32, 84, 197, 360, 690, 774, 854, 1051, 1116, 1245, 1779, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_24 : good 3 w3_24 := by
  exact build (cs := [w2_9, w2_24, w2_37, w2_43, w2_54, w2_57, w2_63, w2_69, w2_73, w2_93, w2_109, w2_119, w2_143, w2_152, w2_153, w2_154, w2_155]) (ccons h2_9 (ccons h2_24 (ccons h2_37 (ccons h2_43 (ccons h2_54 (ccons h2_57 (ccons h2_63 (ccons h2_69 (ccons h2_73 (ccons h2_93 (ccons h2_109 (ccons h2_119 (ccons h2_143 (ccons h2_152 (ccons h2_153 (ccons h2_154 (ccons h2_155 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_25 : List T := [1, 2, 8, 20, 32, 104, 197, 518, 692, 1036, 1051, 1116, 1245, 1550, 1558, 1630, 1759, 1775, 1783, 1787, 1789, 1790, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_25 : good 3 w3_25 := by
  exact build (cs := [w2_10, w2_25, w2_37, w2_44, w2_56, w2_64, w2_70, w2_74, w2_83, w2_107, w2_120, w2_130, w2_136, w2_144, w2_156, w2_157, w2_158, w2_159, w2_160]) (ccons h2_10 (ccons h2_25 (ccons h2_37 (ccons h2_44 (ccons h2_56 (ccons h2_64 (ccons h2_70 (ccons h2_74 (ccons h2_83 (ccons h2_107 (ccons h2_120 (ccons h2_130 (ccons h2_136 (ccons h2_144 (ccons h2_156 (ccons h2_157 (ccons h2_158 (ccons h2_159 (ccons h2_160 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_26 : List T := [1, 2, 4, 24, 40, 76, 197, 348, 696, 774, 1020, 1051, 1229, 1501, 1870, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_26 : good 3 w3_26 := by
  exact build (cs := [w2_11, w2_26, w2_38, w2_42, w2_45, w2_57, w2_64, w2_84, w2_121, w2_142, w2_161, w2_162, w2_163, w2_164, w2_165, w2_166, w2_167]) (ccons h2_11 (ccons h2_26 (ccons h2_38 (ccons h2_42 (ccons h2_45 (ccons h2_57 (ccons h2_64 (ccons h2_84 (ccons h2_121 (ccons h2_142 (ccons h2_161 (ccons h2_162 (ccons h2_163 (ccons h2_164 (ccons h2_165 (ccons h2_166 (ccons h2_167 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_27 : List T := [2, 4, 8, 17, 32, 197, 212, 360, 688, 757, 774, 1051, 1757, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_27 : good 3 w3_27 := by
  exact build (cs := [w2_3, w2_9, w2_19, w2_25, w2_34, w2_40, w2_62, w2_70, w2_90, w2_99, w2_110, w2_112, w2_147, w2_163, w2_168, w2_169, w2_170, w2_171, w2_172, w2_173]) (ccons h2_3 (ccons h2_9 (ccons h2_19 (ccons h2_25 (ccons h2_34 (ccons h2_40 (ccons h2_62 (ccons h2_70 (ccons h2_90 (ccons h2_99 (ccons h2_110 (ccons h2_112 (ccons h2_147 (ccons h2_163 (ccons h2_168 (ccons h2_169 (ccons h2_170 (ccons h2_171 (ccons h2_172 (ccons h2_173 (by simp))))))))))))))))))))) (by decide +kernel)
private def w3_28 : List T := [3, 5, 8, 16, 32, 262, 360, 688, 775, 1051, 1358, 1373, 1502, 1871, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_28 : good 3 w3_28 := by
  exact build (cs := [w2_0, w2_16, w2_46, w2_66, w2_75, w2_76, w2_77, w2_100, w2_108, w2_121, w2_139, w2_174, w2_175, w2_176, w2_177, w2_178, w2_179, w2_180, w2_181]) (ccons h2_0 (ccons h2_16 (ccons h2_46 (ccons h2_66 (ccons h2_75 (ccons h2_76 (ccons h2_77 (ccons h2_100 (ccons h2_108 (ccons h2_121 (ccons h2_139 (ccons h2_174 (ccons h2_175 (ccons h2_176 (ccons h2_177 (ccons h2_178 (ccons h2_179 (ccons h2_180 (ccons h2_181 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_29 : List T := [1, 4, 10, 16, 32, 197, 360, 688, 782, 1051, 1364, 1493, 1886, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_29 : good 3 w3_29 := by
  exact build (cs := [w2_12, w2_27, w2_32, w2_45, w2_46, w2_48, w2_53, w2_56, w2_58, w2_75, w2_102, w2_104, w2_115, w2_132, w2_166, w2_170, w2_182, w2_183, w2_184, w2_185]) (ccons h2_12 (ccons h2_27 (ccons h2_32 (ccons h2_45 (ccons h2_46 (ccons h2_48 (ccons h2_53 (ccons h2_56 (ccons h2_58 (ccons h2_75 (ccons h2_102 (ccons h2_104 (ccons h2_115 (ccons h2_132 (ccons h2_166 (ccons h2_170 (ccons h2_182 (ccons h2_183 (ccons h2_184 (ccons h2_185 (by simp))))))))))))))))))))) (by decide +kernel)
private def w3_30 : List T := [1, 4, 8, 18, 32, 197, 278, 360, 688, 1051, 1374, 1487, 1501, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_30 : good 3 w3_30 := by
  exact build (cs := [w2_0, w2_4, w2_10, w2_13, w2_14, w2_32, w2_47, w2_48, w2_66, w2_76, w2_91, w2_93, w2_101, w2_114, w2_122, w2_147, w2_164, w2_185, w2_186]) (ccons h2_0 (ccons h2_4 (ccons h2_10 (ccons h2_13 (ccons h2_14 (ccons h2_32 (ccons h2_47 (ccons h2_48 (ccons h2_66 (ccons h2_76 (ccons h2_91 (ccons h2_93 (ccons h2_101 (ccons h2_114 (ccons h2_122 (ccons h2_147 (ccons h2_164 (ccons h2_185 (ccons h2_186 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_31 : List T := [1, 2, 4, 8, 16, 32, 69, 262, 360, 560, 806, 1051, 1359, 1374, 1887, 1903, 1911, 1915, 1917, 1918, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_31 : good 3 w3_31 := by
  exact build (cs := [w2_13, w2_28, w2_33, w2_48, w2_67, w2_77, w2_102, w2_116, w2_123, w2_132, w2_145, w2_148, w2_153, w2_157, w2_165, w2_171, w2_187, w2_188, w2_189]) (ccons h2_13 (ccons h2_28 (ccons h2_33 (ccons h2_48 (ccons h2_67 (ccons h2_77 (ccons h2_102 (ccons h2_116 (ccons h2_123 (ccons h2_132 (ccons h2_145 (ccons h2_148 (ccons h2_153 (ccons h2_157 (ccons h2_165 (ccons h2_171 (ccons h2_187 (ccons h2_188 (ccons h2_189 (by simp)))))))))))))))))))) (by decide +kernel)
private def w3_32 : List T := [1, 4, 10, 16, 32, 69, 332, 360, 688, 774, 878, 1051, 1373, 1887, 1903, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_32 : good 3 w3_32 := by
  exact build (cs := [w2_7, w2_8, w2_29, w2_48, w2_52, w2_54, w2_91, w2_112, w2_124, w2_140, w2_149, w2_158, w2_176, w2_179, w2_188, w2_190, w2_191]) (ccons h2_7 (ccons h2_8 (ccons h2_29 (ccons h2_48 (ccons h2_52 (ccons h2_54 (ccons h2_91 (ccons h2_112 (ccons h2_124 (ccons h2_140 (ccons h2_149 (ccons h2_158 (ccons h2_176 (ccons h2_179 (ccons h2_188 (ccons h2_190 (ccons h2_191 (by simp)))))))))))))))))) (by decide +kernel)
private def w3_33 : List T := [1, 4, 8, 18, 32, 197, 360, 404, 688, 774, 950, 1051, 1501, 2047]
set_option maxHeartbeats 10000000 in
private theorem h3_33 : good 3 w3_33 := by
  exact build (cs := [w2_13, w2_28, w2_37, w2_49, w2_67, w2_78, w2_96, w2_103, w2_117, w2_125, w2_137, w2_140, w2_148, w2_150, w2_166, w2_172, w2_192, w2_193, w2_194, w2_195, w2_196]) (ccons h2_13 (ccons h2_28 (ccons h2_37 (ccons h2_49 (ccons h2_67 (ccons h2_78 (ccons h2_96 (ccons h2_103 (ccons h2_117 (ccons h2_125 (ccons h2_137 (ccons h2_140 (ccons h2_148 (ccons h2_150 (ccons h2_166 (ccons h2_172 (ccons h2_192 (ccons h2_193 (ccons h2_194 (ccons h2_195 (ccons h2_196 (by simp)))))))))))))))))))))) (by decide +kernel)
private def w3_34 : List T := [5, 6, 8, 16, 32, 104, 176, 228, 1055, 1279]
set_option maxHeartbeats 10000000 in
private theorem h3_34 : good 3 w3_34 := by
  exact build (cs := [w2_14, w2_50, w2_58, w2_74, w2_97, w2_108, w2_126, w2_141, w2_151, w2_167, w2_187, w2_191, w2_194]) (ccons h2_14 (ccons h2_50 (ccons h2_58 (ccons h2_74 (ccons h2_97 (ccons h2_108 (ccons h2_126 (ccons h2_141 (ccons h2_151 (ccons h2_167 (ccons h2_187 (ccons h2_191 (ccons h2_194 (by simp)))))))))))))) (by decide +kernel)
private def w3_35 : List T := [1, 2, 4, 40, 48, 69, 262, 1083, 1407]
set_option maxHeartbeats 10000000 in
private theorem h3_35 : good 3 w3_35 := by
  exact build (cs := [w2_15, w2_30, w2_97, w2_127, w2_135, w2_142, w2_155, w2_159, w2_173, w2_181, w2_197, w2_198, w2_199, w2_200]) (ccons h2_15 (ccons h2_30 (ccons h2_97 (ccons h2_127 (ccons h2_135 (ccons h2_142 (ccons h2_155 (ccons h2_159 (ccons h2_173 (ccons h2_181 (ccons h2_197 (ccons h2_198 (ccons h2_199 (ccons h2_200 (by simp))))))))))))))) (by decide +kernel)
private def w4_0 : List T := [1, 2, 4, 8, 16, 32, 197, 360, 688, 774, 1051, 1492, 2047]
set_option maxHeartbeats 10000000 in
private theorem h4_0 : good 4 w4_0 := by
  exact build (cs := [w3_0, w3_1, w3_2, w3_3, w3_4, w3_5, w3_6, w3_7, w3_8, w3_9, w3_10, w3_11, w3_12, w3_13, w3_14, w3_15, w3_16, w3_17, w3_18, w3_19, w3_20, w3_21, w3_22, w3_23, w3_24, w3_25, w3_26, w3_27, w3_28, w3_29, w3_30, w3_31, w3_32, w3_33, w3_34, w3_35]) (ccons h3_0 (ccons h3_1 (ccons h3_2 (ccons h3_3 (ccons h3_4 (ccons h3_5 (ccons h3_6 (ccons h3_7 (ccons h3_8 (ccons h3_9 (ccons h3_10 (ccons h3_11 (ccons h3_12 (ccons h3_13 (ccons h3_14 (ccons h3_15 (ccons h3_16 (ccons h3_17 (ccons h3_18 (ccons h3_19 (ccons h3_20 (ccons h3_21 (ccons h3_22 (ccons h3_23 (ccons h3_24 (ccons h3_25 (ccons h3_26 (ccons h3_27 (ccons h3_28 (ccons h3_29 (ccons h3_30 (ccons h3_31 (ccons h3_32 (ccons h3_33 (ccons h3_34 (ccons h3_35 (by simp))))))))))))))))))))))))))))))))))))) (by decide +kernel)
private def bit (k : Fin 11) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 11) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private def paid (g : Gate) : Bool := match g.op with
  | .or => true
  | _ => false

private theorem gate_table {n s} (hs : good n s) (w : List T)
    (hw : ∀ x ∈ w, cov s x = true) (g : Gate) (hg : legal g) :
    ∃ a b, cov s a = true ∧ cov s b = true ∧
      ∀ k, step (w.map (bit k)) g =
        (w ++ [if paid g then a ||| b else a &&& b]).map (bit k) := by
  have H := base hs
  simp only [basic, Bool.and_eq_true] at H
  have mem (i : ℕ) : cov s (w.getD i 0) := by
    by_cases h : i < w.length
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using hw w[i] (by simp)
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)] using H.1.1.2
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨2047,2047,H.1.2,H.1.2,by simp [paid,step,GateOp.eval,bit]; decide⟩
    · exact ⟨0,0,H.1.1.2,H.1.1.2,by simp [paid,step,GateOp.eval,bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      refine ⟨_,_,mem i,mem i,?_⟩
      rcases hop with rfl | rfl <;> simp only [step, List.map_cons, List.map_nil, read_bit] <;> simp [paid, GateOp.eval]
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        refine ⟨_,_,mem i,mem j,?_⟩
        rcases hop with rfl | rfl <;> simp only [step, List.map_cons, List.map_nil, read_bit] <;> simp [paid, GateOp.eval, bit]

private theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w s : List T) (hw : ∀ x ∈ w, cov s x = true) (n : ℕ)
    (hs : good n s) (cost : gs.countP paid ≤ n)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) : False := by
  have H := base hs
  simp only [basic, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at H
  induction gs generalizing w s n with
  | nil =>
    have hval : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have ht : cov s (w.getD out 0) := by
      by_cases h : out < w.length
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using hw w[out] (by simp)
      · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)] using H.1.1.2
    rw [hval,H.1.1.1] at ht
    contradiction
  | cons g gs ih =>
    obtain ⟨a,b,ha,hb,hstep⟩ := gate_table hs w hw g (hg g (by simp))
    obtain ⟨x,hx,hax⟩ := List.any_eq_true.mp ha
    obtain ⟨y,hy,hby⟩ := List.any_eq_true.mp hb
    let z := if paid g then a ||| b else a &&& b
    have nextval (k) : (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k target := by
      simpa only [List.foldl_cons, hstep,z] using he k
    have tailLegal : ∀ u ∈ gs, legal u := fun u hu => hg u (by simp [hu])
    by_cases hp : paid g
    · cases n with
      | zero => simp [hp] at cost
      | succ n =>
        obtain ⟨t,ht,hinc,hor⟩ := hs.2 x hx y hy
        refine ih tailLegal (w ++ [z]) t ?_ n ht (by simpa [hp] using cost) nextval ?_
        · intro v hv
          rcases List.mem_append.mp hv with hv | hv
          · obtain ⟨r,hr,hvr⟩ := List.any_eq_true.mp (hw v hv)
            exact cmono hvr (hinc r hr)
          · obtain rfl := List.mem_singleton.mp hv
            simpa [z,hp] using cmono (dops hax hby).2 hor
        · have hb' := base ht
          simpa only [basic, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] using hb'
    · refine ih tailLegal (w ++ [z]) s ?_ n hs (by simpa [hp] using cost) nextval ?_
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hw v hv
        · obtain rfl := List.mem_singleton.mp hv
          simpa [z,hp] using cmono (dops hax hby).1 (H.2 x hx y hy)
      · exact H

private theorem count (gs : List Gate) (A : Finset ℕ) (off : ℕ)
    (h : ∀ j g, gs[j]? = some g → g.op = .or → off+j ∈ A) :
    gs.countP paid ≤ A.card := by
  induction gs generalizing off A with
  | nil => simp
  | cons g gs ih =>
    have tailH (j u) (hu : gs[j]? = some u) (hop : u.op = .or) : off+1+j ∈ A := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using h (j+1) u (by simpa using hu) hop
    cases hp : paid g
    · simpa [hp] using ih A (off+1) tailH
    · have ho : g.op = .or := by cases he : g.op <;> simp_all [paid]
      have hm : off ∈ A := by simpa using h 0 g (by simp) ho
      have q := ih (A.erase off) (off+1) (fun j u hu hop =>
        Finset.mem_erase.mpr ⟨by omega,tailH j u hu hop⟩)
      rw [Finset.card_erase_of_mem hm] at q
      have := Finset.card_pos.mpr ⟨_,hm⟩
      simp [hp]
      omega

private def assignment (k : Fin 11) (i : Fin 5) := bit k (ins.getD i.val 0)

end PEqualNP.Outside.L_meta_597_aux

open PEqualNP.Outside.L_meta_597_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_597 :
∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → ∀ A : Finset ℕ, (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) → 5 ≤ A.card
 := by
  intro C hm he A ha
  by_contra! hcard
  have hcost := count C.gates A 0 (by simpa using ha)
  apply exclude C.gates C.output (fun g hg => hm g hg) ins w4_0 (by decide) 4 h4_0 (by omega)
  intro k
  have hi : ∀ t, List.ofFn (assignment t) = ins.map (bit t) := by decide
  have hx := he (assignment k)
  have ht : ∀ t, (bit t target = true ↔ ∃ u v : Fin 5,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)] : List (ℕ × ℕ)) ∧
      assignment t u = true ∧ assignment t v = true) := by decide
  have eq := Bool.eq_iff_iff.mpr (hx.trans (ht k).symm)
  unfold PEqualNP.Outside.L_meta_597_aux.step
  simpa only [Circuit.eval,Circuit.wires,hi] using eq

