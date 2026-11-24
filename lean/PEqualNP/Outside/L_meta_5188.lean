import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5188_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire semantics, as in the accepted project proofs.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_pre (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_pre gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_pre gs w
  rw [ht, List.getD_append _ _ _ _ h]

-- The value of gate number k of a gate list appended after the wires W.
theorem qGate (gs : List Gate) : ∀ (W : List Bool) (k : ℕ) (g : Gate), gs[k]? = some g →
    (∀ i ∈ g.inputs, i < W.length + k) →
    (wiresFrom gs W).getD (W.length + k) false =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs W).getD i false) := by
  induction gs with
  | nil => intro W k g hg; simp at hg
  | cons g0 gs ih =>
    intro W k g hg hin
    have hstep : wiresFrom (g0 :: gs) W =
        wiresFrom gs (W ++ [g0.op.eval (g0.inputs.map fun i => W.getD i false)]) := rfl
    rw [hstep]
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      have hin' : ∀ i ∈ g0.inputs, i < W.length := by simpa using hin
      generalize hv : g0.op.eval (g0.inputs.map fun i => W.getD i false) = v
      have hmap : g0.inputs.map (fun i => (wiresFrom gs (W ++ [v])).getD i false) =
          g0.inputs.map (fun i => W.getD i false) := by
        apply List.map_congr_left
        intro i hi
        have h1 := hin' i hi
        rw [getD_wiresFrom gs (W ++ [v]) i (by simp; omega)]
        exact List.getD_append _ _ _ _ h1
      rw [hmap, hv, getD_wiresFrom gs (W ++ [v]) (W.length + 0) (by simp)]
      simp
    · simp only [List.getElem?_cons_succ] at hg
      have h := ih (W ++ [g0.op.eval (g0.inputs.map fun i => W.getD i false)]) k g hg
        (by intro i hi; have := hin i hi; simp; omega)
      rw [List.length_append, List.length_singleton] at h
      rw [show W.length + (k + 1) = W.length + 1 + k by omega]
      exact h

-- The 32 incident pairs (point, line) with line at least 5.
def qLines : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12]

def qDs : List ℕ := [0, 1, 3, 9]

def qPairs : List (ℕ × ℕ) := qLines.flatMap (fun l => qDs.map (fun d => ((l + d) % 13, l)))

def qStar (y : ℕ → Bool) : Bool :=
  qLines.any (fun l => y (13 + l) && qDs.any (fun d => y ((l + d) % 13)))

set_option maxRecDepth 100000 in
theorem qPairIff : ∀ a b : Fin 13,
    ((5 : ℕ) ≤ (b : ℕ) ∧ a - b ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ↔
      ((a : ℕ), (b : ℕ)) ∈ qPairs := by
  decide

theorem qPairBound : ∀ p ∈ qPairs, p.1 < 13 ∧ p.2 < 13 := by
  decide

theorem qAnyAnd (b : Bool) (l : List ℕ) (f : ℕ → Bool) :
    l.any (fun d => f d && b) = (b && l.any f) := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.any_cons, List.any_cons, ih]; cases b <;> simp

theorem qPairAny (y : ℕ → Bool) : qPairs.any (fun p => y p.1 && y (13 + p.2)) = qStar y := by
  unfold qPairs qStar
  rw [List.any_flatMap]
  congr 1
  funext l
  rw [List.any_map]
  exact qAnyAnd (y (13 + l)) qDs (fun d => y ((l + d) % 13))

theorem qSpecCore (y : ℕ → Bool) :
    (∃ (x7 : Fin 13) (x8 : Fin 13), (5 : ℕ) ≤ (x8 : ℕ) ∧
      x7 - x8 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      y (x7 : ℕ) = true ∧ y (13 + (x8 : ℕ)) = true) ↔ qStar y = true := by
  rw [← qPairAny, List.any_eq_true]
  constructor
  · rintro ⟨a, b, h5, hs, ha, hb⟩
    refine ⟨((a : ℕ), (b : ℕ)), (qPairIff a b).1 ⟨h5, hs⟩, ?_⟩
    simp [ha, hb]
  · rintro ⟨p, hp, hv⟩
    obtain ⟨h1, h2⟩ := qPairBound p hp
    have hpair := (qPairIff ⟨p.1, h1⟩ ⟨p.2, h2⟩).2 hp
    simp only [Bool.and_eq_true] at hv
    exact ⟨⟨p.1, h1⟩, ⟨p.2, h2⟩, hpair.1, hpair.2, hv.1, hv.2⟩

theorem qOfFn (x6 : Fin 26 → Bool) (i : Fin 26) : (List.ofFn x6).getD i.val false = x6 i := by
  have h : i.val < (List.ofFn x6).length := by simp
  exact (List.getD_eq_getElem _ _ h).trans (List.getElem_ofFn h)

theorem qSpecIff (x6 : Fin 26 → Bool) :
    (∃ (x7 : Fin 13) (x8 : Fin 13), (5 : ℕ) ≤ (x8 : ℕ) ∧
      x7 - x8 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
      x6 (Fin.castAdd 13 x7) = true ∧ x6 (Fin.natAdd 13 x8) = true) ↔
      qStar (fun i => (List.ofFn x6).getD i false) = true := by
  have hc : ∀ x7 : Fin 13, x6 (Fin.castAdd 13 x7) = (List.ofFn x6).getD (x7 : ℕ) false :=
    fun x7 => (qOfFn x6 (Fin.castAdd 13 x7)).symm
  have hn : ∀ x8 : Fin 13, x6 (Fin.natAdd 13 x8) = (List.ofFn x6).getD (13 + (x8 : ℕ)) false :=
    fun x8 => (qOfFn x6 (Fin.natAdd 13 x8)).symm
  simp only [hc, hn]
  exact qSpecCore (fun i => (List.ofFn x6).getD i false)

-- The 40 appended gates: eight line stars, an OR chain, and the final OR.
def qExtra (m out : ℕ) : List Gate :=
  [⟨GateOp.or, [8, 1]⟩,
    ⟨GateOp.or, [6, m + 0]⟩,
    ⟨GateOp.or, [5, m + 1]⟩,
    ⟨GateOp.and, [18, m + 2]⟩,
    ⟨GateOp.or, [9, 2]⟩,
    ⟨GateOp.or, [7, m + 4]⟩,
    ⟨GateOp.or, [6, m + 5]⟩,
    ⟨GateOp.and, [19, m + 6]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.or, [8, m + 8]⟩,
    ⟨GateOp.or, [7, m + 9]⟩,
    ⟨GateOp.and, [20, m + 10]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.or, [9, m + 12]⟩,
    ⟨GateOp.or, [8, m + 13]⟩,
    ⟨GateOp.and, [21, m + 14]⟩,
    ⟨GateOp.or, [12, 5]⟩,
    ⟨GateOp.or, [10, m + 16]⟩,
    ⟨GateOp.or, [9, m + 17]⟩,
    ⟨GateOp.and, [22, m + 18]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [11, m + 20]⟩,
    ⟨GateOp.or, [10, m + 21]⟩,
    ⟨GateOp.and, [23, m + 22]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [12, m + 24]⟩,
    ⟨GateOp.or, [11, m + 25]⟩,
    ⟨GateOp.and, [24, m + 26]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [0, m + 28]⟩,
    ⟨GateOp.or, [12, m + 29]⟩,
    ⟨GateOp.and, [25, m + 30]⟩,
    ⟨GateOp.or, [m + 27, m + 31]⟩,
    ⟨GateOp.or, [m + 23, m + 32]⟩,
    ⟨GateOp.or, [m + 19, m + 33]⟩,
    ⟨GateOp.or, [m + 15, m + 34]⟩,
    ⟨GateOp.or, [m + 11, m + 35]⟩,
    ⟨GateOp.or, [m + 7, m + 36]⟩,
    ⟨GateOp.or, [m + 3, m + 37]⟩,
    ⟨GateOp.or, [out, m + 38]⟩]

theorem qExtraVal (W : List Bool) (out : ℕ) (y : ℕ → Bool) (hout : out < W.length)
    (h26 : 26 ≤ W.length) (hin : ∀ i, i < 26 → W.getD i false = y i) :
    (wiresFrom (qExtra W.length out) W).getD (W.length + 39) false = (W.getD out false || qStar y) := by
  have e0 : (wiresFrom (qExtra W.length out) W).getD (W.length + 0) false = ((wiresFrom (qExtra W.length out) W).getD 8 false || (wiresFrom (qExtra W.length out) W).getD 1 false) := by
    rw [qGate (qExtra W.length out) W 0 ⟨GateOp.or, [8, 1]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e1 : (wiresFrom (qExtra W.length out) W).getD (W.length + 1) false = ((wiresFrom (qExtra W.length out) W).getD 6 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 0) false) := by
    rw [qGate (qExtra W.length out) W 1 ⟨GateOp.or, [6, W.length + 0]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e2 : (wiresFrom (qExtra W.length out) W).getD (W.length + 2) false = ((wiresFrom (qExtra W.length out) W).getD 5 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 1) false) := by
    rw [qGate (qExtra W.length out) W 2 ⟨GateOp.or, [5, W.length + 1]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e3 : (wiresFrom (qExtra W.length out) W).getD (W.length + 3) false = ((wiresFrom (qExtra W.length out) W).getD 18 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 2) false) := by
    rw [qGate (qExtra W.length out) W 3 ⟨GateOp.and, [18, W.length + 2]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e4 : (wiresFrom (qExtra W.length out) W).getD (W.length + 4) false = ((wiresFrom (qExtra W.length out) W).getD 9 false || (wiresFrom (qExtra W.length out) W).getD 2 false) := by
    rw [qGate (qExtra W.length out) W 4 ⟨GateOp.or, [9, 2]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e5 : (wiresFrom (qExtra W.length out) W).getD (W.length + 5) false = ((wiresFrom (qExtra W.length out) W).getD 7 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 4) false) := by
    rw [qGate (qExtra W.length out) W 5 ⟨GateOp.or, [7, W.length + 4]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e6 : (wiresFrom (qExtra W.length out) W).getD (W.length + 6) false = ((wiresFrom (qExtra W.length out) W).getD 6 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 5) false) := by
    rw [qGate (qExtra W.length out) W 6 ⟨GateOp.or, [6, W.length + 5]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e7 : (wiresFrom (qExtra W.length out) W).getD (W.length + 7) false = ((wiresFrom (qExtra W.length out) W).getD 19 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 6) false) := by
    rw [qGate (qExtra W.length out) W 7 ⟨GateOp.and, [19, W.length + 6]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e8 : (wiresFrom (qExtra W.length out) W).getD (W.length + 8) false = ((wiresFrom (qExtra W.length out) W).getD 10 false || (wiresFrom (qExtra W.length out) W).getD 3 false) := by
    rw [qGate (qExtra W.length out) W 8 ⟨GateOp.or, [10, 3]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e9 : (wiresFrom (qExtra W.length out) W).getD (W.length + 9) false = ((wiresFrom (qExtra W.length out) W).getD 8 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 8) false) := by
    rw [qGate (qExtra W.length out) W 9 ⟨GateOp.or, [8, W.length + 8]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e10 : (wiresFrom (qExtra W.length out) W).getD (W.length + 10) false = ((wiresFrom (qExtra W.length out) W).getD 7 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 9) false) := by
    rw [qGate (qExtra W.length out) W 10 ⟨GateOp.or, [7, W.length + 9]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e11 : (wiresFrom (qExtra W.length out) W).getD (W.length + 11) false = ((wiresFrom (qExtra W.length out) W).getD 20 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 10) false) := by
    rw [qGate (qExtra W.length out) W 11 ⟨GateOp.and, [20, W.length + 10]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e12 : (wiresFrom (qExtra W.length out) W).getD (W.length + 12) false = ((wiresFrom (qExtra W.length out) W).getD 11 false || (wiresFrom (qExtra W.length out) W).getD 4 false) := by
    rw [qGate (qExtra W.length out) W 12 ⟨GateOp.or, [11, 4]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e13 : (wiresFrom (qExtra W.length out) W).getD (W.length + 13) false = ((wiresFrom (qExtra W.length out) W).getD 9 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 12) false) := by
    rw [qGate (qExtra W.length out) W 13 ⟨GateOp.or, [9, W.length + 12]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e14 : (wiresFrom (qExtra W.length out) W).getD (W.length + 14) false = ((wiresFrom (qExtra W.length out) W).getD 8 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 13) false) := by
    rw [qGate (qExtra W.length out) W 14 ⟨GateOp.or, [8, W.length + 13]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e15 : (wiresFrom (qExtra W.length out) W).getD (W.length + 15) false = ((wiresFrom (qExtra W.length out) W).getD 21 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 14) false) := by
    rw [qGate (qExtra W.length out) W 15 ⟨GateOp.and, [21, W.length + 14]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e16 : (wiresFrom (qExtra W.length out) W).getD (W.length + 16) false = ((wiresFrom (qExtra W.length out) W).getD 12 false || (wiresFrom (qExtra W.length out) W).getD 5 false) := by
    rw [qGate (qExtra W.length out) W 16 ⟨GateOp.or, [12, 5]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e17 : (wiresFrom (qExtra W.length out) W).getD (W.length + 17) false = ((wiresFrom (qExtra W.length out) W).getD 10 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 16) false) := by
    rw [qGate (qExtra W.length out) W 17 ⟨GateOp.or, [10, W.length + 16]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e18 : (wiresFrom (qExtra W.length out) W).getD (W.length + 18) false = ((wiresFrom (qExtra W.length out) W).getD 9 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 17) false) := by
    rw [qGate (qExtra W.length out) W 18 ⟨GateOp.or, [9, W.length + 17]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e19 : (wiresFrom (qExtra W.length out) W).getD (W.length + 19) false = ((wiresFrom (qExtra W.length out) W).getD 22 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 18) false) := by
    rw [qGate (qExtra W.length out) W 19 ⟨GateOp.and, [22, W.length + 18]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e20 : (wiresFrom (qExtra W.length out) W).getD (W.length + 20) false = ((wiresFrom (qExtra W.length out) W).getD 0 false || (wiresFrom (qExtra W.length out) W).getD 6 false) := by
    rw [qGate (qExtra W.length out) W 20 ⟨GateOp.or, [0, 6]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e21 : (wiresFrom (qExtra W.length out) W).getD (W.length + 21) false = ((wiresFrom (qExtra W.length out) W).getD 11 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 20) false) := by
    rw [qGate (qExtra W.length out) W 21 ⟨GateOp.or, [11, W.length + 20]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e22 : (wiresFrom (qExtra W.length out) W).getD (W.length + 22) false = ((wiresFrom (qExtra W.length out) W).getD 10 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 21) false) := by
    rw [qGate (qExtra W.length out) W 22 ⟨GateOp.or, [10, W.length + 21]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e23 : (wiresFrom (qExtra W.length out) W).getD (W.length + 23) false = ((wiresFrom (qExtra W.length out) W).getD 23 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 22) false) := by
    rw [qGate (qExtra W.length out) W 23 ⟨GateOp.and, [23, W.length + 22]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e24 : (wiresFrom (qExtra W.length out) W).getD (W.length + 24) false = ((wiresFrom (qExtra W.length out) W).getD 1 false || (wiresFrom (qExtra W.length out) W).getD 7 false) := by
    rw [qGate (qExtra W.length out) W 24 ⟨GateOp.or, [1, 7]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e25 : (wiresFrom (qExtra W.length out) W).getD (W.length + 25) false = ((wiresFrom (qExtra W.length out) W).getD 12 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 24) false) := by
    rw [qGate (qExtra W.length out) W 25 ⟨GateOp.or, [12, W.length + 24]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e26 : (wiresFrom (qExtra W.length out) W).getD (W.length + 26) false = ((wiresFrom (qExtra W.length out) W).getD 11 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 25) false) := by
    rw [qGate (qExtra W.length out) W 26 ⟨GateOp.or, [11, W.length + 25]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e27 : (wiresFrom (qExtra W.length out) W).getD (W.length + 27) false = ((wiresFrom (qExtra W.length out) W).getD 24 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 26) false) := by
    rw [qGate (qExtra W.length out) W 27 ⟨GateOp.and, [24, W.length + 26]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e28 : (wiresFrom (qExtra W.length out) W).getD (W.length + 28) false = ((wiresFrom (qExtra W.length out) W).getD 2 false || (wiresFrom (qExtra W.length out) W).getD 8 false) := by
    rw [qGate (qExtra W.length out) W 28 ⟨GateOp.or, [2, 8]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e29 : (wiresFrom (qExtra W.length out) W).getD (W.length + 29) false = ((wiresFrom (qExtra W.length out) W).getD 0 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 28) false) := by
    rw [qGate (qExtra W.length out) W 29 ⟨GateOp.or, [0, W.length + 28]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e30 : (wiresFrom (qExtra W.length out) W).getD (W.length + 30) false = ((wiresFrom (qExtra W.length out) W).getD 12 false || (wiresFrom (qExtra W.length out) W).getD (W.length + 29) false) := by
    rw [qGate (qExtra W.length out) W 30 ⟨GateOp.or, [12, W.length + 29]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e31 : (wiresFrom (qExtra W.length out) W).getD (W.length + 31) false = ((wiresFrom (qExtra W.length out) W).getD 25 false && (wiresFrom (qExtra W.length out) W).getD (W.length + 30) false) := by
    rw [qGate (qExtra W.length out) W 31 ⟨GateOp.and, [25, W.length + 30]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
  have e32 : (wiresFrom (qExtra W.length out) W).getD (W.length + 32) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 27) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 31) false) := by
    rw [qGate (qExtra W.length out) W 32 ⟨GateOp.or, [W.length + 27, W.length + 31]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e33 : (wiresFrom (qExtra W.length out) W).getD (W.length + 33) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 23) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 32) false) := by
    rw [qGate (qExtra W.length out) W 33 ⟨GateOp.or, [W.length + 23, W.length + 32]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e34 : (wiresFrom (qExtra W.length out) W).getD (W.length + 34) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 19) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 33) false) := by
    rw [qGate (qExtra W.length out) W 34 ⟨GateOp.or, [W.length + 19, W.length + 33]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e35 : (wiresFrom (qExtra W.length out) W).getD (W.length + 35) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 15) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 34) false) := by
    rw [qGate (qExtra W.length out) W 35 ⟨GateOp.or, [W.length + 15, W.length + 34]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e36 : (wiresFrom (qExtra W.length out) W).getD (W.length + 36) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 11) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 35) false) := by
    rw [qGate (qExtra W.length out) W 36 ⟨GateOp.or, [W.length + 11, W.length + 35]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e37 : (wiresFrom (qExtra W.length out) W).getD (W.length + 37) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 7) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 36) false) := by
    rw [qGate (qExtra W.length out) W 37 ⟨GateOp.or, [W.length + 7, W.length + 36]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e38 : (wiresFrom (qExtra W.length out) W).getD (W.length + 38) false = ((wiresFrom (qExtra W.length out) W).getD (W.length + 3) false || (wiresFrom (qExtra W.length out) W).getD (W.length + 37) false) := by
    rw [qGate (qExtra W.length out) W 38 ⟨GateOp.or, [W.length + 3, W.length + 37]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have e39 : (wiresFrom (qExtra W.length out) W).getD (W.length + 39) false = ((wiresFrom (qExtra W.length out) W).getD out false || (wiresFrom (qExtra W.length out) W).getD (W.length + 38) false) := by
    rw [qGate (qExtra W.length out) W 39 ⟨GateOp.or, [out, W.length + 38]⟩ rfl
      (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega)]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
  have hlow : ∀ i, i < 26 → (wiresFrom (qExtra W.length out) W).getD i false = y i :=
    fun i hi => (getD_wiresFrom _ _ _ (by omega)).trans (hin i hi)
  rw [e39, getD_wiresFrom _ _ _ hout, e38, e37, e36, e35, e34, e33, e32, e31, e30, e29, e28, e27, e26, e25, e24, e23, e22, e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0]
  simp only [hlow 0 (by norm_num), hlow 1 (by norm_num), hlow 2 (by norm_num), hlow 3 (by norm_num), hlow 4 (by norm_num), hlow 5 (by norm_num), hlow 6 (by norm_num), hlow 7 (by norm_num), hlow 8 (by norm_num), hlow 9 (by norm_num), hlow 10 (by norm_num), hlow 11 (by norm_num), hlow 12 (by norm_num), hlow 18 (by norm_num), hlow 19 (by norm_num), hlow 20 (by norm_num), hlow 21 (by norm_num), hlow 22 (by norm_num), hlow 23 (by norm_num), hlow 24 (by norm_num), hlow 25 (by norm_num)]
  simp only [qStar, qLines, qDs, List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd,
    Nat.reduceMod]

theorem qExtraMono (m out : ℕ) : ∀ g ∈ qExtra m out,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [qExtra]

theorem qExtraLen (m out : ℕ) : (qExtra m out).length = 40 := rfl

end PEqualNP.Outside.L_meta_5188_aux

open PEqualNP.Outside.L_meta_5188_aux in
theorem PEqualNP.Outside.L_meta_5188 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.output < (26 : ℕ) + x2.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size + (40 : ℕ) ∧ ∀ (x6 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 x6 = (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x6 || Decidable.decide (∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (5 : ℕ) ≤ ↑x8 ∧ x7 - x8 ∈ x1 ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true)) := by
  dsimp only
  intro C hmono hout
  refine ⟨⟨C.gates ++ qExtra (26 + C.size) C.output, 26 + C.size + 39⟩, ?_, ?_, ?_⟩
  · show ∀ g ∈ C.gates ++ qExtra (26 + C.size) C.output, _
    intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hmono g h
    · exact qExtraMono _ _ g h
  · show (C.gates ++ qExtra (26 + C.size) C.output).length ≤ C.gates.length + 40
    exact le_of_eq (by rw [List.length_append, qExtraLen])
  · intro x6
    show (wiresFrom (C.gates ++ qExtra (26 + C.size) C.output) (List.ofFn x6)).getD
        (26 + C.size + 39) false = ((wiresFrom C.gates (List.ofFn x6)).getD C.output false || _)
    have hW : (wiresFrom C.gates (List.ofFn x6)).length = 26 + C.size := by
      simp only [length_wiresFrom, List.length_ofFn, PEqualNP.CircuitLowerBounds.Circuit.size]
    rw [wiresFrom_append, ← hW]
    rw [qExtraVal (wiresFrom C.gates (List.ofFn x6)) C.output (fun i => (List.ofFn x6).getD i false)
      (by omega) (by omega) (fun i hi => getD_wiresFrom _ _ _ (by simpa using hi))]
    congr 1
    exact Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact (qSpecIff x6).symm)
