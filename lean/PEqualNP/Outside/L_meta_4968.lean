import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4968_aux

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dfltGate : Gate := ⟨GateOp.and, []⟩

lemma getD_append_singleton : ∀ (w : List Bool) (v : Bool), (w ++ [v]).getD w.length false = v
  | [], v => by simp
  | x :: t, v => by
    rw [List.cons_append, List.length_cons, List.getD_cons_succ]
    exact getD_append_singleton t v

lemma wstep_length (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  rw [wstep]
  exact List.getD_append w _ false i h

lemma wstep_getD_self (w : List Bool) (g : Gate) :
    (wstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [wstep]
  exact getD_append_singleton w _

lemma foldl_length (l : List Gate) (w : List Bool) :
    (l.foldl wstep w).length = w.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons g0 t ih =>
    rw [List.foldl_cons, ih (w := wstep w g0), wstep_length, List.length_cons]
    omega

lemma foldl_getD_lt (l : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (l.foldl wstep w).getD i false = w.getD i false := by
  induction l generalizing w with
  | nil => simp
  | cons g0 t ih =>
    rw [List.foldl_cons]
    refine (ih (w := wstep w g0) ?_).trans (wstep_getD_lt w g0 h)
    rw [wstep_length]
    omega

lemma wires_eq_fold (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

lemma wires_length (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  rw [wires_eq_fold, foldl_length]
  rfl

lemma wires_getD_input (C : Circuit) (x : List Bool) {i : ℕ} (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq_fold]
  exact foldl_getD_lt C.gates x h

lemma and_eval_pair (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

lemma or_eval_pair (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

lemma ofFn_getD {n : ℕ} (f : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

lemma ofFn_gate_getD {n : ℕ} (gs : Fin n → Gate) {i : ℕ} (hi : i < n) :
    (List.ofFn gs).getD i dfltGate = gs ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

lemma ofFn_apply {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i :=
  ofFn_getD f i.isLt

def andGates (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ) : List Gate :=
  List.ofFn fun i : Fin (x2 + 1) => ⟨GateOp.and, [x4 i, x5 i]⟩

def termVals (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ)
    (w : List Bool) : List Bool :=
  List.ofFn fun i : Fin (x2 + 1) => w.getD (x4 i) false && w.getD (x5 i) false

def prevW (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) : ℕ :=
  if k = 0 then x1 + x3.size + x2 else x1 + x3.size + (x2 + 1) + (k - 1)

def gateO (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) : Gate :=
  ⟨GateOp.or, [prevW x1 x2 x3 k, x1 + x3.size + k]⟩

def gatesO (x1 x2 : ℕ) (x3 : Circuit) : ℕ → List Gate
  | 0 => []
  | k + 1 => gatesO x1 x2 x3 k ++ [gateO x1 x2 x3 k]

def pval (x2 : ℕ) (av : List Bool) : ℕ → Bool
  | 0 => av.getD x2 false || av.getD 0 false
  | k + 1 => pval x2 av k || av.getD (k + 1) false

def built (x1 x2 : ℕ) (x3 : Circuit) (x4 : Fin (x2 + 1) → Fin x1)
    (x5 : Fin (x2 + 1) → ℕ) : Circuit :=
  { gates := x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2
    output := x1 + x3.size + 2 * x2 }

lemma andGates_length (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ) :
    (andGates x1 x2 x4 x5).length = x2 + 1 := by
  rw [andGates, List.length_ofFn]

lemma andGates_getD (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ)
    {j : ℕ} (hj : j < x2 + 1) :
    (andGates x1 x2 x4 x5).getD j dfltGate = ⟨GateOp.and, [x4 ⟨j, hj⟩, x5 ⟨j, hj⟩]⟩ := by
  rw [andGates]
  exact ofFn_gate_getD (fun i : Fin (x2 + 1) => ⟨GateOp.and, [x4 i, x5 i]⟩) hj

lemma termVals_getD (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ)
    (w : List Bool) {j : ℕ} (hj : j < x2 + 1) :
    (termVals x1 x2 x4 x5 w).getD j false
      = (w.getD (x4 ⟨j, hj⟩) false && w.getD (x5 ⟨j, hj⟩) false) := by
  rw [termVals]
  exact ofFn_getD (fun i : Fin (x2 + 1) => w.getD (x4 i) false && w.getD (x5 i) false) hj

lemma andGates_mono (x1 x2 : ℕ) (x4 : Fin (x2 + 1) → Fin x1) (x5 : Fin (x2 + 1) → ℕ)
    (g : Gate) (hg : g ∈ andGates x1 x2 x4 x5) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rw [andGates, List.mem_ofFn] at hg
  obtain ⟨i, rfl⟩ := hg
  exact ⟨by simp, by simp⟩

lemma gatesO_zero (x1 x2 : ℕ) (x3 : Circuit) : gatesO x1 x2 x3 0 = [] := rfl

lemma gatesO_succ (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) :
    gatesO x1 x2 x3 (k + 1) = gatesO x1 x2 x3 k ++ [gateO x1 x2 x3 k] := rfl

lemma gatesO_length (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) :
    (gatesO x1 x2 x3 k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (gatesO x1 x2 x3 k ++ [gateO x1 x2 x3 k]).length = k + 1
    rw [List.length_append, ih, List.length_singleton]

lemma gatesO_mono (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) (g : Gate)
    (hg : g ∈ gatesO x1 x2 x3 k) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero =>
    rw [gatesO_zero] at hg
    simp at hg
  | succ k ih =>
    rw [gatesO_succ] at hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact ih h
    · refine ⟨Or.inr rfl, ?_⟩
      simp [gateO]

lemma prevW_zero (x1 x2 : ℕ) (x3 : Circuit) : prevW x1 x2 x3 0 = x1 + x3.size + x2 := by
  rw [prevW]
  simp

lemma prevW_succ (x1 x2 : ℕ) (x3 : Circuit) (k : ℕ) :
    prevW x1 x2 x3 (k + 1) = x1 + x3.size + (x2 + 1) + k := by
  rw [prevW]
  simp only [Nat.succ_ne_zero, if_false]
  omega

lemma pval_iff (x2 : ℕ) (av : List Bool) (k : ℕ) :
    pval x2 av k = true ↔ av.getD x2 false = true ∨ ∃ j, j ≤ k ∧ av.getD j false = true := by
  induction k with
  | zero =>
    show (av.getD x2 false || av.getD 0 false) = true ↔ _
    rw [Bool.or_eq_true]
    constructor
    · intro h
      rcases h with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨0, by omega, h2⟩
    · intro h
      rcases h with h1 | ⟨j, hj, h2⟩
      · exact Or.inl h1
      · have hj0 : j = 0 := by omega
        subst hj0
        exact Or.inr h2
  | succ k ih =>
    show (pval x2 av k || av.getD (k + 1) false) = true ↔ _
    rw [Bool.or_eq_true, ih]
    constructor
    · intro h
      rcases h with (h1 | ⟨j, hj, h2⟩) | h3
      · exact Or.inl h1
      · exact Or.inr ⟨j, by omega, h2⟩
      · exact Or.inr ⟨k + 1, by omega, h3⟩
    · intro h
      rcases h with h1 | ⟨j, hj, h2⟩
      · exact Or.inl (Or.inl h1)
      · by_cases hjk : j ≤ k
        · exact Or.inl (Or.inr ⟨j, hjk, h2⟩)
        · have hj' : j = k + 1 := by omega
          subst hj'
          exact Or.inr h2

lemma foldl_base : ∀ (l : List Gate) (w : List Bool) (v : ℕ → Bool),
    (∀ (j : ℕ), j < l.length → ∀ i ∈ (l.getD j dfltGate).inputs, i < w.length) →
    (∀ (j : ℕ), j < l.length →
      (l.getD j dfltGate).op.eval ((l.getD j dfltGate).inputs.map fun i => w.getD i false) = v j) →
    (∀ i, i < w.length → (l.foldl wstep w).getD i false = w.getD i false) ∧
      (∀ j, j < l.length → (l.foldl wstep w).getD (w.length + j) false = v j) := by
  intro l
  induction l with
  | nil =>
    intro w v hread hval
    refine ⟨fun i _ => by simp, ?_⟩
    intro j hj
    simp at hj
  | cons g0 t ih =>
    intro w v hread hval
    have hval0 : g0.op.eval (g0.inputs.map fun i => w.getD i false) = v 0 := hval 0 (by simp)
    have hreadT : ∀ (j : ℕ), j < t.length → ∀ i ∈ (t.getD j dfltGate).inputs, i < w.length := by
      intro j hj i hi
      exact hread (j + 1) (by simp [hj]) i (by simpa using hi)
    have hvalT : ∀ (j : ℕ), j < t.length →
        (t.getD j dfltGate).op.eval ((t.getD j dfltGate).inputs.map fun i => w.getD i false)
          = v (j + 1) := by
      intro j hj
      simpa using hval (j + 1) (by simp [hj])
    obtain ⟨ih1, ih2⟩ := ih (w := wstep w g0) (v := fun j => v (j + 1))
      (by
        intro j hj i hi
        have h1 := hreadT j hj i hi
        rw [wstep_length]
        omega)
      (by
        intro j hj
        rw [← hvalT j hj]
        have hm : (t.getD j dfltGate).inputs.map (fun i => (wstep w g0).getD i false)
            = (t.getD j dfltGate).inputs.map (fun i => w.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact wstep_getD_lt w g0 (hreadT j hj i hi)
        rw [hm])
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [List.foldl_cons]
      exact (ih1 i (by rw [wstep_length]; omega)).trans (wstep_getD_lt w g0 hi)
    · intro j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, foldl_getD_lt t (wstep w g0) (by rw [wstep_length]; omega),
          wstep_getD_self]
        exact hval0
      | succ k =>
        rw [show w.length + (k + 1) = (wstep w g0).length + k by rw [wstep_length]; omega]
        exact ih2 k (by simpa using hj)

lemma and_side (x1 x2 : ℕ) (x3 : Circuit) (x4 : Fin (x2 + 1) → Fin x1)
    (x5 : Fin (x2 + 1) → ℕ) (hlt : ∀ i, x5 i < x1 + x3.size) (xs : List Bool)
    (hxs : xs.length = x1) :
    (∀ i, i < x1 + x3.size →
        ((andGates x1 x2 x4 x5).foldl wstep (x3.wires xs)).getD i false
          = (x3.wires xs).getD i false) ∧
      (∀ j, j < x2 + 1 →
        ((andGates x1 x2 x4 x5).foldl wstep (x3.wires xs)).getD (x1 + x3.size + j) false
          = (termVals x1 x2 x4 x5 (x3.wires xs)).getD j false) ∧
      ((andGates x1 x2 x4 x5).foldl wstep (x3.wires xs)).length = x1 + x3.size + (x2 + 1) := by
  have hwlen : (x3.wires xs).length = x1 + x3.size := by
    rw [wires_length, hxs]
  have hread : ∀ (j : ℕ), j < (andGates x1 x2 x4 x5).length →
      ∀ i ∈ ((andGates x1 x2 x4 x5).getD j dfltGate).inputs, i < (x3.wires xs).length := by
    intro j hj i hi
    have hj' : j < x2 + 1 := by rw [andGates_length] at hj; exact hj
    rw [andGates_getD x1 x2 x4 x5 hj'] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hwlen]
    rcases hi with h | h
    · rw [h]
      exact Nat.lt_of_lt_of_le (x4 ⟨j, hj'⟩).isLt (Nat.le_add_right x1 x3.size)
    · rw [h]
      exact hlt ⟨j, hj'⟩
  have hval : ∀ (j : ℕ), j < (andGates x1 x2 x4 x5).length →
      ((andGates x1 x2 x4 x5).getD j dfltGate).op.eval
          (((andGates x1 x2 x4 x5).getD j dfltGate).inputs.map fun i => (x3.wires xs).getD i false)
        = (termVals x1 x2 x4 x5 (x3.wires xs)).getD j false := by
    intro j hj
    have hj' : j < x2 + 1 := by rw [andGates_length] at hj; exact hj
    rw [andGates_getD x1 x2 x4 x5 hj']
    show GateOp.and.eval [(x3.wires xs).getD (x4 ⟨j, hj'⟩) false,
      (x3.wires xs).getD (x5 ⟨j, hj'⟩) false] = _
    rw [and_eval_pair, termVals_getD x1 x2 x4 x5 (x3.wires xs) hj']
  obtain ⟨h1, h2⟩ := foldl_base (andGates x1 x2 x4 x5) (x3.wires xs)
    (fun j => (termVals x1 x2 x4 x5 (x3.wires xs)).getD j false) hread hval
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact h1 i (by rw [hwlen]; exact hi)
  · intro j hj
    have h := h2 j (by rw [andGates_length]; exact hj)
    rw [hwlen] at h
    exact h
  · rw [foldl_length, hwlen, andGates_length]

lemma gatesO_spec (x1 x2 : ℕ) (x3 : Circuit) (av : List Bool) (w1 : List Bool)
    (hw1 : w1.length = x1 + x3.size + (x2 + 1))
    (hav : ∀ (j : ℕ), j < x2 + 1 → w1.getD (x1 + x3.size + j) false = av.getD j false) :
    ∀ (k : ℕ), k ≤ x2 →
      (∀ i, i < x1 + x3.size + (x2 + 1) →
          ((gatesO x1 x2 x3 k).foldl wstep w1).getD i false = w1.getD i false) ∧
        (∀ j, j < k →
          ((gatesO x1 x2 x3 k).foldl wstep w1).getD (x1 + x3.size + (x2 + 1) + j) false
            = pval x2 av j) := by
  intro k
  induction k with
  | zero =>
    intro hk
    refine ⟨fun i _ => by rw [gatesO_zero]; rfl, ?_⟩
    intro j hj
    omega
  | succ k ih =>
    intro hk
    have hk' : k ≤ x2 := by omega
    obtain ⟨ih1, ih2⟩ := ih hk'
    have hulen : ((gatesO x1 x2 x3 k).foldl wstep w1).length = x1 + x3.size + (x2 + 1) + k := by
      rw [foldl_length, hw1, gatesO_length]
    have hfold : (gatesO x1 x2 x3 (k + 1)).foldl wstep w1
        = wstep ((gatesO x1 x2 x3 k).foldl wstep w1) (gateO x1 x2 x3 k) := by
      rw [gatesO_succ, List.foldl_append]
      rfl
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [hfold, wstep_getD_lt _ _ (by rw [hulen]; omega)]
      exact ih1 i hi
    · intro j hj
      rw [hfold]
      rcases Nat.lt_or_eq_of_le (show j ≤ k by omega) with hlt | heq
      · rw [wstep_getD_lt _ _ (by rw [hulen]; omega)]
        exact ih2 j hlt
      · rw [heq]
        rw [← hulen, wstep_getD_self]
        simp only [gateO, List.map_cons, List.map_nil, or_eval_pair]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [prevW_zero]
          have h1 : ((gatesO x1 x2 x3 0).foldl wstep w1).getD (x1 + x3.size + x2) false
              = av.getD x2 false := by
            rw [ih1 (x1 + x3.size + x2) (by omega)]
            exact hav x2 (by omega)
          have h2 : ((gatesO x1 x2 x3 0).foldl wstep w1).getD (x1 + x3.size + 0) false
              = av.getD 0 false := by
            rw [ih1 (x1 + x3.size + 0) (by omega)]
            exact hav 0 (by omega)
          rw [h1, h2]
          rfl
        · obtain ⟨j0, hj0⟩ : ∃ j0, k = j0 + 1 := ⟨k - 1, by omega⟩
          subst hj0
          rw [prevW_succ]
          have h1 : ((gatesO x1 x2 x3 (j0 + 1)).foldl wstep w1).getD
              (x1 + x3.size + (x2 + 1) + j0) false = pval x2 av j0 := ih2 j0 (by omega)
          have h2 : ((gatesO x1 x2 x3 (j0 + 1)).foldl wstep w1).getD
              (x1 + x3.size + (j0 + 1)) false = av.getD (j0 + 1) false := by
            rw [ih1 (x1 + x3.size + (j0 + 1)) (by omega)]
            exact hav (j0 + 1) (by omega)
          rw [h1, h2]
          rfl

lemma or_side (x1 x2 : ℕ) (x3 : Circuit) (av : List Bool) (w1 : List Bool)
    (hw1 : w1.length = x1 + x3.size + (x2 + 1))
    (hav : ∀ (j : ℕ), j < x2 + 1 → w1.getD (x1 + x3.size + j) false = av.getD j false) :
    (∀ i, i < x1 + x3.size + (x2 + 1) →
        ((gatesO x1 x2 x3 x2).foldl wstep w1).getD i false = w1.getD i false) ∧
      (∀ j, j < x2 →
        ((gatesO x1 x2 x3 x2).foldl wstep w1).getD (x1 + x3.size + (x2 + 1) + j) false
          = pval x2 av j) ∧
      ((gatesO x1 x2 x3 x2).foldl wstep w1).length = x1 + x3.size + 2 * x2 + 1 := by
  obtain ⟨h1, h2⟩ := gatesO_spec x1 x2 x3 av w1 hw1 hav x2 (le_refl x2)
  refine ⟨h1, h2, ?_⟩
  rw [foldl_length, hw1, gatesO_length]
  omega

lemma termVals_true (x1 x2 : ℕ) (x3 : Circuit) (x4 : Fin (x2 + 1) → Fin x1)
    (x5 : Fin (x2 + 1) → ℕ) (xs : List Bool) (hxs : xs.length = x1)
    {j : ℕ} (hj : j < x2 + 1) :
    (termVals x1 x2 x4 x5 (x3.wires xs)).getD j false = true ↔
      xs.getD (x4 ⟨j, hj⟩) false = true ∧ (x3.wires xs).getD (x5 ⟨j, hj⟩) false = true := by
  rw [termVals_getD x1 x2 x4 x5 (x3.wires xs) hj, Bool.and_eq_true]
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    rw [← wires_getD_input x3 xs (by rw [hxs]; exact (x4 ⟨j, hj⟩).isLt)]
    exact h.1
  · intro h
    refine ⟨?_, h.2⟩
    rw [wires_getD_input x3 xs (by rw [hxs]; exact (x4 ⟨j, hj⟩).isLt)]
    exact h.1

lemma exists_termVals (x1 x2 : ℕ) (x3 : Circuit) (x4 : Fin (x2 + 1) → Fin x1)
    (x5 : Fin (x2 + 1) → ℕ) (xs : List Bool) (hxs : xs.length = x1) :
    (∃ j, j < x2 + 1 ∧ (termVals x1 x2 x4 x5 (x3.wires xs)).getD j false = true) ↔
      ∃ i : Fin (x2 + 1), xs.getD (x4 i) false = true ∧
        (x3.wires xs).getD (x5 i) false = true := by
  constructor
  · rintro ⟨j, hj, hv⟩
    exact ⟨⟨j, hj⟩, (termVals_true x1 x2 x3 x4 x5 xs hxs hj).mp hv⟩
  · rintro ⟨i, h1, h2⟩
    exact ⟨i, i.isLt, (termVals_true x1 x2 x3 x4 x5 xs hxs i.isLt).mpr ⟨h1, h2⟩⟩

lemma eval_iff (x1 x2 : ℕ) (x3 : Circuit) (x4 : Fin (x2 + 1) → Fin x1)
    (x5 : Fin (x2 + 1) → ℕ) (hlt : ∀ i, x5 i < x1 + x3.size) (xs : List Bool)
    (hxs : xs.length = x1) :
    ((built x1 x2 x3 x4 x5).wires xs).getD (x1 + x3.size + 2 * x2) false = true ↔
      ∃ i : Fin (x2 + 1), xs.getD (x4 i) false = true ∧
        (x3.wires xs).getD (x5 i) false = true := by
  obtain ⟨a1, a2, a3⟩ := and_side x1 x2 x3 x4 x5 hlt xs hxs
  obtain ⟨o1, o2, o3⟩ := or_side x1 x2 x3 (termVals x1 x2 x4 x5 (x3.wires xs))
    ((andGates x1 x2 x4 x5).foldl wstep (x3.wires xs)) a3 a2
  have hwires : (built x1 x2 x3 x4 x5).wires xs
      = (gatesO x1 x2 x3 x2).foldl wstep
          ((andGates x1 x2 x4 x5).foldl wstep (x3.wires xs)) := by
    rw [wires_eq_fold]
    show (x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2).foldl wstep xs = _
    rw [List.foldl_append, List.foldl_append, ← wires_eq_fold]
  rw [hwires]
  rcases Nat.eq_zero_or_pos x2 with hx0 | hxpos
  · subst hx0
    have hg : gatesO x1 0 x3 0 = [] := gatesO_zero x1 0 x3
    rw [hg, List.foldl_nil]
    simp only [Nat.mul_zero, Nat.add_zero]
    have h1 : ((andGates x1 0 x4 x5).foldl wstep (x3.wires xs)).getD (x1 + x3.size) false
        = (termVals x1 0 x4 x5 (x3.wires xs)).getD 0 false := by
      have h := a2 0 (by omega)
      rwa [Nat.add_zero] at h
    rw [h1]
    constructor
    · intro h
      exact (exists_termVals x1 0 x3 x4 x5 xs hxs).mp ⟨0, by omega, h⟩
    · intro h
      obtain ⟨j, hj, hv⟩ := (exists_termVals x1 0 x3 x4 x5 xs hxs).mpr h
      have hj0 : j = 0 := by omega
      rw [hj0] at hv
      exact hv
  · have hidx : x1 + x3.size + 2 * x2 = x1 + x3.size + (x2 + 1) + (x2 - 1) := by omega
    rw [hidx, o2 (x2 - 1) (by omega),
      pval_iff x2 (termVals x1 x2 x4 x5 (x3.wires xs)) (x2 - 1)]
    constructor
    · intro h
      rcases h with h1 | ⟨j, hj, h2⟩
      · exact (exists_termVals x1 x2 x3 x4 x5 xs hxs).mp ⟨x2, by omega, h1⟩
      · exact (exists_termVals x1 x2 x3 x4 x5 xs hxs).mp ⟨j, by omega, h2⟩
    · intro h
      obtain ⟨j, hj, hv⟩ := (exists_termVals x1 x2 x3 x4 x5 xs hxs).mpr h
      by_cases hjc : j ≤ x2 - 1
      · exact Or.inr ⟨j, hjc, hv⟩
      · exact Or.inl (by
          have hjx : j = x2 := by omega
          rw [hjx] at hv
          exact hv)

end PEqualNP.Outside.L_meta_4968_aux

open PEqualNP.Outside.L_meta_4968_aux

theorem PEqualNP.Outside.L_meta_4968 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (x2 + (1 : ℕ)) → Fin x1) (x5 : Fin (x2 + (1 : ℕ)) → ℕ), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x2 + (1 : ℕ))), x5 x7 < x1 + x3.size) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x3.size + (2 : ℕ) * x2 + (1 : ℕ) ∧ x8.output < x1 + x8.size ∧ (∀ (x9 : Fin x1 → Bool), ∀ x10 < x1 + x3.size, (x8.wires (List.ofFn x9)).getD x10 Bool.false = (x3.wires (List.ofFn x9)).getD x10 Bool.false) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin (x2 + (1 : ℕ))), x9 (x4 x10) = Bool.true ∧ (x3.wires (List.ofFn x9)).getD (x5 x10) Bool.false = Bool.true := by
  intro x1 x2 x3 x4 x5 hmono hlt
  refine ⟨built x1 x2 x3 x4 x5, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2 at hg
    rw [List.mem_append, List.mem_append] at hg
    rcases hg with (h | h) | h
    · exact hmono g h
    · exact andGates_mono x1 x2 x4 x5 g h
    · exact gatesO_mono x1 x2 x3 x2 g h
  · show (x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2).length
      = x3.gates.length + 2 * x2 + 1
    rw [List.length_append, List.length_append, andGates_length, gatesO_length]
    omega
  · show x1 + x3.gates.length + 2 * x2
      < x1 + (x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2).length
    rw [List.length_append, List.length_append, andGates_length, gatesO_length]
    omega
  · intro x9 x10 hx10
    obtain ⟨a1, a2, a3⟩ := and_side x1 x2 x3 x4 x5 hlt (List.ofFn x9) List.length_ofFn
    obtain ⟨o1, o2, o3⟩ := or_side x1 x2 x3 (termVals x1 x2 x4 x5 (x3.wires (List.ofFn x9)))
      ((andGates x1 x2 x4 x5).foldl wstep (x3.wires (List.ofFn x9))) a3 a2
    have hw : (built x1 x2 x3 x4 x5).wires (List.ofFn x9)
        = (gatesO x1 x2 x3 x2).foldl wstep
            ((andGates x1 x2 x4 x5).foldl wstep (x3.wires (List.ofFn x9))) := by
      rw [wires_eq_fold]
      show (x3.gates ++ andGates x1 x2 x4 x5 ++ gatesO x1 x2 x3 x2).foldl wstep (List.ofFn x9) = _
      rw [List.foldl_append, List.foldl_append, ← wires_eq_fold]
    rw [hw, o1 x10 (by omega), a1 x10 hx10]
  · intro x9
    show ((built x1 x2 x3 x4 x5).wires (List.ofFn x9)).getD (x1 + x3.size + 2 * x2) false
      = true ↔ _
    rw [eval_iff x1 x2 x3 x4 x5 hlt (List.ofFn x9) List.length_ofFn]
    constructor
    · rintro ⟨i, h1, h2⟩
      refine ⟨i, ?_, h2⟩
      rw [← ofFn_apply x9 (x4 i)]
      exact h1
    · rintro ⟨i, h1, h2⟩
      refine ⟨i, ?_, h2⟩
      rw [ofFn_apply x9 (x4 i)]
      exact h1
