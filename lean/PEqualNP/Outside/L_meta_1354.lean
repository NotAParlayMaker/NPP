import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

def rr (n B i : ℕ) : ℕ := if i < n then i else if i = n then B else i - 1

def rl (n B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rr n B)⟩

lemma wires_nil (x : List Bool) : Circuit.wires ⟨[], 0⟩ x = x := by
  simp [Circuit.wires]

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc]
    simp [ih]
    omega

lemma getD_snoc_lt (A : List Bool) (e : Bool) (w : ℕ) (h : w < A.length) :
    (A ++ [e]).getD w false = A.getD w false :=
  List.getD_append _ _ _ _ h

lemma getD_snoc_eq (A : List Bool) (e : Bool) : (A ++ [e]).getD A.length false = e := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma getD_snoc_gt (A : List Bool) (e : Bool) (w : ℕ) (h : A.length < w) :
    (A ++ [e]).getD w false = false :=
  List.getD_eq_default _ _ (by simp; omega)

lemma ofFn_getD {n : ℕ} (v : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn v).getD w false = v ⟨w, hw⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

lemma ofFn_getD_ge {n : ℕ} (v : Fin n → Bool) (w : ℕ) (hw : n ≤ w) :
    (List.ofFn v).getD w false = false :=
  List.getD_eq_default _ _ (by simpa using hw)

lemma key (n B : ℕ) (x : Fin n → Bool) (gs : List Gate) (hB : n + gs.length ≤ B) :
    ∀ i, (Circuit.wires ⟨gs.map (rl n B), 0⟩ (List.ofFn x)).getD (rr n B i) false =
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x ++ [false])).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    simp only [List.map_nil, wires_nil]
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    by_cases h1 : i < n
    · have hr : rr n B i = i := by unfold rr; rw [if_pos h1]
      rw [hr, getD_snoc_lt _ _ _ (by rw [hlen]; exact h1)]
    · by_cases h2 : i = n
      · have hr : rr n B i = B := by unfold rr; rw [if_neg h1, if_pos h2]
        have e2 := getD_snoc_eq (List.ofFn x) false
        rw [hlen] at e2
        rw [hr, h2, e2, ofFn_getD_ge x B (by simp at hB; omega)]
      · have hr : rr n B i = i - 1 := by unfold rr; rw [if_neg h1, if_neg h2]
        rw [hr, ofFn_getD_ge x (i - 1) (by omega), getD_snoc_gt _ _ _ (by rw [hlen]; omega)]
  | append_singleton gs g ih =>
    intro i
    have hB' : n + gs.length ≤ B := by simp at hB; omega
    have ih' := ih hB'
    rw [List.map_append, List.map_singleton, wires_snoc, wires_snoc]
    have hl' : (Circuit.wires ⟨gs.map (rl n B), 0⟩ (List.ofFn x)).length = n + gs.length := by
      rw [wires_length]; simp
    have hl : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x ++ [false])).length = n + 1 + gs.length := by
      rw [wires_length]; simp
    have he : (rl n B g).op.eval ((rl n B g).inputs.map fun i =>
          (Circuit.wires ⟨gs.map (rl n B), 0⟩ (List.ofFn x)).getD i false) =
        g.op.eval (g.inputs.map fun i =>
          (Circuit.wires ⟨gs, 0⟩ (List.ofFn x ++ [false])).getD i false) := by
      simp only [rl, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact ih' i
    rw [he]
    set W' := Circuit.wires ⟨gs.map (rl n B), 0⟩ (List.ofFn x) with hW'
    set W := Circuit.wires ⟨gs, 0⟩ (List.ofFn x ++ [false]) with hW
    set E := g.op.eval (g.inputs.map fun i => W.getD i false) with hE
    rcases lt_trichotomy i (n + 1 + gs.length) with hi | hi | hi
    · rw [getD_snoc_lt W E i (by rw [hl]; exact hi), ← ih' i]
      by_cases h1 : i < n
      · have hr : rr n B i = i := by unfold rr; rw [if_pos h1]
        rw [hr, getD_snoc_lt W' E i (by rw [hl']; omega)]
      · by_cases h2 : i = n
        · have hr : rr n B i = B := by unfold rr; rw [if_neg h1, if_pos h2]
          rw [hr, getD_snoc_gt W' E B (by rw [hl']; simp at hB; omega),
            List.getD_eq_default _ _ (by rw [hl']; simp at hB; omega)]
        · have hr : rr n B i = i - 1 := by unfold rr; rw [if_neg h1, if_neg h2]
          rw [hr, getD_snoc_lt W' E (i - 1) (by rw [hl']; omega)]
    · have hr : rr n B i = n + gs.length := by
        unfold rr; rw [if_neg (by omega), if_neg (by omega)]; omega
      have e1 := getD_snoc_eq W' E
      rw [hl'] at e1
      have e2 := getD_snoc_eq W E
      rw [hl] at e2
      rw [hr, e1, hi, e2]
    · have hr : rr n B i = i - 1 := by unfold rr; rw [if_neg (by omega), if_neg (by omega)]
      rw [hr, getD_snoc_gt W' E (i - 1) (by rw [hl']; omega), getD_snoc_gt W E i (by rw [hl]; omega)]

end PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨gates.map (PEqualNP.Outside.L_meta_1354.rl n (n + gates.length)), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, PEqualNP.Outside.L_meta_1354.rl]
  · simp [List.map_map, Function.comp_def, PEqualNP.Outside.L_meta_1354.rl]
  · intro j x hj
    have h := PEqualNP.Outside.L_meta_1354.key n (n + gates.length) x gates (le_refl _) (n + 1 + j)
    have hr : PEqualNP.Outside.L_meta_1354.rr n (n + gates.length) (n + 1 + j) = n + j := by
      unfold PEqualNP.Outside.L_meta_1354.rr; rw [if_neg (by omega), if_neg (by omega)]; omega
    rw [hr] at h
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    exact h
