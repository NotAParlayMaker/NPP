import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1351_aux

open PEqualNP.CircuitLowerBounds

def relabel (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩ : ℕ) else i

theorem relabel_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) (L : ℕ) (hL : n ≤ L) (i : ℕ) :
    relabel n σ i < L ↔ i < L := by
  unfold relabel
  split_ifs with h
  · have := (σ ⟨i, h⟩).isLt
    constructor <;> intro <;> omega
  · exact Iff.rfl

theorem relabel_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) (L : ℕ) (hL : n ≤ L) (i : ℕ) :
    relabel n σ i = L ↔ i = L := by
  unfold relabel
  split_ifs with h
  · have := (σ ⟨i, h⟩).isLt
    constructor <;> intro <;> omega
  · exact Iff.rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapGate (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (relabel n σ)⟩

theorem getD_append_one (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem fold_rel (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ (w w' : List Bool), w.length = w'.length → n ≤ w.length →
      (∀ i, w'.getD (relabel n σ i) false = w.getD i false) →
      ∀ i, ((gs.map (mapGate n σ)).foldl step w').getD (relabel n σ i) false =
        (gs.foldl step w).getD i false := by
  induction gs with
  | nil =>
    intro w w' hlen _ h
    exact fun i => by simpa using h i
  | cons g gs ih =>
    intro w w' hlen hn h
    have hval : g.op.eval ((g.inputs.map (relabel n σ)).map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    have hstep : ∀ i, (step w' (mapGate n σ g)).getD (relabel n σ i) false =
        (step w g).getD i false := by
      intro i
      unfold step mapGate
      simp only
      rw [getD_append_one, getD_append_one, hval, ← hlen]
      have e1 := relabel_lt n σ w.length hn i
      have e2 := relabel_eq n σ w.length hn i
      by_cases h1 : i < w.length
      · rw [ite_eq_left (e1.2 h1), ite_eq_left h1]
        exact h i
      · rw [ite_eq_right (fun hh => h1 (e1.1 hh)), ite_eq_right h1]
        by_cases h2 : i = w.length
        · rw [ite_eq_left (e2.2 h2), ite_eq_left h2]
        · rw [ite_eq_right (fun hh => h2 (e2.1 hh)), ite_eq_right h2]
    have hl1 : (step w g).length = (step w' (mapGate n σ g)).length := by
      simp [step, hlen]
    have hl2 : n ≤ (step w g).length := by
      simp [step]
      omega
    simpa using ih (step w g) (step w' (mapGate n σ g)) hl1 hl2 hstep

end PEqualNP.Outside.L_meta_1351_aux

open PEqualNP.Outside.L_meta_1351_aux in
theorem PEqualNP.Outside.L_meta_1351 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (σ : Equiv.Perm (Fin n)), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun h => h.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + j⟩ (List.ofFn (x ∘ σ)) := by
  intro n gates σ
  refine ⟨gates.map (mapGate n σ), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, mapGate]
  · simp [List.map_map, Function.comp_def, mapGate]
  · intro j x
    have h0 : ∀ i, (List.ofFn x).getD (relabel n σ i) false =
        (List.ofFn (x ∘ σ)).getD i false := by
      intro i
      unfold relabel
      split_ifs with h
      · simp [List.getD_eq_getElem?_getD, h]
      · simp [List.getD_eq_getElem?_getD, h]
    have hc := fold_rel n σ gates (List.ofFn (x ∘ σ)) (List.ofFn x) (by simp)
      (by simp) h0
    have hr : relabel n σ (n + j) = n + j := by
      unfold relabel
      split_ifs with h
      · omega
      · rfl
    have := hc (n + j)
    rw [hr] at this
    exact this
