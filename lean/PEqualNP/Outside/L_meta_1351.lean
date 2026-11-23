import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

def permWmap (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩ : ℕ) else w

def permRelGate (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWmap n σ)⟩

def permStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def permRel (n : ℕ) (σ : Equiv.Perm (Fin n)) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length = W.length ∧
    ∀ w : ℕ, W'.getD (permWmap n σ w) false = W.getD w false

theorem permSnocDefault {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

theorem permRelStep (n : ℕ) (σ : Equiv.Perm (Fin n)) (W W' : List Bool) (g : Gate)
    (h : permRel n σ W W') :
    permRel n σ (permStep W g) (permStep W' (permRelGate n σ g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (permRelGate n σ g).op.eval
      ((permRelGate n σ g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [permRelGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [permStep]; omega, by simp [permStep, h2], ?_⟩
  intro w
  simp only [permStep, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : permWmap n σ w < W'.length := by
      unfold permWmap
      split
      · have := (σ ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : permWmap n σ w = W'.length := by
      unfold permWmap
      split
      · omega
      · omega
    rw [he, hw, permSnocDefault, permSnocDefault]
  · have hge : W'.length + 1 ≤ permWmap n σ w := by
      unfold permWmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem permRelFold (n : ℕ) (σ : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ W W' : List Bool, permRel n σ W W' →
      permRel n σ (gs.foldl permStep W) ((gs.map (permRelGate n σ)).foldl permStep W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (permRelStep n σ W W' g h)

theorem permRelInit (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    permRel n σ (List.ofFn (x ∘ σ)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w
  unfold permWmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1351 :
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (σ : Equiv.Perm (Fin n)), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun h => h.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + j⟩ (List.ofFn (x ∘ σ)) := by
  intro n gates σ
  let gates' : List PEqualNP.CircuitLowerBounds.Gate := gates.map (PEqualNP.MetaComplexity.permRelGate n σ)
  refine ⟨gates', ?_, ?_, ?_⟩
  · simp [gates', PEqualNP.MetaComplexity.permRelGate]
  · simp [gates', PEqualNP.MetaComplexity.permRelGate]
  · intro j x
    change ((gates.map (PEqualNP.MetaComplexity.permRelGate n σ)).foldl PEqualNP.MetaComplexity.permStep (List.ofFn x)).getD (n + j) false =
      (gates.foldl PEqualNP.MetaComplexity.permStep (List.ofFn (x ∘ σ))).getD (n + j) false
    have hRel := PEqualNP.MetaComplexity.permRelFold n σ gates (List.ofFn (x ∘ σ)) (List.ofFn x) (PEqualNP.MetaComplexity.permRelInit n σ x)
    have hw := hRel.2.2 (n + j)
    rw [show PEqualNP.MetaComplexity.permWmap n σ (n + j) = n + j by unfold PEqualNP.MetaComplexity.permWmap; split <;> omega] at hw
    exact hw
