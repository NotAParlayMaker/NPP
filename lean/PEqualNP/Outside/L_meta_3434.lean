import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (b : Bool) {i : ℕ} (h : i < L.length) :
    (L ++ [b]).getD i false = L.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (b : Bool) :
    (L ++ [b]).getD L.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (b : Bool) {i : ℕ} (h : L.length < i) :
    (L ++ [b]).getD i false = false := by
  rw [List.getD_eq_default _ _ (by simp; omega)]

theorem getD_ge (L : List Bool) {i : ℕ} (h : L.length ≤ i) : L.getD i false = false :=
  List.getD_eq_default _ _ h

theorem run (σ : ℕ → ℕ) (L size : ℕ)
    (hid : ∀ i, L ≤ i → σ i = i)
    (hsw : ∀ i, i < L → σ i < L ∨ L + size ≤ σ i) :
    ∀ (gs : List Gate) (x y : List Bool),
      x.length = y.length → L ≤ x.length → x.length + gs.length ≤ L + size →
      (∀ i, y.getD (σ i) false = x.getD i false) →
      ∀ i, ((gs.map fun g => ({ op := g.op, inputs := g.inputs.map σ } : Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) y).getD (σ i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro x y _ _ _ hag i
    exact hag i
  | cons g gs ih =>
    intro x y hlen hL hb hag i
    simp only [List.map_cons, List.foldl_cons]
    have hval : g.op.eval ((g.inputs.map σ).map fun j => y.getD j false)
        = g.op.eval (g.inputs.map fun j => x.getD j false) := by
      congr 1
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left (fun j _ => hag j)
    have hlt : x.length < L + size := by
      simp only [List.length_cons] at hb; omega
    refine ih (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])
      (y ++ [g.op.eval ((g.inputs.map σ).map fun j => y.getD j false)]) ?_ ?_ ?_ ?_ i
    · simp [hlen]
    · simp; omega
    · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hb ⊢; omega
    · intro k
      rw [hval]
      set b := g.op.eval (g.inputs.map fun j => x.getD j false) with hbdef
      by_cases hk : k < x.length
      · rw [getD_snoc_lt x b hk]
        have hk' := hag k
        by_cases hsk : σ k < y.length
        · rw [getD_snoc_lt y b hsk]; exact hk'
        · have hge : y.length ≤ σ k := by omega
          have hne : σ k ≠ y.length := by
            by_cases hkL : k < L
            · rcases hsw k hkL with h | h
              · omega
              · omega
            · have := hid k (by omega); omega
          rw [getD_ge y hge] at hk'
          have : y.length < σ k := by omega
          rw [getD_snoc_gt y b this, ← hk']
      · by_cases hke : k = x.length
        · subst hke
          have hs : σ x.length = x.length := hid _ hL
          rw [hs, getD_snoc_eq x b, hlen, getD_snoc_eq y b]
        · have hgt : x.length < k := by omega
          rw [hid k (by omega), getD_snoc_gt x b hgt, getD_snoc_gt y b (by omega)]

end PEqualNP.Outside.L_meta_3434

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro σ C x y hlen hid hsw hag
  have h := PEqualNP.Outside.L_meta_3434.run σ x.length C.size hid hsw C.gates x y hlen (le_refl _)
    (by simp [PEqualNP.CircuitLowerBounds.Circuit.size]) hag C.output
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact h
