import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5004

open PEqualNP.CircuitLowerBounds

def ren (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_lt (w : List Bool) (b : Bool) (j : ℕ) (h : j < w.length) :
    (w ++ [b]).getD j false = w.getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (w : List Bool) (b : Bool) (j : ℕ) (h : w.length < j) :
    (w ++ [b]).getD j false = w.getD j false := by
  rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma key (n : ℕ) (s : ℕ → ℕ) (hin : ∀ x < n, s x < n) (hfix : ∀ x, n ≤ x → s x = x) :
    ∀ (gs : List Gate) (W' W : List Bool), W'.length = W.length → n ≤ W.length →
      (∀ j, W'.getD (s j) false = W.getD j false) →
      ((gs.map (ren s)).foldl step W').length = (gs.foldl step W).length ∧
      ∀ j, ((gs.map (ren s)).foldl step W').getD (s j) false =
        (gs.foldl step W).getD j false := by
  intro gs
  induction gs with
  | nil => intro W' W hl _ h; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro W' W hl hn h
    have hv : (ren s g).op.eval ((ren s g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [ren, List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left (fun i _ => h i)
    apply ih
    · simp [step, hl]
    · simp [step]; omega
    · intro j
      simp only [step]
      rw [hv]
      by_cases hj : j < n
      · have hs := hin j hj
        rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact h j
      · have hs := hfix j (by omega)
        rw [hs]
        rcases lt_trichotomy j W.length with hlt | heq | hgt
        · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ hlt]
          have := h j
          rwa [hs] at this
        · subst heq
          rw [← hl, getD_snoc_eq, hl, getD_snoc_eq]
        · rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ hgt,
            List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_5004

open PEqualNP.Outside.L_meta_5004

theorem PEqualNP.Outside.L_meta_5004 : ∀ (x1 : ℕ) (x2 : ℕ → ℕ), (∀ x3 < x1, x2 x3 < x1) → (∀ (x4 : ℕ), x1 ≤ x4 → x2 x4 = x4) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size = x5.size ∧ ∀ (x8 x9 : List Bool), x8.length = x1 → x9.length = x1 → (∀ (x12 : ℕ), x8.getD (x2 x12) Bool.false = x9.getD x12 Bool.false) → x7.eval x8 = x5.eval x9 := by
  intro n s hin hfix C hC
  refine ⟨⟨C.gates.map (ren s), s C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := hC g0 hg0
    exact ⟨hop, by simpa [ren] using hlen⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro a b ha hb h
    have k := (key n s hin hfix C.gates a b (by rw [ha, hb]) (by omega) h).2 C.output
    exact k
