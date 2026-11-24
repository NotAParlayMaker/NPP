import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ren (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem getD_big {l : List Bool} {i : ℕ} (h : l.length ≤ i) : l.getD i false = false :=
  List.getD_eq_default _ _ h

-- Wire w of the circuit on A is wire f w of the renamed circuit on B, gate after gate.
theorem sim (L : ℕ) (f : ℕ → ℕ) (hfix : ∀ w, L ≤ w → f w = w) :
    ∀ (gs : List Gate) (A B : List Bool), A.length = B.length → L ≤ A.length →
      (∀ w < L, f w < L ∨ A.length + gs.length ≤ f w) →
      (∀ w, B.getD (f w) false = A.getD w false) →
      ∀ w, ((gs.map (ren f)).foldl stp B).getD (f w) false = (gs.foldl stp A).getD w false := by
  intro gs
  induction gs with
  | nil => intro A B _ _ _ h w; exact h w
  | cons g gs ih =>
    intro A B hl hL hf h
    simp only [List.map_cons, List.foldl_cons]
    have hv : g.op.eval ((ren f g).inputs.map fun i => B.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := by
      simp only [ren, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    have hstp : stp B (ren f g) = B ++ [g.op.eval (g.inputs.map fun i => A.getD i false)] := by
      simp only [stp]
      rw [show (ren f g).op = g.op from rfl, hv]
    apply ih
    · simp [stp, hl]
    · simp [stp]; omega
    · intro w hw
      rcases hf w hw with h1 | h1
      · exact Or.inl h1
      · right; simp [stp] at h1 ⊢; omega
    · intro w
      rw [hstp]
      simp only [stp]
      rcases Nat.lt_trichotomy w A.length with hw | hw | hw
      · rw [List.getD_append _ _ _ _ hw]
        by_cases hfw : f w < B.length
        · rw [List.getD_append _ _ _ _ hfw]
          exact h w
        · have hwL : w < L := by
            by_contra hc
            have := hfix w (by omega)
            omega
          have hbig : A.length + (gs.length + 1) ≤ f w := by
            rcases hf w hwL with h1 | h1
            · omega
            · simpa using h1
          rw [getD_big (by simp; omega)]
          rw [← h w, getD_big (by omega)]
      · have hfw : f w = w := hfix w (by omega)
        rw [hfw, hw, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (le_refl _)]
        simp [hl]
      · have hfw : f w = w := hfix w (by omega)
        rw [hfw, getD_big (by simp; omega), getD_big (by simp; omega)]

end PEqualNP.Outside.L_meta_3434

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3434

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro f C A B hl hfix hf h
  show (List.foldl _ B (C.gates.map (ren f))).getD (f C.output) false =
    (List.foldl _ A C.gates).getD C.output false
  exact sim A.length f (fun w hw => hfix w hw) C.gates A B hl le_rfl
    (fun w hw => hf w hw) h C.output
