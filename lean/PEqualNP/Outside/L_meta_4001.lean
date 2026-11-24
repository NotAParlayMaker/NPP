import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4001_aux

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

def rl (a b : ℕ) (f : Fin a → Fin b) (w : ℕ) : ℕ :=
  if h : w < a then (f ⟨w, h⟩ : ℕ) else w - a + b

def mg (a b : ℕ) (f : Fin a → Fin b) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rl a b f)⟩

theorem getD_app (L : List Bool) (v : Bool) (i : ℕ) :
    (L ++ [v]).getD i false =
      if i < L.length then L.getD i false else if i = L.length then v else false := by
  rcases lt_trichotomy i L.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem key (a b : ℕ) (f : Fin a → Fin b) (gs : List Gate) :
    ∀ (W W' : List Bool) (m : ℕ), W.length = a + m → W'.length = b + m →
      (∀ w, W'.getD (rl a b f w) false = W.getD w false) →
      ∀ w, (run (gs.map (mg a b f)) W').getD (rl a b f w) false = (run gs W).getD w false := by
  induction gs with
  | nil => intro W W' m _ _ h; exact h
  | cons g gs ih =>
    intro W W' m hW hW' h
    rw [List.map_cons, run_cons, run_cons]
    have hv : (mg a b f g).op.eval ((mg a b f g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [mg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [hv]
    apply ih _ _ (m + 1) (by simp [hW]; omega) (by simp [hW']; omega)
    intro w
    rw [getD_app, getD_app]
    by_cases hw : w < a
    · have h1 : rl a b f w < W'.length := by
        simp only [rl, dif_pos hw]; have := (f ⟨w, hw⟩).isLt; omega
      rw [if_pos h1, if_pos (by omega)]
      exact h w
    · have hr : rl a b f w = w - a + b := by simp only [rl, dif_neg hw]
      rw [hr]
      rcases lt_trichotomy w (a + m) with h2 | h2 | h2
      · rw [if_pos (by omega), if_pos (by omega), ← hr]
        exact h w
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end PEqualNP.Outside.L_meta_4001_aux

theorem PEqualNP.Outside.L_meta_4001 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 : (Fin x1 → Bool) → Bool) (x5 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x5 → PEqualNP.MetaComplexity.HasCircuitSize x2 (fun (x7 : Fin x2 → Bool) => x4 fun (x8 : Fin x1) => x7 (x3 x8)) x5 := by
  intro x1 x2 x3 x4 x5 hC
  obtain ⟨C, hF, hs, he⟩ := hC
  refine ⟨⟨C.gates.map (L_meta_4001_aux.mg x1 x2 x3), L_meta_4001_aux.rl x1 x2 x3 C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hF g0 hg0).1, by simpa [L_meta_4001_aux.mg] using (hF g0 hg0).2⟩
  · simpa [Circuit.size] using hs
  · intro y
    show _ = x4 (fun i => y (x3 i))
    rw [← he (fun i => y (x3 i))]
    change (L_meta_4001_aux.run _ (List.ofFn y)).getD (L_meta_4001_aux.rl x1 x2 x3 C.output) false =
      (L_meta_4001_aux.run C.gates _).getD C.output false
    apply L_meta_4001_aux.key x1 x2 x3 C.gates _ _ 0 (by simp) (by simp)
    intro w
    by_cases hw : w < x1
    · simp only [L_meta_4001_aux.rl, dif_pos hw]
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · simp only [L_meta_4001_aux.rl, dif_neg hw]
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
