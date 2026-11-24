import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4827_aux

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

def rl (f : Fin 9 → Fin 9) (w : ℕ) : ℕ :=
  if h : w < 9 then (f ⟨w, h⟩ : ℕ) else w

def mg (f : Fin 9 → Fin 9) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rl f)⟩

theorem getD_app (L : List Bool) (v : Bool) (i : ℕ) :
    (L ++ [v]).getD i false =
      if i < L.length then L.getD i false else if i = L.length then v else false := by
  rcases lt_trichotomy i L.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem key (f : Fin 9 → Fin 9) (gs : List Gate) :
    ∀ (W W' : List Bool) (m : ℕ), W.length = 9 + m → W'.length = 9 + m →
      (∀ w, W'.getD (rl f w) false = W.getD w false) →
      ∀ w, (run (gs.map (mg f)) W').getD (rl f w) false = (run gs W).getD w false := by
  induction gs with
  | nil => intro W W' m _ _ h; exact h
  | cons g gs ih =>
    intro W W' m hW hW' h
    rw [List.map_cons, run_cons, run_cons]
    have hv : (mg f g).op.eval ((mg f g).inputs.map fun i => W'.getD i false) =
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
    by_cases hw : w < 9
    · have h1 : rl f w < W'.length := by
        simp only [rl, dif_pos hw]; have := (f ⟨w, hw⟩).isLt; omega
      rw [if_pos h1, if_pos (by omega)]
      exact h w
    · have hr : rl f w = w := by simp only [rl, dif_neg hw]
      rw [hr]
      rcases lt_trichotomy w (9 + m) with h2 | h2 | h2
      · rw [if_pos (by omega), if_pos (by omega)]
        have := h w
        rwa [hr] at this
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem rl_eq (f : Fin 9 → Fin 9) (hf : ∀ x, f (f x) = x) (x3 : Fin 9) (w : ℕ) :
    rl f w = ((f x3 : Fin 9) : ℕ) ↔ w = (x3 : ℕ) := by
  constructor
  · intro h
    by_cases hw : w < 9
    · simp only [rl, dif_pos hw] at h
      have h2 : f ⟨w, hw⟩ = f x3 := Fin.ext h
      have h3 := congrArg f h2
      rw [hf, hf] at h3
      rw [← h3]
    · simp only [rl, dif_neg hw] at h
      have := (f x3).isLt
      omega
  · rintro rfl
    simp [rl]

theorem mem_iff (f : Fin 9 → Fin 9) (hf : ∀ x, f (f x) = x) (x3 : Fin 9) (L : List ℕ) :
    ((f x3 : Fin 9) : ℕ) ∈ L.map (rl f) ↔ (x3 : ℕ) ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨w, hw, he⟩
    rw [rl_eq f hf] at he
    rw [← he]; exact hw
  · intro h
    exact ⟨_, h, (rl_eq f hf x3 _).2 rfl⟩

theorem get_map (f : Gate → Gate) (C : Circuit) (y : Fin (C.gates.map f).length)
    (h : y.1 < C.gates.length) : (C.gates.map f).get y = f (C.gates.get ⟨y.1, h⟩) := by
  simp

end PEqualNP.Outside.L_meta_4827_aux

theorem PEqualNP.Outside.L_meta_4827 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)) (x4 : Fin x1.size), (∀ (x5 : Fin (9 : ℕ)), x2 (x2 x5) = x5) → PEqualNP.MetaComplexity.FanInTwo x1 → (x1.gates.get x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x8 : Fin x1.size), ↑x3 ∈ (x1.gates.get x8).inputs ↔ x8 = x4) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin x9.size), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size = x1.size ∧ (∀ (x11 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x9 x11 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => x11 (x2 x12)) ∧ (x9.gates.get x10).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ (x11 : Fin x9.size), ↑(x2 x3) ∈ (x9.gates.get x11).inputs ↔ x11 = x10 := by
  intro x1 x2 x3 x4 hinv hF hop hocc
  refine ⟨⟨x1.gates.map (L_meta_4827_aux.mg x2), L_meta_4827_aux.rl x2 x1.output⟩,
    ⟨x4.1, by simpa [Circuit.size] using x4.2⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hF g0 hg0).1, by simpa [L_meta_4827_aux.mg] using (hF g0 hg0).2⟩
  · simp [Circuit.size]
  · intro y
    change (L_meta_4827_aux.run _ (List.ofFn y)).getD (L_meta_4827_aux.rl x2 x1.output) false =
      (L_meta_4827_aux.run x1.gates _).getD x1.output false
    apply L_meta_4827_aux.key x2 x1.gates _ _ 0 (by simp) (by simp)
    intro w
    by_cases hw : w < 9
    · simp only [L_meta_4827_aux.rl, dif_pos hw]
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_ofFn]
    · simp only [L_meta_4827_aux.rl, dif_neg hw]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro h
    apply hop
    have e := L_meta_4827_aux.get_map (L_meta_4827_aux.mg x2) x1
      ⟨x4.1, by simpa [Circuit.size] using x4.2⟩ x4.2
    exact (congrArg Gate.op e).symm.trans h
  · intro y
    have hy : y.1 < x1.size := by simpa [Circuit.size] using y.2
    have e := L_meta_4827_aux.get_map (L_meta_4827_aux.mg x2) x1 y hy
    have h1 := L_meta_4827_aux.mem_iff x2 hinv x3 (x1.gates.get ⟨y.1, hy⟩).inputs
    have h2 := hocc ⟨y.1, hy⟩
    refine Iff.trans ?_ (h1.trans (h2.trans ?_))
    · exact Iff.of_eq (congrArg (fun g => ((x2 x3 : Fin 9) : ℕ) ∈ g.inputs) e)
    · rw [Fin.ext_iff, Fin.ext_iff]
