import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3204
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

end PEqualNP.Outside.L_meta_3204

open PEqualNP.Outside.L_meta_3204 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3204 : ∀ (x1 : ℕ) (x2 : Equiv.Perm (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : List Bool), x5.eval (List.ofFn x6 ++ x7) = x3.eval ((List.ofFn fun (x8 : Fin x1) => x6 (x2 x8)) ++ x7) := by
  intro n σ C hC
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℕ, ρ = fun i => if h : i < n then ((σ ⟨i, h⟩ : Fin n) : ℕ) else i := ⟨_, rfl⟩
  have hlt : ∀ v (h : v < n), ρ v = ((σ ⟨v, h⟩ : Fin n) : ℕ) := by
    intro v h; rw [hρ]; simp [h]
  have hge : ∀ v, n ≤ v → ρ v = v := by
    intro v h; rw [hρ]; simp [Nat.not_lt.mpr h]
  have key : ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length → n ≤ U.length →
      (∀ v, U'.getD v false = U.getD (ρ v) false) →
      ∀ v, (wf gs U').getD v false
        = (wf (gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)) U).getD (ρ v) false := by
    intro gs
    induction gs with
    | nil => intro U U' _ _ h v; exact h v
    | cons g gs ih =>
      intro U U' hlen hn h v
      rw [List.map_cons, wf_cons, wf_cons]
      have hv : g.op.eval (g.inputs.map fun i => U'.getD i false)
          = (⟨g.op, g.inputs.map ρ⟩ : Gate).op.eval ((⟨g.op, g.inputs.map ρ⟩ : Gate).inputs.map fun i => U.getD i false) := by
        show _ = g.op.eval ((g.inputs.map ρ).map fun i => U.getD i false)
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      rw [← hv]
      refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ v
      intro t
      rcases Nat.lt_trichotomy t U'.length with ht | ht | ht
      · have h1 : ρ t < U.length := by
          by_cases htn : t < n
          · rw [hlt t htn]; have := (σ ⟨t, htn⟩).isLt; omega
          · rw [hge t (by omega)]; omega
        rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
        exact h t
      · subst ht
        rw [hge _ (by omega), getD_snoc_eq, ← hlen, getD_snoc_eq]
      · rw [hge _ (by omega), getD_snoc_gt _ _ _ ht, getD_snoc_gt _ _ _ (by omega)]
  refine ⟨⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), ρ C.output⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hC g0 hg0).1, by simpa using (hC g0 hg0).2⟩
  · intro x y
    show (wf (C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)) (List.ofFn x ++ y)).getD (ρ C.output) false
      = (wf C.gates ((List.ofFn fun (x8 : Fin n) => x (σ x8)) ++ y)).getD C.output false
    refine (key C.gates (List.ofFn x ++ y) ((List.ofFn fun (x8 : Fin n) => x (σ x8)) ++ y) (by simp) (by simp) ?_ C.output).symm
    intro v
    by_cases hvn : v < n
    · rw [hlt v hvn, List.getD_append _ _ _ _ (by simpa using hvn),
        List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, hvn]
    · rw [hge v (by omega), List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
