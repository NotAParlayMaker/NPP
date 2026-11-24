import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4506

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    have hstep : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hstep, ih]
    simp
    omega

-- Wire m is the constant false wire: it is renamed to a wire N that never exists, and the
-- wires after it move down by one.
def sg (m N i : ℕ) : ℕ := if i < m then i else if i = m then N else i - 1

def ren (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

lemma key (W t : List Bool) (N i : ℕ) (hN : W.length + t.length ≤ N) :
    (W ++ t).getD (sg W.length N i) false = (W ++ false :: t).getD i false := by
  unfold sg
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1]
  · subst h2
    rw [List.getD_eq_default _ _ (by rw [List.length_append]; exact hN),
      List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · have h3 : W.length < i := by omega
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, i - W.length = d + 1 := ⟨i - W.length - 1, by omega⟩
    rw [hd, List.getD_cons_succ]
    congr 1
    omega

lemma run (N : ℕ) (W : List Bool) : ∀ (B : List Gate) (t : List Bool),
    W.length + t.length + B.length ≤ N →
    ∃ t' : List Bool, wiresFrom B (W ++ false :: t) = W ++ false :: t' ∧
      wiresFrom (B.map (ren (sg W.length N))) (W ++ t) = W ++ t' ∧
      t'.length = t.length + B.length := by
  intro B
  induction B with
  | nil => intro t _; exact ⟨t, rfl, rfl, by simp⟩
  | cons g B ih =>
    intro t hN
    simp only [List.length_cons] at hN
    obtain ⟨t', h1, h2, h3⟩ := ih (t ++ [g.op.eval (g.inputs.map fun i =>
      (W ++ false :: t).getD i false)]) (by simp; omega)
    refine ⟨t', ?_, ?_, by simp at h3; simp; omega⟩
    · have hstep : wiresFrom (g :: B) (W ++ false :: t) =
          wiresFrom B ((W ++ false :: t) ++ [g.op.eval (g.inputs.map fun i =>
            (W ++ false :: t).getD i false)]) := rfl
      rw [hstep, ← h1]
      simp
    · have hstep : wiresFrom ((g :: B).map (ren (sg W.length N))) (W ++ t) =
          wiresFrom (B.map (ren (sg W.length N))) ((W ++ t) ++
            [g.op.eval ((g.inputs.map (sg W.length N)).map fun i => (W ++ t).getD i false)]) := rfl
      rw [hstep, ← h2, List.map_map]
      have hv : (g.inputs.map ((fun i => (W ++ t).getD i false) ∘ sg W.length N)) =
          (g.inputs.map fun i => (W ++ false :: t).getD i false) := by
        apply List.map_congr_left
        intro i _
        exact key W t N i (by omega)
      rw [hv]
      simp

theorem glue (n : ℕ) (C1 C2 : Circuit) (h1 : FanInTwo C1) (h2 : FanInTwo C2) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ C1.size + C2.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = C2.eval (C1.wires (List.ofFn x) ++ [false]) := by
  refine ⟨⟨C1.gates ++ C2.gates.map (ren (sg (n + C1.gates.length) (n + C1.gates.length + C2.gates.length))),
    sg (n + C1.gates.length) (n + C1.gates.length + C2.gates.length) C2.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      have := h2 g0 hg0
      exact ⟨this.1, by simpa [ren] using this.2⟩
  · simp [Circuit.size]
  · intro x
    have hlen : (wiresFrom C1.gates (List.ofFn x)).length = n + C1.gates.length := by
      rw [length_wiresFrom]; simp
    obtain ⟨t', e1, e2, e3⟩ := run (n + C1.gates.length + C2.gates.length)
      (wiresFrom C1.gates (List.ofFn x)) C2.gates [] (by rw [hlen]; simp)
    rw [hlen] at e2
    show (wiresFrom (C1.gates ++ _) (List.ofFn x)).getD _ false =
      (wiresFrom C2.gates (wiresFrom C1.gates (List.ofFn x) ++ [false])).getD C2.output false
    rw [wiresFrom_append, e1]
    have e2' := e2
    simp only [List.append_nil] at e2'
    rw [e2']
    have hk := key (wiresFrom C1.gates (List.ofFn x)) t'
      (n + C1.gates.length + C2.gates.length) C2.output (by rw [hlen]; simp at e3; omega)
    rw [hlen] at hk
    exact hk

end PEqualNP.Outside.L_meta_4506

theorem PEqualNP.Outside.L_meta_4506 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x5 : Fin (8 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x5) ++ [Bool.false]) = (x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) → Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ))) (x1.size + x2.size) := by
  intro x1 x2 h1 h2 hf
  obtain ⟨C, hC, hs, he⟩ := PEqualNP.Outside.L_meta_4506.glue 8 x1 x2 h1 h2
  exact ⟨C, hC, hs, fun x => (he x).trans (hf x)⟩
