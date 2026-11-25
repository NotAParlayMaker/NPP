import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8295

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_length (G : List Gate) :
    ∀ x : List Bool, (G.foldl stepB x).length = x.length + G.length := by
  induction G with
  | nil => intro x; rfl
  | cons g t ih =>
    intro x
    rw [List.foldl_cons, ih]
    simp only [stepB, List.length_append, List.length_cons, List.length_nil]
    omega

theorem split_last (l : List Gate) (h : ∃ g ∈ l, g.op = GateOp.not) :
    ∃ (A : List Gate) (g : Gate) (B : List Gate),
      l = A ++ g :: B ∧ g.op = GateOp.not ∧ ∀ b ∈ B, b.op ≠ GateOp.not := by
  induction l with
  | nil =>
    obtain ⟨g, hg, _⟩ := h
    simp at hg
  | cons a t ih =>
    by_cases ht : ∃ g ∈ t, g.op = GateOp.not
    · obtain ⟨A, g, B, hl, hg, hB⟩ := ih ht
      exact ⟨a :: A, g, B, by rw [hl]; rfl, hg, hB⟩
    · obtain ⟨g, hg, hgn⟩ := h
      rcases List.mem_cons.1 hg with hga | hg2
      · rw [hga] at hgn
        exact ⟨[], a, t, rfl, hgn, fun b hb hbn => ht ⟨b, hb, hbn⟩⟩
      · exact absurd ⟨g, hg2, hgn⟩ ht

theorem main (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ (C5 : Circuit) (C6 : Circuit), PEqualNP.MetaComplexity.FanInTwo C5 ∧
      PEqualNP.MetaComplexity.Monotone2 C6 ∧ C5.size + C6.size + (1 : ℕ) = C.size ∧
      ∀ (x : Fin n → Bool), C.eval (List.ofFn x)
        = C6.eval (C5.wires (List.ofFn x) ++ [!C5.eval (List.ofFn x)]) := by
  obtain ⟨A, g, B, hl, hg, hB⟩ := split_last C.gates h
  have hA : ∀ a ∈ A, a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      a.inputs.length ≤ 2 := fun a ha => hC a (by rw [hl]; simp [ha])
  have hBm : ∀ b ∈ B, b.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ b.inputs.length ≤ 2 := by
    intro b hb
    have hb2 := hC b (by rw [hl]; simp [hb])
    refine ⟨?_, hb2.2⟩
    rcases hb2.1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 (hB b hb)
  refine ⟨⟨A, g.inputs.headD (n + A.length)⟩, ⟨B, C.output⟩, hA, hBm, ?_, ?_⟩
  · show A.length + B.length + 1 = C.gates.length
    rw [hl]
    simp only [List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (A.foldl stepB (List.ofFn x)).length = n + A.length := by
      rw [wires_length, List.length_ofFn]
    have hout : (A.foldl stepB (List.ofFn x)).getD (n + A.length) false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (le_of_eq hlen)]
      rfl
    have key : g.op.eval (g.inputs.map fun i => (A.foldl stepB (List.ofFn x)).getD i false)
        = !((A.foldl stepB (List.ofFn x)).getD (g.inputs.headD (n + A.length)) false) := by
      rw [hg]
      show (!((g.inputs.map fun i => (A.foldl stepB (List.ofFn x)).getD i false).headD false)) = _
      cases hi : g.inputs with
      | nil =>
        have hout2 := hout
        rw [List.getD_eq_getElem?_getD] at hout2
        simp [hout2]
      | cons i t => simp
    show (C.gates.foldl stepB (List.ofFn x)).getD C.output false
      = (B.foldl stepB ((A.foldl stepB (List.ofFn x)) ++
          [!((A.foldl stepB (List.ofFn x)).getD (g.inputs.headD (n + A.length)) false)])).getD
          C.output false
    rw [hl, List.foldl_append, List.foldl_cons, ← key]
    rfl

end PEqualNP.Outside.L_meta_8295

theorem PEqualNP.Outside.L_meta_8295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ x4 ∈ x2.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ x5.size + x6.size + (1 : ℕ) = x2.size ∧ ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x6.eval (x5.wires (List.ofFn x7) ++ [!x5.eval (List.ofFn x7)]) := by
  intro x1 x2 h1 h2
  exact PEqualNP.Outside.L_meta_8295.main x1 x2 h1 h2
