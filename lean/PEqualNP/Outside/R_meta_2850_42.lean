import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2850_42
    (hrestrict : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) C.gates).length ≤ 1 →
      (∀ x : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => if i = 0 then !x 0 else x i) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
         x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size + 1 ≤ C.size ∧
        (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates).length ≤ 1 ∧
        ∀ y : Fin 8 → Bool,
          PEqualNP.MetaComplexity.circuitFun 8 D (fun i : Fin 8 => if i = 0 then !y 0 else y i) =
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
           y 2 && y 6 || y 3 && y 7 || y 5 && y 6 || y 7 && y 5))
    (hG6_not : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates).length ≤ 1 →
      (∀ g ∈ D.gates, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ y : Fin 8 → Bool,
        PEqualNP.MetaComplexity.circuitFun 8 D (fun i : Fin 8 => if i = 0 then !y 0 else y i) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
         y 2 && y 6 || y 3 && y 7 || y 5 && y 6 || y 7 && y 5))
    (hG6_and : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates).length ≤ 1 →
      (∀ g ∈ D.gates, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      ∃ y : Fin 8 → Bool,
        PEqualNP.MetaComplexity.circuitFun 8 D (fun i : Fin 8 => if i = 0 then !y 0 else y i) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
         y 2 && y 6 || y 3 && y 7 || y 5 && y 6 || y 7 && y 5))
    (hG6_or : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates).length ≤ 1 →
      (∀ g ∈ D.gates, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∃ y : Fin 8 → Bool,
        PEqualNP.MetaComplexity.circuitFun 8 D (fun i : Fin 8 => if i = 0 then !y 0 else y i) ≠
        (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 ||
         y 2 && y 6 || y 3 && y 7 || y 5 && y 6 || y 7 && y 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → x2 = Bool.true → ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro C x2 hfan hsize hfilt hx2
  subst hx2
  by_contra hnone
  push Not at hnone
  have hfun : ∀ x : Fin 9 → Bool,
      PEqualNP.MetaComplexity.circuitFun 9 C (fun i : Fin 9 => if i = 0 then !x 0 else x i) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
       x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    simpa [Bool.true_bne] using hnone x
  obtain ⟨D, hDfan, hDsz, hDfilt, hDfun⟩ := hrestrict C hfan hfilt hfun
  have hDle : D.size ≤ 13 := by omega
  cases hf : List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates with
  | nil =>
    have hall : ∀ g ∈ D.gates, g.inputs.contains 0 = true → g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg h0
      have hmem : g ∈ List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates :=
        List.mem_filter.mpr ⟨hg, h0⟩
      rw [hf] at hmem
      cases hmem
    obtain ⟨y, hy⟩ := hG6_not D hDfan hDle hDfilt hall
    exact hy (hDfun y)
  | cons g0 rest =>
    rw [hf, List.length_cons] at hDfilt
    have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrest
    have hDfilt' : (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates).length ≤ 1 := by
      rw [hf]; simp
    have hg0_mem : g0 ∈ D.gates := (List.mem_filter.mp (hf ▸ List.mem_cons_self)).1
    have huniq : ∀ g ∈ D.gates, g.inputs.contains 0 = true → g = g0 := by
      intro g hg h0
      have hmem : g ∈ List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.contains 0) D.gates :=
        List.mem_filter.mpr ⟨hg, h0⟩
      rw [hf] at hmem
      exact List.mem_singleton.mp hmem
    have hop := (hDfan g0 hg0_mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor | hnot
    · obtain ⟨y, hy⟩ := hG6_and D hDfan hDle hDfilt'
        (fun g hg h0 => by rw [huniq g hg h0, hand])
      exact hy (hDfun y)
    · obtain ⟨y, hy⟩ := hG6_or D hDfan hDle hDfilt'
        (fun g hg h0 => by rw [huniq g hg h0, hor])
      exact hy (hDfun y)
    · obtain ⟨y, hy⟩ := hG6_not D hDfan hDle hDfilt'
        (fun g hg h0 => by rw [huniq g hg h0, hnot])
      exact hy (hDfun y)
