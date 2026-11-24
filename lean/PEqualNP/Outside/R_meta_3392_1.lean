import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3392_1
    (hRest : ∀ b ∈ ([1, 2, 3, 6] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hNot : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))] ++ [x6 (4 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro b hb C hF hsz
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 6 := by
    simpa [List.mem_cons, List.mem_singleton] using hb
  rcases hb' with rfl | rfl | rfl | rfl | rfl
  · exact hRest 1 (by decide) C hF hsz
  · exact hRest 2 (by decide) C hF hsz
  · exact hRest 3 (by decide) C hF hsz
  · let φ (i : ℕ) : ℕ := if i = 10 then 4 else if 10 < i then i - 1 else i
    let mapG (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩
    let C' : Circuit := ⟨C.gates.map mapG, φ C.output⟩
    have hF' : FanInTwo C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      obtain ⟨hop, hlen⟩ := hF g0 hg0
      exact ⟨hop, by simpa [mapG] using hlen⟩
    have hsz' : C'.size ≤ 13 := by
      simpa [C', Circuit.size] using hsz
    obtain ⟨x, hx⟩ := hNot C' hF' hsz'
    have agree : ∀ (gs : List Gate) (wL wS : List Bool),
        wS.length + 1 = wL.length → 10 ≤ wS.length →
        (∀ i, wL.getD i false = wS.getD (φ i) false) →
        ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) wL).getD i false =
          ((gs.map mapG).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) wS).getD (φ i) false := by
      intro gs
      induction gs with
      | nil =>
        intro wL wS _ _ hinv i
        simp only [List.foldl_nil, List.map_nil]
        exact hinv i
      | cons g gs ih =>
        intro wL wS hlen hbase hinv i
        have hreads : g.inputs.map (fun j => wL.getD j false) =
            g.inputs.map (fun j => wS.getD (φ j) false) := by
          apply List.map_congr_left
          intro j _
          exact hinv j
        have hv : g.op.eval (g.inputs.map fun j => wL.getD j false) =
            g.op.eval ((mapG g).inputs.map fun j => wS.getD j false) := by
          simp only [mapG]
          rw [List.map_map]
          exact congrArg g.op.eval hreads
        let v := g.op.eval (g.inputs.map fun j => wL.getD j false)
        have hφlt : ∀ i, i < wL.length → φ i < wS.length := by
          intro i hi
          by_cases h10 : i = 10
          · simp [φ, h10]
            omega
          · by_cases hgt : 10 < i
            · simp [φ, h10, hgt]
              omega
            · simp [φ, h10, hgt]
              omega
        have hinv' : ∀ i, (wL ++ [v]).getD i false = (wS ++ [v]).getD (φ i) false := by
          intro i
          by_cases hi : i < wL.length
          · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hφlt i hi)]
            exact hinv i
          · have hge : wL.length ≤ i := Nat.le_of_not_gt hi
            by_cases heq : i = wL.length
            · subst heq
              have hbig : 10 < wL.length := by omega
              have hφn : φ wL.length = wS.length := by
                have hsub : wL.length - 1 = wS.length := by omega
                have hne : wL.length ≠ 10 := by omega
                simp [φ, hne, hbig, hsub]
              rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
              rw [hφn, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
            · have hbig : 10 < i := by omega
              have hpast : wL.length + 1 ≤ i := by omega
              rw [show φ i = i - 1 by
                have hne : i ≠ 10 := by omega
                simp [φ, hne, hbig]]
              rw [List.getD_append_right _ _ _ _ hge]
              rw [List.getD_eq_default _ _ (by simp; omega)]
              rw [List.getD_append_right _ _ _ _ (show wS.length ≤ i - 1 by omega)]
              rw [List.getD_eq_default _ _ (by simp; omega)]
        have hlen' : (wS ++ [v]).length + 1 = (wL ++ [v]).length := by simp [hlen]
        have hbase' : 10 ≤ (wS ++ [v]).length := by simp; omega
        simp only [List.foldl_cons, List.map_cons]
        rw [← hv]
        exact ih (wL ++ [v]) (wS ++ [v]) hlen' hbase' hinv' i
    let L0 : List Bool := List.ofFn x ++ [!x 0]
    let L : List Bool := L0 ++ [x 4 || x 4]
    have hL0 : L0.length = 10 := by simp [L0]
    have h4 : L0.getD 4 false = x 4 := by
      have hlt : 4 < (List.ofFn x).length := by simp
      rw [show L0 = List.ofFn x ++ [!x 0] from rfl, List.getD_append _ _ _ _ hlt,
        List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]
      rfl
    have hinv0 : ∀ i, L.getD i false = L0.getD (φ i) false := by
      intro i
      by_cases h10 : i = 10
      · subst h10
        rw [show φ 10 = 4 by unfold φ; rfl]
        rw [List.getD_append_right (l := L0) (l' := [x 4 || x 4]) (d := false) (n := 10) (by simp [hL0])]
        have hzero : 10 - L0.length = 0 := by simp [hL0]
        rw [hzero, List.getD_cons_zero, Bool.or_self]
        exact h4.symm
      · by_cases hgt : 10 < i
        · rw [show φ i = i - 1 by simp [φ, h10, hgt]]
          have hLlen : L.length = 11 := by simp [L, hL0]
          rw [List.getD_eq_default (l := L) (d := false) (n := i) (by simp [hLlen]; omega)]
          rw [List.getD_eq_default (l := L0) (d := false) (n := i - 1) (by simp [hL0]; omega)]
        · have hi : i < 10 := by omega
          rw [show φ i = i by simp [φ, h10, hgt]]
          rw [List.getD_append (l := L0) (l' := [x 4 || x 4]) (d := false) (n := i) (by simp [hL0]; omega)]
    have hlen0 : L0.length + 1 = L.length := by simp [L]
    have heval : C.eval L = C'.eval L0 := by
      simp only [Circuit.eval, Circuit.wires, C']
      exact agree C.gates L L0 hlen0 (by simp [hL0]) hinv0 C.output
    refine ⟨x, ?_⟩
    rw [heval]
    simpa [L0, Bool.or_self] using hx
  · exact hRest 6 (by decide) C hF hsz
