import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The vertices of each degree form a single orbit. One negated input of each degree suffices.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3143_28
    (degreeTwo : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!(x 0),true,false]) =
        ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any (fun e => x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e%10)))) → 13 ≤ C.size)
    (degreeThree : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!(x 1),true,false]) =
        ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any (fun e => x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e%10)))) → 13 ≤ C.size) :
  ∀ (x1 : Fin (8 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 x1, Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size := by
  let mapGate (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let rewired (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate σ),σ C.output⟩

  have fan {C : Circuit} (σ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (rewired σ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h a ha).1,by simpa [mapGate] using (h a ha).2⟩

  have run {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (gs : List Gate) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires y).getD (σ i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map (fun i => x.getD i false))
      have same : (mapGate σ g).op.eval ((mapGate σ g).inputs.map (fun i => y.getD i false)) = b := by
        simp only [b,mapGate,List.map_map,Function.comp_def,agree]
      change ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires (y++[_])).getD (σ i) false =
        ((Circuit.mk gs 0).wires (x++[b])).getD i false
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i<x.length
      · have hsi : σ i<y.length := by
          by_cases hr : i<cut
          · have := raw i hr; omega
          · rw [later i (by omega)]; omega
        rw [List.getD_append _ _ _ _ hsi, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [later i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]

  have evalMap {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (C : Circuit) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      (rewired σ C).eval y = C.eval x :=
    run σ raw later C.gates x y len lo agree C.output

  let rawMap (p : Fin 8 → Fin 8) (i : ℕ) := if h : i < 8 then (p ⟨i,h⟩).val else i
  let target := fun (x : Fin 8 → Bool) => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any (fun e => x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e%10)))
  intro j C hf computes
  change ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!(x j),true,false]) = target x at computes
  have transport (p : Fin 8 → Fin 8) (r : Fin 8) (hj : p j = r)
      (symm : ∀ x, target (x ∘ p) = target x)
      (bound : ∀ D : Circuit, FanInTwo D →
        (∀ x : Fin 8 → Bool, D.eval (List.ofFn x ++ [!(x r),true,false]) = target x) → 13 ≤ D.size) :
      13 ≤ C.size := by
    let σ := rawMap p
    have small (i : ℕ) (h : i < 8) : σ i < 8 := by simp [σ,rawMap,h]
    have late (i : ℕ) (h : 8 ≤ i) : σ i = i := by simp [σ,rawMap,Nat.not_lt.mpr h]
    have hb := bound (rewired σ C) (fan σ hf) (by
      intro x
      rw [← symm x, ← computes (x ∘ p)]
      simp only [Function.comp_apply,hj]
      apply evalMap σ small late C _ _ (by simp) (by simp)
      intro i
      by_cases h : i < 8
      · have h1 : σ i < (List.ofFn x).length := by simpa using small i h
        have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using h
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
          List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2]
        simp only [List.getElem_ofFn,Function.comp_apply]
        congr 1
        apply Fin.ext
        exact dite_eq_left h
      · have hn : 8 ≤ i := by omega
        rw [late i hn, List.getD_append_right _ _ _ _ (by simpa using hn),
          List.getD_append_right _ _ _ _ (by simpa using hn)]
        simp)
    change 13 ≤ (C.gates.map (mapGate σ)).length at hb
    rw [List.length_map] at hb
    exact hb
  fin_cases j
  · exact degreeTwo C hf computes
  · exact degreeThree C hf computes
  · apply transport (![3, 2, 1, 0, 7, 6, 5, 4] : Fin 8 → Fin 8) 1 rfl _ degreeThree
    intro x
    change (((x 3 && x 2) || ((x 2 && x 1) || ((x 1 && x 0) || ((x 3 && x 7) || ((x 2 && x 6) || ((x 1 && x 5) || ((x 0 && x 4) || ((x 7 && x 5) || ((x 6 && x 4) || ((x 4 && x 7) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
  · apply transport (![3, 2, 1, 0, 7, 6, 5, 4] : Fin 8 → Fin 8) 0 rfl _ degreeTwo
    intro x
    change (((x 3 && x 2) || ((x 2 && x 1) || ((x 1 && x 0) || ((x 3 && x 7) || ((x 2 && x 6) || ((x 1 && x 5) || ((x 0 && x 4) || ((x 7 && x 5) || ((x 6 && x 4) || ((x 4 && x 7) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
  · apply transport (![0, 4, 7, 3, 1, 6, 5, 2] : Fin 8 → Fin 8) 1 rfl _ degreeThree
    intro x
    change (((x 0 && x 4) || ((x 4 && x 7) || ((x 7 && x 3) || ((x 0 && x 1) || ((x 4 && x 6) || ((x 7 && x 5) || ((x 3 && x 2) || ((x 1 && x 5) || ((x 6 && x 2) || ((x 2 && x 1) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
  · apply transport (![5, 1, 2, 6, 7, 0, 3, 4] : Fin 8 → Fin 8) 0 rfl _ degreeTwo
    intro x
    change (((x 5 && x 1) || ((x 1 && x 2) || ((x 2 && x 6) || ((x 5 && x 7) || ((x 1 && x 0) || ((x 2 && x 3) || ((x 6 && x 4) || ((x 7 && x 3) || ((x 0 && x 4) || ((x 4 && x 7) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
  · apply transport (![5, 7, 4, 6, 1, 3, 0, 2] : Fin 8 → Fin 8) 0 rfl _ degreeTwo
    intro x
    change (((x 5 && x 7) || ((x 7 && x 4) || ((x 4 && x 6) || ((x 5 && x 1) || ((x 7 && x 3) || ((x 4 && x 0) || ((x 6 && x 2) || ((x 1 && x 0) || ((x 3 && x 2) || ((x 2 && x 1) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
  · apply transport (![3, 7, 4, 0, 2, 5, 6, 1] : Fin 8 → Fin 8) 1 rfl _ degreeThree
    intro x
    change (((x 3 && x 7) || ((x 7 && x 4) || ((x 4 && x 0) || ((x 3 && x 2) || ((x 7 && x 5) || ((x 4 && x 6) || ((x 0 && x 1) || ((x 2 && x 6) || ((x 5 && x 1) || ((x 1 && x 2) || false))))))))))) =
      (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false)))))))))))
    ac_rfl
