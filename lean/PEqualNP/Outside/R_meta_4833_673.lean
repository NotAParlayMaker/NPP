import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4833_673
    (normalize :
      ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 →
      (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (_ : Fin x1) => Bool.false) = Bool.false → ∃ (x5 :
      PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 ∧ x5.size ≤ x2.size ∧
      PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2)
    (lower :
      let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
      ∀ (v : Fin 11) (D : PEqualNP.CircuitLowerBounds.Circuit), v.val < 4 →
        PEqualNP.TopForm.IsAO2 10 D →
        (∀ x : Fin 10 → Bool, PEqualNP.MetaComplexity.circuitFun 10 D x =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (v.insertNth false x)) → 19 ≤ D.size) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)),
      ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 :
      ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8
      : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ),
      (9 : ℕ))];
    ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) →
      PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false →
      PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1
      ∅ x6) → (19 : ℕ) ≤ x3.size := by
  have removeInput : ∀ (n : ℕ) (v : Fin (n + 1)) (C : Circuit),
      Monotone2 C → ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
        ∀ x : Fin n → Bool, circuitFun n D x = circuitFun (n + 1) C (v.insertNth false x) := by
    intro n v C mono
    let cap := n + C.size
    let rename (i : ℕ) := if i = v.val then cap else if i < v.val then i else i - 1
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have readErase (w : List Bool) (hv : v.val < w.length)
        (bound : w.length ≤ cap + 1) (zero : w.getD v.val false = false) (i : ℕ) :
        (w.eraseIdx v.val).getD (rename i) false = w.getD i false := by
      by_cases eq : i = v.val
      · subst i
        have outside : (w.eraseIdx v.val).length ≤ cap := by
          rw [List.length_eraseIdx_of_lt hv]
          omega
        simp only [rename, ite_eq_left rfl]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside]
        exact zero.symm
      · by_cases lt : i < v.val
        · simp [rename, eq, List.getD_eq_getElem?_getD, List.getElem?_eraseIdx, lt]
        · have ge : v.val ≤ i - 1 := by omega
          have back : i - 1 + 1 = i := by omega
          simp [rename, eq, lt, List.getD_eq_getElem?_getD,
            List.getElem?_eraseIdx_of_ge ge, back]
    have run : ∀ (gs : List Gate) (w : List Bool), v.val < w.length →
        w.length + gs.length ≤ cap + 1 → w.getD v.val false = false →
        ((gs.map mapGate).foldl step (w.eraseIdx v.val)) =
          (gs.foldl step w).eraseIdx v.val := by
      intro gs
      induction gs with
      | nil => intro w hv bound zero; rfl
      | cons g gs ih =>
        intro w hv bound zero
        have values : g.inputs.map (fun i => (w.eraseIdx v.val).getD (rename i) false) =
            g.inputs.map (fun i => w.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact readErase w hv (by simpa using Nat.le_trans (Nat.le_add_right _ _) bound) zero i
        have one : step (w.eraseIdx v.val) (mapGate g) = (step w g).eraseIdx v.val := by
          simp only [step, mapGate, List.map_map, Function.comp_def]
          rw [values, List.eraseIdx_append_of_lt_length hv]
        simp only [List.map_cons, List.foldl_cons]
        rw [one]
        apply ih
        · simp only [step, List.length_append, List.length_singleton]
          omega
        · simp only [step, List.length_append, List.length_singleton]
          simp only [List.length_cons] at bound
          omega
        · change (w ++ _).getD v.val false = false
          rw [List.getD_append _ _ _ _ hv]
          exact zero
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨old, oldMem, rfl⟩ := List.mem_map.mp hg
      obtain ⟨op, arity⟩ := mono old oldMem
      exact ⟨op, by simpa [mapGate] using arity⟩
    · change (C.gates.map mapGate).length ≤ C.gates.length
      simp only [List.length_map, le_refl]
    · intro x
      let w := List.ofFn (v.insertNth false x)
      have hv : v.val < w.length := by simpa [w] using v.isLt
      have zero : w.getD v.val false = false := by
        change (List.ofFn (v.insertNth false x))[v.val]?.getD false = false
        rw [List.getElem?_ofFn]
        simp only [dite_eq_left v.isLt, Option.getD_some]
        exact Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => Bool) v false x
      have initial : w.eraseIdx v.val = List.ofFn x := by
        apply List.ext_getElem
        · simp only [List.length_eraseIdx_of_lt hv, w, List.length_ofFn]; omega
        · intro i hi hj
          have h : i < n := by simpa using hj
          let a : Fin n := ⟨i, h⟩
          have value := Fin.insertNth_apply_succAbove (α := fun _ : Fin (n + 1) => Bool) v false x a
          by_cases lt : i < v.val
          · have before : a.castSucc < v := lt
            rw [Fin.succAbove_of_castSucc_lt v a before] at value
            simp only [w, List.getElem_eraseIdx]
            rw [dite_eq_left lt]
            simp only [List.getElem_ofFn]
            exact value
          · have after : v ≤ a.castSucc := Nat.le_of_not_gt lt
            rw [Fin.succAbove_of_le_castSucc v a after] at value
            simp only [w, List.getElem_eraseIdx]
            rw [dite_eq_right lt]
            simp only [List.getElem_ofFn]
            exact value
      have bound : w.length + C.gates.length ≤ cap + 1 := by
        change (List.ofFn (v.insertNth false x)).length + C.gates.length ≤
          n + C.gates.length + 1
        rw [List.length_ofFn]
        omega
      have traced := run C.gates w hv bound zero
      change ((C.gates.map mapGate).foldl step (List.ofFn x)).getD (rename C.output) false =
        (C.gates.foldl step w).getD C.output false
      rw [← initial, traced]
      have lengthRun : ∀ (gs : List Gate) (ws : List Bool),
          (gs.foldl step ws).length = ws.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro ws; rfl
        | cons g gs ih =>
          intro ws
          rw [List.foldl_cons, ih]
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
      apply readErase
      · rw [lengthRun]; omega
      · rw [lengthRun]; exact bound
      · have old : ∀ (gs : List Gate) (w : List Bool), v.val < w.length →
            (gs.foldl step w).getD v.val false = w.getD v.val false := by
          intro gs
          induction gs with
          | nil => intro w hv; rfl
          | cons g gs ih =>
            intro w hv
            rw [List.foldl_cons, ih]
            · exact List.getD_append _ _ _ _ hv
            · simp [step]; omega
        rw [old C.gates w hv]
        exact zero
  intro G v C hv ao agree
  have mono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    have hop := ao.1 g hg
    have hlen := ao.2.2 g hg
    exact ⟨by simpa using hop, by omega⟩
  obtain ⟨D, dmono, dsize, eval⟩ := removeInput 10 v C mono
  have computes (x : Fin 10 → Bool) : PEqualNP.MetaComplexity.circuitFun 10 D x =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (v.insertNth false x) :=
    (eval x).trans (agree _ (Fin.insertNth_apply_same _ _ _))
  have zero : v.insertNth false (fun _ : Fin 10 => false) = (fun _ : Fin 11 => false) := by
    funext i
    induction i using Fin.succAboveCases v
    · exact Fin.insertNth_apply_same _ _ _
    · exact Fin.insertNth_apply_succAbove _ _ _ _
  have outFalse : PEqualNP.MetaComplexity.circuitFun 10 D (fun _ => false) = false := by
    rw [computes, zero]
    delta PEqualNP.MetaComplexity.NestedCover.graphFun
    simp
  obtain ⟨E, eao, esize, same⟩ := normalize 10 D dmono outFalse
  exact (lower v E hv eao (fun x => (congrFun same x).trans (computes x))).trans (esize.trans dsize)
