import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_2114_1
    (cofactor : ¬ HasCircuitSize (8 : ℕ)
        (fun x : Fin (8 : ℕ) → Bool =>
          (x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ))) ||
          (x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ))) ||
          (x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ))) ||
          (x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))) ||
          (x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ))) ||
          (x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ))) ||
          (x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ))) ||
          (x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ))) ||
          (x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ))) ||
          (x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)))) (12 : ℕ))
    (drop3 : ∀ (C : Circuit) (v : Fin (9 : ℕ)),
        FanInTwo C →
        circuitFun (9 : ℕ) C =
          (fun x : Fin (9 : ℕ) → Bool =>
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ))) ||
            (x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ))) ||
            (x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ))) ||
            (x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ))) ||
            (x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ))) ||
            (x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) ||
            (x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ))) ||
            (x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ))) ||
            (x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ))) ||
            (x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ))) ||
            (x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ))) ||
            (x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) →
        (v = (4 : Fin (9 : ℕ)) ∨ v = (6 : Fin (9 : ℕ)) ∨ v = (7 : Fin (9 : ℕ))) →
        (Finset.card {i : Fin C.size | (v : ℕ) ∈ (C.gates.get i).inputs} = (2 : ℕ)) →
        (∀ i : Fin C.size, (v : ℕ) ∈ (C.gates.get i).inputs →
          (C.gates.get i).op = GateOp.or) →
        HasCircuitSize (8 : ℕ)
          (fun y : Fin (8 : ℕ) → Bool => circuitFun (9 : ℕ) C (Fin.insertNth v false y))
          (C.size - (3 : ℕ))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x7 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x7).card = (2 : ℕ)) → False := by
  intro x1 x2 x3 C hC hReaders hDouble
  let t : (Fin (8 : ℕ) → Bool) → Bool := fun x =>
    (x (0 : Fin (8 : ℕ)) && x (1 : Fin (8 : ℕ))) ||
    (x (1 : Fin (8 : ℕ)) && x (2 : Fin (8 : ℕ))) ||
    (x (2 : Fin (8 : ℕ)) && x (3 : Fin (8 : ℕ))) ||
    (x (0 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ))) ||
    (x (1 : Fin (8 : ℕ)) && x (5 : Fin (8 : ℕ))) ||
    (x (2 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ))) ||
    (x (3 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ))) ||
    (x (4 : Fin (8 : ℕ)) && x (6 : Fin (8 : ℕ))) ||
    (x (5 : Fin (8 : ℕ)) && x (7 : Fin (8 : ℕ))) ||
    (x (7 : Fin (8 : ℕ)) && x (4 : Fin (8 : ℕ)))
  have hfan : FanInTwo C := hC.1.1
  have hsize : C.size ≤ (15 : ℕ) := hC.2.1
  have hfunC : circuitFun (9 : ℕ) C = x1 := hC.2.2.1
  obtain ⟨v, hvmem, hcard⟩ := hDouble
  have hv : v = (4 : Fin (9 : ℕ)) ∨ v = (6 : Fin (9 : ℕ)) ∨ v = (7 : Fin (9 : ℕ)) := by
    simpa [List.mem_cons, List.mem_singleton] using hvmem
  have hall : ∀ i : Fin C.size, (v : ℕ) ∈ (C.gates.get i).inputs →
      (C.gates.get i).op = GateOp.or := by
    intro i hi
    have hi' : i ∈ x2 C v := by
      simpa [x2, Finset.mem_filter] using hi
    exact hReaders v hvmem i hi'
  obtain ⟨E, hEf, hEs, hEe⟩ := drop3 C v hfan hfunC hv hcard hall
  let p6 : Fin (8 : ℕ) → Fin (8 : ℕ) := fun i => Fin.ofNat (8 : ℕ) <|
    match i.1 with
    | 0 => 1
    | 1 => 0
    | 2 => 4
    | 3 => 7
    | 4 => 5
    | 5 => 2
    | 6 => 6
    | 7 => 3
    | _ => 0
  let p7 : Fin (8 : ℕ) → Fin (8 : ℕ) := fun i => Fin.ofNat (8 : ℕ) <|
    match i.1 with
    | 0 => 1
    | 1 => 2
    | 2 => 3
    | 3 => 7
    | 4 => 5
    | 5 => 0
    | 6 => 6
    | 7 => 4
    | _ => 0
  let p : Fin (8 : ℕ) → Fin (8 : ℕ) :=
    if v = (6 : Fin (9 : ℕ)) then p6 else if v = (7 : Fin (9 : ℕ)) then p7 else id
  have hagree : ∀ z : Fin (8 : ℕ) → Bool,
      x1 (Fin.insertNth v false (fun i => z (p i))) = t z := by
    rcases hv with rfl | rfl | rfl
    · decide
    · decide
    · decide
  let remap : ℕ → ℕ := fun i => if h : i < 8 then (p ⟨i, h⟩).1 else i
  let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map remap⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have append_getD (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false =
        if i < w.length then w.getD i false else if i = w.length then b else false := by
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : i < w.length
    · rw [List.getElem?_append_left hi]
      simp [hi, List.getD_eq_getElem?_getD]
    · by_cases he : i = w.length
      · subst he
        have hidx : (w ++ [b])[w.length]? = some b := by
          rw [List.getElem?_append_right (Nat.le_refl _)]
          simp
        simp
      · have hlt : w.length < i := by omega
        have hnone : (w ++ [b])[i]? = none := by
          rw [List.getElem?_eq_none]
          simp
          omega
        simp [hnone, hi, he]
  have ofFn_getD (x : Fin (8 : ℕ) → Bool) (i : ℕ) :
      (List.ofFn x).getD i false = if h : i < 8 then x ⟨i, h⟩ else false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases h : i < 8
    · simp [h]
    · simp [h]
  have remap_lt (i : ℕ) (hi : i < 8) : remap i = (p ⟨i, hi⟩).1 := by
    simp [remap, hi]
  have remap_ge (i : ℕ) (hi : ¬ i < 8) : remap i = i := by
    simp [remap, hi]
  have fold_rel (gs : List Gate) (w z : List Bool)
      (hlen : w.length = z.length) (h8 : (8 : ℕ) ≤ z.length)
      (hinv : ∀ i, w.getD i false = z.getD (remap i) false) :
      ∀ i, (gs.foldl step w).getD i false =
        ((gs.map rename).foldl step z).getD (remap i) false := by
    induction gs generalizing w z with
    | nil =>
      intro i
      simpa using hinv i
    | cons g gs ih =>
      intro i
      rw [List.foldl_cons, List.map_cons, List.foldl_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro j
        have hb : g.op.eval (g.inputs.map fun k => w.getD k false) =
            g.op.eval ((rename g).inputs.map fun k => z.getD k false) := by
          simp only [rename, List.map_map]
          congr 1
          apply List.map_congr_left
          intro k _
          exact hinv k
        rw [append_getD, append_getD, hb]
        by_cases hj : j < w.length
        · have hremap : remap j < z.length := by
            by_cases hsmall : j < 8
            · rw [remap_lt j hsmall]
              exact lt_of_lt_of_le (p ⟨j, hsmall⟩).2 h8
            · rw [remap_ge j hsmall]
              rw [hlen] at hj
              exact hj
          rw [ite_eq_left hj, ite_eq_left hremap]
          exact hinv j
        · rw [ite_eq_right hj]
          by_cases he : j = w.length
          · have hge : ¬ j < 8 := by
              intro hsmall
              exact hj (lt_of_lt_of_le hsmall (by omega))
            have hre : remap j = z.length := by
              rw [remap_ge j hge, he, hlen]
            have hnot : ¬ remap j < z.length := by
              rw [hre]
              exact lt_irrefl _
            rw [ite_eq_left he, ite_eq_right hnot, ite_eq_left hre]
          · have hgt : w.length < j := by omega
            have hge : ¬ j < 8 := by
              intro hsmall
              have h8w : (8 : ℕ) ≤ w.length := by omega
              omega
            have hre : z.length < remap j := by
              rw [remap_ge j hge, ← hlen]
              exact hgt
            have hne : remap j ≠ z.length := by omega
            rw [ite_eq_right he, ite_eq_right (not_lt_of_gt hre), ite_eq_right hne]
  have init_inv (z : Fin (8 : ℕ) → Bool) (i : ℕ) :
      (List.ofFn (fun j => z (p j))).getD i false =
        (List.ofFn z).getD (remap i) false := by
    rw [ofFn_getD, ofFn_getD]
    by_cases hi : i < 8
    · rw [remap_lt i hi]
      simp [hi, (p ⟨i, hi⟩).2]
    · rw [remap_ge i hi]
      simp [hi]
  let D : Circuit := ⟨E.gates.map rename, remap E.output⟩
  have hDf : FanInTwo D := by
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rename] using hEf g0 hg0
  have hDs : D.size ≤ (12 : ℕ) := by
    have hlen : D.size = E.size := by simp [D, Circuit.size]
    have hsub : C.size - (3 : ℕ) ≤ (12 : ℕ) := by omega
    omega
  have hDt : ∀ z : Fin (8 : ℕ) → Bool, D.eval (List.ofFn z) = t z := by
    intro z
    have hwire : ∀ i, (E.gates.foldl step (List.ofFn (fun j => z (p j)))).getD i false =
        (D.gates.foldl step (List.ofFn z)).getD (remap i) false := by
      simpa [D, rename] using
        fold_rel E.gates (List.ofFn (fun j => z (p j))) (List.ofFn z)
          (by simp) (by simp) (init_inv z)
    have hEv : D.eval (List.ofFn z) =
        E.eval (List.ofFn (fun j => z (p j))) := by
      simp only [Circuit.eval, Circuit.wires, D]
      exact (hwire E.output).symm
    rw [hEv, hEe (fun j => z (p j))]
    change circuitFun (9 : ℕ) C (Fin.insertNth v false (fun j => z (p j))) = t z
    rw [hfunC]
    exact hagree z
  exact cofactor ⟨D, hDf, hDs, hDt⟩
