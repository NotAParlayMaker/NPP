import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The input wire relabeling argument is adapted from the checked L_meta_735.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_3143_97
  (h0 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 (0 : Fin 8), Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size)
  (h1 : ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 (1 : Fin 8), Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size) :
  ∀ (x1 : Fin (8 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 x1, Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size := by
  let edge : (Fin 8 → Bool) → Bool := fun x =>
    ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
      (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
  let p : Fin 8 → Fin 8 → Fin 8 := ![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 4, 7, 3, 1, 6, 5, 2], ![5, 1, 2, 6, 7, 0, 3, 4], ![5, 7, 4, 6, 1, 3, 0, 2], ![3, 7, 4, 0, 2, 5, 6, 1]]
  let r : Fin 8 → Fin 8 := ![0, 1, 1, 0, 1, 0, 0, 1]
  have hr : ∀ j, r j = 0 ∨ r j = 1 := by decide +kernel
  have hp : ∀ j, p j j = r j := by decide +kernel
  let edges : List (Fin 8 × Fin 8) :=
    [(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)]
  have decode : ([1,12,23,4,15,26,37,46,57,74] : List ℕ).map
      (fun e => (Fin.ofNat 8 (e / 10), Fin.ofNat 8 (e % 10))) = edges := by decide +kernel
  have edge_eq (x : Fin 8 → Bool) : edge x = edges.any (fun e => x e.1 && x e.2) := by
    rw [← decode, List.any_map] <;> rfl
  let normalize (e : Fin 8 × Fin 8) := if e.1 ≤ e.2 then e else (e.2,e.1)
  have hperm : ∀ j, (edges.map (fun e => normalize (p j e.1, p j e.2))).Perm
      (edges.map normalize) := by decide +kernel
  have hed (j : Fin 8) (x : Fin 8 → Bool) : edge (fun i => x (p j i)) = edge x := by
    let f (e : Fin 8 × Fin 8) := x e.1 && x e.2
    have fnorm (e : Fin 8 × Fin 8) : f (normalize e) = f e := by
      unfold normalize
      split <;> simp [f, Bool.and_comm]
    have h := (hperm j).any_eq (f := f)
    rw [edge_eq (fun i => x (p j i)), edge_eq x]
    simp only [List.any_map] at h
    calc
      _ = edges.any (fun e => f (normalize (p j e.1, p j e.2))) :=
        List.any_congr rfl (fun e => (fnorm (p j e.1, p j e.2)).symm)
      _ = edges.any (fun e => f (normalize e)) := h
      _ = _ := List.any_congr rfl fnorm
  intro j C fan he
  change ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!x j, true, false]) = edge x at he
  let phi (i : ℕ) : ℕ := if hi : i < 8 then (p j ⟨i,hi⟩).val else i
  let reindex (g : Gate) : Gate := ⟨g.op, g.inputs.map phi⟩
  let D : Circuit := ⟨C.gates.map reindex, phi C.output⟩
  have hfan : FanInTwo D := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [reindex] using fan g' hg'
  have snoc (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases lt : i < w.length
    · simp [List.getD, List.getElem?_append_left lt, Nat.ne_of_lt lt]
    · rw [List.getD, List.getElem?_append_right (by omega)]
      by_cases eq : i = w.length
      · simp [eq]
      · have a : w.length ≤ i := by omega
        have b' : [b].length ≤ i - w.length := by simp; omega
        simp [eq, List.getD, List.getElem?_eq_none a, List.getElem?_eq_none b']
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have fold_eq (gs : List Gate) (a b : List Bool) (hL : a.length = b.length)
      (h8 : 8 ≤ b.length) (H : ∀ i, b.getD (phi i) false = a.getD i false) :
      ∀ i, ((gs.map reindex).foldl step b).getD (phi i) false =
        (gs.foldl step a).getD i false := by
    induction gs generalizing a b with
    | nil => exact H
    | cons g gs ih =>
      have hm : (g.inputs.map phi).map (fun i => b.getD i false) =
          g.inputs.map (fun i => a.getD i false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => H i)
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [step, hL]
      · simp [step]; omega
      · intro i
        have hi : phi i = b.length ↔ i = a.length := by
          by_cases h : i < 8
          · have hpi := (p j ⟨i,h⟩).isLt
            simp only [phi, dite_eq_left h]
            constructor <;> intro hh <;> omega
          · simp [phi, h, hL]
        simp only [step, reindex, snoc, hi, hm, H]
  have hD (x : Fin 8 → Bool) :
      D.eval (List.ofFn x ++ [!x (r j),true,false]) = edge x := by
    let y : Fin 8 → Bool := fun i => x (p j i)
    let a := List.ofFn y ++ [!y j,true,false]
    let b := List.ofFn x ++ [!x (r j),true,false]
    have hb : ∀ i, b.getD (phi i) false = a.getD i false := by
      intro i
      by_cases hi : i < 8
      · have hpi := (p j ⟨i,hi⟩).isLt
        simp only [a, b, phi, dite_eq_left hi, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using hpi),
          List.getElem?_append_left (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem?_ofFn, dite_eq_left hpi, dite_eq_left hi, Option.getD_some, y]
      · simp only [a, b, phi, dite_eq_right hi, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi),
          List.getElem?_append_right (by simpa using Nat.le_of_not_gt hi)]
        simp [y, hp]
    have hFold := fold_eq C.gates a b (by simp [a,b]) (by simp [b]) hb C.output
    change D.eval b = edge x
    change D.eval b = C.eval a at hFold
    rw [hFold, he y]
    exact hed j x
  have hsize : 13 ≤ D.size := by
    rcases hr j with hj | hj
    · exact h0 D hfan (by simpa only [hj, edge] using hD)
    · exact h1 D hfan (by simpa only [hj, edge] using hD)
  simpa [D, Circuit.size] using hsize
