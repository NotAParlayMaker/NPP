import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The mixed choices form three orbits under pin exchange and the reflection fixing vertex zero.
-- Wire transport follows the parent reduction R_meta_2762_612.
-- Appending constant-false gates preserves every output, including out-of-range output indices.
theorem PEqualNP.Outside.R_meta_3174_641
    (oneTwo : ∀ D : Circuit, FanInTwo D → D.size = 13 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 1 || x 2]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (oneThree : ∀ D : Circuit, FanInTwo D → D.size = 13 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 1 || x 3]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5))
    (oneEight : ∀ D : Circuit, FanInTwo D → D.size = 13 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 1 || x 8]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro ops hlen allowed mixed C hf hs
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha := allowed a (by simp)
  have hb := allowed b (by simp)
  let A : Fin 9 := ⟨a, by omega⟩
  let B : Fin 9 := ⟨b, by omega⟩
  let f := fun (x : Fin 9 → Bool) =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let w := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0, x A || x B]
  have read (x : Fin 9 → Bool) (extra : List Bool) (i : Fin 9) :
      (List.ofFn x ++ extra).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  by_contra! agree
  have correct (x : Fin 9 → Bool) : C.eval (w x) = f x := by
    have e := Classical.not_not.mp (agree x)
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [((List.ofFn x ++ [!x 0]).getD A.val false || ((List.ofFn x ++ [!x 0]).getD B.val false || false))]) = _ at e
    simpa only [w, read, Bool.or_false, List.append_assoc, List.cons_append, List.nil_append] using e
  let move := fun (r : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map r)
  let relabel := fun (r : ℕ → ℕ) => Circuit.mk (C.gates.map (move r)) (r C.output)
  have fan (r : ℕ → ℕ) : FanInTwo (relabel r) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hf t ht).1, by simpa [move] using (hf t ht).2⟩
  have transport (r : ℕ → ℕ) (low : ∀ i < 11, r i < 11) (high : ∀ i, 11 ≤ i → r i = i)
      (u v : List Bool) (hu : u.length = 11) (hv : v.length = 11)
      (h : ∀ i, v.getD (r i) false = u.getD i false) : (relabel r).eval v = C.eval u := by
    let step := fun (t : List Bool) (g : Gate) => t ++ [g.op.eval (g.inputs.map fun j => t.getD j false)]
    have loop (gs : List Gate) (u v : List Bool) (heq : v.length = u.length) (large : 11 ≤ u.length)
        (inv : ∀ i, v.getD (r i) false = u.getD i false) (i : ℕ) :
        ((gs.map (move r)).foldl step v).getD (r i) false = (gs.foldl step u).getD i false := by
      induction gs generalizing u v with
      | nil => exact inv i
      | cons g gs ih =>
        change ((gs.map (move r)).foldl step (step v (move r g))).getD (r i) false =
          (gs.foldl step (step u g)).getD i false
        have ins : ((move r g).inputs.map fun j => v.getD j false) = (g.inputs.map fun j => u.getD j false) := by
          simp only [move, List.map_map, Function.comp_def, inv]
        apply ih _ _ (by simp [step, heq]) (by simp [step]; omega)
        intro j
        by_cases jl : j < u.length
        · have rj : r j < v.length := by
            by_cases hh : j < 11
            · have hh' := low j hh
              omega
            · rw [high j (by omega), heq]
              exact jl
          exact (List.getD_append _ _ _ _ rj).trans ((inv j).trans (List.getD_append _ _ _ _ jl).symm)
        · rw [high j (by omega)]
          simp only [step, move, List.getD, List.getElem?_append, heq, ite_eq_right jl]
          change ([g.op.eval ((move r g).inputs.map fun j => v.getD j false)][j-u.length]?).getD false = _
          rw [ins]
          rfl
    exact loop C.gates u v (hv.trans hu.symm) hu.ge h C.output

  let zeroGate : Gate := ⟨.or, []⟩
  let pad := fun D : Circuit =>
    Circuit.mk (D.gates ++ List.replicate (13 - D.size) zeroGate) D.output
  have padSize (D : Circuit) (small : D.size ≤ 13) : (pad D).size = 13 := by
    change D.gates.length ≤ 13 at small
    change (D.gates ++ List.replicate (13 - D.gates.length) zeroGate).length = 13
    rw [List.length_append, List.length_replicate]
    omega
  have padFan (D : Circuit) (good : FanInTwo D) : FanInTwo (pad D) := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact good _ h
    · obtain rfl := (List.mem_replicate.mp h).2
      simp [zeroGate]
  have padEval (D : Circuit) (xs : List Bool) : (pad D).eval xs = D.eval xs := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have padWires (k : ℕ) (w : List Bool) :
        (List.replicate k zeroGate).foldl step w = w ++ List.replicate k false := by
      induction k generalizing w with
      | zero => simp
      | succ k ih =>
        rw [List.replicate_succ, List.foldl_cons, ih]
        change (w ++ [false]) ++ List.replicate k false = w ++ List.replicate (k + 1) false
        simp only [List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ]
    change ((D.gates ++ List.replicate (13 - D.size) zeroGate).foldl step xs).getD D.output false =
      (D.gates.foldl step xs).getD D.output false
    rw [List.foldl_append, padWires]
    let ws := D.gates.foldl step xs
    change (ws ++ List.replicate (13 - D.size) false).getD D.output false = ws.getD D.output false
    by_cases h : D.output < ws.length
    · exact List.getD_append ws _ false D.output h
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default ws false (by omega)]
      exact List.getElem?_getD_replicate_default_eq false _ _

  let perm := fun (s : Bool) (i : Fin 9) =>
    if s then (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) i else i
  let vertices := ([1,2,3,5,8] : List (Fin 9))
  let first := ([1,5] : List (Fin 9))
  let second := ([2,3,8] : List (Fin 9))
  let codes := ([12,13,18] : List ℕ)
  have reps : ∀ u ∈ vertices, ∀ v ∈ vertices,
      ¬ (u ∈ first ∧ v ∈ first) → ¬ (u ∈ second ∧ v ∈ second) →
      ∃ k ∈ codes, ∃ s : Bool,
        (perm s u, perm s v) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10)) ∨
        (perm s v, perm s u) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10)) := by
    decide +kernel
  have aV : A ∈ vertices := by simpa [vertices, A, Fin.ext_iff] using ha
  have bV : B ∈ vertices := by simpa [vertices, B, Fin.ext_iff] using hb
  have notFirst : ¬ (A ∈ first ∧ B ∈ first) := by
    intro pair
    apply mixed.1
    simpa [first, A, B, Fin.ext_iff] using pair
  have notSecond : ¬ (A ∈ second ∧ B ∈ second) := by
    intro pair
    apply mixed.2
    simpa [second, A, B, Fin.ext_iff] using pair
  obtain ⟨k, hk, s, hab⟩ := reps A aV B bV notFirst notSecond
  have canonical (t : ℕ) (ht : t ∈ codes) (D : Circuit) (hd : FanInTwo D) (sz : D.size = 13) :
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++
        [!x 0, x (Fin.ofNat 9 (t / 10)) || x (Fin.ofNat 9 (t % 10))]) ≠ f x := by
    simp [codes] at ht
    rcases ht with rfl | rfl | rfl
    · exact oneTwo D hd sz
    · exact oneThree D hd sz
    · exact oneEight D hd sz
  let r := fun i : ℕ => if h : i < 9 then (perm s ⟨i,h⟩).val else i
  have fixes : perm s 0 = 0 := by cases s <;> decide
  have symm (turn : Bool) (x : Fin 9 → Bool) : f (x ∘ perm turn) = f x := by
    cases turn with
    | false => rfl
    | true =>
      change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 1 || x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 ||
        x 7 && x 2 || x 2 && x 1) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)
      ac_rfl
  have resized : (relabel r).size ≤ 13 := by
    change (C.gates.map (move r)).length ≤ 13
    rw [List.length_map]
    exact hs
  obtain ⟨x, hx⟩ := canonical k hk (pad (relabel r)) (padFan _ (fan r)) (padSize _ resized)
  let y := x ∘ perm s
  let v := List.ofFn x ++ [!x 0, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]
  have hor : (y A || y B) = (x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))) := by
    rcases hab with h | h
    · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2]
    · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2, Bool.or_comm]
  have tr := transport r (by
    intro i hi
    by_cases h : i < 9
    · simpa [r,h] using (show (perm s ⟨i,h⟩).val < 11 by have := (perm s ⟨i,h⟩).isLt; omega)
    · simpa [r,h] using hi)
    (by intro i hi; simp [r, show ¬i < 9 by omega]) (w y) v (by simp [w]) (by simp [v]) (by
    intro i
    by_cases h : i < 9
    · rw [show r i = (perm s ⟨i,h⟩).val by simp [r,h]]
      exact (read x _ (perm s ⟨i,h⟩)).trans (read y _ ⟨i,h⟩).symm
    · simp only [v, w, r, dite_eq_right h, List.getD, List.getElem?_append, List.length_ofFn, ite_eq_right h, hor, show y 0 = x 0 by simp [y, fixes]])
  exact hx ((padEval (relabel r) v).trans (tr.trans ((correct y).trans (symm s x))))
