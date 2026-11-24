import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2523_731
    (lowerNine :
      (¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
        (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 1 && x 6) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 11) ∧
      (¬ HasCircuitSize 9 (fun x : Fin 9 → Bool =>
        (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
        (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 11))
    (restrictOr : ∀ (C : Circuit) (v : Fin 9),
      let ev (x : Fin 9 → Bool) := C.eval (List.ofFn x ++ [false])
      let readers := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      FanInTwo C → C.size ≤ 13 →
      (∃ x y, (∀ j ≠ v, x j = y j) ∧ ev x ≠ ev y) →
      HasCircuitSize 9 (fun x : Fin 9 → Bool => ev (Function.update x v false)) 11 ∨
        ∃ g, readers = [g] ∧ g.op = .or)
    (singleOr : ∀ C : Circuit,
      FanInTwo C → C.size ≤ 13 →
      (∀ v : Fin 2, ∃ g, C.gates.filter (fun h =>
        (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] ∧ g.op = .or) →
      (∀ x : Fin 9 → Bool, (x 0 && x 1) = false →
        C.eval (List.ofFn x ++ [false]) =
          ([(1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
            (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      False) :
  have x1 : Finset (Fin (9 : ℕ) → Bool) := {x1 : Fin (9 : ℕ) → Bool | (x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ))) = Bool.false}; have x2 : Finset (Fin (9 : ℕ) × Fin (9 : ℕ)) := {((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))}; ¬∃ (x3 : List (Finset (Fin (9 : ℕ) → Bool))) (x4 : ℕ),     have x5 : ℕ → List (Finset (Fin (9 : ℕ) → Bool)) := fun (x5 : ℕ) => (List.ofFn fun (x6 : Fin (9 : ℕ)) => {x7 ∈ x1 | x7 x6 = Bool.true}) ++ [∅] ++ List.take x5 x3;     x3.length ≤ (13 : ℕ) ∧       (∀ x6 < x3.length,           have x8 : ℕ → Finset (Fin (9 : ℕ) → Bool) := fun (x8 : ℕ) => (x5 x6).getD x8 ∅;           ∃ (x9 : ℕ) (x10 : ℕ), x3.getD x6 ∅ = x8 x9 ∪ x8 x10 ∨ x3.getD x6 ∅ = x8 x9 ∩ x8 x10 ∨ x3.getD x6 ∅ = x1 \ x8 x9) ∧         ∀ x6 ∈ x1, x6 ∈ (x5 x3.length).getD x4 ∅ ↔ ∃ x8 ∈ x2, x6 x8.1 = Bool.true ∧ x6 x8.2 = Bool.true := by
  classical
  have traceToCircuit : ∀ (T : Finset (Fin 9 → Bool)) (W : List (Finset (Fin 9 → Bool))) (o : ℕ),
      let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ [∅] ++ W.take j
      (∀ j < W.length, let A := fun i => (V j).getD i ∅
        ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b ∨
          W.getD j ∅ = T \ A a) →
      ∃ C : Circuit, FanInTwo C ∧ C.size = W.length ∧
        ∀ x ∈ T, C.eval (List.ofFn x ++ [false]) = true ↔ x ∈ (V W.length).getD o ∅ := by
    intro T W o
    dsimp only
    intro build
    let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ [∅] ++ W.take j
    let A (j i : ℕ) := (V j).getD i ∅
    have step (j : Fin W.length) : ∃ a b : ℕ,
        W.getD j ∅ = A j a ∪ A j b ∨ W.getD j ∅ = A j a ∩ A j b ∨
          W.getD j ∅ = T \ A j a := build j j.isLt
    choose a b h using step
    let gate (j : Fin W.length) : Gate :=
      if W.getD j ∅ = A j (a j) ∪ A j (b j) then ⟨.or, [a j, b j]⟩
      else if W.getD j ∅ = A j (a j) ∩ A j (b j) then ⟨.and, [a j, b j]⟩
      else ⟨.not, [a j]⟩
    let gates := List.ofFn gate
    let C : Circuit := ⟨gates, o⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ List.ofFn gate at hg
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      dsimp only [gate]
      split
      · simp
      · split <;> simp
    · change (List.ofFn gate).length = W.length
      simp only [List.length_ofFn]
    · intro x hx
      let mem (s : Finset (Fin 9 → Bool)) : Bool := decide (x ∈ s)
      have get (l : List (Finset (Fin 9 → Bool))) (i : ℕ) :
          (l.map mem).getD i false = mem (l.getD i ∅) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases l[i]? <;> simp [mem]
      let initial : List Bool := List.ofFn x ++ [false]
      let advance (w : List Bool) (g : Gate) :=
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have evaluateStep (j : Fin W.length) :
          advance ((V j).map mem) (gate j) =
            (V j).map mem ++ [mem (W.getD j ∅)] := by
        apply congrArg (fun b : Bool => (V j).map mem ++ [b])
        dsimp only [gate]
        split
        · rename_i hu
          change (((V j).map mem).getD (a j) false ||
            (((V j).map mem).getD (b j) false || false)) = mem (W.getD j ∅)
          rw [Bool.or_false, get, get, hu]
          simp [mem, Finset.mem_union, A]
        · rename_i hu
          split
          · rename_i hi
            change (((V j).map mem).getD (a j) false &&
              (((V j).map mem).getD (b j) false && true)) = mem (W.getD j ∅)
            rw [Bool.and_true, get, get, hi]
            simp [mem, Finset.mem_inter, A]
          · rename_i hi
            have hn := (h j).resolve_left hu |>.resolve_left hi
            change (!(((V j).map mem).getD (a j) false)) = mem (W.getD j ∅)
            rw [get, hn]
            simp [mem, Finset.mem_sdiff, hx, A]
      have evaluatedPrefix (j : ℕ) (hj : j ≤ W.length) :
          (gates.take j).foldl advance initial = (V j).map mem := by
        induction j with
        | zero =>
            change initial = ((List.ofFn (fun i : Fin 9 => T.filter (fun u : Fin 9 → Bool => u i)) ++ [∅]).map mem)
            let b (i : Fin 9) : Bool := mem (T.filter (fun u : Fin 9 → Bool => u i))
            have hb : b = x := by
              funext i
              simp [b, mem, hx]
            simp only [initial, List.map_append, List.map_cons, List.map_nil, List.map_ofFn]
            change List.ofFn x ++ [false] = List.ofFn b ++ [mem ∅]
            rw [hb]
            simp [mem]
        | succ j ih =>
            have hjW : j < W.length := by omega
            have hjG : j < gates.length := by simpa [gates] using hjW
            rw [List.take_succ_eq_append_getElem hjG, List.foldl_append, ih (by omega)]
            have gateAt : gates[j] = gate ⟨j, hjW⟩ := by simp [gates]
            simp only [List.foldl_cons, List.foldl_nil, gateAt]
            rw [evaluateStep ⟨j, hjW⟩]
            have newValue : W.getD j ∅ = W[j] := List.getD_eq_getElem W ∅ hjW
            simp only [V, List.take_succ_eq_append_getElem hjW, List.map_append, List.map_cons,
              List.map_nil, newValue, List.append_assoc]
      have all : gates.foldl advance initial = (V W.length).map mem := by
        have hg : gates.length = W.length := by simp [gates]
        have fullTake : gates.take W.length = gates := List.take_of_length_le (le_of_eq hg)
        simpa only [fullTake] using evaluatedPrefix W.length le_rfl
      change ((gates.foldl advance initial).getD o false = true) ↔ _
      rw [all, get]
      simp [mem, V]
  dsimp only
  rintro ⟨W, o, hsize, hstep, hW⟩
  let T : Finset (Fin 9 → Bool) := Finset.univ.filter (fun x => (x 0 && x 1) = false)
  let E : Finset (Fin 9 × Fin 9) :=
    {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
       (3, 8), (5, 7), (6, 8), (8, 5)}
  let f (x : Fin 9 → Bool) :=
    ([(1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
      (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  obtain ⟨C, hfan, hlen, hval⟩ := traceToCircuit T W o hstep
  have hCsize : C.size ≤ 13 := by simpa only [hlen] using hsize
  have fC (x : Fin 9 → Bool) (hx : (x 0 && x 1) = false) :
      C.eval (List.ofFn x ++ [false]) = f x := by
    apply Bool.eq_iff_iff.mpr
    have hmem : x ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    refine (hval x hmem).trans ((hW x hmem).trans ?_)
    have edge : (∃ e ∈ E, x e.1 = true ∧ x e.2 = true) ↔ f x = true := by
      simp [E, f, List.any_cons, Bool.or_eq_true, Bool.and_eq_true]
      intro h0 h1
      simp [h0, h1] at hx
    exact edge
  let lift (v : Fin 2) : Fin 9 := v.castAdd 7
  have dep (v : Fin 2) : ∃ x y : Fin 9 → Bool,
      (∀ j ≠ lift v, x j = y j) ∧
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn y ++ [false]) := by
    let x : Fin 9 → Bool := fun j => decide (j = if v = 0 then 4 else 2)
    let y : Fin 9 → Bool := Function.update x (lift v) true
    refine ⟨x, y, ?_, ?_⟩
    · intro j hj
      simp [y, Function.update_of_ne hj]
    · have hx : (x 0 && x 1) = false := by fin_cases v <;> decide
      have hy : (y 0 && y 1) = false := by fin_cases v <;> decide
      rw [fC x hx, fC y hy]
      fin_cases v <;> decide
  apply singleOr C hfan hCsize _ fC
  intro v
  rcases restrictOr C (lift v) hfan hCsize (dep v) with h | h
  · exfalso
    have same : (fun x : Fin 9 → Bool =>
        C.eval (List.ofFn (Function.update x (lift v) false) ++ [false])) =
        fun x : Fin 9 → Bool => f (Function.update x (lift v) false) := by
      funext x
      apply fC
      let z := Function.update x (lift v) false
      have hz : z (lift v) = false := Function.update_self _ _ _
      change (z 0 && z 1) = false
      fin_cases v
      · change z 0 = false at hz
        simp [hz]
      · change z 1 = false at hz
        simp [hz]
    rw [same] at h
    fin_cases v
    · apply lowerNine.1
      change HasCircuitSize 9 (fun x => f (Function.update x 0 false)) 11 at h
      convert h using 1
      funext x
      simp [f, List.any_cons, Function.update, Bool.or_assoc]
    · apply lowerNine.2
      change HasCircuitSize 9 (fun x => f (Function.update x 1 false)) 11 at h
      convert h using 1
      funext x
      simp [f, List.any_cons, Function.update, Bool.or_assoc]
  · exact h
