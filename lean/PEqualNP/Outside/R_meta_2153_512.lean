import Mathlib
import PEqualNP.Defs

-- The last allowed source index at each gate reads false.
-- A second-gate source of ten covers a missing or out-of-range NOT input.
theorem PEqualNP.Outside.R_meta_2153_512
    (encode :
      let decode := fun (k : Fin 13) (op : Fin 13 → Fin 3)
        (a b : (j : Fin 13) → Fin (12 + j.val)) =>
          if op k = 0 then PEqualNP.CircuitLowerBounds.Gate.mk .and [(a k).val, (b k).val]
          else if op k = 1 then PEqualNP.CircuitLowerBounds.Gate.mk .or [(a k).val, (b k).val]
          else PEqualNP.CircuitLowerBounds.Gate.mk .not [(a k).val]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 13 → ∃ (op : Fin 13 → Fin 3) (a b : (j : Fin 13) → Fin (12 + j.val))
          (o : Fin 25), ∀ w : List Bool, w.length = 11 →
          (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn fun k => decode k op a b) o.val).eval w =
            D.eval w)
    (exclude :
      let decode := fun (k : Fin 13) (op : Fin 13 → Fin 3)
        (a b : (j : Fin 13) → Fin (12 + j.val)) =>
          if op k = 0 then PEqualNP.CircuitLowerBounds.Gate.mk .and [(a k).val, (b k).val]
          else if op k = 1 then PEqualNP.CircuitLowerBounds.Gate.mk .or [(a k).val, (b k).val]
          else PEqualNP.CircuitLowerBounds.Gate.mk .not [(a k).val]
      let f : (Fin 9 → Bool) → Bool := fun x =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ (i : Fin 11) (op : Fin 13 → Fin 3) (a b : (j : Fin 13) → Fin (12 + j.val))
        (o : Fin 25), ∃ x : Fin 9 → Bool,
          let w := List.ofFn x ++ [x 0 || x 4]
          (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn fun k => decode k op a b) o.val).eval
            (w ++ [!(w.getD i.val false)]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hfan hfirst hfun hnot
  by_contra! small
  cases C with
  | mk gs out =>
    cases gs with
    | nil => simp at hnot
    | cons g gs =>
      cases gs with
      | nil => simp at hnot
      | cons h gs =>
        have hn : h.op = .not := by simpa using hnot
        let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, out⟩
        have dfan : PEqualNP.MetaComplexity.FanInTwo D := by
          intro t ht
          exact hfan t (by simp [D] at ht; simp [ht])
        have dsize : D.size ≤ 13 := by
          change gs.length ≤ 13
          change (g :: h :: gs).length < 16 at small
          simp only [List.length_cons] at small
          omega
        obtain ⟨op, a, b, o, agrees⟩ := encode D dfan dsize
        let i : Fin 11 := ⟨min (h.inputs.headD 10) 10, by omega⟩
        obtain ⟨x, bad⟩ := exclude i op a b o
        let v := List.ofFn x
        let z := g.op.eval (g.inputs.map fun j => v.getD j false)
        let w := v ++ [z]
        let step := fun (u : List Bool) (t : PEqualNP.CircuitLowerBounds.Gate) =>
          u ++ [t.op.eval (t.inputs.map fun j => u.getD j false)]
        have keep (ts : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool)
            (j : ℕ) (hj : j < u.length) : (ts.foldl step u).getD j false = u.getD j false := by
          induction ts generalizing u with
          | nil => rfl
          | cons t ts ih =>
            change (ts.foldl step (step u t)).getD j false = _
            rw [ih _ (by simp [step]; omega)]
            exact List.getD_append _ _ _ _ hj
        have hz : z = (x 0 || x 4) := by
          have hh := hfirst x
          change ((h :: gs).foldl step w).getD 9 false = _ at hh
          rw [keep _ _ _ (by simp [w, v])] at hh
          simpa [w, v, List.getD, List.getElem?_append] using hh
        have len : w.length = 10 := by simp [w, v]
        have neg : h.op.eval (h.inputs.map fun j => w.getD j false) = !(w.getD i.val false) := by
          rw [hn]
          change Bool.not ((h.inputs.map fun j => w.getD j false).headD false) = _
          cases he : h.inputs with
          | nil => simp [i, he, List.getElem?_eq_none len.le]
          | cons j js =>
            by_cases hj : j ≤ 10
            · simp [i, he, Nat.min_eq_left hj]
            · have h1 : w.length ≤ j := by omega
              simp [i, he, Nat.min_eq_right (by omega : 10 ≤ j),
                List.getElem?_eq_none h1, List.getElem?_eq_none len.le]
        let inp := w ++ [!(w.getD i.val false)]
        have simulates : D.eval inp =
            (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: h :: gs) out).eval v := by
          change (gs.foldl step inp).getD out false = (gs.foldl step (step w h)).getD out false
          simp only [step, neg, inp]
        have comp := congrFun hfun x
        change (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: h :: gs) out).eval v = _ at comp
        have table : ∀ y : Fin 9 → Bool,
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
           y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
           y 6 && y 8 || y 8 && y 5) =
          (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
            fun e => y (Fin.ofNat 9 (e / 10)) && y (Fin.ofNat 9 (e % 10))) := by
          decide +kernel
        have result := (agrees inp (by simp [inp, len])).trans (simulates.trans (comp.trans (table x)))
        exact bad (by simpa only [inp, w, v, hz] using result)
