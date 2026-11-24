import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3237_584
    (pack : let col (i : ℕ) : BitVec 512 :=
        (BitVec.ofBoolListLE ((List.range 512).map fun r => r.testBit i)).setWidth 512
      let pin (w : List (BitVec 512)) (i : Fin 24) (s : Bool) :=
        if s then w.getD i.val 0 else ~~~(w.getD i.val 0)
      let run (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24) :=
        (gs.foldl (fun w g => w ++ [pin w g.1 g.2.2.1 &&& pin w g.2.1 g.2.2.2])
          (List.ofFn (fun i : Fin 9 => col i.val) ++ [col 0 ||| col 1, 0])).getD o.val 0
      ∀ (C : PEqualNP.MetaComplexity.BinaryCircuit), C.size < 14 →
        (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun u v => u == a && v == b) →
        (∀ g, C.gates[0]? = some g → ∃ b : Bool, g.op = fun u v => u == true && v == b) →
        ∃ (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24),
          gs.length = C.size ∧ (gs.head?.all fun g => g.2.2.1) = true ∧
          ∀ r : ℕ, r < 512 →
            let x (i : Fin 9) := r.testBit i.val
            (run gs o).getLsbD r = C.eval (List.ofFn x ++ [x 0 || x 1, false]))
    (exclude : let col (i : ℕ) : BitVec 512 :=
        (BitVec.ofBoolListLE ((List.range 512).map fun r => r.testBit i)).setWidth 512
      let pin (w : List (BitVec 512)) (i : Fin 24) (s : Bool) :=
        if s then w.getD i.val 0 else ~~~(w.getD i.val 0)
      let run (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24) :=
        (gs.foldl (fun w g => w ++ [pin w g.1 g.2.2.1 &&& pin w g.2.1 g.2.2.2])
          (List.ofFn (fun i : Fin 9 => col i.val) ++ [col 0 ||| col 1, 0])).getD o.val 0
      ∀ (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24) (b : Bool),
        gs.length < 14 → (gs.head?.all fun g => g.2.2.1) = true →
        (if b then ~~~(run gs o) else run gs o) ≠
          (col 0 &&& col 1 ||| col 1 &&& col 2 ||| col 2 &&& col 3 ||| col 3 &&& col 4 |||
           col 4 &&& col 0 ||| col 0 &&& col 5 ||| col 1 &&& col 6 ||| col 2 &&& col 7 |||
           col 3 &&& col 8 ||| col 5 &&& col 7 ||| col 6 &&& col 8 ||| col 8 &&& col 5)) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 :
      Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 :
      PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op
      = fun (x7 x8 : Bool) => x7 == Bool.true && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ),
      (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ),
      (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right])
      → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin
      (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9
      : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9
      : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9
      : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9
      : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9
      : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9
      : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b hsigned hfirst hcorrect
  by_contra! small
  obtain ⟨gs, o, hsize, hsign, hbits⟩ := pack C small hsigned (fun g hg => (hfirst g hg).1)
  dsimp only at hbits
  apply exclude gs o b (by omega) hsign
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  let x (i : Fin 9) := r.testBit i.val
  have evalRow := hcorrect x
  have wireRow := hbits r hr
  have colRow (i : ℕ) : ((BitVec.ofBoolListLE ((List.range 512).map fun t =>
      t.testBit i)).setWidth 512).getLsbD r = r.testBit i := by
    have h : r < ((List.range 512).map fun t => t.testBit i).length := by
      simpa only [List.length_map, List.length_range] using hr
    simp only [BitVec.getLsbD_setWidth, decide_eq_true hr, Bool.true_and,
      BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h, Option.getD_some, List.getElem_map, List.getElem_range]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_not, BitVec.getLsbD_or,
    BitVec.getLsbD_and, colRow, decide_true, hr, Bool.true_and] <;>
    rw [wireRow] <;> simpa [x, Bool.or_assoc] using evalRow
