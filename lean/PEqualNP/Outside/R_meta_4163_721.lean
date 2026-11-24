import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4163_721
  (compile : let pins := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
    let touches := fun (a b : ℕ) (g : Gate) => (pins g).contains a || (pins g).contains b
    ∀ (P Q : List Gate) (g : Gate) (o : ℕ), let C : Circuit := ⟨P ++ g :: Q,o⟩
    FanInTwo C → (∀ h ∈ P ++ Q, 6 ∉ pins h) → 6 ∈ pins g → g.op = .or → o ≠ 6 →
    ∃ (A B : List Gate) (s j : ℕ), let D : Circuit := ⟨A ++ B,j⟩
      FanInTwo D ∧ (∀ h ∈ A, 6 ∉ pins h) ∧ A.length = P.length ∧ B.length = Q.length ∧
      (A ++ B).countP (touches 6 9) ≤ P.countP (fun h => (pins h).contains 9) + Q.countP (touches 9 (10+P.length)) ∧
      ∀ u : List Bool, u.length = 10 →
        D.eval (u.set 6 (u.getD 6 false || (Circuit.mk A s).eval (u.set 6 false))) = C.eval u)
  (bound : let pins := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
    let touches := fun (a b : ℕ) (g : Gate) => (pins g).contains a || (pins g).contains b
    let inp := fun (x : Fin 8 → Bool) (w z : Bool) => [x 1,x 0,x 4,x 7,x 5,x 2,w,x 6,x 3,z]
    let H := fun (x : Fin 8 → Bool) => (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (tableIndex x / 64) 0).testBit (tableIndex x % 64)
    ∀ (A B : List Gate) (s j : ℕ), let D : Circuit := ⟨A ++ B,j⟩
    let t := fun x : Fin 8 → Bool => (Circuit.mk A s).eval (inp x false (x 1))
    FanInTwo D → (∀ h ∈ A, 6 ∉ pins h) → A.length + B.length ≤ 13 → (A ++ B).countP (touches 6 9) ≤ 3 →
    (∀ x, x 1 = true → H x = false → x 3 = true → t x = false) →
    (∀ x, D.eval (inp x (t x) (x 1)) = H x) →
    ∃ x, D.eval (inp x true true) ≠ (H x || x 0 || x 3)) :
have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>   have x2 : ℕ := PEqualNP.MetaComplexity.tableIndex x1;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x2 / (64 : ℕ)) (0 : ℕ)).testBit (x2 % (64 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => if x3.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs; ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 → x4.length + x5.length ≤ (13 : ℕ) → (∀ x11 ∈ x4 ++ x5, ((x3 x11).any fun (x13 : ℕ) => Decidable.decide (x13 = (6 : ℕ))) = Bool.false) → ((x3 x6).any fun (x12 : ℕ) => Decidable.decide (x12 = (6 : ℕ))) = Bool.true → x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) ≤ x4.length + x5.length - ((List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ)) x4).length + (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ) || (x3 x14).contains ((10 : ℕ) + x4.length)) x5).length) → ¬((∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x1 x15) ∧ ∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x15) = (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) := by
  let pins := fun (g : Gate) => if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
  let inp := fun (x : Fin 8 → Bool) (w z : Bool) => [x 1,x 0,x 4,x 7,x 5,x 2,w,x 6,x 3,z]
  let H := fun (x : Fin 8 → Bool) => (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (tableIndex x / 64) 0).testBit (tableIndex x % 64)
  intro F incoming selected P Q g o orig fan sz clean hit op budget pair
  let C : Circuit := ⟨P ++ g :: Q,o⟩
  have lo (x) : C.eval (inp x false (x 1)) = H x := by simpa [C,inp,H,F,incoming,orig] using pair.1 x
  have hi (x) : C.eval (inp x true true) = (H x || x 0 || x 3) := by simpa [C,inp,H,F,incoming,orig] using pair.2 x
  have ne : o ≠ 6 := by
    intro eq
    let row : Fin 8 → Bool := fun _ => false
    have v := hi row
    have keep : ∀ (L : List Gate) (w : List Bool), 6 < w.length →
        (L.foldl (fun (a : List Bool) (h : Gate) => a ++ [h.op.eval (h.inputs.map fun i => a.getD i false)]) w).getD 6 false = w.getD 6 false := by
      intro L
      induction L with
      | nil => simp
      | cons h L ih =>
        intro w hw
        rw [List.foldl_cons,ih _ (by simp; omega),List.getD_eq_getElem?_getD,List.getElem?_append_left hw]
        rfl
    change ((P ++ g :: Q).foldl _ (inp row true true)).getD o false = _ at v
    rw [eq,keep _ _ (by decide)] at v
    exact (by decide : ¬ ((inp row true true).getD 6 false = (H row || row 0 || row 3))) v
  obtain ⟨A,B,s,j,fd,ac,pa,qb,ct,sem⟩ := compile P Q g o fan
    (fun h mem hm => by
      have ex : (selected h).any (fun i => decide (i = 6)) = true := List.any_eq_true.mpr ⟨6,hm,by decide⟩
      rw [clean h mem] at ex
      contradiction)
    (by simpa [pins,selected,List.any_eq_true] using hit) op ne
  let D : Circuit := ⟨A ++ B,j⟩
  let t := fun x : Fin 8 → Bool => (Circuit.mk A s).eval (inp x false (x 1))
  have dlo (x) : D.eval (inp x (t x) (x 1)) = H x := by
    exact (sem (inp x false (x 1)) rfl).trans (lo x)
  have dhi (x) : D.eval (inp x true true) = (H x || x 0 || x 3) := by
    exact (sem (inp x true true) rfl).trans (hi x)
  have cb : (A ++ B).countP (fun h => (pins h).contains 6 || (pins h).contains 9) ≤ 3 := by
    change (A ++ B).countP (fun h => (pins h).contains 6 || (pins h).contains 9) ≤ P.countP (fun h => (pins h).contains 9) + Q.countP (fun h => (pins h).contains 9 || (pins h).contains (10+P.length)) at ct
    change 10 ≤ P.length + Q.length - ((P.filter (fun h => (pins h).contains 9)).length + (Q.filter (fun h => (pins h).contains 9 || (pins h).contains (10+P.length))).length) at budget
    simp only [← List.countP_eq_length_filter] at budget
    omega
  obtain ⟨x,hx⟩ := bound A B s j fd ac (by omega) cb (by
    intro x hx he h3
    change H x = false at he
    change t x = false
    cases ht : t x with
    | false => rfl
    | true =>
      have a := dlo x
      have b := dhi x
      rw [ht,hx,he] at a
      rw [he,h3] at b
      simp_all) dlo
  exact hx (dhi x)
