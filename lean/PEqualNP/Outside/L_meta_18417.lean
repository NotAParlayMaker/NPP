import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18417

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def addr (f : Fin 17 → Fin 25) (base i : ℕ) : ℕ :=
  if h : i < 17 then (f ⟨i, h⟩).val else base + (i - 17)

private def translate (f : Fin 17 → Fin 25) (base : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (addr f base)⟩

private theorem readAddr (f : Fin 17 → Fin 25) (x : Fin 25 → Bool)
    (bank tail : List Bool)
    (input : ∀ j : Fin 25, bank.getD j.val false = x j)
    (hlen : 25 ≤ bank.length) (i : ℕ) :
    (bank ++ tail).getD (addr f bank.length i) false =
      (List.ofFn (fun j => x (f j)) ++ tail).getD i false := by
  unfold addr
  split
  · rename_i hi
    rw [List.getD_append _ _ _ _ (lt_of_lt_of_le (f ⟨i, hi⟩).isLt hlen), input,
      List.getD_append _ _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
    simp only [List.getElem_ofFn]
  · rename_i hi
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_lt hi)]
    simp

private theorem copyValues (f : Fin 17 → Fin 25) (x : Fin 25 → Bool)
    (bank : List Bool) (input : ∀ j : Fin 25, bank.getD j.val false = x j)
    (hlen : 25 ≤ bank.length) (gs : List Gate) (tail : List Bool) :
    ∃ result, (gs.map (translate f bank.length)).foldl advance (bank ++ tail) =
      bank ++ result ∧
      gs.foldl advance (List.ofFn (fun j => x (f j)) ++ tail) =
        List.ofFn (fun j => x (f j)) ++ result ∧ result.length = tail.length + gs.length := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, rfl, rfl, by simp⟩
  | cons g gs ih =>
    let a := List.ofFn (fun j => x (f j))
    let v := g.op.eval (g.inputs.map fun i => (a ++ tail).getD i false)
    have hval :
        (translate f bank.length g).op.eval
            ((translate f bank.length g).inputs.map fun i => (bank ++ tail).getD i false) =
          v := by
      simp only [translate, v, a, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => readAddr f x bank tail input hlen i)
    obtain ⟨result, hlarge, hsmall, hsize⟩ := ih (tail ++ [v])
    refine ⟨result, ?_, ?_, ?_⟩
    · simpa only [List.map_cons, List.foldl_cons, advance, hval, List.append_assoc] using hlarge
    · simpa only [List.foldl_cons, advance, List.append_assoc, v, a] using hsmall
    · simp at hsize ⊢
      omega

private theorem addrBound (f : Fin 17 → Fin 25) {base size i : ℕ}
    (hbase : 25 ≤ base) (hi : i < 17 + size) : addr f base i < base + size := by
  unfold addr
  split
  · rename_i h
    exact lt_of_lt_of_le (f ⟨i, h⟩).isLt (by omega)
  · omega

private def construct (C : Circuit) (w : ℕ) (f g : Fin 17 → Fin 25) : Circuit × ℕ :=
  let base := 25 + C.size
  let output := 25 + 2 * C.size
  (⟨C.gates.map (translate f 25) ++ C.gates.map (translate g base) ++
      [⟨.or, [addr f 25 C.output, addr g base C.output]⟩,
        ⟨.or, [addr f 25 w, addr g base w]⟩], output⟩, output + 1)

theorem packed (C : Circuit) (w : ℕ) (hC : Monotone2 C)
    (ho : C.output < 17 + C.size) (hw : w < 17 + C.size) (f g : Fin 17 → Fin 25) :
    ∃ D : Circuit, ∃ q : ℕ, Monotone2 D ∧ D.size ≤ 2 * C.size + 2 ∧
      D.output < 25 + D.size ∧ q < 25 + D.size ∧
      ∀ x : Fin 25 → Bool,
        D.eval (List.ofFn x) =
          (C.eval (List.ofFn fun j => x (f j)) || C.eval (List.ofFn fun j => x (g j))) ∧
        (D.wires (List.ofFn x)).getD q false =
          ((C.wires (List.ofFn fun j => x (f j))).getD w false ||
           (C.wires (List.ofFn fun j => x (g j))).getD w false) := by
  refine ⟨(construct C w f g).1, (construct C w f g).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [construct, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    rcases ha with (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) | (rfl | rfl)
    · simpa [translate] using hC b hb
    · simpa [translate] using hC b hb
    · simp
    · simp
  · simp [construct, Circuit.size]; omega
  · simp [construct, Circuit.size]; omega
  · simp [construct, Circuit.size]; omega
  · intro x
    let p := List.ofFn x
    have hp : p.length = 25 := by simp [p]
    have hread : ∀ j : Fin 25, p.getD j.val false = x j := by
      intro j
      change (List.ofFn x).getD j.val false = x j
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
      simp only [List.getElem_ofFn, Fin.eta]
    obtain ⟨a, ha, hfa, hal⟩ := copyValues f x p hread (by omega) C.gates []
    simp only [List.append_nil, List.length_nil, zero_add] at ha hfa hal
    rw [hp] at ha
    have habase : (p ++ a).length = 25 + C.size := by simp [hp, hal, Circuit.size]
    have haread : ∀ j : Fin 25, (p ++ a).getD j.val false = x j := by
      intro j
      rw [List.getD_append _ _ _ _ (by simp [hp]), hread]
    obtain ⟨b, hb, hgb, hbl⟩ := copyValues g x (p ++ a) haread (by omega) C.gates []
    simp only [List.append_nil, List.length_nil, zero_add] at hb hgb hbl
    rw [habase] at hb
    let z := (p ++ a) ++ b
    have hz : z.length = 25 + 2 * C.size := by simp [z, hbl, Circuit.size]; omega
    have readF (i : ℕ) (hi : i < 17 + C.size) :
        z.getD (addr f 25 i) false = (C.wires (List.ofFn fun j => x (f j))).getD i false := by
      have hlt : addr f 25 i < (p ++ a).length := by
        rw [habase]
        exact addrBound f (by omega) hi
      rw [show z = (p ++ a) ++ b from rfl, List.getD_append _ _ _ _ hlt, Circuit.wires,
        show (fun (ws : List Bool) (q : Gate) => ws ++ [q.op.eval (q.inputs.map fun k =>
          ws.getD k false)]) = advance from rfl, hfa]
      simpa only [hp] using readAddr f x p a hread (by omega) i
    have readG (i : ℕ) :
        z.getD (addr g (25 + C.size) i) false =
          (C.wires (List.ofFn fun j => x (g j))).getD i false := by
      rw [Circuit.wires, show (fun (ws : List Bool) (q : Gate) =>
        ws ++ [q.op.eval (q.inputs.map fun k => ws.getD k false)]) = advance from rfl, hgb]
      simpa only [habase] using readAddr g x (p ++ a) b haread (by omega) i
    let o := z.getD (addr f 25 C.output) false || z.getD (addr g (25 + C.size) C.output) false
    let q := z.getD (addr f 25 w) false || z.getD (addr g (25 + C.size) w) false
    have lastRead (i : ℕ) (hi : i < 17 + C.size) :
        ((z ++ [o]).getD (addr f 25 i) false || (z ++ [o]).getD (addr g (25 + C.size) i) false) =
          ((z.getD (addr f 25 i) false || z.getD (addr g (25 + C.size) i) false)) := by
      rw [List.getD_append _ _ _ _ (show addr f 25 i < z.length from by
            have := addrBound f (base := 25) (by omega) hi
            omega),
          List.getD_append _ _ _ _ (show addr g (25 + C.size) i < z.length from by
            have := addrBound g (base := 25 + C.size) (by omega) hi
            omega)]
    have allWires : (construct C w f g).1.wires p = z ++ [o, q] := by
      change ((C.gates.map (translate f 25) ++ C.gates.map (translate g (25 + C.size)) ++
        [Gate.mk .or [addr f 25 C.output, addr g (25 + C.size) C.output],
         Gate.mk .or [addr f 25 w, addr g (25 + C.size) w]]).foldl advance p) = _
      rw [List.foldl_append, List.foldl_append, ha, hb]
      simp only [List.foldl_cons, List.foldl_nil, advance, GateOp.eval, List.map_cons,
        List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rw [show z = (p ++ a) ++ b from rfl] at lastRead
      rw [lastRead w hw]
      simp [z, o, q, List.append_assoc]
    constructor
    · change ((construct C w f g).1.wires p).getD (25 + 2 * C.size) false = _
      rw [allWires, List.getD_append_right _ _ _ _ (by omega), hz, Nat.sub_self]
      simp only [List.getD_cons_zero, o, readF _ ho, readG, Circuit.eval]
    · change ((construct C w f g).1.wires p).getD (25 + 2 * C.size + 1) false = _
      rw [allWires, List.getD_append_right _ _ _ _ (by omega), hz]
      simp only [Nat.add_sub_cancel_left, List.getD_cons_succ, List.getD_cons_zero, q, readF _ hw,
        readG]

end PEqualNP.Outside.L_meta_18417

theorem PEqualNP.Outside.L_meta_18417 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (17 : ℕ) + x1.size →       x2 < (17 : ℕ) + x1.size →         ∀ (x6 x7 : Fin (17 : ℕ) → Fin (25 : ℕ)),           ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ),             PEqualNP.MetaComplexity.Monotone2 x8 ∧               x8.size ≤ (2 : ℕ) * x1.size + (2 : ℕ) ∧                 x8.output < (25 : ℕ) + x8.size ∧                   x9 < (25 : ℕ) + x8.size ∧                     ∀ (x10 : Fin (25 : ℕ) → Bool),                       have x11 : List Bool := List.ofFn fun (x11 : Fin (17 : ℕ)) => x10 (x6 x11);                       have x12 : List Bool := List.ofFn fun (x12 : Fin (17 : ℕ)) => x10 (x7 x12);                       x8.eval (List.ofFn x10) = (x1.eval x11 || x1.eval x12) ∧ (x8.wires (List.ofFn x10)).getD x9 Bool.false = ((x1.wires x11).getD x2 Bool.false || (x1.wires x12).getD x2 Bool.false) := PEqualNP.Outside.L_meta_18417.packed
