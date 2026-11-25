import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5569

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The graph: u in {0, 1} or v = 0.
-- Upper: OR of wires 0 and 1, then OR with wire 4.
-- Lower: one gate reads at most two wires; reads beyond the input length give false,
-- so every wire index can be clipped to a bounded range and the rest is a finite check.

def up : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [8, 4]⟩], 9⟩

theorem up_mono : Monotone2 up := by
  intro g hg
  simp only [up, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl <;> simp

theorem up_rep :
    Represents (fun u v : Fin 4 => (4607 : ℕ).testBit (4 * u.val + v.val)) up := by
  decide

theorem getD_min (l : List Bool) (i : ℕ) :
    l.getD i false = l.getD (min i l.length) false := by
  by_cases h : i < l.length
  · rw [Nat.min_eq_left h.le]
  · rw [Nat.min_eq_right (by omega)]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem len_oneEach (u v : Fin 4) : (oneEach u v).length = 8 := by
  simp [oneEach]

theorem eval_zero (o : ℕ) (x : List Bool) :
    (⟨[], o⟩ : Circuit).eval x = x.getD o false := rfl

theorem eval_one (op : GateOp) (ins : List ℕ) (o : ℕ) (x : List Bool) :
    (⟨[⟨op, ins⟩], o⟩ : Circuit).eval x =
      (x ++ [op.eval (ins.map fun i => x.getD i false)]).getD o false := rfl

theorem norm0 (o : ℕ) (x : List Bool) (hx : x.length = 8) :
    (⟨[], o⟩ : Circuit).eval x = (⟨[], min o 8⟩ : Circuit).eval x := by
  rw [eval_zero, eval_zero, getD_min x o, hx]

theorem norm1 (op : GateOp) (ins : List ℕ) (o : ℕ) (x : List Bool) (hx : x.length = 8) :
    (⟨[⟨op, ins⟩], o⟩ : Circuit).eval x =
      (⟨[⟨op, ins.map fun i => min i 8⟩], min o 9⟩ : Circuit).eval x := by
  rw [eval_one, eval_one]
  have hm : (ins.map fun i => x.getD i false) =
      ((ins.map fun i => min i 8).map fun i => x.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [getD_min x i, hx]
  rw [← hm]
  conv_lhs => rw [getD_min]
  simp [hx]

def ev (C : Circuit) (u v : Fin 4) : Bool := C.eval (oneEach u v)

def bad (C : Circuit) : Bool := ev C 0 1 && ev C 1 1 && ev C 2 0 && !ev C 2 1

theorem bad_norm0 (o : ℕ) : bad ⟨[], o⟩ = bad ⟨[], min o 8⟩ := by
  unfold bad ev
  rw [norm0 o _ (len_oneEach 0 1), norm0 o _ (len_oneEach 1 1), norm0 o _ (len_oneEach 2 0),
    norm0 o _ (len_oneEach 2 1)]

theorem bad_norm1 (op : GateOp) (ins : List ℕ) (o : ℕ) :
    bad ⟨[⟨op, ins⟩], o⟩ = bad ⟨[⟨op, ins.map fun i => min i 8⟩], min o 9⟩ := by
  unfold bad ev
  rw [norm1 op ins o _ (len_oneEach 0 1), norm1 op ins o _ (len_oneEach 1 1),
    norm1 op ins o _ (len_oneEach 2 0), norm1 op ins o _ (len_oneEach 2 1)]

theorem fin_zero : ∀ o, o < 9 → bad ⟨[], o⟩ = false := by
  decide +kernel

theorem fin_one : ∀ o, o < 10 →
    bad ⟨[⟨GateOp.and, []⟩], o⟩ = false ∧ bad ⟨[⟨GateOp.or, []⟩], o⟩ = false ∧
    ∀ a, a < 9 → bad ⟨[⟨GateOp.and, [a]⟩], o⟩ = false ∧ bad ⟨[⟨GateOp.or, [a]⟩], o⟩ = false ∧
    ∀ b, b < 9 → bad ⟨[⟨GateOp.and, [a, b]⟩], o⟩ = false ∧
      bad ⟨[⟨GateOp.or, [a, b]⟩], o⟩ = false := by
  decide +kernel

theorem lower :
    ¬ RepSizeAtMost (fun u v : Fin 4 => (4607 : ℕ).testBit (4 * u.val + v.val)) 1 := by
  rintro ⟨⟨gates, o⟩, hmono, hsize, hrep⟩
  have hb : bad ⟨gates, o⟩ = true := by
    unfold bad ev
    rw [hrep 0 1, hrep 1 1, hrep 2 0, hrep 2 1]
    decide
  simp only [Circuit.size] at hsize
  rcases gates with _ | ⟨⟨op, ins⟩, _ | ⟨g2, rest⟩⟩
  · rw [bad_norm0] at hb
    rw [fin_zero (min o 8) (by omega)] at hb
    exact Bool.false_ne_true hb
  · have hg := hmono ⟨op, ins⟩ (List.mem_singleton_self _)
    obtain ⟨hop, hlen⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rw [bad_norm1] at hb
    have F := fin_one (min o 9) (by omega)
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp only [List.map_nil] at hb
      rcases hop with rfl | rfl
      · rw [F.1] at hb; exact Bool.false_ne_true hb
      · rw [F.2.1] at hb; exact Bool.false_ne_true hb
    · simp only [List.map_cons, List.map_nil] at hb
      have Fa := F.2.2 (min a 8) (by omega)
      rcases hop with rfl | rfl
      · rw [Fa.1] at hb; exact Bool.false_ne_true hb
      · rw [Fa.2.1] at hb; exact Bool.false_ne_true hb
    · simp only [List.map_cons, List.map_nil] at hb
      have Fb := (F.2.2 (min a 8) (by omega)).2.2 (min b 8) (by omega)
      rcases hop with rfl | rfl
      · rw [Fb.1] at hb; exact Bool.false_ne_true hb
      · rw [Fb.2] at hb; exact Bool.false_ne_true hb
    · simp at hlen
  · simp at hsize

end PEqualNP.Outside.L_meta_5569

theorem PEqualNP.Outside.L_meta_5569 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4607 : ℕ).testBit (4 * u.val + v.val)) 2 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4607 : ℕ).testBit (4 * u.val + v.val)) 1 :=
  ⟨⟨PEqualNP.Outside.L_meta_5569.up, PEqualNP.Outside.L_meta_5569.up_mono, by decide,
    PEqualNP.Outside.L_meta_5569.up_rep⟩, PEqualNP.Outside.L_meta_5569.lower⟩
