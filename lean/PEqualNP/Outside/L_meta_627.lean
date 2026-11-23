import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_len (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp [stp]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stp w g).getD i false = w.getD i false := by
  simp only [stp, List.getD_append _ _ _ _ hi]

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (stp w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp only [stp]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih (stp w g), step_len, List.length_cons]
      omega

theorem fold_lt (gs : List Gate) (w : List Bool) :
    ∀ i, i < w.length → (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => intro i hi; simpa using hi
  | cons g gs ih =>
      intro i hi
      rw [List.foldl_cons]
      exact (ih (stp w g) i (by rw [step_len]; omega)).trans (step_lt w g i hi)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem ofFn_getD {n : ℕ} (y : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ := by
  rw [List.getD_eq_getElem (l := List.ofFn y) (d := false) (n := i) (by simpa using h)]
  exact List.getElem_ofFn (by simpa using h)

theorem getD_append_add {α : Type} (l l' : List α) (d : α) (k : ℕ) :
    (l ++ l').getD (l.length + k) d = l'.getD k d := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

def g0 (u v : ℕ) : Gate := ⟨GateOp.or, [u, v]⟩
def g1 (u v : ℕ) : Gate := ⟨GateOp.and, [u, v]⟩
def g2 (m : ℕ) : Gate := ⟨GateOp.not, [m + 1]⟩
def g3 (m : ℕ) : Gate := ⟨GateOp.and, [m + 0, m + 2]⟩
def g4 (m : ℕ) : Gate := ⟨GateOp.not, [m + 3]⟩
def g5 (m o1 : ℕ) : Gate := ⟨GateOp.and, [o1, m + 4]⟩
def g6 (m o2 : ℕ) : Gate := ⟨GateOp.and, [o2, m + 3]⟩
def g7 (m : ℕ) : Gate := ⟨GateOp.or, [m + 5, m + 6]⟩

def blk (m o1 o2 u v : ℕ) : List Gate :=
  [g0 u v, g1 u v, g2 m, g3 m, g4 m, g5 m o1, g6 m o2, g7 m]

def xor4 (m u v : ℕ) : List Gate := [g0 u v, g1 u v, g2 m, g3 m]

def eX (a b : Bool) : Bool := (a || b) && !(a && b)

theorem xor4_value (m u v : ℕ) (w : List Bool) (hm : m = w.length)
    (hu : u < w.length) (hv : v < w.length) :
    ((xor4 m u v).foldl stp w).getD (w.length + 3) false =
      eX (w.getD u false) (w.getD v false) := by
  subst hm
  set xu : Bool := w.getD u false with hxu
  set xv : Bool := w.getD v false with hxv
  set t0 : Bool := xu || xv with ht0
  set t1 : Bool := xu && xv with ht1
  set t2 : Bool := !t1 with ht2
  set t3 : Bool := t0 && t2 with ht3
  have f1u : (w ++ [t0]).getD u false = xu := by
    rw [List.getD_append w [t0] false u hu]
  have f1v : (w ++ [t0]).getD v false = xv := by
    rw [List.getD_append w [t0] false v hv]
  have f2 : (w ++ [t0, t1]).getD (w.length + 1) false = t1 := by
    simp only [id_eq, getD_append_add w [t0, t1] false 1, List.getD_cons_zero,
      List.getD_cons_succ]
  have f3a : (w ++ [t0, t1, t2]).getD (w.length + 0) false = t0 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2] false 0, List.getD_cons_zero,
      List.getD_cons_succ]
  have f3b : (w ++ [t0, t1, t2]).getD (w.length + 2) false = t2 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2] false 2, List.getD_cons_zero,
      List.getD_cons_succ]
  have s0 : (xor4 w.length u v).foldl stp w =
      (g1 u v :: [g2 w.length, g3 w.length]).foldl stp (w ++ [t0]) := by
    rw [show xor4 w.length u v = g0 u v :: [g1 u v, g2 w.length, g3 w.length] from rfl,
      List.foldl_cons]
    simp only [stp, id_eq, g0, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, List.getD_cons_zero, List.getD_cons_succ, Bool.or_false,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [ht0, hxu, hxv]
  have s1 : (g1 u v :: [g2 w.length, g3 w.length]).foldl stp (w ++ [t0]) =
      (g2 w.length :: [g3 w.length]).foldl stp (w ++ [t0, t1]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, List.getD_cons_zero, List.getD_cons_succ, Bool.and_true,
      List.append_assoc, List.cons_append, List.nil_append, f1u, f1v]
    rw [ht1]
  have s2 : (g2 w.length :: [g3 w.length]).foldl stp (w ++ [t0, t1]) =
      (g3 w.length :: []).foldl stp (w ++ [t0, t1, t2]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g2, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
      List.getD_cons_zero, List.getD_cons_succ, List.append_assoc, List.cons_append,
      List.nil_append, f2]
    rw [ht2]
  have s3 : (g3 w.length :: []).foldl stp (w ++ [t0, t1, t2]) =
      (w ++ [t0, t1, t2, t3]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g3, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ,
      List.append_assoc, List.cons_append, List.nil_append, f3a, f3b]
    rw [ht3]
  rw [s0, s1, s2, s3, getD_append_add w [t0, t1, t2, t3] false 3]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [ht3, ht2, ht1, ht0, hxu, hxv]
  simp only [eX]

theorem block_value (o1 o2 u v : ℕ) (w : List Bool)
    (ho1 : o1 < w.length) (ho2 : o2 < w.length) (hu : u < w.length) (hv : v < w.length) :
    ((blk w.length o1 o2 u v).foldl stp w).getD (w.length + 7) false =
      (if w.getD u false = w.getD v false then w.getD o1 false else w.getD o2 false) := by
  set xu : Bool := w.getD u false with hxu
  set xv : Bool := w.getD v false with hxv
  set a : Bool := w.getD o1 false with ha
  set b : Bool := w.getD o2 false with hb
  set t0 : Bool := xu || xv with ht0
  set t1 : Bool := xu && xv with ht1
  set t2 : Bool := !t1 with ht2
  set t3 : Bool := t0 && t2 with ht3
  set t4 : Bool := !t3 with ht4
  set t5 : Bool := a && t4 with ht5
  set t6 : Bool := b && t3 with ht6
  set t7 : Bool := t5 || t6 with ht7
  have f1u : (w ++ [t0]).getD u false = xu := by
    rw [List.getD_append w [t0] false u hu]
  have f1v : (w ++ [t0]).getD v false = xv := by
    rw [List.getD_append w [t0] false v hv]
  have f2 : (w ++ [t0, t1]).getD (w.length + 1) false = t1 := by
    simp only [id_eq, getD_append_add w [t0, t1] false 1, List.getD_cons_zero,
      List.getD_cons_succ]
  have f3a : (w ++ [t0, t1, t2]).getD (w.length + 0) false = t0 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2] false 0, List.getD_cons_zero,
      List.getD_cons_succ]
  have f3b : (w ++ [t0, t1, t2]).getD (w.length + 2) false = t2 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2] false 2, List.getD_cons_zero,
      List.getD_cons_succ]
  have f4 : (w ++ [t0, t1, t2, t3]).getD (w.length + 3) false = t3 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2, t3] false 3, List.getD_cons_zero,
      List.getD_cons_succ]
  have f5a : (w ++ [t0, t1, t2, t3, t4]).getD o1 false = a := by
    rw [List.getD_append w [t0, t1, t2, t3, t4] false o1 ho1]
  have f5b : (w ++ [t0, t1, t2, t3, t4]).getD (w.length + 4) false = t4 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2, t3, t4] false 4, List.getD_cons_zero,
      List.getD_cons_succ]
  have f6a : (w ++ [t0, t1, t2, t3, t4, t5]).getD o2 false = b := by
    rw [List.getD_append w [t0, t1, t2, t3, t4, t5] false o2 ho2]
  have f6b : (w ++ [t0, t1, t2, t3, t4, t5]).getD (w.length + 3) false = t3 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2, t3, t4, t5] false 3,
      List.getD_cons_zero, List.getD_cons_succ]
  have f7a : (w ++ [t0, t1, t2, t3, t4, t5, t6]).getD (w.length + 5) false = t5 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2, t3, t4, t5, t6] false 5,
      List.getD_cons_zero, List.getD_cons_succ]
  have f7b : (w ++ [t0, t1, t2, t3, t4, t5, t6]).getD (w.length + 6) false = t6 := by
    simp only [id_eq, getD_append_add w [t0, t1, t2, t3, t4, t5, t6] false 6,
      List.getD_cons_zero, List.getD_cons_succ]
  have s0 : (blk w.length o1 o2 u v).foldl stp w =
      (g1 u v :: [g2 w.length, g3 w.length, g4 w.length, g5 w.length o1,
        g6 w.length o2, g7 w.length]).foldl stp (w ++ [t0]) := by
    rw [show blk w.length o1 o2 u v = g0 u v :: [g1 u v, g2 w.length, g3 w.length,
      g4 w.length, g5 w.length o1, g6 w.length o2, g7 w.length] from rfl, List.foldl_cons]
    simp only [stp, id_eq, g0, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, List.getD_cons_zero, List.getD_cons_succ, Bool.or_false,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [ht0, hxu, hxv]
  have s1 : (g1 u v :: [g2 w.length, g3 w.length, g4 w.length, g5 w.length o1,
        g6 w.length o2, g7 w.length]).foldl stp (w ++ [t0]) =
      (g2 w.length :: [g3 w.length, g4 w.length, g5 w.length o1, g6 w.length o2,
        g7 w.length]).foldl stp (w ++ [t0, t1]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, List.getD_cons_zero, List.getD_cons_succ, Bool.and_true,
      List.append_assoc, List.cons_append, List.nil_append, f1u, f1v]
    rw [ht1]
  have s2 : (g2 w.length :: [g3 w.length, g4 w.length, g5 w.length o1, g6 w.length o2,
        g7 w.length]).foldl stp (w ++ [t0, t1]) =
      (g3 w.length :: [g4 w.length, g5 w.length o1, g6 w.length o2,
        g7 w.length]).foldl stp (w ++ [t0, t1, t2]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g2, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
      List.getD_cons_zero, List.getD_cons_succ, List.append_assoc, List.cons_append,
      List.nil_append, f2]
    rw [ht2]
  have s3 : (g3 w.length :: [g4 w.length, g5 w.length o1, g6 w.length o2,
        g7 w.length]).foldl stp (w ++ [t0, t1, t2]) =
      (g4 w.length :: [g5 w.length o1, g6 w.length o2,
        g7 w.length]).foldl stp (w ++ [t0, t1, t2, t3]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g3, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true, List.getD_cons_zero, List.getD_cons_succ,
      List.append_assoc, List.cons_append, List.nil_append, f3a, f3b]
    rw [ht3]
  have s4 : (g4 w.length :: [g5 w.length o1, g6 w.length o2, g7 w.length]).foldl stp
        (w ++ [t0, t1, t2, t3]) =
      (g5 w.length o1 :: [g6 w.length o2, g7 w.length]).foldl stp
        (w ++ [t0, t1, t2, t3, t4]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g4, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
      List.getD_cons_zero, List.getD_cons_succ, List.append_assoc, List.cons_append,
      List.nil_append, f4]
    rw [ht4]
  have s5 : (g5 w.length o1 :: [g6 w.length o2, g7 w.length]).foldl stp
        (w ++ [t0, t1, t2, t3, t4]) =
      (g6 w.length o2 :: [g7 w.length]).foldl stp (w ++ [t0, t1, t2, t3, t4, t5]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g5, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true, List.getD_cons_zero, List.getD_cons_succ,
      List.append_assoc, List.cons_append, List.nil_append, f5a, f5b]
    rw [ht5]
  have s6 : (g6 w.length o2 :: [g7 w.length]).foldl stp (w ++ [t0, t1, t2, t3, t4, t5]) =
      [g7 w.length].foldl stp (w ++ [t0, t1, t2, t3, t4, t5, t6]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g6, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, Bool.and_true, List.getD_cons_zero, List.getD_cons_succ,
      List.append_assoc, List.cons_append, List.nil_append, f6a, f6b]
    rw [ht6]
  have s7 : [g7 w.length].foldl stp (w ++ [t0, t1, t2, t3, t4, t5, t6]) =
      (w ++ [t0, t1, t2, t3, t4, t5, t6, t7]) := by
    rw [List.foldl_cons]
    simp only [stp, id_eq, g7, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ,
      Bool.or_false, List.append_assoc, List.cons_append, List.nil_append, f7a, f7b]
    rw [ht7]
  rw [s0, s1, s2, s3, s4, s5, s6, s7,
    getD_append_add w [t0, t1, t2, t3, t4, t5, t6, t7] false 7]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [ht7, ht5, ht6, ht4, ht3, ht2, ht1, ht0]
  cases xu <;> cases xv <;> cases a <;> cases b <;> decide

theorem xor4_fan (m u v : ℕ) :
    ∀ g ∈ xor4 m u v,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [xor4, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp [g0, g1, g2, g3]

theorem blk_fan (m o1 o2 u v : ℕ) :
    ∀ g ∈ blk m o1 o2 u v,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [blk, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [g0, g1, g2, g3, g4, g5, g6, g7]

theorem fan_append {a b : List Gate}
    (ha : ∀ g ∈ a, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hb : ∀ g ∈ b, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ a ++ b, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with h' | h'
  · exact ha g h'
  · exact hb g h'

def gN3 (m : ℕ) : Gate := ⟨GateOp.not, [m + 3]⟩
def gA1 (m o1 : ℕ) : Gate := ⟨GateOp.and, [o1, m + 4]⟩
def gA2 (m o2 : ℕ) : Gate := ⟨GateOp.and, [o2, m + 3]⟩
def gF : Gate := ⟨GateOp.or, []⟩

theorem fan_one (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hin : g.inputs.length ≤ 2) :
    ∀ h ∈ [g], h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      h.inputs.length ≤ 2 := by
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  subst hh
  exact ⟨hop, hin⟩

theorem fan_two (g h : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hgi : g.inputs.length ≤ 2)
    (hh : h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hhi : h.inputs.length ≤ 2) :
    ∀ k ∈ [g, h], k.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      k.inputs.length ≤ 2 := by
  intro k hk
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact ⟨hg, hgi⟩
  · exact ⟨hh, hhi⟩

theorem gN3_fan (m : ℕ) :
    ∀ g ∈ [gN3 m], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 :=
  fan_one (gN3 m) (by simp [gN3]) (by simp [gN3])

theorem gA1_fan (m o1 : ℕ) :
    ∀ g ∈ [gA1 m o1], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 :=
  fan_one (gA1 m o1) (by simp [gA1]) (by simp [gA1])

theorem gA2_fan (m o2 : ℕ) :
    ∀ g ∈ [gA2 m o2], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 :=
  fan_one (gA2 m o2) (by simp [gA2]) (by simp [gA2])

theorem gF_fan :
    ∀ g ∈ [gF], g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 :=
  fan_one gF (by simp [gF]) (by simp [gF])

theorem d1_value (m o2 u v : ℕ) (w : List Bool) (hm : m = w.length)
    (ho2 : o2 < w.length) (hu : u < w.length) (hv : v < w.length) :
    ((xor4 m u v ++ [gA2 m o2]).foldl stp w).getD (m + 4) false =
      (w.getD o2 false && eX (w.getD u false) (w.getD v false)) := by
  have hw4 : ((xor4 m u v).foldl stp w).length = w.length + 4 := by
    rw [fold_length]; simp [xor4]
  have h1 : ((xor4 m u v).foldl stp w).getD o2 false = w.getD o2 false :=
    fold_lt (xor4 m u v) w o2 ho2
  have h2 : ((xor4 m u v).foldl stp w).getD (m + 3) false =
      eX (w.getD u false) (w.getD v false) := by
    rw [show m + 3 = w.length + 3 by omega]
    exact xor4_value m u v w hm hu hv
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [step_last _ (gA2 m o2) (m + 4) (by rw [hw4]; omega)]
  simp only [gA2, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, id_eq, h1, h2]

theorem d3_value (m o1 u v : ℕ) (w : List Bool) (hm : m = w.length)
    (ho1 : o1 < w.length) (hu : u < w.length) (hv : v < w.length) :
    ((xor4 m u v ++ [gN3 m, gA1 m o1]).foldl stp w).getD (m + 5) false =
      (w.getD o1 false && !(eX (w.getD u false) (w.getD v false))) := by
  have hw4 : ((xor4 m u v).foldl stp w).length = w.length + 4 := by
    rw [fold_length]; simp [xor4]
  have hw5 : (stp ((xor4 m u v).foldl stp w) (gN3 m)).length = w.length + 5 := by
    rw [step_len, hw4]
  have hA : (stp ((xor4 m u v).foldl stp w) (gN3 m)).getD o1 false = w.getD o1 false := by
    rw [step_lt _ _ o1 (by rw [hw4]; omega)]
    exact fold_lt (xor4 m u v) w o1 ho1
  have hO : (stp ((xor4 m u v).foldl stp w) (gN3 m)).getD (m + 4) false =
      !(eX (w.getD u false) (w.getD v false)) := by
    rw [step_last ((xor4 m u v).foldl stp w) (gN3 m) (m + 4) (by rw [hw4]; omega)]
    have h2 : ((xor4 m u v).foldl stp w).getD (m + 3) false =
        eX (w.getD u false) (w.getD v false) := by
      rw [show m + 3 = w.length + 3 by omega]
      exact xor4_value m u v w hm hu hv
    simp only [gN3, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, h2]
  rw [List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  rw [step_last _ (gA1 m o1) (m + 5) (by rw [hw5]; omega)]
  simp only [gA1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, id_eq, hA, hO]

theorem main_627 (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n)
    (h : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧
      (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) :
    HasCircuitSize n F (s + 8) := by
  obtain ⟨C, hfan, hsz, o1, o2, hspec⟩ := h
  have hsz2 : C.gates.length ≤ s := hsz
  have hlen : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).length = n + C.gates.length := by
    intro x
    rw [wires_eq, fold_length]
    simp
  have hU : ∀ x : Fin n → Bool, u.val < (C.wires (List.ofFn x)).length := by
    intro x; rw [hlen x]; have := u.isLt; omega
  have hV : ∀ x : Fin n → Bool, v.val < (C.wires (List.ofFn x)).length := by
    intro x; rw [hlen x]; have := v.isLt; omega
  have hxuget : ∀ (x : Fin n → Bool), (C.wires (List.ofFn x)).getD u.val false = x u := by
    intro x
    rw [wires_eq, fold_lt C.gates (List.ofFn x) u.val (by simpa using hU x)]
    exact ofFn_getD x u.isLt
  have hxvget : ∀ (x : Fin n → Bool), (C.wires (List.ofFn x)).getD v.val false = x v := by
    intro x
    rw [wires_eq, fold_lt C.gates (List.ofFn x) v.val (by simpa using hV x)]
    exact ofFn_getD x v.isLt
  by_cases hAB : o1 < n + C.gates.length ∧ o2 < n + C.gates.length
  · have ho1 : ∀ x : Fin n → Bool, o1 < (C.wires (List.ofFn x)).length := by
      intro x; rw [hlen x]; exact hAB.1
    have ho2 : ∀ x : Fin n → Bool, o2 < (C.wires (List.ofFn x)).length := by
      intro x; rw [hlen x]; exact hAB.2
    refine ⟨Circuit.mk (C.gates ++ blk (n + C.gates.length) o1 o2 u.val v.val)
      (n + C.gates.length + 7),
      fan_append hfan (blk_fan (n + C.gates.length) o1 o2 u.val v.val), ?_, ?_⟩
    · show (C.gates ++ blk (n + C.gates.length) o1 o2 u.val v.val).length ≤ s + 8
      rw [List.length_append]
      have hb : (blk (n + C.gates.length) o1 o2 u.val v.val).length = 8 := by simp [blk]
      rw [hb]; omega
    · intro x
      have hwlen : (C.wires (List.ofFn x)).length = n + C.gates.length := hlen x
      have hfold : (C.gates ++ blk (n + C.gates.length) o1 o2 u.val v.val).foldl stp
          (List.ofFn x) = (blk (n + C.gates.length) o1 o2 u.val v.val).foldl stp
            (C.wires (List.ofFn x)) := by
        rw [List.foldl_append, ← wires_eq]
      show ((C.gates ++ blk (n + C.gates.length) o1 o2 u.val v.val).foldl stp
        (List.ofFn x)).getD (n + C.gates.length + 7) false = F x
      rw [hfold, show n + C.gates.length + 7 = (C.wires (List.ofFn x)).length + 7 by omega,
        show blk (n + C.gates.length) o1 o2 u.val v.val =
          blk (C.wires (List.ofFn x)).length o1 o2 u.val v.val by rw [hwlen],
        block_value o1 o2 u.val v.val (C.wires (List.ofFn x)) (ho1 x) (ho2 x) (hU x) (hV x),
        hxuget x, hxvget x]
      by_cases hEq : x u = x v
      · rw [if_pos hEq]
        have hup : Function.update x u (x v) = x := by
          rw [← hEq]; exact Function.update_eq_self u x
        rw [(hspec x).1, hup]
      · rw [if_neg hEq]
        have hne : (!(x v)) = x u := by
          cases h3 : x u <;> cases h4 : x v <;> simp_all
        have hup : Function.update x u (!(x v)) = x := by
          rw [hne]; exact Function.update_eq_self u x
        rw [(hspec x).2, hup]
  · have hAfalse : ∀ x : Fin n → Bool, n + C.gates.length ≤ o1 →
        F (Function.update x u (x v)) = false := by
      intro x hge
      rw [← (hspec x).1]
      exact List.getD_eq_default (l := C.wires (List.ofFn x)) (d := false) (n := o1)
        (by rw [hlen x]; exact hge)
    have hBfalse : ∀ x : Fin n → Bool, n + C.gates.length ≤ o2 →
        F (Function.update x u (!(x v))) = false := by
      intro x hge
      rw [← (hspec x).2]
      exact List.getD_eq_default (l := C.wires (List.ofFn x)) (d := false) (n := o2)
        (by rw [hlen x]; exact hge)
    have hZ : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + C.gates.length) false =
        false := by
      intro x
      exact List.getD_eq_default (l := C.wires (List.ofFn x)) (d := false)
        (n := n + C.gates.length) (by rw [hlen x])
    by_cases h1 : o1 < n + C.gates.length
    · by_cases h2 : o2 < n + C.gates.length
      · exact absurd ⟨h1, h2⟩ hAB
      · have hge2 : n + C.gates.length ≤ o2 := by omega
        refine ⟨Circuit.mk (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gN3 (n + C.gates.length), gA1 (n + C.gates.length) o1]))
            (n + C.gates.length + 5),
          fan_append hfan (fan_append (xor4_fan (n + C.gates.length) u.val v.val)
            (fan_two _ _ (by simp [gN3]) (by simp [gN3]) (by simp [gA1]) (by simp [gA1]))),
          ?_, ?_⟩
        · show (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gN3 (n + C.gates.length), gA1 (n + C.gates.length) o1])).length ≤ s + 8
          rw [List.length_append, List.length_append]
          have hx4 : (xor4 (n + C.gates.length) u.val v.val).length = 4 := by simp [xor4]
          rw [hx4]
          simp only [List.length_cons, List.length_nil]
          omega
        · intro x
          have hwlen : (C.wires (List.ofFn x)).length = n + C.gates.length := hlen x
          have ho1x : o1 < (C.wires (List.ofFn x)).length := by rw [hwlen]; exact h1
          have hfold : (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
              [gN3 (n + C.gates.length), gA1 (n + C.gates.length) o1])).foldl stp
              (List.ofFn x) = (xor4 (n + C.gates.length) u.val v.val ++
                [gN3 (n + C.gates.length), gA1 (n + C.gates.length) o1]).foldl stp
                (C.wires (List.ofFn x)) := by
            rw [List.foldl_append, ← wires_eq]
          show ((C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gN3 (n + C.gates.length), gA1 (n + C.gates.length) o1])).foldl stp
            (List.ofFn x)).getD (n + C.gates.length + 5) false = F x
          rw [hfold,
            d3_value (n + C.gates.length) o1 u.val v.val (C.wires (List.ofFn x)) (hlen x).symm
              ho1x (hU x) (hV x), (hspec x).1, hxuget x, hxvget x]
          by_cases hEq : x u = x v
          · have he : eX (x u) (x v) = false := by
              rw [hEq]; cases h3 : x v <;> rfl
            have hup : Function.update x u (x v) = x := by
              rw [← hEq]; exact Function.update_eq_self u x
            have hFx : F x = F (Function.update x u (x v)) := by rw [hup]
            rw [he, hFx]; simp
          · have he : eX (x u) (x v) = true := by
              cases h3 : x u <;> cases h4 : x v <;> simp_all [eX]
            have hne : (!(x v)) = x u := by
              cases h3 : x u <;> cases h4 : x v <;> simp_all
            have hup : Function.update x u (!(x v)) = x := by
              rw [hne]; exact Function.update_eq_self u x
            have hFx : F x = F (Function.update x u (!(x v))) := by rw [hup]
            have hB0 : F (Function.update x u (!(x v))) = false := hBfalse x hge2
            rw [he, hFx, hB0]; simp
    · by_cases h2 : o2 < n + C.gates.length
      · have hge1 : n + C.gates.length ≤ o1 := by omega
        refine ⟨Circuit.mk (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gA2 (n + C.gates.length) o2])) (n + C.gates.length + 4),
          fan_append hfan (fan_append (xor4_fan (n + C.gates.length) u.val v.val)
            (gA2_fan (n + C.gates.length) o2)), ?_, ?_⟩
        · show (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gA2 (n + C.gates.length) o2])).length ≤ s + 8
          rw [List.length_append, List.length_append]
          have hx4 : (xor4 (n + C.gates.length) u.val v.val).length = 4 := by simp [xor4]
          rw [hx4]
          simp only [List.length_cons, List.length_nil]
          omega
        · intro x
          have hwlen : (C.wires (List.ofFn x)).length = n + C.gates.length := hlen x
          have ho2x : o2 < (C.wires (List.ofFn x)).length := by rw [hwlen]; exact h2
          have hfold : (C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
              [gA2 (n + C.gates.length) o2])).foldl stp (List.ofFn x) =
              (xor4 (n + C.gates.length) u.val v.val ++
                [gA2 (n + C.gates.length) o2]).foldl stp (C.wires (List.ofFn x)) := by
            rw [List.foldl_append, ← wires_eq]
          show ((C.gates ++ (xor4 (n + C.gates.length) u.val v.val ++
            [gA2 (n + C.gates.length) o2])).foldl stp
            (List.ofFn x)).getD (n + C.gates.length + 4) false = F x
          rw [hfold,
            d1_value (n + C.gates.length) o2 u.val v.val (C.wires (List.ofFn x)) (hlen x).symm
              ho2x (hU x) (hV x), (hspec x).2, hxuget x, hxvget x]
          by_cases hEq : x u = x v
          · have he : eX (x u) (x v) = false := by
              rw [hEq]; cases h3 : x v <;> rfl
            have hup : Function.update x u (x v) = x := by
              rw [← hEq]; exact Function.update_eq_self u x
            have hFx : F x = F (Function.update x u (x v)) := by rw [hup]
            have hA0 : F (Function.update x u (x v)) = false := hAfalse x hge1
            rw [he, hFx, hA0]; simp
          · have he : eX (x u) (x v) = true := by
              cases h3 : x u <;> cases h4 : x v <;> simp_all [eX]
            have hne : (!(x v)) = x u := by
              cases h3 : x u <;> cases h4 : x v <;> simp_all
            have hup : Function.update x u (!(x v)) = x := by
              rw [hne]; exact Function.update_eq_self u x
            have hFx : F x = F (Function.update x u (!(x v))) := by rw [hup]
            rw [he, hFx]; simp
      · have hge1 : n + C.gates.length ≤ o1 := by omega
        have hge2 : n + C.gates.length ≤ o2 := by omega
        refine ⟨Circuit.mk (C.gates ++ [gF]) (n + C.gates.length),
          fan_append hfan gF_fan, ?_, ?_⟩
        · show (C.gates ++ [gF]).length ≤ s + 8
          rw [List.length_append]
          simp only [List.length_cons, List.length_nil]
          omega
        · intro x
          have hwlen : (C.wires (List.ofFn x)).length = n + C.gates.length := hlen x
          have hfold : (C.gates ++ [gF]).foldl stp (List.ofFn x) =
              stp (C.wires (List.ofFn x)) gF := by
            rw [List.foldl_append, ← wires_eq]
            rfl
          show ((C.gates ++ [gF]).foldl stp (List.ofFn x)).getD
            (n + C.gates.length) false = F x
          rw [hfold, step_last (C.wires (List.ofFn x)) gF (n + C.gates.length) (hlen x).symm]
          simp only [gF, GateOp.eval, List.map_nil, List.any_nil]
          by_cases hEq : x u = x v
          · have hup : Function.update x u (x v) = x := by
              rw [← hEq]; exact Function.update_eq_self u x
            have hFx : F x = false := by
              rw [← hup]; exact hAfalse x hge1
            rw [hFx]
          · have hne : (!(x v)) = x u := by
              cases h3 : x u <;> cases h4 : x v <;> simp_all
            have hup : Function.update x u (!(x v)) = x := by
              rw [hne]; exact Function.update_eq_self u x
            have hFx : F x = false := by
              rw [← hup]; exact hBfalse x hge2
            rw [hFx]

end PEqualNP.Outside.L_meta_627_aux

theorem PEqualNP.Outside.L_meta_627 :
    ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n),
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
        C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧
        (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v))))
      → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) :=
  PEqualNP.Outside.L_meta_627_aux.main_627
