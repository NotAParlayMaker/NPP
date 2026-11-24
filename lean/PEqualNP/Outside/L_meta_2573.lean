import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2573

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def F : List Bool → Gate → List Bool :=
  fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma flen (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih]; simp [F]; omega

lemma fpre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [F]; omega)]
    exact List.getD_append _ _ _ _ hi

def ext (n o y : ℕ) : List Gate :=
  [⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [25 + n, 20]⟩, ⟨GateOp.or, [25 + n + 1, 24]⟩,
   ⟨GateOp.and, [25 + n + 2, 0]⟩,
   ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.or, [25 + n + 4, 22]⟩, ⟨GateOp.or, [25 + n + 5, 23]⟩,
   ⟨GateOp.and, [25 + n + 6, 2]⟩,
   ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [25 + n + 8, 17]⟩, ⟨GateOp.or, [25 + n + 9, 19]⟩,
   ⟨GateOp.and, [25 + n + 10, 8]⟩,
   ⟨GateOp.or, [o, 25 + n + 3]⟩, ⟨GateOp.or, [25 + n + 12, 25 + n + 7]⟩,
   ⟨GateOp.or, [25 + n + 13, 25 + n + 11]⟩, ⟨GateOp.or, [y, 12]⟩]

lemma rd1 (W L : List Bool) (i : ℕ) (hi : i < W.length) :
    (W ++ L).getD i false = W.getD i false := List.getD_append _ _ _ _ hi

lemma rd2 (W L : List Bool) (k : ℕ) :
    (W ++ L).getD (W.length + k) false = L.getD k false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma rd0 (W L : List Bool) :
    (W ++ L).getD W.length false = L.getD 0 false := by
  simpa using rd2 W L 0

lemma fold_ext (W : List Bool) (o y : ℕ) (hW : 25 ≤ W.length) (ho : o < W.length)
    (hy : y < W.length) :
    (List.foldl F W (ext (W.length - 25) o y)).getD (W.length + 14) false =
      (W.getD o false || (W.getD 12 false || W.getD 14 false || W.getD 20 false ||
        W.getD 24 false) && W.getD 0 false ||
       (W.getD 12 false || W.getD 18 false || W.getD 22 false || W.getD 23 false) &&
        W.getD 2 false ||
       (W.getD 12 false || W.getD 16 false || W.getD 17 false || W.getD 19 false) &&
        W.getD 8 false) ∧
    (List.foldl F W (ext (W.length - 25) o y)).getD (W.length + 15) false =
      (W.getD y false || W.getD 12 false) := by
  have e : 25 + (W.length - 25) = W.length := by omega
  have h0 : 0 < W.length := by omega
  have h2 : 2 < W.length := by omega
  have h8 : 8 < W.length := by omega
  have h12 : 12 < W.length := by omega
  have h14 : 14 < W.length := by omega
  have h16 : 16 < W.length := by omega
  have h17 : 17 < W.length := by omega
  have h18 : 18 < W.length := by omega
  have h19 : 19 < W.length := by omega
  have h20 : 20 < W.length := by omega
  have h22 : 22 < W.length := by omega
  have h23 : 23 < W.length := by omega
  have h24 : 24 < W.length := by omega
  simp only [ext, e, List.foldl_cons, List.foldl_nil, F, List.append_assoc, List.singleton_append,
    List.cons_append, List.map_cons, List.map_nil, List.nil_append]
  simp only [rd1 _ _ _ h0, rd1 _ _ _ h2, rd1 _ _ _ h8, rd1 _ _ _ h12, rd1 _ _ _ h14,
    rd1 _ _ _ h16, rd1 _ _ _ h17, rd1 _ _ _ h18, rd1 _ _ _ h19, rd1 _ _ _ h20, rd1 _ _ _ h22,
    rd1 _ _ _ h23, rd1 _ _ _ h24, rd1 _ _ _ ho, rd1 _ _ _ hy, Nat.add_zero, rd0, rd2, List.getD_cons_succ,
    List.getD_cons_zero]
  simp [GateOp.eval]

lemma pairs : ∀ a b : Fin 25,
    ((a : ℕ) < 12 ∧ 12 ≤ (b : ℕ) ∧ ((a : ℕ) + (b : ℕ) + 2) % 13 ∈ [0, 1, 3, 9] ∧
      (a : ℕ) ∈ [0, 2, 8]) ↔
    (a, b) ∈ [((0 : Fin 25), (12 : Fin 25)), (0, 14), (0, 20), (0, 24), (2, 12), (2, 18), (2, 22),
      (2, 23), (8, 12), (8, 16), (8, 17), (8, 19)] := by
  decide

lemma mono_ext (n o y : ℕ) :
    ∀ g ∈ ext n o y, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  simp [ext]

end PEqualNP.Outside.L_meta_2573

theorem PEqualNP.Outside.L_meta_2573 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output < (25 : ℕ) + x1.size → x2 < (25 : ℕ) + x1.size → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (16 : ℕ) ∧ x6.output < (25 : ℕ) + x6.size ∧ x7 < (25 : ℕ) + x6.size ∧ ∀ (x8 : Fin (25 : ℕ) → Bool), (x6.eval (List.ofFn x8) = Bool.true ↔ x1.eval (List.ofFn x8) = Bool.true ∨ ∃ (x9 : Fin (25 : ℕ)) (x10 : Fin (25 : ℕ)), ↑x9 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x10 ∧ (↑x9 + ↑x10 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x9 ∈ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) ∧ (x6.wires (List.ofFn x8)).getD x7 Bool.false = ((x1.wires (List.ofFn x8)).getD x2 Bool.false || x8 (12 : Fin (25 : ℕ))) := by
  intro C y hM ho hy
  refine ⟨⟨C.gates ++ PEqualNP.Outside.L_meta_2573.ext C.size C.output y, 25 + C.size + 14⟩,
    25 + C.size + 15, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hM g hg
    · exact PEqualNP.Outside.L_meta_2573.mono_ext _ _ _ g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext]
    omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, PEqualNP.Outside.L_meta_2573.ext]
    omega
  · intro x
    let W := C.wires (List.ofFn x)
    have hWl : W.length = 25 + C.size := by
      show (C.gates.foldl PEqualNP.Outside.L_meta_2573.F (List.ofFn x)).length = _
      rw [PEqualNP.Outside.L_meta_2573.flen]
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    have hx : ∀ i : Fin 25, W.getD i.val false = x i := by
      intro i
      show (C.gates.foldl PEqualNP.Outside.L_meta_2573.F (List.ofFn x)).getD i.val false = _
      have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
      rw [PEqualNP.Outside.L_meta_2573.fpre _ _ _ hi, List.getD_eq_getElem _ _ hi,
        List.getElem_ofFn]
    have hC' : (PEqualNP.CircuitLowerBounds.Circuit.mk
        (C.gates ++ PEqualNP.Outside.L_meta_2573.ext C.size C.output y)
        (25 + C.size + 14)).wires (List.ofFn x) =
        (PEqualNP.Outside.L_meta_2573.ext C.size C.output y).foldl
          PEqualNP.Outside.L_meta_2573.F W := by
      show List.foldl PEqualNP.Outside.L_meta_2573.F _ (C.gates ++ _) = _
      rw [List.foldl_append]
      rfl
    obtain ⟨e14, e15⟩ := PEqualNP.Outside.L_meta_2573.fold_ext W C.output y (by omega)
      (by omega) (by omega)
    rw [show W.length - 25 = C.size by omega, hWl] at e14 e15
    have h0 : W.getD 0 false = x 0 := hx 0
    have h2 : W.getD 2 false = x 2 := hx 2
    have h8 : W.getD 8 false = x 8 := hx 8
    have h12 : W.getD 12 false = x 12 := hx 12
    have h14 : W.getD 14 false = x 14 := hx 14
    have h16 : W.getD 16 false = x 16 := hx 16
    have h17 : W.getD 17 false = x 17 := hx 17
    have h18 : W.getD 18 false = x 18 := hx 18
    have h19 : W.getD 19 false = x 19 := hx 19
    have h20 : W.getD 20 false = x 20 := hx 20
    have h22 : W.getD 22 false = x 22 := hx 22
    have h23 : W.getD 23 false = x 23 := hx 23
    have h24 : W.getD 24 false = x 24 := hx 24
    have hev : C.eval (List.ofFn x) = W.getD C.output false := rfl
    have hex : (∃ (a b : Fin 25), (a : ℕ) < 12 ∧ 12 ≤ (b : ℕ) ∧
        ((a : ℕ) + (b : ℕ) + 2) % 13 ∈ [0, 1, 3, 9] ∧ (a : ℕ) ∈ [0, 2, 8] ∧
        x a = true ∧ x b = true) ↔
        ((x 12 || x 14 || x 20 || x 24) && x 0 || (x 12 || x 18 || x 22 || x 23) && x 2 ||
          (x 12 || x 16 || x 17 || x 19) && x 8) = true := by
      constructor
      · rintro ⟨a, b, h1, h2, h3, h4, ha, hb⟩
        have hm := (PEqualNP.Outside.L_meta_2573.pairs a b).mp ⟨h1, h2, h3, h4⟩
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ <;> simp [ha, hb]
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true, or_assoc] at h
        rcases h with ⟨hb | hb | hb | hb, ha⟩ | ⟨hb | hb | hb | hb, ha⟩ | ⟨hb | hb | hb | hb, ha⟩
        all_goals exact ⟨_, _, by decide, by decide, by decide, by decide, ha, hb⟩
    refine ⟨?_, ?_⟩
    · show ((PEqualNP.CircuitLowerBounds.Circuit.mk
        (C.gates ++ PEqualNP.Outside.L_meta_2573.ext C.size C.output y)
        (25 + C.size + 14)).wires (List.ofFn x)).getD (25 + C.size + 14) false = true ↔ _
      rw [hC', e14, hev, hex, h0, h2, h8, h12, h14, h16, h17, h18, h19, h20, h22, h23, h24]
      simp only [Bool.or_assoc]
      exact Bool.or_eq_true_iff
    · rw [hC', e15, h12]
