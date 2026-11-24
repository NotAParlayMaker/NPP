import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2521_aux

/-- The value a gate writes on the wire list `w`. -/
def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

/-- The wires after running the gates `gs` on the wire list `w`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp; omega

theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

/-- The input wires: the nine bits, then the constant `false` wire. -/
def base (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [false]

theorem base_length (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]

/-- The wires after the first `j` gates. -/
def pw (gs : List Gate) (j : ℕ) (x : Fin 9 → Bool) : List Bool := run (gs.take j) (base x)

theorem pw_length (gs : List Gate) (j : ℕ) (x : Fin 9 → Bool) :
    (pw gs j x).length = 10 + min j gs.length := by
  simp [pw, run_length, base_length, List.length_take]

/-- Wires already written do not change. -/
theorem pw_stable (gs : List Gate) {j k : ℕ} (hjk : j ≤ k) (x : Fin 9 → Bool) (i : ℕ)
    (hi : i < 10 + min j gs.length) : (pw gs k x).getD i false = (pw gs j x).getD i false := by
  have hsplit : gs.take k = gs.take j ++ (gs.take k).drop j := by
    conv_lhs => rw [← List.take_append_drop j (gs.take k)]
    rw [List.take_take, Nat.min_eq_left hjk]
  unfold pw
  rw [hsplit, run_append]
  exact run_preserves _ _ _ (by rw [run_length, base_length, List.length_take]; omega)

theorem pw_succ (gs : List Gate) {j : ℕ} (hj : j < gs.length) (x : Fin 9 → Bool) :
    pw gs (j + 1) x = pw gs j x ++ [value gs[j] (pw gs j x)] := by
  unfold pw
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, run_append, run_cons,
    run_nil]

theorem pw_input (gs : List Gate) (j : ℕ) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 10) :
    (pw gs j x).getD i false = (base x).getD i false := by
  rw [pw_stable gs (Nat.zero_le j) x i (by omega)]
  simp [pw, run]
  rfl

/-- The set traced by gate `j`. -/
def tr (gs : List Gate) (T : Finset (Fin 9 → Bool)) (j : ℕ) : Finset (Fin 9 → Bool) :=
  T.filter (fun x => (pw gs (j + 1) x).getD (10 + j) false = true)

/-- The traced sets of all gates. -/
def W (gs : List Gate) (T : Finset (Fin 9 → Bool)) : List (Finset (Fin 9 → Bool)) :=
  (List.range gs.length).map (tr gs T)

/-- The wire sets after the first `j` gates. -/
def V (gs : List Gate) (T : Finset (Fin 9 → Bool)) (j : ℕ) : List (Finset (Fin 9 → Bool)) :=
  (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ [∅] ++ (W gs T).take j

theorem W_length (gs : List Gate) (T : Finset (Fin 9 → Bool)) : (W gs T).length = gs.length := by
  simp [W]

theorem W_getD (gs : List Gate) (T : Finset (Fin 9 → Bool)) {j : ℕ} (hj : j < gs.length) :
    (W gs T).getD j ∅ = tr gs T j := by
  simp [W, List.getD_eq_getElem?_getD, hj]

/-- The input part of a wire list read at `i < 9`. -/
theorem base_getD (x : Fin 9 → Bool) {i : ℕ} (h : i < 9) : (base x).getD i false = x ⟨i, h⟩ := by
  rw [base, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
    List.getElem?_ofFn, dif_pos h]
  rfl

theorem base_getD9 (x : Fin 9 → Bool) : (base x).getD 9 false = false := by
  rw [base, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The wire sets read at `i`, by cases. -/
theorem V_get (gs : List Gate) (T : Finset (Fin 9 → Bool)) (j i : ℕ) :
    (V gs T j).getD i ∅ =
      if h : i < 9 then T.filter (fun x => x ⟨i, h⟩) else
      if i - 10 < j ∧ i - 10 < gs.length ∧ 10 ≤ i then tr gs T (i - 10) else ∅ := by
  unfold V
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < 9
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_ofFn, dif_pos h1, dif_pos h1]
    rfl
  rw [dif_neg h1]
  by_cases h2 : i = 9
  · subst h2
    rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
    simp
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_ofFn, List.length_singleton]
  rw [List.getElem?_take]
  by_cases h3 : i - (9 + 1) < j
  · rw [if_pos h3]
    by_cases h4 : i - (9 + 1) < gs.length
    · rw [if_pos ⟨h3, h4, by omega⟩]
      simp [W, List.getElem?_range h4]
    · rw [if_neg (by omega)]
      simp only [W, List.getElem?_map]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  · rw [if_neg h3, if_neg (by omega)]
    rfl

/-- Every wire set lies in `T`. -/
theorem V_sub (gs : List Gate) (T : Finset (Fin 9 → Bool)) (j i : ℕ) :
    (V gs T j).getD i ∅ ⊆ T := by
  rw [V_get]
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

/-- Membership in a wire set is the wire's value. -/
theorem V_mem (gs : List Gate) (T : Finset (Fin 9 → Bool)) {j : ℕ} (hj : j ≤ gs.length)
    {x : Fin 9 → Bool} (hx : x ∈ T) (i : ℕ) :
    x ∈ (V gs T j).getD i ∅ ↔ (pw gs j x).getD i false = true := by
  rw [V_get]
  by_cases h1 : i < 9
  · rw [dif_pos h1, pw_input gs j x i (by omega), base_getD x h1]
    simp [hx]
  rw [dif_neg h1]
  by_cases h2 : i = 9
  · subst h2
    rw [if_neg (by omega), pw_input gs j x 9 (by omega), base_getD9]
    simp
  by_cases h3 : i - 10 < j
  · rw [if_pos ⟨h3, by omega, by omega⟩]
    simp only [tr, Finset.mem_filter, hx, true_and]
    have hi : 10 + (i - 10) = i := by omega
    rw [hi, pw_stable gs (show i - 10 + 1 ≤ j by omega) x i (by omega)]
  · rw [if_neg (by omega)]
    simp only [Finset.notMem_empty, false_iff]
    rw [List.getD_eq_default _ _ (by rw [pw_length]; omega)]
    simp

/-- The value of gate `j` from the wire sets. -/
theorem tr_mem (gs : List Gate) (T : Finset (Fin 9 → Bool)) {j : ℕ} (hj : j < gs.length)
    {x : Fin 9 → Bool} (hx : x ∈ T) :
    x ∈ tr gs T j ↔ value gs[j] (pw gs j x) = true := by
  simp only [tr, Finset.mem_filter, hx, true_and]
  rw [pw_succ gs hj, List.getD_append_right _ _ _ _ (by rw [pw_length]; omega)]
  rw [pw_length, Nat.min_eq_left hj.le, Nat.sub_self]
  simp

theorem set_eq {T S R : Finset (Fin 9 → Bool)} (hS : S ⊆ T) (hR : R ⊆ T)
    (h : ∀ x ∈ T, x ∈ S ↔ x ∈ R) : S = R := by
  ext x
  by_cases hx : x ∈ T
  · exact h x hx
  · exact ⟨fun h' => absurd (hS h') hx, fun h' => absurd (hR h') hx⟩

theorem tr_sub (gs : List Gate) (T : Finset (Fin 9 → Bool)) (j : ℕ) : tr gs T j ⊆ T :=
  Finset.filter_subset _ _

/-- A fan-in-two AND/OR/NOT gate whose value set is `S`, over wire sets `A`, is a union, an
intersection or a complement in `T` of wire sets. -/
theorem gate_sets (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (T S : Finset (Fin 9 → Bool)) (A : ℕ → Finset (Fin 9 → Bool)) (P : (Fin 9 → Bool) → List Bool)
    (hS : S ⊆ T) (hA : ∀ i, A i ⊆ T)
    (hmem : ∀ x ∈ T, ∀ i, x ∈ A i ↔ (P x).getD i false = true)
    (h9 : ∀ x ∈ T, (P x).getD 9 false = false)
    (hval : ∀ x ∈ T, x ∈ S ↔ value g (P x) = true) :
    ∃ a b : ℕ, S = A a ∪ A b ∨ S = A a ∩ A b ∨ S = T \ A a := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hU : ∀ a b, A a ∪ A b ⊆ T := fun a b => Finset.union_subset (hA a) (hA b)
  have hI : ∀ a b, A a ∩ A b ⊆ T := fun a b => (Finset.inter_subset_left).trans (hA a)
  have hD : ∀ a, T \ A a ⊆ T := fun a => Finset.sdiff_subset
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨9, 9, Or.inr (Or.inr (set_eq hS (hD 9) fun x hx => ?_))⟩
      rw [hval x hx, Finset.mem_sdiff, hmem x hx, h9 x hx]
      simp [value, GateOp.eval, hx]
    · refine ⟨a, a, Or.inr (Or.inl (set_eq hS (hI a a) fun x hx => ?_))⟩
      rw [hval x hx, Finset.mem_inter, hmem x hx]
      simp [value, GateOp.eval]
    · refine ⟨a, b, Or.inr (Or.inl (set_eq hS (hI a b) fun x hx => ?_))⟩
      rw [hval x hx, Finset.mem_inter, hmem x hx, hmem x hx]
      simp [value, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨9, 9, Or.inl (set_eq hS (hU 9 9) fun x hx => ?_)⟩
      rw [hval x hx, Finset.mem_union, hmem x hx, h9 x hx]
      simp [value, GateOp.eval]
    · refine ⟨a, a, Or.inl (set_eq hS (hU a a) fun x hx => ?_)⟩
      rw [hval x hx, Finset.mem_union, hmem x hx]
      simp [value, GateOp.eval]
    · refine ⟨a, b, Or.inl (set_eq hS (hU a b) fun x hx => ?_)⟩
      rw [hval x hx, Finset.mem_union, hmem x hx, hmem x hx]
      simp [value, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · refine ⟨9, 9, Or.inr (Or.inr (set_eq hS (hD 9) fun x hx => ?_))⟩
      rw [hval x hx, Finset.mem_sdiff, hmem x hx, h9 x hx]
      simp [value, GateOp.eval, hx]
    · refine ⟨a, a, Or.inr (Or.inr (set_eq hS (hD a) fun x hx => ?_))⟩
      rw [hval x hx, Finset.mem_sdiff, hmem x hx]
      simp [value, GateOp.eval, hx]

/-- The output: membership in the last wire sets is the circuit's value. -/
theorem out_mem (C : Circuit) (T : Finset (Fin 9 → Bool)) {x : Fin 9 → Bool} (hx : x ∈ T) :
    C.eval (List.ofFn x ++ [false]) = true ↔
      x ∈ (V C.gates T (W C.gates T).length).getD C.output ∅ := by
  rw [W_length, V_mem C.gates T le_rfl hx]
  simp only [pw, List.take_length]
  rfl

end PEqualNP.Outside.L_meta_2521_aux

open PEqualNP.Outside.L_meta_2521_aux in
theorem PEqualNP.Outside.L_meta_2521 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ) → Bool)),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∃ (x4 : List (Finset (Fin (9 : ℕ) → Bool))),       have x5 : ℕ → List (Finset (Fin (9 : ℕ) → Bool)) := fun (x5 : ℕ) => (List.ofFn fun (x6 : Fin (9 : ℕ)) => {x7 ∈ x2 | x7 x6 = Bool.true}) ++ [∅] ++ List.take x5 x4;       x4.length = x1.size ∧         (∀ x6 < x4.length,             have x8 : ℕ → Finset (Fin (9 : ℕ) → Bool) := fun (x8 : ℕ) => (x5 x6).getD x8 ∅;             ∃ (x9 : ℕ) (x10 : ℕ), x4.getD x6 ∅ = x8 x9 ∪ x8 x10 ∨ x4.getD x6 ∅ = x8 x9 ∩ x8 x10 ∨ x4.getD x6 ∅ = x2 \ x8 x9) ∧           ∀ x6 ∈ x2, x1.eval (List.ofFn x6 ++ [Bool.false]) = Bool.true ↔ x6 ∈ (x5 x4.length).getD x1.output ∅ := by
  intro C T hC
  refine ⟨W C.gates T, W_length C.gates T, ?_, ?_⟩
  · intro j hj
    rw [W_length] at hj
    have hg := hC C.gates[j] (List.getElem_mem hj)
    rw [W_getD C.gates T hj]
    exact gate_sets C.gates[j] hg T (tr C.gates T j) (fun i => (V C.gates T j).getD i ∅)
      (pw C.gates j) (tr_sub C.gates T j) (fun i => V_sub C.gates T j i)
      (fun x hx i => V_mem C.gates T hj.le hx i)
      (fun x _ => by rw [pw_input C.gates j x 9 (by omega), base_getD9])
      (fun x hx => tr_mem C.gates T hj hx)
  · intro x hx
    exact out_mem C T hx
