import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3178_1
    (h14 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ (14 : ℕ) →
      ∃ (x : Fin (9 : ℕ) → Bool),
        C.eval (List.ofFn x) ≠
          (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h11 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ (11 : ℕ) →
      ∃ (x : Fin (9 : ℕ) → Bool),
        x (0 : Fin (9 : ℕ)) = Bool.false ∧
        C.eval (List.ofFn x) ≠
          (x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h13a : ∀ (k : Fin (9 : ℕ)),
      k = (1 : Fin (9 : ℕ)) ∨ k = (4 : Fin (9 : ℕ)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = (13 : ℕ) →
        (∀ g ∈ C.gates, (0 : ℕ) ∉ g.inputs) →
        C.output ≠ (0 : ℕ) →
        C.gates.countP (fun g => g.inputs.contains (9 : ℕ)) = (1 : ℕ) →
        (∀ g ∈ C.gates, (9 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs.length = (2 : ℕ) ∧ g.inputs.Nodup) →
        C.output ≠ (9 : ℕ) →
        (∃ g ∈ C.gates, (10 : ℕ) ∈ g.inputs) →
        ∃ (x : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), x (0 : Fin (9 : ℕ)) || x k]) ≠
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))))
    (h13b : ∀ (k : Fin (9 : ℕ)),
      k = (2 : Fin (9 : ℕ)) ∨ k = (3 : Fin (9 : ℕ)) ∨ k = (6 : Fin (9 : ℕ)) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size = (13 : ℕ) →
        (∀ g ∈ C.gates, (0 : ℕ) ∉ g.inputs) →
        C.output ≠ (0 : ℕ) →
        C.gates.countP (fun g => g.inputs.contains (9 : ℕ)) = (1 : ℕ) →
        (∀ g ∈ C.gates, (9 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs.length = (2 : ℕ) ∧ g.inputs.Nodup) →
        C.output ≠ (9 : ℕ) →
        (∃ g ∈ C.gates, (10 : ℕ) ∈ g.inputs) →
        ∃ (x : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), x (0 : Fin (9 : ℕ)) || x k]) ≠
            (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
  intro x1 hlen hlt _ hcond C0 hfan0 hsize0
  by_contra hcon
  push Not at hcon
  let edgeF : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have size_eq : ∀ C : Circuit, C.size = C.gates.length := fun _ => rfl
  have getD_ofFn : ∀ (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9),
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    intro x i hi
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    exact List.getElem_ofFn (by simp [hi])
  have getD_snoc : ∀ (w : List Bool) (b : Bool) (i : ℕ),
      (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
    intro w b i
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have getD_snoc_sum : ∀ (env : List (Sum Bool ℕ)) (z : Sum Bool ℕ) (i : ℕ),
      (env ++ [z]).getD i (Sum.inl false) =
        if i < env.length then env.getD i (Sum.inl false) else if i = env.length then z else Sum.inl false := by
    intro env z i
    simp only [List.getD_eq_getElem?_getD]
    split_ifs with h1 h2
    · rw [List.getElem?_append_left h1]
    · subst h2; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  have getD_ge_sum : ∀ (env : List (Sum Bool ℕ)) (i : ℕ),
      env.length ≤ i → env.getD i (Sum.inl false) = Sum.inl false := by
    intro env i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  have foldl_len : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
      omega
  have extract_k : ∃ k : Fin 9, k.val ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      C0.eval (List.ofFn x ++ [!x 0, x 0 || x k]) = edgeF x := by
    rcases List.length_eq_two.mp hlen with ⟨a, b, rfl⟩
    have ha : a < 10 := hlt a (by simp)
    have hb : b < 10 := hlt b (by simp)
    rcases hcond with ⟨hne, h0mem⟩
    have h0ab : a = 0 ∨ b = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h0mem
      rcases h0mem with h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have hcases : (a = 0 ∧ 1 ≤ b ∧ b < 9) ∨ (b = 0 ∧ 1 ≤ a ∧ a < 9) := by
      rcases h0ab with rfl | rfl
      · have hbne : b ≠ 0 ∧ b ≠ 9 := by
          constructor <;> intro heq <;> apply hne <;> intro z hz <;> simp at hz <;> rcases hz with rfl | rfl <;> simp [heq]
        exact Or.inl ⟨rfl, by omega, by omega⟩
      · have hane : a ≠ 0 ∧ a ≠ 9 := by
          constructor <;> intro heq <;> apply hne <;> intro z hz <;> simp at hz <;> rcases hz with rfl | rfl <;> simp [heq]
        exact Or.inr ⟨rfl, by omega, by omega⟩
    rcases hcases with ⟨rfl, hb1, hb9⟩ | ⟨rfl, ha1, ha9⟩
    · refine ⟨⟨b, hb9⟩, by simp; omega, fun x => ?_⟩
      have hx : C0.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [0, b])]) = edgeF x :=
        Classical.not_not.mp (hcon x)
      have hget0 : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left (by omega), getD_ofFn x 0 (by omega)]; rfl
      have hgetb : (List.ofFn x ++ [!x 0]).getD b false = x ⟨b, hb9⟩ := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left hb9, getD_ofFn x b hb9]
      have hor : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [0, b]) = (x 0 || x ⟨b, hb9⟩) := by
        rw [eval_or]
        simp only [List.map_cons, List.map_nil, hget0, hgetb, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have heq : (List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [0, b])] =
          List.ofFn x ++ [!x 0, x 0 || x ⟨b, hb9⟩] := by
        rw [hor, List.append_assoc]; rfl
      rw [← heq]; exact hx
    · refine ⟨⟨a, ha9⟩, by simp; omega, fun x => ?_⟩
      have hx : C0.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [a, 0])]) = edgeF x :=
        Classical.not_not.mp (hcon x)
      have hget0 : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left (by omega), getD_ofFn x 0 (by omega)]; rfl
      have hgeta : (List.ofFn x ++ [!x 0]).getD a false = x ⟨a, ha9⟩ := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left ha9, getD_ofFn x a ha9]
      have hor : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [a, 0]) = (x 0 || x ⟨a, ha9⟩) := by
        rw [eval_or]
        simp only [List.map_cons, List.map_nil, hget0, hgeta, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact Bool.or_comm _ _
      have heq : (List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [a, 0])] =
          List.ofFn x ++ [!x 0, x 0 || x ⟨a, ha9⟩] := by
        rw [hor, List.append_assoc]; rfl
      rw [← heq]; exact hx
  obtain ⟨k0, hk0ne, hC0eval⟩ := extract_k
  let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have hσ_edge : ∀ x : Fin 9 → Bool, edgeF (fun i => x (σ i)) = edgeF x := by
    have hbool : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
        (a0 && a5 || a5 && a8 || a8 && a3 || a3 && a4 || a4 && a0 ||
         a0 && a1 || a5 && a7 || a8 && a6 || a3 && a2 || a1 && a6 ||
         a7 && a2 || a2 && a1) =
        (a0 && a1 || a1 && a2 || a2 && a3 || a3 && a4 || a4 && a0 ||
         a0 && a5 || a1 && a6 || a2 && a7 || a3 && a8 || a5 && a7 ||
         a6 && a8 || a8 && a5) := by
      intro a0 a1 a2 a3 a4 a5 a6 a7 a8
      rw [Bool.and_comm a5 a8, Bool.and_comm a8 a3, Bool.and_comm a8 a6, Bool.and_comm a3 a2,
        Bool.and_comm a7 a2, Bool.and_comm a2 a1]
      ac_rfl
    intro x
    exact hbool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  let permW : ℕ → ℕ := fun i => if h : i < 9 then (σ ⟨i, h⟩).val else i
  let remapC : (ℕ → ℕ) → Circuit → Circuit := fun f C =>
    ⟨C.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C.output⟩
  have permW_lt : ∀ i L, 11 ≤ L → i < L → permW i < L := by
    intro i L hL hi
    dsimp [permW]
    split_ifs with h
    · have := (σ ⟨i, h⟩).isLt; omega
    · exact hi
  have permW_ge : ∀ i, 11 ≤ i → permW i = i := by
    intro i hi
    dsimp [permW]
    rw [dite_eq_right (by omega)]
  have remap_fold_eq : ∀ (f : ℕ → ℕ),
      (∀ i L, 11 ≤ L → i < L → f i < L) →
      (∀ i, 11 ≤ i → f i = i) →
      ∀ (gs : List Gate) (w1 w2 : List Bool),
        w1.length = w2.length → 11 ≤ w1.length →
        (∀ i, w1.getD (f i) false = w2.getD i false) →
        ∀ i, ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w1).getD (f i) false =
             (gs.foldl step w2).getD i false := by
    intro f hltf hgef gs
    induction gs with
    | nil => intro w1 w2 _ _ hrel i; exact hrel i
    | cons g gs ih =>
      intro w1 w2 hlenw h11 hrel i
      simp only [List.map_cons, List.foldl_cons]
      have hgval : g.op.eval ((g.inputs.map f).map fun j => w1.getD j false) =
          g.op.eval (g.inputs.map fun j => w2.getD j false) := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro j _
        exact hrel j
      apply ih
      · simp [step, hlenw]
      · simp [step]; omega
      · intro j
        simp only [step, getD_snoc, hgval]
        by_cases hj : j < w2.length
        · have hf := hltf j w1.length h11 (by omega)
          rw [ite_eq_left hf, ite_eq_left hj, hrel j]
        · by_cases he : j = w2.length
          · have hfj : f j = w1.length := by rw [hgef j (by omega)]; omega
            rw [ite_eq_right (by omega), ite_eq_left hfj, ite_eq_right hj, ite_eq_left he]
          · rw [hgef j (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hj, ite_eq_right he]
  have canon_k : ∃ (k : Fin 9) (C1 : Circuit),
      (k = 1 ∨ k = 4 ∨ k = 2 ∨ k = 3 ∨ k = 6) ∧
      FanInTwo C1 ∧ C1.size ≤ 13 ∧
      (∀ g ∈ C1.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      ∀ x : Fin 9 → Bool, C1.eval (List.ofFn x ++ [!x 0, x 0 || x k]) = edgeF x := by
    let normNot : Gate → Gate := fun g =>
      GateOp.casesOn g.op g g ⟨GateOp.not, g.inputs.take 1⟩ (fun _ => g) g
    have norm_eval : ∀ (gs : List Gate) (w : List Bool),
        (gs.map normNot).foldl step w = gs.foldl step w := by
      intro gs
      induction gs with
      | nil => intro w; rfl
      | cons g gs ih =>
        intro w
        simp only [List.map_cons, List.foldl_cons]
        have hstep : step w (normNot g) = step w g := by
          rcases g with ⟨op, ins⟩
          cases op with
          | not => cases ins <;> rfl
          | and => rfl
          | or => rfl
          | mod _ => rfl
          | maj => rfl
        rw [hstep, ih]
    have norm_fan : ∀ C : Circuit, FanInTwo C → FanInTwo ⟨C.gates.map normNot, C.output⟩ := by
      intro C hf g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hlen⟩ := hf g0 hg0
      rcases g0 with ⟨op, ins⟩
      cases op with
      | not => exact ⟨hop, by simp [normNot]⟩
      | and => exact ⟨hop, hlen⟩
      | or => exact ⟨hop, hlen⟩
      | mod _ => exact ⟨hop, hlen⟩
      | maj => exact ⟨hop, hlen⟩
    have norm_not : ∀ (C : Circuit) (g : Gate), g ∈ C.gates.map normNot →
        g.op = GateOp.not → g.inputs.length ≤ 1 := by
      intro C g hg hop
      obtain ⟨g0, _, rfl⟩ := List.mem_map.mp hg
      rcases g0 with ⟨op, ins⟩
      cases op <;> simp [normNot] at hop ⊢
    have mkOrbit : ∀ k : Fin 9, k.val ≠ 0 →
        (∀ x : Fin 9 → Bool, C0.eval (List.ofFn x ++ [!x 0, x 0 || x k]) = edgeF x) →
        ∃ (k' : Fin 9) (C' : Circuit),
          (k' = 1 ∨ k' = 4 ∨ k' = 2 ∨ k' = 3 ∨ k' = 6) ∧
          FanInTwo C' ∧ C'.size ≤ 13 ∧
          ∀ x : Fin 9 → Bool, C'.eval (List.ofFn x ++ [!x 0, x 0 || x k']) = edgeF x := by
      intro k hkne hk
      by_cases hcan : k = 1 ∨ k = 4 ∨ k = 2 ∨ k = 3 ∨ k = 6
      · exact ⟨k, C0, hcan, hfan0, hsize0, hk⟩
      · have hk578 : k = 5 ∨ k = 7 ∨ k = 8 := by
          fin_cases k <;> simp_all
        have hσk : σ k = 1 ∨ σ k = 4 ∨ σ k = 2 ∨ σ k = 3 ∨ σ k = 6 := by
          rcases hk578 with rfl | rfl | rfl <;> decide
        refine ⟨σ k, remapC permW C0, hσk, ?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
          obtain ⟨hop, hlen⟩ := hfan0 g0 hg0
          exact ⟨hop, by simpa using hlen⟩
        · rw [size_eq]; dsimp only [remapC]; rw [List.length_map]; exact hsize0
        · intro x
          have hbase : ∀ i,
              (List.ofFn x ++ [!x 0, x 0 || x (σ k)]).getD (permW i) false =
              (List.ofFn (fun j => x (σ j)) ++ [!x (σ 0), x (σ 0) || x (σ k)]).getD i false := by
            intro i
            dsimp [permW]
            by_cases hi9 : i < 9
            · rw [dite_eq_left hi9]
              have hltσ := (σ ⟨i, hi9⟩).isLt
              have h1 : (List.ofFn x ++ [!x 0, x 0 || x (σ k)]).getD (σ ⟨i, hi9⟩).val false = x (σ ⟨i, hi9⟩) := by
                rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp)]
                exact List.getElem_ofFn (by simp)
              have h2 : (List.ofFn (fun j => x (σ j)) ++ [!x (σ 0), x (σ 0) || x (σ k)]).getD i false = x (σ ⟨i, hi9⟩) := by
                rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
                exact List.getElem_ofFn (by simp; omega)
              rw [h1, h2]
            · rw [dite_eq_right hi9]
              by_cases hi9e : i = 9
              · subst hi9e
                have hσ0 : σ 0 = 0 := rfl
                simp [List.getD_eq_getElem?_getD, hσ0]
              · by_cases hi10 : i = 10
                · subst hi10
                  have hσ0 : σ 0 = 0 := rfl
                  simp [List.getD_eq_getElem?_getD, hσ0]
                · rw [getD_ge _ i (by simp; omega), getD_ge _ i (by simp; omega)]
          have hrel := remap_fold_eq permW permW_lt permW_ge C0.gates
            (List.ofFn x ++ [!x 0, x 0 || x (σ k)])
            (List.ofFn (fun j => x (σ j)) ++ [!x (σ 0), x (σ 0) || x (σ k)])
            (by simp) (by simp) hbase C0.output
          change ((C0.gates.map fun g => ⟨g.op, g.inputs.map permW⟩).foldl step _).getD (permW C0.output) false = _
          rw [hrel]
          exact (hk (fun j => x (σ j))).trans (hσ_edge x)
    obtain ⟨k, C', hcan, hf', hs', he'⟩ := mkOrbit k0 hk0ne hC0eval
    refine ⟨k, ⟨C'.gates.map normNot, C'.output⟩, hcan, norm_fan C' hf', ?_, norm_not C', ?_⟩
    · rw [size_eq]; dsimp only; rw [List.length_map]; exact hs'
    · intro x
      change ((C'.gates.map normNot).foldl step _).getD C'.output false = _
      rw [norm_eval]
      exact he' x
  obtain ⟨k, C1, hkcan, hfan1, hsize1, hnot1, hC1eval⟩ := canon_k
  have mk14_of_le12 : ∀ (D : Circuit), FanInTwo D → D.size ≤ 12 →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 0 || x k]) = edgeF x) → False := by
    intro D hfanD hszD hevD
    let C14 : Circuit := ⟨⟨GateOp.not, [0]⟩ :: ⟨GateOp.or, [0, k.val]⟩ :: D.gates, D.output⟩
    have hfan14 : FanInTwo C14 := by
      intro g hg
      simp only [C14, List.mem_cons] at hg
      rcases hg with rfl | rfl | hgD
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact hfanD g hgD
    have hsz14 : C14.size ≤ 14 := by
      rw [size_eq] at hszD ⊢
      dsimp only [C14]
      simp only [List.length_cons]
      omega
    obtain ⟨x, hx⟩ := h14 C14 hfan14 hsz14
    apply hx
    have h01 : step (step (List.ofFn x) ⟨GateOp.not, [0]⟩) ⟨GateOp.or, [0, k.val]⟩ =
        List.ofFn x ++ [!x 0, x 0 || x k] := by
      have hklt : k.val < 9 := k.isLt
      have h0 : (List.ofFn x).getD 0 false = x 0 := by rw [getD_ofFn x 0 (by omega)]; rfl
      have hstep1 : step (List.ofFn x) ⟨GateOp.not, [0]⟩ = List.ofFn x ++ [!x 0] := by
        dsimp only [step]
        rw [eval_not]
        simp only [List.map_cons, List.map_nil, h0, List.headD_cons]
      rw [hstep1]
      have h0' : (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left (by omega), getD_ofFn x 0 (by omega)]; rfl
      have hk' : (List.ofFn x ++ [!x 0]).getD k.val false = x k := by
        rw [getD_snoc, List.length_ofFn, ite_eq_left hklt, getD_ofFn x k.val hklt]
      dsimp only [step]
      rw [eval_or]
      simp only [List.map_cons, List.map_nil, h0', hk', List.any_cons, List.any_nil, id_eq, Bool.or_false, List.append_assoc, List.singleton_append]
    change (D.gates.foldl step (step (step (List.ofFn x) ⟨GateOp.not, [0]⟩) ⟨GateOp.or, [0, k.val]⟩)).getD D.output false = _
    rw [h01]
    exact hevD x
  have hsz13 : C1.size = 13 := by
    by_contra hne
    exact mk14_of_le12 C1 hfan1 (by omega) hC1eval
  have del_unused : ∀ (pos : ℕ) (gs : List Gate) (out : ℕ) (w1 w2 : List Bool),
      w1.length = w2.length + 1 → pos ≤ w2.length →
      (∀ i, i ≠ pos → w1.getD i false = w2.getD (if i < pos then i else if i = pos then 0 else i - 1) false) →
      (∀ g ∈ gs, pos ∉ g.inputs) → out ≠ pos →
      let f := fun i => if i < pos then i else if i = pos then 0 else i - 1
      ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w2).getD (f out) false =
        (gs.foldl step w1).getD out false := by
    intro pos gs out
    let f : ℕ → ℕ := fun i => if i < pos then i else if i = pos then 0 else i - 1
    have hfold : ∀ (gs : List Gate) (w1 w2 : List Bool),
        w1.length = w2.length + 1 → pos ≤ w2.length →
        (∀ i, i ≠ pos → w1.getD i false = w2.getD (f i) false) →
        (∀ g ∈ gs, pos ∉ g.inputs) →
        ∀ i, i ≠ pos →
          ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w2).getD (f i) false =
            (gs.foldl step w1).getD i false := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ hrel _ i hi; exact (hrel i hi).symm
      | cons g gs ih =>
        intro w1 w2 hlenw hpos hrel hmem i hi
        simp only [List.map_cons, List.foldl_cons]
        have hgpos : pos ∉ g.inputs := hmem g (by simp)
        have hgval : g.op.eval ((g.inputs.map f).map fun j => w2.getD j false) =
            g.op.eval (g.inputs.map fun j => w1.getD j false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro j hj
          exact (hrel j (fun he => hgpos (he ▸ hj))).symm
        apply ih (step w1 g) (step w2 ⟨g.op, g.inputs.map f⟩)
        · simp [step, hlenw]
        · simp [step]; omega
        · intro j hjne
          simp only [step, getD_snoc, hgval]
          by_cases hjlt : j < w1.length
          · by_cases hjp : j < pos
            · have hf : f j = j := by simp [f, hjp]
              rw [hf, ite_eq_left hjlt, ite_eq_left (by omega), hrel j hjne, hf]
            · have hf : f j = j - 1 := by simp [f, hjp, hjne]
              rw [hf, ite_eq_left hjlt, ite_eq_left (by omega), hrel j hjne, hf]
          · by_cases hje : j = w1.length
            · have hf : f j = w2.length := by
                simp only [f, show ¬ j < pos by omega, hjne, ite_false]; omega
              rw [hf, ite_eq_right hjlt, ite_eq_left hje, ite_eq_right (by omega), ite_eq_left rfl]
            · have hf : f j = j - 1 := by simp [f, show ¬ j < pos by omega, hjne]
              rw [hf, ite_eq_right hjlt, ite_eq_right hje, ite_eq_right (by omega), ite_eq_right (by omega)]
        · intro g' hg'; exact hmem g' (by simp [hg'])
        · exact hi
    intro w1 w2 hlenw hpos hrel hmem hout
    exact hfold gs w1 w2 hlenw hpos hrel hmem out hout
  have del_copy : ∀ (pos rep : ℕ) (gs : List Gate) (out : ℕ) (w1 w2 : List Bool),
      w1.length = w2.length + 1 → pos ≤ w2.length → rep < pos →
      (∀ i, w1.getD i false = w2.getD (if i < pos then i else if i = pos then rep else i - 1) false) →
      let f := fun i => if i < pos then i else if i = pos then rep else i - 1
      ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w2).getD (f out) false =
        (gs.foldl step w1).getD out false := by
    intro pos rep gs out
    let f : ℕ → ℕ := fun i => if i < pos then i else if i = pos then rep else i - 1
    have hfold : ∀ (gs : List Gate) (w1 w2 : List Bool),
        w1.length = w2.length + 1 → pos ≤ w2.length → rep < pos →
        (∀ i, w1.getD i false = w2.getD (f i) false) →
        ∀ i, ((gs.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step w2).getD (f i) false =
          (gs.foldl step w1).getD i false := by
      intro gs
      induction gs with
      | nil => intro w1 w2 _ _ _ hrel i; exact (hrel i).symm
      | cons g gs ih =>
        intro w1 w2 hlenw hpos hrep hrel i
        simp only [List.map_cons, List.foldl_cons]
        have hgval : g.op.eval ((g.inputs.map f).map fun j => w2.getD j false) =
            g.op.eval (g.inputs.map fun j => w1.getD j false) := by
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro j _
          exact (hrel j).symm
        apply ih (step w1 g) (step w2 ⟨g.op, g.inputs.map f⟩)
        · simp [step, hlenw]
        · simp [step]; omega
        · exact hrep
        · intro j
          simp only [step, getD_snoc, hgval]
          by_cases hjlt : j < w1.length
          · by_cases hjp : j < pos
            · have hf : f j = j := by simp [f, hjp]
              rw [hf, ite_eq_left hjlt, ite_eq_left (by omega), hrel j, hf]
            · by_cases hje : j = pos
              · have hf : f j = rep := by simp [f, hje]
                rw [hf, ite_eq_left hjlt, ite_eq_left (by omega), hrel j, hf]
              · have hf : f j = j - 1 := by simp [f, hjp, hje]
                rw [hf, ite_eq_left hjlt, ite_eq_left (by omega), hrel j, hf]
          · by_cases hje : j = w1.length
            · have hf : f j = w2.length := by
                simp only [f, show ¬ j < pos by omega, show j ≠ pos by omega, ite_false]; omega
              rw [hf, ite_eq_right hjlt, ite_eq_left hje, ite_eq_right (by omega), ite_eq_left rfl]
            · have hf : f j = j - 1 := by
                simp [f, show ¬ j < pos by omega, show j ≠ pos by omega]
              rw [hf, ite_eq_right hjlt, ite_eq_right hje, ite_eq_right (by omega), ite_eq_right (by omega)]
    intro w1 w2 hlenw hpos hrep hrel
    exact hfold gs w1 w2 hlenw hpos hrep hrel out
  have kill_no9 : (∀ g ∈ C1.gates, 9 ∉ g.inputs) → C1.output ≠ 9 → False := by
    intro hno9 hout9
    let f : ℕ → ℕ := fun i => if i < 9 then i else if i = 9 then 0 else i - 1
    let C14 : Circuit := ⟨⟨GateOp.or, [0, k.val]⟩ :: C1.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C1.output⟩
    have hfan14 : FanInTwo C14 := by
      intro g hg
      simp only [C14, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g0, hg0, rfl⟩
      · exact ⟨by simp, by simp⟩
      · obtain ⟨hop, hlen⟩ := hfan1 g0 hg0
        exact ⟨hop, by simpa using hlen⟩
    have hsz14 : C14.size ≤ 14 := by
      change (C1.gates.map _).length + 1 ≤ 14
      rw [List.length_map]; change C1.gates.length = 13 at hsz13; omega
    obtain ⟨x, hx⟩ := h14 C14 hfan14 hsz14
    apply hx
    have h0step : step (List.ofFn x) ⟨GateOp.or, [0, k.val]⟩ = List.ofFn x ++ [x 0 || x k] := by
      have hklt : k.val < 9 := k.isLt
      have h0 : (List.ofFn x).getD 0 false = x 0 := by rw [getD_ofFn x 0 (by omega)]; rfl
      have hk' : (List.ofFn x).getD k.val false = x k := by rw [getD_ofFn x k.val hklt]
      dsimp only [step]
      rw [eval_or]
      simp only [List.map_cons, List.map_nil, h0, hk', List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change ((C1.gates.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step
      (step (List.ofFn x) ⟨GateOp.or, [0, k.val]⟩)).getD (f C1.output) false = _
    rw [h0step]
    have hbase : ∀ i, i ≠ 9 →
        (List.ofFn x ++ [!x 0, x 0 || x k]).getD i false =
        (List.ofFn x ++ [x 0 || x k]).getD (f i) false := by
      intro i hi9
      dsimp [f]
      by_cases hi : i < 9
      · rw [ite_eq_left hi]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
      · rw [ite_eq_right hi, ite_eq_right hi9]
        by_cases hi10 : i = 10
        · subst hi10; simp [List.getD_eq_getElem?_getD]
        · rw [getD_ge _ i (by simp; omega), getD_ge _ (i - 1) (by simp; omega)]
    rw [del_unused 9 C1.gates C1.output _ _ (by simp) (by simp) hbase hno9 hout9]
    exact hC1eval x
  have kill_no10 : (∀ g ∈ C1.gates, 10 ∉ g.inputs) → False := by
    intro hno10
    have hout10 : C1.output ≠ 10 := by
      intro heq
      have hx := hC1eval (fun j => decide (j = 0))
      have hkeep : ∀ (gs : List Gate) (w : List Bool), 10 < w.length →
          (gs.foldl step w).getD 10 false = w.getD 10 false := by
        intro gs
        induction gs with
        | nil => intro w _; rfl
        | cons g gs ih =>
          intro w hw
          rw [List.foldl_cons, ih _ (by simp [step]; omega)]
          dsimp only [step]
          rw [getD_snoc, ite_eq_left hw]
      have h10 : C1.eval (List.ofFn (fun j : Fin 9 => decide (j = 0)) ++ [!decide ((0 : Fin 9) = 0), decide ((0 : Fin 9) = 0) || decide (k = 0)]) =
          (List.ofFn (fun j : Fin 9 => decide (j = 0)) ++ [!decide ((0 : Fin 9) = 0), decide ((0 : Fin 9) = 0) || decide (k = 0)]).getD 10 false := by
        change (C1.gates.foldl step _).getD C1.output false = _
        rw [heq, hkeep _ _ (by simp)]
      rw [h10] at hx
      have hLHS : (List.ofFn (fun j : Fin 9 => decide (j = 0)) ++ [!decide ((0 : Fin 9) = 0), decide ((0 : Fin 9) = 0) || decide (k = 0)]).getD 10 false = true := by
        simp [List.getD_eq_getElem?_getD]
      have hRHS : edgeF (fun j : Fin 9 => decide (j = 0)) = false := by decide
      rw [hLHS, hRHS] at hx
      exact Bool.noConfusion hx
    let f : ℕ → ℕ := fun i => if i < 10 then i else if i = 10 then 0 else i - 1
    let C14 : Circuit := ⟨⟨GateOp.not, [0]⟩ :: C1.gates.map fun g => ⟨g.op, g.inputs.map f⟩, f C1.output⟩
    have hfan14 : FanInTwo C14 := by
      intro g hg
      simp only [C14, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g0, hg0, rfl⟩
      · exact ⟨by simp, by simp⟩
      · obtain ⟨hop, hlen⟩ := hfan1 g0 hg0
        exact ⟨hop, by simpa using hlen⟩
    have hsz14 : C14.size ≤ 14 := by
      change (C1.gates.map _).length + 1 ≤ 14
      rw [List.length_map]; change C1.gates.length = 13 at hsz13; omega
    obtain ⟨x, hx⟩ := h14 C14 hfan14 hsz14
    apply hx
    have h0step : step (List.ofFn x) ⟨GateOp.not, [0]⟩ = List.ofFn x ++ [!x 0] := by
      have h0 : (List.ofFn x).getD 0 false = x 0 := by rw [getD_ofFn x 0 (by omega)]; rfl
      dsimp only [step]
      rw [eval_not]
      simp only [List.map_cons, List.map_nil, h0, List.headD_cons]
    change ((C1.gates.map fun g => ⟨g.op, g.inputs.map f⟩).foldl step
      (step (List.ofFn x) ⟨GateOp.not, [0]⟩)).getD (f C1.output) false = _
    rw [h0step]
    have hbase : ∀ i, i ≠ 10 →
        (List.ofFn x ++ [!x 0, x 0 || x k]).getD i false =
        (List.ofFn x ++ [!x 0]).getD (f i) false := by
      intro i hi10
      dsimp [f]
      by_cases hi : i < 10
      · rw [ite_eq_left hi]
        have hrew : List.ofFn x ++ [!x 0, x 0 || x k] = (List.ofFn x ++ [!x 0]) ++ [x 0 || x k] := by simp
        rw [hrew, getD_snoc, ite_eq_left (by simp; omega)]
      · rw [ite_eq_right hi, ite_eq_right hi10]
        rw [getD_ge _ i (by simp; omega), getD_ge _ (i - 1) (by simp; omega)]
    rw [del_unused 10 C1.gates C1.output _ _ (by simp) (by simp) hbase hno10 hout10]
    exact hC1eval x
  let env0 : List (Sum Bool ℕ) :=
    [Sum.inl false, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5,
     Sum.inr 6, Sum.inr 7, Sum.inr 8, Sum.inl true, Sum.inr k.val]
  let stepSim : List Gate × List (Sum Bool ℕ) → Gate → List Gate × List (Sum Bool ℕ) :=
    fun st g =>
      let gs' := st.1
      let env := st.2
      let v : ℕ → Sum Bool ℕ := fun i => env.getD i (Sum.inl false)
      GateOp.casesOn g.op
        (List.casesOn g.inputs (gs', env ++ [Sum.inl true]) fun a rest =>
          List.casesOn rest (gs', env ++ [v a]) fun b _ =>
            Sum.elim
              (fun ba => Bool.casesOn ba (gs', env ++ [Sum.inl false]) (gs', env ++ [v b]))
              (fun ja => Sum.elim
                (fun bb => Bool.casesOn bb (gs', env ++ [Sum.inl false]) (gs', env ++ [Sum.inr ja]))
                (fun jb => (gs' ++ [⟨GateOp.and, [ja, jb]⟩], env ++ [Sum.inr (9 + gs'.length)]))
                (v b))
              (v a))
        (List.casesOn g.inputs (gs', env ++ [Sum.inl false]) fun a rest =>
          List.casesOn rest (gs', env ++ [v a]) fun b _ =>
            Sum.elim
              (fun ba => Bool.casesOn ba (gs', env ++ [v b]) (gs', env ++ [Sum.inl true]))
              (fun ja => Sum.elim
                (fun bb => Bool.casesOn bb (gs', env ++ [Sum.inr ja]) (gs', env ++ [Sum.inl true]))
                (fun jb => (gs' ++ [⟨GateOp.or, [ja, jb]⟩], env ++ [Sum.inr (9 + gs'.length)]))
                (v b))
              (v a))
        (List.casesOn g.inputs (gs', env ++ [Sum.inl true]) fun a _ =>
          Sum.elim
            (fun b => (gs', env ++ [Sum.inl (!b)]))
            (fun j => (gs' ++ [⟨GateOp.not, [j]⟩], env ++ [Sum.inr (9 + gs'.length)]))
            (v a))
        (fun _ => (gs', env ++ [Sum.inl false]))
        (gs', env ++ [Sum.inl false])
  have sim_step_ok : ∀ (st : List Gate × List (Sum Bool ℕ)) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i j, st.2.getD i (Sum.inl false) = Sum.inr j → j < 9 + st.1.length) →
      (st.1.length ≤ (stepSim st g).1.length ∧ (stepSim st g).1.length ≤ st.1.length + 1) ∧
      (stepSim st g).2.length = st.2.length + 1 ∧
      (∀ g' ∈ (stepSim st g).1, g' ∈ st.1 ∨ (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2)) ∧
      (∀ i < st.2.length, (stepSim st g).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false)) ∧
      (∀ i j, (stepSim st g).2.getD i (Sum.inl false) = Sum.inr j → j < 9 + (stepSim st g).1.length) := by
    intro st g hg hbd
    obtain ⟨gs', env⟩ := st
    dsimp only at hbd
    obtain ⟨hop, hglen⟩ := hg
    rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have hkeep : ∀ (z : Sum Bool ℕ) (hz : ∀ j, z = Sum.inr j → j < 9 + gs'.length),
        (gs'.length ≤ gs'.length ∧ gs'.length ≤ gs'.length + 1) ∧
        (env ++ [z]).length = env.length + 1 ∧
        (∀ g' ∈ gs', g' ∈ gs' ∨ (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2)) ∧
        (∀ i < env.length, (env ++ [z]).getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
        (∀ i j, (env ++ [z]).getD i (Sum.inl false) = Sum.inr j → j < 9 + gs'.length) := by
      intro z hz
      refine ⟨⟨le_rfl, by omega⟩, by simp, fun g' hg' => Or.inl hg', fun i hi => ?_, fun i j hij => ?_⟩
      · rw [getD_snoc_sum, ite_eq_left hi]
      · rw [getD_snoc_sum] at hij
        split_ifs at hij with h1 h2
        · exact hbd i j hij
        · exact hz j hij
    have hemit : ∀ (gnew : Gate),
        (gnew.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gnew.inputs.length ≤ 2) →
        (gs'.length ≤ (gs' ++ [gnew]).length ∧ (gs' ++ [gnew]).length ≤ gs'.length + 1) ∧
        (env ++ [Sum.inr (9 + gs'.length)]).length = env.length + 1 ∧
        (∀ g' ∈ gs' ++ [gnew], g' ∈ gs' ∨ (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2)) ∧
        (∀ i < env.length, (env ++ [Sum.inr (9 + gs'.length)]).getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
        (∀ i j, (env ++ [Sum.inr (9 + gs'.length)]).getD i (Sum.inl false) = Sum.inr j → j < 9 + (gs' ++ [gnew]).length) := by
      intro gnew hgnew
      refine ⟨⟨by simp, by simp⟩, by simp, fun g' hg' => ?_, fun i hi => ?_, fun i j hij => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h1 | rfl
        · exact Or.inl h1
        · exact Or.inr hgnew
      · rw [getD_snoc_sum, ite_eq_left hi]
      · rw [getD_snoc_sum] at hij
        split_ifs at hij with h1 h2
        · have := hbd i j hij; simp; omega
        · cases hij; simp
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim]; exact hkeep _ (fun _ h => by cases h)
      · dsimp only [stepSim]; exact hkeep _ (fun j h => hbd a j h)
      · dsimp only [stepSim]
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          cases ba
          · exact hkeep _ (fun _ h => by cases h)
          · exact hkeep _ (fun j h => hbd b j h)
        | inr ja =>
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb
            · exact hkeep _ (fun _ h => by cases h)
            · exact hkeep _ (fun j h => hbd a j (ha.trans h))
          | inr jb =>
            exact hemit ⟨GateOp.and, [ja, jb]⟩ ⟨by simp, by simp⟩
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim]; exact hkeep _ (fun _ h => by cases h)
      · dsimp only [stepSim]; exact hkeep _ (fun j h => hbd a j h)
      · dsimp only [stepSim]
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          cases ba
          · exact hkeep _ (fun j h => hbd b j h)
          · exact hkeep _ (fun _ h => by cases h)
        | inr ja =>
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            cases bb
            · exact hkeep _ (fun j h => hbd a j (ha.trans h))
            · exact hkeep _ (fun _ h => by cases h)
          | inr jb =>
            exact hemit ⟨GateOp.or, [ja, jb]⟩ ⟨by simp, by simp⟩
    · rcases ins with _ | ⟨a, rest⟩
      · dsimp only [stepSim]; exact hkeep _ (fun _ h => by cases h)
      · dsimp only [stepSim]
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          exact hkeep _ (fun _ h => by cases h)
        | inr ja =>
          exact hemit ⟨GateOp.not, [ja]⟩ ⟨by simp, by simp⟩
  have sim_step_eval : ∀ (x : Fin 9 → Bool) (gs' : List Gate) (env : List (Sum Bool ℕ)) (w : List Bool) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i j, env.getD i (Sum.inl false) = Sum.inr j → j < 9 + gs'.length) →
      w.length = env.length →
      (∀ i, Sum.elim (fun b => w.getD i false = b) (fun j => w.getD i false = (gs'.foldl step (List.ofFn x)).getD j false) (env.getD i (Sum.inl false))) →
      ∀ i, Sum.elim (fun b => (step w g).getD i false = b) (fun j => (step w g).getD i false = ((stepSim (gs', env) g).1.foldl step (List.ofFn x)).getD j false) ((stepSim (gs', env) g).2.getD i (Sum.inl false)) := by
    intro x gs' env w g hg hbd hlenw hrel
    obtain ⟨hop, hglen⟩ := hg
    let w' := gs'.foldl step (List.ofFn x)
    have hw'len : w'.length = 9 + gs'.length := by simp [w', foldl_len]
    have hno_emit : ∀ (z : Sum Bool ℕ),
        Sum.elim (fun b => g.op.eval (g.inputs.map fun i => w.getD i false) = b)
          (fun j => g.op.eval (g.inputs.map fun i => w.getD i false) = w'.getD j false) z →
        ∀ i, Sum.elim (fun b => (step w g).getD i false = b) (fun j => (step w g).getD i false = w'.getD j false)
          ((env ++ [z]).getD i (Sum.inl false)) := by
      intro z hz i
      dsimp only [step]
      rw [getD_snoc_sum, getD_snoc, hlenw]
      split_ifs with h1 h2
      · exact hrel i
      · exact hz
      · rfl
    have hemit : ∀ (gnew : Gate),
        gnew.op.eval (gnew.inputs.map fun j => w'.getD j false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) →
        ∀ i, Sum.elim (fun b => (step w g).getD i false = b) (fun j => (step w g).getD i false = ((gs' ++ [gnew]).foldl step (List.ofFn x)).getD j false)
          ((env ++ [Sum.inr (9 + gs'.length)]).getD i (Sum.inl false)) := by
      intro gnew hge i
      have hfold_new : (gs' ++ [gnew]).foldl step (List.ofFn x) = step w' gnew := by
        simp [w', List.foldl_append]
      rw [hfold_new]
      dsimp only [step]
      rw [getD_snoc_sum, getD_snoc, hlenw]
      split_ifs with h1 h2
      · have hri := hrel i
        cases hi : env.getD i (Sum.inl false) with
        | inl b =>
          rw [hi] at hri; exact hri
        | inr j =>
          rw [hi] at hri
          have hj : j < w'.length := by rw [hw'len]; exact hbd i j hi
          dsimp only [Sum.elim]
          rw [getD_snoc, ite_eq_left hj]; exact hri
      · dsimp only [Sum.elim]
        rw [getD_snoc, hw'len, ite_eq_right (by omega), ite_eq_left rfl, hge]
      · rfl
    rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim]; exact hno_emit (Sum.inl true) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_nil, List.all_nil])
      · dsimp only [stepSim]
        have hra := hrel a
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hno_emit (Sum.inl ba) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hra])
        | inr ja =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hno_emit (Sum.inr ja) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hra]; rfl)
      · simp only [List.length_cons] at hglen
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        dsimp only [stepSim]
        have hra := hrel a
        have hrb := hrel b
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          cases ba
          · exact hno_emit (Sum.inl false) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hra, Bool.false_and])
          · cases hb : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hb] at hrb; dsimp only [Sum.elim] at hrb
              exact hno_emit (Sum.inl bb) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hra, hrb, Bool.true_and, Bool.and_true])
            | inr jb =>
              rw [hb] at hrb; dsimp only [Sum.elim] at hrb
              exact hno_emit (Sum.inr jb) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hra, hrb, Bool.true_and, Bool.and_true]; rfl)
        | inr ja =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hb] at hrb; dsimp only [Sum.elim] at hrb
            cases bb
            · exact hno_emit (Sum.inl false) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hrb, Bool.false_and, Bool.and_false])
            · exact hno_emit (Sum.inr ja) (by dsimp only [Sum.elim]; rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hra, hrb, Bool.and_true]; rfl)
          | inr jb =>
            rw [hb] at hrb; dsimp only [Sum.elim] at hrb
            exact hemit ⟨GateOp.and, [ja, jb]⟩ (by rw [eval_and, eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hra, hrb]; rfl)
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim]; exact hno_emit (Sum.inl false) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_nil, List.any_nil])
      · dsimp only [stepSim]
        have hra := hrel a
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hno_emit (Sum.inl ba) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hra])
        | inr ja =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hno_emit (Sum.inr ja) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hra]; rfl)
      · simp only [List.length_cons] at hglen
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        dsimp only [stepSim]
        have hra := hrel a
        have hrb := hrel b
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          cases ba
          · cases hb : env.getD b (Sum.inl false) with
            | inl bb =>
              rw [hb] at hrb; dsimp only [Sum.elim] at hrb
              exact hno_emit (Sum.inl bb) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hra, hrb, Bool.false_or, Bool.or_false])
            | inr jb =>
              rw [hb] at hrb; dsimp only [Sum.elim] at hrb
              exact hno_emit (Sum.inr jb) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hra, hrb, Bool.false_or, Bool.or_false]; rfl)
          · exact hno_emit (Sum.inl true) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hra, Bool.true_or])
        | inr ja =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hb] at hrb; dsimp only [Sum.elim] at hrb
            cases bb
            · exact hno_emit (Sum.inr ja) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hra, hrb, Bool.or_false]; rfl)
            · exact hno_emit (Sum.inl true) (by dsimp only [Sum.elim]; rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hrb, Bool.true_or, Bool.or_true])
          | inr jb =>
            rw [hb] at hrb; dsimp only [Sum.elim] at hrb
            exact hemit ⟨GateOp.or, [ja, jb]⟩ (by rw [eval_or, eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hra, hrb]; rfl)
    · rcases ins with _ | ⟨a, rest⟩
      · dsimp only [stepSim]; exact hno_emit (Sum.inl true) (by dsimp only [Sum.elim]; rw [eval_not]; simp only [List.map_nil, List.headD_nil, Bool.not_false])
      · dsimp only [stepSim]
        have hra := hrel a
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hno_emit (Sum.inl (!ba)) (by dsimp only [Sum.elim]; rw [eval_not]; simp only [List.map_cons, List.headD_cons, hra])
        | inr ja =>
          rw [ha] at hra; dsimp only [Sum.elim] at hra
          exact hemit ⟨GateOp.not, [ja]⟩ (by rw [eval_not, eval_not]; simp only [List.map_cons, List.headD_cons, hra]; rfl)
  have sim_fold_len : ∀ (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i j, st.2.getD i (Sum.inl false) = Sum.inr j → j < 9 + st.1.length) →
      (st.1.length ≤ (gs.foldl stepSim st).1.length ∧ (gs.foldl stepSim st).1.length ≤ st.1.length + gs.length) ∧
      (gs.foldl stepSim st).2.length = st.2.length + gs.length ∧
      (∀ g ∈ (gs.foldl stepSim st).1, g ∈ st.1 ∨ (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)) ∧
      (∀ i < st.2.length, (gs.foldl stepSim st).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false)) ∧
      (∀ i j, (gs.foldl stepSim st).2.getD i (Sum.inl false) = Sum.inr j → j < 9 + (gs.foldl stepSim st).1.length) := by
    intro gs
    induction gs with
    | nil =>
      intro st _ hbd
      exact ⟨⟨le_rfl, by simp⟩, by simp, fun g hg => Or.inl hg, fun _ _ => rfl, hbd⟩
    | cons g gs ih =>
      intro st hgs hbd
      have hg := hgs g (by simp)
      obtain ⟨⟨h1a, h1b⟩, h2, h3, h4, h5⟩ := sim_step_ok st g hg hbd
      obtain ⟨⟨h1a', h1b'⟩, h2', h3', h4', h5'⟩ := ih (stepSim st g) (fun g' hg' => hgs g' (by simp [hg'])) h5
      refine ⟨⟨by simp only [List.foldl_cons]; omega, by simp only [List.foldl_cons, List.length_cons]; omega⟩,
        by simp only [List.foldl_cons, List.length_cons]; omega, fun g' hg' => ?_, fun i hi => ?_, h5'⟩
      · rcases h3' g' hg' with h | h
        · exact h3 g' h
        · exact Or.inr h
      · rw [List.foldl_cons, h4' i (by omega), h4 i hi]
  have sim_fold_eval : ∀ (gs : List Gate) (x : Fin 9 → Bool) (st : List Gate × List (Sum Bool ℕ)) (w : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i j, st.2.getD i (Sum.inl false) = Sum.inr j → j < 9 + st.1.length) →
      w.length = st.2.length →
      (∀ i, Sum.elim (fun b => w.getD i false = b) (fun j => w.getD i false = (st.1.foldl step (List.ofFn x)).getD j false) (st.2.getD i (Sum.inl false))) →
      ∀ i, Sum.elim (fun b => (gs.foldl step w).getD i false = b) (fun j => (gs.foldl step w).getD i false = ((gs.foldl stepSim st).1.foldl step (List.ofFn x)).getD j false) ((gs.foldl stepSim st).2.getD i (Sum.inl false)) := by
    intro gs
    induction gs with
    | nil => intro x st w _ _ _ hrel i; exact hrel i
    | cons g gs ih =>
      intro x st w hgs hbd hlenw hrel i
      have hg := hgs g (by simp)
      obtain ⟨_, hlen2, _, _, hbd2⟩ := sim_step_ok st g hg hbd
      have hev := sim_step_eval x st.1 st.2 w g hg hbd hlenw hrel
      exact ih x (stepSim st g) (step w g) (fun g' hg' => hgs g' (by simp [hg'])) hbd2 (by simp [step, hlenw, hlen2]) hev i
  have hbd0 : ∀ i j, env0.getD i (Sum.inl false) = Sum.inr j → j < 9 + ([] : List Gate).length := by
    intro i j hij
    have hklt : k.val < 9 := k.isLt
    by_cases hi : i < 11
    · interval_cases i <;> simp [env0, List.getD_eq_getElem?_getD] at hij <;> subst hij <;> omega
    · rw [getD_ge_sum env0 i (by simp [env0]; omega)] at hij
      cases hij
  obtain ⟨⟨_, hfin_le⟩, hfin_envlen, hfin_mem, hfin_keep, _⟩ :=
    sim_fold_len C1.gates ([], env0) hfan1 hbd0
  let st_fin := C1.gates.foldl stepSim ([], env0)
  have hfin_fan : FanInTwo ⟨st_fin.1, 0⟩ := by
    intro g hg
    rcases hfin_mem g hg with h | h
    · simp at h
    · exact h
  have hbase_sim : ∀ (x : Fin 9 → Bool), x 0 = false →
      ∀ i, Sum.elim (fun b => (List.ofFn x ++ [!x 0, x 0 || x k]).getD i false = b)
        (fun j => (List.ofFn x ++ [!x 0, x 0 || x k]).getD i false = (List.ofFn x).getD j false)
        (env0.getD i (Sum.inl false)) := by
    intro x hx0 i
    have hlt9 : ∀ m : ℕ, m < 9 → (List.ofFn x ++ [!x 0, x 0 || x k]).getD m false = (List.ofFn x).getD m false := by
      intro m hm
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getD_eq_getElem _ _ (by simp; omega)]
    by_cases hi : i < 11
    · have hklt : k.val < 9 := k.isLt
      interval_cases i
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 0 false = false
        rw [hlt9 0 (by omega), getD_ofFn x 0 (by omega)]; exact hx0
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 1 false = (List.ofFn x).getD 1 false
        exact hlt9 1 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 2 false = (List.ofFn x).getD 2 false
        exact hlt9 2 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 3 false = (List.ofFn x).getD 3 false
        exact hlt9 3 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 4 false = (List.ofFn x).getD 4 false
        exact hlt9 4 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 5 false = (List.ofFn x).getD 5 false
        exact hlt9 5 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 6 false = (List.ofFn x).getD 6 false
        exact hlt9 6 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 7 false = (List.ofFn x).getD 7 false
        exact hlt9 7 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 8 false = (List.ofFn x).getD 8 false
        exact hlt9 8 (by omega)
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 9 false = true
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)]
        simp [hx0]
      · change (List.ofFn x ++ [!x 0, x 0 || x k]).getD 10 false = (List.ofFn x).getD k.val false
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp), getD_ofFn x k.val hklt]
        simp [hx0]
    · rw [getD_ge_sum env0 i (by simp [env0]; omega), getD_ge _ i (by simp; omega)]; rfl
  have hfin_eval : ∀ (x : Fin 9 → Bool), x 0 = false →
      Sum.elim (fun b => edgeF x = b) (fun j => edgeF x = (st_fin.1.foldl step (List.ofFn x)).getD j false)
        (st_fin.2.getD C1.output (Sum.inl false)) := by
    intro x hx0
    have h := sim_fold_eval C1.gates x ([], env0) (List.ofFn x ++ [!x 0, x 0 || x k])
      hfan1 hbd0 (by simp [env0]) (hbase_sim x hx0) C1.output
    have hev := hC1eval x
    change (C1.gates.foldl step (List.ofFn x ++ [!x 0, x 0 || x k])).getD C1.output false = edgeF x at hev
    rw [hev] at h
    exact h
  have hout_inr : ∃ out', st_fin.2.getD C1.output (Sum.inl false) = Sum.inr out' := by
    cases h : st_fin.2.getD C1.output (Sum.inl false) with
    | inr out' => exact ⟨out', rfl⟩
    | inl b =>
      have hA := hfin_eval (fun _ => false) rfl
      have hB := hfin_eval (fun j => decide (j = 1 ∨ j = 2)) (by decide)
      rw [h] at hA hB
      have heA : edgeF (fun _ => false) = false := by decide
      have heB : edgeF (fun j => decide (j = 1 ∨ j = 2)) = true := by decide
      dsimp only [Sum.elim] at hA hB
      rw [heA] at hA; rw [heB] at hB
      rw [← hA] at hB; exact Bool.noConfusion hB
  obtain ⟨out', hout_eq⟩ := hout_inr
  have hout_ne0 : C1.output ≠ 0 := by
    intro heq
    rw [heq, hfin_keep 0 (by simp [env0])] at hout_eq
    simp [env0, List.getD_eq_getElem?_getD] at hout_eq
  have hout_ne9 : C1.output ≠ 9 := by
    intro heq
    rw [heq, hfin_keep 9 (by simp [env0])] at hout_eq
    simp [env0, List.getD_eq_getElem?_getD] at hout_eq
  have hfin_ge12 : 12 ≤ st_fin.1.length := by
    by_contra hlt12
    have hle11 : (⟨st_fin.1, out'⟩ : Circuit).size ≤ 11 := by rw [size_eq]; dsimp only; omega
    obtain ⟨x, hx0, hxne⟩ := h11 ⟨st_fin.1, out'⟩ hfin_fan hle11
    apply hxne
    have hfe := hfin_eval x hx0
    rw [hout_eq] at hfe
    dsimp only [Sum.elim] at hfe
    have hedge0 : edgeF x =
        (x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 1 && x 6 || x 2 && x 7 ||
         x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      simp [edgeF, hx0]
    exact hfe.symm.trans hedge0
  have no_elim_step : ∀ (st : List Gate × List (Sum Bool ℕ)) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (g.op = GateOp.not → g.inputs.length ≤ 1) →
      (stepSim st g).1.length = st.1.length + 1 →
      (∀ i ∈ g.inputs, ∃ j, st.2.getD i (Sum.inl false) = Sum.inr j) ∧
      ∃ j, (stepSim st g).2.getD st.2.length (Sum.inl false) = Sum.inr j := by
    intro st g hg hnot hlen1
    obtain ⟨gs', env⟩ := st
    obtain ⟨hop, hglen⟩ := hg
    rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim] at hlen1; omega
      · dsimp only [stepSim] at hlen1; omega
      · simp only [List.length_cons] at hglen
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        dsimp only [stepSim] at hlen1 ⊢
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hlen1
          cases ba <;> (dsimp only [Sum.elim] at hlen1; omega)
        | inr ja =>
          rw [ha] at hlen1
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hb] at hlen1
            cases bb <;> (dsimp only [Sum.elim] at hlen1; omega)
          | inr jb =>
            refine ⟨fun i hi => ?_, ⟨9 + gs'.length, ?_⟩⟩
            · simp at hi; rcases hi with rfl | rfl; exact ⟨ja, ha⟩; exact ⟨jb, hb⟩
            · dsimp only [Sum.elim]
              rw [getD_snoc_sum, ite_eq_right (by omega), ite_eq_left rfl]
    · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · dsimp only [stepSim] at hlen1; omega
      · dsimp only [stepSim] at hlen1; omega
      · simp only [List.length_cons] at hglen
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        dsimp only [stepSim] at hlen1 ⊢
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hlen1
          cases ba <;> (dsimp only [Sum.elim] at hlen1; omega)
        | inr ja =>
          rw [ha] at hlen1
          cases hb : env.getD b (Sum.inl false) with
          | inl bb =>
            rw [hb] at hlen1
            cases bb <;> (dsimp only [Sum.elim] at hlen1; omega)
          | inr jb =>
            refine ⟨fun i hi => ?_, ⟨9 + gs'.length, ?_⟩⟩
            · simp at hi; rcases hi with rfl | rfl; exact ⟨ja, ha⟩; exact ⟨jb, hb⟩
            · dsimp only [Sum.elim]
              rw [getD_snoc_sum, ite_eq_right (by omega), ite_eq_left rfl]
    · have hnot1 := hnot rfl
      rcases ins with _ | ⟨a, rest⟩
      · dsimp only [stepSim] at hlen1; omega
      · simp only [List.length_cons] at hnot1
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest
        dsimp only [stepSim] at hlen1 ⊢
        cases ha : env.getD a (Sum.inl false) with
        | inl ba =>
          rw [ha] at hlen1; dsimp only [Sum.elim] at hlen1; omega
        | inr ja =>
          refine ⟨fun i hi => ?_, ⟨9 + gs'.length, ?_⟩⟩
          · simp at hi; subst hi; exact ⟨ja, ha⟩
          · dsimp only [Sum.elim]
            rw [getD_snoc_sum, ite_eq_right (by omega), ite_eq_left rfl]
  have no_elim_fold : ∀ (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∀ i j, st.2.getD i (Sum.inl false) = Sum.inr j → j < 9 + st.1.length) →
      (gs.foldl stepSim st).1.length = st.1.length + gs.length →
      (∀ g ∈ gs, ∀ p < st.2.length, (∃ b, st.2.getD p (Sum.inl false) = Sum.inl b) → p ∉ g.inputs) ∧
      (∀ p, st.2.length ≤ p → p < (gs.foldl stepSim st).2.length → ∃ j, (gs.foldl stepSim st).2.getD p (Sum.inl false) = Sum.inr j) := by
    intro gs
    induction gs with
    | nil =>
      intro st _ _ _ _
      exact ⟨fun _ h => by simp at h, fun _ h1 h2 => by simp at h2; omega⟩
    | cons g gs ih =>
      intro st hgs hnot hbd hlen
      have hg := hgs g (by simp)
      obtain ⟨⟨h1a, h1b⟩, hlen2, _, h4, hbd2⟩ := sim_step_ok st g hg hbd
      obtain ⟨⟨_, hrest_le⟩, hlen2', _, h4', _⟩ :=
        sim_fold_len gs (stepSim st g) (fun g' hg' => hgs g' (by simp [hg'])) hbd2
      have hstep_len : (stepSim st g).1.length = st.1.length + 1 := by
        simp only [List.foldl_cons, List.length_cons] at hlen; omega
      have hrest_len : (gs.foldl stepSim (stepSim st g)).1.length = (stepSim st g).1.length + gs.length := by
        simp only [List.foldl_cons, List.length_cons] at hlen; omega
      obtain ⟨hg_in, hg_out⟩ := no_elim_step st g hg (hnot g (by simp)) hstep_len
      obtain ⟨hgs_in, hgs_out⟩ := ih (stepSim st g) (fun g' hg' => hgs g' (by simp [hg']))
        (fun g' hg' => hnot g' (by simp [hg'])) hbd2 hrest_len
      refine ⟨fun g' hg' p hp hex hmem => ?_, fun p hp1 hp2 => ?_⟩
      · rcases hex with ⟨b, hpb⟩
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · obtain ⟨j, hj⟩ := hg_in p hmem
          rw [hpb] at hj; cases hj
        · exact hgs_in g' hg' p (by omega) ⟨b, by rw [h4 p hp, hpb]⟩ hmem
      · by_cases hpe : p = st.2.length
        · subst hpe
          obtain ⟨j, hj⟩ := hg_out
          exact ⟨j, by rw [List.foldl_cons, h4' _ (by omega), hj]⟩
        · exact hgs_out p (by omega) hp2
  have split_one_elim : ∀ (gs : List Gate) (st : List Gate × List (Sum Bool ℕ)),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i j, st.2.getD i (Sum.inl false) = Sum.inr j → j < 9 + st.1.length) →
      (gs.foldl stepSim st).1.length + 1 = st.1.length + gs.length →
      ∃ pref g0 suff, gs = pref ++ [g0] ++ suff ∧
        (pref.foldl stepSim st).1.length = st.1.length + pref.length ∧
        (stepSim (pref.foldl stepSim st) g0).1.length = (pref.foldl stepSim st).1.length ∧
        (suff.foldl stepSim (stepSim (pref.foldl stepSim st) g0)).1.length =
          (stepSim (pref.foldl stepSim st) g0).1.length + suff.length := by
    intro gs
    induction gs with
    | nil => intro st _ _ h; simp at h
    | cons g gs ih =>
      intro st hgs hbd hlen
      have hg := hgs g (by simp)
      obtain ⟨⟨h1a, h1b⟩, _, _, _, hbd2⟩ := sim_step_ok st g hg hbd
      obtain ⟨⟨_, hrest_le⟩, _, _, _, _⟩ :=
        sim_fold_len gs (stepSim st g) (fun g' hg' => hgs g' (by simp [hg'])) hbd2
      simp only [List.foldl_cons, List.length_cons] at hlen
      by_cases h0 : (stepSim st g).1.length = st.1.length
      · refine ⟨[], g, gs, rfl, by simp, h0, ?_⟩
        simp only [List.foldl_nil]; omega
      · have h1 : (stepSim st g).1.length = st.1.length + 1 := by omega
        obtain ⟨pref, g0, suff, hgs_eq, hp1, hp2, hp3⟩ :=
          ih (stepSim st g) (fun g' hg' => hgs g' (by simp [hg'])) hbd2 (by omega)
        refine ⟨g :: pref, g0, suff, by simp [hgs_eq], ?_, hp2, hp3⟩
        simp only [List.foldl_cons, List.length_cons]; omega
  by_cases hfull : st_fin.1.length = 13
  · have hno9 : ∀ g ∈ C1.gates, 9 ∉ g.inputs := by
      have h := (no_elim_fold C1.gates ([], env0) hfan1 hnot1 hbd0 (by change st_fin.1.length = 0 + C1.gates.length; change C1.gates.length = 13 at hsz13; omega)).1
      intro g hg
      exact h g hg 9 (by simp [env0]) ⟨true, by simp [env0, List.getD_eq_getElem?_getD]⟩
    exact kill_no9 hno9 hout_ne9
  · have h12 : st_fin.1.length = 12 := by
      change C1.gates.length = 13 at hsz13
      have : st_fin.1.length ≤ 13 := by simpa [st_fin, hsz13] using hfin_le
      omega
    obtain ⟨pref, g0, suff, hsplit, hpref_len, hg0_len, hsuff_len⟩ :=
      split_one_elim C1.gates ([], env0) hfan1 hbd0 (by change st_fin.1.length + 1 = 0 + C1.gates.length; change C1.gates.length = 13 at hsz13; omega)
    let st1 := pref.foldl stepSim ([], env0)
    let st2 := stepSim st1 g0
    have hpref_fan : ∀ g ∈ pref, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan1 g (by rw [hsplit]; simp [hg])
    have hpref_not : ∀ g ∈ pref, g.op = GateOp.not → g.inputs.length ≤ 1 :=
      fun g hg => hnot1 g (by rw [hsplit]; simp [hg])
    have hg0_fan : g0.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g0.inputs.length ≤ 2 :=
      hfan1 g0 (by rw [hsplit]; simp)
    have hg0_not : g0.op = GateOp.not → g0.inputs.length ≤ 1 :=
      hnot1 g0 (by rw [hsplit]; simp)
    have hsuff_fan : ∀ g ∈ suff, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan1 g (by rw [hsplit]; simp [hg])
    have hsuff_not : ∀ g ∈ suff, g.op = GateOp.not → g.inputs.length ≤ 1 :=
      fun g hg => hnot1 g (by rw [hsplit]; simp [hg])
    obtain ⟨_, hst1_envlen, _, hst1_keep, hbd1⟩ :=
      sim_fold_len pref ([], env0) hpref_fan hbd0
    obtain ⟨_, hst2_envlen, _, hst2_keep, hbd2⟩ := sim_step_ok st1 g0 hg0_fan hbd1
    obtain ⟨_, _, _, hst3_keep, _⟩ :=
      sim_fold_len suff st2 hsuff_fan hbd2
    obtain ⟨hpref_no, hpref_inr⟩ := no_elim_fold pref ([], env0) hpref_fan hpref_not hbd0 hpref_len
    obtain ⟨hsuff_no, _⟩ := no_elim_fold suff st2 hsuff_fan hsuff_not hbd2 hsuff_len
    have hst1_len : st1.2.length = 11 + pref.length := by simpa [st1, env0] using hst1_envlen
    have hst2_len : st2.2.length = 11 + pref.length + 1 := by simpa [st2, hst1_len] using hst2_envlen
    have hst1_inl : ∀ p b, st1.2.getD p (Sum.inl false) = Sum.inl b →
        (p = 0 ∧ b = false) ∨ (p = 9 ∧ b = true) ∨ (11 + pref.length ≤ p ∧ b = false) := by
      intro p b hpb
      by_cases hp11 : p < 11
      · rw [hst1_keep p (by simp [env0]; omega)] at hpb
        interval_cases p <;> simp [env0, List.getD_eq_getElem?_getD] at hpb
        · exact Or.inl ⟨rfl, hpb⟩
        · exact Or.inr (Or.inl ⟨rfl, hpb⟩)
      · by_cases hpst1 : p < st1.2.length
        · obtain ⟨j, hj⟩ := hpref_inr p (by simp [env0]; omega) hpst1
          rw [hpb] at hj; cases hj
        · rw [getD_ge_sum st1.2 p (by omega)] at hpb
          cases hpb
          exact Or.inr (Or.inr ⟨by omega, rfl⟩)
    have hpref_no0 : ∀ g ∈ pref, 0 ∉ g.inputs := fun g hg =>
      hpref_no g hg 0 (by simp [env0]) ⟨false, by simp [env0, List.getD_eq_getElem?_getD]⟩
    have hpref_no9 : ∀ g ∈ pref, 9 ∉ g.inputs := fun g hg =>
      hpref_no g hg 9 (by simp [env0]) ⟨true, by simp [env0, List.getD_eq_getElem?_getD]⟩
    have hsuff_no0 : ∀ g ∈ suff, 0 ∉ g.inputs := fun g hg =>
      hsuff_no g hg 0 (by omega) ⟨false, by rw [hst2_keep 0 (by omega), hst1_keep 0 (by simp [env0])]; simp [env0, List.getD_eq_getElem?_getD]⟩
    have hsuff_no9 : ∀ g ∈ suff, 9 ∉ g.inputs := fun g hg =>
      hsuff_no g hg 9 (by omega) ⟨true, by rw [hst2_keep 9 (by omega), hst1_keep 9 (by simp [env0])]; simp [env0, List.getD_eq_getElem?_getD]⟩
    have kill_dead_g0 : (∃ b, st2.2.getD (11 + pref.length) (Sum.inl false) = Sum.inl b) → False := by
      intro hex
      rcases hex with ⟨b, hb⟩
      have hsuff_nod : ∀ g ∈ suff, (11 + pref.length) ∉ g.inputs :=
        fun g hg => hsuff_no g hg (11 + pref.length) (by omega) ⟨b, hb⟩
      have hout_ned : C1.output ≠ 11 + pref.length := by
        intro heq
        have hfin_eq : st_fin = suff.foldl stepSim st2 := by
          simp [st_fin, st2, st1, hsplit, List.foldl_append]
        rw [hfin_eq, heq, hst3_keep (11 + pref.length) (by omega), hb] at hout_eq
        cases hout_eq
      let pos := 11 + pref.length
      let f : ℕ → ℕ := fun i => if i < pos then i else if i = pos then 0 else i - 1
      let D : Circuit := ⟨pref ++ suff.map fun g => ({ op := g.op, inputs := g.inputs.map f } : Gate), f C1.output⟩
      have hfanD : FanInTwo D := by
        intro g hg
        simp only [D, List.mem_append, List.mem_map] at hg
        rcases hg with hp | ⟨g', hg', rfl⟩
        · exact hpref_fan g hp
        · obtain ⟨hop, hl⟩ := hsuff_fan g' hg'
          exact ⟨hop, by simpa using hl⟩
      have hszD : D.size ≤ 12 := by
        have hlen13 : pref.length + 1 + suff.length = 13 := by
          have := congrArg List.length hsplit
          change C1.gates.length = 13 at hsz13
          simp at this; omega
        rw [size_eq]; dsimp only [D]; rw [List.length_append, List.length_map]; omega
      apply mk14_of_le12 D hfanD hszD
      intro x
      let w0 := List.ofFn x ++ [!x 0, x 0 || x k]
      let wp := pref.foldl step w0
      have hwplen : wp.length = pos := by simp [wp, w0, pos, foldl_len]
      have hbase : ∀ i, i ≠ pos → (step wp g0).getD i false = wp.getD (f i) false := by
        intro i hip
        dsimp only [f, step]
        by_cases hi : i < pos
        · rw [ite_eq_left hi, getD_snoc, hwplen, ite_eq_left hi]
        · rw [ite_eq_right hi, ite_eq_right hip, getD_snoc, hwplen, ite_eq_right hi, ite_eq_right hip, getD_ge wp (i - 1) (by omega)]
      have hdel := del_unused pos suff C1.output (step wp g0) wp (by simp [step, hwplen]) (by omega) hbase hsuff_nod hout_ned
      have hC1x := hC1eval x
      change (C1.gates.foldl step w0).getD C1.output false = edgeF x at hC1x
      rw [hsplit, List.foldl_append, List.foldl_append] at hC1x
      change (suff.foldl step (step wp g0)).getD C1.output false = edgeF x at hC1x
      change ((pref ++ suff.map fun g => ({ op := g.op, inputs := g.inputs.map f } : Gate)).foldl step w0).getD (f C1.output) false = edgeF x
      rw [List.foldl_append]
      exact hdel.trans hC1x
    have kill_copy_g0 : ∀ a, a < 11 + pref.length →
        (∀ w : List Bool, w.length = 11 + pref.length → g0.op.eval (g0.inputs.map fun i => w.getD i false) = w.getD a false) →
        False := by
      intro a ha hcopy
      let pos := 11 + pref.length
      let f : ℕ → ℕ := fun i => if i < pos then i else if i = pos then a else i - 1
      let D : Circuit := ⟨pref ++ suff.map fun g => ({ op := g.op, inputs := g.inputs.map f } : Gate), f C1.output⟩
      have hfanD : FanInTwo D := by
        intro g hg
        simp only [D, List.mem_append, List.mem_map] at hg
        rcases hg with hp | ⟨g', hg', rfl⟩
        · exact hpref_fan g hp
        · obtain ⟨hop, hl⟩ := hsuff_fan g' hg'
          exact ⟨hop, by simpa using hl⟩
      have hszD : D.size ≤ 12 := by
        have hlen13 : pref.length + 1 + suff.length = 13 := by
          have := congrArg List.length hsplit
          change C1.gates.length = 13 at hsz13
          simp at this; omega
        rw [size_eq]; dsimp only [D]; rw [List.length_append, List.length_map]; omega
      apply mk14_of_le12 D hfanD hszD
      intro x
      let w0 := List.ofFn x ++ [!x 0, x 0 || x k]
      let wp := pref.foldl step w0
      have hwplen : wp.length = pos := by simp [wp, w0, pos, foldl_len]
      have hbase : ∀ i, (step wp g0).getD i false = wp.getD (f i) false := by
        intro i
        dsimp only [f, step]
        by_cases hi : i < pos
        · rw [ite_eq_left hi, getD_snoc, hwplen, ite_eq_left hi]
        · by_cases he : i = pos
          · rw [ite_eq_right hi, ite_eq_left he, getD_snoc, hwplen, ite_eq_right hi, ite_eq_left he]
            exact hcopy wp hwplen
          · rw [ite_eq_right hi, ite_eq_right he, getD_snoc, hwplen, ite_eq_right hi, ite_eq_right he, getD_ge wp (i - 1) (by omega)]
      have hdel := del_copy pos a suff C1.output (step wp g0) wp (by simp [step, hwplen]) (by omega) ha hbase
      have hC1x := hC1eval x
      change (C1.gates.foldl step w0).getD C1.output false = edgeF x at hC1x
      rw [hsplit, List.foldl_append, List.foldl_append] at hC1x
      change (suff.foldl step (step wp g0)).getD C1.output false = edgeF x at hC1x
      change ((pref ++ suff.map fun g => ({ op := g.op, inputs := g.inputs.map f } : Gate)).foldl step w0).getD (f C1.output) false = edgeF x
      rw [List.foldl_append]
      exact hdel.trans hC1x
    have hg0_form : g0.op = GateOp.and ∧ g0.inputs.length = 2 ∧ 9 ∈ g0.inputs ∧ 0 ∉ g0.inputs ∧ g0.inputs.Nodup := by
      rcases g0 with ⟨op, ins⟩
      obtain ⟨hop, hglen⟩ := hg0_fan
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have hdead_snoc : ∀ b, st2.2 = st1.2 ++ [Sum.inl b] → False := by
        intro b heq
        apply kill_dead_g0
        refine ⟨b, ?_⟩
        rw [heq, getD_snoc_sum, hst1_len, ite_eq_right (by omega), ite_eq_left rfl]
      rcases hop with rfl | rfl | rfl
      · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · exact False.elim (hdead_snoc true rfl)
        · cases ha : st1.2.getD a (Sum.inl false) with
          | inl ba =>
            exact False.elim (hdead_snoc ba (by dsimp only [st2, stepSim]; rw [ha]))
          | inr ja =>
            have halt : a < 11 + pref.length := by
              by_contra hge
              rw [getD_ge_sum st1.2 a (by omega)] at ha
              cases ha
            exact False.elim (kill_copy_g0 a halt (fun w _ => by rw [eval_and]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]))
        · simp only [List.length_cons] at hglen
          have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hrest
          cases ha : st1.2.getD a (Sum.inl false) with
          | inl ba =>
            cases ba
            · exact False.elim (hdead_snoc false (by dsimp only [st2, stepSim]; rw [ha]; rfl))
            · cases hb : st1.2.getD b (Sum.inl false) with
              | inl bb =>
                exact False.elim (hdead_snoc bb (by dsimp only [st2, stepSim]; rw [ha, hb]; rfl))
              | inr jb =>
                have ha9 : a = 9 := by
                  rcases hst1_inl a true ha with ⟨_, h⟩ | ⟨rfl, _⟩ | ⟨_, h⟩
                  · exact Bool.noConfusion h
                  · rfl
                  · exact Bool.noConfusion h
                have hbne0 : b ≠ 0 := by
                  intro h; subst h; rw [hst1_keep 0 (by simp [env0])] at hb; simp [env0, List.getD_eq_getElem?_getD] at hb
                have hbne9 : b ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at hb; simp [env0, List.getD_eq_getElem?_getD] at hb
                subst ha9
                exact ⟨rfl, rfl, by simp, by simp [Ne.symm hbne0], by simp [Ne.symm hbne9]⟩
          | inr ja =>
            cases hb : st1.2.getD b (Sum.inl false) with
            | inl bb =>
              cases bb
              · exact False.elim (hdead_snoc false (by dsimp only [st2, stepSim]; rw [ha, hb]; rfl))
              · have hb9 : b = 9 := by
                  rcases hst1_inl b true hb with ⟨_, h⟩ | ⟨rfl, _⟩ | ⟨_, h⟩
                  · exact Bool.noConfusion h
                  · rfl
                  · exact Bool.noConfusion h
                have hane0 : a ≠ 0 := by
                  intro h; subst h; rw [hst1_keep 0 (by simp [env0])] at ha; simp [env0, List.getD_eq_getElem?_getD] at ha
                have hane9 : a ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at ha; simp [env0, List.getD_eq_getElem?_getD] at ha
                subst hb9
                exact ⟨rfl, rfl, by simp, by simp [Ne.symm hane0], by simp [hane9]⟩
            | inr jb =>
              change ((stepSim st1 ⟨GateOp.and, [a, b]⟩).1).length = st1.1.length at hg0_len
              dsimp only [stepSim] at hg0_len
              rw [ha, hb] at hg0_len
              simp at hg0_len
      · rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · exact False.elim (hdead_snoc false rfl)
        · cases ha : st1.2.getD a (Sum.inl false) with
          | inl ba =>
            exact False.elim (hdead_snoc ba (by dsimp only [st2, stepSim]; rw [ha]))
          | inr ja =>
            have halt : a < 11 + pref.length := by
              by_contra hge
              rw [getD_ge_sum st1.2 a (by omega)] at ha
              cases ha
            exact False.elim (kill_copy_g0 a halt (fun w _ => by rw [eval_or]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]))
        · simp only [List.length_cons] at hglen
          have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hrest
          cases ha : st1.2.getD a (Sum.inl false) with
          | inl ba =>
            cases ba
            · cases hb : st1.2.getD b (Sum.inl false) with
              | inl bb =>
                exact False.elim (hdead_snoc bb (by dsimp only [st2, stepSim]; rw [ha, hb]; rfl))
              | inr jb =>
                have hane9 : a ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at ha; simp [env0, List.getD_eq_getElem?_getD] at ha
                have hbne9 : b ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at hb; simp [env0, List.getD_eq_getElem?_getD] at hb
                have hno9 : ∀ g ∈ C1.gates, 9 ∉ g.inputs := by
                  intro g hg
                  rw [hsplit] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hp | rfl) | hs
                  · exact hpref_no9 g hp
                  · simp [Ne.symm hane9, Ne.symm hbne9]
                  · exact hsuff_no9 g hs
                exact False.elim (kill_no9 hno9 hout_ne9)
            · exact False.elim (hdead_snoc true (by dsimp only [st2, stepSim]; rw [ha]; rfl))
          | inr ja =>
            cases hb : st1.2.getD b (Sum.inl false) with
            | inl bb =>
              cases bb
              · have hane9 : a ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at ha; simp [env0, List.getD_eq_getElem?_getD] at ha
                have hbne9 : b ≠ 9 := by
                  intro h; subst h; rw [hst1_keep 9 (by simp [env0])] at hb; simp [env0, List.getD_eq_getElem?_getD] at hb
                have hno9 : ∀ g ∈ C1.gates, 9 ∉ g.inputs := by
                  intro g hg
                  rw [hsplit] at hg
                  simp only [List.mem_append, List.mem_singleton] at hg
                  rcases hg with (hp | rfl) | hs
                  · exact hpref_no9 g hp
                  · simp [Ne.symm hane9, Ne.symm hbne9]
                  · exact hsuff_no9 g hs
                exact False.elim (kill_no9 hno9 hout_ne9)
              · exact False.elim (hdead_snoc true (by dsimp only [st2, stepSim]; rw [ha, hb]; rfl))
            | inr jb =>
              change ((stepSim st1 ⟨GateOp.or, [a, b]⟩).1).length = st1.1.length at hg0_len
              dsimp only [stepSim] at hg0_len
              rw [ha, hb] at hg0_len
              simp at hg0_len
      · rcases ins with _ | ⟨a, rest⟩
        · exact False.elim (hdead_snoc true rfl)
        · cases ha : st1.2.getD a (Sum.inl false) with
          | inl ba =>
            exact False.elim (hdead_snoc (!ba) (by dsimp only [st2, stepSim]; rw [ha]; rfl))
          | inr ja =>
            change ((stepSim st1 ⟨GateOp.not, a :: rest⟩).1).length = st1.1.length at hg0_len
            dsimp only [stepSim] at hg0_len
            rw [ha] at hg0_len
            simp at hg0_len
    obtain ⟨hg0_and, hg0_len2, hg0_mem9, hg0_no0, hg0_nd⟩ := hg0_form
    have hall_no0 : ∀ g ∈ C1.gates, 0 ∉ g.inputs := by
      intro g hg
      rw [hsplit] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hp | rfl) | hs
      · exact hpref_no0 g hp
      · exact hg0_no0
      · exact hsuff_no0 g hs
    have hcnt9 : C1.gates.countP (fun g => g.inputs.contains 9) = 1 := by
      rw [hsplit, List.countP_append, List.countP_append]
      have hp0 : pref.countP (fun g => g.inputs.contains 9) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg
        simp [hpref_no9 g hg]
      have hs0 : suff.countP (fun g => g.inputs.contains 9) = 0 := by
        rw [List.countP_eq_zero]
        intro g hg
        simp [hsuff_no9 g hg]
      have hg1 : ([g0] : List Gate).countP (fun g => g.inputs.contains 9) = 1 := by
        simp [hg0_mem9]
      omega
    have h9props : ∀ g ∈ C1.gates, 9 ∈ g.inputs → g.op = GateOp.and ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
      intro g hg h9
      rw [hsplit] at hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hp | rfl) | hs
      · exact False.elim (hpref_no9 g hp h9)
      · exact ⟨hg0_and, hg0_len2, hg0_nd⟩
      · exact False.elim (hsuff_no9 g hs h9)
    have hhas10 : ∃ g ∈ C1.gates, 10 ∈ g.inputs := by
      by_contra hno
      push Not at hno
      exact kill_no10 hno
    rcases hkcan with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨x, hx⟩ := h13a 1 (Or.inl rfl) C1 hfan1 hsz13 hall_no0 hout_ne0 hcnt9 h9props hout_ne9 hhas10
      exact hx (hC1eval x)
    · obtain ⟨x, hx⟩ := h13a 4 (Or.inr rfl) C1 hfan1 hsz13 hall_no0 hout_ne0 hcnt9 h9props hout_ne9 hhas10
      exact hx (hC1eval x)
    · obtain ⟨x, hx⟩ := h13b 2 (Or.inl rfl) C1 hfan1 hsz13 hall_no0 hout_ne0 hcnt9 h9props hout_ne9 hhas10
      exact hx (hC1eval x)
    · obtain ⟨x, hx⟩ := h13b 3 (Or.inr (Or.inl rfl)) C1 hfan1 hsz13 hall_no0 hout_ne0 hcnt9 h9props hout_ne9 hhas10
      exact hx (hC1eval x)
    · obtain ⟨x, hx⟩ := h13b 6 (Or.inr (Or.inr rfl)) C1 hfan1 hsz13 hall_no0 hout_ne0 hcnt9 h9props hout_ne9 hhas10
      exact hx (hC1eval x)
