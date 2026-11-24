import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3630_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (x1 : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map x1⟩

def rho (a b m k : ℕ) : ℕ := if k < 9 then k else if k = 9 then a else if k = 10 then b else k + m

lemma rho_lt (a b m k : ℕ) (ha : a < 11 + m) (hb : b < 11 + m) (hk : k < 11) : rho a b m k < 11 + m := by
  unfold rho
  split_ifs <;> omega

lemma rho_ge (a b m k : ℕ) (hk : 11 ≤ k) : rho a b m k = k + m := by
  unfold rho
  split_ifs <;> omega

lemma step_inv (a b m : ℕ) (ha : a < 11 + m) (hb : b < 11 + m) (W Y : List Bool) (g : Gate)
    (hl : W.length = Y.length + m) (hn : 11 ≤ Y.length)
    (hv : ∀ k, W.getD (rho a b m k) false = Y.getD k false) :
    ∀ k, (stepW W (reGate (rho a b m) g)).getD (rho a b m k) false = (stepW Y g).getD k false := by
  intro k
  have hm : (g.inputs.map (rho a b m)).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => hv i)
  show (W ++ [g.op.eval ((g.inputs.map (rho a b m)).map fun i => W.getD i false)]).getD (rho a b m k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  by_cases hk : k < Y.length
  · have hs : rho a b m k < W.length := by
      by_cases h11 : k < 11
      · have := rho_lt a b m k ha hb h11
        omega
      · rw [rho_ge a b m k (by omega)]
        omega
    rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hk, hv k]
  · have hs : rho a b m k = k + m := rho_ge a b m k (by omega)
    rw [hs, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    congr 1
    omega

lemma fold_inv (a b m : ℕ) (ha : a < 11 + m) (hb : b < 11 + m) (gs : List Gate) :
    ∀ (W Y : List Bool), W.length = Y.length + m → 11 ≤ Y.length →
    (∀ k, W.getD (rho a b m k) false = Y.getD k false) →
    ∀ k, ((gs.map (reGate (rho a b m))).foldl stepW W).getD (rho a b m k) false = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro W Y hl hn hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ (step_inv a b m ha hb W Y g hl hn hv)
    · simp [stepW, hl]; omega
    · simp [stepW]; omega

lemma gv (x6 : Fin 9 → Bool) (L : List Bool) (i : Fin 9) : (List.ofFn x6 ++ L).getD i.val false = x6 i := by
  fin_cases i <;> simp

lemma gr (x6 : Fin 9 → Bool) (L : List Bool) (j : ℕ) : (List.ofFn x6 ++ L).getD (9 + j) false = L.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma fin (x1 : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo x1) (d : (Fin 9 → Bool) → Bool)
    (G0 : List Gate) (hG : ∀ g ∈ G0, g.op = GateOp.or ∧ g.inputs.length ≤ 2) (a b m : ℕ)
    (ha : a < 11 + m) (hb : b < 11 + m)
    (hbase : ∀ x6 : Fin 9 → Bool, ∃ T : List Bool, G0.foldl stepW (List.ofFn x6 ++ [false]) = List.ofFn x6 ++ T ∧
      T.length = 2 + m ∧ (List.ofFn x6 ++ T).getD a false = (x6 0 || x6 4) ∧
      (List.ofFn x6 ++ T).getD b false = d x6) :
    ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size + G0.length ∧
      ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false]) = x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, d x6]) := by
  refine ⟨⟨G0 ++ x1.gates.map (reGate (rho a b m)), rho a b m x1.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨h1, h2⟩ := hG g h
      exact ⟨by rw [h1]; simp, h2⟩
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      have := hC g0 hg0
      simpa [reGate] using this
  · simp [Circuit.size]; omega
  · intro x6
    obtain ⟨T, hT, hTl, hTa, hTb⟩ := hbase x6
    show ((G0 ++ x1.gates.map (reGate (rho a b m))).foldl stepW (List.ofFn x6 ++ [false])).getD (rho a b m x1.output) false
      = (x1.gates.foldl stepW (List.ofFn x6 ++ [x6 0 || x6 4, d x6])).getD x1.output false
    rw [List.foldl_append, hT]
    refine fold_inv a b m ha hb x1.gates _ _ (by simp [hTl]; omega) (by simp) ?_ x1.output
    intro k
    by_cases h9 : k < 9
    · have hr : rho a b m k = k := by unfold rho; rw [if_pos h9]
      rw [hr]
      have e1 := gv x6 T ⟨k, h9⟩
      have e2 := gv x6 [x6 0 || x6 4, d x6] ⟨k, h9⟩
      simp only at e1 e2
      rw [e1, e2]
    · by_cases h9e : k = 9
      · have hr : rho a b m k = a := by unfold rho; rw [if_neg h9, if_pos h9e]
        rw [hr, hTa, h9e]
        have := gr x6 [x6 0 || x6 4, d x6] 0
        simpa using this.symm
      · by_cases h10 : k = 10
        · have hr : rho a b m k = b := by unfold rho; rw [if_neg h9, if_neg h9e, if_pos h10]
          rw [hr, hTb, h10]
          have := gr x6 [x6 0 || x6 4, d x6] 1
          simpa using this.symm
        · rw [rho_ge a b m k (by omega), List.getD_eq_default _ _ (by simp [hTl]; omega),
            List.getD_eq_default _ _ (by simp; omega)]

lemma g0 (x6 : Fin 9 → Bool) (L : List Bool) : (List.ofFn x6 ++ L).getD 0 false = x6 0 := gv x6 L 0

lemma g4 (x6 : Fin 9 → Bool) (L : List Bool) : (List.ofFn x6 ++ L).getD 4 false = x6 4 := gv x6 L 4

lemma g9 (x6 : Fin 9 → Bool) (L : List Bool) : (List.ofFn x6 ++ L).getD 9 false = L.getD 0 false := gr x6 L 0

lemma g10 (x6 : Fin 9 → Bool) (L : List Bool) : (List.ofFn x6 ++ L).getD 10 false = L.getD 1 false := gr x6 L 1

lemma g11 (x6 : Fin 9 → Bool) (L : List Bool) : (List.ofFn x6 ++ L).getD 11 false = L.getD 2 false := gr x6 L 2

end PEqualNP.Outside.L_meta_3630_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3630_aux in
theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) := by
  intro x1 x2 hC hcard
  have key : ∀ (G0 : List Gate) (a b m : ℕ), (∀ g ∈ G0, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
      a < 11 + m → b < 11 + m →
      (G0.length ≤ if x2.card ≤ 1 ∨ x2 = {(0 : Fin 9), (4 : Fin 9)} then 1 else 2) →
      (∀ x6 : Fin 9 → Bool, ∃ T : List Bool, G0.foldl stepW (List.ofFn x6 ++ [false]) = List.ofFn x6 ++ T ∧
        T.length = 2 + m ∧ (List.ofFn x6 ++ T).getD a false = (x6 0 || x6 4) ∧
        (List.ofFn x6 ++ T).getD b false = decide (∃ x7 ∈ x2, x6 x7 = true)) →
      ∃ (x5 : Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ 1 ∨ x2 = {(0 : Fin 9), (4 : Fin 9)} then 1 else 2) ∧ ∀ (x6 : Fin 9 → Bool), x5.eval (List.ofFn x6 ++ [false]) = x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, decide (∃ x7 ∈ x2, x6 x7 = true)]) := by
    intro G0 a b m hG ha hb hlen hbase
    obtain ⟨x5, h1, h2, h3⟩ := fin x1 hC (fun x6 => decide (∃ x7 ∈ x2, x6 x7 = true)) G0 hG a b m ha hb hbase
    exact ⟨x5, h1, by omega, h3⟩
  by_cases h04 : x2 = {(0 : Fin 9), (4 : Fin 9)}
  · refine key [⟨GateOp.or, [0, 4]⟩] 10 10 0 (by simp) (by omega) (by omega) (by simp [h04]) ?_
    intro x6
    refine ⟨[false, x6 0 || x6 4], ?_, rfl, ?_, ?_⟩
    · simp [stepW, GateOp.eval, g0, g4]
    · simp [g10]
    · simp [g10, h04]
  · rcases Nat.lt_or_ge x2.card 2 with hc | hc
    · rcases Nat.eq_zero_or_pos x2.card with hz | hp
      · have he : x2 = ∅ := Finset.card_eq_zero.mp hz
        refine key [⟨GateOp.or, [0, 4]⟩] 10 9 0 (by simp) (by omega) (by omega) (by simp [he]) ?_
        intro x6
        refine ⟨[false, x6 0 || x6 4], ?_, rfl, ?_, ?_⟩
        · simp [stepW, GateOp.eval, g0, g4]
        · simp [g10]
        · simp [g9, he]
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : x2.card = 1)
        refine key [⟨GateOp.or, [0, 4]⟩] 10 i.val 0 (by simp) (by omega) (by omega) (by simp [hi]) ?_
        intro x6
        refine ⟨[false, x6 0 || x6 4], ?_, rfl, ?_, ?_⟩
        · simp [stepW, GateOp.eval, g0, g4]
        · simp [g10]
        · rw [gv]; simp [hi]
    · obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp (by omega : x2.card = 2)
      refine key [⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [i.val, j.val]⟩] 10 11 1 (by simp) (by omega) (by omega) (by rw [if_neg (by rintro (h | h); exact absurd h (by omega); exact h04 h)]; simp) ?_
      intro x6
      refine ⟨[false, x6 0 || x6 4, x6 i || x6 j], ?_, rfl, ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [stepW, GateOp.eval]
      · simp [g10]
      · simp [g11, he]
