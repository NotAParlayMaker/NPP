import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3166_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def r (j x2 w : ℕ) : ℕ :=
  if w < 9 then w else if w = 10 + j then x2 else if w < 10 + j then w - 1 else w - 2

def reGate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

theorem fold_pre (B : List Gate) :
    ∀ W : List Bool, ∃ T2 : List Bool, B.foldl stepW W = W ++ T2 := by
  induction B with
  | nil => intro W; exact ⟨[], by simp⟩
  | cons g B ih =>
    intro W
    obtain ⟨T2, h⟩ := ih (stepW W g)
    exact ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: T2, by rw [List.foldl_cons, h]; simp [stepW]⟩

theorem step_inv (f : ℕ → ℕ) (d L0 : ℕ) (Q : ℕ → Prop)
    (H : ∀ w, Q w → (f w < L0 ∧ w < L0 + d) ∨ (L0 ≤ f w ∧ w = f w + d))
    (W Y : List Bool) (g : Gate) (hl : Y.length = W.length + d) (h0 : L0 ≤ W.length)
    (hv : ∀ k, Q k → W.getD (f k) false = Y.getD k false) (hg : ∀ i ∈ g.inputs, Q i) :
    ∀ k, Q k → (stepW W (reGate f g)).getD (f k) false = (stepW Y g).getD k false := by
  intro k hk
  have hm : (g.inputs.map f).map (fun i => W.getD i false)
      = g.inputs.map (fun i => Y.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i hi => hv i (hg i hi))
  show (W ++ [g.op.eval ((g.inputs.map f).map fun i => W.getD i false)]).getD (f k) false
    = (Y ++ [g.op.eval (g.inputs.map fun i => Y.getD i false)]).getD k false
  rw [hm]
  generalize g.op.eval (g.inputs.map fun i => Y.getD i false) = v
  have hv2 := hv k hk
  simp only [List.getD_eq_getElem?_getD] at hv2 ⊢
  rcases H k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact hv2
  · by_cases h3 : f k < W.length
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact hv2
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      have h4 : k - Y.length = f k - W.length := by omega
      rw [h4]

theorem fold_inv (f : ℕ → ℕ) (d L0 : ℕ) (Q : ℕ → Prop)
    (H : ∀ w, Q w → (f w < L0 ∧ w < L0 + d) ∨ (L0 ≤ f w ∧ w = f w + d))
    (gs : List Gate) : (∀ g ∈ gs, ∀ i ∈ g.inputs, Q i) → ∀ (W Y : List Bool),
    Y.length = W.length + d → L0 ≤ W.length →
    (∀ k, Q k → W.getD (f k) false = Y.getD k false) →
    ∀ k, Q k → ((gs.map (reGate f)).foldl stepW W).getD (f k) false
      = (gs.foldl stepW Y).getD k false := by
  induction gs with
  | nil => intro _ W Y _ _ hv; exact hv
  | cons g gs ih =>
    intro hg W Y hl h0 hv
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    refine ih (fun g2 h2 => hg g2 (List.mem_cons_of_mem _ h2)) _ _ ?_ ?_
      (step_inv f d L0 Q H W Y g hl h0 hv (hg g List.mem_cons_self))
    · simp [stepW, hl]
      omega
    · simp [stepW]
      omega

theorem pre_get (x : Fin 9 → Bool) (T : List Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x ++ T).getD i false = x ⟨i, hi⟩ := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_ofFn]
  simp [hi]

theorem pre_get9 (x : Fin 9 → Bool) (a : Bool) (T : List Bool) :
    ((List.ofFn x ++ [a]) ++ T).getD 9 false = a := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp), List.getElem?_append_right (by simp)]
  simp

theorem absorb (g : Gate) (Y : List Bool) (x2 : ℕ) (c v : Bool) (hop : g.op = GateOp.or)
    (hin : g.inputs = [9, x2] ∨ g.inputs = [x2, 9]) (h9 : Y.getD 9 false = c)
    (h2 : Y.getD x2 false = v) (habs : (c || v) = v) :
    g.op.eval (g.inputs.map fun i => Y.getD i false) = v := by
  simp only [List.getD_eq_getElem?_getD] at h9 h2 ⊢
  rcases hin with h | h <;> simp [hop, GateOp.eval, h, h9, h2] <;>
    cases c <;> cases v <;> simp_all

end PEqualNP.Outside.L_meta_3166_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3166_aux in
theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) := by
  rintro ⟨gs, out⟩ x2 g hx2 hF hRB hout hfil hop hin
  have hmem : g ∈ gs := by
    have h1 : g ∈ List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) gs := by
      rw [hfil]
      simp
    exact (List.mem_filter.mp h1).1
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hmem
  have h9g : (9 : ℕ) ∈ g.inputs := by
    rcases hin with h | h <;> simp [h]
  replace hfil : List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) A ++
      g :: List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) B = [g] := by
    rw [List.filter_append, List.filter_cons_of_pos (by simpa using h9g)] at hfil
    exact hfil
  have hlen := congrArg List.length hfil
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  have hA9 : ∀ a ∈ A, (9 : ℕ) ∉ a.inputs := by
    have h1 : List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) A = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    simpa [List.filter_eq_nil_iff] using h1
  have hB9 : ∀ a ∈ B, (9 : ℕ) ∉ a.inputs := by
    have h1 : List.filter (fun (x8 : Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) B = [] :=
      List.eq_nil_of_length_eq_zero (by omega)
    simpa [List.filter_eq_nil_iff] using h1
  refine ⟨⟨A.map (reGate (r A.length x2)) ++ B.map (reGate (r A.length x2)),
    r A.length x2 out⟩, ?_, ?_, ?_⟩
  · intro g2 hg2
    simp only [List.mem_append, List.mem_map] at hg2
    rcases hg2 with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · have := hF a (by simp [ha])
      simpa [reGate] using this
    · have := hF a (by simp [ha])
      simpa [reGate] using this
  · simp [Circuit.size]
    omega
  · intro x
    have hAg : ∀ a ∈ A, ∀ i ∈ a.inputs, i ≠ 9 ∧ i < 10 + A.length := by
      intro a ha i hi
      refine ⟨fun h => hA9 a ha (h ▸ hi), ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
      have h1 := hRB k (by simp; omega) i (by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]
        exact hi)
      omega
    have hBg : ∀ a ∈ B, ∀ i ∈ a.inputs, i ≠ 9 := by
      intro a ha i hi h
      exact hB9 a ha (h ▸ hi)
    have HA : ∀ w, (w ≠ 9 ∧ w < 10 + A.length) →
        (r A.length x2 w < 9 ∧ w < 9 + 1) ∨ (9 ≤ r A.length x2 w ∧ w = r A.length x2 w + 1) := by
      intro w hw
      unfold r
      split_ifs <;> omega
    have HC : ∀ w, w ≠ 9 → (r A.length x2 w < 9 + A.length ∧ w < 9 + A.length + 2) ∨
        (9 + A.length ≤ r A.length x2 w ∧ w = r A.length x2 w + 2) := by
      intro w hw
      unfold r
      split_ifs <;> omega
    have hbase : ∀ k, (k ≠ 9 ∧ k < 10 + A.length) → (List.ofFn x).getD (r A.length x2 k) false
        = (List.ofFn x ++ [x 0 && x 2]).getD k false := by
      intro k hk
      simp only [List.getD_eq_getElem?_getD]
      by_cases h : k < 9
      · have h1 : r A.length x2 k = k := by simp [r, h]
        rw [h1, List.getElem?_append_left (by simp; omega)]
      · have h1 : r A.length x2 k = k - 1 := by
          unfold r
          split_ifs <;> omega
        rw [h1, List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hAinv := fold_inv (r A.length x2) 1 9 (fun w => w ≠ 9 ∧ w < 10 + A.length) HA A hAg
      (List.ofFn x) (List.ofFn x ++ [x 0 && x 2]) (by simp) (by simp) hbase
    have hWl := fold_len (A.map (reGate (r A.length x2))) (List.ofFn x)
    have hYl := fold_len A (List.ofFn x ++ [x 0 && x 2])
    obtain ⟨T1, hT1⟩ := fold_pre A (List.ofFn x ++ [x 0 && x 2])
    obtain ⟨T2, hT2⟩ := fold_pre (A.map (reGate (r A.length x2))) (List.ofFn x)
    simp only [List.length_map, List.length_ofFn, List.length_append, List.length_cons,
      List.length_nil] at hWl hYl
    have hY9 : (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])).getD 9 false = (x 0 && x 2) := by
      rw [hT1]
      exact pre_get9 x _ T1
    have hYi : ∀ (i : ℕ) (hi : i < 9),
        (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])).getD i false = x ⟨i, hi⟩ := by
      intro i hi
      rw [hT1, List.append_assoc]
      exact pre_get x _ i hi
    have hWi : ∀ (i : ℕ) (hi : i < 9),
        ((A.map (reGate (r A.length x2))).foldl stepW (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
      intro i hi
      rw [hT2]
      exact pre_get x _ i hi
    have hv : g.op.eval (g.inputs.map fun i =>
        (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])).getD i false)
        = ((A.map (reGate (r A.length x2))).foldl stepW (List.ofFn x)).getD x2 false := by
      have e0 := hYi 0 (by omega)
      have e2 := hYi 2 (by omega)
      have f0 := hWi 0 (by omega)
      have f2 := hWi 2 (by omega)
      have z0 : (⟨0, by omega⟩ : Fin 9) = 0 := rfl
      have z2 : (⟨2, by omega⟩ : Fin 9) = 2 := rfl
      rw [z0] at e0 f0
      rw [z2] at e2 f2
      rcases hx2 with rfl | rfl
      · exact absorb g _ 0 (x 0 && x 2) _ hop hin hY9 (by rw [e0, f0])
          (by rw [f0]; cases x 0 <;> cases x 2 <;> rfl)
      · exact absorb g _ 2 (x 0 && x 2) _ hop hin hY9 (by rw [e2, f2])
          (by rw [f2]; cases x 0 <;> cases x 2 <;> rfl)
    have hBinv : ∀ k, k ≠ 9 →
        ((A.map (reGate (r A.length x2))).foldl stepW (List.ofFn x)).getD (r A.length x2 k) false
        = (stepW (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])) g).getD k false := by
      intro k hk
      show _ = (A.foldl stepW (List.ofFn x ++ [x 0 && x 2]) ++ [g.op.eval (g.inputs.map fun i =>
        (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])).getD i false)]).getD k false
      by_cases h : k < 10 + A.length
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hAinv k ⟨hk, h⟩
      · by_cases h2 : k = 10 + A.length
        · have h1 : r A.length x2 k = x2 := by
            unfold r
            split_ifs <;> omega
          rw [h1, hv]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          have h3 : k - (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])).length = 0 := by omega
          rw [h3]
          simp
        · have h1 : r A.length x2 k = k - 2 := by
            unfold r
            split_ifs <;> omega
          rw [h1]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega)]
    have hC := fold_inv (r A.length x2) 2 (9 + A.length) (fun w => w ≠ 9) HC B hBg
      ((A.map (reGate (r A.length x2))).foldl stepW (List.ofFn x))
      (stepW (A.foldl stepW (List.ofFn x ++ [x 0 && x 2])) g)
      (by show (_ ++ [_]).length = _; rw [List.length_append, List.length_singleton]; omega) (by omega) hBinv out hout
    show ((A.map (reGate (r A.length x2)) ++ B.map (reGate (r A.length x2))).foldl stepW
        (List.ofFn x)).getD (r A.length x2 out) false
      = ((A ++ g :: B).foldl stepW (List.ofFn x ++ [x 0 && x 2])).getD out false
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    exact hC
