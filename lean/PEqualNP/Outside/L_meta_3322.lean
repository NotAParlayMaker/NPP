import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def mapWire (π : Equiv.Perm (Fin 14)) (k : ℕ) : ℕ :=
  if h : k < 14 then (π ⟨k, h⟩ : ℕ) else k

def mapGate (π : Equiv.Perm (Fin 14)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mapWire π)⟩

lemma getD_append_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_singleton_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

lemma getD_append_singleton_gt {α : Type*} (l : List α) (a d : α) (i : ℕ) (h : l.length < i) :
    (l ++ [a]).getD i d = d := by
  have hlen : (l ++ [a]).length ≤ i := by simp; omega
  simp [List.getD, List.getElem?_eq_none hlen]

lemma foldl_wires_map (π : Equiv.Perm (Fin 14)) (gs : List Gate) (w w' : List Bool)
    (hlen : w.length = w'.length) (h14 : 14 ≤ w.length)
    (hmatch : ∀ k, w.getD k false = w'.getD (mapWire π k) false) :
    let wf := gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
    let wf' := (gs.map (mapGate π)).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w'
    wf.length = wf'.length ∧ 14 ≤ wf.length ∧ ∀ k, wf.getD k false = wf'.getD (mapWire π k) false := by
  induction gs generalizing w w' with
  | nil => exact ⟨hlen, h14, hmatch⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hb : g.op.eval (g.inputs.map fun i => w.getD i false) =
        (mapGate π g).op.eval ((mapGate π g).inputs.map fun i => w'.getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def]
      congr 1
      exact List.map_congr_left fun i _ => hmatch i
    apply ih
    · simp [hlen]
    · simp; omega
    · intro k
      by_cases hk : k < w.length
      · have hmk : mapWire π k < w'.length := by
          unfold mapWire
          split_ifs with hk14
          · have : (π ⟨k, hk14⟩ : ℕ) < 14 := (π ⟨k, hk14⟩).isLt
            omega
          · omega
        rw [getD_append_lt w _ k false hk, getD_append_lt w' _ (mapWire π k) false hmk]
        exact hmatch k
      · have hkeq : w.length ≤ k := Nat.le_of_not_lt hk
        rcases Nat.eq_or_lt_of_le hkeq with rfl | hkgt
        · have hm : mapWire π w.length = w'.length := by
            unfold mapWire
            split_ifs with h'
            · exfalso; omega
            · exact hlen
          rw [hm, getD_append_singleton_eq, getD_append_singleton_eq, hb]
        · have hm : w'.length < mapWire π k := by
            unfold mapWire
            split_ifs with h'
            · exfalso; omega
            · omega
          rw [getD_append_singleton_gt w _ false k hkgt, getD_append_singleton_gt w' _ false (mapWire π k) hm]

lemma gateOp_comm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : Bool) :
    op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma perm_x9_comp (σ π : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (if (if i < (14 : Fin 15) then (π (Fin.ofNat 14 i) : ℕ) else 14) < 14 then
      (σ (Fin.ofNat 14 (if i < (14 : Fin 15) then (π (Fin.ofNat 14 i) : ℕ) else 14)) : ℕ)
    else 14) =
    if i < (14 : Fin 15) then ((σ * π) (Fin.ofNat 14 i) : ℕ) else 14 := by
  by_cases hi : i < (14 : Fin 15)
  · simp only [hi, ↓reduceIte]
    have hlt : (π (Fin.ofNat 14 i) : ℕ) < 14 := (π (Fin.ofNat 14 i)).isLt
    simp only [hlt, ↓reduceIte]
    have hof : Fin.ofNat 14 (π (Fin.ofNat 14 i) : ℕ) = π (Fin.ofNat 14 i) := by
      ext
      simp
    rw [hof]
    rfl
  · simp [hi]

lemma fin_min_max_nat {n : ℕ} (a b : Fin n) :
    ((min a b : Fin n) : ℕ) = min (a : ℕ) (b : ℕ) ∧ ((max a b : Fin n) : ℕ) = max (a : ℕ) (b : ℕ) := by
  by_cases h : a ≤ b
  · have h' : (a : ℕ) ≤ (b : ℕ) := h
    simp [min_eq_left h, max_eq_right h, min_eq_left h', max_eq_right h']
  · have h' : (b : ℕ) ≤ (a : ℕ) := le_of_not_ge h
    simp [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), min_eq_right h', max_eq_left h']

end PEqualNP.Outside.L_meta_3322

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro x1 x2 hAO hNodup h2 h26 hEval
  intro x8 x9
  rcases hAO with ⟨hAndOr, hReads, hLen2⟩
  have hgates : ∃ g0 g1 rest, x2.gates = g0 :: g1 :: rest := by
    match hg : x2.gates with
    | [] => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg] at h2
    | [_] => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg] at h2
    | g0 :: g1 :: rest => exact ⟨g0, g1, rest, rfl⟩
  rcases hgates with ⟨g0, g1, rest, hgates_eq⟩
  have hg0_len : g0.inputs.length = 2 := hLen2 g0 (by simp [hgates_eq])
  have hg1_len : g1.inputs.length = 2 := hLen2 g1 (by simp [hgates_eq])
  have hg0_nodup : g0.inputs.Nodup := hNodup g0 (by simp [hgates_eq])
  have hg1_nodup : g1.inputs.Nodup := hNodup g1 (by simp [hgates_eq])
  have hg0_op : g0.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g0.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    hAndOr g0 (by simp [hgates_eq])
  have hg1_op : g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    hAndOr g1 (by simp [hgates_eq])
  have hg0_rb : ∀ i ∈ g0.inputs, i < 14 := by
    have h0 := hReads 0 (by simp [hgates_eq])
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates_eq] using h0
  have hg1_rb : ∀ i ∈ g1.inputs, i < 15 := by
    have h1 := hReads 1 (by simp [hgates_eq])
    simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates_eq] using h1
  rcases List.length_eq_two.mp hg0_len with ⟨a0, b0, hg0_in⟩
  rcases List.length_eq_two.mp hg1_len with ⟨a1, b1, hg1_in⟩
  have ha0_lt : a0 < 14 := hg0_rb a0 (by simp [hg0_in])
  have hb0_lt : b0 < 14 := hg0_rb b0 (by simp [hg0_in])
  have ha1_lt : a1 < 15 := hg1_rb a1 (by simp [hg1_in])
  have hb1_lt : b1 < 15 := hg1_rb b1 (by simp [hg1_in])
  have hab0 : a0 ≠ b0 := by simpa [hg0_in] using hg0_nodup
  have hab1 : a1 ≠ b1 := by simpa [hg1_in] using hg1_nodup
  let fa0 : Fin 14 := ⟨a0, ha0_lt⟩
  let fb0 : Fin 14 := ⟨b0, hb0_lt⟩
  let fa1 : Fin 15 := ⟨a1, ha1_lt⟩
  let fb1 : Fin 15 := ⟨b1, hb1_lt⟩
  have hfab0 : fa0 ≠ fb0 := fun h => hab0 (congrArg Fin.val h)
  have hfab1 : fa1 ≠ fb1 := fun h => hab1 (congrArg Fin.val h)
  let S : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter fun π => ∀ x : Fin 14 → Bool, x1 (x ∘ ⇑π) = x1 x
  have hS_nonempty : S.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => rfl⟩⟩
  let score : Equiv.Perm (Fin 14) → ℕ :=
    fun π => x8 (π fa0 : ℕ) (π fb0 : ℕ) (x9 π fa1) (x9 π fb1)
  obtain ⟨π₀, hπ₀_mem, hπ₀_min⟩ := S.exists_min_image score hS_nonempty
  have hπ₀_sym : ∀ x : Fin 14 → Bool, x1 (x ∘ ⇑π₀) = x1 x := (Finset.mem_filter.mp hπ₀_mem).2
  let u0 : Fin 14 := π₀ fa0
  let v0 : Fin 14 := π₀ fb0
  have huv0 : u0 ≠ v0 := fun h => hfab0 (π₀.injective h)
  let u1 : Fin 15 := ⟨x9 π₀ fa1, by
    dsimp [x9]
    split_ifs
    · exact Nat.lt_succ_of_lt (π₀ _).isLt
    · omega⟩
  let v1 : Fin 15 := ⟨x9 π₀ fb1, by
    dsimp [x9]
    split_ifs
    · exact Nat.lt_succ_of_lt (π₀ _).isLt
    · omega⟩
  have huv1 : u1 ≠ v1 := by
    intro h
    have hval : x9 π₀ fa1 = x9 π₀ fb1 := congrArg Fin.val h
    dsimp [x9] at hval
    by_cases hfa : (fa1 : ℕ) < 14 <;> by_cases hfb : (fb1 : ℕ) < 14
    · have hfa' : fa1 < (14 : Fin 15) := hfa
      have hfb' : fb1 < (14 : Fin 15) := hfb
      simp only [hfa', hfb', ↓reduceIte] at hval
      have hinj : Fin.ofNat 14 (fa1 : ℕ) = Fin.ofNat 14 (fb1 : ℕ) :=
        π₀.injective (Fin.ext hval)
      apply hfab1
      ext
      simpa [Fin.ofNat, Nat.mod_eq_of_lt hfa, Nat.mod_eq_of_lt hfb] using congrArg Fin.val hinj
    · have hfa' : fa1 < (14 : Fin 15) := hfa
      have hfb' : ¬ fb1 < (14 : Fin 15) := hfb
      simp only [hfa', hfb', ↓reduceIte] at hval
      have hlt : (π₀ (Fin.ofNat 14 (fa1 : ℕ)) : ℕ) < 14 := (π₀ _).isLt
      omega
    · have hfa' : ¬ fa1 < (14 : Fin 15) := hfa
      have hfb' : fb1 < (14 : Fin 15) := hfb
      simp only [hfa', hfb', ↓reduceIte] at hval
      have hlt : (π₀ (Fin.ofNat 14 (fb1 : ℕ)) : ℕ) < 14 := (π₀ _).isLt
      omega
    · apply hfab1
      have h1 := fa1.isLt
      have h2 := fb1.isLt
      ext; omega
  let x10 := min u0 v0
  let x11 := max u0 v0
  let x12 := min u1 v1
  let x13 := max u1 v1
  let x16 : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨rest.map (PEqualNP.Outside.L_meta_3322.mapGate π₀), PEqualNP.Outside.L_meta_3322.mapWire π₀ x2.output⟩
  refine ⟨x10, x11, x12, x13, g0.op, g1.op, x16, ?_, ?_, hg0_op, hg1_op, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne min_le_max (by
      by_cases h : u0 ≤ v0
      · simp [x10, x11, min_eq_left h, max_eq_right h, huv0]
      · simp [x10, x11, min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), huv0.symm])
  · exact lt_of_le_of_ne min_le_max (by
      by_cases h : u1 ≤ v1
      · simp [x12, x13, min_eq_left h, max_eq_right h, huv1]
      · simp [x12, x13, min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), huv1.symm])
  · intro σ hσ
    have hcomp : σ * π₀ ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => ?_⟩
      have h1 : x1 (fun i => x (σ (π₀ i))) = x1 (x ∘ ⇑σ) := hπ₀_sym (x ∘ ⇑σ)
      change x1 (fun i => x (σ (π₀ i))) = x1 x
      rw [h1, hσ x]
    have hmin := hπ₀_min (σ * π₀) hcomp
    have hL : x8 (x10 : ℕ) (x11 : ℕ) (x12 : ℕ) (x13 : ℕ) = score π₀ := by
      dsimp [x8, score, x10, x11, x12, x13]
      simp only [min_eq_left (min_le_max (a := (u0 : ℕ)) (b := (v0 : ℕ))),
        max_eq_right (min_le_max (a := (u0 : ℕ)) (b := (v0 : ℕ))),
        min_eq_left (min_le_max (a := (u1 : ℕ)) (b := (v1 : ℕ))),
        max_eq_right (min_le_max (a := (u1 : ℕ)) (b := (v1 : ℕ)))]
      rfl
    have hR : x8 (σ x10 : ℕ) (σ x11 : ℕ) (x9 σ x12) (x9 σ x13) = score (σ * π₀) := by
      dsimp [x8, score]
      have hpair0 : min (σ x10 : ℕ) (σ x11 : ℕ) = min ((σ * π₀) fa0 : ℕ) ((σ * π₀) fb0 : ℕ) ∧
          max (σ x10 : ℕ) (σ x11 : ℕ) = max ((σ * π₀) fa0 : ℕ) ((σ * π₀) fb0 : ℕ) := by
        by_cases h0 : u0 ≤ v0
        · simp only [x10, x11, min_eq_left h0, max_eq_right h0]; exact ⟨rfl, rfl⟩
        · simp only [x10, x11, min_eq_right (le_of_not_ge h0), max_eq_left (le_of_not_ge h0)]
          rw [Nat.min_comm (σ v0 : ℕ), Nat.max_comm (σ v0 : ℕ)]
          exact ⟨rfl, rfl⟩
      have hpair1 : min (x9 σ x12) (x9 σ x13) = min (x9 (σ * π₀) fa1) (x9 (σ * π₀) fb1) ∧
          max (x9 σ x12) (x9 σ x13) = max (x9 (σ * π₀) fa1) (x9 (σ * π₀) fb1) := by
        have hx1 : x9 σ u1 = x9 (σ * π₀) fa1 := PEqualNP.Outside.L_meta_3322.perm_x9_comp σ π₀ fa1
        have hy1 : x9 σ v1 = x9 (σ * π₀) fb1 := PEqualNP.Outside.L_meta_3322.perm_x9_comp σ π₀ fb1
        by_cases h1 : u1 ≤ v1
        · simp only [x12, x13, min_eq_left h1, max_eq_right h1, hx1, hy1, and_self]
        · simp only [x12, x13, min_eq_right (le_of_not_ge h1), max_eq_left (le_of_not_ge h1), hx1, hy1]
          rw [Nat.min_comm (x9 (σ * π₀) fa1), Nat.max_comm (x9 (σ * π₀) fa1)]
          exact ⟨rfl, rfl⟩
      rw [hpair0.1, hpair0.2, hpair1.1, hpair1.2]
      rfl
    omega
  · intro g hg
    simp only [x16, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩
    have hg'_mem : g' ∈ x2.gates := by simp [hgates_eq, hg']
    refine ⟨?_, ?_⟩
    · rcases hAndOr g' hg'_mem with h | h <;> simp [PEqualNP.Outside.L_meta_3322.mapGate, h]
    · simp [PEqualNP.Outside.L_meta_3322.mapGate, hLen2 g' hg'_mem]
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, x16, List.length_map]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size, hgates_eq, List.length_cons] at h26
    omega
  · intro x17
    dsimp only
    have hev := hEval (x17 ∘ ⇑π₀)
    rw [hπ₀_sym x17] at hev
    rw [← hev]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      hgates_eq, List.foldl_cons]
    have hg0_val : g0.op.eval (g0.inputs.map fun i => (List.ofFn (x17 ∘ ⇑π₀)).getD i false) =
        g0.op.eval [x17 x10, x17 x11] := by
      rw [hg0_in]
      simp only [List.map_cons, List.map_nil, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn]
      simp only [ha0_lt, hb0_lt, ↓reduceDIte, Option.getD_some, Function.comp_apply]
      change g0.op.eval [x17 u0, x17 v0] = g0.op.eval [x17 x10, x17 x11]
      by_cases h0 : u0 ≤ v0
      · simp [x10, x11, min_eq_left h0, max_eq_right h0]
      · simp [x10, x11, min_eq_right (le_of_not_ge h0), max_eq_left (le_of_not_ge h0)]
        exact PEqualNP.Outside.L_meta_3322.gateOp_comm g0.op hg0_op (x17 u0) (x17 v0)
    rw [hg0_val]
    set g0v := g0.op.eval [x17 x10, x17 x11]
    set w0 := List.ofFn (x17 ∘ ⇑π₀) ++ [g0v]
    set x18 := List.ofFn x17 ++ [g0v]
    have hw0_match : ∀ (k : ℕ) (hk : k < 15), w0.getD k false = x18.getD (x9 π₀ ⟨k, hk⟩) false := by
      intro k hk
      by_cases hk14 : k < 14
      · have hlt_w0 : k < (List.ofFn (x17 ∘ ⇑π₀)).length := by simp [hk14]
        have hlt_x18 : (π₀ (Fin.ofNat 14 k) : ℕ) < (List.ofFn x17).length := by
          simp [(π₀ _).isLt]
        have hx9 : x9 π₀ ⟨k, hk⟩ = (π₀ (Fin.ofNat 14 k) : ℕ) := by
          dsimp [x9]; simp [show (⟨k, hk⟩ : Fin 15) < 14 from hk14]
        rw [hx9, PEqualNP.Outside.L_meta_3322.getD_append_lt _ _ k false hlt_w0,
          PEqualNP.Outside.L_meta_3322.getD_append_lt _ _ _ false hlt_x18]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn]
        simp only [hk14, (π₀ _).isLt, ↓reduceDIte, Option.getD_some, Function.comp_apply]
        congr 1; ext; simp [Fin.ofNat, Nat.mod_eq_of_lt hk14]
      · have hkeq : k = 14 := by omega
        subst hkeq
        have hx9 : x9 π₀ ⟨14, hk⟩ = 14 := rfl
        rw [hx9]
        have hlen1 : (List.ofFn (x17 ∘ ⇑π₀)).length = 14 := by simp
        have hlen2 : (List.ofFn x17).length = 14 := by simp
        rw [← hlen1, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq,
          hlen1, ← hlen2, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq]
    have hg1_val : g1.op.eval (g1.inputs.map fun i => w0.getD i false) =
        g1.op.eval [x18.getD (x12 : ℕ) false, x18.getD (x13 : ℕ) false] := by
      rw [hg1_in]
      simp only [List.map_cons, List.map_nil]
      rw [hw0_match a1 ha1_lt, hw0_match b1 hb1_lt]
      change g1.op.eval [x18.getD (u1 : ℕ) false, x18.getD (v1 : ℕ) false] =
        g1.op.eval [x18.getD (x12 : ℕ) false, x18.getD (x13 : ℕ) false]
      by_cases h1 : u1 ≤ v1
      · simp [x12, x13, min_eq_left h1, max_eq_right h1]
      · simp [x12, x13, min_eq_right (le_of_not_ge h1), max_eq_left (le_of_not_ge h1)]
        exact PEqualNP.Outside.L_meta_3322.gateOp_comm g1.op hg1_op _ _
    rw [hg1_val]
    set g1v := g1.op.eval [x18.getD (x12 : ℕ) false, x18.getD (x13 : ℕ) false]
    have hfold := PEqualNP.Outside.L_meta_3322.foldl_wires_map π₀ rest (w0 ++ [g1v]) (x18 ++ [g1v])
      (by simp [w0, x18]) (by simp [w0]) (by
        intro k
        by_cases hk : k < 14
        · have hm : PEqualNP.Outside.L_meta_3322.mapWire π₀ k = (π₀ ⟨k, hk⟩ : ℕ) := by
            simp [PEqualNP.Outside.L_meta_3322.mapWire, hk]
          rw [hm]
          have h1 : k < w0.length := by simp [w0]; omega
          have h2 : (π₀ ⟨k, hk⟩ : ℕ) < x18.length := by simp [x18]; exact Nat.lt_succ_of_lt (π₀ _).isLt
          rw [PEqualNP.Outside.L_meta_3322.getD_append_lt w0 _ k false h1,
            PEqualNP.Outside.L_meta_3322.getD_append_lt x18 _ _ false h2]
          have h1' : k < (List.ofFn (x17 ∘ ⇑π₀)).length := by simp [hk]
          have h2' : (π₀ ⟨k, hk⟩ : ℕ) < (List.ofFn x17).length := by simp [(π₀ _).isLt]
          rw [PEqualNP.Outside.L_meta_3322.getD_append_lt _ _ k false h1',
            PEqualNP.Outside.L_meta_3322.getD_append_lt _ _ _ false h2']
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn, List.getElem?_ofFn]
          simp only [hk, (π₀ _).isLt, ↓reduceDIte, Option.getD_some, Function.comp_apply]
        · have hm : PEqualNP.Outside.L_meta_3322.mapWire π₀ k = k := by
            simp [PEqualNP.Outside.L_meta_3322.mapWire, hk]
          rw [hm]
          rcases Nat.lt_trichotomy k 15 with hk15 | rfl | hk15
          · have hkeq : k = 14 := by omega
            subst hkeq
            have h1 : 14 < w0.length := by simp [w0]
            have h2 : 14 < x18.length := by simp [x18]
            rw [PEqualNP.Outside.L_meta_3322.getD_append_lt w0 _ 14 false h1,
              PEqualNP.Outside.L_meta_3322.getD_append_lt x18 _ 14 false h2]
            have hlen1 : (List.ofFn (x17 ∘ ⇑π₀)).length = 14 := by simp
            have hlen2 : (List.ofFn x17).length = 14 := by simp
            rw [← hlen1, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq,
              hlen1, ← hlen2, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq]
          · have hlen1 : w0.length = 15 := by simp [w0]
            have hlen2 : x18.length = 15 := by simp [x18]
            rw [← hlen1, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq,
              hlen1, ← hlen2, PEqualNP.Outside.L_meta_3322.getD_append_singleton_eq]
          · have hlen1 : w0.length < k := by simp [w0]; exact hk15
            have hlen2 : x18.length < k := by simp [x18]; exact hk15
            rw [PEqualNP.Outside.L_meta_3322.getD_append_singleton_gt w0 _ false k hlen1,
              PEqualNP.Outside.L_meta_3322.getD_append_singleton_gt x18 _ false k hlen2])
    exact (hfold.2.2 x2.output).symm
