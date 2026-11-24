import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3861_1
  (eight : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
  (seven : ¬ HasCircuitSize 7 (fun x : Fin 7 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 5) || (x 4 && x 6) || (x 6 && x 3)) 10)
  (erase :
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hits := fun (frozen : ℕ → Bool) (g : Gate) => (reads g).any frozen
    let rows := fun {n : ℕ} (entries : List (Bool ⊕ ℕ)) (z : Fin n → Bool) =>
      entries.map (Sum.elim id (fun i => (List.ofFn z).getD i false))
    ∀ (n : ℕ) (entries : List (Bool ⊕ ℕ)) (frozen : ℕ → Bool) (C : Circuit), FanInTwo C →
      (∀ i, frozen i = true → i < entries.length ∧ ∃ b : Bool, entries.getD i (.inl false) = .inl b) →
      (∃ z : Fin n → Bool, C.eval (rows entries z) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (hits frozen) ≤ C.size ∧
        ∀ z : Fin n → Bool, D.eval (List.ofFn z) = C.eval (rows entries z))
  (core :
    let F := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let hits := fun (frozen : ℕ → Bool) (g : Gate) => (reads g).any frozen
    let freeze0 := fun i : ℕ => decide (i = 0 ∨ i = 9)
    let freeze4 := fun (r i : ℕ) => decide (i = 0 ∨ i = 4 ∨ i = 9 ∨ (r = 4 ∧ i = 10))
    ∀ (r : Fin 9), r = 1 ∨ r = 4 → ∀ C : Circuit, FanInTwo C → C.size = 13 →
      C.gates.countP (hits freeze0) = 1 → C.gates.countP (hits (freeze4 r.val)) = 2 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x r]) ≠ F x) :
  ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (1 : ℕ)] ∨ x1 = [(0 : ℕ), (4 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro simple hs C fan size
  let F := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)
  let H := fun x : Fin 8 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)
  let T := fun x : Fin 7 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
      (x 3 && x 5) || (x 4 && x 6) || (x 6 && x 3)
  let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let hits := fun (frozen : ℕ → Bool) (g : Gate) => (reads g).any frozen
  let freeze0 := fun i : ℕ => decide (i = 0 ∨ i = 9)
  let freeze4 := fun (r i : ℕ) => decide (i = 0 ∨ i = 4 ∨ i = 9 ∨ (r = 4 ∧ i = 10))
  let rows := fun {n : ℕ} (entries : List (Bool ⊕ ℕ)) (z : Fin n → Bool) =>
      entries.map (Sum.elim id (fun i => (List.ofFn z).getD i false))
  let input := fun (r : Fin 9) (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0, x 0 || x r]
  let entry0 := fun r : ℕ =>
    ([.inl false,.inr 0,.inr 1,.inr 2,.inr 6,.inr 7,.inr 4,.inr 5,.inr 3,.inl true,
      .inr (if r = 4 then 6 else 0)] : List (Bool ⊕ ℕ))
  let entry4 := fun r : ℕ =>
    ([.inl false,.inr 0,.inr 1,.inr 2,.inl false,.inr 3,.inr 4,.inr 5,.inr 6,.inl true,
      if r = 4 then .inl false else .inr 0] : List (Bool ⊕ ℕ))
  let complete0 := fun x : Fin 8 → Bool =>
    (![false,x 0,x 1,x 2,x 6,x 7,x 4,x 5,x 3] : Fin 9 → Bool)
  let complete4 := fun x : Fin 7 → Bool =>
    (![false,x 0,x 1,x 2,false,x 3,x 4,x 5,x 6] : Fin 9 → Bool)
  have map0 : ∀ x, F (complete0 x) = H x := by
    dsimp only [F, H, complete0]
    decide +kernel
  have map4 : ∀ x, F (complete4 x) = T x := by
    dsimp only [F, T, complete4]
    decide +kernel
  have args0 (r : Fin 9) (hr : r = 1 ∨ r = 4) (x : Fin 8 → Bool) :
      input r (complete0 x) = rows (entry0 r.val) x := by
    rcases hr with rfl | rfl <;> rfl
  have args4 (r : Fin 9) (hr : r = 1 ∨ r = 4) (x : Fin 7 → Bool) :
      input r (complete4 x) = rows (entry4 r.val) x := by
    rcases hr with rfl | rfl <;> rfl
  have const0 (r i : ℕ) (h : freeze0 i = true) : i < (entry0 r).length ∧
      ∃ b : Bool, (entry0 r).getD i (.inl false) = .inl b := by
    change decide (i = 0 ∨ i = 9) = true at h
    rcases of_decide_eq_true h with rfl | rfl
    · exact ⟨by simp [entry0], false, rfl⟩
    · exact ⟨by simp [entry0], true, rfl⟩
  have const4 (r i : ℕ) (h : freeze4 r i = true) : i < (entry4 r).length ∧
      ∃ b : Bool, (entry4 r).getD i (.inl false) = .inl b := by
    change decide (i = 0 ∨ i = 4 ∨ i = 9 ∨ (r = 4 ∧ i = 10)) = true at h
    rcases of_decide_eq_true h with rfl | rfl | rfl | ⟨rfl, rfl⟩
    · exact ⟨by simp [entry4], false, rfl⟩
    · exact ⟨by simp [entry4], false, rfl⟩
    · exact ⟨by simp [entry4], true, rfl⟩
    · exact ⟨by simp [entry4], false, rfl⟩
  have lower (n bound : ℕ) (entries : List (Bool ⊕ ℕ)) (frozen : ℕ → Bool)
      (G : (Fin n → Bool) → Bool) (forbidden : ¬ HasCircuitSize n G bound)
      (fixed : ∀ i, frozen i = true → i < entries.length ∧
        ∃ b : Bool, entries.getD i (.inl false) = .inl b)
      (computes : ∀ x, C.eval (rows entries x) = G x)
      (hasFalse : ∃ x, G x = false) :
      (bound + 1) + C.gates.countP (hits frozen) ≤ C.size := by
    obtain ⟨x, hx⟩ := hasFalse
    have zero : ∃ x, C.eval (rows entries x) = false := ⟨x, (computes x).trans hx⟩
    obtain ⟨D, hf, count, same⟩ := erase n entries frozen C fan fixed zero
    change D.size + C.gates.countP (hits frozen) ≤ C.size at count
    have enough : bound + 1 ≤ D.size := by
      by_contra sh
      exact forbidden ⟨D, hf, by omega, fun x => (same x).trans (computes x)⟩
    omega
  have boolAnd (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have boolOr (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have boolNot (l : List Bool) : GateOp.eval .not l = !(l.headD false) := rfl

  let signedHits (r : ℕ) (g : Gate) : Bool :=
    (reads g).any (fun i => decide (i = 0 ∨ i = 4 ∨ i = 9 ∨ (r = 4 ∧ i = 10)))

  let inputs (r : Fin 9) (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [!x 0, x 0 || x r]

  let gateValue (w : List Bool) (g : Gate) : Bool :=
    g.op.eval (g.inputs.map fun i => w.getD i false)

  have gate_kind {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates) :
      g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

  have gateValue_congr {C : Circuit} (hC : FanInTwo C) {g : Gate}
      (hg : g ∈ C.gates) (w v : List Bool)
      (h : ∀ i ∈ reads g, w.getD i false = v.getD i false) :
      gateValue w g = gateValue v g := by
    have value (u : List Bool) :
        gateValue u g = g.op.eval ((reads g).map fun i => u.getD i false) := by
      rcases gate_kind hC hg with hop | hop | hop
      · simp [gateValue, reads, hop, boolAnd]
      · simp [gateValue, reads, hop, boolOr]
      · dsimp only [gateValue, reads]
        rw [hop]
        cases g.inputs <;> rfl
    rw [value w, value v, List.map_congr_left h]

  -- Equal appended values produce a common suffix of computed wires.
  have common_suffix (gs : List Gate) (w v : List Bool)
      (h : ∀ g ∈ gs, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) (s : List Bool) :
      ∃ t, gs.foldl (fun u g => u ++ [gateValue u g]) (w ++ s) = w ++ t ∧
        gs.foldl (fun u g => u ++ [gateValue u g]) (v ++ s) = v ++ t := by
    induction gs generalizing s with
    | nil => exact ⟨s, rfl, rfl⟩
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons, h g (by simp) s, List.append_assoc, List.append_assoc]
      exact ih (fun a ha => h a (by simp [ha])) _

  have append_agree {w v : List Bool} (hlen : w.length = v.length) (s : List Bool)
      (i : ℕ) (hi : w.getD i false = v.getD i false) :
      (w ++ s).getD i false = (v ++ s).getD i false := by
    by_cases hw : i < w.length
    · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega), hi]
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

  have eval_eq_of_steps (C : Circuit) (w v : List Bool)
      (hlen : w.length = v.length) (hout : w.getD C.output false = v.getD C.output false)
      (h : ∀ g ∈ C.gates, ∀ s, gateValue (w ++ s) g = gateValue (v ++ s) g) :
      C.eval w = C.eval v := by
    obtain ⟨t, hw, hv⟩ := common_suffix C.gates w v h []
    simp only [List.append_nil] at hw hv
    change C.wires w = w ++ t at hw
    change C.wires v = v ++ t at hv
    change (C.wires w).getD C.output false = (C.wires v).getD C.output false
    rw [hw, hv]
    exact append_agree hlen t _ hout

  have eval_raw (C : Circuit) (w : List Bool) (hout : C.output < w.length) :
      C.eval w = w.getD C.output false := by
    obtain ⟨t, hw, _⟩ := common_suffix C.gates w w (fun _ _ _ => rfl) []
    simp only [List.append_nil] at hw
    change C.wires w = w ++ t at hw
    change (C.wires w).getD C.output false = w.getD C.output false
    rw [hw, List.getD_append _ _ _ _ hout]

  have input_read (r : Fin 9) (x : Fin 9 → Bool) (s : List Bool) (i : ℕ) :
      (inputs r x ++ s).getD i false =
        if h : i < 9 then x ⟨i, h⟩
        else if i = 9 then !x 0
        else if i = 10 then x 0 || x r
        else s.getD (i - 11) false := by
    dsimp only [inputs]
    by_cases hi : i < 9
    · rw [dite_eq_left hi, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dite_eq_left hi]
      rfl
    · rw [dite_eq_right hi]
      by_cases h9 : i = 9
      · subst i
        rw [ite_eq_left rfl, List.getD_append _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ (by simp)]
        rfl
      by_cases h10 : i = 10
      · subst i
        rw [ite_eq_right h9, ite_eq_left rfl, List.getD_append _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ (by simp)]
        rfl
      rw [ite_eq_right h9, ite_eq_right h10, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp

  have inputs_agree {r : Fin 9} {x y : Fin 9 → Bool} {i : ℕ}
      (hbase : ∀ h : i < 9, x ⟨i, h⟩ = y ⟨i, h⟩) (h9 : i = 9 → x 0 = y 0)
      (h10 : i = 10 → (x 0 || x r) = (y 0 || y r)) :
      (inputs r x).getD i false = (inputs r y).getD i false := by
    rw [← List.append_nil (inputs r x), ← List.append_nil (inputs r y), input_read, input_read]
    split
    · exact hbase _
    split
    · rw [h9 (by assumption)]
    split
    · exact h10 (by assumption)
    rfl

  have has_reader {C : Circuit} (hC : FanInTwo C) (w v : List Bool)
      (hlen : w.length = v.length) (bad : ℕ → Prop) (hout : ¬bad C.output)
      (hraw : ∀ i, ¬bad i → w.getD i false = v.getD i false)
      (hne : C.eval w ≠ C.eval v) : ∃ g ∈ C.gates, ∃ i ∈ reads g, bad i := by
    by_contra! hnone
    refine hne (eval_eq_of_steps C w v hlen (hraw _ hout) ?_)
    intro g hg s
    apply gateValue_congr hC hg
    intro i hi
    exact append_agree hlen s i (hraw i (hnone g hg i hi))

  have equal_hit {gs : List Gate} {p : Gate → Bool} (h : gs.countP p ≤ 1)
      {g k : Gate} (hg : g ∈ gs) (hk : k ∈ gs) (hpg : p g = true) (hpk : p k = true) :
      g = k := by
    have mg : g ∈ gs.filter p := List.mem_filter.mpr ⟨hg, hpg⟩
    have mk : k ∈ gs.filter p := List.mem_filter.mpr ⟨hk, hpk⟩
    rw [List.countP_eq_length_filter] at h
    cases he : gs.filter p with
    | nil => simp [he] at mg
    | cons a t =>
      simp only [he, List.length_cons] at h
      have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
      simp only [he, ht, List.mem_singleton] at mg mk
      exact mg.trans mk.symm

  have hit_of_mem {r : ℕ} {g : Gate} {i : ℕ} (hi : i ∈ reads g)
      (h : i = 0 ∨ i = 4 ∨ i = 9 ∨ (r = 4 ∧ i = 10)) : signedHits r g = true :=
    List.any_eq_true.mpr ⟨i, hi, decide_eq_true h⟩

  have binary_at_four {C : Circuit} (hC : FanInTwo C) {g : Gate} (hg : g ∈ C.gates)
      {q : ℕ} (hq : q ∈ reads g) (h4 : 4 ∈ reads g) (hne : q ≠ 4) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ i, g.inputs = [i, 4] ∨ g.inputs = [4, i] := by
    have hlarge : 2 ≤ (reads g).length := by
      cases he : reads g with
      | nil => simp [he] at hq
      | cons a t =>
        cases t with
        | nil =>
          simp only [he, List.mem_singleton] at hq h4
          exact False.elim (hne (hq.trans h4.symm))
        | cons b t => simp
    have hkind : g.op = .and ∨ g.op = .or := by
      rcases gate_kind hC hg with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hs : (reads g).length ≤ 1 := by
          simp [reads, hop, boolNot]
        omega
    have he : reads g = g.inputs := by
      rcases hkind with hop | hop
      · simp [reads, hop, boolAnd]
      · simp [reads, hop, boolOr]
    rw [he] at h4 hlarge
    have hsmall := (hC g hg).2
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by omega : g.inputs.length = 2)
    rw [hab] at h4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with ha | hb
    · exact ⟨hkind, b, Or.inr (by simpa only [ha] using hab)⟩
    · exact ⟨hkind, a, Or.inl (by simpa only [hb] using hab)⟩

  have necessary (r : Fin 9) (hr : r = 1 ∨ r = 4) (C : Circuit) (hC : FanInTwo C)
      (hEval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x r]) = F x) :
      1 ≤ C.gates.countP (hits freeze0) ∧ 2 ≤ C.gates.countP (signedHits r.val) := by
    change ∀ x, C.eval (inputs r x) = F x at hEval
    have raw_exclusion (i : ℕ) (hi : i < 11) (x : Fin 9 → Bool)
        (hx : (inputs r x).getD i false ≠ F x) : C.output ≠ i := by
      intro he
      have hout : C.output < (inputs r x).length := by simpa [he, inputs] using hi
      exact hx (he ▸ (eval_raw C (inputs r x) hout).symm.trans (hEval x))
    have ho0 := raw_exclusion 0 (by decide) (fun j => decide (j = 0)) (by
      rcases hr with rfl | rfl <;> decide)
    have ho4 := raw_exclusion 4 (by decide) (fun j => decide (j = 4)) (by
      rcases hr with rfl | rfl <;> decide)
    have ho9 := raw_exclusion 9 (by decide) (fun _ => false) (by
      rcases hr with rfl | rfl <;> decide)
    have ho10 := raw_exclusion 10 (by decide) (fun j => decide (j = 0)) (by
      rcases hr with rfl | rfl <;> decide)
    have eval_ne (x y : Fin 9 → Bool) (hx : F x = false) (hy : F y = true) :
        C.eval (inputs r x) ≠ C.eval (inputs r y) := by simp [hEval, hx, hy]

    -- With x_r true, changing x_0 affects only raw wires 0 and 9.
    let x0 : Fin 9 → Bool := fun j => decide (j = r)
    let y0 : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = r)
    have n0 := eval_ne x0 y0 (by rcases hr with rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl <;> decide)
    obtain ⟨g0, hg0, q, hq, hqa⟩ := has_reader hC (inputs r x0) (inputs r y0) (by simp [inputs])
      (fun i => i = 0 ∨ i = 9) (fun h => h.elim ho0 ho9) (by
        intro i hi
        apply inputs_agree
        · intro h
          have hn : (⟨i, h⟩ : Fin 9) ≠ 0 := fun he => hi (Or.inl (congrArg Fin.val he))
          simp [x0, y0, hn]
        · intro he
          exact (hi (Or.inr he)).elim
        · intro _
          simp [x0, y0]) n0

    have signHit : hits freeze0 g0 = true := List.any_eq_true.mpr ⟨q, hq, decide_eq_true hqa⟩
    refine ⟨?_, ?_⟩
    · have mem : g0 ∈ C.gates.filter (hits freeze0) := List.mem_filter.mpr ⟨hg0, signHit⟩
      rw [List.countP_eq_length_filter]
      cases h : C.gates.filter (hits freeze0) with
      | nil => simp [h] at mem
      | cons g gs => simp

    -- Turning on x_4 creates edge 3–4 or 0–4 while preserving the supplied OR.
    let a : Fin 9 := if r = 1 then 3 else 0
    let x4 : Fin 9 → Bool := fun j => decide (j = a)
    let y4 : Fin 9 → Bool := fun j => decide (j = 4 ∨ j = a)
    have n4 := eval_ne x4 y4 (by rcases hr with rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl <;> decide)
    obtain ⟨g4, hg4, i, hi, he⟩ := has_reader hC (inputs r x4) (inputs r y4) (by simp [inputs])
      (fun i => i = 4) ho4 (by
        intro i hne
        apply inputs_agree
        · intro h
          have hn : (⟨i, h⟩ : Fin 9) ≠ 4 := fun he => hne (congrArg Fin.val he)
          simp [x4, y4, hn]
        · intro _
          rcases hr with rfl | rfl <;> decide
        · intro _
          rcases hr with rfl | rfl <;> decide) n4
    subst i

    by_contra! hc
    have count : C.gates.countP (signedHits r.val) ≤ 1 := by omega
    have ph0 : signedHits r.val g0 = true := hit_of_mem hq (by omega)
    have ph4 : signedHits r.val g4 = true := hit_of_mem hi (Or.inr (Or.inl rfl))
    have same := equal_hit count hg4 hg0 ph4 ph0
    subst g4
    obtain ⟨hkind, j, hj⟩ := binary_at_four hC hg0 hq hi (by omega)

    -- Fix x_4 to the absorbing value of the sole gate reading the changed wires.
    let b := g0.op.eval [true, false]
    let x : Fin 9 → Bool := fun k => decide (k = 1) || (b && decide (k = 4))
    let y : Fin 9 → Bool := fun k => decide (k = 0) || x k
    have nx : C.eval (inputs r x) ≠ C.eval (inputs r y) := by
      apply eval_ne
      · change F (fun k => decide (k = 1) || (b && decide (k = 4))) = false
        cases b <;> decide
      · change F (fun k => decide (k = 0) ||
          (decide (k = 1) || (b && decide (k = 4)))) = true
        cases b <;> decide
    have hrx (i : ℕ) (h : ¬(i = 0 ∨ i = 4 ∨ i = 9 ∨ (r.val = 4 ∧ i = 10))) :
        (inputs r x).getD i false = (inputs r y).getD i false := by
      apply inputs_agree
      · intro hn
        have hn0 : (⟨i, hn⟩ : Fin 9) ≠ 0 := fun e => h (Or.inl (congrArg Fin.val e))
        simp [y, hn0]
      · intro he
        exact (h (Or.inr (Or.inr (Or.inl he)))).elim
      · intro he
        rcases hr with h1 | h4
        · simp [h1, x, y]
        · exact (h (Or.inr (Or.inr (Or.inr ⟨congrArg Fin.val h4, he⟩)))).elim
    apply nx
    refine eval_eq_of_steps C (inputs r x) (inputs r y) (by simp [inputs]) (hrx _ ?_) ?_
    · rintro (h | h | h | ⟨_, h⟩)
      exacts [ho0 h, ho4 h, ho9 h, ho10 h]
    · intro g hg s
      by_cases hp : signedHits r.val g = true
      · have he := equal_hit count hg hg0 hp ph0
        subst g
        have hx4 : (inputs r x ++ s).getD 4 false = b := by
          rw [input_read, dite_eq_left (by decide : 4 < 9)]
          change x 4 = b
          simp [x]
        have hy4 : (inputs r y ++ s).getD 4 false = b := by
          rw [input_read, dite_eq_left (by decide : 4 < 9)]
          change y 4 = b
          simp [x, y]
        simp only [List.getD_eq_getElem?_getD] at hx4 hy4
        rcases hkind with hop | hop
        · rcases hj with hj | hj <;> simp [gateValue, hop, hj, boolAnd, hx4, hy4, b]
        · rcases hj with hj | hj <;> simp [gateValue, hop, hj, boolOr, hx4, hy4, b]
      · apply gateValue_congr hC hg
        intro i hi
        apply append_agree (by simp [inputs])
        exact hrx i (fun h => hp (hit_of_mem hi h))
  have restriction (r : Fin 9) (hr : r = 1 ∨ r = 4) :
      ∃ x : Fin 9 → Bool, C.eval (input r x) ≠ F x := by
    classical
    by_contra failed
    have computes (x : Fin 9 → Bool) : C.eval (input r x) = F x := by
      by_contra h
      exact failed ⟨x, h⟩
    have slice0 (x) : C.eval (rows (entry0 r.val) x) = H x := by
      rw [← args0 r hr, computes, map0]
    have slice4 (x) : C.eval (rows (entry4 r.val) x) = T x := by
      rw [← args4 r hr, computes, map4]
    have bound0 := lower 8 11 _ freeze0 H eight (const0 _) slice0 ⟨fun _ => false, rfl⟩
    have bound4 := lower 7 10 _ (freeze4 r.val) T seven (const4 _) slice4 ⟨fun _ => false, rfl⟩
    have signed : C.gates.countP (hits freeze0) ≤ 1 := by omega
    obtain ⟨oneSigned, twoFrozen⟩ := necessary r hr C fan computes
    change 2 ≤ C.gates.countP (hits (freeze4 r.val)) at twoFrozen
    have exactSigned : C.gates.countP (hits freeze0) = 1 := by omega
    have exactTwo : C.gates.countP (hits (freeze4 r.val)) = 2 := by omega
    have exactSize : C.size = 13 := by omega
    exact failed (core r hr C fan exactSize exactSigned exactTwo)
  have seedInput (r : Fin 9) (x : Fin 9 → Bool) :
      let w := List.ofFn x ++ [!x 0]
      w ++ [GateOp.or.eval ([0,r.val].map (fun i => w.getD i false))] = input r x := by
    dsimp only
    let w := List.ofFn x ++ [!x 0]
    have get (i : Fin 9) : w.getD i.val false = x i := by
      change (List.ofFn x ++ [!x 0]).getD i.val false = _
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [i.isLt, ↓reduceDIte, Option.getD_some]
    have eval2 (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    change w ++ [GateOp.or.eval [w.getD 0 false,w.getD r.val false]] = input r x
    rw [show w.getD 0 false = x 0 from get (0 : Fin 9), get r, eval2]
    simp only [w, input, List.append_assoc, List.cons_append, List.nil_append]
  rcases hs with rfl | rfl
  · obtain ⟨x, hx⟩ := restriction 1 (Or.inl rfl)
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [GateOp.or.eval ([0,(1 : Fin 9).val].map (fun i => (List.ofFn x ++ [!x 0]).getD i false))]) ≠ F x
    rwa [seedInput 1 x]
  · obtain ⟨x, hx⟩ := restriction 4 (Or.inr rfl)
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [GateOp.or.eval ([0,(4 : Fin 9).val].map (fun i => (List.ofFn x ++ [!x 0]).getD i false))]) ≠ F x
    rwa [seedInput 4 x]
