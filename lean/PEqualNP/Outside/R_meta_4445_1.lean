import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4445_1
  (theta : ¬ HasCircuitSize 7 (fun x : Fin 7 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3) 10)
  (erase :
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
    ∀ (n : ℕ) (entries : List (Bool ⊕ ℕ)) (fixed : ℕ → Bool) (C : Circuit), FanInTwo C →
      (∀ i, fixed i = true → i < entries.length ∧ ∃ b : Bool, entries.getD i (.inl false) = .inl b) →
      (∃ x : Fin n → Bool, C.eval (rows n entries x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + C.gates.countP (fun g => (reads g).any fixed) ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (rows n entries x))
  (prune :
    let inputs := fun (r : Fin 9) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6, (x 4 || x 6) || x r]
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let frozen := fun i : ℕ => decide (i = 4 ∨ i = 6 ∨ i = 9)
    let hits := fun g : Gate => (reads g).any frozen
    let normal := fun g : Gate => g.op = GateOp.or ∧ g.inputs.length = 2 ∧ (g.inputs.filter frozen).length = 1
    let cut := fun y : Fin 7 → Bool => (![y 4,y 0,y 1,y 5,false,y 6,false,y 2,y 3] : Fin 9 → Bool)
    ∀ (r : Fin 9) (C : Circuit), FanInTwo C → C.size = 13 → C.gates.countP hits = 2 →
      (∃ g ∈ C.gates, hits g = true ∧ ¬ normal g) →
      (∃ y : Fin 7 → Bool, C.eval (inputs r (cut y)) = false) →
      (∃ y : Fin 7 → Bool, C.eval (inputs r (cut y)) = true) →
      (∃ B : Circuit, FanInTwo B ∧ B.size ≤ 12 ∧
        ∀ x : Fin 9 → Bool, B.eval (inputs r x) = C.eval (inputs r x)) ∨
      (∃ D : Circuit, FanInTwo D ∧ D.size ≤ 10 ∧
        ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = C.eval (inputs r (cut y))))
  (core :
    let inputs := fun (r : Fin 9) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6, (x 4 || x 6) || x r]
    let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
    let frozen := fun i : ℕ => decide (i = 4 ∨ i = 6 ∨ i = 9)
    let hits := fun g : Gate => (reads g).any frozen
    let normal := fun g : Gate => g.op = GateOp.or ∧ g.inputs.length = 2 ∧ (g.inputs.filter frozen).length = 1
    let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
    ∀ (r : Fin 9), r = 0 ∨ r = 2 ∨ r = 7 → ∀ C : Circuit, FanInTwo C →
      C.size = 13 → C.gates.countP hits = 2 →
      (∀ g ∈ C.gates, hits g = true → normal g) →
      ∃ x : Fin 9 → Bool, C.eval (inputs r x) ≠ F x) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(81 : ℕ), (84 : ℕ), (208 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x4 (Fin.snoc (Fin.snoc x6 (x6 (4 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x7 : Fin (9 : ℕ)), x2.testBit ↑x7 = Bool.true ∧ x6 x7 = Bool.true))) = x1 x6) → (14 : ℕ) ≤ x4.size := by
  intro packed m hm C fan works
  let F := fun x : Fin 9 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let H := fun x : Fin 7 → Bool =>
    x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 ||
    x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3
  let inputs := fun (r : Fin 9) (x : Fin 9 → Bool) => List.ofFn x ++ [x 4 || x 6, (x 4 || x 6) || x r]
  let cut := fun y : Fin 7 → Bool => (![y 4,y 0,y 1,y 5,false,y 6,false,y 2,y 3] : Fin 9 → Bool)
  let reads := fun g : Gate => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let frozen := fun i : ℕ => decide (i = 4 ∨ i = 6 ∨ i = 9)
  let hits := fun g : Gate => (reads g).any frozen
  let normal := fun g : Gate => g.op = GateOp.or ∧ g.inputs.length = 2 ∧ (g.inputs.filter frozen).length = 1
  let rows := fun (n : ℕ) (entries : List (Bool ⊕ ℕ)) (x : Fin n → Bool) => entries.map (Sum.elim id (fun i => (List.ofFn x).getD i false))
  have boolAnd (l : List Bool) : GateOp.eval .and l = l.all id := rfl
  have boolOr (l : List Bool) : GateOp.eval .or l = l.any id := rfl
  have boolNot (l : List Bool) : GateOp.eval .not l = !(l.headD false) := rfl
  have inputs_length (r : Fin 9) (x : Fin 9 → Bool) :
      (inputs r x).length = 11 := by simp [inputs]

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
        else if i = 9 then x 4 || x 6
        else if i = 10 then (x 4 || x 6) || x r
        else s.getD (i - 11) false := by
    by_cases hi : i < 9
    · rw [dite_eq_left hi, List.getD_append _ _ _ _ (by rw [inputs_length]; omega)]
      dsimp only [inputs]
      rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, dite_eq_left hi]
      rfl
    · rw [dite_eq_right hi]
      by_cases h9 : i = 9
      · subst i
        rw [ite_eq_left rfl, List.getD_append _ _ _ _ (by rw [inputs_length]; decide)]
        rfl
      by_cases h10 : i = 10
      · subst i
        rw [ite_eq_right h9, ite_eq_left rfl, List.getD_append _ _ _ _ (by rw [inputs_length]; decide)]
        rfl
      rw [ite_eq_right h9, ite_eq_right h10, List.getD_append_right _ _ _ _ (by rw [inputs_length]; omega),
        inputs_length]

  have inputs_agree {r : Fin 9} {x y : Fin 9 → Bool} {i : ℕ}
      (hbase : ∀ h : i < 9, x ⟨i, h⟩ = y ⟨i, h⟩) (h9 : i = 9 → (x 4 || x 6) = (y 4 || y 6))
      (h10 : i = 10 → ((x 4 || x 6) || x r) = ((y 4 || y 6) || y r)) :
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

  have hit_of_mem {g : Gate} {i : ℕ} (hi : i ∈ reads g)
      (h : i = 4 ∨ i = 6 ∨ i = 9) : hits g = true :=
    List.any_eq_true.mpr ⟨i, hi, decide_eq_true h⟩

  have pair_read {C : Circuit} (fan : FanInTwo C) {g : Gate}
      (inC : g ∈ C.gates) (r4 : 4 ∈ reads g) (r6 : 6 ∈ reads g) :
      (g.op = .and ∨ g.op = .or) ∧ (g.inputs = [4, 6] ∨ g.inputs = [6, 4]) := by
    have htwo : 2 ≤ (reads g).length := by
      cases eqs : reads g with
      | nil => simp [eqs] at r4
      | cons a tail =>
        cases tail with
        | nil =>
          simp [eqs] at r4 r6
          omega
        | cons b t => simp
    have hkind : g.op = .and ∨ g.op = .or := by
      rcases gate_kind fan inC with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hsmall : (reads g).length ≤ 1 := by simp [reads, hop, boolNot]
        omega
    have hread : reads g = g.inputs := by
      rcases hkind with h | h <;> simp [reads, h, boolAnd, boolOr]
    rw [hread] at r4 r6 htwo
    have hsmall := (fan g inC).2
    obtain ⟨a,b,eqs⟩ := List.length_eq_two.mp (by omega : g.inputs.length = 2)
    rw [eqs] at r4 r6
    simp only [List.mem_cons, List.not_mem_nil, or_false] at r4 r6
    refine ⟨hkind, ?_⟩
    rcases r4 with r4 | r4 <;> rcases r6 with r6 | r6
    · omega
    · exact Or.inl (by rw [eqs, ← r4, ← r6])
    · exact Or.inr (by rw [eqs, ← r6, ← r4])
    · omega

  have output_not_input (r : Fin 9) (C : Circuit)
      (eval : ∀ x : Fin 9 → Bool, C.eval (inputs r x) = F x) : 11 ≤ C.output := by
    have hpoint : ∀ (r : Fin 9) (i : Fin 11),
        let x : Fin 9 → Bool := fun j => decide (j.val = if i.val < 9 then i.val else 4)
        (inputs r x).getD i.val false ≠ F x := by decide +kernel
    by_contra! small
    let i : Fin 11 := ⟨C.output, small⟩
    let x : Fin 9 → Bool := fun j => decide (j.val = if i.val < 9 then i.val else 4)
    have h := hpoint r i
    change (inputs r x).getD C.output false ≠ F x at h
    have out : C.output < (inputs r x).length := by simpa only [inputs_length] using small
    exact h ((eval_raw C (inputs r x) out).symm.trans (eval x))

  have separate_readers (r : Fin 9) (C : Circuit) (fan : FanInTwo C)
      (eval : ∀ x : Fin 9 → Bool, C.eval (inputs r x) = F x) :
      (∃ g ∈ C.gates, 4 ∈ reads g) ∧ (∃ g ∈ C.gates, 6 ∈ reads g) := by
    have hr := output_not_input r C eval
    constructor
    · let x : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 6)
      let y : Fin 9 → Bool := fun j => decide (j = 4) || x j
      have h : C.eval (inputs r x) ≠ C.eval (inputs r y) := by
        rw [eval,eval]
        decide
      obtain ⟨g, hg, i, hi, he⟩ := has_reader fan (inputs r x) (inputs r y) (by simp [inputs_length])
        (fun i => i = 4) (by omega) (by
          intro i hne
          apply inputs_agree
          · intro h
            have hn : (⟨i, h⟩ : Fin 9) ≠ 4 := fun he => hne (congrArg Fin.val he)
            simp [y,hn]
          · intro _
            simp [x,y]
          · intro _
            simp [x,y]) h
      exact ⟨g,hg,he ▸ hi⟩
    · let x : Fin 9 → Bool := fun j => decide (j = 1 ∨ j = 4)
      let y : Fin 9 → Bool := fun j => decide (j = 6) || x j
      have h : C.eval (inputs r x) ≠ C.eval (inputs r y) := by
        rw [eval,eval]
        decide
      obtain ⟨g, hg, i, hi, he⟩ := has_reader fan (inputs r x) (inputs r y) (by simp [inputs_length])
        (fun i => i = 6) (by omega) (by
          intro i hne
          apply inputs_agree
          · intro h
            have hn : (⟨i, h⟩ : Fin 9) ≠ 6 := fun he => hne (congrArg Fin.val he)
            simp [y,hn]
          · intro _
            simp [x,y]
          · intro _
            simp [x,y]) h
      exact ⟨g,hg,he ▸ hi⟩

  have necessary (r : Fin 9) (C : Circuit) (fan : FanInTwo C)
      (eval : ∀ x : Fin 9 → Bool, C.eval (inputs r x) = F x) :
      2 ≤ C.gates.countP hits := by
    have ho := output_not_input r C eval
    obtain ⟨⟨g,hg,hg4⟩,⟨k,hk,hk6⟩⟩ := separate_readers r C fan eval
    have gp := hit_of_mem hg4 (Or.inl rfl)
    have kp := hit_of_mem hk6 (Or.inr (Or.inl rfl))
    by_contra! small
    have count : C.gates.countP hits ≤ 1 := by omega
    have same := equal_hit count hk hg kp gp
    subst k
    obtain ⟨kind, pair⟩ := pair_read fan hg hg4 hk6
    let x : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 6)
    let y : Fin 9 → Bool := fun j => decide (j = 0 ∨ j = 4)
    have ne : C.eval (inputs r x) ≠ C.eval (inputs r y) := by
      rw [eval,eval]
      decide
    have agree (i : ℕ) (h : ¬(i = 4 ∨ i = 6 ∨ i = 9)) :
        (inputs r x).getD i false = (inputs r y).getD i false := by
      apply inputs_agree
      · intro hi
        have h4 : (⟨i, hi⟩ : Fin 9) ≠ 4 := fun e => h (Or.inl (congrArg Fin.val e))
        have h6 : (⟨i, hi⟩ : Fin 9) ≠ 6 := fun e => h (Or.inr (Or.inl (congrArg Fin.val e)))
        simp [x,y,h4,h6]
      · intro _
        simp [x,y]
      · intro _
        simp [x,y]
    apply ne
    refine eval_eq_of_steps C (inputs r x) (inputs r y) (by simp [inputs_length]) (agree _ (by omega)) ?_
    intro a ha s
    by_cases h : hits a = true
    · have eqs := equal_hit count ha hg h gp
      subst a
      have x4 : (inputs r x ++ s).getD 4 false = false := by
        rw [input_read, dite_eq_left (by decide : 4 < 9)]
        decide
      have x6 : (inputs r x ++ s).getD 6 false = true := by
        rw [input_read, dite_eq_left (by decide : 6 < 9)]
        decide
      have y4 : (inputs r y ++ s).getD 4 false = true := by
        rw [input_read, dite_eq_left (by decide : 4 < 9)]
        decide
      have y6 : (inputs r y ++ s).getD 6 false = false := by
        rw [input_read, dite_eq_left (by decide : 6 < 9)]
        decide
      simp only [List.getD_eq_getElem?_getD] at x4 x6 y4 y6
      rcases pair with p | p <;> rcases kind with k | k <;>
        simp [gateValue, p, k, boolAnd, boolOr, x4,x6,y4,y6]
    · apply gateValue_congr fan ha
      intro i hi
      exact append_agree (by simp [inputs_length]) s i (agree i fun hb => h (hit_of_mem hi hb))

  have mask_input (m : ℕ) (hm : m ∈ ([81,84,208] : List ℕ)) :
      ∃ r : Fin 9, (r = 0 ∨ r = 2 ∨ r = 7) ∧ ∀ x : Fin 9 → Bool,
        decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true) =
          ((x 4 || x 6) || x r) := by
    have h : m = 81 ∨ m = 84 ∨ m = 208 := by simpa using hm
    rcases h with rfl | rfl | rfl
    · exact ⟨0, by simp, by decide +kernel⟩
    · exact ⟨2, by simp, by decide +kernel⟩
    · exact ⟨7, by simp, by decide +kernel⟩

  have decode_target : ∀ x : Fin 9 → Bool,
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = F x := by
    decide +kernel
  have ofFn_snoc {n : ℕ} (x : Fin n → Bool) (b : Bool) :
      List.ofFn (Fin.snoc x b : Fin (n+1) → Bool) = List.ofFn x ++ [b] := by
    rw [List.ofFn_succ']
    simp
  obtain ⟨r, hr, encode⟩ := mask_input m hm
  have computes (x : Fin 9 → Bool) : C.eval (inputs r x) = F x := by
    have hh := works x
    change C.eval (List.ofFn (Fin.snoc (Fin.snoc x (x 4 || x 6))
      (decide (∃ i : Fin 9, m.testBit i.val = true ∧ x i = true)))) = packed x at hh
    rw [encode x, ofFn_snoc, ofFn_snoc, List.append_assoc] at hh
    exact hh.trans (decode_target x)
  let entries (r : Fin 9) := ([.inr 4,.inr 0,.inr 1,.inr 5,.inl false,.inr 6,.inl false,
    .inr 2,.inr 3,.inl false,.inr (if r = 0 then 4 else if r = 2 then 1 else 2)] : List (Bool ⊕ ℕ))
  have fixed (i : ℕ) (hit : frozen i = true) :
      i < (entries r).length ∧ ∃ b : Bool, (entries r).getD i (.inl false) = .inl b := by
    change decide (i = 4 ∨ i = 6 ∨ i = 9) = true at hit
    rcases of_decide_eq_true hit with rfl | rfl | rfl <;> exact ⟨by simp [entries], false, rfl⟩
  have map (x : Fin 7 → Bool) : inputs r (cut x) = rows 7 (entries r) x := by
    rcases hr with rfl | rfl | rfl <;> rfl
  have mapF : ∀ x : Fin 7 → Bool, F (cut x) = H x := by
    dsimp only [F, cut, H]
    decide +kernel
  have Hfalse : H (fun _ => false) = false := rfl
  have Htrue : H (fun _ => true) = true := rfl
  have lower (B : Circuit) (bf : FanInTwo B)
      (bc : ∀ x, B.eval (inputs r x) = F x) : 11 + B.gates.countP hits ≤ B.size := by
    have slice (x : Fin 7 → Bool) : B.eval (rows 7 (entries r) x) = H x := by
      rw [← map, bc, mapF]
    obtain ⟨D,df,count,same⟩ := erase 7 (entries r) frozen B bf fixed
      ⟨fun _ => false, (slice _).trans Hfalse⟩
    change D.size + B.gates.countP hits ≤ B.size at count
    have good : 11 ≤ D.size := by
      by_contra low
      exact theta ⟨D,df,by omega,fun x => (same x).trans (slice x)⟩
    omega
  by_contra! small
  have budget := lower C fan computes
  have need := necessary r C fan computes
  have exactSize : C.size = 13 := by omega
  have exactReads : C.gates.countP hits = 2 := by omega
  by_cases shape : ∀ g ∈ C.gates, hits g = true → normal g
  · obtain ⟨x, fail⟩ := core r hr C fan exactSize exactReads shape
    exact fail (computes x)
  · push Not at shape
    have restricted (y : Fin 7 → Bool) : C.eval (inputs r (cut y)) = H y :=
      (computes (cut y)).trans (mapF y)
    have someFalse : ∃ y, C.eval (inputs r (cut y)) = false :=
      ⟨fun _ => false, (restricted (fun _ => false)).trans Hfalse⟩
    have someTrue : ∃ y, C.eval (inputs r (cut y)) = true :=
      ⟨fun _ => true, (restricted (fun _ => true)).trans Htrue⟩
    rcases prune r C fan exactSize exactReads shape someFalse someTrue with shortened | sliced
    · obtain ⟨B,bf,smallB,same⟩ := shortened
      have bc (x) : B.eval (inputs r x) = F x := (same x).trans (computes x)
      have enough := lower B bf bc
      have readers := necessary r B bf bc
      omega
    · obtain ⟨D,df,smallD,same⟩ := sliced
      exact theta ⟨D, df, smallD, fun y => (same y).trans (restricted y)⟩
