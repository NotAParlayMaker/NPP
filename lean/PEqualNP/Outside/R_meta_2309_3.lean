import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2309_3
    (hUnneg : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (hBinAnd : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 → (D.gates.filter (fun g => g.inputs.contains 0)).length = 1 → j < D.gates.length → 0 < w → w < 9 + j → PEqualNP.MetaComplexity.NestedCover.gateAt D j = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, w] } → (∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False)
    (hBinOr : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (j w : ℕ), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 → (D.gates.filter (fun g => g.inputs.contains 0)).length = 1 → j < D.gates.length → 0 < w → w < 9 + j → PEqualNP.MetaComplexity.NestedCover.gateAt D j = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, w] } → (∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  intro x1_def C x3_in x4_in x5_in hfan hw9 hfun hsize hflt
  dsimp only [x3_in, x4_in, x5_in] at hflt
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wiresFrom : List Gate → List Bool → List Bool :=
    fun gs w => gs.foldl step w
  have length_wiresFrom : ∀ (gs : List Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wiresFrom]
    | cons g gs ih =>
      intro w
      dsimp only [wiresFrom]
      rw [List.foldl_cons]
      have := ih (step w g)
      dsimp only [wiresFrom] at this
      rw [this]
      simp [step]
      omega
  have getD_wiresFrom_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      dsimp only [wiresFrom]
      rw [List.foldl_cons]
      have := ih (step w g) i (by simp [step]; omega)
      dsimp only [wiresFrom] at this
      rw [this]
      simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ (w : List Bool) (b : Bool), (w ++ [b]).getD w.length false = b := by
    intro w b; simp
  have getD_snoc_ne : ∀ (w : List Bool) (b : Bool) (i : ℕ), i ≠ w.length →
      (w ++ [b]).getD i false = w.getD i false := by
    intro w b i h
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have eval_and : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  let normG : Gate → Gate := fun g =>
    { op := g.op, inputs := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs }
  have normG_eval : ∀ (g : Gate), (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) → ∀ (f : ℕ → Bool),
      (normG g).op.eval ((normG g).inputs.map f) = g.op.eval (g.inputs.map f) := by
    intro g h f
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
    rcases hop with rfl | rfl | rfl
    · have h0 : GateOp.and.eval [false] = false := rfl
      simp only [normG, h0, Bool.false_eq_true, ↓reduceIte]
    · have h0 : GateOp.or.eval [false] = false := rfl
      simp only [normG, h0, Bool.false_eq_true, ↓reduceIte]
    · have h0 : GateOp.not.eval [false] = true := rfl
      cases ins <;> simp [normG, h0, eval_not]
  have normG_ok : ∀ (g : Gate), (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
      ((normG g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (normG g).inputs.length ≤ 2) ∧
      ((normG g).op = GateOp.not → (normG g).inputs.length ≤ 1) := by
    intro g h
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
    rcases hop with rfl | rfl | rfl
    · have h0 : GateOp.and.eval [false] = false := rfl
      exact ⟨⟨Or.inl rfl, by simpa [normG, h0] using h.2⟩, by simp [normG]⟩
    · have h0 : GateOp.or.eval [false] = false := rfl
      exact ⟨⟨Or.inr (Or.inl rfl), by simpa [normG, h0] using h.2⟩, by simp [normG]⟩
    · have h0 : GateOp.not.eval [false] = true := rfl
      refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normG, h0]
  have wiresFrom_normG : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      ∀ w : List Bool, wiresFrom (gs.map normG) w = wiresFrom gs w := by
    intro gs
    induction gs with
    | nil => intro _ w; rfl
    | cons g gs ih =>
      intro hok w
      have hg := hok g List.mem_cons_self
      have s1 : wiresFrom ((g :: gs).map normG) w = wiresFrom (gs.map normG) (step w (normG g)) := rfl
      have s2 : wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl
      have hs : step w (normG g) = step w g := by
        dsimp only [step]
        rw [normG_eval g hg]
      rw [s1, s2, hs, ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]
  let shiftWire : Bool → ℕ → ℕ := fun x7 w =>
    if w = 9 then (if x7 then 0 else 9)
    else if 10 ≤ w then w - 1
    else w
  let transGate : Bool → Gate → Gate := fun x7 g =>
    if 0 ∈ g.inputs ∧ 9 ∈ g.inputs then
      GateOp.casesOn g.op ⟨GateOp.or, []⟩ ⟨GateOp.and, []⟩ ⟨GateOp.and, []⟩ (fun _ => ⟨GateOp.and, []⟩) ⟨GateOp.and, []⟩
    else
      ⟨g.op, g.inputs.map (shiftWire x7)⟩
  have transGate_ok : ∀ (x7 : Bool) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (transGate x7 g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (transGate x7 g).inputs.length ≤ 2 := by
    intro x7 g h
    dsimp only [transGate]
    split_ifs
    · cases g.op <;> simp
    · exact ⟨h.1, by simpa using h.2⟩
  have transGate_mem0 : ∀ (x7 : Bool) (g : Gate),
      (transGate x7 g).inputs.contains 0 = true →
      ([0, 9].any fun w => g.inputs.contains w) = true := by
    intro x7 g
    dsimp only [transGate]
    split_ifs with h09
    · cases g.op <;> simp
    · intro hm
      rw [List.contains_iff_mem, List.mem_map] at hm
      obtain ⟨w, hw, hsw⟩ := hm
      simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, List.contains_iff_mem]
      dsimp only [shiftWire] at hsw
      by_cases hw9 : w = 9
      · subst hw9; exact Or.inr hw
      · rw [if_neg hw9] at hsw
        by_cases hw10 : 10 ≤ w
        · rw [if_pos hw10] at hsw; omega
        · rw [if_neg hw10] at hsw; subst hsw; exact Or.inl hw
  have filter_map_length_le : ∀ {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool),
      (∀ a, q (f a) = true → p a = true) → ∀ l : List α,
      ((l.map f).filter q).length ≤ (l.filter p).length := by
    intro α β f p q h l
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hq : q (f a) = true
      · have hp := h a hq
        simp only [hq, hp, ↓reduceIte, List.length_cons]
        omega
      · have hqf : q (f a) = false := Bool.eq_false_iff.mpr hq
        simp only [hqf, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : p a = true
        · simp only [hp, ↓reduceIte, List.length_cons]; omega
        · have hpf : p a = false := Bool.eq_false_iff.mpr hp
          simp only [hpf, Bool.false_eq_true, ↓reduceIte]; exact ih
  have two_mem_eq : ∀ (l : List ℕ), l.length ≤ 2 → 0 ∈ l → 9 ∈ l → l = [0, 9] ∨ l = [9, 0] := by
    intro l hlen h0 h9
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · cases h0
    · simp only [List.mem_singleton] at h0 h9; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9
      rcases h0 with ha0 | hb0 <;> rcases h9 with ha9 | hb9
      · omega
      · subst ha0; subst hb9; exact Or.inl rfl
      · subst hb0; subst ha9; exact Or.inr rfl
      · omega
    · simp at hlen
  let Rel : Bool → Bool → ℕ → List Bool → List Bool → Prop := fun x7 b0 k w1 w2 =>
    w1.length = 10 + k ∧ w2.length = 9 + k ∧
    w1.getD 0 false = b0 ∧ w1.getD 9 false = !b0 ∧
    (∀ i, 1 ≤ i → i < 9 → w2.getD i false = w1.getD i false) ∧
    (∀ j < k, w2.getD (9 + j) false = w1.getD (10 + j) false) ∧
    (x7 = false → w2.getD 0 false = b0) ∧
    (x7 = true → w2.getD 0 false = !b0)
  have rel_init : ∀ (x7 : Bool) (x8 : Fin 9 → Bool),
      Rel x7 (x8 0) 0 (List.ofFn x8 ++ [!x8 0])
        (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i) := by
    intro x7 x8
    refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.getD_append _ _ _ _ (by simp)]
      simp
    · have hsn := getD_snoc_eq (List.ofFn x8) (!x8 0)
      rwa [List.length_ofFn] at hsn
    · intro i hi1 hi9
      rw [List.getD_append _ _ _ _ (by simp [hi9])]
      have hne : (⟨i, hi9⟩ : Fin 9) ≠ 0 := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have h1 : (List.ofFn fun j : Fin 9 => if j = 0 then x7 != x8 0 else x8 j).getD i false =
          (if (⟨i, hi9⟩ : Fin 9) = 0 then x7 != x8 0 else x8 ⟨i, hi9⟩) := by
        rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
      have h2 : (List.ofFn x8).getD i false = x8 ⟨i, hi9⟩ := by
        rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
      rw [h1, h2]
      simp [hne]
    · intro j hj; cases hj
    · intro hx7; subst hx7; simp
    · intro hx7; subst hx7; simp
  have rel_step : ∀ (x7 b0 : Bool) (k : ℕ) (w1 w2 : List Bool) (g : Gate),
      Rel x7 b0 k w1 w2 →
      ((g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      ((x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) →
      Rel x7 b0 (k + 1) (step w1 g) (step w2 (transGate x7 g)) := by
    intro x7 b0 k w1 w2 g hrel hg_ok hcond
    obtain ⟨hl1, hl2, hw0, hw9, hmid, hprev, hf0, ht0⟩ := hrel
    have heval_eq : (transGate x7 g).op.eval
        ((transGate x7 g).inputs.map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      dsimp only [transGate]
      by_cases h09 : 0 ∈ g.inputs ∧ 9 ∈ g.inputs
      · rw [if_pos h09]
        have hnot_not : g.op ≠ GateOp.not := by
          intro hn
          have hl := hg_ok.2 hn
          rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _⟩⟩
          · rw [hinp] at h09; exact List.not_mem_nil h09.1
          · rw [hinp] at h09; simp only [List.mem_singleton] at h09; omega
          · rw [hinp] at hl; simp at hl
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg_ok.1.1
        have hl_eq := two_mem_eq g.inputs hg_ok.1.2 h09.1 h09.2
        rcases hop with hop | hop | hop
        · rw [hop]
          rcases hl_eq with hin | hin <;> rw [hin] <;>
            simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
        · rw [hop]
          rcases hl_eq with hin | hin <;> rw [hin] <;>
            simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
        · exact (hnot_not hop).elim
      · rw [if_neg h09]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        simp only [Function.comp_apply]
        dsimp only [shiftWire]
        by_cases hw_eq9 : w = 9
        · subst hw_eq9
          rw [if_pos rfl]
          cases hx7 : x7
          · exfalso
            exact h09 ⟨hcond.2 hx7 hw, hw⟩
          · simp only [↓reduceIte, ht0 hx7, hw9]
        · rw [if_neg hw_eq9]
          by_cases hw10 : 10 ≤ w
          · rw [if_pos hw10]
            by_cases hwk : w < 10 + k
            · have hjk : w - 10 < k := by omega
              have h1 : w - 1 = 9 + (w - 10) := by omega
              have h2 : w = 10 + (w - 10) := by omega
              rw [h1, hprev (w - 10) hjk, ← h2]
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
          · rw [if_neg hw10]
            by_cases hw_eq0 : w = 0
            · subst hw_eq0
              cases hx7 : x7
              · rw [hf0 hx7, hw0]
              · exact (hcond.1 hx7 hw).elim
            · exact hmid w (by omega) (by omega)
    let v := g.op.eval (g.inputs.map fun i => w1.getD i false)
    have hs1 : step w1 g = w1 ++ [v] := rfl
    have hs2 : step w2 (transGate x7 g) = w2 ++ [v] := by dsimp only [step]; rw [heval_eq]
    rw [hs1, hs2]
    refine ⟨by simp [hl1]; omega, by simp [hl2]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw0
    · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw9
    · intro i hi1 hi9
      rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
      exact hmid i hi1 hi9
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
        exact hprev j hlt
      · have e2 : 9 + j = w2.length := by omega
        have e1 : 10 + j = w1.length := by omega
        rw [e2, getD_snoc_eq, e1, getD_snoc_eq]
    · intro hx7
      rw [getD_snoc_ne _ _ _ (by omega)]; exact hf0 hx7
    · intro hx7
      rw [getD_snoc_ne _ _ _ (by omega)]; exact ht0 hx7
  have rel_wiresFrom : ∀ (x7 b0 : Bool) (gs : List Gate) (k : ℕ) (w1 w2 : List Bool),
      Rel x7 b0 k w1 w2 →
      (∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      (∀ g ∈ gs, (x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) →
      Rel x7 b0 (k + gs.length) (wiresFrom gs w1) (wiresFrom (gs.map (transGate x7)) w2) := by
    intro x7 b0 gs
    induction gs with
    | nil =>
      intro k w1 w2 hrel _ _
      exact hrel
    | cons g gs ih =>
      intro k w1 w2 hrel hok hcond
      have h1 := rel_step x7 b0 k w1 w2 g hrel (hok g List.mem_cons_self) (hcond g List.mem_cons_self)
      have h2 := ih (k + 1) (step w1 g) (step w2 (transGate x7 g)) h1
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hcond g' (List.mem_cons_of_mem _ hg'))
      change Rel x7 b0 (k + (gs.length + 1)) (wiresFrom gs (step w1 g))
        (wiresFrom (gs.map (transGate x7)) (step w2 (transGate x7 g)))
      rwa [show k + (gs.length + 1) = k + 1 + gs.length by omega]
  have single_filter_disj : ∀ {α : Type} (p : α → Bool) (l : List α),
      (l.filter p).length ≤ 1 → ∀ (a b : α), a ∈ l → b ∈ l →
      p a = true → p b = true → ∀ (q : α → Prop), q a → ¬ q b → False := by
    intro α p l hlen a b ha hb hpa hpb q hqa hqb
    induction l with
    | nil => cases ha
    | cons x xs ih =>
      rw [List.filter_cons] at hlen
      by_cases hpx : p x = true
      · simp only [hpx, ↓reduceIte, List.length_cons] at hlen
        have h0 : xs.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hnone : ∀ y ∈ xs, p y ≠ true := by
          intro y hy hpy
          have hm : y ∈ xs.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
          rw [h0] at hm; cases hm
        rcases List.mem_cons.mp ha with rfl | haxs
        · rcases List.mem_cons.mp hb with rfl | hbxs
          · exact hqb hqa
          · exact hnone b hbxs hpb
        · exact hnone a haxs hpa
      · have hpxf : p x = false := Bool.eq_false_iff.mpr hpx
        simp only [hpxf, Bool.false_eq_true, ↓reduceIte] at hlen
        rcases List.mem_cons.mp ha with rfl | haxs
        · rw [hpa] at hpxf; cases hpxf
        · rcases List.mem_cons.mp hb with rfl | hbxs
          · rw [hpb] at hpxf; cases hpxf
          · exact ih hlen haxs hbxs
  have contract : ∃ (x6 : Circuit) (x7 : Bool),
      FanInTwo x6 ∧ x6.size < C.size ∧
      (List.filter (fun g => g.inputs.contains 0) x6.gates).length ≤ 1 ∧
      ∀ (x8 : Fin 9 → Bool), circuitFun 9 C x8 =
        circuitFun 9 x6 fun i => if i = 0 then x7 != x8 0 else x8 i := by
    obtain ⟨gs, out⟩ := C
    cases gs with
    | nil =>
      exfalso
      have h0 := hw9 (fun _ => false)
      have hl : (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = false :=
        List.getD_eq_default _ _ (by simp)
      change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at h0
      rw [hl] at h0
      cases h0
    | cons g0 tail =>
      have hsz_pos : 0 < ({ gates := g0 :: tail, output := out } : Circuit).size := by
        change 0 < (g0 :: tail).length; simp
      have hw_g0 : ∀ x : Fin 9 → Bool,
          step (List.ofFn x) g0 = List.ofFn x ++ [!x 0] := by
        intro x
        have h9 := hw9 x
        change (wiresFrom tail (step (List.ofFn x) g0)).getD 9 false = !x 0 at h9
        rw [getD_wiresFrom_lt tail _ 9 (by simp [step])] at h9
        have hsn : (step (List.ofFn x) g0).getD 9 false =
            g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
          have h0 := getD_snoc_eq (List.ofFn x)
            (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false))
          rwa [List.length_ofFn] at h0
        rw [hsn] at h9
        dsimp only [step]
        rw [h9]
      let x2 := tail.map normG
      have htail_fan : ∀ g ∈ tail,
          g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
        fun g hg => hfan g (List.mem_cons_of_mem _ hg)
      have hx2_ok : ∀ g ∈ x2,
          (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
          (g.op = GateOp.not → g.inputs.length ≤ 1) := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact normG_ok g' (htail_fan g' hg')
      have hw_eq : ∀ x : Fin 9 → Bool,
          ({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x) =
            wiresFrom x2 (List.ofFn x ++ [!x 0]) := by
        intro x
        change wiresFrom tail (step (List.ofFn x) g0) = _
        rw [hw_g0 x, wiresFrom_normG tail htail_fan]
      by_cases hout9 : out < 9
      · refine ⟨⟨[], out⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
        intro x8
        change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
          (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD out false
        rw [hw_eq x8, getD_wiresFrom_lt x2 _ out (by simp; omega),
          List.getD_append _ _ _ _ (by simp [hout9])]
        congr 1
        ext i
        by_cases hi0 : i = 0
        · subst hi0; simp
        · simp [hi0]
      · by_cases hout_eq9 : out = 9
        · subst hout_eq9
          refine ⟨⟨[], 0⟩, true, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
          intro x8
          rw [show circuitFun 9 { gates := g0 :: tail, output := 9 } x8 = !x8 0 from hw9 x8]
          change (!x8 0) = (List.ofFn fun x9 : Fin 9 => if x9 = 0 then true != x8 0 else x8 x9).getD 0 false
          simp
        · by_cases hout_ge : 10 + x2.length ≤ out
          · refine ⟨⟨[], 9⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
            intro x8
            change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
              (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD 9 false
            rw [hw_eq x8, List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
              List.getD_eq_default _ _ (by simp)]
          · let x7 : Bool := decide (∃ g ∈ x2, 9 ∈ g.inputs ∧ 0 ∉ g.inputs)
            have hflt' : (x2.filter (fun g => [0, 9].any fun w => g.inputs.contains w)).length ≤ 1 := hflt
            have hcond : ∀ g ∈ x2, (x7 = true → 0 ∉ g.inputs) ∧
                (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs) := by
              intro g hg
              refine ⟨?_, ?_⟩
              · intro hx7 h0g
                obtain ⟨g9, hg9, h9in, h0not⟩ := of_decide_eq_true hx7
                have p_g : ([0, 9].any fun w => g.inputs.contains w) = true := by
                  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                    List.contains_iff_mem]
                  exact Or.inl h0g
                have p_g9 : ([0, 9].any fun w => g9.inputs.contains w) = true := by
                  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                    List.contains_iff_mem]
                  exact Or.inr h9in
                exact single_filter_disj _ x2 hflt' g g9 hg hg9 p_g p_g9
                  (fun z => 0 ∈ z.inputs) h0g h0not
              · intro hx7 h9g
                by_contra h0not
                have ht : x7 = true := decide_eq_true ⟨g, hg, h9g, h0not⟩
                rw [hx7] at ht; cases ht
            let x6 : Circuit := ⟨x2.map (transGate x7), out - 1⟩
            have hx6_fan : FanInTwo x6 := by
              intro g hg
              obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
              exact transGate_ok x7 g' (hx2_ok g' hg').1
            have hx6_sz : x6.size < ({ gates := g0 :: tail, output := out } : Circuit).size := by
              change (x2.map (transGate x7)).length < (g0 :: tail).length
              simp [x2]
            have hx6_flt : (x6.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 :=
              (filter_map_length_le (transGate x7)
                (fun g => [0, 9].any fun w => g.inputs.contains w)
                (fun g => g.inputs.contains 0)
                (transGate_mem0 x7) x2).trans hflt'
            refine ⟨x6, x7, hx6_fan, hx6_sz, hx6_flt, ?_⟩
            intro x8
            have hrel := rel_wiresFrom x7 (x8 0) x2 0
              (List.ofFn x8 ++ [!x8 0])
              (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)
              (rel_init x7 x8) hx2_ok hcond
            have hj_lt : out - 10 < 0 + x2.length := by omega
            have hprev := hrel.2.2.2.2.2.1 (out - 10) hj_lt
            have e1 : 10 + (out - 10) = out := by omega
            have e2 : 9 + (out - 10) = out - 1 := by omega
            rw [e1, e2] at hprev
            change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
              (wiresFrom (x2.map (transGate x7))
                (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)).getD (out - 1) false
            rw [hw_eq x8, hprev]
  obtain ⟨D, b, hDFan, hDSize_lt, hDFlt, hDEq⟩ := contract
  have hDSize : D.size ≤ 14 := by omega
  have hD_fun : ∀ x : Fin 9 → Bool,
      circuitFun 9 D (fun i => if i = 0 then b != x 0 else x i) = x1_def x := by
    intro x
    exact (hDEq x).symm.trans (congrFun hfun x)
  cases b with
  | false =>
    have hD_std : circuitFun 9 D = x1_def := by
      funext x
      have same : (fun i : Fin 9 => if i = 0 then false != x 0 else x i) = x := by
        funext i; by_cases h : i = 0 <;> simp [h]
      have h0 := hD_fun x
      rwa [same] at h0
    have h15 := hUnneg D hDFan hD_std
    omega
  | true =>
    have hD_neg : ∀ x : Fin 9 → Bool,
        circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) = x1_def x := by
      intro x
      have same : (fun i : Fin 9 => if i = 0 then true != x 0 else x i) =
          (fun i : Fin 9 => if i = 0 then !x 0 else x i) := by
        funext i; by_cases h : i = 0 <;> simp [h]
      have h0 := hD_fun x
      rwa [same] at h0
    have indep_wires : ∀ (gs : List Gate), (∀ g ∈ gs, 0 ∉ g.inputs) →
        ∀ (w1 w2 : List Bool), w1.length = w2.length →
        (∀ k, k ≠ 0 → w1.getD k false = w2.getD k false) →
        (wiresFrom gs w1).length = (wiresFrom gs w2).length ∧
        (∀ k, k ≠ 0 → (wiresFrom gs w1).getD k false = (wiresFrom gs w2).getD k false) := by
      intro gs hgs
      induction gs with
      | nil =>
        intro w1 w2 hl hk
        exact ⟨hl, hk⟩
      | cons g gs ih =>
        intro w1 w2 hl hk
        have hg0 := hgs g List.mem_cons_self
        have heval : g.op.eval (g.inputs.map fun i => w1.getD i false) =
            g.op.eval (g.inputs.map fun i => w2.getD i false) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          exact hk i (fun h0 => hg0 (h0 ▸ hi))
        have hstep_len : (step w1 g).length = (step w2 g).length := by
          simp [step, hl]
        have hstep_k : ∀ k, k ≠ 0 → (step w1 g).getD k false = (step w2 g).getD k false := by
          intro k hk0
          by_cases hkl : k < w1.length
          · dsimp only [step]
            rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (hl ▸ hkl)]
            exact hk k hk0
          · by_cases hke : k = w1.length
            · dsimp only [step]
              rw [hke, getD_snoc_eq, hl, getD_snoc_eq, heval]
            · dsimp only [step]
              rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [hl]; omega)]
        exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step w1 g) (step w2 g) hstep_len hstep_k
    have hZero_absurd : ∀ (E : Circuit), (∀ g ∈ E.gates, 0 ∉ g.inputs) →
        (∀ x : Fin 9 → Bool, circuitFun 9 E (fun i => if i = 0 then !x 0 else x i) = x1_def x) → False := by
      intro E hnone hE
      by_cases hOut : E.output = 0
      · have hx := hE (fun _ => false)
        change (wiresFrom E.gates (List.ofFn fun i : Fin 9 => if i = 0 then true else false)).getD E.output false = false at hx
        rw [hOut, getD_wiresFrom_lt E.gates _ 0 (by simp)] at hx
        simp at hx
      · let x : Fin 9 → Bool := fun i => decide (i = 1)
        let y : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
        have hx := hE x
        have hy := hE y
        have hxf : x1_def x = false := by decide
        have hyf : x1_def y = true := by decide
        rw [hxf] at hx
        rw [hyf] at hy
        have hag : ∀ k, k ≠ 0 →
            (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i).getD k false =
            (List.ofFn fun i : Fin 9 => if i = 0 then !y 0 else y i).getD k false := by
          intro k hk0
          by_cases hk9 : k < 9
          · have hk1 : (⟨k, hk9⟩ : Fin 9) ≠ 0 := fun e => hk0 (congrArg Fin.val e)
            rw [List.getD_eq_getElem _ _ (by simp [hk9]), List.getElem_ofFn,
              List.getD_eq_getElem _ _ (by simp [hk9]), List.getElem_ofFn]
            simp only [hk1, ↓reduceIte]
            dsimp only [x, y]
            simp [Fin.ext_iff]; omega
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        have hind := (indep_wires E.gates hnone _ _ (by simp) hag).2 E.output hOut
        change (wiresFrom E.gates (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD E.output false = false at hx
        change (wiresFrom E.gates (List.ofFn fun i : Fin 9 => if i = 0 then !y 0 else y i)).getD E.output false = true at hy
        rw [hx, hy] at hind
        cases hind
    have hD_out_ne0 : D.output ≠ 0 := by
      intro hOut
      have hx := hD_neg (fun _ => false)
      change (wiresFrom D.gates (List.ofFn fun i : Fin 9 => if i = 0 then true else false)).getD D.output false = false at hx
      rw [hOut, getD_wiresFrom_lt D.gates _ 0 (by simp)] at hx
      simp at hx
    by_cases hZero : (D.gates.filter fun g => g.inputs.contains 0).length = 0
    · refine hZero_absurd D (fun g hg h0g => ?_) hD_neg
      have hm : g ∈ D.gates.filter (fun g => g.inputs.contains 0) :=
        List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr h0g⟩
      rw [List.eq_nil_of_length_eq_zero hZero] at hm
      exact List.not_mem_nil hm
    · have hOne : (D.gates.filter fun g => g.inputs.contains 0).length = 1 := by omega
      have split_unique : ∀ (l : List Gate), (l.filter fun g => g.inputs.contains 0).length = 1 →
          ∃ pre g0 suf, l = pre ++ g0 :: suf ∧ 0 ∈ g0.inputs ∧
            (∀ g ∈ pre, 0 ∉ g.inputs) ∧ (∀ g ∈ suf, 0 ∉ g.inputs) := by
        intro l
        induction l with
        | nil => simp
        | cons x xs ih =>
          intro hlen
          rw [List.filter_cons] at hlen
          by_cases hx : x.inputs.contains 0 = true
          · simp only [hx, ↓reduceIte, List.length_cons] at hlen
            have h0 : xs.filter (fun g => g.inputs.contains 0) = [] := List.eq_nil_of_length_eq_zero (by omega)
            refine ⟨[], x, xs, rfl, List.contains_iff_mem.mp hx, fun _ h => (List.not_mem_nil h).elim, fun g hg h0g => ?_⟩
            have hm : g ∈ xs.filter (fun g => g.inputs.contains 0) :=
              List.mem_filter.mpr ⟨hg, List.contains_iff_mem.mpr h0g⟩
            rw [h0] at hm; exact List.not_mem_nil hm
          · have hxf : x.inputs.contains 0 = false := Bool.eq_false_iff.mpr hx
            simp only [hxf, Bool.false_eq_true, ↓reduceIte] at hlen
            obtain ⟨pre, g0, suf, heq, h0g, hpre, hsuf⟩ := ih hlen
            refine ⟨x :: pre, g0, suf, by simp [heq], h0g, ?_, hsuf⟩
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hgp
            · intro h0x; exact hx (List.contains_iff_mem.mpr h0x)
            · exact hpre g hgp
      obtain ⟨pre, g0, suf, hD_eq, h0g0, hpre, hsuf⟩ := split_unique D.gates hOne
      have hg0_ok : g0.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g0.inputs.length ≤ 2 := by
        apply hDFan g0
        rw [hD_eq]
        exact List.mem_append_right pre List.mem_cons_self
      have hE_ok : ∀ g0' : Gate,
          (g0'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g0'.inputs.length ≤ 2) →
          FanInTwo ⟨pre ++ g0' :: suf, D.output⟩ := by
        intro g0' hg0' g hg
        simp only [List.mem_append, List.mem_cons] at hg
        rcases hg with hp | rfl | hs
        · exact hDFan g (by rw [hD_eq]; exact List.mem_append_left _ hp)
        · exact hg0'
        · exact hDFan g (by rw [hD_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs))
      have hE_sz : ∀ g0' : Gate, ({ gates := pre ++ g0' :: suf, output := D.output } : Circuit).size ≤ 14 := by
        intro g0'
        change (pre ++ g0' :: suf).length ≤ 14
        have : (pre ++ g0' :: suf).length = D.gates.length := by rw [hD_eq]; simp
        rw [this]
        exact hDSize
      have wiresFrom_app : ∀ (gs1 gs2 : List Gate) (w : List Bool),
          wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
        intro gs1 gs2 w; dsimp only [wiresFrom]; exact List.foldl_append
      have replace_same : ∀ g0' : Gate,
          (∀ x : Fin 9 → Bool,
            g0'.op.eval (g0'.inputs.map fun i => (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD i false) =
            g0.op.eval (g0.inputs.map fun i => (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD i false)) →
          ∀ x : Fin 9 → Bool,
            circuitFun 9 ⟨pre ++ g0' :: suf, D.output⟩ (fun i => if i = 0 then !x 0 else x i) = x1_def x := by
        intro g0' hsame x
        have he : Circuit.wires ⟨pre ++ g0' :: suf, D.output⟩
            (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i) =
            Circuit.wires D (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i) := by
          change wiresFrom (pre ++ g0' :: suf) _ = wiresFrom D.gates _
          rw [hD_eq, wiresFrom_app, wiresFrom_app]
          change wiresFrom (g0' :: suf) _ = wiresFrom (g0 :: suf) _
          have hs : step (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)) g0' =
              step (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)) g0 := by
            dsimp only [step]
            rw [hsame x]
          change wiresFrom suf (step _ g0') = wiresFrom suf (step _ g0)
          rw [hs]
        change (Circuit.wires ⟨pre ++ g0' :: suf, D.output⟩ _).getD D.output false = _
        rw [he]
        exact hD_neg x
      have replace_flip : ∀ g0' : Gate,
          (g0'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g0'.inputs.length ≤ 2) →
          (∀ x : Fin 9 → Bool,
            g0'.op.eval (g0'.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false) =
            g0.op.eval (g0.inputs.map fun i => (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD i false)) →
          False := by
        intro g0' hg0' hflip
        let E : Circuit := ⟨pre ++ g0' :: suf, D.output⟩
        have hE_std : circuitFun 9 E = x1_def := by
          funext x
          let wA := wiresFrom pre (List.ofFn x)
          let wB := wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)
          have hinit_k : ∀ k, k ≠ 0 → (List.ofFn x).getD k false =
              (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i).getD k false := by
            intro k hk0
            by_cases hk9 : k < 9
            · have hk1 : (⟨k, hk9⟩ : Fin 9) ≠ 0 := fun e => hk0 (congrArg Fin.val e)
              rw [List.getD_eq_getElem _ _ (by simp [hk9]), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp [hk9]), List.getElem_ofFn]
              simp [hk1]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have hpre_ind := indep_wires pre hpre (List.ofFn x)
            (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i) (by simp) hinit_k
          have hpre1 : wA.length = wB.length := hpre_ind.1
          have hmid_len : (step wA g0').length = (step wB g0).length := by
            simp [step, hpre1]
          have hmid_k : ∀ k, k ≠ 0 → (step wA g0').getD k false = (step wB g0).getD k false := by
            intro k hk0
            by_cases hkl : k < wA.length
            · dsimp only [step]
              rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (hpre1 ▸ hkl)]
              exact hpre_ind.2 k hk0
            · by_cases hke : k = wA.length
              · dsimp only [step]
                rw [hke, getD_snoc_eq, hpre1, getD_snoc_eq]
                exact hflip x
              · dsimp only [step]
                rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [hpre1]; omega)]
          have hsuf_ind := indep_wires suf hsuf (step wA g0') (step wB g0) hmid_len hmid_k
          have hE_eq : circuitFun 9 E x = circuitFun 9 D (fun i => if i = 0 then !x 0 else x i) := by
            change (wiresFrom (pre ++ g0' :: suf) (List.ofFn x)).getD D.output false =
              (wiresFrom D.gates (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD D.output false
            rw [hD_eq, wiresFrom_app, wiresFrom_app]
            exact hsuf_ind.2 D.output hD_out_ne0
          rw [hE_eq, hD_neg x]
        have h15 := hUnneg E (hE_ok g0' hg0') hE_std
        have h14 := hE_sz g0'
        dsimp only [E] at h15
        omega
      have wA_0 : ∀ x : Fin 9 → Bool, (wiresFrom pre (List.ofFn x)).getD 0 false = x 0 := by
        intro x
        rw [getD_wiresFrom_lt pre _ 0 (by simp)]
        simp
      have wB_0 : ∀ x : Fin 9 → Bool,
          (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD 0 false = !x 0 := by
        intro x
        rw [getD_wiresFrom_lt pre _ 0 (by simp)]
        simp
      have hNone_rep : ∀ g0' : Gate, 0 ∉ g0'.inputs →
          ∀ g ∈ ({ gates := pre ++ g0' :: suf, output := D.output } : Circuit).gates, 0 ∉ g.inputs := by
        intro g0' hg0' g hg
        simp only [List.mem_append, List.mem_cons] at hg
        rcases hg with hp | rfl | hs
        · exact hpre g hp
        · exact hg0'
        · exact hsuf g hs
      have hOne_rep : ∀ g0' : Gate, 0 ∈ g0'.inputs →
          (({ gates := pre ++ g0' :: suf, output := D.output } : Circuit).gates.filter
            fun g => g.inputs.contains 0).length = 1 := by
        intro g0' hg0'
        change ((pre ++ g0' :: suf).filter fun g => g.inputs.contains 0).length = 1
        have hp0 : pre.filter (fun g => g.inputs.contains 0) = [] := by
          rw [List.filter_eq_nil_iff]
          intro g hg hc
          exact hpre g hg (List.contains_iff_mem.mp (by simpa using hc))
        have hs0 : suf.filter (fun g => g.inputs.contains 0) = [] := by
          rw [List.filter_eq_nil_iff]
          intro g hg hc
          exact hsuf g hg (List.contains_iff_mem.mp (by simpa using hc))
        rw [List.filter_append, List.filter_cons, hp0, hs0, if_pos (List.contains_iff_mem.mpr hg0')]
        simp
      have hgate_at : ∀ g0' : Gate,
          NestedCover.gateAt ⟨pre ++ g0' :: suf, D.output⟩ pre.length = g0' := by
        intro g0'
        dsimp only [NestedCover.gateAt]
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
        simp
      have hj_lt : ∀ g0' : Gate, pre.length < ({ gates := pre ++ g0' :: suf, output := D.output } : Circuit).gates.length := by
        intro g0'; simp
      have eval_and : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
      have eval_or : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
      have eval_not : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
      have hop : g0.op = GateOp.and ∨ g0.op = GateOp.or ∨ g0.op = GateOp.not := hg0_ok.1
      have hlen2 : g0.inputs.length ≤ 2 := hg0_ok.2
      rcases hop with hop | hop | hop
      · -- g0.op = .and
        rcases hins : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hins] at h0g0; cases h0g0
        · rw [hins] at h0g0
          have ha : a = 0 := (by simpa using h0g0 : 0 = a).symm
          subst ha
          refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
          rw [hop, hins]
          simp only [List.map_cons, List.map_nil, eval_not, eval_and, List.headD_cons,
            List.all_cons, List.all_nil, id]
          rw [wA_0, wB_0]
          cases x 0 <;> rfl
        · rw [hins] at h0g0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0g0
          rcases h0g0 with rfl | rfl
          · by_cases hb0 : b = 0
            · subst hb0
              refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
              rw [hop, hins]
              simp only [List.map_cons, List.map_nil, eval_not, eval_and, List.headD_cons,
                List.all_cons, List.all_nil, id]
              rw [wA_0, wB_0]
              cases x 0 <;> rfl
            · by_cases hbw : b < 9 + pre.length
              · let E : Circuit := ⟨pre ++ ⟨GateOp.and, [0, b]⟩ :: suf, D.output⟩
                refine hBinAnd E pre.length b (hE_ok _ ⟨Or.inl rfl, by simp⟩) (hE_sz _)
                  (hOne_rep _ (by simp)) (hj_lt _) (Nat.pos_of_ne_zero hb0) hbw (hgate_at _)
                  (replace_same ⟨GateOp.and, [0, b]⟩ (fun x => by rw [hop, hins]))
              · refine hZero_absurd ⟨pre ++ ⟨GateOp.or, []⟩ :: suf, D.output⟩
                  (hNone_rep _ (by simp))
                  (replace_same ⟨GateOp.or, []⟩ (fun x => ?_))
                rw [hop, hins]
                have hdef : (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD b false = false :=
                  List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
                simp only [List.map_cons, List.map_nil, eval_or, eval_and, List.any_nil,
                  List.all_cons, List.all_nil, id]
                rw [hdef]
                simp
          · by_cases ha0 : a = 0
            · subst ha0
              refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
              rw [hop, hins]
              simp only [List.map_cons, List.map_nil, eval_not, eval_and, List.headD_cons,
                List.all_cons, List.all_nil, id]
              rw [wA_0, wB_0]
              cases x 0 <;> rfl
            · by_cases haw : a < 9 + pre.length
              · let E : Circuit := ⟨pre ++ ⟨GateOp.and, [0, a]⟩ :: suf, D.output⟩
                refine hBinAnd E pre.length a (hE_ok _ ⟨Or.inl rfl, by simp⟩) (hE_sz _)
                  (hOne_rep _ (by simp)) (hj_lt _) (Nat.pos_of_ne_zero ha0) haw (hgate_at _)
                  (replace_same ⟨GateOp.and, [0, a]⟩ (fun x => by
                    rw [hop, hins]
                    simp only [List.map_cons, List.map_nil, eval_and, List.all_cons, List.all_nil, id, Bool.and_true]
                    exact Bool.and_comm _ _))
              · refine hZero_absurd ⟨pre ++ ⟨GateOp.or, []⟩ :: suf, D.output⟩
                  (hNone_rep _ (by simp))
                  (replace_same ⟨GateOp.or, []⟩ (fun x => ?_))
                rw [hop, hins]
                have hdef : (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD a false = false :=
                  List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
                simp only [List.map_cons, List.map_nil, eval_or, eval_and, List.any_nil,
                  List.all_cons, List.all_nil, id]
                rw [hdef]
                simp
        · rw [hins] at hlen2; simp at hlen2
      · -- g0.op = .or
        rcases hins : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hins] at h0g0; cases h0g0
        · rw [hins] at h0g0
          have ha : a = 0 := (by simpa using h0g0 : 0 = a).symm
          subst ha
          refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
          rw [hop, hins]
          simp only [List.map_cons, List.map_nil, eval_not, eval_or, List.headD_cons,
            List.any_cons, List.any_nil, id]
          rw [wA_0, wB_0]
          cases x 0 <;> rfl
        · rw [hins] at h0g0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0g0
          rcases h0g0 with rfl | rfl
          · by_cases hb0 : b = 0
            · subst hb0
              refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
              rw [hop, hins]
              simp only [List.map_cons, List.map_nil, eval_not, eval_or, List.headD_cons,
                List.any_cons, List.any_nil, id]
              rw [wA_0, wB_0]
              cases x 0 <;> rfl
            · by_cases hbw : b < 9 + pre.length
              · let E : Circuit := ⟨pre ++ ⟨GateOp.or, [0, b]⟩ :: suf, D.output⟩
                refine hBinOr E pre.length b (hE_ok _ ⟨Or.inr (Or.inl rfl), by simp⟩) (hE_sz _)
                  (hOne_rep _ (by simp)) (hj_lt _) (Nat.pos_of_ne_zero hb0) hbw (hgate_at _)
                  (replace_same ⟨GateOp.or, [0, b]⟩ (fun x => by rw [hop, hins]))
              · refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
                rw [hop, hins]
                have hdef : (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD b false = false :=
                  List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
                simp only [List.map_cons, List.map_nil, eval_not, eval_or, List.headD_cons,
                  List.any_cons, List.any_nil, id]
                rw [wA_0, wB_0, hdef]
                cases x 0 <;> rfl
          · by_cases ha0 : a = 0
            · subst ha0
              refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
              rw [hop, hins]
              simp only [List.map_cons, List.map_nil, eval_not, eval_or, List.headD_cons,
                List.any_cons, List.any_nil, id]
              rw [wA_0, wB_0]
              cases x 0 <;> rfl
            · by_cases haw : a < 9 + pre.length
              · let E : Circuit := ⟨pre ++ ⟨GateOp.or, [0, a]⟩ :: suf, D.output⟩
                refine hBinOr E pre.length a (hE_ok _ ⟨Or.inr (Or.inl rfl), by simp⟩) (hE_sz _)
                  (hOne_rep _ (by simp)) (hj_lt _) (Nat.pos_of_ne_zero ha0) haw (hgate_at _)
                  (replace_same ⟨GateOp.or, [0, a]⟩ (fun x => by
                    rw [hop, hins]
                    simp only [List.map_cons, List.map_nil, eval_or, List.any_cons, List.any_nil, id, Bool.or_false]
                    exact Bool.or_comm _ _))
              · refine replace_flip ⟨GateOp.not, [0]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => ?_)
                rw [hop, hins]
                have hdef : (wiresFrom pre (List.ofFn fun i : Fin 9 => if i = 0 then !x 0 else x i)).getD a false = false :=
                  List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
                simp only [List.map_cons, List.map_nil, eval_not, eval_or, List.headD_cons,
                  List.any_cons, List.any_nil, id]
                rw [wA_0, wB_0, hdef]
                cases x 0 <;> rfl
        · rw [hins] at hlen2; simp at hlen2
      · -- g0.op = .not
        rcases hins : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · rw [hins] at h0g0; cases h0g0
        · rw [hins] at h0g0
          have ha : a = 0 := (by simpa using h0g0 : 0 = a).symm
          subst ha
          refine replace_flip ⟨GateOp.and, [0]⟩ ⟨Or.inl rfl, by simp⟩ (fun x => ?_)
          rw [hop, hins]
          simp only [List.map_cons, List.map_nil, eval_and, eval_not, List.headD_cons,
            List.all_cons, List.all_nil, id]
          rw [wA_0, wB_0]
          cases x 0 <;> rfl
        · rw [hins] at h0g0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0g0
          rcases h0g0 with rfl | rfl
          · refine replace_flip ⟨GateOp.and, [0]⟩ ⟨Or.inl rfl, by simp⟩ (fun x => ?_)
            rw [hop, hins]
            simp only [List.map_cons, List.map_nil, eval_and, eval_not, List.headD_cons,
              List.all_cons, List.all_nil, id]
            rw [wA_0, wB_0]
            cases x 0 <;> rfl
          · by_cases ha0 : a = 0
            · subst ha0
              refine replace_flip ⟨GateOp.and, [0]⟩ ⟨Or.inl rfl, by simp⟩ (fun x => ?_)
              rw [hop, hins]
              simp only [List.map_cons, List.map_nil, eval_and, eval_not, List.headD_cons,
                List.all_cons, List.all_nil, id]
              rw [wA_0, wB_0]
              cases x 0 <;> rfl
            · refine hZero_absurd ⟨pre ++ ⟨GateOp.not, [a]⟩ :: suf, D.output⟩
                (hNone_rep _ (by simp [Ne.symm ha0]))
                (replace_same ⟨GateOp.not, [a]⟩ (fun x => by rw [hop, hins]; rfl))
        · rw [hins] at hlen2; simp at hlen2
