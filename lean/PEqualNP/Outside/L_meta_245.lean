import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def tb (x : Fin 4 → Bool) (c : ℕ) : Bool := c.testBit (tableIndex x)

theorem idx4 (x : Fin 4 → Bool) : tableIndex x
    = (if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0)
      + (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) := by
  simp [tableIndex, Fin.sum_univ_four]

theorem idx_lt (x : Fin 4 → Bool) : tableIndex x < 16 := by
  rw [idx4]
  split_ifs <;> omega

theorem idx_surj (p : ℕ) (hp : p < 16) : ∃ x : Fin 4 → Bool, tableIndex x = p := by
  refine ⟨fun i => p.testBit i, ?_⟩
  rw [idx4]
  interval_cases p <;> decide

theorem tb_zero (x : Fin 4 → Bool) : tb x 0 = false := by simp [tb]

theorem tb_full (x : Fin 4 → Bool) : tb x 65535 = true := by
  have h : ∀ p : ℕ, p < 16 → Nat.testBit 65535 p = true := by
    intro p hp
    interval_cases p <;> rfl
  exact h _ (idx_lt x)

theorem tb_and (x : Fin 4 → Bool) (a b : ℕ) : tb x (a &&& b) = (tb x a && tb x b) := by
  simp [tb, Nat.testBit_and]

theorem tb_or (x : Fin 4 → Bool) (a b : ℕ) : tb x (a ||| b) = (tb x a || tb x b) := by
  simp [tb, Nat.testBit_or]

theorem tb_not (x : Fin 4 → Bool) (a : ℕ) : tb x (65535 ^^^ a) = !tb x a := by
  have h := tb_full x
  unfold tb at h ⊢
  rw [Nat.testBit_xor, h]
  simp

theorem code_inj (c t : ℕ) (hc : c < 65536) (ht : t < 65536)
    (h : ∀ x : Fin 4 → Bool, tb x c = tb x t) : c = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · obtain ⟨x, rfl⟩ := idx_surj i hi
    exact h x
  · have h8 : 65536 ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 16 ≤ i by omega)
      norm_num at this ⊢
      exact this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h8),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht h8)]

def gcode (ws : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 65535
  | GateOp.and, [i] => ws.getD i 0
  | GateOp.and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => ws.getD i 0
  | GateOp.or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | GateOp.not, [] => 65535
  | GateOp.not, i :: _ => 65535 ^^^ ws.getD i 0
  | _, _ => 0

def codesFrom (gs : List Gate) (ws : List ℕ) : List ℕ :=
  gs.foldl (fun ws g => ws ++ [gcode ws g]) ws

theorem getD_map_tb (x : Fin 4 → Bool) (ws : List ℕ) (i : ℕ) :
    (ws.map (tb x)).getD i false = tb x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), tb_zero]

theorem gate_step (x : Fin 4 → Bool) (ws : List ℕ) (g : Gate) (hg : Ok g) :
    g.op.eval (g.inputs.map fun i => (ws.map (tb x)).getD i false) = tb x (gcode ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map_tb]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => simp [gcode, GateOp.eval, tb_full]
    | [i], _ => simp [gcode, GateOp.eval]
    | [i, j], _ => simp [gcode, GateOp.eval, tb_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gcode, GateOp.eval, tb_zero]
    | [i], _ => simp [gcode, GateOp.eval]
    | [i, j], _ => simp [gcode, GateOp.eval, tb_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    match ins with
    | [] => simp [gcode, GateOp.eval, tb_full]
    | i :: _ => simp [gcode, GateOp.eval, tb_not]
  | mod m => simp at hop
  | maj => simp at hop

theorem wires_codes (x : Fin 4 → Bool) : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) →
    wiresFrom gs (ws.map (tb x)) = (codesFrom gs ws).map (tb x) := by
  intro gs
  induction gs with
  | nil => intro ws _; rfl
  | cons g gs ih =>
    intro ws hok
    have e : wiresFrom (g :: gs) (ws.map (tb x))
        = wiresFrom gs ((ws ++ [gcode ws g]).map (tb x)) := by
      show wiresFrom gs (ws.map (tb x)
        ++ [g.op.eval (g.inputs.map fun i => (ws.map (tb x)).getD i false)]) = _
      rw [List.map_append, List.map_singleton,
        gate_step x ws g (hok g List.mem_cons_self)]
    rw [e, ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]
    rfl

theorem getD_mem (ws : List ℕ) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

def Gen (vs : List ℕ) (c : ℕ) : Prop :=
  (∃ a ∈ vs, c = 65535 ^^^ a) ∨ ∃ a ∈ vs, ∃ b ∈ vs, c = a &&& b ∨ c = a ||| b

theorem gcode_gen (ws : List ℕ) (g : Gate) (hg : Ok g) :
    gcode ws g ∈ 0 :: ws ∨ Gen (0 :: ws) (gcode ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => exact Or.inr (Or.inl ⟨0, List.mem_cons_self, rfl⟩)
    | [i], _ => exact Or.inl (getD_mem ws i)
    | [i, j], _ =>
      exact Or.inr (Or.inr ⟨_, getD_mem ws i, _, getD_mem ws j, Or.inl rfl⟩)
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact Or.inl List.mem_cons_self
    | [i], _ => exact Or.inl (getD_mem ws i)
    | [i, j], _ =>
      exact Or.inr (Or.inr ⟨_, getD_mem ws i, _, getD_mem ws j, Or.inr rfl⟩)
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    match ins with
    | [] => exact Or.inr (Or.inl ⟨0, List.mem_cons_self, rfl⟩)
    | i :: _ => exact Or.inr (Or.inl ⟨_, getD_mem ws i, rfl⟩)
  | mod m => simp at hop
  | maj => simp at hop

theorem gen_lt (vs : List ℕ) (h : ∀ a ∈ vs, a < 65536) (c : ℕ) (hc : Gen vs c) : c < 65536 := by
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact Nat.xor_lt_two_pow (n := 16) (by norm_num) (h a ha)
  · exact Nat.and_lt_two_pow (n := 16) a (h b hb)
  · exact Nat.or_lt_two_pow (n := 16) (h a ha) (h b hb)

theorem codes_lt : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) → (∀ a ∈ ws, a < 65536) →
    ∀ a ∈ codesFrom gs ws, a < 65536 := by
  intro gs
  induction gs with
  | nil => intro ws _ h; exact h
  | cons g gs ih =>
    intro ws hok h
    have h0 : ∀ a ∈ 0 :: ws, a < 65536 := by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · norm_num
      · exact h a ha
    have hc : gcode ws g < 65536 := by
      rcases gcode_gen ws g (hok g List.mem_cons_self) with hm | hm
      · exact h0 _ hm
      · exact gen_lt _ h0 _ hm
    show ∀ a ∈ codesFrom gs (ws ++ [gcode ws g]), a < 65536
    refine ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.1 ha]; exact hc

def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => Nat.beq a b || memb a l

theorem memb_iff (a : ℕ) : ∀ l : List ℕ, memb a l = true ↔ a ∈ l
  | [] => by simp [memb]
  | b :: l => by simp [memb, memb_iff a l]

def pairs : List ℕ → List ℕ
  | [] => []
  | a :: l => l.flatMap (fun b => [a &&& b, a ||| b]) ++ pairs l

theorem mem_pairs : ∀ (l : List ℕ) (c : ℕ), c ∈ pairs l →
    ∃ a ∈ l, ∃ b ∈ l, c = a &&& b ∨ c = a ||| b
  | [], c, h => by simp [pairs] at h
  | a :: l, c, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨b, hb, hc⟩ := List.mem_flatMap.1 h
      refine ⟨a, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, ?_⟩
      simpa using hc
    · obtain ⟨a', ha', b, hb, hc⟩ := mem_pairs l c h
      exact ⟨a', List.mem_cons_of_mem _ ha', b, List.mem_cons_of_mem _ hb, hc⟩

theorem pairs_mem : ∀ (l : List ℕ) (a b : ℕ), a ∈ l → b ∈ l →
    a = b ∨ (a &&& b ∈ pairs l ∧ a ||| b ∈ pairs l)
  | [], a, b, ha, _ => by simp at ha
  | d :: l, a, b, ha, hb => by
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩)⟩
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩)⟩
      · rw [Nat.and_comm]; simp
      · rw [Nat.or_comm]; simp
    · rcases pairs_mem l a b ha' hb' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩

def cands (vs : List ℕ) : List ℕ := vs.map (fun a => 65535 ^^^ a) ++ pairs vs

theorem cands_gen (vs : List ℕ) (c : ℕ) (h : c ∈ cands vs) : Gen vs c := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr (mem_pairs vs c h)

theorem gen_cands (vs : List ℕ) (c : ℕ) (h : Gen vs c) : c ∈ vs ∨ c ∈ cands vs := by
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hc⟩
  · exact Or.inr (List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  · rcases pairs_mem vs a b ha hb with rfl | ⟨h1, h2⟩
    · left
      rcases hc with rfl | rfl
      · rw [Nat.and_self]; exact ha
      · rw [Nat.or_self]; exact ha
    · right
      rcases hc with rfl | rfl
      · exact List.mem_append_right _ h1
      · exact List.mem_append_right _ h2

theorem gen_mono (vs vs' : List ℕ) (h : ∀ a ∈ vs, a ∈ vs') (c : ℕ) (hc : Gen vs c) :
    Gen vs' c := by
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hc⟩
  · exact Or.inl ⟨a, h a ha, rfl⟩
  · exact Or.inr ⟨a, h a ha, b, h b hb, hc⟩

def fnd (ts : List ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | k + 1, vs => (cands vs).any fun c =>
      memb c ts || (match k with
        | 0 => false
        | _ => !memb c vs && fnd ts k (c :: vs))

theorem fnd_succ (ts : List ℕ) (k : ℕ) (vs : List ℕ) : fnd ts (k + 1) vs = true ↔
    ∃ c ∈ cands vs, c ∈ ts ∨ (c ∉ vs ∧ fnd ts k (c :: vs) = true) := by
  cases k with
  | zero => simp [fnd, memb_iff]
  | succ k =>
    rw [fnd]
    simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      memb_iff, ← Bool.not_eq_true]

def Hit (ts vs : List ℕ) : Prop := ∃ t ∈ ts, t ∈ vs

theorem fnd_mono (ts : List ℕ) : ∀ (k : ℕ) (vs vs' : List ℕ) (k' : ℕ), (∀ a ∈ vs, a ∈ vs') →
    k ≤ k' → fnd ts k vs = true → Hit ts vs' ∨ fnd ts k' vs' = true := by
  intro k
  induction k with
  | zero => intro vs vs' k' _ _ h; simp [fnd] at h
  | succ k ih =>
    intro vs vs' k' hsub hk h
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    obtain ⟨c, hc, hcase⟩ := (fnd_succ ts k vs).1 h
    have hgen : Gen vs' c := gen_mono vs vs' hsub c (cands_gen vs c hc)
    by_cases hin : c ∈ vs'
    · rcases hcase with ht | ⟨_, hf⟩
      · exact Or.inl ⟨c, ht, hin⟩
      · refine ih (c :: vs) vs' (k' + 1) ?_ (by omega) hf
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hin
        · exact hsub a ha
    · have hc' : c ∈ cands vs' := (gen_cands vs' c hgen).resolve_left hin
      rcases hcase with ht | ⟨_, hf⟩
      · exact Or.inr ((fnd_succ ts k' vs').2 ⟨c, hc', Or.inl ht⟩)
      · have := ih (c :: vs) (c :: vs') k' (by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub a ha)) (by omega) hf
        rcases this with ⟨t, ht, htv⟩ | hf'
        · rcases List.mem_cons.1 htv with rfl | htv
          · exact Or.inr ((fnd_succ ts k' vs').2 ⟨t, hc', Or.inl ht⟩)
          · exact Or.inl ⟨t, ht, htv⟩
        · exact Or.inr ((fnd_succ ts k' vs').2 ⟨c, hc', Or.inr ⟨hin, hf'⟩⟩)

theorem search_sound (ts : List ℕ) : ∀ (gs : List Gate) (ws : List ℕ) (k o : ℕ),
    (∀ g ∈ gs, Ok g) → gs.length ≤ k → (codesFrom gs ws).getD o 0 ∈ ts →
    Hit ts (0 :: ws) ∨ fnd ts k (0 :: ws) = true := by
  intro gs
  induction gs with
  | nil =>
    intro ws k o _ _ h
    exact Or.inl ⟨_, h, getD_mem ws o⟩
  | cons g gs ih =>
    intro ws k o hok hk h
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    set c := gcode ws g with hcdef
    have h1 := ih (ws ++ [c]) k o (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp at hk; omega) h
    have hsub : ∀ a ∈ 0 :: (ws ++ [c]), a ∈ c :: 0 :: ws := by
      intro a ha
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
      tauto
    have h2 : Hit ts (c :: 0 :: ws) ∨ fnd ts k (c :: 0 :: ws) = true := by
      rcases h1 with ⟨t, ht, htv⟩ | hf
      · exact Or.inl ⟨t, ht, hsub t htv⟩
      · exact fnd_mono ts k _ _ k hsub le_rfl hf
    by_cases hin : c ∈ 0 :: ws
    · have hsub' : ∀ a ∈ c :: 0 :: ws, a ∈ 0 :: ws := by
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hin
        · exact ha
      rcases h2 with ⟨t, ht, htv⟩ | hf
      · exact Or.inl ⟨t, ht, hsub' t htv⟩
      · exact fnd_mono ts k _ _ (k + 1) hsub' (by omega) hf
    · have hgen : Gen (0 :: ws) c :=
        (gcode_gen ws g (hok g List.mem_cons_self)).resolve_left hin
      have hc' : c ∈ cands (0 :: ws) := (gen_cands _ c hgen).resolve_left hin
      rcases h2 with ⟨t, ht, htv⟩ | hf
      · rcases List.mem_cons.1 htv with he | htv
        · exact Or.inr ((fnd_succ ts k _).2 ⟨c, hc', Or.inl (he ▸ ht)⟩)
        · exact Or.inl ⟨t, ht, htv⟩
      · exact Or.inr ((fnd_succ ts k _).2 ⟨c, hc', Or.inr ⟨hin, hf⟩⟩)

def inputs : List ℕ := [43690, 52428, 61680, 65280]

theorem ofFn_codes (x : Fin 4 → Bool) : List.ofFn x = inputs.map (tb x) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hx]
  simp only [inputs, List.map_cons, List.map_nil, tb, idx4]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

def path4 (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

theorem path4_code (x : Fin 4 → Bool) : path4 x = tb x 63688 := by
  simp only [path4, tb, idx4]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

theorem search_empty : fnd [63688] 3 (0 :: inputs) = false := by decide +kernel

theorem eval_code (C : Circuit) (ok : ∀ g ∈ C.gates, Ok g) (x : Fin 4 → Bool) :
    C.eval (List.ofFn x) = tb x ((codesFrom C.gates inputs).getD C.output 0) := by
  show (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
  rw [ofFn_codes, wires_codes x C.gates inputs ok, getD_map_tb]

theorem lower (D : Circuit) (ok : ∀ g ∈ D.gates, Ok g) (hsz : D.gates.length ≤ 3)
    (hev : ∀ x : Fin 4 → Bool, D.eval (List.ofFn x) = path4 x) : False := by
  have hlt : (codesFrom D.gates inputs).getD D.output 0 < 65536 := by
    have hm := getD_mem (codesFrom D.gates inputs) D.output
    rcases List.mem_cons.1 hm with e | hm
    · rw [e]; norm_num
    · exact codes_lt D.gates inputs ok (by decide) _ hm
  have e : (codesFrom D.gates inputs).getD D.output 0 = 63688 := by
    apply code_inj _ _ hlt (by norm_num)
    intro x
    rw [← eval_code D ok x, hev x, path4_code]
  have := search_sound [63688] D.gates inputs 3 D.output ok hsz
    (by rw [e]; exact List.mem_singleton.2 rfl)
  rcases this with hh | hf
  · revert hh
    unfold Hit
    decide
  · rw [search_empty] at hf
    exact absurd hf (by decide)

def pathC : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩

theorem pathC_ok : ∀ g ∈ pathC.gates, Ok g := by
  intro g hg
  simp only [pathC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]

theorem pathC_fun : circuitFun 4 pathC = path4 := by
  funext x
  show pathC.eval (List.ofFn x) = path4 x
  rw [eval_code pathC pathC_ok x, path4_code]
  rfl

theorem pathC_min : IsMinimalCircuit 4 pathC := by
  refine ⟨pathC_ok, fun D hD heq => ?_⟩
  by_contra hlt
  apply lower D hD (by simp only [Circuit.size, pathC] at hlt; simp at hlt; omega)
  intro x
  have := congrFun heq x
  rw [pathC_fun] at this
  exact this

end PEqualNP.Outside.L_meta_245

theorem PEqualNP.Outside.L_meta_245 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩], 7⟩ → PEqualNP.MetaComplexity.IsMinimalCircuit 4 C ∧ PEqualNP.MetaComplexity.circuitFun 4 C = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) ∧ C.gates[3]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩ := by
  intro C hC
  subst hC
  exact ⟨PEqualNP.Outside.L_meta_245.pathC_min, PEqualNP.Outside.L_meta_245.pathC_fun, rfl⟩
