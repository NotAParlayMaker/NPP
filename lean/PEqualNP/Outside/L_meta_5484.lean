import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5484

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 5) ||
  (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)

def fM (m : ℕ) : Bool :=
  (m.testBit 0 && m.testBit 1) || (m.testBit 0 && m.testBit 3) ||
  (m.testBit 0 && m.testBit 5) || (m.testBit 1 && m.testBit 2) ||
  (m.testBit 1 && m.testBit 4) || (m.testBit 2 && m.testBit 3)

def maskToFun (m : Fin 64) (i : Fin 6) : Bool := m.val.testBit i.val

def funToMaskVal (x : Fin 6 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)

lemma funToMaskVal_lt (x : Fin 6 → Bool) : funToMaskVal x < 64 := by
  unfold funToMaskVal
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide

def funToMask (x : Fin 6 → Bool) : Fin 64 := ⟨funToMaskVal x, funToMaskVal_lt x⟩

lemma maskToFun_funToMask_aux (b0 b1 b2 b3 b4 b5 : Bool) (i : Fin 6) :
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
     (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)).testBit i.val =
    match i.val with
    | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5 := by
  revert b0 b1 b2 b3 b4 b5 i; decide

lemma maskToFun_funToMask (x : Fin 6 → Bool) (i : Fin 6) :
    maskToFun (funToMask x) i = x i := by
  change (funToMaskVal x).testBit i.val = x i
  unfold funToMaskVal
  rw [maskToFun_funToMask_aux (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i]
  fin_cases i <;> rfl

lemma target_maskToFun (m : Fin 64) : target (maskToFun m) = fM m.val := rfl

lemma target_eq_fM (x : Fin 6 → Bool) : target x = fM (funToMask x).val := by
  have h : x = maskToFun (funToMask x) := funext fun i => (maskToFun_funToMask x i).symm
  conv_lhs => rw [h]
  rfl

def setBitVal (m : ℕ) (i : Fin 6) (b : Bool) : ℕ :=
  if b then m ||| (1 <<< i.val) else m &&& (63 ^^^ (1 <<< i.val))

lemma setBitVal_lt (m : Fin 64) (i : Fin 6) (b : Bool) : setBitVal m.val i b < 64 := by
  revert m i b; decide

def set2M (m : Fin 64) (a b : Fin 6) (u v : Bool) : Fin 64 :=
  ⟨setBitVal (setBitVal m.val a u) b v, by
    have h1 := setBitVal_lt m a u
    exact setBitVal_lt ⟨setBitVal m.val a u, h1⟩ b v⟩

lemma maskToFun_set2M_other (m : Fin 64) (a b i : Fin 6) (u v : Bool)
    (hia : i ≠ a) (hib : i ≠ b) :
    maskToFun (set2M m a b u v) i = maskToFun m i := by
  revert m a b i u v hia hib; decide

lemma maskToFun_set2M_a (m : Fin 64) (a b : Fin 6) (u v : Bool) (hab : a ≠ b) :
    maskToFun (set2M m a b u v) a = u := by
  revert m a b u v hab; decide

lemma maskToFun_set2M_b (m : Fin 64) (a b : Fin 6) (u v : Bool) :
    maskToFun (set2M m a b u v) b = v := by
  revert m a b u v; decide

lemma target_three_cofactors_aux :
    ∀ a b : Fin 6, a ≠ b →
      ∃ p1 p2 p3 : Bool × Bool,
        (∃ m : Fin 64, fM (set2M m a b p1.1 p1.2).val ≠ fM (set2M m a b p2.1 p2.2).val) ∧
        (∃ m : Fin 64, fM (set2M m a b p1.1 p1.2).val ≠ fM (set2M m a b p3.1 p3.2).val) ∧
        (∃ m : Fin 64, fM (set2M m a b p2.1 p2.2).val ≠ fM (set2M m a b p3.1 p3.2).val) := by
  decide

lemma target_three_cofactors (a b : Fin 6) (hab : a ≠ b) (g : Bool → Bool → Bool) :
    ∃ x y : Fin 6 → Bool,
      (∀ i : Fin 6, i ≠ a → i ≠ b → x i = y i) ∧
      g (x a) (x b) = g (y a) (y b) ∧
      target x ≠ target y := by
  obtain ⟨p1, p2, p3, h12, h13, h23⟩ := target_three_cofactors_aux a b hab
  have hpair : ∃ q1 q2 : Bool × Bool, g q1.1 q1.2 = g q2.1 q2.2 ∧
      ∃ m : Fin 64, fM (set2M m a b q1.1 q1.2).val ≠ fM (set2M m a b q2.1 q2.2).val := by
    cases hg1 : g p1.1 p1.2 <;> cases hg2 : g p2.1 p2.2 <;> cases hg3 : g p3.1 p3.2
    · exact ⟨p1, p2, by rw [hg1, hg2], h12⟩
    · exact ⟨p1, p2, by rw [hg1, hg2], h12⟩
    · exact ⟨p1, p3, by rw [hg1, hg3], h13⟩
    · exact ⟨p2, p3, by rw [hg2, hg3], h23⟩
    · exact ⟨p2, p3, by rw [hg2, hg3], h23⟩
    · exact ⟨p1, p3, by rw [hg1, hg3], h13⟩
    · exact ⟨p1, p2, by rw [hg1, hg2], h12⟩
    · exact ⟨p1, p2, by rw [hg1, hg2], h12⟩
  obtain ⟨q1, q2, hgeq, m, hne⟩ := hpair
  refine ⟨maskToFun (set2M m a b q1.1 q1.2), maskToFun (set2M m a b q2.1 q2.2), ?_, ?_, ?_⟩
  · intro i hia hib
    rw [maskToFun_set2M_other m a b i q1.1 q1.2 hia hib,
        maskToFun_set2M_other m a b i q2.1 q2.2 hia hib]
  · rw [maskToFun_set2M_a m a b q1.1 q1.2 hab, maskToFun_set2M_b m a b q1.1 q1.2,
        maskToFun_set2M_a m a b q2.1 q2.2 hab, maskToFun_set2M_b m a b q2.1 q2.2]
    exact hgeq
  · rw [target_maskToFun, target_maskToFun]
    exact hne

lemma target_matters (i : Fin 6) :
    ∃ x y : Fin 6 → Bool, (∀ j : Fin 6, j ≠ i → x j = y j) ∧ target x ≠ target y := by
  fin_cases i
  · exact ⟨maskToFun 32, maskToFun 33, by decide, by decide⟩
  · exact ⟨maskToFun 16, maskToFun 18, by decide, by decide⟩
  · exact ⟨maskToFun 8, maskToFun 12, by decide, by decide⟩
  · exact ⟨maskToFun 4, maskToFun 12, by decide, by decide⟩
  · exact ⟨maskToFun 2, maskToFun 18, by decide, by decide⟩
  · exact ⟨maskToFun 1, maskToFun 33, by decide, by decide⟩

lemma target_singleton_false (i : Fin 6) : target (fun j => decide (j = i)) = false := by
  fin_cases i <;> rfl

lemma target_all_true : target (fun _ => true) = true := rfl

lemma target_all_false : target (fun _ => false) = false := rfl

/-! ## Wire evaluation and effective inputs -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wval (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma getD_append_left (u v : List Bool) (i : ℕ) (hi : i < u.length) :
    (u ++ v).getD i false = u.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (u v : List Bool) (i : ℕ) (hi : u.length ≤ i) :
    (u ++ v).getD i false = v.getD (i - u.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge (u : List Bool) (i : ℕ) (hi : u.length ≤ i) : u.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma foldl_step_ext (gs : List Gate) (w : List Bool) :
    ∃ ext : List Bool, ext.length = gs.length ∧ gs.foldl step w = w ++ ext := by
  induction gs generalizing w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    obtain ⟨ext, hlen, heq⟩ := ih (step w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ ext, ?_, ?_⟩
    · simp [hlen]
    · rw [heq]; dsimp only [step]; rw [List.append_assoc]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨ext, hlen, heq⟩ := foldl_step_ext gs w
  rw [heq, List.length_append, hlen]

lemma wval_lt (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) (hw : w < 6) :
    wval C x w = x ⟨w, hw⟩ := by
  unfold wval Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD w false = x ⟨w, hw⟩
  obtain ⟨ext, _, heq⟩ := foldl_step_ext C.gates (List.ofFn x)
  rw [heq, getD_append_left _ _ w (by rw [List.length_ofFn]; exact hw)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hw]

lemma wval_ge (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) (hw : 6 + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD w false = false
  apply getD_ge
  rw [foldl_step_len, List.length_ofFn]
  exact hw

lemma wval_gate (C : Circuit) (x : Fin 6 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (6 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 6 + j then wval C x i else false) := by
  unfold wval Circuit.wires
  change (C.gates.foldl step (List.ofFn x)).getD (6 + j) false = _
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  let pref := (C.gates.take j).foldl step (List.ofFn x)
  have hpref_len : pref.length = 6 + j := by
    dsimp only [pref]
    rw [foldl_step_len, List.length_ofFn, List.length_take_of_le (Nat.le_of_lt hj)]
  have htot : C.gates.foldl step (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl step (step pref C.gates[j]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  obtain ⟨ext, _, hext⟩ := foldl_step_ext (C.gates.drop (j + 1)) (step pref C.gates[j])
  have hpref_eq : ∀ i, i < 6 + j → pref.getD i false = (C.gates.foldl step (List.ofFn x)).getD i false := by
    intro i hi
    rw [htot, hext]
    dsimp only [step]
    rw [List.append_assoc, getD_append_left pref _ i (by omega)]
  have hmap : (C.gates[j]).inputs.map (fun i => pref.getD i false) =
      (C.gates[j]).inputs.map (fun i => if i < 6 + j then (C.gates.foldl step (List.ofFn x)).getD i false else false) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < 6 + j
    · simp only [hi, ↓reduceIte]
      exact hpref_eq i hi
    · simp only [hi, ↓reduceIte]
      exact getD_ge pref i (by omega)
  rw [htot, hext]
  dsimp only [step]
  rw [getD_append_left (pref ++ _) ext (6 + j) (by rw [List.length_append, List.length_singleton]; omega),
      getD_append_right pref _ (6 + j) (by omega)]
  have hzero : 6 + j - pref.length = 0 := by omega
  rw [hzero]
  change (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => pref.getD i false) =
    (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < 6 + j then (C.gates.foldl step (List.ofFn x)).getD i false else false)
  rw [hmap]

def effInputsGate (g : Gate) (j : ℕ) : List ℕ :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => []
    | a :: _ => if a < 6 + j then [a] else []
  | GateOp.and =>
    match g.inputs with
    | [] => []
    | [a] => if a < 6 + j then [a] else []
    | [a, b] =>
      if a < 6 + j then
        if b < 6 + j then
          if a = b then [a] else [a, b]
        else [a]
      else
        if b < 6 + j then [b] else []
    | _ => []
  | GateOp.or =>
    match g.inputs with
    | [] => []
    | [a] => if a < 6 + j then [a] else []
    | [a, b] =>
      if a < 6 + j then
        if b < 6 + j then
          if a = b then [a] else [a, b]
        else [a]
      else
        if b < 6 + j then [b] else []
    | _ => []
  | _ => []

def effInputs0 (C : Circuit) (j : ℕ) : List ℕ :=
  if hj : j < C.gates.length then effInputsGate C.gates[j] j else []

lemma effInputsGate_nodup (g : Gate) (j : ℕ) : (effInputsGate g j).Nodup := by
  cases g with
  | mk op ins =>
    cases op <;> unfold effInputsGate <;> dsimp only
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only
      · exact List.nodup_nil
      · split_ifs <;> simp
      · split_ifs <;> simp_all
      · exact List.nodup_nil
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only
      · exact List.nodup_nil
      · split_ifs <;> simp
      · split_ifs <;> simp_all
      · exact List.nodup_nil
    · rcases ins with _ | ⟨a, _⟩ <;> dsimp only
      · exact List.nodup_nil
      · split_ifs <;> simp
    · exact List.nodup_nil
    · exact List.nodup_nil

lemma effInputs0_nodup (C : Circuit) (j : ℕ) : (effInputs0 C j).Nodup := by
  unfold effInputs0
  split_ifs with hj
  · exact effInputsGate_nodup C.gates[j] j
  · exact List.nodup_nil

lemma effInputsGate_lt (g : Gate) (j u : ℕ) (hu : u ∈ effInputsGate g j) : u < 6 + j := by
  cases g with
  | mk op ins =>
    cases op <;> unfold effInputsGate at hu <;> dsimp only at hu
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only at hu
      · simp at hu
      · split_ifs at hu <;> simp_all
      · split_ifs at hu <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;> omega
      · simp at hu
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only at hu
      · simp at hu
      · split_ifs at hu <;> simp_all
      · split_ifs at hu <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;> omega
      · simp at hu
    · rcases ins with _ | ⟨a, _⟩ <;> dsimp only at hu
      · simp at hu
      · split_ifs at hu <;> simp_all
    · simp at hu
    · simp at hu

lemma effInputs0_lt (C : Circuit) (j u : ℕ) (hu : u ∈ effInputs0 C j) : u < 6 + j := by
  unfold effInputs0 at hu
  split_ifs at hu with hj
  · exact effInputsGate_lt C.gates[j] j u hu
  · simp at hu

lemma effInputsGate_len_le (g : Gate) (j : ℕ) : (effInputsGate g j).length ≤ 2 := by
  cases g with
  | mk op ins =>
    cases op <;> unfold effInputsGate <;> dsimp only
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only
      · simp
      · split_ifs <;> simp
      · split_ifs <;> simp
      · simp
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only
      · simp
      · split_ifs <;> simp
      · split_ifs <;> simp
      · simp
    · rcases ins with _ | ⟨a, _⟩ <;> dsimp only
      · simp
      · split_ifs <;> simp
    · simp
    · simp

lemma effInputs0_len_le (C : Circuit) (j : ℕ) : (effInputs0 C j).length ≤ 2 := by
  unfold effInputs0
  split_ifs with hj
  · exact effInputsGate_len_le C.gates[j] j
  · simp

lemma effInputsGate_congr (g : Gate) (j : ℕ) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (fx fy : ℕ → Bool)
    (h : ∀ u ∈ effInputsGate g j, fx u = fy u) :
    g.op.eval (g.inputs.map fun i => if i < 6 + j then fx i else false) =
    g.op.eval (g.inputs.map fun i => if i < 6 + j then fy i else false) := by
  cases g with
  | mk op ins =>
    dsimp only at hop hlen ⊢
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · rfl
      · unfold effInputsGate at h; dsimp only at h
        simp only [List.map_cons, List.map_nil]
        by_cases ha : a < 6 + j
        · simp only [ha, ↓reduceIte] at h ⊢; rw [h a (by simp)]
        · simp only [ha, ↓reduceIte]
      · unfold effInputsGate at h; dsimp only at h
        simp only [List.map_cons, List.map_nil]
        by_cases ha : a < 6 + j <;> by_cases hb : b < 6 + j
        · simp only [ha, hb, ↓reduceIte] at h ⊢
          by_cases hab : a = b
          · subst hab; simp only [↓reduceIte] at h ⊢; rw [h a (by simp)]
          · simp only [hab, ↓reduceIte] at h ⊢; rw [h a (by simp), h b (by simp)]
        · simp only [ha, hb, ↓reduceIte] at h ⊢; rw [h a (by simp)]
        · simp only [ha, hb, ↓reduceIte] at h ⊢; rw [h b (by simp)]
        · simp only [ha, hb, ↓reduceIte]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · rfl
      · unfold effInputsGate at h; dsimp only at h
        simp only [List.map_cons, List.map_nil]
        by_cases ha : a < 6 + j
        · simp only [ha, ↓reduceIte] at h ⊢; rw [h a (by simp)]
        · simp only [ha, ↓reduceIte]
      · unfold effInputsGate at h; dsimp only at h
        simp only [List.map_cons, List.map_nil]
        by_cases ha : a < 6 + j <;> by_cases hb : b < 6 + j
        · simp only [ha, hb, ↓reduceIte] at h ⊢
          by_cases hab : a = b
          · subst hab; simp only [↓reduceIte] at h ⊢; rw [h a (by simp)]
          · simp only [hab, ↓reduceIte] at h ⊢; rw [h a (by simp), h b (by simp)]
        · simp only [ha, hb, ↓reduceIte] at h ⊢; rw [h a (by simp)]
        · simp only [ha, hb, ↓reduceIte] at h ⊢; rw [h b (by simp)]
        · simp only [ha, hb, ↓reduceIte]
      · simp at hlen
    · rcases ins with _ | ⟨a, _⟩
      · rfl
      · unfold effInputsGate at h; dsimp only at h
        simp only [List.map_cons, GateOp.eval, List.headD_cons]
        by_cases ha : a < 6 + j
        · simp only [ha, ↓reduceIte] at h ⊢; rw [h a (by simp)]
        · simp only [ha, ↓reduceIte]

lemma effInputs0_congr (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (x y : Fin 6 → Bool) (h : ∀ u ∈ effInputs0 C j, wval C x u = wval C y u) :
    wval C x (6 + j) = wval C y (6 + j) := by
  rw [wval_gate C x j hj, wval_gate C y j hj]
  obtain ⟨hop, hlen⟩ := hF C.gates[j] (List.getElem_mem hj)
  apply effInputsGate_congr C.gates[j] j hop hlen
  intro u hu
  apply h u
  unfold effInputs0
  simp only [hj, ↓reduceDIte]
  exact hu

lemma effInputsGate_len2 (g : Gate) (j : ℕ)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (h2 : (effInputsGate g j).length = 2) :
    ∃ a b : ℕ, effInputsGate g j = [a, b] ∧ a ≠ b ∧ a < 6 + j ∧ b < 6 + j ∧
      g.inputs = [a, b] ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  cases g with
  | mk op ins =>
    dsimp only at hop hlen ⊢
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [effInputsGate] at h2
      · unfold effInputsGate at h2; dsimp only at h2; split_ifs at h2 <;> simp_all
      · unfold effInputsGate at h2 ⊢; dsimp only at h2 ⊢
        split_ifs at h2 with ha hb hab
        · simp at h2
        · refine ⟨a, b, ?_, hab, ha, hb, rfl, Or.inl rfl⟩
          simp [ha, hb, hab]
        · simp at h2
        · simp at h2
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [effInputsGate] at h2
      · unfold effInputsGate at h2; dsimp only at h2; split_ifs at h2 <;> simp_all
      · unfold effInputsGate at h2 ⊢; dsimp only at h2 ⊢
        split_ifs at h2 with ha hb hab
        · simp at h2
        · refine ⟨a, b, ?_, hab, ha, hb, rfl, Or.inr rfl⟩
          simp [ha, hb, hab]
        · simp at h2
        · simp at h2
      · simp at hlen
    · rcases ins with _ | ⟨a, _⟩
      · simp [effInputsGate] at h2
      · unfold effInputsGate at h2; dsimp only at h2; split_ifs at h2 <;> simp_all

lemma effInputs0_len2 (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (h2 : (effInputs0 C j).length = 2) :
    ∃ a b : ℕ, effInputs0 C j = [a, b] ∧ a ≠ b ∧ a < 6 + j ∧ b < 6 + j ∧
      (((C.gates[j]).op = GateOp.and ∧ ∀ x, wval C x (6 + j) = (wval C x a && wval C x b)) ∨
       ((C.gates[j]).op = GateOp.or ∧ ∀ x, wval C x (6 + j) = (wval C x a || wval C x b))) := by
  obtain ⟨hop, hlen⟩ := hF C.gates[j] (List.getElem_mem hj)
  have h2' : (effInputsGate C.gates[j] j).length = 2 := by
    unfold effInputs0 at h2; simp only [hj, ↓reduceDIte] at h2; exact h2
  obtain ⟨a, b, heq, hab, ha, hb, hins, hcop⟩ := effInputsGate_len2 C.gates[j] j hop hlen h2'
  refine ⟨a, b, ?_, hab, ha, hb, ?_⟩
  · unfold effInputs0; simp only [hj, ↓reduceDIte]; exact heq
  · rcases hcop with hcop | hcop
    · refine Or.inl ⟨hcop, fun x => ?_⟩
      rw [wval_gate C x j hj, hcop, hins]
      simp [ha, hb, GateOp.eval]
    · refine Or.inr ⟨hcop, fun x => ?_⟩
      rw [wval_gate C x j hj, hcop, hins]
      simp [ha, hb, GateOp.eval]

/-! ## Backward reachability `reach` -/

def reach (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h6 : w < 6 then {w}
  else if hm : w < 6 + C.gates.length then
    insert w ((effInputs0 C (w - 6)).attach.foldr
      (fun ⟨u, hu⟩ acc =>
        have : u < w := by
          have hlt := effInputs0_lt C (w - 6) u hu
          omega
        reach C u ∪ acc)
      ∅)
  else ∅
termination_by w

lemma reach_lt6 (C : Circuit) (w : ℕ) (hw : w < 6) : reach C w = {w} := by
  rw [reach]; simp [hw]

lemma reach_gate (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    reach C (6 + j) = insert (6 + j) ((effInputs0 C j).toFinset.biUnion (reach C)) := by
  rw [reach]
  have h1 : ¬ 6 + j < 6 := by omega
  have h2 : 6 + j < 6 + C.gates.length := by omega
  simp only [h1, h2, ↓reduceDIte]
  congr 1
  have hfold : ∀ (l : List ℕ),
      l.attach.foldr (fun x acc => reach C x.1 ∪ acc) ∅ = l.toFinset.biUnion (reach C) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.attach_cons, List.foldr_cons, List.foldr_map, List.toFinset_cons,
                 Finset.biUnion_insert]
      rw [ih]
  rw [hfold (effInputs0 C (6 + j - 6)), Nat.add_sub_cancel_left]

lemma reach_ge (C : Circuit) (w : ℕ) (hw : 6 + C.gates.length ≤ w) : reach C w = ∅ := by
  rw [reach]
  have h1 : ¬ w < 6 := by omega
  have h2 : ¬ w < 6 + C.gates.length := by omega
  simp [h1, h2]

lemma mem_reach_le (C : Circuit) (w u : ℕ) (hu : u ∈ reach C w) : u ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 6
    · rw [reach_lt6 C w h1, Finset.mem_singleton] at hu; omega
    · by_cases h2 : w < 6 + C.gates.length
      · have hw : w = 6 + (w - 6) := by omega
        rw [hw, reach_gate C (w - 6) (by omega), Finset.mem_insert, Finset.mem_biUnion] at hu
        rcases hu with rfl | ⟨v, hv, huv⟩
        · omega
        · rw [List.mem_toFinset] at hv
          have hvlt : v < w := by have := effInputs0_lt C (w - 6) v hv; omega
          have hle := ih v hvlt huv
          omega
      · rw [reach_ge C w (by omega)] at hu; simp at hu

lemma mem_reach_self (C : Circuit) (w : ℕ) (hw : w < 6 + C.gates.length) : w ∈ reach C w := by
  by_cases h1 : w < 6
  · rw [reach_lt6 C w h1]; simp
  · have h : w = 6 + (w - 6) := by omega
    rw [h, reach_gate C (w - 6) (by omega)]; simp

lemma reach_subset_of_effInput (C : Circuit) (j u : ℕ) (hj : j < C.gates.length)
    (hu : u ∈ effInputs0 C j) : reach C u ⊆ reach C (6 + j) := by
  intro v hv
  rw [reach_gate C j hj, Finset.mem_insert, Finset.mem_biUnion]
  exact Or.inr ⟨u, List.mem_toFinset.mpr hu, hv⟩

lemma reach_trans (C : Circuit) (w v u : ℕ) (hv : v ∈ reach C w) (hu : u ∈ reach C v) :
    u ∈ reach C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 6
    · rw [reach_lt6 C w h1, Finset.mem_singleton] at hv; subst hv; exact hu
    · by_cases h2 : w < 6 + C.gates.length
      · have hw : w = 6 + (w - 6) := by omega
        rw [hw, reach_gate C (w - 6) (by omega), Finset.mem_insert, Finset.mem_biUnion] at hv
        rcases hv with rfl | ⟨a, ha, hva⟩
        · rw [hw]; exact hu
        · rw [List.mem_toFinset] at ha
          have halt : a < w := by have := effInputs0_lt C (w - 6) a ha; omega
          have hua := ih a halt hva
          rw [hw]
          exact reach_subset_of_effInput C (w - 6) a (by omega) ha hua
      · rw [reach_ge C w (by omega)] at hv; simp at hv

lemma reach_congr (C : Circuit) (hF : FanInTwo C) (x y : Fin 6 → Bool) (w : ℕ)
    (h : ∀ i : Fin 6, i.val ∈ reach C w → x i = y i) : wval C x w = wval C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 6
    · rw [wval_lt C x w h1, wval_lt C y w h1]
      exact h ⟨w, h1⟩ (by rw [reach_lt6 C w h1]; simp)
    · by_cases h2 : w < 6 + C.gates.length
      · have hw : w = 6 + (w - 6) := by omega
        rw [hw]
        apply effInputs0_congr C hF (w - 6) (by omega)
        intro u hu
        have hult : u < w := by have := effInputs0_lt C (w - 6) u hu; omega
        apply ih u hult
        intro i hi
        apply h i
        rw [hw]
        exact reach_subset_of_effInput C (w - 6) u (by omega) hu hi
      · rw [wval_ge C x w (by omega), wval_ge C y w (by omega)]

lemma reach_has_reader (C : Circuit) (w u : ℕ) (hu : u ∈ reach C w) (hne : u ≠ w) :
    ∃ j : ℕ, j < C.gates.length ∧ 6 + j ∈ reach C w ∧ u ∈ effInputs0 C j := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 6
    · rw [reach_lt6 C w h1, Finset.mem_singleton] at hu; exact (hne hu).elim
    · by_cases h2 : w < 6 + C.gates.length
      · have hw : w = 6 + (w - 6) := by omega
        rw [hw, reach_gate C (w - 6) (by omega), Finset.mem_insert, Finset.mem_biUnion] at hu
        rcases hu with rfl | ⟨a, ha, hua⟩
        · exact (hne hw.symm).elim
        · rw [List.mem_toFinset] at ha
          by_cases heq : u = a
          · subst heq
            exact ⟨w - 6, by omega, by rw [← hw]; exact mem_reach_self C w h2, ha⟩
          · have halt : a < w := by have := effInputs0_lt C (w - 6) a ha; omega
            obtain ⟨j, hj, h6j, huj⟩ := ih a halt hua heq
            exact ⟨j, hj, by rw [hw]; exact reach_subset_of_effInput C (w - 6) a (by omega) ha h6j, huj⟩
      · rw [reach_ge C w (by omega)] at hu; simp at hu

/-! ## Monotone binary trees for Case 2 (v = 6) -/

inductive MonoTree where
  | var (i : Fin 6)
  | and (l r : MonoTree)
  | or (l r : MonoTree)

def MonoTree.eval : MonoTree → (Fin 6 → Bool) → Bool
  | .var i, x => x i
  | .and l r, x => l.eval x && r.eval x
  | .or l r, x => l.eval x || r.eval x

def MonoTree.vars : MonoTree → Finset (Fin 6)
  | .var i => {i}
  | .and l r => l.vars ∪ r.vars
  | .or l r => l.vars ∪ r.vars

def MonoTree.leaves : MonoTree → ℕ
  | .var _ => 1
  | .and l r => l.leaves + r.leaves
  | .or l r => l.leaves + r.leaves

def MonoTree.nodes : MonoTree → ℕ
  | .var _ => 0
  | .and l r => 1 + l.nodes + r.nodes
  | .or l r => 1 + l.nodes + r.nodes

lemma MonoTree.leaves_eq_nodes_add_one (T : MonoTree) : T.leaves = T.nodes + 1 := by
  induction T with
  | var _ => rfl
  | and l r ihl ihr => simp [MonoTree.leaves, MonoTree.nodes, ihl, ihr]; omega
  | or l r ihl ihr => simp [MonoTree.leaves, MonoTree.nodes, ihl, ihr]; omega

lemma MonoTree.vars_card_le_leaves (T : MonoTree) : T.vars.card ≤ T.leaves := by
  induction T with
  | var _ => simp [MonoTree.vars, MonoTree.leaves]
  | and l r ihl ihr =>
    simp only [MonoTree.vars, MonoTree.leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)
  | or l r ihl ihr =>
    simp only [MonoTree.vars, MonoTree.leaves]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add ihl ihr)

lemma MonoTree.vars_nonempty (T : MonoTree) : T.vars.Nonempty := by
  induction T with
  | var i => exact ⟨i, by simp [MonoTree.vars]⟩
  | and l _ ihl _ => exact ihl.mono Finset.subset_union_left
  | or l _ ihl _ => exact ihl.mono Finset.subset_union_left

lemma MonoTree.mono (T : MonoTree) (x y : Fin 6 → Bool)
    (hxy : ∀ i, x i = true → y i = true) : T.eval x = true → T.eval y = true := by
  induction T with
  | var i => exact hxy i
  | and l r ihl ihr =>
    simp only [MonoTree.eval, Bool.and_eq_true]
    exact fun ⟨hl, hr⟩ => ⟨ihl hl, ihr hr⟩
  | or l r ihl ihr =>
    simp only [MonoTree.eval, Bool.or_eq_true]
    exact fun h => h.elim (fun hl => Or.inl (ihl hl)) (fun hr => Or.inr (ihr hr))

lemma MonoTree.eval_congr (T : MonoTree) (x y : Fin 6 → Bool)
    (hxy : ∀ i ∈ T.vars, x i = y i) : T.eval x = T.eval y := by
  induction T with
  | var i => exact hxy i (by simp [MonoTree.vars])
  | and l r ihl ihr =>
    simp only [MonoTree.eval]
    rw [ihl (fun i hi => hxy i (Finset.mem_union_left _ hi)),
        ihr (fun i hi => hxy i (Finset.mem_union_right _ hi))]
  | or l r ihl ihr =>
    simp only [MonoTree.eval]
    rw [ihl (fun i hi => hxy i (Finset.mem_union_left _ hi)),
        ihr (fun i hi => hxy i (Finset.mem_union_right _ hi))]

lemma MonoTree.eval_false (T : MonoTree) : T.eval (fun _ => false) = false := by
  induction T with
  | var _ => rfl
  | and l r ihl ihr => simp [MonoTree.eval, ihl, ihr]
  | or l r ihl ihr => simp [MonoTree.eval, ihl, ihr]

lemma MonoTree.eval_true (T : MonoTree) : T.eval (fun _ => true) = true := by
  induction T with
  | var _ => rfl
  | and l r ihl ihr => simp [MonoTree.eval, ihl, ihr]
  | or l r ihl ihr => simp [MonoTree.eval, ihl, ihr]

lemma MonoTree.eval_of_vars_singleton (T : MonoTree) (a : Fin 6) (h : T.vars = {a})
    (x : Fin 6 → Bool) : T.eval x = x a := by
  cases hx : x a
  · rw [← T.eval_false]
    apply T.eval_congr
    intro i hi
    rw [h, Finset.mem_singleton] at hi
    subst hi; exact hx
  · rw [← T.eval_true]
    apply T.eval_congr
    intro i hi
    rw [h, Finset.mem_singleton] at hi
    subst hi; exact hx

def setMask (S : Finset (Fin 6)) : Fin 64 := funToMask (fun i => decide (i ∈ S))

lemma testBit_setMask (S : Finset (Fin 6)) (i : Fin 6) :
    (setMask S).val.testBit i.val = decide (i ∈ S) := by
  exact maskToFun_funToMask (fun i => decide (i ∈ S)) i

lemma popcount_eq_card (S : Finset (Fin 6)) :
    ((Finset.univ : Finset (Fin 6)).filter fun i => (setMask S).val.testBit i.val).card = S.card := by
  congr 1
  ext i
  simp [testBit_setMask]

def edges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 3), (0, 5), (1, 2), (1, 4), (2, 3)]

def maskCard (m : Fin 64) : ℕ :=
  ((List.finRange 6).filter fun i => m.val.testBit i.val).length

lemma maskCard_setMask (S : Finset (Fin 6)) : maskCard (setMask S) = S.card := by
  unfold maskCard
  have h1 : ((List.finRange 6).filter fun i => (setMask S).val.testBit i.val).length =
      ((Finset.univ : Finset (Fin 6)).filter fun i => (setMask S).val.testBit i.val).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 6).filter _)]
    congr 1; ext i; simp
  rw [h1, popcount_eq_card]

def isVCMask (m : Fin 64) (es : List (Fin 6 × Fin 6)) : Bool :=
  es.all fun e => m.val.testBit e.1.val || m.val.testBit e.2.val

def subEdges (drop : Fin 6) : List (Fin 6 × Fin 6) :=
  edges.filter fun e => decide (e.1 ≠ drop ∧ e.2 ≠ drop)

def subFM (drop : Fin 6) (m : ℕ) : Bool :=
  (subEdges drop).any fun e => m.testBit e.1.val && m.testBit e.2.val

lemma and_top_cex :
    ∀ v1 v2 : Fin 64,
      isVCMask v1 edges = true → isVCMask v2 edges = true →
      maskCard v1 + maskCard v2 ≤ 7 →
      ∃ x : Fin 64,
        fM x.val = false ∧
        fM (x.val ||| (63 ^^^ v1.val)) = true ∧
        fM (x.val ||| (63 ^^^ v2.val)) = true := by
  decide +kernel

lemma or_top_only :
    ∀ v1 v2 : Fin 64,
      2 ≤ maskCard v1 → 2 ≤ maskCard v2 →
      maskCard v1 + maskCard v2 ≤ 7 →
      (edges.all fun e => (v1.val.testBit e.1.val && v1.val.testBit e.2.val) ||
                          (v2.val.testBit e.1.val && v2.val.testBit e.2.val)) = true →
      (v1.val = 18 ∧ v2.val = 47) ∨ (v1.val = 47 ∧ v2.val = 18) ∨
      (v1.val = 33 ∧ v2.val = 31) ∨ (v1.val = 31 ∧ v2.val = 33) := by
  decide +kernel

lemma sub_and_cex (drop : Fin 6) (hdrop : drop = 4 ∨ drop = 5) :
    ∀ v1 v2 : Fin 64,
      v1.val.testBit drop.val = false → v2.val.testBit drop.val = false →
      isVCMask v1 (subEdges drop) = true → isVCMask v2 (subEdges drop) = true →
      maskCard v1 + maskCard v2 ≤ 5 →
      ∃ x : Fin 64,
        x.val.testBit drop.val = false ∧
        subFM drop x.val = false ∧
        subFM drop (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ v1.val)) = true ∧
        subFM drop (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ v2.val)) = true := by
  rcases hdrop with rfl | rfl <;> decide +kernel

lemma sub_or_none (drop : Fin 6) (hdrop : drop = 4 ∨ drop = 5) :
    ∀ v1 v2 : Fin 64,
      v1.val.testBit drop.val = false → v2.val.testBit drop.val = false →
      2 ≤ maskCard v1 → 2 ≤ maskCard v2 →
      maskCard v1 + maskCard v2 ≤ 5 →
      ¬ ((subEdges drop).all fun e =>
          (v1.val.testBit e.1.val && v1.val.testBit e.2.val) ||
          (v2.val.testBit e.1.val && v2.val.testBit e.2.val)) = true := by
  rcases hdrop with rfl | rfl <;> decide +kernel

lemma mask_or_compl_bit (x v : Fin 64) (i : Fin 6) :
    (x.val ||| (63 ^^^ v.val)).testBit i.val =
      if v.val.testBit i.val then x.val.testBit i.val else true := by
  revert x v i; decide

lemma mask_or_sub_compl_bit (drop : Fin 6) (x v : Fin 64) (i : Fin 6)
    (hx : x.val.testBit drop.val = false) (hv : v.val.testBit drop.val = false) :
    (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ v.val)).testBit i.val =
      if i = drop then false else if v.val.testBit i.val then x.val.testBit i.val else true := by
  revert drop x v i hx hv; decide +kernel

lemma target_eq_subFM (drop : Fin 6) (hdrop : drop = 4 ∨ drop = 5) (m : Fin 64)
    (hm : m.val.testBit drop.val = false) :
    fM m.val = subFM drop m.val := by
  rcases hdrop with rfl | rfl <;> revert m hm <;> decide

lemma or_xor_lt64 (x v : Fin 64) : (x.val ||| (63 ^^^ v.val)) < 64 := by
  revert x v; decide +kernel

lemma or_sub_xor_lt64 (drop : Fin 6) (x v : Fin 64) :
    (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ v.val)) < 64 := by
  revert drop x v; decide +kernel

lemma fM_pair (u v : Fin 6) (huv : (u, v) ∈ edges) :
    target (fun i => decide (i = u ∨ i = v)) = true := by
  revert u v huv; decide

lemma sub_tree_impossible (drop : Fin 6) (hdrop : drop = 4 ∨ drop = 5) (M : MonoTree)
    (hleaves : M.leaves ≤ 5) (hdrop_not : drop ∉ M.vars)
    (hMeval : ∀ x : Fin 6 → Bool, x drop = false → M.eval x = target x) : False := by
  cases M with
  | var a =>
    have ha : a ≠ drop := fun h => hdrop_not (by rw [← h]; simp [MonoTree.vars])
    have he := hMeval (fun i => decide (i = a)) (by simp [ha.symm])
    rw [MonoTree.eval, target_singleton_false] at he
    simp at he
  | and M1 M2 =>
    have hcard : M1.vars.card + M2.vars.card ≤ 5 := by
      have h1 := M1.vars_card_le_leaves
      have h2 := M2.vars_card_le_leaves
      simp only [MonoTree.leaves] at hleaves
      omega
    have hd1 : drop ∉ M1.vars := fun h => hdrop_not (Finset.mem_union_left _ h)
    have hd2 : drop ∉ M2.vars := fun h => hdrop_not (Finset.mem_union_right _ h)
    have hvc : ∀ T : MonoTree, (drop ∉ T.vars) →
        (∀ x : Fin 6 → Bool, x drop = false → target x = true → T.eval x = true) →
        isVCMask (setMask T.vars) (subEdges drop) = true := by
      intro T hdT hT
      unfold isVCMask
      rw [List.all_eq_true]
      intro e he
      have hed : e ∈ edges := (List.mem_filter.mp he).1
      have hnd : e.1 ≠ drop ∧ e.2 ≠ drop := of_decide_eq_true (List.mem_filter.mp he).2
      by_contra hfalse
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, testBit_setMask,
                 decide_eq_false_iff_not] at hfalse
      let xp : Fin 6 → Bool := fun i => decide (i = e.1 ∨ i = e.2)
      have hxp_drop : xp drop = false := by
        dsimp only [xp]; simp [hnd.1.symm, hnd.2.symm]
      have ht1 : T.eval xp = true := hT xp hxp_drop (fM_pair e.1 e.2 hed)
      have ht0 : T.eval xp = T.eval (fun _ => false) := by
        apply T.eval_congr
        intro i hi
        dsimp only [xp]
        have h1 : i ≠ e.1 := fun h => hfalse.1 (h ▸ hi)
        have h2 : i ≠ e.2 := fun h => hfalse.2 (h ▸ hi)
        simp [h1, h2]
      rw [T.eval_false] at ht0
      rw [ht0] at ht1
      exact Bool.false_ne_true ht1
    have hvc1 : isVCMask (setMask M1.vars) (subEdges drop) = true :=
      hvc M1 hd1 fun x hx htx => by
        have h := hMeval x hx
        rw [htx, MonoTree.eval] at h
        exact ((Bool.and_eq_true _ _).mp h).1
    have hvc2 : isVCMask (setMask M2.vars) (subEdges drop) = true :=
      hvc M2 hd2 fun x hx htx => by
        have h := hMeval x hx
        rw [htx, MonoTree.eval] at h
        exact ((Bool.and_eq_true _ _).mp h).2
    have htb1 : (setMask M1.vars).val.testBit drop.val = false := by
      rw [testBit_setMask]; simp [hd1]
    have htb2 : (setMask M2.vars).val.testBit drop.val = false := by
      rw [testBit_setMask]; simp [hd2]
    obtain ⟨x, hxdrop, hxf, hx1, hx2⟩ :=
      sub_and_cex drop hdrop (setMask M1.vars) (setMask M2.vars) htb1 htb2 hvc1 hvc2
        (by rw [maskCard_setMask, maskCard_setMask]; exact hcard)
    have hsub_lift : ∀ (T : MonoTree) (hdT : drop ∉ T.vars)
        (hT : ∀ y : Fin 6 → Bool, y drop = false → target y = true → T.eval y = true),
        subFM drop (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ (setMask T.vars).val)) = true →
        T.eval (maskToFun x) = true := by
      intro T hdT hT hsub
      let y : Fin 6 → Bool := fun i =>
        if i = drop then false else if i ∈ T.vars then maskToFun x i else true
      have hy_drop : y drop = false := by simp [y]
      have hy_mask : ∀ i : Fin 6,
          (x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ (setMask T.vars).val)).testBit i.val = y i := by
        intro i
        have htbT : (setMask T.vars).val.testBit drop.val = false := by
          rw [testBit_setMask]; simp [hdT]
        rw [mask_or_sub_compl_bit drop x (setMask T.vars) i hxdrop htbT]
        dsimp only [y, maskToFun]
        by_cases hid : i = drop
        · simp [hid]
        · simp [hid, testBit_setMask]
      have hty : target y = true := by
        have hmf : y = maskToFun ⟨x.val ||| ((63 ^^^ (1 <<< drop.val)) ^^^ (setMask T.vars).val),
            or_sub_xor_lt64 drop x (setMask T.vars)⟩ := funext fun i => (hy_mask i).symm
        rw [hmf, target_maskToFun, target_eq_subFM drop hdrop _ (by rw [hy_mask]; exact hy_drop)]
        exact hsub
      have hTy : T.eval y = true := hT y hy_drop hty
      have hcongr : T.eval y = T.eval (maskToFun x) := by
        apply T.eval_congr
        intro i hi
        have hid : i ≠ drop := fun h => hdT (h ▸ hi)
        simp [y, hid, hi]
      rw [← hcongr]; exact hTy
    have h1 := hsub_lift M1 hd1 (fun y hy hty => by
      have h := hMeval y hy; rw [hty, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).1) hx1
    have h2 := hsub_lift M2 hd2 (fun y hy hty => by
      have h := hMeval y hy; rw [hty, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).2) hx2
    have hfx : target (maskToFun x) = false := by
      rw [target_maskToFun, target_eq_subFM drop hdrop x hxdrop]; exact hxf
    have hm := hMeval (maskToFun x) hxdrop
    rw [MonoTree.eval, h1, h2, hfx] at hm
    exact Bool.false_ne_true hm.symm
  | or M1 M2 =>
    have hcard : M1.vars.card + M2.vars.card ≤ 5 := by
      have h1 := M1.vars_card_le_leaves
      have h2 := M2.vars_card_le_leaves
      simp only [MonoTree.leaves] at hleaves
      omega
    have hd1 : drop ∉ M1.vars := fun h => hdrop_not (Finset.mem_union_left _ h)
    have hd2 : drop ∉ M2.vars := fun h => hdrop_not (Finset.mem_union_right _ h)
    have hge2 : ∀ T : MonoTree, (drop ∉ T.vars) →
        (∀ x : Fin 6 → Bool, x drop = false → T.eval x = true → target x = true) →
        2 ≤ T.vars.card := by
      intro T hdT hT
      have hpos : 1 ≤ T.vars.card := Finset.card_pos.mpr T.vars_nonempty
      by_contra hlt
      have h1 : T.vars.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have had : a ≠ drop := fun h => hdT (by rw [ha, h]; simp)
      have hv := T.eval_of_vars_singleton a ha (fun i => decide (i = a))
      simp only [decide_true] at hv
      have ht := hT (fun i => decide (i = a)) (by simp [had.symm]) hv
      rw [target_singleton_false] at ht
      exact Bool.false_ne_true ht
    have hge2_1 : 2 ≤ M1.vars.card := hge2 M1 hd1 fun x hx h1 => by
      have h := hMeval x hx; rw [MonoTree.eval, h1, Bool.true_or] at h; exact h.symm
    have hge2_2 : 2 ≤ M2.vars.card := hge2 M2 hd2 fun x hx h2 => by
      have h := hMeval x hx; rw [MonoTree.eval, h2, Bool.or_true] at h; exact h.symm
    have hcov : ((subEdges drop).all fun e =>
        ((setMask M1.vars).val.testBit e.1.val && (setMask M1.vars).val.testBit e.2.val) ||
        ((setMask M2.vars).val.testBit e.1.val && (setMask M2.vars).val.testBit e.2.val)) = true := by
      rw [List.all_eq_true]
      intro e he
      have hed : e ∈ edges := (List.mem_filter.mp he).1
      have hnd : e.1 ≠ drop ∧ e.2 ≠ drop := of_decide_eq_true (List.mem_filter.mp he).2
      let xp : Fin 6 → Bool := fun i => decide (i = e.1 ∨ i = e.2)
      have hxp_drop : xp drop = false := by dsimp only [xp]; simp [hnd.1.symm, hnd.2.symm]
      have htx : target xp = true := fM_pair e.1 e.2 hed
      have hm := hMeval xp hxp_drop
      rw [htx, MonoTree.eval, Bool.or_eq_true] at hm
      have hboth : ∀ T : MonoTree, (drop ∉ T.vars) →
          (∀ x : Fin 6 → Bool, x drop = false → T.eval x = true → target x = true) →
          T.eval xp = true → e.1 ∈ T.vars ∧ e.2 ∈ T.vars := by
        intro T _ hT hTe
        constructor
        · by_contra hnot
          have hc : T.eval xp = T.eval (fun i => decide (i = e.2)) := by
            apply T.eval_congr; intro i hi
            have hne : i ≠ e.1 := fun h => hnot (h ▸ hi)
            simp [xp, hne]
          rw [hc] at hTe
          have ht := hT (fun i => decide (i = e.2)) (by simp [hnd.2.symm]) hTe
          rw [target_singleton_false] at ht; exact Bool.false_ne_true ht
        · by_contra hnot
          have hc : T.eval xp = T.eval (fun i => decide (i = e.1)) := by
            apply T.eval_congr; intro i hi
            have hne : i ≠ e.2 := fun h => hnot (h ▸ hi)
            simp [xp, hne]
          rw [hc] at hTe
          have ht := hT (fun i => decide (i = e.1)) (by simp [hnd.1.symm]) hTe
          rw [target_singleton_false] at ht; exact Bool.false_ne_true ht
      rcases hm with h1 | h2
      · obtain ⟨h1a, h1b⟩ := hboth M1 hd1 (fun x hx h => by
          have hm := hMeval x hx; rw [MonoTree.eval, h, Bool.true_or] at hm; exact hm.symm) h1
        simp [testBit_setMask, h1a, h1b]
      · obtain ⟨h2a, h2b⟩ := hboth M2 hd2 (fun x hx h => by
          have hm := hMeval x hx; rw [MonoTree.eval, h, Bool.or_true] at hm; exact hm.symm) h2
        simp [testBit_setMask, h2a, h2b]
    have htb1 : (setMask M1.vars).val.testBit drop.val = false := by rw [testBit_setMask]; simp [hd1]
    have htb2 : (setMask M2.vars).val.testBit drop.val = false := by rw [testBit_setMask]; simp [hd2]
    exact sub_or_none drop hdrop (setMask M1.vars) (setMask M2.vars) htb1 htb2
      (by rw [maskCard_setMask]; exact hge2_1)
      (by rw [maskCard_setMask]; exact hge2_2)
      (by rw [maskCard_setMask, maskCard_setMask]; exact hcard) hcov

lemma tree_7_impossible (T : MonoTree) (hleaves : T.leaves ≤ 7)
    (heval : ∀ x : Fin 6 → Bool, T.eval x = target x) : False := by
  cases T with
  | var a =>
    have h := heval (fun i => decide (i = a))
    rw [MonoTree.eval, target_singleton_false] at h
    simp at h
  | and L R =>
    have hcard : L.vars.card + R.vars.card ≤ 7 := by
      have h1 := L.vars_card_le_leaves
      have h2 := R.vars_card_le_leaves
      simp only [MonoTree.leaves] at hleaves
      omega
    have hvc : ∀ U : MonoTree, (∀ x, target x = true → U.eval x = true) →
        isVCMask (setMask U.vars) edges = true := by
      intro U hU
      unfold isVCMask
      rw [List.all_eq_true]
      intro e he
      by_contra hfalse
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, testBit_setMask,
                 decide_eq_false_iff_not] at hfalse
      let xp : Fin 6 → Bool := fun i => decide (i = e.1 ∨ i = e.2)
      have ht1 : U.eval xp = true := hU xp (fM_pair e.1 e.2 he)
      have ht0 : U.eval xp = U.eval (fun _ => false) := by
        apply U.eval_congr; intro i hi
        have h1 : i ≠ e.1 := fun h => hfalse.1 (h ▸ hi)
        have h2 : i ≠ e.2 := fun h => hfalse.2 (h ▸ hi)
        simp [xp, h1, h2]
      rw [U.eval_false] at ht0; rw [ht0] at ht1
      exact Bool.false_ne_true ht1
    have hvc1 := hvc L fun x htx => by
      have h := heval x; rw [htx, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).1
    have hvc2 := hvc R fun x htx => by
      have h := heval x; rw [htx, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).2
    obtain ⟨x, hxf, hx1, hx2⟩ :=
      and_top_cex (setMask L.vars) (setMask R.vars) hvc1 hvc2
        (by rw [maskCard_setMask, maskCard_setMask]; exact hcard)
    have hlift : ∀ U : MonoTree, (∀ y, target y = true → U.eval y = true) →
        fM (x.val ||| (63 ^^^ (setMask U.vars).val)) = true → U.eval (maskToFun x) = true := by
      intro U hU hfm
      let y : Fin 6 → Bool := fun i => if i ∈ U.vars then maskToFun x i else true
      have hy_mask : ∀ i : Fin 6, (x.val ||| (63 ^^^ (setMask U.vars).val)).testBit i.val = y i := by
        intro i
        rw [mask_or_compl_bit x (setMask U.vars) i, testBit_setMask]
        dsimp only [y, maskToFun]
        by_cases hi : i ∈ U.vars <;> simp [hi]
      have hty : target y = true := by
        have hmf : y = maskToFun ⟨x.val ||| (63 ^^^ (setMask U.vars).val),
            or_xor_lt64 x (setMask U.vars)⟩ := funext fun i => (hy_mask i).symm
        rw [hmf, target_maskToFun]; exact hfm
      have hUy := hU y hty
      have hcongr : U.eval y = U.eval (maskToFun x) := by
        apply U.eval_congr; intro i hi; simp [y, hi]
      rw [← hcongr]; exact hUy
    have hL := hlift L (fun y hty => by
      have h := heval y; rw [hty, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).1) hx1
    have hR := hlift R (fun y hty => by
      have h := heval y; rw [hty, MonoTree.eval] at h; exact ((Bool.and_eq_true _ _).mp h).2) hx2
    have htot := heval (maskToFun x)
    rw [MonoTree.eval, hL, hR, target_maskToFun, hxf] at htot
    exact Bool.false_ne_true htot.symm
  | or L R =>
    have hcard : L.vars.card + R.vars.card ≤ 7 := by
      have h1 := L.vars_card_le_leaves
      have h2 := R.vars_card_le_leaves
      simp only [MonoTree.leaves] at hleaves
      omega
    have hge2 : ∀ U : MonoTree, (∀ x, U.eval x = true → target x = true) → 2 ≤ U.vars.card := by
      intro U hU
      have hpos : 1 ≤ U.vars.card := Finset.card_pos.mpr U.vars_nonempty
      by_contra hlt
      have h1 : U.vars.card = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
      have hv := U.eval_of_vars_singleton a ha (fun i => decide (i = a))
      simp only [decide_true] at hv
      have ht := hU (fun i => decide (i = a)) hv
      rw [target_singleton_false] at ht
      exact Bool.false_ne_true ht
    have hL2 : 2 ≤ L.vars.card := hge2 L fun x h => by
      have hm := heval x; rw [MonoTree.eval, h, Bool.true_or] at hm; exact hm.symm
    have hR2 : 2 ≤ R.vars.card := hge2 R fun x h => by
      have hm := heval x; rw [MonoTree.eval, h, Bool.or_true] at hm; exact hm.symm
    have hcov : (edges.all fun e =>
        ((setMask L.vars).val.testBit e.1.val && (setMask L.vars).val.testBit e.2.val) ||
        ((setMask R.vars).val.testBit e.1.val && (setMask R.vars).val.testBit e.2.val)) = true := by
      rw [List.all_eq_true]
      intro e he
      let xp : Fin 6 → Bool := fun i => decide (i = e.1 ∨ i = e.2)
      have hm := heval xp
      rw [fM_pair e.1 e.2 he, MonoTree.eval, Bool.or_eq_true] at hm
      have hboth : ∀ U : MonoTree, (∀ x, U.eval x = true → target x = true) →
          U.eval xp = true → e.1 ∈ U.vars ∧ e.2 ∈ U.vars := by
        intro U hU hUe
        constructor
        · by_contra hnot
          have hc : U.eval xp = U.eval (fun i => decide (i = e.2)) := by
            apply U.eval_congr; intro i hi
            have hne : i ≠ e.1 := fun h => hnot (h ▸ hi)
            simp [xp, hne]
          rw [hc] at hUe
          have ht := hU (fun i => decide (i = e.2)) hUe
          rw [target_singleton_false] at ht; exact Bool.false_ne_true ht
        · by_contra hnot
          have hc : U.eval xp = U.eval (fun i => decide (i = e.1)) := by
            apply U.eval_congr; intro i hi
            have hne : i ≠ e.2 := fun h => hnot (h ▸ hi)
            simp [xp, hne]
          rw [hc] at hUe
          have ht := hU (fun i => decide (i = e.1)) hUe
          rw [target_singleton_false] at ht; exact Bool.false_ne_true ht
      rcases hm with h1 | h2
      · obtain ⟨h1a, h1b⟩ := hboth L (fun x h => by
          have hm := heval x; rw [MonoTree.eval, h, Bool.true_or] at hm; exact hm.symm) h1
        simp [testBit_setMask, h1a, h1b]
      · obtain ⟨h2a, h2b⟩ := hboth R (fun x h => by
          have hm := heval x; rw [MonoTree.eval, h, Bool.or_true] at hm; exact hm.symm) h2
        simp [testBit_setMask, h2a, h2b]
    have hcases := or_top_only (setMask L.vars) (setMask R.vars)
      (by rw [maskCard_setMask]; exact hL2)
      (by rw [maskCard_setMask]; exact hR2)
      (by rw [maskCard_setMask, maskCard_setMask]; exact hcard) hcov
    have hfinish : ∀ (A B : MonoTree) (drop keep : Fin 6),
        (drop = 4 ∧ keep = 1 ∧ (setMask A.vars).val = 18 ∧ (setMask B.vars).val = 47) ∨
        (drop = 5 ∧ keep = 0 ∧ (setMask A.vars).val = 33 ∧ (setMask B.vars).val = 31) →
        A.leaves + B.leaves ≤ 7 →
        (∀ x, (A.eval x || B.eval x) = target x) → False := by
      intro A B drop keep hspec hsum hAB
      have hAdrop : drop = 4 ∨ drop = 5 := by
        rcases hspec with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _, _⟩ <;> simp
      have hBnd : drop ∉ B.vars := by
        have htb : (setMask B.vars).val.testBit drop.val = false := by
          rcases hspec with ⟨rfl, _, _, hB⟩ | ⟨rfl, _, _, hB⟩ <;> rw [hB] <;> decide
        rw [testBit_setMask] at htb; simpa using htb
      have hAvars : ∀ i ∈ A.vars, i = drop ∨ i = keep := by
        intro i hi
        have htb : (setMask A.vars).val.testBit i.val = true := by rw [testBit_setMask]; simp [hi]
        rcases hspec with ⟨rfl, rfl, hA, _⟩ | ⟨rfl, rfl, hA, _⟩
        · rw [hA] at htb; clear hi; revert i htb; decide
        · rw [hA] at htb; clear hi; revert i htb; decide
      have hAcard : 2 ≤ A.vars.card := by
        have hmc : maskCard (setMask A.vars) = 2 := by
          rcases hspec with ⟨_, _, hA, _⟩ | ⟨_, _, hA, _⟩ <;>
            simp [maskCard, hA] <;> decide
        rw [maskCard_setMask] at hmc; omega
      have hAleaves : 2 ≤ A.leaves := le_trans hAcard A.vars_card_le_leaves
      have hBleaves : B.leaves ≤ 5 := by omega
      have hdk_ne : drop ≠ keep := by
        rcases hspec with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩ <;> decide
      have hAfalse : ∀ x : Fin 6 → Bool, x drop = false → A.eval x = false := by
        intro x hxd
        by_contra hAt
        have hAt' : A.eval x = true := by cases h : A.eval x <;> simp_all
        let x' : Fin 6 → Bool := fun i => if i = keep then x keep else false
        have hcongr : A.eval x = A.eval x' := by
          apply A.eval_congr; intro i hi
          rcases hAvars i hi with hieq | hieq
          · subst hieq; simp [x', hdk_ne, hxd]
          · subst hieq; simp [x']
        rw [hcongr] at hAt'
        have htx' : target x' = true := by
          have h := hAB x'; rw [hAt', Bool.true_or] at h; exact h.symm
        cases hxk : x keep
        · have hx0 : x' = fun _ => false := funext fun i => by simp [x', hxk]
          rw [hx0, target_all_false] at htx'; exact Bool.false_ne_true htx'
        · have hx1 : x' = fun i => decide (i = keep) := funext fun i => by
            dsimp only [x']; by_cases hi : i = keep <;> simp [hi, hxk]
          rw [hx1, target_singleton_false] at htx'; exact Bool.false_ne_true htx'
      apply sub_tree_impossible drop hAdrop B hBleaves hBnd
      intro x hxd
      have h := hAB x
      rw [hAfalse x hxd, Bool.false_or] at h
      exact h
    simp only [MonoTree.leaves] at hleaves
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hfinish L R 4 1 (Or.inl ⟨rfl, rfl, h1, h2⟩) hleaves fun x => by
        simpa [MonoTree.eval] using heval x
    · exact hfinish R L 4 1 (Or.inl ⟨rfl, rfl, h2, h1⟩) (by omega) fun x => by
        have h := heval x; rw [MonoTree.eval, Bool.or_comm] at h; exact h
    · exact hfinish L R 5 0 (Or.inr ⟨rfl, rfl, h1, h2⟩) hleaves fun x => by
        simpa [MonoTree.eval] using heval x
    · exact hfinish R L 5 0 (Or.inr ⟨rfl, rfl, h2, h1⟩) (by omega) fun x => by
        have h := heval x; rw [MonoTree.eval, Bool.or_comm] at h; exact h

/-! ## Main lower bound proof -/

lemma no_circuit_le6 (C : Circuit) (hF : FanInTwo C) (hS : C.size ≤ 6)
    (heval : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) : False := by
  have hwval_out : ∀ x : Fin 6 → Bool, wval C x C.output = target x := heval
  let m : ℕ := C.gates.length
  have hm : m ≤ 6 := hS
  let live : Finset ℕ := reach C C.output
  have hlive_inputs : ∀ i : Fin 6, i.val ∈ live := by
    intro i
    by_contra hnot
    obtain ⟨x, y, hagree, hne⟩ := target_matters i
    have hEq : wval C x C.output = wval C y C.output := by
      apply reach_congr C hF x y C.output
      intro j hj
      have hji : j ≠ i := fun h => hnot (h ▸ hj)
      exact hagree j hji
    rw [hwval_out x, hwval_out y] at hEq
    exact hne hEq
  have hout_ge6 : 6 ≤ C.output := by
    by_contra hlt
    have h1 : C.output < 6 := by omega
    have h := hwval_out (fun j => decide (j = ⟨C.output, h1⟩))
    rw [wval_lt C _ C.output h1, target_singleton_false] at h
    simp at h
  have hout_lt : C.output < 6 + m := by
    by_contra hge
    have h := hwval_out (fun _ => true)
    rw [wval_ge C _ C.output (by omega), target_all_true] at h
    exact Bool.false_ne_true h
  have hout_mem : C.output ∈ live := mem_reach_self C C.output hout_lt
  let Lg : Finset ℕ := (Finset.range m).filter fun j => 6 + j ∈ live
  let outdeg (u : ℕ) : ℕ := (Lg.filter fun j => u ∈ effInputs0 C j).card
  have hlive_sub : live ⊆ Finset.range 6 ∪ Lg.image (6 + ·) := by
    intro w hw
    have hle : w ≤ C.output := mem_reach_le C C.output w hw
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_image]
    by_cases h6 : w < 6
    · exact Or.inl h6
    · refine Or.inr ⟨w - 6, ?_, by omega⟩
      simp only [Lg, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hsub : 6 + (w - 6) = w := by omega
      rw [hsub]
      exact hw
  have hsub_live : Finset.range 6 ∪ Lg.image (6 + ·) ⊆ live := by
    intro w hw
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_image] at hw
    rcases hw with h6 | ⟨j, hj, rfl⟩
    · exact hlive_inputs ⟨w, h6⟩
    · exact (Finset.mem_filter.mp hj).2
  have hlive_eq : live = Finset.range 6 ∪ Lg.image (6 + ·) := Finset.Subset.antisymm hlive_sub hsub_live
  have hdisj : Disjoint (Finset.range 6) (Lg.image (6 + ·)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_range] at hw1
    rw [Finset.mem_image] at hw2
    obtain ⟨j, _, rfl⟩ := hw2
    omega
  have hlive_card : live.card = 6 + Lg.card := by
    rw [hlive_eq, Finset.card_union_of_disjoint hdisj, Finset.card_range,
        Finset.card_image_of_injective _ (fun a b h => by omega)]
  have hlive_erase_card : (live.erase C.output).card = 5 + Lg.card := by
    rw [Finset.card_erase_of_mem hout_mem, hlive_card]; omega
  have houtdeg_pos : ∀ u ∈ live.erase C.output, 1 ≤ outdeg u := by
    intro u hu
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hu
    obtain ⟨j, hj, h6j, huj⟩ := reach_has_reader C C.output u hmem hne
    apply Finset.card_pos.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h6j⟩, huj⟩⟩
  have hsum_eq : ∑ u ∈ live, outdeg u = ∑ j ∈ Lg, (effInputs0 C j).length := by
    dsimp only [outdeg]
    calc ∑ u ∈ live, (Lg.filter fun j => u ∈ effInputs0 C j).card
        = ∑ u ∈ live, ∑ j ∈ Lg, if u ∈ effInputs0 C j then 1 else 0 := by
            congr 1; ext u; rw [Finset.card_filter]
      _ = ∑ j ∈ Lg, ∑ u ∈ live, if u ∈ effInputs0 C j then 1 else 0 := Finset.sum_comm
      _ = ∑ j ∈ Lg, (effInputs0 C j).length := by
            apply Finset.sum_congr rfl
            intro j hjmem
            rw [← Finset.card_filter]
            have hsub : (effInputs0 C j).toFinset ⊆ live := by
              intro u hu
              rw [List.mem_toFinset] at hu
              have hjL := Finset.mem_filter.mp hjmem
              have hjlt : j < m := Finset.mem_range.mp hjL.1
              have h6j : 6 + j ∈ live := hjL.2
              exact reach_trans C C.output (6 + j) u h6j
                (reach_subset_of_effInput C j u hjlt hu (mem_reach_self C u (by
                  have := effInputs0_lt C j u hu; omega)))
            have hfeq : live.filter (fun u => u ∈ effInputs0 C j) = (effInputs0 C j).toFinset := by
              ext u; simp only [Finset.mem_filter, List.mem_toFinset]
              exact ⟨fun h => h.2, fun h => ⟨hsub (List.mem_toFinset.mpr h), h⟩⟩
            rw [hfeq, List.toFinset_card_of_nodup (effInputs0_nodup C j)]
  let B : Finset ℕ := Lg.filter fun j => (effInputs0 C j).length = 2
  let U : Finset ℕ := Lg.filter fun j => (effInputs0 C j).length ≠ 2
  have hLg_card : Lg.card = B.card + U.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1))]
    congr 1; ext j; simp only [B, U, Finset.mem_union, Finset.mem_filter]; tauto
  have hU_le1 : ∀ j ∈ U, (effInputs0 C j).length ≤ 1 := by
    intro j hj
    have hne : (effInputs0 C j).length ≠ 2 := (Finset.mem_filter.mp hj).2
    have hle := effInputs0_len_le C j
    omega
  have hsum_le : ∑ j ∈ Lg, (effInputs0 C j).length ≤ 2 * B.card + U.card := by
    have hpart : Lg = B ∪ U := by
      ext j; simp only [B, U, Finset.mem_union, Finset.mem_filter]; tauto
    have hBU_disj : Disjoint B U := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
    rw [hpart, Finset.sum_union hBU_disj]
    have hBsum : ∑ j ∈ B, (effInputs0 C j).length = 2 * B.card := by
      have : ∀ j ∈ B, (effInputs0 C j).length = 2 := fun j hj => (Finset.mem_filter.mp hj).2
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]; omega
    have hUsum : ∑ j ∈ U, (effInputs0 C j).length ≤ U.card := by
      calc ∑ j ∈ U, (effInputs0 C j).length
          ≤ ∑ _ ∈ U, 1 := Finset.sum_le_sum hU_le1
        _ = U.card := by simp
    omega
  have hsum_ge : 5 + Lg.card ≤ ∑ u ∈ live.erase C.output, outdeg u := by
    calc 5 + Lg.card = (live.erase C.output).card := hlive_erase_card.symm
      _ = ∑ _ ∈ live.erase C.output, 1 := by simp
      _ ≤ ∑ u ∈ live.erase C.output, outdeg u := Finset.sum_le_sum houtdeg_pos
  have hsum_erase_le : ∑ u ∈ live.erase C.output, outdeg u ≤ ∑ u ∈ live, outdeg u :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset C.output live)
  have hLg_le6 : Lg.card ≤ 6 := le_trans (Finset.card_le_card (Finset.filter_subset _ _))
    (by rw [Finset.card_range]; exact hm)
  have hB_ge5 : 5 ≤ B.card := by omega
  have hB_le6 : B.card ≤ 6 := by omega
  by_cases hB5 : B.card = 5
  · -- Case 1: v = 5 (every wire in live \ {C.output} has outdeg = 1, every j ∈ U has len = 1)
    have hsum_eq_all : ∑ u ∈ live.erase C.output, outdeg u = 5 + Lg.card := by omega
    have houtdeg_one : ∀ u ∈ live.erase C.output, outdeg u = 1 := by
      intro u hu
      by_contra hne
      have hge2 : 2 ≤ outdeg u := by have := houtdeg_pos u hu; omega
      have hsplit : ∑ v ∈ live.erase C.output, outdeg v =
          outdeg u + ∑ v ∈ (live.erase C.output).erase u, outdeg v :=
        (Finset.add_sum_erase _ _ hu).symm
      have hrest : ((live.erase C.output).erase u).card ≤
          ∑ v ∈ (live.erase C.output).erase u, outdeg v := by
        calc ((live.erase C.output).erase u).card
            = ∑ _ ∈ (live.erase C.output).erase u, 1 := by simp
          _ ≤ ∑ v ∈ (live.erase C.output).erase u, outdeg v :=
              Finset.sum_le_sum fun v hv => houtdeg_pos v (Finset.mem_of_mem_erase hv)
      have hc : ((live.erase C.output).erase u).card + 1 = (live.erase C.output).card := by
        rw [Finset.card_erase_of_mem hu]
        have : 0 < (live.erase C.output).card := Finset.card_pos.mpr ⟨u, hu⟩
        omega
      omega
    have hU_eq1 : ∀ j ∈ U, (effInputs0 C j).length = 1 := by
      intro j hj
      by_contra hne
      have h0 : (effInputs0 C j).length = 0 := by have := hU_le1 j hj; omega
      have hUsum : ∑ k ∈ U, (effInputs0 C k).length ≤ U.card - 1 := by
        rw [← Finset.add_sum_erase _ _ hj, h0, Nat.zero_add]
        calc ∑ k ∈ U.erase j, (effInputs0 C k).length
            ≤ ∑ _ ∈ U.erase j, 1 := Finset.sum_le_sum fun k hk => hU_le1 k (Finset.mem_of_mem_erase hk)
          _ = (U.erase j).card := by simp
          _ = U.card - 1 := Finset.card_erase_of_mem hj
      have hpart : Lg = B ∪ U := by
        ext k; simp only [B, U, Finset.mem_union, Finset.mem_filter]; tauto
      have hBU_disj : Disjoint B U := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
      have hBsum : ∑ k ∈ B, (effInputs0 C k).length = 2 * B.card := by
        have : ∀ k ∈ B, (effInputs0 C k).length = 2 := fun k hk => (Finset.mem_filter.mp hk).2
        rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]; omega
      have hcardU_pos : 1 ≤ U.card := Finset.card_pos.mpr ⟨j, hj⟩
      have htot : ∑ k ∈ Lg, (effInputs0 C k).length ≤ 2 * B.card + U.card - 1 := by
        rw [hpart, Finset.sum_union hBU_disj]; omega
      omega
    have hB_ne : B.Nonempty := Finset.card_pos.mp (by omega)
    let j0 : ℕ := B.min' hB_ne
    have hj0_B : j0 ∈ B := Finset.min'_mem B hB_ne
    have hj0_Lg : j0 ∈ Lg := (Finset.mem_filter.mp hj0_B).1
    have hj0_lt : j0 < m := Finset.mem_range.mp (Finset.mem_filter.mp hj0_Lg).1
    have hj0_live : 6 + j0 ∈ live := (Finset.mem_filter.mp hj0_Lg).2
    have hj0_len2 : (effInputs0 C j0).length = 2 := (Finset.mem_filter.mp hj0_B).2
    obtain ⟨a, b, hab_eq, hab_ne, ha_lt, hb_lt, _⟩ := effInputs0_len2 C hF j0 hj0_lt hj0_len2
    have hlt_j0_U : ∀ j ∈ Lg, j < j0 → j ∈ U := by
      intro j hjL hlt
      refine Finset.mem_filter.mpr ⟨hjL, ?_⟩
      intro hlen2
      have hmemB : j ∈ B := Finset.mem_filter.mpr ⟨hjL, hlen2⟩
      have hge := Finset.min'_le B j hmemB
      omega
    have hunique_reader : ∀ u ∈ live.erase C.output, ∀ j1 ∈ Lg, ∀ j2 ∈ Lg,
        u ∈ effInputs0 C j1 → u ∈ effInputs0 C j2 → j1 = j2 := by
      intro u hu j1 hj1 j2 hj2 hu1 hu2
      have hc1 := houtdeg_one u hu
      dsimp only [outdeg] at hc1
      obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc1
      have h1 : j1 ∈ Lg.filter (fun j => u ∈ effInputs0 C j) := Finset.mem_filter.mpr ⟨hj1, hu1⟩
      have h2 : j2 ∈ Lg.filter (fun j => u ∈ effInputs0 C j) := Finset.mem_filter.mpr ⟨hj2, hu2⟩
      rw [hk, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    have hlt_out : ∀ w, w < 6 + j0 → w ≠ C.output := by
      intro w hw heq
      have hle := mem_reach_le C C.output (6 + j0) hj0_live
      omega
    have hchain_inp : ∀ w : ℕ, w ∈ live → w < 6 + j0 →
        ∃ i : Fin 6, i.val ∈ reach C w ∧ ∀ k : Fin 6, k.val ∈ reach C w → k = i := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw hlt
        by_cases h6 : w < 6
        · refine ⟨⟨w, h6⟩, by rw [reach_lt6 C w h6]; simp, ?_⟩
          intro k hk
          rw [reach_lt6 C w h6, Finset.mem_singleton] at hk
          exact Fin.ext hk
        · have hw_eq : w = 6 + (w - 6) := by omega
          have hjL : w - 6 ∈ Lg := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
            by rw [← hw_eq]; exact hw⟩
          have hjU : w - 6 ∈ U := hlt_j0_U (w - 6) hjL (by omega)
          have hlen1 := hU_eq1 (w - 6) hjU
          obtain ⟨u, hu_eq⟩ := List.length_eq_one_iff.mp hlen1
          have hu_mem : u ∈ effInputs0 C (w - 6) := by rw [hu_eq]; simp
          have hult : u < w := by have := effInputs0_lt C (w - 6) u hu_mem; omega
          have hu_in_w : u ∈ reach C w := by
            rw [hw_eq]
            exact reach_subset_of_effInput C (w - 6) u (by omega) hu_mem
              (mem_reach_self C u (by omega))
          have hu_live : u ∈ live := reach_trans C C.output w u hw hu_in_w
          obtain ⟨i, hi_mem, hi_uniq⟩ := ih u hult hu_live (by omega)
          have hreach_eq : reach C w = insert w (reach C u) := by
            rw [hw_eq, reach_gate C (w - 6) (by omega), hu_eq]
            simp
          refine ⟨i, by rw [hreach_eq]; exact Finset.mem_insert_of_mem hi_mem, ?_⟩
          intro k hk
          rw [hreach_eq, Finset.mem_insert] at hk
          rcases hk with hkeq | hk'
          · omega
          · exact hi_uniq k hk'
    have ha_mem : a ∈ effInputs0 C j0 := by rw [hab_eq]; simp
    have hb_mem : b ∈ effInputs0 C j0 := by rw [hab_eq]; simp
    have ha_live : a ∈ live := reach_trans C C.output (6 + j0) a hj0_live
      (reach_subset_of_effInput C j0 a hj0_lt ha_mem (mem_reach_self C a (by omega)))
    have hb_live : b ∈ live := reach_trans C C.output (6 + j0) b hj0_live
      (reach_subset_of_effInput C j0 b hj0_lt hb_mem (mem_reach_self C b (by omega)))
    have hdisj_ab : Disjoint (reach C a) (reach C b) := by
      rw [Finset.disjoint_left]
      intro u hua hub
      let common := reach C a ∩ reach C b
      have hcom_ne : common.Nonempty := ⟨u, Finset.mem_inter.mpr ⟨hua, hub⟩⟩
      let umax := common.max' hcom_ne
      have humax_mem := Finset.max'_mem common hcom_ne
      have humax_a : umax ∈ reach C a := (Finset.mem_inter.mp humax_mem).1
      have humax_b : umax ∈ reach C b := (Finset.mem_inter.mp humax_mem).2
      have humax_lt : umax < 6 + j0 := by
        have := mem_reach_le C a umax humax_a; omega
      have humax_live : umax ∈ live.erase C.output :=
        Finset.mem_erase.mpr ⟨hlt_out umax humax_lt, reach_trans C C.output a umax ha_live humax_a⟩
      by_cases h1 : umax = a
      · have hne_b : umax ≠ b := by rw [h1]; exact hab_ne
        obtain ⟨j1, hj1_lt, hj1_rb, hj1_u⟩ := reach_has_reader C b umax humax_b hne_b
        have hj1_le : 6 + j1 ≤ b := mem_reach_le C b (6 + j1) hj1_rb
        have hj1_Lg : j1 ∈ Lg := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hj1_lt, reach_trans C C.output b (6 + j1) hb_live hj1_rb⟩
        have heq := hunique_reader umax humax_live j1 hj1_Lg j0 hj0_Lg hj1_u (h1 ▸ ha_mem)
        omega
      · by_cases h2 : umax = b
        · obtain ⟨j1, hj1_lt, hj1_ra, hj1_u⟩ := reach_has_reader C a umax humax_a h1
          have hj1_le : 6 + j1 ≤ a := mem_reach_le C a (6 + j1) hj1_ra
          have hj1_Lg : j1 ∈ Lg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hj1_lt, reach_trans C C.output a (6 + j1) ha_live hj1_ra⟩
          have heq := hunique_reader umax humax_live j1 hj1_Lg j0 hj0_Lg hj1_u (h2 ▸ hb_mem)
          omega
        · obtain ⟨j1, hj1_lt, hj1_ra, hj1_u⟩ := reach_has_reader C a umax humax_a h1
          obtain ⟨j2, hj2_lt, hj2_rb, hj2_u⟩ := reach_has_reader C b umax humax_b h2
          have hj1_Lg : j1 ∈ Lg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hj1_lt, reach_trans C C.output a (6 + j1) ha_live hj1_ra⟩
          have hj2_Lg : j2 ∈ Lg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hj2_lt, reach_trans C C.output b (6 + j2) hb_live hj2_rb⟩
          have heq := hunique_reader umax humax_live j1 hj1_Lg j2 hj2_Lg hj1_u hj2_u
          subst heq
          have hmem_c : 6 + j1 ∈ common := Finset.mem_inter.mpr ⟨hj1_ra, hj2_rb⟩
          have hle_max := Finset.le_max' common (6 + j1) hmem_c
          have hlt_u := effInputs0_lt C j1 umax hj1_u
          omega
    obtain ⟨ia, hia_mem, hia_uniq⟩ := hchain_inp a ha_live ha_lt
    obtain ⟨ib, hib_mem, hib_uniq⟩ := hchain_inp b hb_live hb_lt
    have hiab_ne : ia ≠ ib := by
      intro h; subst h
      exact Finset.disjoint_left.mp hdisj_ab hia_mem hib_mem
    let gfun : Bool → Bool → Bool := fun u v =>
      wval C (fun i => if i = ia then u else if i = ib then v else false) (6 + j0)
    have hj0_dep : ∀ x : Fin 6 → Bool, wval C x (6 + j0) = gfun (x ia) (x ib) := by
      intro x
      dsimp only [gfun]
      apply reach_congr C hF
      intro k hk
      rw [reach_gate C j0 hj0_lt, hab_eq, Finset.mem_insert] at hk
      rcases hk with hkeq | hk'
      · omega
      · simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
                   Finset.biUnion_insert, Finset.singleton_biUnion, Finset.mem_union] at hk'
        rcases hk' with hka | hkb
        · have heq := hia_uniq k hka; subst heq; simp
        · have heq := hib_uniq k hkb; subst heq; simp [hiab_ne.symm]
    have hno_escape : ∀ w ∈ reach C a ∪ reach C b, ∀ j ∈ Lg,
        w ∈ effInputs0 C j → j = j0 ∨ 6 + j ∈ reach C a ∪ reach C b := by
      intro w hw j hjL hwj
      have hw_lt : w < 6 + j0 := by
        rw [Finset.mem_union] at hw
        rcases hw with hwa | hwb
        · have := mem_reach_le C a w hwa; omega
        · have := mem_reach_le C b w hwb; omega
      have hw_live : w ∈ live.erase C.output := by
        refine Finset.mem_erase.mpr ⟨hlt_out w hw_lt, ?_⟩
        rw [Finset.mem_union] at hw
        rcases hw with hwa | hwb
        · exact reach_trans C C.output a w ha_live hwa
        · exact reach_trans C C.output b w hb_live hwb
      rw [Finset.mem_union] at hw
      rcases hw with hwa | hwb
      · by_cases hwa_eq : w = a
        · subst hwa_eq
          exact Or.inl (hunique_reader w hw_live j hjL j0 hj0_Lg hwj ha_mem)
        · obtain ⟨j1, hj1_lt, hj1_ra, hj1_w⟩ := reach_has_reader C a w hwa hwa_eq
          have hj1_Lg : j1 ∈ Lg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hj1_lt, reach_trans C C.output a (6 + j1) ha_live hj1_ra⟩
          have heq := hunique_reader w hw_live j hjL j1 hj1_Lg hwj hj1_w
          subst heq
          exact Or.inr (Finset.mem_union_left _ hj1_ra)
      · by_cases hwb_eq : w = b
        · subst hwb_eq
          exact Or.inl (hunique_reader w hw_live j hjL j0 hj0_Lg hwj hb_mem)
        · obtain ⟨j1, hj1_lt, hj1_rb, hj1_w⟩ := reach_has_reader C b w hwb hwb_eq
          have hj1_Lg : j1 ∈ Lg := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hj1_lt, reach_trans C C.output b (6 + j1) hb_live hj1_rb⟩
          have heq := hunique_reader w hw_live j hjL j1 hj1_Lg hwj hj1_w
          subst heq
          exact Or.inr (Finset.mem_union_right _ hj1_rb)
    obtain ⟨x, y, hagree, hgeq, hne⟩ := target_three_cofactors ia ib hiab_ne gfun
    have hout_eq : ∀ w : ℕ, w ∈ live → w ∉ reach C a ∪ reach C b → wval C x w = wval C y w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_live hw_not
        by_cases h6 : w < 6
        · rw [wval_lt C x w h6, wval_lt C y w h6]
          have hna : ⟨w, h6⟩ ≠ ia := fun h => hw_not (Finset.mem_union_left _ (by rw [← h] at hia_mem; exact hia_mem))
          have hnb : ⟨w, h6⟩ ≠ ib := fun h => hw_not (Finset.mem_union_right _ (by rw [← h] at hib_mem; exact hib_mem))
          exact hagree ⟨w, h6⟩ hna hnb
        · by_cases hgj0 : w = 6 + j0
          · subst hgj0
            rw [hj0_dep x, hj0_dep y]
            exact hgeq
          · have hw_lt : w < 6 + m := by
              have := mem_reach_le C C.output w hw_live; omega
            have hw_eq : w = 6 + (w - 6) := by omega
            have hjL : w - 6 ∈ Lg := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), by rw [← hw_eq]; exact hw_live⟩
            rw [hw_eq]
            apply effInputs0_congr C hF (w - 6) (by omega)
            intro u hu
            have hult : u < w := by have := effInputs0_lt C (w - 6) u hu; omega
            have hu_in_w : u ∈ reach C w := by
              rw [hw_eq]
              exact reach_subset_of_effInput C (w - 6) u (by omega) hu
                (mem_reach_self C u (by omega))
            have hu_live : u ∈ live := reach_trans C C.output w u hw_live hu_in_w
            have hu_not : u ∉ reach C a ∪ reach C b := by
              intro hu_in
              rcases hno_escape u hu_in (w - 6) hjL hu with h1 | h2
              · exact hgj0 (by omega)
              · rw [← hw_eq] at h2; exact hw_not h2
            exact ih u hult hu_live hu_not
    have hout_not : C.output ∉ reach C a ∪ reach C b := by
      intro hmem
      rw [Finset.mem_union] at hmem
      have hle : 6 + j0 ≤ C.output := mem_reach_le C C.output (6 + j0) hj0_live
      rcases hmem with h1 | h2
      · have := mem_reach_le C a C.output h1; omega
      · have := mem_reach_le C b C.output h2; omega
    have hEq := hout_eq C.output hout_mem hout_not
    rw [hwval_out x, hwval_out y] at hEq
    exact hne hEq
  · -- Case 2: v = 6 (all 6 gates are live binary AND/OR gates, excess fan-out = 1)
    have hB6 : B.card = 6 := by omega
    have hLg6 : Lg.card = 6 := by omega
    have hm6 : m = 6 := by
      have : Lg.card ≤ m := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
      omega
    have hLg_eq : Lg = Finset.range 6 := by
      apply Finset.eq_of_subset_of_card_le
      · rw [← hm6]; exact Finset.filter_subset _ _
      · rw [Finset.card_range, hLg6]
    have hB_eq : B = Finset.range 6 := by
      apply Finset.eq_of_subset_of_card_le
      · exact le_trans (Finset.filter_subset _ _) (by rw [hLg_eq])
      · rw [Finset.card_range, hB6]
    have hlen2_all : ∀ j < 6, (effInputs0 C j).length = 2 := by
      intro j hj
      have hjB : j ∈ B := by rw [hB_eq, Finset.mem_range]; exact hj
      exact (Finset.mem_filter.mp hjB).2
    have hout11 : C.output = 11 := by
      have h5Lg : 5 ∈ Lg := by rw [hLg_eq]; simp
      have h11live : 11 ∈ live := (Finset.mem_filter.mp h5Lg).2
      have hle : 11 ≤ C.output := mem_reach_le C C.output 11 h11live
      omega
    have hlive_eq12 : live = Finset.range 12 := by
      ext w
      rw [hlive_eq, hLg_eq, Finset.mem_union, Finset.mem_range, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (h | ⟨j, hj, rfl⟩)
        · omega
        · rw [Finset.mem_range] at hj; omega
      · intro h
        by_cases h6 : w < 6
        · exact Or.inl h6
        · exact Or.inr ⟨w - 6, Finset.mem_range.mpr (by omega), by omega⟩
    have houtdeg11 : outdeg 11 = 0 := by
      dsimp only [outdeg]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hjL hj11
      have hj6 : j < 6 := by rw [hLg_eq, Finset.mem_range] at hjL; exact hjL
      have hlt := effInputs0_lt C j 11 hj11
      omega
    have hsum11 : ∑ u ∈ Finset.range 11, outdeg u = 12 := by
      have h1 : live.erase C.output = Finset.range 11 := by
        rw [hlive_eq12, hout11]
        ext w; simp only [Finset.mem_erase, Finset.mem_range]; omega
      have h2 : ∑ u ∈ live, outdeg u = 12 := by
        rw [hsum_eq, hLg_eq]
        have : ∀ j ∈ Finset.range 6, (effInputs0 C j).length = 2 := fun j hj =>
          hlen2_all j (Finset.mem_range.mp hj)
        rw [Finset.sum_congr rfl this]; simp
      have h3 : ∑ u ∈ live, outdeg u = outdeg C.output + ∑ u ∈ live.erase C.output, outdeg u :=
        (Finset.add_sum_erase _ _ hout_mem).symm
      rw [h1, hout11, houtdeg11, Nat.zero_add] at h3
      omega
    have houtdeg_ge1 : ∀ u < 11, 1 ≤ outdeg u := by
      intro u hu
      apply houtdeg_pos u
      rw [hlive_eq12, hout11, Finset.mem_erase, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    have hex_wstar : ∃ wStar < 11, outdeg wStar = 2 ∧ ∀ u < 11, u ≠ wStar → outdeg u = 1 := by
      have hnotall1 : ¬ ∀ u ∈ Finset.range 11, outdeg u = 1 := by
        intro hall
        have h := Finset.sum_congr rfl hall
        rw [hsum11, Finset.sum_const, Finset.card_range] at h
        simp at h
      push Not at hnotall1
      obtain ⟨wStar, hwmem, hwne1⟩ := hnotall1
      have hwlt : wStar < 11 := Finset.mem_range.mp hwmem
      have hwge2 : 2 ≤ outdeg wStar := by have := houtdeg_ge1 wStar hwlt; omega
      have hsplit : ∑ u ∈ Finset.range 11, outdeg u =
          outdeg wStar + ∑ u ∈ (Finset.range 11).erase wStar, outdeg u :=
        (Finset.add_sum_erase _ _ hwmem).symm
      have hrest_ge : 10 ≤ ∑ u ∈ (Finset.range 11).erase wStar, outdeg u := by
        have hcard : ((Finset.range 11).erase wStar).card = 10 := by
          rw [Finset.card_erase_of_mem hwmem, Finset.card_range]
        calc 10 = ∑ _ ∈ (Finset.range 11).erase wStar, 1 := by rw [Finset.sum_const, hcard]; rfl
          _ ≤ ∑ u ∈ (Finset.range 11).erase wStar, outdeg u :=
              Finset.sum_le_sum fun u hu => houtdeg_ge1 u (Finset.mem_range.mp (Finset.mem_of_mem_erase hu))
      have hw2 : outdeg wStar = 2 := by omega
      have hrest_eq : ∑ u ∈ (Finset.range 11).erase wStar, outdeg u = 10 := by omega
      refine ⟨wStar, hwlt, hw2, ?_⟩
      intro u hult hune
      have humem : u ∈ (Finset.range 11).erase wStar :=
        Finset.mem_erase.mpr ⟨hune, Finset.mem_range.mpr hult⟩
      by_contra hne1
      have huge2 : 2 ≤ outdeg u := by have := houtdeg_ge1 u hult; omega
      have hsp2 := (Finset.add_sum_erase _ outdeg humem).symm
      have hr2 : 9 ≤ ∑ v ∈ ((Finset.range 11).erase wStar).erase u, outdeg v := by
        have hc2 : (((Finset.range 11).erase wStar).erase u).card = 9 := by
          rw [Finset.card_erase_of_mem humem, Finset.card_erase_of_mem hwmem, Finset.card_range]
        calc 9 = ∑ _ ∈ ((Finset.range 11).erase wStar).erase u, 1 := by rw [Finset.sum_const, hc2]; rfl
          _ ≤ ∑ v ∈ ((Finset.range 11).erase wStar).erase u, outdeg v :=
              Finset.sum_le_sum fun v hv =>
                houtdeg_ge1 v (Finset.mem_range.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv)))
      omega
    obtain ⟨wStar, hwStar_lt, _, houtdeg_other⟩ := hex_wstar
    obtain ⟨a0, b0, hab0_eq, hab0_ne, ha0_lt, hb0_lt, _⟩ :=
      effInputs0_len2 C hF 0 (by omega) (hlen2_all 0 (by omega))
    have hwStar_lt6 : wStar < 6 := by
      by_contra hge6
      have ha0_1 : outdeg a0 = 1 := houtdeg_other a0 (by omega) (by omega)
      have hb0_1 : outdeg b0 = 1 := houtdeg_other b0 (by omega) (by omega)
      have honly0 : ∀ u, (u = a0 ∨ u = b0) → ∀ j < 6, u ∈ effInputs0 C j → j = 0 := by
        intro u hu j hj6 huj
        have h1 : outdeg u = 1 := by rcases hu with rfl | rfl <;> assumption
        have h0in : u ∈ effInputs0 C 0 := by rw [hab0_eq]; rcases hu with rfl | rfl <;> simp
        dsimp only [outdeg] at h1
        obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
        have hm0 : 0 ∈ Lg.filter (fun j => u ∈ effInputs0 C j) :=
          Finset.mem_filter.mpr ⟨by rw [hLg_eq]; simp, h0in⟩
        have hmj : j ∈ Lg.filter (fun j => u ∈ effInputs0 C j) :=
          Finset.mem_filter.mpr ⟨by rw [hLg_eq, Finset.mem_range]; exact hj6, huj⟩
        rw [hk, Finset.mem_singleton] at hm0 hmj
        rw [hmj, ← hm0]
      let g0 : Bool → Bool → Bool := fun u v =>
        wval C (fun i => if i = ⟨a0, ha0_lt⟩ then u else if i = ⟨b0, hb0_lt⟩ then v else false) 6
      have h6_dep : ∀ x : Fin 6 → Bool, wval C x 6 = g0 (x ⟨a0, ha0_lt⟩) (x ⟨b0, hb0_lt⟩) := by
        intro x
        dsimp only [g0]
        apply effInputs0_congr C hF 0 (by omega)
        intro u hu
        rw [hab0_eq] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hueq | hueq
        · rw [hueq, wval_lt C x a0 ha0_lt, wval_lt C _ a0 ha0_lt]; simp
        · rw [hueq, wval_lt C x b0 hb0_lt, wval_lt C _ b0 hb0_lt]
          have hne : (⟨b0, hb0_lt⟩ : Fin 6) ≠ ⟨a0, ha0_lt⟩ := fun h => hab0_ne (Fin.mk.inj h).symm
          simp [hne]
      have hne_fin : (⟨a0, ha0_lt⟩ : Fin 6) ≠ ⟨b0, hb0_lt⟩ := fun h => hab0_ne (Fin.mk.inj h)
      obtain ⟨x, y, hagree, hgeq, hne⟩ := target_three_cofactors ⟨a0, ha0_lt⟩ ⟨b0, hb0_lt⟩ hne_fin g0
      have hw_eq : ∀ w < 12, w ≠ a0 → w ≠ b0 → wval C x w = wval C y w := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw12 hna hnb
          by_cases h6 : w < 6
          · rw [wval_lt C x w h6, wval_lt C y w h6]
            exact hagree ⟨w, h6⟩ (fun h => hna (congrArg Fin.val h)) (fun h => hnb (congrArg Fin.val h))
          · by_cases hw6 : w = 6
            · subst hw6; rw [h6_dep x, h6_dep y]; exact hgeq
            · have hw_eq' : w = 6 + (w - 6) := by omega
              rw [hw_eq']
              apply effInputs0_congr C hF (w - 6) (by omega)
              intro u hu
              have hult : u < w := by have := effInputs0_lt C (w - 6) u hu; omega
              have huna : u ≠ a0 := fun h => by
                have := honly0 u (Or.inl h) (w - 6) (by omega) hu; omega
              have hunb : u ≠ b0 := fun h => by
                have := honly0 u (Or.inr h) (w - 6) (by omega) hu; omega
              exact ih u hult (by omega) huna hunb
      have h11 := hw_eq 11 (by omega) (by omega) (by omega)
      rw [← hout11, hwval_out x, hwval_out y] at h11
      exact hne h11
    -- Every gate wire 6..10 has outdeg = 1, so unfolding C from wire 11 gives a MonoTree with ≤ 7 leaves
    have hgate_out1 : ∀ w, 6 ≤ w → w < 11 → outdeg w = 1 := fun w h6 h11 =>
      houtdeg_other w h11 (by omega)
    have hgate_unique_reader : ∀ w, 6 ≤ w → w < 11 → ∀ j1 < 6, ∀ j2 < 6,
        w ∈ effInputs0 C j1 → w ∈ effInputs0 C j2 → j1 = j2 := by
      intro w h6 h11 j1 hj1 j2 hj2 hw1 hw2
      have h1 := hgate_out1 w h6 h11
      dsimp only [outdeg] at h1
      obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
      have hm1 : j1 ∈ Lg.filter (fun j => w ∈ effInputs0 C j) :=
        Finset.mem_filter.mpr ⟨by rw [hLg_eq, Finset.mem_range]; exact hj1, hw1⟩
      have hm2 : j2 ∈ Lg.filter (fun j => w ∈ effInputs0 C j) :=
        Finset.mem_filter.mpr ⟨by rw [hLg_eq, Finset.mem_range]; exact hj2, hw2⟩
      rw [hk, Finset.mem_singleton] at hm1 hm2
      rw [hm1, hm2]
    have hbuild : ∀ w < 12,
        ∃ (T : MonoTree) (ns : List ℕ),
          (∀ x, T.eval x = wval C x w) ∧
          ns.length = T.nodes ∧
          ns.Nodup ∧
          (∀ k ∈ ns, k < 6 ∧ 6 + k ∈ reach C w) := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw12
        by_cases h6 : w < 6
        · refine ⟨MonoTree.var ⟨w, h6⟩, [], ?_, rfl, List.nodup_nil, by simp⟩
          intro x; rw [MonoTree.eval, wval_lt C x w h6]
        · let j := w - 6
          have hj6 : j < 6 := by omega
          have hw_eq : w = 6 + j := by omega
          obtain ⟨a, b, hab_eq, hab_ne, ha_lt, hb_lt, hop⟩ :=
            effInputs0_len2 C hF j (by omega) (hlen2_all j hj6)
          obtain ⟨Ta, nsa, hTa_ev, hTa_len, hTa_nd, hTa_mem⟩ := ih a (by omega) (by omega)
          obtain ⟨Tb, nsb, hTb_ev, hTb_len, hTb_nd, hTb_mem⟩ := ih b (by omega) (by omega)
          have hdisj_ns : List.Disjoint nsa nsb := by
            intro k hka hkb
            let common := (reach C a ∩ reach C b).filter (6 ≤ ·)
            have h6k_a : 6 + k ∈ reach C a := (hTa_mem k hka).2
            have h6k_b : 6 + k ∈ reach C b := (hTb_mem k hkb).2
            have hcom_ne : common.Nonempty :=
              ⟨6 + k, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨h6k_a, h6k_b⟩, by omega⟩⟩
            let umax := common.max' hcom_ne
            have humax_f := Finset.max'_mem common hcom_ne
            have humax_a : umax ∈ reach C a := (Finset.mem_inter.mp (Finset.mem_filter.mp humax_f).1).1
            have humax_b : umax ∈ reach C b := (Finset.mem_inter.mp (Finset.mem_filter.mp humax_f).1).2
            have humax_ge6 : 6 ≤ umax := (Finset.mem_filter.mp humax_f).2
            have humax_lt : umax < 6 + j := by have := mem_reach_le C a umax humax_a; omega
            have ha_mem : a ∈ effInputs0 C j := by rw [hab_eq]; simp
            have hb_mem : b ∈ effInputs0 C j := by rw [hab_eq]; simp
            by_cases h1 : umax = a
            · obtain ⟨j1, hj1_lt, hj1_rb, hj1_u⟩ := reach_has_reader C b umax humax_b (by rw [h1]; exact hab_ne)
              have hj1_le : 6 + j1 ≤ b := mem_reach_le C b (6 + j1) hj1_rb
              have heq := hgate_unique_reader umax humax_ge6 (by omega) j1 (by omega) j hj6 hj1_u (h1 ▸ ha_mem)
              omega
            · by_cases h2 : umax = b
              · obtain ⟨j1, hj1_lt, hj1_ra, hj1_u⟩ := reach_has_reader C a umax humax_a h1
                have hj1_le : 6 + j1 ≤ a := mem_reach_le C a (6 + j1) hj1_ra
                have heq := hgate_unique_reader umax humax_ge6 (by omega) j1 (by omega) j hj6 hj1_u (h2 ▸ hb_mem)
                omega
              · obtain ⟨j1, hj1_lt, hj1_ra, hj1_u⟩ := reach_has_reader C a umax humax_a h1
                obtain ⟨j2, hj2_lt, hj2_rb, hj2_u⟩ := reach_has_reader C b umax humax_b h2
                have heq := hgate_unique_reader umax humax_ge6 (by omega) j1 (by omega) j2 (by omega) hj1_u hj2_u
                subst heq
                have hmem_c : 6 + j1 ∈ common :=
                  Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hj1_ra, hj2_rb⟩, by omega⟩
                have hle_max := Finset.le_max' common (6 + j1) hmem_c
                have hlt_u := effInputs0_lt C j1 umax hj1_u
                omega
          have hj_not_a : j ∉ nsa := fun h => by
            have := mem_reach_le C a (6 + j) (hTa_mem j h).2; omega
          have hj_not_b : j ∉ nsb := fun h => by
            have := mem_reach_le C b (6 + j) (hTb_mem j h).2; omega
          have hnd : (j :: (nsa ++ nsb)).Nodup := by
            rw [List.nodup_cons, List.nodup_append]
            exact ⟨fun h => (List.mem_append.mp h).elim hj_not_a hj_not_b, hTa_nd, hTb_nd,
              fun x hx y hy hxy => hdisj_ns hx (hxy ▸ hy)⟩
          have hmem : ∀ k ∈ j :: (nsa ++ nsb), k < 6 ∧ 6 + k ∈ reach C w := by
            intro k hk
            rw [List.mem_cons, List.mem_append] at hk
            rcases hk with rfl | hka | hkb
            · exact ⟨hj6, by rw [← hw_eq]; exact mem_reach_self C w (by omega)⟩
            · exact ⟨(hTa_mem k hka).1, by
                rw [hw_eq]
                exact reach_subset_of_effInput C j a (by omega) (by rw [hab_eq]; simp) (hTa_mem k hka).2⟩
            · exact ⟨(hTb_mem k hkb).1, by
                rw [hw_eq]
                exact reach_subset_of_effInput C j b (by omega) (by rw [hab_eq]; simp) (hTb_mem k hkb).2⟩
          rcases hop with ⟨_, hev⟩ | ⟨_, hev⟩
          · refine ⟨MonoTree.and Ta Tb, j :: (nsa ++ nsb), ?_, ?_, hnd, hmem⟩
            · intro x; rw [MonoTree.eval, hTa_ev x, hTb_ev x, hw_eq, hev x]
            · simp [MonoTree.nodes, hTa_len, hTb_len]; omega
          · refine ⟨MonoTree.or Ta Tb, j :: (nsa ++ nsb), ?_, ?_, hnd, hmem⟩
            · intro x; rw [MonoTree.eval, hTa_ev x, hTb_ev x, hw_eq, hev x]
            · simp [MonoTree.nodes, hTa_len, hTb_len]; omega
    obtain ⟨T, ns, hTev, hTlen, hTnd, hTmem⟩ := hbuild 11 (by omega)
    have hns_le6 : ns.length ≤ 6 := by
      have hsub : ns.toFinset ⊆ Finset.range 6 := by
        intro k hk
        rw [Finset.mem_range]
        exact (hTmem k (List.mem_toFinset.mp hk)).1
      have hcard := Finset.card_le_card hsub
      rw [List.toFinset_card_of_nodup hTnd, Finset.card_range] at hcard
      exact hcard
    have hTleaves : T.leaves ≤ 7 := by
      rw [T.leaves_eq_nodes_add_one]; omega
    exact tree_7_impossible T hTleaves fun x => by
      rw [hTev x, ← hout11, hwval_out x]

end PEqualNP.Outside.L_meta_5484

theorem PEqualNP.Outside.L_meta_5484 :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 3)) t → 7 ≤ t := by
  intro t ht
  by_contra hlt
  have hle : t ≤ 6 := by omega
  obtain ⟨C, hF, hS, heval⟩ := ht
  exact PEqualNP.Outside.L_meta_5484.no_circuit_le6 C hF (le_trans hS hle) heval
