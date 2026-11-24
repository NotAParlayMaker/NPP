import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3477

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadK

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma ao2_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧
    C.gates[j].inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := hAO2.1 _ hmem
  have hlen : C.gates[j].inputs.length = 2 := hAO2.2.2 _ hmem
  have hgat : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  have hin : C.gates[j].inputs = [opnd C j 0, opnd C j 1] := by
    have h2 := list_eq_two hlen
    simpa [opnd, hgat] using h2
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hgat, hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hgat, hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def back (C : Circuit) (n : ℕ) : ℕ → Finset ℕ → Finset ℕ
  | 0, S => S
  | j + 1, S =>
      let S' := if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S
      back C n j S'

lemma subset_back (C : Circuit) (n : ℕ) : ∀ (m : ℕ) (S : Finset ℕ), S ⊆ back C n m S
  | 0, _ => Finset.Subset.refl _
  | j + 1, S => by
    unfold back
    have h1 : S ⊆ if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S := by
      split_ifs
      · intro x hx; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
      · exact Finset.Subset.refl _
    exact h1.trans (subset_back C n j _)

lemma back_ge_iff {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ (m : ℕ) (hm : m ≤ C.gates.length) (S : Finset ℕ) (w : ℕ),
      n + m ≤ w → (w ∈ back C n m S ↔ w ∈ S)
  | 0, _, _, _, _ => Iff.rfl
  | j + 1, hm, S, w, hw => by
    unfold back
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, h0, h1⟩ := ao2_gate hAO2 hj
    have hw' : n + j ≤ w := by omega
    rw [back_ge_iff hAO2 j (by omega) _ w hw']
    split_ifs
    · have hne0 : w ≠ opnd C j 0 := by omega
      have hne1 : w ≠ opnd C j 1 := by omega
      simp [hne0, hne1]
    · rfl

lemma back_closed {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ (m : ℕ) (hm : m ≤ C.gates.length) (S : Finset ℕ) (j : ℕ),
      j < m → n + j ∈ back C n m S →
      opnd C j 0 ∈ back C n m S ∧ opnd C j 1 ∈ back C n m S
  | 0, _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | k + 1, hm, S, j, hj, hmem => by
    unfold back at hmem ⊢
    by_cases hjk : j = k
    · subst hjk
      have hge : n + j ∈ (if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S) :=
        (back_ge_iff hAO2 j (by omega) _ (n + j) le_rfl).mp hmem
      have hinS : n + j ∈ S := by
        by_contra hnot
        simp [hnot] at hge
      rw [if_pos hinS]
      have hsub := subset_back C n j (insert (opnd C j 0) (insert (opnd C j 1) S))
      exact ⟨hsub (Finset.mem_insert_self _ _),
        hsub (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
    · exact back_closed hAO2 k (by omega) _ j (by omega) hmem

lemma back_bound_step {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (S : Finset ℕ) :
    ((if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S).filter (· < n + j)).card +
      (S.filter (fun w => n + (j + 1) ≤ w)).card ≤
    (S.filter (· < n + (j + 1))).card +
      ((if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S).filter (fun w => n + j ≤ w)).card := by
  obtain ⟨_, _, h0, h1⟩ := ao2_gate hAO2 hj
  by_cases hmem : n + j ∈ S
  · rw [if_pos hmem]
    have hE : ((insert (opnd C j 0) (insert (opnd C j 1) S)).filter (fun w => n + j ≤ w)) =
        insert (n + j) (S.filter (fun w => n + (j + 1) ≤ w)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | rfl | hw, hge⟩
        · omega
        · omega
        · by_cases heq : w = n + j
          · exact Or.inl heq
          · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hge⟩)
        · exact ⟨Or.inr (Or.inr hmem), le_rfl⟩
        · exact ⟨Or.inr (Or.inr hw), by omega⟩
    have hnotE : n + j ∉ S.filter (fun w => n + (j + 1) ≤ w) := by
      simp only [Finset.mem_filter]; omega
    have hEcard : ((insert (opnd C j 0) (insert (opnd C j 1) S)).filter (fun w => n + j ≤ w)).card =
        (S.filter (fun w => n + (j + 1) ≤ w)).card + 1 := by
      rw [hE, Finset.card_insert_of_notMem hnotE]
    have hF1 : (S.filter (· < n + (j + 1))) = insert (n + j) (S.filter (· < n + j)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases heq : w = n + j
        · exact Or.inl heq
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨hmem, by omega⟩
        · exact ⟨hw, by omega⟩
    have hnotF : n + j ∉ S.filter (· < n + j) := by
      simp only [Finset.mem_filter]; omega
    have hF1card : (S.filter (· < n + (j + 1))).card = (S.filter (· < n + j)).card + 1 := by
      rw [hF1, Finset.card_insert_of_notMem hnotF]
    have hFsub : ((insert (opnd C j 0) (insert (opnd C j 1) S)).filter (· < n + j)) ⊆
        insert (opnd C j 0) (insert (opnd C j 1) (S.filter (· < n + j))) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_insert] at hw ⊢
      rcases hw with ⟨rfl | rfl | hw, hlt⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hw, hlt⟩)
    have hF2card : ((insert (opnd C j 0) (insert (opnd C j 1) S)).filter (· < n + j)).card ≤
        (S.filter (· < n + j)).card + 2 := by
      have c1 := Finset.card_le_card hFsub
      have c2 := Finset.card_insert_le (opnd C j 0) (insert (opnd C j 1) (S.filter (· < n + j)))
      have c3 := Finset.card_insert_le (opnd C j 1) (S.filter (· < n + j))
      omega
    omega
  · rw [if_neg hmem]
    have hE : S.filter (fun w => n + j ≤ w) = S.filter (fun w => n + (j + 1) ≤ w) := by
      ext w; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hge⟩
        have hne : w ≠ n + j := fun e => hmem (e ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hge⟩; exact ⟨hw, by omega⟩
    have hF : S.filter (· < n + j) = S.filter (· < n + (j + 1)) := by
      ext w; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩; exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ n + j := fun e => hmem (e ▸ hw)
        exact ⟨hw, by omega⟩
    rw [hE, hF]

lemma back_bound {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ (m : ℕ) (hm : m ≤ C.gates.length) (S : Finset ℕ),
      ((back C n m S).filter (· < n)).card + (S.filter (fun w => n + m ≤ w)).card ≤
        (S.filter (· < n + m)).card + ((back C n m S).filter (fun w => n ≤ w)).card
  | 0, _, S => by simp [back]
  | j + 1, hm, S => by
    unfold back
    dsimp only
    let S' := if n + j ∈ S then insert (opnd C j 0) (insert (opnd C j 1) S) else S
    have hstep : (S'.filter (· < n + j)).card + (S.filter (fun w => n + (j + 1) ≤ w)).card ≤
        (S.filter (· < n + (j + 1))).card + (S'.filter (fun w => n + j ≤ w)).card :=
      back_bound_step hAO2 j (by omega) S
    have hih : ((back C n j S').filter (· < n)).card + (S'.filter (fun w => n + j ≤ w)).card ≤
        (S'.filter (· < n + j)).card + ((back C n j S').filter (fun w => n ≤ w)).card :=
      back_bound hAO2 j (by omega) S'
    change ((back C n j S').filter (· < n)).card + (S.filter (fun w => n + (j + 1) ≤ w)).card ≤
      (S.filter (· < n + (j + 1))).card + ((back C n j S').filter (fun w => n ≤ w)).card
    omega

lemma back_lt_bound {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ (m : ℕ) (hm : m ≤ C.gates.length) (S : Finset ℕ),
      (∀ w ∈ S, w < n + C.gates.length) →
      ∀ w ∈ back C n m S, w < n + C.gates.length
  | 0, _, _, hS, w, hw => hS w hw
  | j + 1, hm, S, hS, w, hw => by
    unfold back at hw
    obtain ⟨_, _, h0, h1⟩ := ao2_gate hAO2 (by omega : j < C.gates.length)
    apply back_lt_bound hAO2 j (by omega) _ _ w hw
    intro u hu
    split_ifs at hu
    · simp only [Finset.mem_insert] at hu
      rcases hu with rfl | rfl | hu
      · omega
      · omega
      · exact hS u hu
    · exact hS u hu

lemma back_inputs_card {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (hout : C.output < n + C.gates.length) :
    ((back C n C.gates.length {C.output}).filter (· < n)).card ≤ C.size + 1 := by
  have hb := back_bound hAO2 C.gates.length le_rfl {C.output}
  have hS1eq : ({C.output} : Finset ℕ).filter (· < n + C.gates.length) = {C.output} := by
    ext w; simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hout⟩⟩
  have hS1 : (({C.output} : Finset ℕ).filter (· < n + C.gates.length)).card = 1 := by
    rw [hS1eq]; simp
  have hS2eq : ({C.output} : Finset ℕ).filter (fun w => n + C.gates.length ≤ w) = ∅ := by
    ext w; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, hge⟩; omega
  have hS2 : (({C.output} : Finset ℕ).filter (fun w => n + C.gates.length ≤ w)).card = 0 := by
    rw [hS2eq]; simp
  have hRsub : (back C n C.gates.length {C.output}).filter (fun w => n ≤ w) ⊆
      Finset.Ico n (n + C.gates.length) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_Ico] at hw ⊢
    exact ⟨hw.2, back_lt_bound hAO2 C.gates.length le_rfl {C.output}
      (fun u hu => by simp only [Finset.mem_singleton] at hu; omega) w hw.1⟩
  have hRcard : ((back C n C.gates.length {C.output}).filter (fun w => n ≤ w)).card ≤ C.gates.length := by
    have c := Finset.card_le_card hRsub
    simpa [Nat.card_Ico] using c
  change ((back C n C.gates.length {C.output}).filter (· < n)).card ≤ C.gates.length + 1
  rw [hS1, hS2] at hb
  omega

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma foldl_len {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (gs.foldl (fun l g => l ++ [step l g]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_getD_lt {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun l g => l ++ [step l g]) w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma foldl_getD_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ u v : List α, (∀ i < w.length + j, u.getD i d = v.getD i d) →
      step u gs[j] = step v gs[j]) :
    (gs.foldl (fun l g => l ++ [step l g]) w).getD (w.length + j) d =
      step (gs.foldl (fun l g => l ++ [step l g]) w) gs[j] := by
  let pre := (gs.take j).foldl (fun l g => l ++ [step l g]) w
  have hplen : pre.length = w.length + j := by
    simp [pre, foldl_len, Nat.min_eq_left hj.le]
  have hsplit : gs.foldl (fun l g => l ++ [step l g]) w =
      (gs[j] :: gs.drop (j + 1)).foldl (fun l g => l ++ [step l g]) pre := by
    have h1 := List.take_append_drop j gs
    conv_lhs => rw [← h1, List.foldl_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j,
      (gs.foldl (fun l g => l ++ [step l g]) w).getD i d = pre.getD i d := by
    intro i hi
    rw [hsplit]
    exact foldl_getD_lt step _ pre d i (by omega)
  have hval : (gs.foldl (fun l g => l ++ [step l g]) w).getD (w.length + j) d =
      step pre gs[j] := by
    rw [hsplit, List.foldl_cons, foldl_getD_lt step _ _ d (w.length + j) (by simp [hplen])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp
  rw [hval]
  exact hstep pre _ (fun i hi => (hpre i hi).symm)

lemma lp_gate_eq {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (isLine : ℕ → Bool) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (linearParts C isLine x).getD (n + j) (false, false) =
      linStep (linearParts C isLine x) C.gates[j] := by
  have hinit : ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)).length = n := by
    simp [hx]
  have heq := foldl_getD_gate linStep C.gates
    ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))
    (false, false) j hj (by
      intro u v huv
      unfold linStep
      obtain ⟨_, hin, h0, h1⟩ := ao2_gate hAO2 hj
      rw [hinit] at huv
      rw [hin]
      simp only [List.map_cons, List.map_nil, huv _ h0, huv _ h1])
  rw [hinit] at heq
  exact heq

lemma wires_gate_eq {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false = boolStep (C.wires x) C.gates[j] := by
  have heq := foldl_getD_gate boolStep C.gates x false j hj (by
    intro u v huv
    unfold boolStep
    obtain ⟨_, hin, h0, h1⟩ := ao2_gate hAO2 hj
    rw [hx] at huv
    rw [hin]
    simp only [List.map_cons, List.map_nil, huv _ h0, huv _ h1])
  rw [hx] at heq
  exact heq

lemma lp_input_eq (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (linearParts C isLine x).getD i (false, false) =
      if isLine i then (false, x.getD i false) else (x.getD i false, false) := by
  change (C.gates.foldl (fun l g => l ++ [linStep l g])
    ((x.zipIdx).map fun (b, k) => if isLine k then (false, b) else (b, false))).getD i (false, false) = _
  have hlen : ((x.zipIdx).map fun (b, k) => if isLine k then (false, b) else (b, false)).length = x.length := by
    simp
  rw [foldl_getD_lt linStep C.gates _ (false, false) i (by omega)]
  rw [List.getD_eq_getElem _ _ (by omega), List.getElem_map]
  simp only [List.getElem_zipIdx, zero_add]
  have hx' : x.getD i false = x[i] := List.getD_eq_getElem _ _ hi
  rw [hx']

lemma wires_input_eq (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_getD_lt boolStep C.gates x false i hi

lemma linStep_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (w : List (Bool × Bool))
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    let a := w.getD (opnd C j 0) (false, false)
    let b := w.getD (opnd C j 1) (false, false)
    linStep w C.gates[j] = (a.1 && b.1, (a.1 && b.2) || (a.2 && b.1)) := by
  obtain ⟨_, hin, _, _⟩ := ao2_gate hAO2 hj
  unfold linStep
  rw [hin, hop]
  simp

lemma linStep_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (w : List (Bool × Bool))
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    let a := w.getD (opnd C j 0) (false, false)
    let b := w.getD (opnd C j 1) (false, false)
    linStep w C.gates[j] = (a.1 || b.1, a.2 || b.2) := by
  obtain ⟨_, hin, _, _⟩ := ao2_gate hAO2 hj
  unfold linStep
  rw [hin, hop]
  simp

lemma boolStep_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (w : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) :
    boolStep w C.gates[j] = (w.getD (opnd C j 0) false && w.getD (opnd C j 1) false) := by
  obtain ⟨_, hin, _, _⟩ := ao2_gate hAO2 hj
  unfold boolStep
  rw [hin, hop]
  simp [GateOp.eval]

lemma boolStep_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (w : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.or) :
    boolStep w C.gates[j] = (w.getD (opnd C j 0) false || w.getD (opnd C j 1) false) := by
  obtain ⟨_, hin, _, _⟩ := ao2_gate hAO2 hj
  unfold boolStep
  rw [hin, hop]
  simp [GateOp.eval]

lemma bool_and_le (a1 a2 b1 b2 wa wb : Bool) (h1 : a1 ≤ wa) (h2 : a2 ≤ wa) (h3 : b1 ≤ wb) (h4 : b2 ≤ wb) :
    (a1 && b1) ≤ (wa && wb) ∧ ((a1 && b2) || (a2 && b1)) ≤ (wa && wb) := by
  revert h1 h2 h3 h4; cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases wa <;> cases wb <;> decide

lemma bool_or_le (a1 a2 b1 b2 wa wb : Bool) (h1 : a1 ≤ wa) (h2 : a2 ≤ wa) (h3 : b1 ≤ wb) (h4 : b2 ≤ wb) :
    (a1 || b1) ≤ (wa || wb) ∧ (a2 || b2) ≤ (wa || wb) := by
  revert h1 h2 h3 h4; cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases wa <;> cases wb <;> decide

lemma lp_le_wires {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (isLine : ℕ → Bool) (x : List Bool)
    (hx : x.length = n) :
    ∀ w < n + C.gates.length,
      ((linearParts C isLine x).getD w (false, false)).1 ≤ (C.wires x).getD w false ∧
      ((linearParts C isLine x).getD w (false, false)).2 ≤ (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [lp_input_eq C isLine x w (by omega), wires_input_eq C x w (by omega)]
      split_ifs <;> simp
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate hAO2 hj
      have ih0 := ih (opnd C j 0) (by omega) (by omega)
      have ih1 := ih (opnd C j 1) (by omega) (by omega)
      rw [hwj, lp_gate_eq hAO2 isLine x hx j hj, wires_gate_eq hAO2 x hx j hj]
      rcases hop with hand | hor
      · rw [linStep_and hAO2 _ j hj hand, boolStep_and hAO2 _ j hj hand]
        exact bool_and_le _ _ _ _ _ _ ih0.1 ih0.2 ih1.1 ih1.2
      · rw [linStep_or hAO2 _ j hj hor, boolStep_or hAO2 _ j hj hor]
        exact bool_or_le _ _ _ _ _ _ ih0.1 ih0.2 ih1.1 ih1.2

lemma lp_agree_on_closed {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (isLine : ℕ → Bool)
    (R : Finset ℕ) (hclosed : ∀ j < C.gates.length, n + j ∈ R → opnd C j 0 ∈ R ∧ opnd C j 1 ∈ R)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ i < n, i ∈ R → x.getD i false = y.getD i false) :
    ∀ w < n + C.gates.length, w ∈ R →
      (linearParts C isLine x).getD w (false, false) =
      (linearParts C isLine y).getD w (false, false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmem
    by_cases hlt : w < n
    · rw [lp_input_eq C isLine x w (by omega), lp_input_eq C isLine y w (by omega), hxy w hlt hmem]
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hmem ⊢
      obtain ⟨h0R, h1R⟩ := hclosed j hj hmem
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate hAO2 hj
      rw [lp_gate_eq hAO2 isLine x hx j hj, lp_gate_eq hAO2 isLine y hy j hj]
      rcases hop with hand | hor
      · rw [linStep_and hAO2 _ j hj hand, linStep_and hAO2 _ j hj hand,
          ih (opnd C j 0) (by omega) (by omega) h0R, ih (opnd C j 1) (by omega) (by omega) h1R]
      · rw [linStep_or hAO2 _ j hj hor, linStep_or hAO2 _ j hj hor,
          ih (opnd C j 0) (by omega) (by omega) h0R, ih (opnd C j 1) (by omega) (by omega) h1R]

lemma lp_part1_false_of_no_marked {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (isLine : ℕ → Bool)
    (R : Finset ℕ) (hclosed : ∀ j < C.gates.length, n + j ∈ R → opnd C j 0 ∈ R ∧ opnd C j 1 ∈ R)
    (x : List Bool) (hx : x.length = n)
    (hno : ∀ i < n, i ∈ R → isLine i = false) :
    ∀ w < n + C.gates.length, w ∈ R →
      ((linearParts C isLine x).getD w (false, false)).2 = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmem
    by_cases hlt : w < n
    · rw [lp_input_eq C isLine x w (by omega), hno w hlt hmem]
      simp
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      rw [hwj] at hmem ⊢
      obtain ⟨h0R, h1R⟩ := hclosed j hj hmem
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate hAO2 hj
      rw [lp_gate_eq hAO2 isLine x hx j hj]
      have z0 := ih (opnd C j 0) (by omega) (by omega) h0R
      have z1 := ih (opnd C j 1) (by omega) (by omega) h1R
      rcases hop with hand | hor
      · rw [linStep_and hAO2 _ j hj hand]; dsimp only; rw [z0, z1]; simp
      · rw [linStep_or hAO2 _ j hj hor]; dsimp only; rw [z0, z1]; simp

lemma main_proof (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq2 : 2 ≤ q) (hq9 : q ≤ 9)
    (hdeg : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (hAO2 : IsAO2 (N + N) C)
    (hsound : ∀ (z : Fin (N + N) → Bool),
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬ ∃ (p l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card { e : Fin N × Fin N // I e.1 e.2 ∧
      lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val) = true } ≤
      10 * C.size := by
  let isPt : ℕ → Bool := fun k => decide (k < N)
  let S : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ lineSingle C (N + N) isPt e.1.val (N + e.2.val) = true)
  have hcardS : Fintype.card { e : Fin N × Fin N // I e.1 e.2 ∧
      lineSingle C (N + N) isPt e.1.val (N + e.2.val) = true } = S.card := by
    rw [Fintype.card_subtype]
  rw [hcardS]
  by_cases hEmpty : S = ∅
  · rw [hEmpty]; simp
  obtain ⟨⟨p0, l0⟩, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hls0 : lineSingle C (N + N) isPt p0.val (N + l0.val) = true := (Finset.mem_filter.mp he0).2.2
  have hout_lt : C.output < N + N + C.gates.length := by
    by_contra hge
    have hlen : (linearParts C isPt ((List.range (N + N)).map fun i => i == p0.val || i == N + l0.val)).length =
        N + N + C.gates.length := by
      unfold linearParts
      rw [foldl_len]
      simp
    have hdef : (linearParts C isPt ((List.range (N + N)).map fun i => i == p0.val || i == N + l0.val)).getD
        C.output (false, false) = (false, false) :=
      List.getD_eq_default _ _ (by omega)
    unfold lineSingle at hls0
    rw [hdef] at hls0
    cases hls0
  let R := back C (N + N) C.gates.length {C.output}
  have houtR : C.output ∈ R := subset_back C (N + N) C.gates.length {C.output} (Finset.mem_singleton_self _)
  have hRclosed : ∀ j < C.gates.length, N + N + j ∈ R → opnd C j 0 ∈ R ∧ opnd C j 1 ∈ R :=
    fun j hj hm => back_closed hAO2 C.gates.length le_rfl {C.output} j hj hm
  have hexPt : ∃ p : ℕ, p < N ∧ p ∈ R := by
    by_contra hno
    push_neg at hno
    have hfalse := lp_part1_false_of_no_marked hAO2 isPt R hRclosed
      ((List.range (N + N)).map fun i => i == p0.val || i == N + l0.val) (by simp)
      (fun i _ hiR => by
        by_cases hlt : i < N
        · exact absurd hiR (hno i hlt)
        · simp [isPt, hlt])
      C.output hout_lt houtR
    unfold lineSingle at hls0
    rw [hfalse] at hls0
    cases hls0
  obtain ⟨pHit, hpHit_lt, hpHit_R⟩ := hexPt
  have hline_in_R : ∀ e ∈ S, N + e.2.val ∈ R := by
    intro ⟨p, l⟩ he
    have hls : lineSingle C (N + N) isPt p.val (N + l.val) = true := (Finset.mem_filter.mp he).2.2
    by_contra hnotR
    let xPair : List Bool := (List.range (N + N)).map fun i => i == p.val || i == N + l.val
    let zOnly : Fin (N + N) → Bool := fun k => decide (k.val = p.val)
    let xOnly : List Bool := List.ofFn zOnly
    have hagree : ∀ i < N + N, i ∈ R → xPair.getD i false = xOnly.getD i false := by
      intro i hi hiR
      have hneL : i ≠ N + l.val := fun e => hnotR (e ▸ hiR)
      rw [List.getD_eq_getElem _ _ (by simp [xPair, hi]),
        List.getD_eq_getElem _ _ (by simp [xOnly, hi])]
      simp only [xPair, xOnly, zOnly, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      have hb : (i == N + l.val) = false := by simp [hneL]
      rw [hb, Bool.or_false]
      by_cases hep : i = p.val <;> simp [hep]
    have heq := lp_agree_on_closed hAO2 isPt R hRclosed xPair xOnly (by simp [xPair]) (by simp [xOnly])
      hagree C.output hout_lt houtR
    have hle := (lp_le_wires hAO2 isPt xOnly (by simp [xOnly]) C.output hout_lt).2
    have htrue : (C.wires xOnly).getD C.output false = true := by
      have h1 : ((linearParts C isPt xOnly).getD C.output (false, false)).2 = true := by
        rw [← heq]; exact hls
      rw [h1] at hle
      cases hw : (C.wires xOnly).getD C.output false
      · rw [hw] at hle; exact hle rfl
      · rfl
    have hzeroLines : Fintype.card { l' : Fin N // zOnly (Fin.natAdd N l') = true } ≤ q := by
      have hemp : IsEmpty { l' : Fin N // zOnly (Fin.natAdd N l') = true } := by
        refine ⟨fun ⟨l', hl'⟩ => ?_⟩
        simp only [zOnly, Fin.val_natAdd, decide_eq_true_eq] at hl'
        omega
      rw [Fintype.card_eq_zero]
      omega
    have hnoInc : ¬ ∃ (p' l' : Fin N), I p' l' ∧ zOnly (Fin.castAdd N p') = true ∧
        zOnly (Fin.natAdd N l') = true := by
      rintro ⟨p', l', _, _, hl'⟩
      simp only [zOnly, Fin.val_natAdd, decide_eq_true_eq] at hl'
      omega
    have hsf := hsound zOnly hzeroLines hnoInc
    unfold circuitFun Circuit.eval at hsf
    change (C.wires xOnly).getD C.output false = false at hsf
    rw [htrue] at hsf
    cases hsf
  let A : Finset (Fin N) := Finset.univ.filter (fun l => N + l.val ∈ R)
  have hAcard : A.card ≤ C.size := by
    have hinp : (R.filter (· < N + N)).card ≤ C.size + 1 := back_inputs_card hAO2 hout_lt
    let img : Finset ℕ := insert pHit (A.image (fun l : Fin N => N + l.val))
    have himgSub : img ⊆ R.filter (· < N + N) := by
      intro w hw
      simp only [img, Finset.mem_insert, Finset.mem_image] at hw
      simp only [Finset.mem_filter]
      rcases hw with rfl | ⟨l, hl, rfl⟩
      · exact ⟨hpHit_R, by omega⟩
      · exact ⟨(Finset.mem_filter.mp hl).2, by omega⟩
    have hpNotIn : pHit ∉ A.image (fun l : Fin N => N + l.val) := by
      simp only [Finset.mem_image]
      rintro ⟨l, _, heq⟩
      omega
    have hinj : Function.Injective (fun l : Fin N => N + l.val) := by
      intro a b hab
      dsimp only at hab
      exact Fin.ext (by omega)
    have himgCard : img.card = A.card + 1 := by
      rw [show img = insert pHit (A.image (fun l : Fin N => N + l.val)) from rfl,
        Finset.card_insert_of_notMem hpNotIn, Finset.card_image_of_injective A hinj]
    have hle := Finset.card_le_card himgSub
    omega
  let B : Finset (Fin N × Fin N) := A.biUnion (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).map
    ⟨fun p => (p, l), fun a b h => by cases h; rfl⟩)
  have hSB : S ⊆ B := by
    intro ⟨p, l⟩ he
    have hlR := hline_in_R (p, l) he
    have hI : I p l := (Finset.mem_filter.mp he).2.1
    simp only [B, Finset.mem_biUnion, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hlR⟩, p, hI, rfl⟩
  have hBcard : B.card ≤ ∑ l ∈ A, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
    calc B.card ≤ ∑ l ∈ A, ((Finset.univ.filter (fun p : Fin N => I p l)).map
            ⟨fun p => (p, l), fun a b h => by cases h; rfl⟩).card := Finset.card_biUnion_le
      _ = ∑ l ∈ A, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
            refine Finset.sum_congr rfl (fun l _ => Finset.card_map _)
  have hsum : ∑ l ∈ A, (Finset.univ.filter (fun p : Fin N => I p l)).card = A.card * (q + 1) := by
    have hterm : ∀ l ∈ A, (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
      intro l _
      rw [← Fintype.card_subtype]
      exact hdeg l
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hS_le : S.card ≤ A.card * (q + 1) := (Finset.card_le_card hSB).trans (hBcard.trans hsum.le)
  have hmul : A.card * (q + 1) ≤ C.size * 10 := Nat.mul_le_mul hAcard (by omega)
  omega

end PEqualNP.Outside.L_meta_3477

theorem PEqualNP.Outside.L_meta_3477 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (9 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 hq2 hq9 _ hdeg _ hAO2 hsound
  exact PEqualNP.Outside.L_meta_3477.main_proof x1 x2 x3 x5 hq2 hq9 hdeg hAO2 hsound
