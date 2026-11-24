import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3063

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp [List.foldl_cons, ih, step]; omega

lemma getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma foldl_step_getD_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    simp only [List.foldl_cons]
    rw [ih (step w g) i (by simp [step]; omega), getD_step_lt w g i h]

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_step_getD_lt C.gates x i hi

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hIn : ∀ i ∈ (gateAt C j).inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let wj := (C.gates.take j).foldl step x
  have hwj_len : wj.length = x.length + j := by
    rw [foldl_step_len, List.length_take_of_le (Nat.le_of_lt hj)]
  have hwires : C.wires x = (C.gates.drop (j + 1)).foldl step (step wj C.gates[j]) := by
    unfold Circuit.wires
    conv_lhs => rw [hsplit]
    simp only [List.foldl_append, List.foldl_cons]
    rfl
  have h1 : (C.wires x).getD (x.length + j) false = (step wj C.gates[j]).getD (x.length + j) false := by
    rw [hwires]
    exact foldl_step_getD_lt _ _ _ (by simp [step, hwj_len])
  have h2 : (step wj C.gates[j]).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => wj.getD i false) := by
    unfold step
    rw [← hwj_len, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  rw [h1, h2, ← gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < wj.length := by rw [hwj_len]; exact hIn i hi
  have hwires2 : C.wires x = (C.gates.drop j).foldl step wj := by
    unfold Circuit.wires
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append]
    rfl
  rw [hwires2, foldl_step_getD_lt _ _ _ hilt]

def inp {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) : List Bool :=
  List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))

lemma inp_len {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) :
    (inp P L).length = n + m := by
  simp [inp]

lemma inp_getD_pt {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (u : Fin n) :
    (inp P L).getD u.val false = decide (u ∈ P) := by
  unfold inp
  have hu : u.val < (List.ofFn (fun u' : Fin n => decide (u' ∈ P))).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hu, List.getElem?_eq_getElem hu]
  simp

lemma inp_getD_ln {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) (v : Fin m) :
    (inp P L).getD (n + v.val) false = decide (v ∈ L) := by
  unfold inp
  have hle : (List.ofFn (fun u' : Fin n => decide (u' ∈ P))).length ≤ n + v.val := by simp
  have hv : n + v.val - (List.ofFn (fun u' : Fin n => decide (u' ∈ P))).length <
      (List.ofFn (fun v' : Fin m => decide (v' ∈ L))).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle, List.getElem?_eq_getElem hv]
  simp

lemma inp_singleton_eq {n m : ℕ} (p : Fin n) (l : Fin m) :
    (List.ofFn (fun u : Fin n => decide (u = p)) ++ List.ofFn (fun v : Fin m => decide (v = l))) =
      inp ({p} : Finset (Fin n)) ({l} : Finset (Fin m)) := by
  unfold inp
  simp only [Finset.mem_singleton]

lemma card_biUnion_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset β) (F : β → Finset α) (h : ∀ b ∈ S, (F b).card ≤ 1) :
    (S.biUnion F).card ≤ S.card := by
  calc (S.biUnion F).card
    _ ≤ ∑ b ∈ S, (F b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S, 1 := Finset.sum_le_sum h
    _ = S.card := by simp

lemma dag_union_bound_wires {α : Type*} [DecidableEq α] (M : ℕ) (F : ℕ → Finset α)
    (hBase : ∀ w < M, (F w).card ≤ 1) :
    ∀ (s : ℕ), (∀ j < s, ∃ u < M + j, ∃ v < M + j, F (M + j) ⊆ F u ∪ F v) →
      ∀ (W : Finset ℕ), (∀ w ∈ W, w < M + s) →
        (W.biUnion F).card ≤
          ((Finset.range s).filter (fun j => 2 ≤ (F (M + j)).card)).card + W.card := by
  intro s
  induction s with
  | zero =>
    intro _ W hW
    simp only [Nat.add_zero, Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add] at hW ⊢
    exact card_biUnion_le_one W F (fun w hw => hBase w (hW w hw))
  | succ s ih =>
    intro hStep W hW
    have hStep' : ∀ j < s, ∃ u < M + j, ∃ v < M + j, F (M + j) ⊆ F u ∪ F v :=
      fun j hj => hStep j (Nat.lt_succ_of_lt hj)
    let Gs := (Finset.range s).filter (fun j => 2 ≤ (F (M + j)).card)
    let Gs1 := (Finset.range (s + 1)).filter (fun j => 2 ≤ (F (M + j)).card)
    have hGs_sub : Gs ⊆ Gs1 := by
      intro j hj
      simp only [Gs, Gs1, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨Nat.lt_succ_of_lt hj.1, hj.2⟩
    by_cases hMem : M + s ∈ W
    · let W' := W.erase (M + s)
      have hW'_lt : ∀ w ∈ W', w < M + s := by
        intro w hw
        have hne : w ≠ M + s := (Finset.mem_erase.mp hw).1
        have hlt : w < M + (s + 1) := hW w (Finset.mem_of_mem_erase hw)
        omega
      have hW_card : W.card = W'.card + 1 := (Finset.card_erase_add_one hMem).symm
      by_cases hBig : 2 ≤ (F (M + s)).card
      · have hGs1_card : Gs1.card = Gs.card + 1 := by
          have hEq : Gs1 = insert s Gs := by
            ext j
            simp only [Gs, Gs1, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
            constructor
            · rintro ⟨hj, hc⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
              · exact Or.inr ⟨hlt, hc⟩
              · exact Or.inl rfl
            · rintro (hjs | ⟨hlt, hc⟩)
              · rw [hjs]; exact ⟨Nat.lt_succ_self s, hBig⟩
              · exact ⟨Nat.lt_succ_of_lt hlt, hc⟩
          have hNotMem : s ∉ Gs := by simp [Gs]
          rw [hEq]
          exact Finset.card_insert_of_notMem hNotMem
        obtain ⟨u, hu, v, hv, hSub⟩ := hStep s (Nat.lt_succ_self s)
        let W'' := insert u (insert v W')
        have hW''_lt : ∀ w ∈ W'', w < M + s := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hu
          · rcases Finset.mem_insert.mp hw with rfl | hw'
            · exact hv
            · exact hW'_lt w hw'
        have hUnion_sub : W.biUnion F ⊆ W''.biUnion F := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hw_eq : w = M + s
          · subst hw_eq
            rcases Finset.mem_union.mp (hSub hxw) with hxu | hxv
            · exact ⟨u, Finset.mem_insert_self u _, hxu⟩
            · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_self v _), hxv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hw_eq, hw⟩)), hxw⟩
        have hW''_card : W''.card ≤ W'.card + 2 := by
          have c1 : W''.card ≤ (insert v W').card + 1 := Finset.card_insert_le u (insert v W')
          have c2 := Finset.card_insert_le v W'
          omega
        have hIH := ih hStep' W'' hW''_lt
        have hCardLe := Finset.card_le_card hUnion_sub
        change (W.biUnion F).card ≤ Gs1.card + W.card
        change (W''.biUnion F).card ≤ Gs.card + W''.card at hIH
        omega
      · have hSmall : (F (M + s)).card ≤ 1 := by omega
        have hIH := ih hStep' W' hW'_lt
        have hGs_le : Gs.card ≤ Gs1.card := Finset.card_le_card hGs_sub
        have hW_eq : W = insert (M + s) W' := (Finset.insert_erase hMem).symm
        have hBi : W.biUnion F = F (M + s) ∪ W'.biUnion F := by
          conv_lhs => rw [hW_eq]
          exact Finset.biUnion_insert
        have hCardU : (W.biUnion F).card ≤ (F (M + s)).card + (W'.biUnion F).card := by
          rw [hBi]
          exact Finset.card_union_le _ _
        change (W.biUnion F).card ≤ Gs1.card + W.card
        change (W'.biUnion F).card ≤ Gs.card + W'.card at hIH
        omega
    · have hW_lt : ∀ w ∈ W, w < M + s := by
        intro w hw
        have hne : w ≠ M + s := fun h => hMem (h ▸ hw)
        have hlt : w < M + (s + 1) := hW w hw
        omega
      have hIH := ih hStep' W hW_lt
      have hGs_le : Gs.card ≤ Gs1.card := Finset.card_le_card hGs_sub
      change (W.biUnion F).card ≤ Gs1.card + W.card
      change (W.biUnion F).card ≤ Gs.card + W.card at hIH
      omega

lemma dag_union_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (M s : ℕ) (F : ℕ → Finset α)
    (hBase : ∀ w < M, (F w).card ≤ 1)
    (hStep : ∀ j < s, ∃ u < M + j, ∃ v < M + j, F (M + j) ⊆ F u ∪ F v)
    (I : Finset β) (r : β → ℕ) (hr : ∀ t ∈ I, r t < M + s) :
    (I.biUnion (fun t => F (r t))).card ≤
      ((Finset.range s).filter (fun j => 2 ≤ (F (M + j)).card)).card + I.card := by
  let W := I.image r
  have hW : ∀ w ∈ W, w < M + s := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
    exact hr t ht
  have hEq : I.biUnion (fun t => F (r t)) = W.biUnion F := by
    ext x
    simp [W]
  rw [hEq]
  have h1 := dag_union_bound_wires M F hBase s hStep W hW
  have h2 : W.card ≤ I.card := Finset.card_image_le
  omega

def Pset (n m : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => (C.wires (inp ({p} : Finset (Fin n)) (∅ : Finset (Fin m)))).getD w false = true)

def Lset (n m : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun l => (C.wires (inp (∅ : Finset (Fin n)) ({l} : Finset (Fin m)))).getD w false = true)

lemma Pset_card_lt (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n + m) :
    (Pset n m C w).card ≤ 1 := by
  by_cases hwn : w < n
  · have hsub : Pset n m C w ⊆ {⟨w, hwn⟩} := by
      intro p hp
      simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [wires_input C _ w (by rw [inp_len]; exact hw)] at hp
      have heq : w = (⟨w, hwn⟩ : Fin n).val := rfl
      rw [heq, inp_getD_pt] at hp
      simp only [Finset.mem_singleton, decide_eq_true_eq] at hp ⊢
      exact hp.symm
    exact le_trans (Finset.card_le_card hsub) (by simp)
  · have hmlt : w - n < m := by omega
    have hw_eq : w = n + (⟨w - n, hmlt⟩ : Fin m).val := by simp; omega
    have hemp : Pset n m C w = ∅ := by
      ext p
      simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [wires_input C _ w (by rw [inp_len]; exact hw), hw_eq, inp_getD_ln]
      simp
    simp [hemp]

lemma Lset_card_lt (n m : ℕ) (C : Circuit) (w : ℕ) (hw : w < n + m) :
    (Lset n m C w).card ≤ 1 := by
  by_cases hwn : w < n
  · have hw_eq : w = (⟨w, hwn⟩ : Fin n).val := rfl
    have hemp : Lset n m C w = ∅ := by
      ext l
      simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rw [wires_input C _ w (by rw [inp_len]; exact hw), hw_eq, inp_getD_pt]
      simp
    simp [hemp]
  · have hmlt : w - n < m := by omega
    let l0 : Fin m := ⟨w - n, hmlt⟩
    have hw_eq : w = n + l0.val := by simp [l0]; omega
    have hsub : Lset n m C w ⊆ {l0} := by
      intro l hl
      simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [wires_input C _ w (by rw [inp_len]; exact hw), hw_eq, inp_getD_ln] at hl
      simp only [Finset.mem_singleton, decide_eq_true_eq] at hl ⊢
      exact hl.symm
    exact le_trans (Finset.card_le_card hsub) (by simp)

lemma or_gate_sets (n m s : ℕ) (C : Circuit)
    (hRB : ReadsBack (n + m) C) (hLen : s ≤ C.gates.length)
    (hOr : ∀ j < s, (gateAt C j).op = GateOp.or ∧ (gateAt C j).inputs.length = 2)
    (j : ℕ) (hj : j < s) :
    ∃ u < n + m + j, ∃ v < n + m + j,
      Pset n m C (n + m + j) = Pset n m C u ∪ Pset n m C v ∧
      Lset n m C (n + m + j) = Lset n m C u ∪ Lset n m C v := by
  have hjC : j < C.gates.length := Nat.lt_of_lt_of_le hj hLen
  obtain ⟨hop, hilen⟩ := hOr j hj
  rcases hins : (gateAt C j).inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
  · simp [hins] at hilen
  · simp [hins] at hilen
  · have hu : u < n + m + j := hRB j hjC u (by simp [hins])
    have hv : v < n + m + j := hRB j hjC v (by simp [hins])
    refine ⟨u, hu, v, hv, ?_, ?_⟩
    · ext p
      simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      have hwg := wires_gate C (inp ({p} : Finset (Fin n)) (∅ : Finset (Fin m))) j hjC (by
        intro i hi; rw [inp_len]; exact hRB j hjC i hi)
      rw [inp_len] at hwg
      rw [hwg, hop, hins]
      simp [GateOp.eval, Bool.or_eq_true]
    · ext l
      simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      have hwg := wires_gate C (inp (∅ : Finset (Fin n)) ({l} : Finset (Fin m))) j hjC (by
        intro i hi; rw [inp_len]; exact hRB j hjC i hi)
      rw [inp_len] at hwg
      rw [hwg, hop, hins]
      simp [GateOp.eval, Bool.or_eq_true]
  · simp [hins] at hilen

def PiSet {n m : ℕ} (inc : Fin n → Fin m → Bool) (p : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun l => inc p l = true)

def LamSet {n m : ℕ} (inc : Fin n → Fin m → Bool) (l : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun p => inc p l = true)

lemma unique_pencil {n m : ℕ} {inc : Fin n → Fin m → Bool}
    (hInc : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    {S : Finset (Fin m)} (h2 : 2 ≤ S.card) {p1 p2 : Fin n}
    (h1 : S ⊆ PiSet inc p1) (h2' : S ⊆ PiSet inc p2) : p1 = p2 := by
  by_contra hne
  obtain ⟨l1, hl1, l2, hl2, hne_l⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have i11 : inc p1 l1 = true := (Finset.mem_filter.mp (h1 hl1)).2
  have i21 : inc p2 l1 = true := (Finset.mem_filter.mp (h2' hl1)).2
  have i12 : inc p1 l2 = true := (Finset.mem_filter.mp (h1 hl2)).2
  have i22 : inc p2 l2 = true := (Finset.mem_filter.mp (h2' hl2)).2
  exact hInc p1 p2 l1 l2 hne hne_l i11 i21 i12 i22

lemma unique_line {n m : ℕ} {inc : Fin n → Fin m → Bool}
    (hInc : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    {Q : Finset (Fin n)} (h2 : 2 ≤ Q.card) {l1 l2 : Fin m}
    (h1 : Q ⊆ LamSet inc l1) (h2' : Q ⊆ LamSet inc l2) : l1 = l2 := by
  by_contra hne
  obtain ⟨p1, hp1, p2, hp2, hne_p⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  have i11 : inc p1 l1 = true := (Finset.mem_filter.mp (h1 hp1)).2
  have i12 : inc p1 l2 = true := (Finset.mem_filter.mp (h2' hp1)).2
  have i21 : inc p2 l1 = true := (Finset.mem_filter.mp (h1 hp2)).2
  have i22 : inc p2 l2 = true := (Finset.mem_filter.mp (h2' hp2)).2
  exact hInc p1 p2 l1 l2 hne_p hne i11 i21 i12 i22

set_option maxHeartbeats 800000 in
lemma main_bound
    (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : Circuit) (s k T : ℕ)
    (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m))
    (hInc : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
      inc p l' = true → inc p' l' = true → False)
    (hRB : ReadsBack (n + m) C)
    (hSize : C.size = s + k + T)
    (hOr : ∀ j < s, (gateAt C j).op = GateOp.or ∧ (gateAt C j).inputs.length = 2)
    (hRect : ∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
      (gateAt C (s + i.val)).op = GateOp.and ∧
      (gateAt C (s + i.val)).inputs = [a i, b i] ∧
      ∀ x : List Bool, x.length = n + m →
        ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
         (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true)))
    (hEval : ∀ x : List Bool, x.length = n + m →
      C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
        (C.wires x).getD (n + m + s + j1.val) false = true))
    (hSound : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
      ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
      (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
      C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) :
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
        C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
      ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
          (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
          (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card := by
  have hGatesLen : C.gates.length = s + k + T := hSize
  have hsLen : s ≤ C.gates.length := by omega
  have hRectWire : ∀ (i : Fin k) (P : Finset (Fin n)) (L : Finset (Fin m)),
      (C.wires (inp P L)).getD (n + m + s + i.val) false =
        decide ((∃ pa ∈ A i, pa ∈ P) ∧ (∃ lb ∈ B i, lb ∈ L)) := by
    intro i P L
    obtain ⟨_, _, hai, hbi, hop, hins, hsem⟩ := hRect i
    have hj : s + i.val < C.gates.length := by have := i.isLt; omega
    have hwg := wires_gate C (inp P L) (s + i.val) hj (by
      intro w hw
      rw [hins] at hw
      rw [inp_len]
      rcases List.mem_cons.mp hw with rfl | hw'
      · omega
      · rcases List.mem_singleton.mp hw' with rfl
        omega)
    have hlen : (inp P L).length = n + m := inp_len P L
    have ⟨hsa, hsb⟩ := hsem (inp P L) hlen
    have heq_idx : (inp P L).length + (s + i.val) = n + m + s + i.val := by omega
    rw [← heq_idx, hwg, hop, hins]
    simp only [GateOp.eval, List.map, id_eq, List.all_cons, List.all_nil, Bool.and_true, hsa, hsb]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, inp_getD_pt, inp_getD_ln]
  have hEvalInp : ∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
      C.eval (inp P L) = true ↔
        ∃ i1 j1 : Fin k, i1 ≠ j1 ∧
          (∃ pa ∈ A i1, pa ∈ P) ∧ (∃ lb ∈ B i1, lb ∈ L) ∧
          (∃ pa ∈ A j1, pa ∈ P) ∧ (∃ lb ∈ B j1, lb ∈ L) := by
    intro P L
    rw [hEval (inp P L) (inp_len P L), decide_eq_true_eq]
    constructor
    · rintro ⟨i1, j1, hlt, h1, h2⟩
      rw [hRectWire, decide_eq_true_eq] at h1 h2
      exact ⟨i1, j1, ne_of_lt hlt, h1.1, h1.2, h2.1, h2.2⟩
    · rintro ⟨i1, j1, hne, h1a, h1b, h2a, h2b⟩
      rcases lt_trichotomy i1 j1 with hlt | rfl | hgt
      · refine ⟨i1, j1, hlt, ?_, ?_⟩ <;> rw [hRectWire, decide_eq_true_eq]
        · exact ⟨h1a, h1b⟩
        · exact ⟨h2a, h2b⟩
      · exact absurd rfl hne
      · refine ⟨j1, i1, hgt, ?_, ?_⟩ <;> rw [hRectWire, decide_eq_true_eq]
        · exact ⟨h2a, h2b⟩
        · exact ⟨h1a, h1b⟩
  have hMeetPt : ∀ (i j : Fin k) (p : Fin n), i ≠ j → p ∈ A i → p ∈ A j →
      B i ⊆ PiSet inc p ∨ B j ⊆ PiSet inc p := by
    intro i j p hne hpi hpj
    by_contra hnot
    obtain ⟨hn1, hn2⟩ := not_or.mp hnot
    obtain ⟨l1, hl1, hnl1⟩ := Finset.not_subset.mp hn1
    obtain ⟨l2, hl2, hnl2⟩ := Finset.not_subset.mp hn2
    simp only [PiSet, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnl1 hnl2
    let P : Finset (Fin n) := {p}
    let L : Finset (Fin m) := {l1, l2}
    have hcard : (P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1) := by
      left
      refine ⟨Finset.card_singleton p, ?_⟩
      exact le_trans (Finset.card_insert_le l1 {l2}) (by simp)
    have hnoinc : ∀ p' ∈ P, ∀ l' ∈ L, inc p' l' = false := by
      intro p' hp' l' hl'
      rcases Finset.mem_singleton.mp hp' with rfl
      rcases Finset.mem_insert.mp hl' with rfl | hl'
      · exact hnl1
      · rcases Finset.mem_singleton.mp hl' with rfl
        exact hnl2
    have hfalse : C.eval (inp P L) = false := hSound P L hcard hnoinc
    have htrue : C.eval (inp P L) = true := (hEvalInp P L).mpr ⟨i, j, hne,
      ⟨p, hpi, Finset.mem_singleton_self p⟩,
      ⟨l1, hl1, Finset.mem_insert_self l1 {l2}⟩,
      ⟨p, hpj, Finset.mem_singleton_self p⟩,
      ⟨l2, hl2, Finset.mem_insert_of_mem (Finset.mem_singleton_self l2)⟩⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  have hMeetLn : ∀ (i j : Fin k) (l : Fin m), i ≠ j → l ∈ B i → l ∈ B j →
      A i ⊆ LamSet inc l ∨ A j ⊆ LamSet inc l := by
    intro i j l hne hli hlj
    by_contra hnot
    obtain ⟨hn1, hn2⟩ := not_or.mp hnot
    obtain ⟨p1, hp1, hnp1⟩ := Finset.not_subset.mp hn1
    obtain ⟨p2, hp2, hnp2⟩ := Finset.not_subset.mp hn2
    simp only [LamSet, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hnp1 hnp2
    let P : Finset (Fin n) := {p1, p2}
    let L : Finset (Fin m) := {l}
    have hcard : (P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1) := by
      right
      refine ⟨?_, Finset.card_singleton l⟩
      exact le_trans (Finset.card_insert_le p1 {p2}) (by simp)
    have hnoinc : ∀ p' ∈ P, ∀ l' ∈ L, inc p' l' = false := by
      intro p' hp' l' hl'
      rcases Finset.mem_singleton.mp hl' with rfl
      rcases Finset.mem_insert.mp hp' with rfl | hp'
      · exact hnp1
      · rcases Finset.mem_singleton.mp hp' with rfl
        exact hnp2
    have hfalse : C.eval (inp P L) = false := hSound P L hcard hnoinc
    have htrue : C.eval (inp P L) = true := (hEvalInp P L).mpr ⟨i, j, hne,
      ⟨p1, hp1, Finset.mem_insert_self p1 {p2}⟩,
      ⟨l, hli, Finset.mem_singleton_self l⟩,
      ⟨p2, hp2, Finset.mem_insert_of_mem (Finset.mem_singleton_self p2)⟩,
      ⟨l, hlj, Finset.mem_singleton_self l⟩⟩
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  have hPa : ∀ i : Fin k, Pset n m C (a i) = A i := by
    intro i
    obtain ⟨_, _, _, _, _, _, hsem⟩ := hRect i
    ext p
    simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(hsem _ (inp_len _ _)).1, decide_eq_true_eq]
    constructor
    · rintro ⟨pa, hpa, hx⟩
      rw [inp_getD_pt, decide_eq_true_eq, Finset.mem_singleton] at hx
      exact hx ▸ hpa
    · intro hp
      exact ⟨p, hp, by rw [inp_getD_pt, decide_eq_true_eq]; exact Finset.mem_singleton_self p⟩
  have hLa : ∀ i : Fin k, Lset n m C (a i) = ∅ := by
    intro i
    obtain ⟨_, _, _, _, _, _, hsem⟩ := hRect i
    ext l
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rw [(hsem _ (inp_len _ _)).1, decide_eq_true_eq]
    rintro ⟨pa, _, hx⟩
    rw [inp_getD_pt] at hx
    simp at hx
  have hPb : ∀ i : Fin k, Pset n m C (b i) = ∅ := by
    intro i
    obtain ⟨_, _, _, _, _, _, hsem⟩ := hRect i
    ext p
    simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rw [(hsem _ (inp_len _ _)).2, decide_eq_true_eq]
    rintro ⟨lb, _, hx⟩
    rw [inp_getD_ln] at hx
    simp at hx
  have hLb : ∀ i : Fin k, Lset n m C (b i) = B i := by
    intro i
    obtain ⟨_, _, _, _, _, _, hsem⟩ := hRect i
    ext l
    simp only [Lset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(hsem _ (inp_len _ _)).2, decide_eq_true_eq]
    constructor
    · rintro ⟨lb, hlb, hx⟩
      rw [inp_getD_ln, decide_eq_true_eq, Finset.mem_singleton] at hx
      exact hx ▸ hlb
    · intro hl
      exact ⟨l, hl, by rw [inp_getD_ln, decide_eq_true_eq]; exact Finset.mem_singleton_self l⟩
  let P0 : Finset (Fin n) := Finset.univ.filter (fun q => ∃ j : Fin k, A j = {q} ∧ ¬ (B j ⊆ PiSet inc q))
  let tau : Fin n → ℕ → Finset (Fin m) := fun p w =>
    if Pset n m C w = ∅ ∧ Lset n m C w ⊆ PiSet inc p then Lset n m C w else ∅
  let sigma : Fin m → ℕ → Finset (Fin n) := fun l w =>
    if Lset n m C w = ∅ ∧ Pset n m C w ⊆ LamSet inc l then Pset n m C w
    else if Lset n m C w = ∅ ∧ Pset n m C w ∩ P0 ⊆ LamSet inc l then Pset n m C w ∩ P0
    else ∅
  have hTauBase : ∀ p : Fin n, ∀ w < n + m, (tau p w).card ≤ 1 := by
    intro p w hw
    dsimp only [tau]
    split_ifs
    · exact Lset_card_lt n m C w hw
    · simp
  have hSigmaBase : ∀ l : Fin m, ∀ w < n + m, (sigma l w).card ≤ 1 := by
    intro l w hw
    dsimp only [sigma]
    split_ifs
    · exact Pset_card_lt n m C w hw
    · exact le_trans (Finset.card_le_card Finset.inter_subset_left) (Pset_card_lt n m C w hw)
    · simp
  have hTauStep : ∀ p : Fin n, ∀ j < s, ∃ u < n + m + j, ∃ v < n + m + j,
      tau p (n + m + j) ⊆ tau p u ∪ tau p v := by
    intro p j hj
    obtain ⟨u, hu, v, hv, hPuv, hLuv⟩ := or_gate_sets n m s C hRB hsLen hOr j hj
    refine ⟨u, hu, v, hv, ?_⟩
    by_cases h1 : Pset n m C (n + m + j) = ∅ ∧ Lset n m C (n + m + j) ⊆ PiSet inc p
    · have h_lhs : tau p (n + m + j) = Lset n m C (n + m + j) := if_pos h1
      obtain ⟨hPempty, hLsub⟩ := h1
      rw [hPuv, Finset.union_eq_empty] at hPempty
      rw [hLuv] at hLsub
      have hu_cond : Pset n m C u = ∅ ∧ Lset n m C u ⊆ PiSet inc p :=
        ⟨hPempty.1, (Finset.union_subset_iff.mp hLsub).1⟩
      have hv_cond : Pset n m C v = ∅ ∧ Lset n m C v ⊆ PiSet inc p :=
        ⟨hPempty.2, (Finset.union_subset_iff.mp hLsub).2⟩
      have h_u : tau p u = Lset n m C u := if_pos hu_cond
      have h_v : tau p v = Lset n m C v := if_pos hv_cond
      rw [h_lhs, h_u, h_v, hLuv]
    · have h_lhs : tau p (n + m + j) = ∅ := if_neg h1
      rw [h_lhs]
      exact Finset.empty_subset _
  have hSigmaStep : ∀ l : Fin m, ∀ j < s, ∃ u < n + m + j, ∃ v < n + m + j,
      sigma l (n + m + j) ⊆ sigma l u ∪ sigma l v := by
    intro l j hj
    obtain ⟨u, hu, v, hv, hPuv, hLuv⟩ := or_gate_sets n m s C hRB hsLen hOr j hj
    refine ⟨u, hu, v, hv, ?_⟩
    by_cases h1 : Lset n m C (n + m + j) = ∅ ∧ Pset n m C (n + m + j) ⊆ LamSet inc l
    · have h_lhs : sigma l (n + m + j) = Pset n m C (n + m + j) := if_pos h1
      obtain ⟨hLempty, hPsub⟩ := h1
      rw [hLuv, Finset.union_eq_empty] at hLempty
      rw [hPuv] at hPsub
      have hu1 : Lset n m C u = ∅ ∧ Pset n m C u ⊆ LamSet inc l :=
        ⟨hLempty.1, (Finset.union_subset_iff.mp hPsub).1⟩
      have hv1 : Lset n m C v = ∅ ∧ Pset n m C v ⊆ LamSet inc l :=
        ⟨hLempty.2, (Finset.union_subset_iff.mp hPsub).2⟩
      have h_u : sigma l u = Pset n m C u := if_pos hu1
      have h_v : sigma l v = Pset n m C v := if_pos hv1
      rw [h_lhs, h_u, h_v, hPuv]
    · by_cases h2 : Lset n m C (n + m + j) = ∅ ∧ Pset n m C (n + m + j) ∩ P0 ⊆ LamSet inc l
      · have h_lhs : sigma l (n + m + j) = Pset n m C (n + m + j) ∩ P0 := by
          dsimp only [sigma]
          rw [if_neg h1, if_pos h2]
        obtain ⟨hLempty, hP0sub⟩ := h2
        rw [hLuv, Finset.union_eq_empty] at hLempty
        have hu_inter : Pset n m C u ∩ P0 ⊆ sigma l u := by
          have hu0 : Pset n m C u ∩ P0 ⊆ LamSet inc l := by
            intro x hx
            apply hP0sub
            rw [hPuv]
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
          dsimp only [sigma]
          split_ifs with hu1 hu2
          · exact Finset.inter_subset_left
          · exact le_refl _
          · exfalso; exact hu2 ⟨hLempty.1, hu0⟩
        have hv_inter : Pset n m C v ∩ P0 ⊆ sigma l v := by
          have hv0 : Pset n m C v ∩ P0 ⊆ LamSet inc l := by
            intro x hx
            apply hP0sub
            rw [hPuv]
            exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
          dsimp only [sigma]
          split_ifs with hv1 hv2
          · exact Finset.inter_subset_left
          · exact le_refl _
          · exfalso; exact hv2 ⟨hLempty.2, hv0⟩
        rw [h_lhs, hPuv, Finset.union_inter_distrib_right]
        exact Finset.union_subset_union hu_inter hv_inter
      · have h_lhs : sigma l (n + m + j) = ∅ := by
          dsimp only [sigma]
          rw [if_neg h1, if_neg h2]
        rw [h_lhs]
        exact Finset.empty_subset _
  let gatesP : Fin n → Finset ℕ := fun p => (Finset.range s).filter (fun j => 2 ≤ (tau p (n + m + j)).card)
  let gatesL : Fin m → Finset ℕ := fun l => (Finset.range s).filter (fun j => 2 ≤ (sigma l (n + m + j)).card)
  have hGP_disj : ∀ p1 p2 : Fin n, p1 ≠ p2 → Disjoint (gatesP p1) (gatesP p2) := by
    intro p1 p2 hne
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [gatesP, Finset.mem_filter] at hj1 hj2
    have c1 := hj1.2
    have c2 := hj2.2
    dsimp only [tau] at c1 c2
    split_ifs at c1 with h1
    · split_ifs at c2 with h2
      · exact hne (unique_pencil hInc c1 h1.2 h2.2)
      · simp at c2
    · simp at c1
  have hGL_disj : ∀ l1 l2 : Fin m, l1 ≠ l2 → Disjoint (gatesL l1) (gatesL l2) := by
    intro l1 l2 hne
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [gatesL, Finset.mem_filter] at hj1 hj2
    have c1 := hj1.2
    have c2 := hj2.2
    dsimp only [sigma] at c1 c2
    split_ifs at c1 with h1a h1b <;> split_ifs at c2 with h2a h2b
    · exact hne (unique_line hInc c1 h1a.2 h2a.2)
    · have hsub1 : Pset n m C (n + m + j) ∩ P0 ⊆ LamSet inc l1 :=
        Finset.Subset.trans Finset.inter_subset_left h1a.2
      exact hne (unique_line hInc c2 hsub1 h2b.2)
    · simp at c2
    · have hsub2 : Pset n m C (n + m + j) ∩ P0 ⊆ LamSet inc l2 :=
        Finset.Subset.trans Finset.inter_subset_left h2a.2
      exact hne (unique_line hInc c1 h1b.2 hsub2)
    · exact hne (unique_line hInc c1 h1b.2 h2b.2)
    · simp at c2
    · simp at c1
    · simp at c1
    · simp at c1
  have hGPL_disj : Disjoint (Finset.univ.biUnion gatesP) (Finset.univ.biUnion gatesL) := by
    rw [Finset.disjoint_left]
    intro j hjP hjL
    rw [Finset.mem_biUnion] at hjP hjL
    obtain ⟨p, _, hjP⟩ := hjP
    obtain ⟨l, _, hjL⟩ := hjL
    simp only [gatesP, gatesL, Finset.mem_filter] at hjP hjL
    have cP := hjP.2
    have cL := hjL.2
    dsimp only [tau] at cP
    split_ifs at cP with hp_cond
    · have hPempty : Pset n m C (n + m + j) = ∅ := hp_cond.1
      dsimp only [sigma] at cL
      split_ifs at cL <;> simp [hPempty] at cL
    · simp at cP
  have hGatesSum : (∑ p : Fin n, (gatesP p).card) + (∑ l : Fin m, (gatesL l).card) ≤ s := by
    have h1 : (Finset.univ.biUnion gatesP).card = ∑ p : Fin n, (gatesP p).card :=
      Finset.card_biUnion (fun p1 _ p2 _ hne => hGP_disj p1 p2 hne)
    have h2 : (Finset.univ.biUnion gatesL).card = ∑ l : Fin m, (gatesL l).card :=
      Finset.card_biUnion (fun l1 _ l2 _ hne => hGL_disj l1 l2 hne)
    have hsub : Finset.univ.biUnion gatesP ∪ Finset.univ.biUnion gatesL ⊆ Finset.range s := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj <;> rw [Finset.mem_biUnion] at hj
      · obtain ⟨p, _, hj⟩ := hj; exact (Finset.mem_filter.mp hj).1
      · obtain ⟨l, _, hj⟩ := hj; exact (Finset.mem_filter.mp hj).1
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hGPL_disj, h1, h2, Finset.card_range] at hcard
    exact hcard
  let IP : Fin n → Finset (Fin k) := fun p =>
    Finset.univ.filter (fun t => p ∈ A t ∧ 2 ≤ (B t).card ∧ B t ⊆ PiSet inc p)
  let IL : Fin m → Finset (Fin k) := fun l =>
    Finset.univ.filter (fun t => l ∈ B t ∧ 2 ≤ (A t).card ∧ A t ⊆ LamSet inc l)
  let IP_all : Finset (Fin k) := Finset.univ.biUnion IP
  let IL_all : Finset (Fin k) := Finset.univ.biUnion IL
  let R1 : Finset (Fin k) := Finset.univ.filter (fun t => (A t).card = 1 ∧ (B t).card = 1)
  let RB : Fin m → Finset (Fin k) := fun l =>
    Finset.univ.filter (fun t => t ∉ IP_all ∪ IL_all ∧ 2 ≤ (A t).card ∧ B t = {l})
  let RB_all : Finset (Fin k) := Finset.univ.biUnion RB
  let D : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun t =>
    (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
    (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))
  have hIP_disj : ∀ p1 p2 : Fin n, p1 ≠ p2 → Disjoint (IP p1) (IP p2) := by
    intro p1 p2 hne
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [IP, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    exact hne (unique_pencil hInc ht1.2.1 ht1.2.2 ht2.2.2)
  have hIL_disj : ∀ l1 l2 : Fin m, l1 ≠ l2 → Disjoint (IL l1) (IL l2) := by
    intro l1 l2 hne
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [IL, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    exact hne (unique_line hInc ht1.2.1 ht1.2.2 ht2.2.2)
  have hRB_disj : ∀ l1 l2 : Fin m, l1 ≠ l2 → Disjoint (RB l1) (RB l2) := by
    intro l1 l2 hne
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    simp only [RB, Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2
    have heq : ({l1} : Finset (Fin m)) = {l2} := ht1.2.2.symm.trans ht2.2.2
    exact hne (Finset.singleton_injective heq)
  have hIP_sum : ∑ p : Fin n, (IP p).card = IP_all.card :=
    (Finset.card_biUnion (fun p1 _ p2 _ hne => hIP_disj p1 p2 hne)).symm
  have hIL_sum : ∑ l : Fin m, (IL l).card = IL_all.card :=
    (Finset.card_biUnion (fun l1 _ l2 _ hne => hIL_disj l1 l2 hne)).symm
  have hRB_sum : ∑ l : Fin m, (RB l).card = RB_all.card :=
    (Finset.card_biUnion (fun l1 _ l2 _ hne => hRB_disj l1 l2 hne)).symm
  have hInterD : IP_all ∩ IL_all ⊆ D := by
    intro t ht
    obtain ⟨htP, htL⟩ := Finset.mem_inter.mp ht
    rw [Finset.mem_biUnion] at htP htL
    obtain ⟨c, _, hc⟩ := htP
    obtain ⟨f, _, hf⟩ := htL
    simp only [IP, IL, Finset.mem_filter, Finset.mem_univ, true_and] at hc hf
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨c, hc.2.1, fun e he => (Finset.mem_filter.mp (hc.2.2 he)).2⟩,
            ⟨f, hf.1, hf.2.1, fun g hg => (Finset.mem_filter.mp (hf.2.2 hg)).2⟩⟩
  have hDisj1 : Disjoint (IP_all ∪ IL_all) RB_all := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_biUnion] at ht2
    obtain ⟨l, _, hl⟩ := ht2
    exact (Finset.mem_filter.mp hl).2.1 ht1
  have hDisj2 : Disjoint ((IP_all ∪ IL_all) ∪ RB_all) R1 := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨hA1, hB1⟩ := (Finset.mem_filter.mp ht2).2
    rcases Finset.mem_union.mp ht1 with hIPL | hRBt
    · rcases Finset.mem_union.mp hIPL with hIPt | hILt
      · rw [Finset.mem_biUnion] at hIPt
        obtain ⟨p, _, hp⟩ := hIPt
        have := (Finset.mem_filter.mp hp).2.2.1
        omega
      · rw [Finset.mem_biUnion] at hILt
        obtain ⟨l, _, hl⟩ := hILt
        have := (Finset.mem_filter.mp hl).2.2.1
        omega
    · rw [Finset.mem_biUnion] at hRBt
      obtain ⟨l, _, hl⟩ := hRBt
      have := (Finset.mem_filter.mp hl).2.2.1
      omega
  have hRectCount : IP_all.card + IL_all.card + RB_all.card + R1.card ≤ k + D.card := by
    have hunion_inter := Finset.card_union_add_card_inter IP_all IL_all
    have hD_le : (IP_all ∩ IL_all).card ≤ D.card := Finset.card_le_card hInterD
    have hPack : ((IP_all ∪ IL_all) ∪ RB_all ∪ R1).card ≤ k := by
      have := Finset.card_le_univ ((IP_all ∪ IL_all) ∪ RB_all ∪ R1)
      simpa using this
    rw [Finset.card_union_of_disjoint hDisj2, Finset.card_union_of_disjoint hDisj1] at hPack
    omega
  have hBoundP : ∀ p : Fin n, ((IP p).biUnion B).card ≤ (gatesP p).card + (IP p).card := by
    intro p
    have hEq : (IP p).biUnion B = (IP p).biUnion (fun t => tau p (b t)) := by
      apply Finset.biUnion_congr rfl
      intro t ht
      obtain ⟨_, _, htSub⟩ := (Finset.mem_filter.mp ht).2
      dsimp only [tau]
      rw [if_pos ⟨hPb t, by rw [hLb t]; exact htSub⟩, hLb t]
    rw [hEq]
    exact dag_union_bound (n + m) s (tau p) (hTauBase p) (hTauStep p) (IP p) b
      (fun t _ => (hRect t).2.2.2.1)
  let AccL : Fin m → Finset (Fin n) := fun l =>
    ((IL l).biUnion A) ∪ ((RB l).biUnion (fun t => A t ∩ P0))
  have hRB_P0_sub : ∀ (l : Fin m) (t : Fin k), t ∈ RB l → A t ∩ P0 ⊆ LamSet inc l := by
    intro l t ht q hq
    obtain ⟨_, hA2, hBsingle⟩ := (Finset.mem_filter.mp ht).2
    obtain ⟨hqA, hqP0⟩ := Finset.mem_inter.mp hq
    obtain ⟨j, hAj, hnBj⟩ := (Finset.mem_filter.mp hqP0).2
    have hne : t ≠ j := by
      intro heq
      subst heq
      rw [hAj, Finset.card_singleton] at hA2
      omega
    have hqj : q ∈ A j := by rw [hAj]; exact Finset.mem_singleton_self q
    rcases hMeetPt t j q hne hqA hqj with hBt | hBj
    · have hlmem : l ∈ B t := by rw [hBsingle]; exact Finset.mem_singleton_self l
      have hinc : inc q l = true := (Finset.mem_filter.mp (hBt hlmem)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hinc⟩
    · exact absurd hBj hnBj
  have hBoundL : ∀ l : Fin m, (AccL l).card ≤ (gatesL l).card + (IL l).card + (RB l).card := by
    intro l
    have hDisjLR : Disjoint (IL l) (RB l) := by
      rw [Finset.disjoint_left]
      intro t htL htR
      have hInL : t ∈ IL_all := Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, htL⟩
      exact (Finset.mem_filter.mp htR).2.1 (Finset.mem_union_right _ hInL)
    have hSubSigma : AccL l ⊆ (IL l ∪ RB l).biUnion (fun t => sigma l (a t)) := by
      intro q hq
      rcases Finset.mem_union.mp hq with hq1 | hq2
      · obtain ⟨t, ht, hqt⟩ := Finset.mem_biUnion.mp hq1
        refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_union_left _ ht, ?_⟩
        obtain ⟨_, _, hAtSub⟩ := (Finset.mem_filter.mp ht).2
        dsimp only [sigma]
        rw [if_pos ⟨hLa t, by rw [hPa t]; exact hAtSub⟩, hPa t]
        exact hqt
      · obtain ⟨t, ht, hqt⟩ := Finset.mem_biUnion.mp hq2
        refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_union_right _ ht, ?_⟩
        have hSubLam : Pset n m C (a t) ∩ P0 ⊆ LamSet inc l := by
          rw [hPa t]; exact hRB_P0_sub l t ht
        dsimp only [sigma]
        split_ifs with h1 h2
        · rw [hPa t]; exact (Finset.mem_inter.mp hqt).1
        · rw [hPa t]; exact hqt
        · exfalso; exact h2 ⟨hLa t, hSubLam⟩
    have hDag := dag_union_bound (n + m) s (sigma l) (hSigmaBase l) (hSigmaStep l)
      (IL l ∪ RB l) a (fun t _ => (hRect t).2.2.1)
    have hCardSub := Finset.card_le_card hSubSigma
    have hCardUn := Finset.card_union_of_disjoint hDisjLR
    change (AccL l).card ≤ (gatesL l).card + (IL l).card + (RB l).card
    change ((IL l ∪ RB l).biUnion (fun t => sigma l (a t))).card ≤ (gatesL l).card + (IL l ∪ RB l).card at hDag
    omega
  let Acc : Finset (Fin n × Fin m) := (Finset.univ : Finset (Fin n × Fin m)).filter (fun q =>
    inc q.1 q.2 = true ∧
    C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)
  let SetP : Finset (Fin n × Fin m) :=
    Finset.univ.biUnion (fun p => ((IP p).biUnion B).image (fun l => (p, l)))
  let SetL : Finset (Fin n × Fin m) :=
    Finset.univ.biUnion (fun l => (AccL l).image (fun p => (p, l)))
  let SetR1 : Finset (Fin n × Fin m) :=
    R1.biUnion (fun t => A t ×ˢ B t)
  have hCover : Acc ⊆ (SetP ∪ SetL) ∪ SetR1 := by
    intro q hq
    rcases q with ⟨p, l⟩
    simp only [Acc, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hinc_pl, heval_pl⟩ := hq
    rw [inp_singleton_eq p l, hEvalInp] at heval_pl
    obtain ⟨i, j, hne, ⟨pa1, hpa1, hpa1_eq⟩, ⟨lb1, hlb1, hlb1_eq⟩, ⟨pa2, hpa2, hpa2_eq⟩, ⟨lb2, hlb2, hlb2_eq⟩⟩ := heval_pl
    rw [Finset.mem_singleton.mp hpa1_eq] at hpa1
    rw [Finset.mem_singleton.mp hlb1_eq] at hlb1
    rw [Finset.mem_singleton.mp hpa2_eq] at hpa2
    rw [Finset.mem_singleton.mp hlb2_eq] at hlb2
    by_cases hInP : l ∈ (IP p).biUnion B
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, Finset.mem_image.mpr ⟨l, hInP, rfl⟩⟩
    · by_cases hInL : p ∈ (IL l).biUnion A
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
        exact Finset.mem_union_left _ hInL
      · by_cases hInR1 : ∃ t ∈ R1, p ∈ A t ∧ l ∈ B t
        · obtain ⟨t, ht, hpt, hlt⟩ := hInR1
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_product.mpr ⟨hpt, hlt⟩⟩
        · have hNotR1 : ∀ t : Fin k, t ∈ R1 → p ∈ A t → l ∈ B t → False := by
            intro t ht hpt hlt
            exact hInR1 ⟨t, ht, hpt, hlt⟩
          have hexB1 : ∃ i1 : Fin k, p ∈ A i1 ∧ B i1 = {l} := by
            rcases hMeetPt i j p hne hpa1 hpa2 with hBi | hBj
            · refine ⟨i, hpa1, ?_⟩
              have hlt2 : (B i).card < 2 := by
                by_contra hge2
                have hiIP : i ∈ IP p := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpa1, by omega, hBi⟩
                exact hInP (Finset.mem_biUnion.mpr ⟨i, hiIP, hlb1⟩)
              have hpos : 0 < (B i).card := Finset.Nonempty.card_pos ⟨l, hlb1⟩
              have hc1 : (B i).card = 1 := by omega
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
              rw [hx] at hlb1 ⊢
              rw [Finset.mem_singleton.mp hlb1]
            · refine ⟨j, hpa2, ?_⟩
              have hlt2 : (B j).card < 2 := by
                by_contra hge2
                have hjIP : j ∈ IP p := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpa2, by omega, hBj⟩
                exact hInP (Finset.mem_biUnion.mpr ⟨j, hjIP, hlb2⟩)
              have hpos : 0 < (B j).card := Finset.Nonempty.card_pos ⟨l, hlb2⟩
              have hc1 : (B j).card = 1 := by omega
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
              rw [hx] at hlb2 ⊢
              rw [Finset.mem_singleton.mp hlb2]
          have hexA1 : ∃ j1 : Fin k, A j1 = {p} ∧ l ∈ B j1 := by
            rcases hMeetLn i j l hne hlb1 hlb2 with hAi | hAj
            · refine ⟨i, ?_, hlb1⟩
              have hlt2 : (A i).card < 2 := by
                by_contra hge2
                have hiIL : i ∈ IL l := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlb1, by omega, hAi⟩
                exact hInL (Finset.mem_biUnion.mpr ⟨i, hiIL, hpa1⟩)
              have hpos : 0 < (A i).card := Finset.Nonempty.card_pos ⟨p, hpa1⟩
              have hc1 : (A i).card = 1 := by omega
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
              rw [hx] at hpa1 ⊢
              rw [Finset.mem_singleton.mp hpa1]
            · refine ⟨j, ?_, hlb2⟩
              have hlt2 : (A j).card < 2 := by
                by_contra hge2
                have hjIL : j ∈ IL l := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlb2, by omega, hAj⟩
                exact hInL (Finset.mem_biUnion.mpr ⟨j, hjIL, hpa2⟩)
              have hpos : 0 < (A j).card := Finset.Nonempty.card_pos ⟨p, hpa2⟩
              have hc1 : (A j).card = 1 := by omega
              obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc1
              rw [hx] at hpa2 ⊢
              rw [Finset.mem_singleton.mp hpa2]
          obtain ⟨i1, hpi1, hBi1⟩ := hexB1
          obtain ⟨j1, hAj1, hlj1⟩ := hexA1
          have hi1_A2 : 2 ≤ (A i1).card := by
            by_contra hlt2
            have hpos : 0 < (A i1).card := Finset.Nonempty.card_pos ⟨p, hpi1⟩
            have hc1 : (A i1).card = 1 := by omega
            have hcB1 : (B i1).card = 1 := by rw [hBi1]; exact Finset.card_singleton l
            have hi1R1 : i1 ∈ R1 := Finset.mem_filter.mpr ⟨Finset.mem_univ i1, hc1, hcB1⟩
            exact hNotR1 i1 hi1R1 hpi1 (by rw [hBi1]; exact Finset.mem_singleton_self l)
          have hi1_notIPL : i1 ∉ IP_all ∪ IL_all := by
            intro hmem
            rcases Finset.mem_union.mp hmem with hP | hL
            · rw [Finset.mem_biUnion] at hP
              obtain ⟨p', _, hp'⟩ := hP
              have hB2 := (Finset.mem_filter.mp hp').2.2.1
              rw [hBi1, Finset.card_singleton] at hB2
              omega
            · rw [Finset.mem_biUnion] at hL
              obtain ⟨l', _, hl'⟩ := hL
              have hl'mem : l' ∈ B i1 := (Finset.mem_filter.mp hl').2.1
              rw [hBi1, Finset.mem_singleton] at hl'mem
              subst hl'mem
              exact hInL (Finset.mem_biUnion.mpr ⟨i1, hl', hpi1⟩)
          have hi1_RB : i1 ∈ RB l :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ i1, hi1_notIPL, hi1_A2, hBi1⟩
          have hj1_B2 : 2 ≤ (B j1).card := by
            by_contra hlt2
            have hpos : 0 < (B j1).card := Finset.Nonempty.card_pos ⟨l, hlj1⟩
            have hc1 : (B j1).card = 1 := by omega
            have hcA1 : (A j1).card = 1 := by rw [hAj1]; exact Finset.card_singleton p
            have hj1R1 : j1 ∈ R1 := Finset.mem_filter.mpr ⟨Finset.mem_univ j1, hcA1, hc1⟩
            exact hNotR1 j1 hj1R1 (by rw [hAj1]; exact Finset.mem_singleton_self p) hlj1
          have hj1_notPi : ¬ (B j1 ⊆ PiSet inc p) := by
            intro hsub
            have hj1IP : j1 ∈ IP p := Finset.mem_filter.mpr ⟨Finset.mem_univ j1,
              by rw [hAj1]; exact Finset.mem_singleton_self p, hj1_B2, hsub⟩
            exact hInP (Finset.mem_biUnion.mpr ⟨j1, hj1IP, hlj1⟩)
          have hp_P0 : p ∈ P0 := Finset.mem_filter.mpr ⟨Finset.mem_univ p, ⟨j1, hAj1, hj1_notPi⟩⟩
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨i1, hi1_RB, Finset.mem_inter.mpr ⟨hpi1, hp_P0⟩⟩
  have hSetP_card : SetP.card ≤ (∑ p : Fin n, (gatesP p).card) + IP_all.card := by
    calc SetP.card
      _ ≤ ∑ p : Fin n, (((IP p).biUnion B).image (fun l => (p, l))).card := Finset.card_biUnion_le
      _ ≤ ∑ p : Fin n, ((IP p).biUnion B).card := Finset.sum_le_sum (fun p _ => Finset.card_image_le)
      _ ≤ ∑ p : Fin n, ((gatesP p).card + (IP p).card) := Finset.sum_le_sum (fun p _ => hBoundP p)
      _ = (∑ p : Fin n, (gatesP p).card) + (∑ p : Fin n, (IP p).card) := Finset.sum_add_distrib
      _ = (∑ p : Fin n, (gatesP p).card) + IP_all.card := by rw [hIP_sum]
  have hSetL_card : SetL.card ≤ (∑ l : Fin m, (gatesL l).card) + IL_all.card + RB_all.card := by
    calc SetL.card
      _ ≤ ∑ l : Fin m, ((AccL l).image (fun p => (p, l))).card := Finset.card_biUnion_le
      _ ≤ ∑ l : Fin m, (AccL l).card := Finset.sum_le_sum (fun l _ => Finset.card_image_le)
      _ ≤ ∑ l : Fin m, ((gatesL l).card + (IL l).card + (RB l).card) := Finset.sum_le_sum (fun l _ => hBoundL l)
      _ = (∑ l : Fin m, (gatesL l).card) + (∑ l : Fin m, (IL l).card) + (∑ l : Fin m, (RB l).card) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ l : Fin m, (gatesL l).card) + IL_all.card + RB_all.card := by rw [hIL_sum, hRB_sum]
  have hSetR1_card : SetR1.card ≤ R1.card := by
    apply card_biUnion_le_one R1 (fun t => A t ×ˢ B t)
    intro t ht
    obtain ⟨hcA, hcB⟩ := (Finset.mem_filter.mp ht).2
    rw [Finset.card_product, hcA, hcB]
  have hAcc_le : Acc.card ≤ SetP.card + SetL.card + SetR1.card := by
    calc Acc.card
      _ ≤ ((SetP ∪ SetL) ∪ SetR1).card := Finset.card_le_card hCover
      _ ≤ (SetP ∪ SetL).card + SetR1.card := Finset.card_union_le _ _
      _ ≤ SetP.card + SetL.card + SetR1.card := by
          have := Finset.card_union_le SetP SetL
          omega
  change Acc.card ≤ s + k + D.card
  omega

end PEqualNP.Outside.L_meta_3063

theorem PEqualNP.Outside.L_meta_3063 :
    ∀ (n m : ℕ) (inc : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (s k T : ℕ)
  (a b : Fin k → ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)),
  (∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' → inc p l = true → inc p' l = true →
    inc p l' = true → inc p' l' = true → False) →
  PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  C.size = s + k + T → 1 ≤ k →
  (∀ j < s, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) →
  (∀ i : Fin k, (A i).Nonempty ∧ (B i).Nonempty ∧ a i < n + m + s ∧ b i < n + m + s ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (s + i.val)).inputs = [a i, b i] ∧
    ∀ x : List Bool, x.length = n + m →
      ((C.wires x).getD (a i) false = decide (∃ pa ∈ A i, x.getD pa.val false = true) ∧
       (C.wires x).getD (b i) false = decide (∃ lb ∈ B i, x.getD (n + lb.val) false = true))) →
  (∀ x : List Bool, x.length = n + m →
    C.eval x = decide (∃ i1 j1 : Fin k, i1 < j1 ∧ (C.wires x).getD (n + m + s + i1.val) false = true ∧
      (C.wires x).getD (n + m + s + j1.val) false = true)) →
  (∀ (P : Finset (Fin n)) (L : Finset (Fin m)),
    ((P.card = 1 ∧ L.card ≤ 2) ∨ (P.card ≤ 2 ∧ L.card = 1)) →
    (∀ p ∈ P, ∀ l ∈ L, inc p l = false) →
    C.eval (List.ofFn (fun u : Fin n => decide (u ∈ P)) ++ List.ofFn (fun v : Fin m => decide (v ∈ L))) = false) →
  ((Finset.univ : Finset (Fin n × Fin m)).filter (fun q => inc q.1 q.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = q.1)) ++ List.ofFn (fun v : Fin m => decide (v = q.2))) = true)).card
    ≤ s + k + ((Finset.univ : Finset (Fin k)).filter (fun t =>
        (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
        (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ∧
  (k ≤ T + 1 →
    ((Finset.univ : Finset (Fin n × Fin m)).filter (fun r => inc r.1 r.2 = true ∧
      C.eval (List.ofFn (fun u : Fin n => decide (u = r.1)) ++ List.ofFn (fun v : Fin m => decide (v = r.2))) = true)).card
    ≤ C.size + 1) := by
  intro n m inc C s k T a b A B hInc _ hRB hSize _ hOr hRect hEval hSound
  have hMain := PEqualNP.Outside.L_meta_3063.main_bound n m inc C s k T a b A B hInc hRB hSize hOr hRect hEval hSound
  refine ⟨hMain, fun hkT => ?_⟩
  have hD_le : ((Finset.univ : Finset (Fin k)).filter (fun t =>
      (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
      (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))).card ≤ k := by
    have := Finset.card_le_univ (((Finset.univ : Finset (Fin k)).filter (fun t =>
      (∃ c : Fin n, 2 ≤ (B t).card ∧ ∀ e ∈ B t, inc c e = true) ∧
      (∃ f ∈ B t, 2 ≤ (A t).card ∧ ∀ g ∈ A t, inc g f = true))))
    simpa using this
  omega
