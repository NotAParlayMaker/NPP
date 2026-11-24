import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3087

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gv g w]

lemma eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl step x).getD C.output false := rfl

lemma foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

def Good (C D : Circuit) : Prop :=
  FanInTwo D ∧ circuitFun 10 D = circuitFun 10 C ∧ D.size ≤ C.size

def meas (D : Circuit) : ℕ := 3 * D.gates.length + (D.gates.flatMap Gate.inputs).length

lemma replace_better (C D : Circuit) (hD : Good C D) (A B : List Gate) (g g' : Gate)
    (hg : D.gates = A ++ g :: B)
    (hop : g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not)
    (hlen : g'.inputs.length < g.inputs.length)
    (hv : ∀ w : List Bool, w.length = 10 + A.length → gv g' w = gv g w) :
    ∃ D', Good C D' ∧ meas D' < meas D := by
  obtain ⟨hF, hf, hs⟩ := hD
  refine ⟨⟨A ++ g' :: B, D.output⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h hh
    simp only [List.mem_append, List.mem_cons] at hh
    have hg2 := hF g (by rw [hg]; simp)
    rcases hh with hh | hh | hh
    · exact hF h (by rw [hg]; simp [hh])
    · subst hh
      refine ⟨?_, by omega⟩
      rcases hop with h1 | h1 | h1 <;> simp [h1]
    · exact hF h (by rw [hg]; simp [hh])
  · rw [← hf]
    funext x
    simp only [circuitFun, eval_eq, hg, List.foldl_append, List.foldl_cons]
    have hl : (A.foldl step (List.ofFn x)).length = 10 + A.length := by
      rw [foldl_step_length]; simp
    have : step (A.foldl step (List.ofFn x)) g' = step (A.foldl step (List.ofFn x)) g := by
      simp only [step, hv _ hl]
    rw [this]
  · simp only [Circuit.size, hg, List.length_append, List.length_cons] at hs ⊢
    omega
  · simp only [meas, hg, List.length_append, List.length_cons, List.flatMap_append,
      List.flatMap_cons]
    omega

def ri (r i : ℕ) : ℕ := if i < r then i else i - 1

def rg (r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ri r)⟩

lemma getD_ri (u : List Bool) (r i : ℕ) (hi : i ≠ r) :
    (u.eraseIdx r).getD (ri r i) false = u.getD i false := by
  unfold ri
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split_ifs <;> first | rfl | omega | rw [show i - 1 + 1 = i by omega]

lemma foldl_erase (B : List Gate) (r : ℕ) (u : List Bool) (hr : r < u.length)
    (hB : ∀ g ∈ B, r ∉ g.inputs) :
    (B.map (rg r)).foldl step (u.eraseIdx r) = (B.foldl step u).eraseIdx r := by
  induction B generalizing u with
  | nil => rfl
  | cons b B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hv : gv (rg r b) (u.eraseIdx r) = gv b u := by
      unfold gv rg
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact getD_ri u r i (fun h => hB b (by simp) (by rw [← h]; exact hi))
    have he : step (u.eraseIdx r) (rg r b) = (step u b).eraseIdx r := by
      unfold step
      rw [hv, List.eraseIdx_append_of_lt_length hr]
    rw [he]
    apply ih
    · simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
    · intro g hg; exact hB g (List.mem_cons_of_mem _ hg)

lemma remove_better (C D : Circuit) (hD : Good C D) (A B : List Gate) (g : Gate)
    (hg : D.gates = A ++ g :: B) (hout : D.output ≠ 10 + A.length)
    (hB : ∀ b ∈ B, 10 + A.length ∉ b.inputs) : ∃ D', Good C D' ∧ meas D' < meas D := by
  obtain ⟨hF, hf, hs⟩ := hD
  set r := 10 + A.length with hr
  refine ⟨⟨A ++ B.map (rg r), ri r D.output⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h hh
    simp only [List.mem_append, List.mem_map] at hh
    rcases hh with hh | ⟨b, hb, rfl⟩
    · exact hF h (by rw [hg]; simp [hh])
    · have := hF b (by rw [hg]; simp [hb])
      simpa [rg] using this
  · rw [← hf]
    funext x
    simp only [circuitFun, eval_eq, hg, List.foldl_append, List.foldl_cons]
    have hl : (A.foldl step (List.ofFn x)).length = r := by
      rw [foldl_step_length]; simp [hr]
    have h1 : ∀ w : List Bool, w.length = r → (step w g).eraseIdx r = w := by
      intro w hw
      unfold step
      rw [List.eraseIdx_append_of_length_le (by omega), hw, Nat.sub_self]
      simp
    have key := foldl_erase B r (step (A.foldl step (List.ofFn x)) g)
      (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega) hB
    rw [h1 _ hl] at key
    rw [key, getD_ri _ _ _ hout]
  · simp only [Circuit.size, hg, List.length_append, List.length_cons, List.length_map] at hs ⊢
    omega
  · have : ((B.map (rg r)).flatMap Gate.inputs).length = (B.flatMap Gate.inputs).length := by
      simp [List.length_flatMap, rg, Function.comp_def]
    simp only [meas, hg, List.length_append, List.length_cons, List.length_map,
      List.flatMap_append, List.flatMap_cons, this]
    omega

lemma gv_congr (g : Gate) (u v : List Bool)
    (h : ∀ j ∈ g.inputs, u.getD j false = v.getD j false) : gv g u = gv g v := by
  unfold gv
  congr 1
  exact List.map_congr_left h

lemma foldl_agree (G : List Gate) (i : ℕ) (hG : ∀ g ∈ G, i ∉ g.inputs) (u v : List Bool)
    (hl : u.length = v.length) (h : ∀ k, k ≠ i → u.getD k false = v.getD k false) :
    ∀ k, k ≠ i → (G.foldl step u).getD k false = (G.foldl step v).getD k false := by
  induction G generalizing u v with
  | nil => exact h
  | cons g G ih =>
    simp only [List.foldl_cons]
    have hgv : gv g u = gv g v :=
      gv_congr g u v (fun j hj => h j (fun hji => hG g (by simp) (by rw [← hji]; exact hj)))
    refine ih (fun g' hg' => hG g' (by simp [hg'])) _ _ (by simp [step, hl]) ?_
    intro k hk
    unfold step
    by_cases hku : k < u.length
    · rw [List.getD_append _ _ _ _ hku, List.getD_append _ _ _ _ (hl ▸ hku)]
      exact h k hk
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        hgv, hl]

lemma input_used (D : Circuit) (i : ℕ) (hi : i < 10)
    (hdep : ∃ x4 x5 : Fin 10 → Bool, (∀ x6 : Fin 10, x6 ≠ ⟨i, hi⟩ → x4 x6 = x5 x6) ∧
      circuitFun 10 D x4 ≠ circuitFun 10 D x5) :
    i ∈ D.output :: D.gates.flatMap Gate.inputs := by
  by_contra hn
  simp only [List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hn
  obtain ⟨hno, hng⟩ := hn
  obtain ⟨x4, x5, hagree, hne⟩ := hdep
  apply hne
  simp only [circuitFun, eval_eq]
  refine foldl_agree D.gates i (fun g hg => hng g hg) _ _ (by simp) ?_ D.output (Ne.symm hno)
  intro k hk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with hk10
  · simp only [Option.getD_some]
    exact hagree ⟨k, hk10⟩ (fun h => hk (congrArg Fin.val h))
  · rfl

lemma output_lt (D : Circuit)
    (hdep : ∃ x4 x5 : Fin 10 → Bool, circuitFun 10 D x4 ≠ circuitFun 10 D x5) :
    D.output < 10 + D.gates.length := by
  by_contra hn
  obtain ⟨x4, x5, hne⟩ := hdep
  apply hne
  simp only [circuitFun, eval_eq]
  rw [List.getD_eq_default _ _ (by rw [foldl_step_length]; simp; omega),
    List.getD_eq_default _ _ (by rw [foldl_step_length]; simp; omega)]

lemma sum_count_le (S : Finset ℕ) (L : List ℕ) : ∑ w ∈ S, L.count w ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, Finset.sum_ite_eq,
      List.length_cons]
    split_ifs <;> omega

lemma not_bound (G : List Gate)
    (h : ∀ g ∈ G, g.inputs.length +
      (if (g.op.eval [false] && !g.op.eval [true]) = true then 1 else 0) ≤ 2) :
    (G.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
      (G.flatMap Gate.inputs).length ≤ 2 * G.length := by
  induction G with
  | nil => simp
  | cons g G ih =>
    have h1 := h g (by simp)
    have h2 := ih (fun g' hg' => h g' (by simp [hg']))
    simp only [List.filter_cons, List.flatMap_cons, List.length_append, List.length_cons]
    split_ifs at h1 ⊢ <;> (try simp only [List.length_cons]) <;> omega

lemma key (C : Circuit) (hC : FanInTwo C) :
    ∃ D : Circuit, Good C D ∧
      (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
      (∀ A g B, D.gates = A ++ g :: B → ∀ i ∈ g.inputs, i < 10 + A.length) ∧
      (∀ A g B, D.gates = A ++ g :: B →
        D.output = 10 + A.length ∨ ∃ b ∈ B, 10 + A.length ∈ b.inputs) := by
  classical
  have hex : ∃ k, ∃ D, Good C D ∧ meas D = k := ⟨_, C, ⟨hC, rfl, le_rfl⟩, rfl⟩
  obtain ⟨D, hD, hk⟩ := Nat.find_spec hex
  have hmin : ∀ D', Good C D' → ¬ meas D' < meas D := by
    intro D' h' hlt
    have := Nat.find_min' hex ⟨D', h', rfl⟩
    omega
  have P1 : ∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop
    by_contra hlen
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hg
    obtain ⟨op, ins⟩ := g
    simp only at hop hlen
    subst hop
    rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hlen
    · simp at hlen
    · obtain ⟨D', h', hlt⟩ := replace_better C D hD A B _ ⟨GateOp.not, [a]⟩ hAB (by simp)
        (by simp) (by intro w _; simp [gv, GateOp.eval])
      exact hmin D' h' hlt
  have P2 : ∀ A g B, D.gates = A ++ g :: B → ∀ i ∈ g.inputs, i < 10 + A.length := by
    intro A g B hAB i hi
    by_contra hlt
    push_neg at hlt
    have hfalse : ∀ w : List Bool, w.length = 10 + A.length → w.getD i false = false :=
      fun w hw => List.getD_eq_default _ _ (by omega)
    have hg2 := hD.1 g (by rw [hAB]; simp)
    have P1g := P1 g (by rw [hAB]; simp)
    obtain ⟨op, ins⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg2
    obtain ⟨hop, hlen2⟩ := hg2
    have hpos : 0 < ins.length := List.length_pos_of_mem hi
    rcases hop with rfl | rfl | rfl
    · obtain ⟨D', h', hlt'⟩ := replace_better C D hD A B _ ⟨GateOp.or, []⟩ hAB (by simp)
        (by show 0 < ins.length; exact hpos) (by
          intro w hw
          simp only [gv, GateOp.eval, List.map_nil, List.any_nil]
          symm
          rw [Bool.eq_false_iff]
          intro hall
          have := List.all_eq_true.1 hall false (List.mem_map.2 ⟨i, hi, hfalse w hw⟩)
          simp at this)
      exact hmin D' h' hlt'
    · obtain ⟨D', h', hlt'⟩ := replace_better C D hD A B _ ⟨GateOp.or, ins.erase i⟩ hAB
        (by simp) (by
          show (ins.erase i).length < ins.length
          rw [List.length_erase_of_mem hi]
          exact Nat.sub_lt (List.length_pos_of_mem hi) Nat.one_pos)
        (by
          intro w hw
          simp only [gv, GateOp.eval]
          rw [Bool.eq_iff_iff]
          simp only [List.any_eq_true, List.mem_map, id]
          constructor
          · rintro ⟨c, ⟨j, hj, rfl⟩, hc⟩
            exact ⟨_, ⟨j, List.mem_of_mem_erase hj, rfl⟩, hc⟩
          · rintro ⟨c, ⟨j, hj, rfl⟩, hc⟩
            have hji : j ≠ i := by
              rintro rfl
              rw [hfalse w hw] at hc
              exact absurd hc (by simp)
            exact ⟨_, ⟨j, (List.mem_erase_of_ne hji).2 hj, rfl⟩, hc⟩)
      exact hmin D' h' hlt'
    · have h1 := P1g rfl
      rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩
      · simp at hi
      · simp only [List.mem_singleton] at hi
        subst hi
        obtain ⟨D', h', hlt'⟩ := replace_better C D hD A B _ ⟨GateOp.and, []⟩ hAB (by simp)
          (by simp) (by
            intro w hw
            have hf0 := hfalse w hw
            rw [List.getD_eq_getElem?_getD] at hf0
            simp [gv, GateOp.eval, hf0])
        exact hmin D' h' hlt'
      · simp at h1
  have P3 : ∀ A g B, D.gates = A ++ g :: B →
      D.output = 10 + A.length ∨ ∃ b ∈ B, 10 + A.length ∈ b.inputs := by
    intro A g B hAB
    by_contra hn
    push_neg at hn
    obtain ⟨D', h', hlt'⟩ := remove_better C D hD A B g hAB hn.1 hn.2
    exact hmin D' h' hlt'
  exact ⟨D, hD, P1, P2, P3⟩

lemma final (C : Circuit) (hC : FanInTwo C)
    (hdep : ∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool),
      (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧
      PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C x4 ≠
        PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C x5) :
    ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧
      PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) C ∧
      x4.size ≤ C.size ∧
      (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧
      (∀ x5 < (10 : ℕ) + x4.size,
        x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧
      (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) =>
          x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length +
        ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size),
          (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)
            - (1 : ℕ)) ≤ x4.size := by
  obtain ⟨D, ⟨hF, hf, hs⟩, P1, P2, P3⟩ := key C hC
  have P5 : D.output < 10 + D.gates.length := by
    obtain ⟨x4, x5, -, hne⟩ := hdep 0
    exact output_lt D ⟨x4, x5, by rwa [hf]⟩
  have P4 : ∀ i, i < 10 → i ∈ D.output :: D.gates.flatMap Gate.inputs := by
    intro i hi
    apply input_used D i hi
    obtain ⟨x4, x5, hag, hne⟩ := hdep ⟨i, hi⟩
    exact ⟨x4, x5, hag, by rwa [hf]⟩
  have Pin : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i < 10 + D.gates.length := by
    intro g hg i hi
    obtain ⟨A, B, hAB⟩ := List.append_of_mem hg
    have := P2 A g B hAB i hi
    have hl : D.gates.length = A.length + 1 + B.length := by
      rw [hAB]; simp only [List.length_append, List.length_cons]; omega
    omega
  have Pused : ∀ w, w < 10 + D.gates.length → w ∈ D.output :: D.gates.flatMap Gate.inputs := by
    intro w hw
    by_cases hw10 : w < 10
    · exact P4 w hw10
    · have hj : w - 10 < D.gates.length := by omega
      have hAB : D.gates = D.gates.take (w - 10) ++ D.gates[w - 10] :: D.gates.drop (w - 10 + 1) := by
        rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      have hlen : (D.gates.take (w - 10)).length = w - 10 := by simp; omega
      rcases P3 _ _ _ hAB with h | ⟨b, hb, hin⟩
      · rw [hlen] at h
        simp only [List.mem_cons]
        left
        omega
      · rw [hlen, show 10 + (w - 10) = w by omega] at hin
        simp only [List.mem_cons, List.mem_flatMap]
        right
        exact ⟨b, List.mem_of_mem_drop hb, hin⟩
  refine ⟨D, hF, hf, hs, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Circuit.size]; omega
  · intro g hg i hi
    have := Pin g hg i hi
    simp only [Circuit.size]; omega
  · intro w hw
    exact Pused w (by simpa [Circuit.size] using hw)
  · have hnb := not_bound D.gates (by
      intro g hg
      obtain ⟨hop, hl2⟩ := hF g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h | h
      · simp [h, GateOp.eval] <;> omega
      · simp [h, GateOp.eval] <;> omega
      · have := P1 g hg h
        simp [h, GateOp.eval] <;> omega)
    have hge : ∀ w ∈ Finset.range (10 + D.size),
        1 ≤ (D.output :: D.gates.flatMap Gate.inputs).count w := by
      intro w hw
      exact List.count_pos_iff.2 (Pused w (by simpa [Circuit.size] using hw))
    have hsum := sum_count_le (Finset.range (10 + D.size)) (D.output :: D.gates.flatMap Gate.inputs)
    have hcard : ∑ w ∈ Finset.range (10 + D.size), (1 : ℕ) = 10 + D.size := by simp
    have hlow : 10 + D.size ≤
        ∑ w ∈ Finset.range (10 + D.size), (D.output :: D.gates.flatMap Gate.inputs).count w := by
      have := Finset.sum_le_sum hge
      rw [hcard] at this
      exact this
    rw [Finset.sum_tsub_distrib _ hge, hcard]
    simp only [List.length_cons] at hsum
    simp only [Circuit.size] at *
    omega

end PEqualNP.Outside.L_meta_3087

theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  intro C hC hdep
  exact PEqualNP.Outside.L_meta_3087.final C hC hdep
