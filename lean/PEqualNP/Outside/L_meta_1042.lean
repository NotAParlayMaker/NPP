import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1042_aux

open PEqualNP.CircuitLowerBounds

private def pasch : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

private lemma pasch_inter : ∀ i j : Fin 4, i ≠ j → (pasch i ∩ pasch j).card ≤ 1 := by decide
private lemma pasch_sum : ∑ w : Fin 4, ((pasch w).card - 1) = 8 := by decide
private lemma pasch_card (w : Fin 4) : (pasch w).card = 3 := by revert w; decide
private lemma pasch_erase1 (v : Fin 6) :
    (∀ i j : Fin 4, i ≠ j → ((pasch i).erase v ∩ (pasch j).erase v).card ≤ 1) ∧
    (∀ w : Fin 4, ((pasch w).erase v).Nonempty) ∧
    ∑ w : Fin 4, (((pasch w).erase v).card - 1) = 6 := by revert v; decide
private lemma pasch_erase2 (a b : Fin 6) (hab : a ≠ b) :
    (∀ i j : Fin 4, i ≠ j → (((pasch i).erase a).erase b ∩ ((pasch j).erase a).erase b).card ≤ 1) ∧
    (∀ w : Fin 4, (((pasch w).erase a).erase b).Nonempty) ∧
    ∑ w : Fin 4, ((((pasch w).erase a).erase b).card - 1) = 4 := by revert a b hab; decide
private lemma pasch_not_mem_two (v : Fin 6) :
    ∃ w1 w2 : Fin 4, w1 ≠ w2 ∧ v ∉ pasch w1 ∧ v ∉ pasch w2 := by revert v; decide
private lemma pasch_mem_two (v : Fin 6) :
    ∃ w1 w2 : Fin 4, w1 ≠ w2 ∧ v ∈ pasch w1 ∧ v ∈ pasch w2 := by revert v; decide
private lemma pasch_diff (w1 w2 : Fin 4) (h : w1 ≠ w2) :
    ∃ v : Fin 6, v ∈ pasch w1 ∧ v ∉ pasch w2 := by revert w1 w2 h; decide
private lemma pasch_ne_single (w : Fin 4) (v : Fin 6) :
    ∃ u : Fin 6, u ∈ pasch w ∧ u ≠ v := by revert w v; decide

private def evalWires (gl : List Gate) (x : List Bool) : List Bool :=
  Circuit.wires ⟨gl, 0⟩ x

private def wireVal (gl : List Gate) (x : Fin 6 → Bool) (i : ℕ) : Bool :=
  (evalWires gl (List.ofFn x)).getD i false

private lemma evalWires_nil (x : List Bool) : evalWires [] x = x := rfl

private lemma evalWires_append (gl1 gl2 : List Gate) (x : List Bool) :
    evalWires (gl1 ++ gl2) x = evalWires gl2 (evalWires gl1 x) := by
  simp [evalWires, Circuit.wires, List.foldl_append]

private lemma evalWires_singleton (g : Gate) (x : List Bool) :
    evalWires [g] x = x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)] := rfl

private lemma evalWires_length (gl : List Gate) (x : List Bool) :
    (evalWires gl x).length = x.length + gl.length := by
  induction gl generalizing x with
  | nil => simp [evalWires_nil]
  | cons g rest ih =>
    change (evalWires rest (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

private lemma evalWires_prefix_getD (gl1 gl2 : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gl1.length) :
    (evalWires (gl1 ++ gl2) x).getD i false = (evalWires gl1 x).getD i false := by
  rw [evalWires_append]
  have hlen : i < (evalWires gl1 x).length := by
    rw [evalWires_length]
    exact hi
  induction gl2 generalizing gl1 x with
  | nil => rfl
  | cons g rest ih =>
    have hstep : (evalWires [g] (evalWires gl1 x)).getD i false = (evalWires gl1 x).getD i false := by
      simp only [evalWires_singleton, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    have hlen' : i < (evalWires (gl1 ++ [g]) x).length := by
      rw [evalWires_length]
      simp
      omega
    have h1 := ih (gl1 ++ [g]) x (by simp; omega) hlen'
    rw [evalWires_append] at h1
    change (evalWires rest (evalWires [g] (evalWires gl1 x))).getD i false = _
    rw [h1, hstep]

private lemma evalWires_take_getD (gl : List Gate) (k : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length + min k gl.length) :
    (evalWires gl x).getD i false = (evalWires (gl.take k) x).getD i false := by
  have hsplit : gl = gl.take k ++ gl.drop k := (List.take_append_drop k gl).symm
  conv_lhs => rw [hsplit]
  apply evalWires_prefix_getD
  rw [List.length_take]
  exact hi

private lemma evalWires_gate_getD (gl : List Gate) (j : ℕ) (hj : j < gl.length) (x : List Bool) :
    (evalWires gl x).getD (x.length + j) false =
      (gl[j]).op.eval ((gl[j]).inputs.map fun i => (evalWires (gl.take j) x).getD i false) := by
  have hsplit : gl = gl.take j ++ [gl[j]] ++ gl.drop (j + 1) := by
    have h1 := List.take_append_drop j gl
    have h2 : gl.drop j = gl[j] :: gl.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa [List.append_assoc] using h1.symm
  conv_lhs => rw [hsplit]
  rw [evalWires_prefix_getD (gl.take j ++ [gl[j]]) (gl.drop (j + 1)) x (x.length + j)]
  · rw [evalWires_append, evalWires_singleton]
    have hlen : (evalWires (gl.take j) x).length = x.length + j := by
      rw [evalWires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl
  · simp only [List.length_append, List.length_take, List.length_singleton]
    omega

private lemma evalWires_input_getD (gl : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (evalWires gl x).getD i false = x.getD i false := by
  have h := evalWires_take_getD gl 0 x i (by simpa using hi)
  simpa [evalWires_nil] using h

private lemma evalWires_ge_len (gl : List Gate) (x : List Bool) (i : ℕ)
    (hi : x.length + gl.length ≤ i) :
    (evalWires gl x).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · rfl
  · rw [evalWires_length]; exact hi

private lemma wireVal_input (gl : List Gate) (x : Fin 6 → Bool) (i : Fin 6) :
    wireVal gl x i.val = x i := by
  unfold wireVal
  rw [evalWires_input_getD gl (List.ofFn x) i.val (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

private lemma wireVal_take (gl : List Gate) (k : ℕ) (x : Fin 6 → Bool) (i : ℕ)
    (hi : i < 6 + min k gl.length) :
    wireVal gl x i = wireVal (gl.take k) x i := by
  unfold wireVal
  exact evalWires_take_getD gl k (List.ofFn x) i (by simpa using hi)

private lemma wireVal_gate (gl : List Gate) (j : ℕ) (hj : j < gl.length) (x : Fin 6 → Bool) :
    wireVal gl x (6 + j) =
      (gl[j]).op.eval ((gl[j]).inputs.map fun i => wireVal (gl.take j) x i) := by
  unfold wireVal
  have h := evalWires_gate_getD gl j hj (List.ofFn x)
  simpa using h

private lemma wireVal_gate_self (gl : List Gate) (j : ℕ) (hj : j < gl.length) (x : Fin 6 → Bool) :
    wireVal gl x (6 + j) =
      (gl[j]).op.eval ((gl[j]).inputs.map fun i => if i < 6 + j then wireVal gl x i else false) := by
  rw [wireVal_gate gl j hj x]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 6 + j
  · simp only [hi, ite_true]
    rw [wireVal_take gl j x i]
    rw [Nat.min_eq_left (Nat.le_of_lt hj)]
    exact hi
  · simp only [hi, ite_false]
    unfold wireVal
    apply evalWires_ge_len
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    omega

private lemma wireVal_ge_len (gl : List Gate) (x : Fin 6 → Bool) (i : ℕ) (hi : 6 + gl.length ≤ i) :
    wireVal gl x i = false := by
  unfold wireVal
  exact evalWires_ge_len gl (List.ofFn x) i (by simpa using hi)

private def BoolLe (a b : Bool) : Prop := a = true → b = true

private lemma gateOp_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), BoolLe l1[i] l2[i]) :
    BoolLe (op.eval l1) (op.eval l2) := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, BoolLe, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi1 : i < l1.length := hlen ▸ hi
    exact hle i hi1 hi (h1 l1[i] (List.getElem_mem hi1))
  · simp only [GateOp.eval, BoolLe, List.any_eq_true, id_eq]
    rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi1, haeq⟩ := List.getElem_of_mem ha
    have hi2 : i < l2.length := hlen ▸ hi1
    exact ⟨l2[i], List.getElem_mem hi2, hle i hi1 hi2 haeq⟩

private lemma wireVal_mono (gl : List Gate)
    (hmono : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : Fin 6 → Bool} (hxy : ∀ i : Fin 6, BoolLe (x i) (y i)) :
    ∀ w : ℕ, BoolLe (wireVal gl x w) (wireVal gl y w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · have h1 := wireVal_input gl x ⟨w, hw6⟩
      have h2 := wireVal_input gl y ⟨w, hw6⟩
      simpa [h1, h2] using hxy ⟨w, hw6⟩
    · by_cases hwlen : w < 6 + gl.length
      · set j := w - 6
        have hj : j < gl.length := by omega
        have hwj : w = 6 + j := by omega
        rw [hwj, wireVal_gate_self gl j hj x, wireVal_gate_self gl j hj y]
        apply gateOp_mono (hmono gl[j] (List.getElem_mem hj)) (by simp)
        intro idx h1 h2
        have hidx : idx < (gl[j]).inputs.length := by simpa using h1
        simp only [List.getElem_map]
        by_cases hlt : (gl[j]).inputs[idx]'hidx < 6 + j
        · simp only [hlt, ite_true]
          exact ih _ (by omega)
        · simp [hlt, BoolLe]
      · rw [wireVal_ge_len gl x w (by omega)]
        simp [BoolLe]

private lemma eval_replace_gate (gl : List Gate) (k : ℕ) (hk : k < gl.length) (g' : Gate)
    (x : Fin 6 → Bool)
    (heq : g'.op.eval (g'.inputs.map fun i => if i < 6 + k then wireVal gl x i else false) =
      wireVal gl x (6 + k)) :
    ∀ w : ℕ, wireVal (gl.set k g') x w = wireVal gl x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input (gl.set k g') x ⟨w, hw6⟩, wireVal_input gl x ⟨w, hw6⟩]
    · by_cases hwlen : w < 6 + gl.length
      · set j := w - 6
        have hj : j < gl.length := by omega
        have hj' : j < (gl.set k g').length := by simpa using hj
        have hwj : w = 6 + j := by omega
        rw [hwj, wireVal_gate_self (gl.set k g') j hj' x]
        by_cases hjk : j = k
        · subst hjk
          rw [List.getElem_set_self hj']
          rw [← heq]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < 6 + j
          · simp only [hi, ite_true]
            exact ih i (by omega)
          · simp [hi]
        · rw [List.getElem_set_ne (Ne.symm hjk) hj', wireVal_gate_self gl j hj x]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < 6 + j
          · simp only [hi, ite_true]
            exact ih i (by omega)
          · simp [hi]
      · rw [wireVal_ge_len (gl.set k g') x w (by simp; omega),
            wireVal_ge_len gl x w (by omega)]

private lemma eval_replace_unused_gate (gl : List Gate) (k : ℕ) (hk : k < gl.length) (g' : Gate)
    (hunused : ∀ j (hj : j < gl.length), k < j → 6 + k ∉ (gl[j]).inputs)
    (x : Fin 6 → Bool) :
    ∀ w : ℕ, w ≠ 6 + k → wireVal (gl.set k g') x w = wireVal gl x w := by
  intro w hne
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input (gl.set k g') x ⟨w, hw6⟩, wireVal_input gl x ⟨w, hw6⟩]
    · by_cases hwlen : w < 6 + gl.length
      · set j := w - 6
        have hj : j < gl.length := by omega
        have hj' : j < (gl.set k g').length := by simpa using hj
        have hwj : w = 6 + j := by omega
        have hjk : j ≠ k := by omega
        rw [hwj, wireVal_gate_self (gl.set k g') j hj' x,
            List.getElem_set_ne (Ne.symm hjk) hj', wireVal_gate_self gl j hj x]
        congr 1
        apply List.map_congr_left
        intro i hi_mem
        by_cases hi : i < 6 + j
        · simp only [hi, ite_true]
          have hik : i ≠ 6 + k := by
            intro heq
            subst heq
            exact hunused j hj (by omega) hi_mem
          exact ih i (by omega) hik
        · simp [hi]
      · rw [wireVal_ge_len (gl.set k g') x w (by simp; omega),
            wireVal_ge_len gl x w (by omega)]

private lemma wireVal_indep_of_no_reader (gl : List Gate) (t : ℕ) (ht : t ≤ gl.length)
    (v : Fin 6) (hno : ∀ j (hj : j < t), v.val ∉ (gl[j]'(by omega)).inputs)
    (x y : Fin 6 → Bool) (hxy : ∀ i : Fin 6, i ≠ v → x i = y i) :
    ∀ w < 6 + t, w ≠ v.val → wireVal gl x w = wireVal gl y w := by
  intro w hw hne
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input gl x ⟨w, hw6⟩, wireVal_input gl y ⟨w, hw6⟩]
      exact hxy ⟨w, hw6⟩ (fun heq => hne (by simpa using congrArg Fin.val heq))
    · set j := w - 6
      have hj : j < t := by omega
      have hjg : j < gl.length := by omega
      have hwj : w = 6 + j := by omega
      rw [hwj, wireVal_gate_self gl j hjg x, wireVal_gate_self gl j hjg y]
      congr 1
      apply List.map_congr_left
      intro i hi_mem
      by_cases hi : i < 6 + j
      · simp only [hi, ite_true]
        have hiv : i ≠ v.val := fun heq => hno j hj (heq ▸ hi_mem)
        exact ih i (by omega) (by omega) hiv
      · simp [hi]

private lemma wireVal_indep_of_no_reader_gate (gl : List Gate) (t : ℕ) (ht : t ≤ gl.length)
    (v : Fin 6) (g1 : ℕ) (hg1 : g1 < t)
    (hno_v : ∀ j (hj : j < t), j ≠ g1 → v.val ∉ (gl[j]'(by omega)).inputs)
    (hno_g1 : ∀ j (hj : j < t), g1 < j → 6 + g1 ∉ (gl[j]'(by omega)).inputs)
    (x y : Fin 6 → Bool) (hxy : ∀ i : Fin 6, i ≠ v → x i = y i) :
    ∀ w < 6 + t, w ≠ v.val → w ≠ 6 + g1 → wireVal gl x w = wireVal gl y w := by
  intro w hw hnev hneg1
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input gl x ⟨w, hw6⟩, wireVal_input gl y ⟨w, hw6⟩]
      exact hxy ⟨w, hw6⟩ (fun heq => hnev (by simpa using congrArg Fin.val heq))
    · set j := w - 6
      have hj : j < t := by omega
      have hjg : j < gl.length := by omega
      have hwj : w = 6 + j := by omega
      have hjne : j ≠ g1 := by omega
      rw [hwj, wireVal_gate_self gl j hjg x, wireVal_gate_self gl j hjg y]
      congr 1
      apply List.map_congr_left
      intro i hi_mem
      by_cases hi : i < 6 + j
      · simp only [hi, ite_true]
        have hiv : i ≠ v.val := fun heq => hno_v j hj hjne (heq ▸ hi_mem)
        have hig1 : i ≠ 6 + g1 := fun heq => hno_g1 j hj (by omega) (heq ▸ hi_mem)
        exact ih i (by omega) (by omega) hiv hig1
      · simp [hi]

private lemma wireVal_antimono_of_only_via_not (gl : List Gate) (k : ℕ) (hk : k < gl.length)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → (gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or))
    (hnot_k : (gl[k]).op = GateOp.not)
    (v : Fin 6) (g1 : ℕ) (hg1 : g1 < k)
    (hno_v : ∀ j (hj : j < gl.length), j ≠ g1 → j ≠ k → v.val ∉ (gl[j]).inputs)
    (hno_g1 : ∀ j (hj : j < gl.length), g1 < j → j ≠ k → 6 + g1 ∉ (gl[j]).inputs)
    (x : Fin 6 → Bool) :
    ∀ w, w ≠ v.val → w ≠ 6 + g1 →
      BoolLe (wireVal gl (Function.update x v true) w)
             (wireVal gl (Function.update x v false) w) := by
  intro w hnev hneg1
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input gl _ ⟨w, hw6⟩, wireVal_input gl _ ⟨w, hw6⟩]
      have hne : (⟨w, hw6⟩ : Fin 6) ≠ v := fun heq => hnev (by simpa using congrArg Fin.val heq)
      simp [Function.update_of_ne hne, BoolLe]
    · by_cases hwlen : w < 6 + gl.length
      · set j := w - 6
        have hj : j < gl.length := by omega
        have hwj : w = 6 + j := by omega
        have hjne : j ≠ g1 := by omega
        by_cases hjk : j = k
        · subst hjk
          rw [hwj, wireVal_gate_self gl j hj, wireVal_gate_self gl j hj]
          simp only [hnot_k, GateOp.eval]
          cases hin : (gl[j]).inputs with
          | nil => simp [BoolLe]
          | cons a rest =>
            simp only [List.map_cons, List.headD_cons, BoolLe, Bool.not_eq_true']
            by_cases ha : a < 6 + j
            · simp only [ha, ↓reduceIte]
              have hmono_pre : ∀ g ∈ gl.take j, g.op = GateOp.and ∨ g.op = GateOp.or := by
                intro g hg
                obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
                rw [List.getElem_take]
                have hlt : idx < j := by rw [List.length_take] at hidx; omega
                exact hvalid idx (by omega) (by omega)
              have hm := wireVal_mono (gl.take j) hmono_pre
                (x := Function.update x v false) (y := Function.update x v true)
                (fun i => by by_cases hi : i = v <;> simp [hi, BoolLe]) a
              have h1 := wireVal_take gl j (Function.update x v false) a (by rw [Nat.min_eq_left (Nat.le_of_lt hj)]; exact ha)
              have h2 := wireVal_take gl j (Function.update x v true) a (by rw [Nat.min_eq_left (Nat.le_of_lt hj)]; exact ha)
              rw [h1, h2]
              intro ht
              cases hval : wireVal (gl.take j) (Function.update x v false) a with
              | false => rfl
              | true => have := hm hval; rw [ht] at this; simp at this
            · simp [ha]
        · rw [hwj, wireVal_gate_self gl j hj, wireVal_gate_self gl j hj]
          apply gateOp_mono (hvalid j hj hjk) (by simp)
          intro idx h1 h2
          have hidx : idx < (gl[j]).inputs.length := by simpa using h1
          simp only [List.getElem_map]
          by_cases hlt : (gl[j]).inputs[idx]'hidx < 6 + j
          · simp only [hlt, ite_true]
            have hmem : (gl[j]).inputs[idx]'hidx ∈ (gl[j]).inputs := List.getElem_mem hidx
            have hiv : (gl[j]).inputs[idx]'hidx ≠ v.val := fun heq => hno_v j hj hjne hjk (heq ▸ hmem)
            have hig1 : (gl[j]).inputs[idx]'hidx ≠ 6 + g1 := fun heq => hno_g1 j hj (by omega) hjk (heq ▸ hmem)
            exact ih _ (by omega) hiv hig1
          · simp [hlt, BoolLe]
      · rw [wireVal_ge_len gl _ w (by omega)]
        simp [BoolLe]

private def applyRho (ρ : Fin 6 → Option Bool) (x : Fin 6 → Bool) : Fin 6 → Bool :=
  fun i => match ρ i with | some b => b | none => x i

private def initEnv (ρ : Fin 6 → Option Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin 6 => match ρ i with | some b => Sum.inl b | none => Sum.inr i.val

private def evalSym (gl' : List Gate) (x : Fin 6 → Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr w => wireVal gl' x w

private def simpStep (k : ℕ) (bnot : Bool)
    (st : List Gate × List (Bool ⊕ ℕ) × Finset ℕ) (gj : Gate × ℕ) :
    List Gate × List (Bool ⊕ ℕ) × Finset ℕ :=
  let (gl', env, elim) := st
  let (g, j) := gj
  if j = k then
    (gl', env ++ [Sum.inl bnot], insert j elim)
  else
    let look (i : ℕ) : Bool ⊕ ℕ := if i < 6 + j then env.getD i (Sum.inl false) else Sum.inl false
    match g.inputs with
    | [] =>
      let b := match g.op with | GateOp.and => true | _ => false
      (gl', env ++ [Sum.inl b], insert j elim)
    | [a] =>
      (gl', env ++ [look a], insert j elim)
    | [a, b] =>
      let va := look a
      let vb := look b
      match g.op, va, vb with
      | GateOp.and, Sum.inl false, _ => (gl', env ++ [Sum.inl false], insert j elim)
      | GateOp.and, _, Sum.inl false => (gl', env ++ [Sum.inl false], insert j elim)
      | GateOp.and, Sum.inl true, v => (gl', env ++ [v], insert j elim)
      | GateOp.and, v, Sum.inl true => (gl', env ++ [v], insert j elim)
      | GateOp.or, Sum.inl true, _ => (gl', env ++ [Sum.inl true], insert j elim)
      | GateOp.or, _, Sum.inl true => (gl', env ++ [Sum.inl true], insert j elim)
      | GateOp.or, Sum.inl false, v => (gl', env ++ [v], insert j elim)
      | GateOp.or, v, Sum.inl false => (gl', env ++ [v], insert j elim)
      | op, Sum.inr a', Sum.inr b' =>
        (gl' ++ [⟨op, [a', b']⟩], env ++ [Sum.inr (6 + gl'.length)], elim)
      | _, _, _ => (gl', env ++ [Sum.inl false], insert j elim)
    | _ => (gl', env ++ [Sum.inl false], insert j elim)

private def runSimpTake (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool) (t : ℕ) :
    List Gate × List (Bool ⊕ ℕ) × Finset ℕ :=
  ((gl.take t).zipIdx).foldl (simpStep k bnot) ([], initEnv ρ, ∅)

private lemma runSimpTake_succ (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (t : ℕ) (ht : t < gl.length) :
    runSimpTake gl k bnot ρ (t + 1) = simpStep k bnot (runSimpTake gl k bnot ρ t) (gl[t], t) := by
  unfold runSimpTake
  have htake : (gl.take (t + 1)).zipIdx = (gl.take t).zipIdx ++ [(gl[t], t)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.zipIdx_append]
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt ht)]
  rw [htake, List.foldl_append]
  rfl

private lemma evalSym_append_gate (gl' : List Gate) (g : Gate) (x : Fin 6 → Bool) (v : Bool ⊕ ℕ)
    (hv : ∀ w, v = Sum.inr w → w < 6 + gl'.length) :
    evalSym (gl' ++ [g]) x v = evalSym gl' x v := by
  cases v with
  | inl b => rfl
  | inr w =>
    simp only [evalSym, wireVal]
    apply evalWires_prefix_getD
    simpa using hv w rfl

private lemma simpStep_env_append (k : ℕ) (bnot : Bool)
    (st : List Gate × List (Bool ⊕ ℕ) × Finset ℕ) (gj : Gate × ℕ) :
    ∃ v, (simpStep k bnot st gj).2.1 = st.2.1 ++ [v] ∧ st.2.2 ⊆ (simpStep k bnot st gj).2.2 := by
  rcases st with ⟨gl', env, elim⟩
  rcases gj with ⟨g, j⟩
  unfold simpStep
  dsimp only
  split_ifs
  · exact ⟨_, rfl, Finset.subset_insert _ _⟩
  · cases g.inputs with
    | nil => exact ⟨_, rfl, Finset.subset_insert _ _⟩
    | cons a r1 =>
      cases r1 with
      | nil => exact ⟨_, rfl, Finset.subset_insert _ _⟩
      | cons b r2 =>
        cases r2 with
        | nil =>
          dsimp only
          split <;> first | exact ⟨_, rfl, Finset.subset_insert _ _⟩ | exact ⟨_, rfl, Finset.Subset.refl _⟩
        | cons c r3 => exact ⟨_, rfl, Finset.subset_insert _ _⟩

private lemma runSimpTake_env_len (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (t : ℕ) (ht : t ≤ gl.length) :
    (runSimpTake gl k bnot ρ t).2.1.length = 6 + t := by
  induction t with
  | zero => simp [runSimpTake, initEnv]
  | succ t ih =>
    rw [runSimpTake_succ gl k bnot ρ t (by omega)]
    obtain ⟨v, hv, _⟩ := simpStep_env_append k bnot (runSimpTake gl k bnot ρ t) (gl[t], t)
    rw [hv, List.length_append, List.length_singleton, ih (by omega)]
    omega

private lemma runSimpTake_prefix (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (t1 t2 : ℕ) (h12 : t1 ≤ t2) (h2 : t2 ≤ gl.length) :
    (∀ i < 6 + t1, (runSimpTake gl k bnot ρ t2).2.1.getD i (Sum.inl false) =
      (runSimpTake gl k bnot ρ t1).2.1.getD i (Sum.inl false)) ∧
    (runSimpTake gl k bnot ρ t1).2.2 ⊆ (runSimpTake gl k bnot ρ t2).2.2 := by
  induction t2 with
  | zero =>
    have : t1 = 0 := by omega
    subst this
    exact ⟨fun _ _ => rfl, Finset.Subset.refl _⟩
  | succ t2 ih =>
    by_cases heq : t1 = t2 + 1
    · subst heq; exact ⟨fun _ _ => rfl, Finset.Subset.refl _⟩
    · have h12' : t1 ≤ t2 := by omega
      have h2' : t2 < gl.length := by omega
      obtain ⟨ih_env, ih_sub⟩ := ih h12' (Nat.le_of_lt h2')
      rw [runSimpTake_succ gl k bnot ρ t2 h2']
      obtain ⟨v, hv_env, hv_sub⟩ := simpStep_env_append k bnot (runSimpTake gl k bnot ρ t2) (gl[t2], t2)
      have hlen2 := runSimpTake_env_len gl k bnot ρ t2 (Nat.le_of_lt h2')
      constructor
      · intro i hi
        rw [hv_env, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD]
        exact ih_env i hi
      · exact Finset.Subset.trans ih_sub hv_sub

private lemma simpStep_invariants (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2)
    (hbnot : ∀ x : Fin 6 → Bool, k < gl.length → wireVal gl (applyRho ρ x) (6 + k) = bnot) :
    ∀ t (ht : t ≤ gl.length),
      let res := runSimpTake gl k bnot ρ t
      res.2.1.length = 6 + t ∧
      (∀ j ∈ res.2.2, j < t) ∧
      res.1.length + res.2.2.card = t ∧
      (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ v ∈ res.2.1, ∀ w, v = Sum.inr w → w < 6 + res.1.length) ∧
      (∀ x : Fin 6 → Bool, ∀ i < 6 + t,
        evalSym res.1 x (res.2.1.getD i (Sum.inl false)) = wireVal gl (applyRho ρ x) i) := by
  intro t ht
  induction t with
  | zero =>
    refine ⟨by simp [runSimpTake, initEnv], by simp [runSimpTake], by simp [runSimpTake],
      by simp [runSimpTake], ?_, ?_⟩
    · intro v hv w hw
      simp only [runSimpTake, List.take_zero, List.zipIdx_nil, List.foldl_nil, initEnv,
        List.mem_ofFn] at hv
      obtain ⟨i, rfl⟩ := hv
      cases hρ : ρ i with
      | some b => simp [hρ] at hw
      | none => simp [hρ] at hw; subst hw; exact i.isLt
    · intro x i hi
      have hi6 : i < 6 := by omega
      rw [wireVal_input gl (applyRho ρ x) ⟨i, hi6⟩]
      simp only [runSimpTake, List.take_zero, List.zipIdx_nil, List.foldl_nil, initEnv,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi6, ↓reduceDIte, Option.getD_some,
        applyRho]
      cases hρ : ρ ⟨i, hi6⟩ with
      | some b => rfl
      | none =>
        simp only [evalSym]
        exact wireVal_input [] x ⟨i, hi6⟩
  | succ t ih =>
    have ht' : t < gl.length := by omega
    obtain ⟨hlen, hlt_elim, hsum, hmono', hbound, heval⟩ := ih (Nat.le_of_lt ht')
    dsimp only
    rw [runSimpTake_succ gl k bnot ρ t ht']
    rcases hres : runSimpTake gl k bnot ρ t with ⟨gl', env, elim⟩
    rw [hres] at hlen hlt_elim hsum hmono' hbound heval
    dsimp only at hlen hlt_elim hsum hmono' hbound heval
    have hnotmem : t ∉ elim := fun h => Nat.lt_irrefl t (hlt_elim t h)
    have hcard_ins : (insert t elim).card = elim.card + 1 := Finset.card_insert_of_notMem hnotmem
    have hlt_ins : ∀ j ∈ insert t elim, j < t + 1 := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · omega
      · exact Nat.lt_succ_of_lt (hlt_elim j hj')
    have hstep_no_gate : ∀ (v : Bool ⊕ ℕ),
        (∀ w, v = Sum.inr w → w < 6 + gl'.length) →
        (∀ x, evalSym gl' x v = wireVal gl (applyRho ρ x) (6 + t)) →
        (env ++ [v]).length = 6 + (t + 1) ∧
        (∀ j ∈ insert t elim, j < t + 1) ∧
        gl'.length + (insert t elim).card = t + 1 ∧
        (∀ g ∈ gl', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        (∀ u ∈ env ++ [v], ∀ w, u = Sum.inr w → w < 6 + gl'.length) ∧
        (∀ x : Fin 6 → Bool, ∀ i < 6 + (t + 1),
          evalSym gl' x ((env ++ [v]).getD i (Sum.inl false)) = wireVal gl (applyRho ρ x) i) := by
      intro v hv_bnd hv_eval
      refine ⟨by simp [hlen]; omega, hlt_ins, by omega, hmono', ?_, ?_⟩
      · intro u hu w hw
        rcases List.mem_append.mp hu with hu1 | hu2
        · exact hbound u hu1 w hw
        · simp only [List.mem_singleton] at hu2
          subst hu2
          exact hv_bnd w hw
      · intro x i hi
        by_cases hit : i < 6 + t
        · have hlen_i : i < env.length := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen_i, ← List.getD_eq_getElem?_getD]
          exact heval x i hit
        · have hieq : i = 6 + t := by omega
          subst hieq
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          exact hv_eval x
    unfold simpStep
    dsimp only
    by_cases htk : t = k
    · rw [if_pos htk]
      have hbk : ∀ x, evalSym gl' x (Sum.inl bnot) = wireVal gl (applyRho ρ x) (6 + t) := by
        intro x; rw [htk]; exact (hbnot x (htk ▸ ht')).symm
      exact hstep_no_gate (Sum.inl bnot) (by intro w hw; simp at hw) hbk
    · rw [if_neg htk]
      have hgate_op := (hvalid t ht').1 htk
      have hgate_len := (hvalid t ht').2
      set g := gl[t]
      have hlook_bnd : ∀ i, ∀ w,
          (if i < 6 + t then env.getD i (Sum.inl false) else Sum.inl false) = Sum.inr w →
          w < 6 + gl'.length := by
        intro i w hw
        split_ifs at hw with hi
        have hlen_i : i < env.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_i, Option.getD_some] at hw
        exact hbound env[i] (List.getElem_mem hlen_i) w hw
      have hlook_eval : ∀ x i,
          evalSym gl' x (if i < 6 + t then env.getD i (Sum.inl false) else Sum.inl false) =
          if i < 6 + t then wireVal gl (applyRho ρ x) i else false := by
        intro x i
        split_ifs with hi
        · exact heval x i hi
        · rfl
      cases hin : g.inputs with
      | nil =>
        exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
          rw [wireVal_gate_self gl t ht' (applyRho ρ x)]
          change _ = g.op.eval (g.inputs.map _)
          rw [hin]
          rcases hgate_op with hop | hop <;> simp [hop, evalSym, GateOp.eval]
      | cons a rest =>
        cases rest with
        | nil =>
          exact hstep_no_gate _ (hlook_bnd a) fun x => by
            rw [wireVal_gate_self gl t ht' (applyRho ρ x)]
            change _ = g.op.eval (g.inputs.map _)
            rw [hin, List.map_cons, List.map_nil, ← hlook_eval x a]
            rcases hgate_op with hop | hop <;> simp [hop, GateOp.eval]
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            have hgate_e : ∀ x, wireVal gl (applyRho ρ x) (6 + t) =
                g.op.eval [evalSym gl' x (if a < 6 + t then env.getD a (Sum.inl false) else Sum.inl false),
                           evalSym gl' x (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false)] := by
              intro x
              rw [wireVal_gate_self gl t ht' (applyRho ρ x)]
              change g.op.eval (g.inputs.map _) = _
              rw [hin, List.map_cons, List.map_cons, List.map_nil, hlook_eval x a, hlook_eval x b]
            have hstep_gate : ∀ (op : GateOp) (wa wb : ℕ),
                (op = GateOp.and ∨ op = GateOp.or) →
                (if a < 6 + t then env.getD a (Sum.inl false) else Sum.inl false) = Sum.inr wa →
                (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false) = Sum.inr wb →
                g.op = op →
                let ng : Gate := ⟨op, [wa, wb]⟩
                (env ++ [Sum.inr (6 + gl'.length)]).length = 6 + (t + 1) ∧
                (∀ j ∈ elim, j < t + 1) ∧
                (gl' ++ [ng]).length + elim.card = t + 1 ∧
                (∀ g0 ∈ gl' ++ [ng], (g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs.length = 2) ∧
                (∀ u ∈ env ++ [Sum.inr (6 + gl'.length)], ∀ w, u = Sum.inr w → w < 6 + (gl' ++ [ng]).length) ∧
                (∀ x : Fin 6 → Bool, ∀ i < 6 + (t + 1),
                  evalSym (gl' ++ [ng]) x ((env ++ [Sum.inr (6 + gl'.length)]).getD i (Sum.inl false)) =
                    wireVal gl (applyRho ρ x) i) := by
              intro op wa wb hop_ok hva hvb hop_eq
              let ng : Gate := ⟨op, [wa, wb]⟩
              have hwa : wa < 6 + gl'.length := hlook_bnd a wa hva
              have hwb : wb < 6 + gl'.length := hlook_bnd b wb hvb
              refine ⟨by simp [hlen]; omega, fun j hj => Nat.lt_succ_of_lt (hlt_elim j hj),
                by simp; omega, ?_, ?_, ?_⟩
              · intro g0 hg0
                rcases List.mem_append.mp hg0 with h1 | h2
                · exact hmono' g0 h1
                · simp only [List.mem_singleton] at h2; subst h2; exact ⟨hop_ok, rfl⟩
              · intro u hu w hw
                rcases List.mem_append.mp hu with h1 | h2
                · have := hbound u h1 w hw; simp; omega
                · simp only [List.mem_singleton] at h2; subst h2; simp at hw; subst hw; simp
              · intro x i hi
                by_cases hit : i < 6 + t
                · have hlen_i : i < env.length := by omega
                  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen_i,
                      ← List.getD_eq_getElem?_getD]
                  rw [evalSym_append_gate]
                  · exact heval x i hit
                  · intro w hw
                    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_i,
                        Option.getD_some] at hw
                    exact hbound env[i] (List.getElem_mem hlen_i) w hw
                · have hieq : i = 6 + t := by omega
                  subst hieq
                  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
                      hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
                  rw [hgate_e x, hop_eq, hva, hvb]
                  change wireVal (gl' ++ [ng]) x (6 + gl'.length) = _
                  have hnew := wireVal_gate_self (gl' ++ [ng]) gl'.length (by simp) x
                  rw [hnew]
                  simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
                    List.getElem_cons_zero, ng, List.map_cons, List.map_nil, hwa, hwb, ↓reduceIte]
                  congr 1
                  have e1 : wireVal (gl' ++ [ng]) x wa = wireVal gl' x wa :=
                    evalSym_append_gate gl' ng x (Sum.inr wa) (by intro w hw; injection hw with hw; omega)
                  have e2 : wireVal (gl' ++ [ng]) x wb = wireVal gl' x wb :=
                    evalSym_append_gate gl' ng x (Sum.inr wb) (by intro w hw; injection hw with hw; omega)
                  rw [e1, e2]
                  rfl
            rcases hgate_op with hop | hop
            · rw [hop]
              cases hva : (if a < 6 + t then env.getD a (Sum.inl false) else Sum.inl false) with
              | inl ba =>
                cases ba
                · simp only [hva]
                  exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                    rw [hgate_e x, hop, hva]; rfl
                · cases hvb : (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false) with
                  | inl bb =>
                    cases bb
                    · simp only [hva, hvb]
                      exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                        rw [hgate_e x, hop, hva, hvb]; rfl
                    · simp only [hva, hvb]
                      exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                        rw [hgate_e x, hop, hva, hvb]; rfl
                  | inr wb =>
                    simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; exact hlook_bnd b w (hvb.trans hw)) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
              | inr wa =>
                cases hvb : (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false) with
                | inl bb =>
                  cases bb
                  · simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
                  · simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; exact hlook_bnd a w (hva.trans hw)) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
                | inr wb =>
                  simp only [hva, hvb]
                  exact hstep_gate GateOp.and wa wb (Or.inl rfl) hva hvb hop
            · rw [hop]
              cases hva : (if a < 6 + t then env.getD a (Sum.inl false) else Sum.inl false) with
              | inl ba =>
                cases ba
                · cases hvb : (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false) with
                  | inl bb =>
                    cases bb
                    · simp only [hva, hvb]
                      exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                        rw [hgate_e x, hop, hva, hvb]; rfl
                    · simp only [hva, hvb]
                      exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                        rw [hgate_e x, hop, hva, hvb]; rfl
                  | inr wb =>
                    simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; exact hlook_bnd b w (hvb.trans hw)) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
                · simp only [hva]
                  exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                    rw [hgate_e x, hop, hva]; rfl
              | inr wa =>
                cases hvb : (if b < 6 + t then env.getD b (Sum.inl false) else Sum.inl false) with
                | inl bb =>
                  cases bb
                  · simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; exact hlook_bnd a w (hva.trans hw)) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
                  · simp only [hva, hvb]
                    exact hstep_no_gate _ (by intro w hw; simp at hw) fun x => by
                      rw [hgate_e x, hop, hva, hvb]; simp [evalSym, GateOp.eval]
                | inr wb =>
                  simp only [hva, hvb]
                  exact hstep_gate GateOp.or wa wb (Or.inr rfl) hva hvb hop
          | cons c rest3 =>
            simp [hin] at hgate_len

private lemma simp_mem_elim_k (gl : List Gate) (k : ℕ) (hk : k < gl.length) (bnot : Bool)
    (ρ : Fin 6 → Option Bool) :
    k ∈ (runSimpTake gl k bnot ρ gl.length).2.2 ∧
    (runSimpTake gl k bnot ρ gl.length).2.1.getD (6 + k) (Sum.inl false) = Sum.inl bnot := by
  have hlen_k := runSimpTake_env_len gl k bnot ρ k (Nat.le_of_lt hk)
  have hpre := runSimpTake_prefix gl k bnot ρ (k + 1) gl.length hk (le_refl _)
  have hstep : runSimpTake gl k bnot ρ (k + 1) =
      ((runSimpTake gl k bnot ρ k).1, (runSimpTake gl k bnot ρ k).2.1 ++ [Sum.inl bnot],
       insert k (runSimpTake gl k bnot ρ k).2.2) := by
    rw [runSimpTake_succ gl k bnot ρ k hk]
    simp [simpStep]
  constructor
  · apply hpre.2
    rw [hstep]
    exact Finset.mem_insert_self k _
  · rw [hpre.1 (6 + k) (by omega), hstep]
    dsimp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen_k, Nat.sub_self]
    rfl

private lemma simp_mem_elim_of_const_input (gl : List Gate) (k : ℕ) (bnot : Bool)
    (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2)
    (j : ℕ) (hj : j < gl.length) (a : ℕ) (ha_mem : a ∈ (gl[j]).inputs) (ha_lt : a < 6 + j)
    (b : Bool) (hconst : (runSimpTake gl k bnot ρ gl.length).2.1.getD a (Sum.inl false) = Sum.inl b) :
    j ∈ (runSimpTake gl k bnot ρ gl.length).2.2 := by
  have hpre_j := runSimpTake_prefix gl k bnot ρ j gl.length (Nat.le_of_lt hj) (le_refl _)
  have hpre_j1 := runSimpTake_prefix gl k bnot ρ (j + 1) gl.length hj (le_refl _)
  have hconst_j : (runSimpTake gl k bnot ρ j).2.1.getD a (Sum.inl false) = Sum.inl b := by
    rw [← hpre_j.1 a ha_lt]; exact hconst
  apply hpre_j1.2
  rw [runSimpTake_succ gl k bnot ρ j hj]
  unfold simpStep
  dsimp only
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    have hlen_in := (hvalid j hj).2
    cases hin : (gl[j]).inputs with
    | nil => simp [hin] at ha_mem
    | cons u r1 =>
      cases r1 with
      | nil => simp
      | cons v r2 =>
        cases r2 with
        | nil =>
          rw [hin] at ha_mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_mem
          rcases ha_mem with rfl | rfl
          · simp only [ha_lt, ↓reduceIte, hconst_j]
            rcases (hvalid j hj).1 hjk with hop | hop <;> rw [hop] <;> cases b
            · exact Finset.mem_insert_self j _
            · cases (if v < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD v (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
            · cases (if v < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD v (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
            · exact Finset.mem_insert_self j _
          · simp only [ha_lt, ↓reduceIte, hconst_j]
            rcases (hvalid j hj).1 hjk with hop | hop <;> rw [hop] <;> cases b
            · cases (if u < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD u (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
            · cases (if u < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD u (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
            · cases (if u < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD u (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
            · cases (if u < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD u (Sum.inl false) else Sum.inl false) with
              | inl bb => cases bb <;> exact Finset.mem_insert_self j _
              | inr _ => exact Finset.mem_insert_self j _
        | cons w r3 => simp [hin] at hlen_in

private lemma simp_env_input (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (i : Fin 6) :
    (runSimpTake gl k bnot ρ gl.length).2.1.getD i.val (Sum.inl false) =
      match ρ i with | some b => Sum.inl b | none => Sum.inr i.val := by
  have hpre := runSimpTake_prefix gl k bnot ρ 0 gl.length (Nat.zero_le _) (le_refl _)
  rw [hpre.1 i.val (by omega)]
  simp only [runSimpTake, List.take_zero, List.zipIdx_nil, List.foldl_nil, initEnv,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

private lemma list_getD_append_last {α : Type*} (l : List α) (x d : α) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h, Nat.sub_self]
  rfl

private lemma simp_env_const_of_or_true (gl : List Gate) (k : ℕ) (bnot : Bool)
    (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2)
    (j : ℕ) (hj : j < gl.length) (hjk : j ≠ k) (hop : (gl[j]).op = GateOp.or)
    (a : ℕ) (ha_mem : a ∈ (gl[j]).inputs) (ha_lt : a < 6 + j)
    (hconst : (runSimpTake gl k bnot ρ gl.length).2.1.getD a (Sum.inl false) = Sum.inl true) :
    (runSimpTake gl k bnot ρ gl.length).2.1.getD (6 + j) (Sum.inl false) = Sum.inl true := by
  have hlen_j := runSimpTake_env_len gl k bnot ρ j (Nat.le_of_lt hj)
  have hpre_j := runSimpTake_prefix gl k bnot ρ j gl.length (Nat.le_of_lt hj) (le_refl _)
  have hpre_j1 := runSimpTake_prefix gl k bnot ρ (j + 1) gl.length hj (le_refl _)
  have hconst_j : (runSimpTake gl k bnot ρ j).2.1.getD a (Sum.inl false) = Sum.inl true := by
    rw [← hpre_j.1 a ha_lt]; exact hconst
  rw [hpre_j1.1 (6 + j) (by omega), runSimpTake_succ gl k bnot ρ j hj]
  unfold simpStep
  simp only [hjk, ↓reduceIte]
  have hlen_in := (hvalid j hj).2
  cases hin : (gl[j]).inputs with
  | nil => simp [hin] at ha_mem
  | cons u r1 =>
    cases r1 with
    | nil =>
      rw [hin] at ha_mem; simp only [List.mem_singleton] at ha_mem; subst ha_mem
      dsimp only
      rw [list_getD_append_last _ _ _ _ hlen_j, if_pos ha_lt]
      exact hconst_j
    | cons v r2 =>
      cases r2 with
      | nil =>
        rw [hin] at ha_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha_mem
        rcases ha_mem with rfl | rfl
        · dsimp only
          rw [hop]
          simp only [ha_lt, ↓reduceIte, hconst_j]
          exact list_getD_append_last _ _ _ _ hlen_j
        · dsimp only
          rw [hop]
          simp only [ha_lt, ↓reduceIte, hconst_j]
          cases (if u < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD u (Sum.inl false) else Sum.inl false) with
          | inl bb => cases bb <;> exact list_getD_append_last _ _ _ _ hlen_j
          | inr _ => exact list_getD_append_last _ _ _ _ hlen_j
      | cons w r3 => simp [hin] at hlen_in

private lemma simp_env_const_of_all_const (gl : List Gate) (k : ℕ) (bnot : Bool)
    (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2)
    (j : ℕ) (hj : j < gl.length) (hjk : j ≠ k)
    (hall : ∀ a ∈ (gl[j]).inputs, a < 6 + j → ∃ b, (runSimpTake gl k bnot ρ gl.length).2.1.getD a (Sum.inl false) = Sum.inl b) :
    ∃ b, (runSimpTake gl k bnot ρ gl.length).2.1.getD (6 + j) (Sum.inl false) = Sum.inl b := by
  have hlen_j := runSimpTake_env_len gl k bnot ρ j (Nat.le_of_lt hj)
  have hpre_j := runSimpTake_prefix gl k bnot ρ j gl.length (Nat.le_of_lt hj) (le_refl _)
  have hpre_j1 := runSimpTake_prefix gl k bnot ρ (j + 1) gl.length hj (le_refl _)
  have hall_j : ∀ a ∈ (gl[j]).inputs, ∃ b,
      (if a < 6 + j then (runSimpTake gl k bnot ρ j).2.1.getD a (Sum.inl false) else Sum.inl false) = Sum.inl b := by
    intro a ha
    by_cases hlt : a < 6 + j
    · obtain ⟨b, hb⟩ := hall a ha hlt
      exact ⟨b, by rw [if_pos hlt, ← hpre_j.1 a hlt]; exact hb⟩
    · exact ⟨false, by simp [hlt]⟩
  rw [hpre_j1.1 (6 + j) (by omega), runSimpTake_succ gl k bnot ρ j hj]
  unfold simpStep
  simp only [hjk, ↓reduceIte]
  have hlen_in := (hvalid j hj).2
  cases hin : (gl[j]).inputs with
  | nil => exact ⟨_, list_getD_append_last _ _ _ _ hlen_j⟩
  | cons u r1 =>
    cases r1 with
    | nil =>
      obtain ⟨b, hb⟩ := hall_j u (by simp [hin])
      exact ⟨b, by dsimp only; rw [list_getD_append_last _ _ _ _ hlen_j]; exact hb⟩
    | cons v r2 =>
      cases r2 with
      | nil =>
        obtain ⟨bu, hbu⟩ := hall_j u (by simp [hin])
        obtain ⟨bv, hbv⟩ := hall_j v (by simp [hin])
        dsimp only
        rw [hbu, hbv]
        rcases (hvalid j hj).1 hjk with hop | hop <;> rw [hop] <;> cases bu <;> cases bv <;>
          exact ⟨_, list_getD_append_last _ _ _ _ hlen_j⟩
      | cons w r3 => simp [hin] at hlen_in

private lemma simp_env_true_of_zero_true (gl : List Gate) (k : ℕ) (hk : k < gl.length)
    (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2) :
    ∀ w < 6 + k, wireVal gl (fun _ => false) w = true →
      (runSimpTake gl k bnot ρ gl.length).2.1.getD w (Sum.inl false) = Sum.inl true := by
  intro w hw hval
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw6 : w < 6
    · rw [wireVal_input gl (fun _ => false) ⟨w, hw6⟩] at hval; simp at hval
    · set j := w - 6
      have hj : j < k := by omega
      have hjg : j < gl.length := by omega
      have hjk : j ≠ k := by omega
      have hwj : w = 6 + j := by omega
      rw [hwj] at hval ⊢
      rw [wireVal_gate_self gl j hjg (fun _ => false)] at hval
      have hlen_j := runSimpTake_env_len gl k bnot ρ j (Nat.le_of_lt hjg)
      have hpre_j := runSimpTake_prefix gl k bnot ρ j gl.length (Nat.le_of_lt hjg) (le_refl _)
      have hpre_j1 := runSimpTake_prefix gl k bnot ρ (j + 1) gl.length hjg (le_refl _)
      have hlen_in := (hvalid j hjg).2
      rcases (hvalid j hjg).1 hjk with hop | hop
      · rw [hpre_j1.1 (6 + j) (by omega), runSimpTake_succ gl k bnot ρ j hjg]
        unfold simpStep; simp only [hjk, ↓reduceIte]
        cases hin : (gl[j]).inputs with
        | nil =>
          dsimp only; rw [hop]; exact list_getD_append_last _ _ _ _ hlen_j
        | cons u r1 =>
          cases r1 with
          | nil =>
            simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
              List.all_nil, id_eq, Bool.and_true] at hval
            have hu_lt : u < 6 + j := by by_contra hge; simp [hge] at hval
            simp only [hu_lt, ↓reduceIte] at hval
            have hu_env := ih u (by omega) (by omega) hval
            dsimp only; rw [list_getD_append_last _ _ _ _ hlen_j, if_pos hu_lt, ← hpre_j.1 u hu_lt]; exact hu_env
          | cons v r2 =>
            cases r2 with
            | nil =>
              simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hval
              have hu_lt : u < 6 + j := by by_contra hge; simp [hge] at hval
              have hv_lt : v < 6 + j := by by_contra hge; simp [hge] at hval
              simp only [hu_lt, hv_lt, ↓reduceIte] at hval
              have hu_env := ih u (by omega) (by omega) hval.1
              have hv_env := ih v (by omega) (by omega) hval.2
              dsimp only; rw [hop, if_pos hu_lt, if_pos hv_lt, ← hpre_j.1 u hu_lt, ← hpre_j.1 v hv_lt, hu_env, hv_env]
              exact list_getD_append_last _ _ _ _ hlen_j
            | cons z r3 => simp [hin] at hlen_in
      · cases hin : (gl[j]).inputs with
        | nil => simp [hop, hin, GateOp.eval] at hval
        | cons u r1 =>
          cases r1 with
          | nil =>
            simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
              List.any_nil, id_eq, Bool.or_false] at hval
            have hu_lt : u < 6 + j := by by_contra hge; simp [hge] at hval
            simp only [hu_lt, ↓reduceIte] at hval
            exact simp_env_const_of_or_true gl k bnot ρ hvalid j hjg hjk hop u (by simp [hin]) hu_lt
              (ih u (by omega) (by omega) hval)
          | cons v r2 =>
            cases r2 with
            | nil =>
              simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
                List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hval
              rcases hval with hu | hv
              · have hu_lt : u < 6 + j := by by_contra hge; simp [hge] at hu
                simp only [hu_lt, ↓reduceIte] at hu
                exact simp_env_const_of_or_true gl k bnot ρ hvalid j hjg hjk hop u (by simp [hin]) hu_lt
                  (ih u (by omega) (by omega) hu)
              · have hv_lt : v < 6 + j := by by_contra hge; simp [hge] at hv
                simp only [hv_lt, ↓reduceIte] at hv
                exact simp_env_const_of_or_true gl k bnot ρ hvalid j hjg hjk hop v (by simp [hin]) hv_lt
                  (ih v (by omega) (by omega) hv)
            | cons z r3 => simp [hin] at hlen_in

private lemma apply_hmono_simp
    (hmono : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      ∀ (gates : List Gate) (out : Fin m → ℕ),
        (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ (w : Fin m) (x : Fin n → Bool),
          Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
        ∑ w, ((S w).card - 1) ≤ gates.length)
    (gl : List Gate) (k : ℕ) (bnot : Bool) (ρ : Fin 6 → Option Bool)
    (hvalid : ∀ j (hj : j < gl.length),
      (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2)
    (hbnot : ∀ x : Fin 6 → Bool, k < gl.length → wireVal gl (applyRho ρ x) (6 + k) = bnot)
    (m : ℕ) (S : Fin m → Finset (Fin 6)) (out : Fin m → ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hnonempty : ∀ w : Fin m, (S w).Nonempty)
    (heval_out : ∀ (w : Fin m) (x : Fin 6 → Bool),
      wireVal gl (applyRho ρ x) (out w) = decide (∃ v ∈ S w, x v = true)) :
    ∑ w, ((S w).card - 1) ≤ (runSimpTake gl k bnot ρ gl.length).1.length := by
  have hinv := simpStep_invariants gl k bnot ρ hvalid hbnot gl.length (le_refl _)
  set res := runSimpTake gl k bnot ρ gl.length
  have hout_lt : ∀ w : Fin m, out w < 6 + gl.length := by
    intro w
    by_contra hge
    have h1 := wireVal_ge_len gl (applyRho ρ (fun _ => true)) (out w) (by omega)
    rw [heval_out w (fun _ => true)] at h1
    obtain ⟨v, hv⟩ := hnonempty w
    have h2 : decide (∃ v ∈ S w, (fun _ : Fin 6 => true) v = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨v, hv, by simp⟩
    rw [h2] at h1
    simp at h1
  have hout_inr : ∀ w : Fin m, ∃ o', res.2.1.getD (out w) (Sum.inl false) = Sum.inr o' := by
    intro w
    cases h : res.2.1.getD (out w) (Sum.inl false) with
    | inr o' => exact ⟨o', rfl⟩
    | inl b =>
      have h0 := hinv.2.2.2.2.2 (fun _ => false) (out w) (hout_lt w)
      have h1 := hinv.2.2.2.2.2 (fun _ => true) (out w) (hout_lt w)
      rw [h, heval_out w (fun _ => false)] at h0
      rw [h, heval_out w (fun _ => true)] at h1
      simp only [evalSym, Bool.false_eq_true, and_false, exists_false, decide_false] at h0
      obtain ⟨v, hv⟩ := hnonempty w
      have ht : decide (∃ v ∈ S w, (fun _ : Fin 6 => true) v = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨v, hv, by simp⟩
      rw [ht] at h1
      simp only [evalSym] at h1
      rw [h0] at h1
      simp at h1
  choose out' hout' using hout_inr
  apply hmono 6 m S hinter res.1 out' (fun g hg => ⟨(hinv.2.2.2.1 g hg).1, by have := (hinv.2.2.2.1 g hg).2; omega⟩)
  intro w x
  have h1 := hinv.2.2.2.2.2 x (out w) (hout_lt w)
  rw [hout' w] at h1
  exact h1.trans (heval_out w x)

private def eVec (v : Fin 6) : Fin 6 → Bool := fun i => decide (i = v)
private def z1Vec (v : Fin 6) : Fin 6 → Bool := fun i => decide (i ≠ v)
private def z2Vec (a b : Fin 6) : Fin 6 → Bool := fun i => decide (i ≠ a ∧ i ≠ b)

private def hasM1 (f : (Fin 6 → Bool) → Bool) : Prop := ∃ v : Fin 6, f (eVec v) = true
private def hasZ1 (f : (Fin 6 → Bool) → Bool) : Prop := ∃ v : Fin 6, f (z1Vec v) = false
private def hasZ2 (f : (Fin 6 → Bool) → Bool) : Prop := ∃ a b : Fin 6, f (z2Vec a b) = false

private lemma hasZ1_imp_hasZ2 {f : (Fin 6 → Bool) → Bool} (h : hasZ1 f) : hasZ2 f := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, v, ?_⟩
  have heq : z2Vec v v = z1Vec v := by funext i; simp [z2Vec, z1Vec]
  rw [heq]; exact hv

private lemma wireVal_input_hasM1 (gl : List Gate) (w : ℕ) (hw : w < 6) :
    hasM1 (fun x => wireVal gl x w) := by
  refine ⟨⟨w, hw⟩, ?_⟩
  dsimp only
  rw [wireVal_input gl (eVec ⟨w, hw⟩) ⟨w, hw⟩]
  simp [eVec]

private lemma wireVal_input_hasZ1 (gl : List Gate) (w : ℕ) (hw : w < 6) :
    hasZ1 (fun x => wireVal gl x w) := by
  refine ⟨⟨w, hw⟩, ?_⟩
  dsimp only
  rw [wireVal_input gl (z1Vec ⟨w, hw⟩) ⟨w, hw⟩]
  simp [z1Vec]

private lemma wireVal_mono_z1_to_z2 (gl : List Gate)
    (hmono : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (a b : Fin 6) (ha : wireVal gl (z1Vec a) w = false) :
    wireVal gl (z2Vec a b) w = false := by
  have hle : BoolLe (wireVal gl (z2Vec a b) w) (wireVal gl (z1Vec a) w) := by
    apply wireVal_mono gl hmono
    intro i hi
    simp only [z2Vec, decide_eq_true_eq] at hi
    simp [z1Vec, hi.1]
  cases h : wireVal gl (z2Vec a b) w with
  | false => rfl
  | true =>
    have := hle h
    rw [ha] at this
    simp at this

private lemma gate_or_hasZ2_of_hasZ1 (gl : List Gate)
    (hmono : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (hj : j < gl.length) (hop : (gl[j]).op = GateOp.or)
    (a b : ℕ) (hin : (gl[j]).inputs = [a, b])
    (ha : a < 6 + j → hasZ1 (fun x => wireVal gl x a))
    (hb : b < 6 + j → hasZ1 (fun x => wireVal gl x b)) :
    hasZ2 (fun x => wireVal gl x (6 + j)) := by
  have ha' : ∃ va : Fin 6, (if a < 6 + j then wireVal gl (z1Vec va) a else false) = false := by
    by_cases hlt : a < 6 + j
    · obtain ⟨va, hva⟩ := ha hlt
      exact ⟨va, by simp [hlt, hva]⟩
    · exact ⟨0, by simp [hlt]⟩
  have hb' : ∃ vb : Fin 6, (if b < 6 + j then wireVal gl (z1Vec vb) b else false) = false := by
    by_cases hlt : b < 6 + j
    · obtain ⟨vb, hvb⟩ := hb hlt
      exact ⟨vb, by simp [hlt, hvb]⟩
    · exact ⟨0, by simp [hlt]⟩
  obtain ⟨va, hva⟩ := ha'
  obtain ⟨vb, hvb⟩ := hb'
  refine ⟨va, vb, ?_⟩
  dsimp only
  rw [wireVal_gate_self gl j hj (z2Vec va vb)]
  simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    id_eq, Bool.or_false]
  have h1 : (if a < 6 + j then wireVal gl (z2Vec va vb) a else false) = false := by
    split_ifs with hlt
    · simp only [hlt, ↓reduceIte] at hva
      exact wireVal_mono_z1_to_z2 gl hmono a va vb hva
    · rfl
  have h2 : (if b < 6 + j then wireVal gl (z2Vec va vb) b else false) = false := by
    split_ifs with hlt
    · simp only [hlt, ↓reduceIte] at hvb
      have hcomm : z2Vec va vb = z2Vec vb va := by funext i; simp [z2Vec, and_comm]
      rw [hcomm]
      exact wireVal_mono_z1_to_z2 gl hmono b vb va hvb
    · rfl
  rw [h1, h2]
  rfl

private lemma gate_pair_inputs {g : Gate} (h : g.inputs.length = 2) :
    ∃ a b, g.inputs = [a, b] := by
  cases hin : g.inputs with
  | nil => simp [hin] at h
  | cons a r1 =>
    cases r1 with
    | nil => simp [hin] at h
    | cons b r2 =>
      cases r2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons c r3 => simp [hin] at h

private lemma gate_0_props (gl : List Gate)
    (hmono : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h0 : 0 < gl.length) :
    (hasM1 (fun x => wireVal gl x 6) ∨ hasZ1 (fun x => wireVal gl x 6)) ∧
    hasZ2 (fun x => wireVal gl x 6) := by
  have hm_op : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmono g hg).1
  obtain ⟨a, b, hin⟩ := gate_pair_inputs (hmono gl[0] (List.getElem_mem h0)).2
  rcases (hmono gl[0] (List.getElem_mem h0)).1 with hop | hop
  · have hz : hasZ1 (fun x => wireVal gl x 6) := by
      by_cases ha : a < 6
      · obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl a ha
        refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 0 h0]; simp [hop, hin, ha, hv, GateOp.eval]
      · refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 0 h0]; simp [hop, hin, ha, GateOp.eval]
    exact ⟨Or.inr hz, hasZ1_imp_hasZ2 hz⟩
  · have hz2 : hasZ2 (fun x => wireVal gl x 6) :=
      gate_or_hasZ2_of_hasZ1 gl hm_op 0 h0 hop a b hin
        (fun ha => wireVal_input_hasZ1 gl a ha) (fun hb => wireVal_input_hasZ1 gl b hb)
    by_cases ha : a < 6
    · refine ⟨Or.inl ?_, hz2⟩
      obtain ⟨v, hv⟩ := wireVal_input_hasM1 gl a ha
      refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 0 h0]; simp [hop, hin, ha, hv, GateOp.eval]
    · by_cases hb : b < 6
      · refine ⟨Or.inl ?_, hz2⟩
        obtain ⟨v, hv⟩ := wireVal_input_hasM1 gl b hb
        refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 0 h0]; simp [hop, hin, ha, hb, hv, GateOp.eval]
      · refine ⟨Or.inr ?_, hz2⟩
        refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 0 h0]; simp [hop, hin, ha, hb, GateOp.eval]

private lemma gate_1_hasM1_or_hasZ1 (gl : List Gate)
    (hmono : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h1 : 1 < gl.length) :
    hasM1 (fun x => wireVal gl x 7) ∨ hasZ1 (fun x => wireVal gl x 7) := by
  have h0_p := (gate_0_props gl hmono (by omega)).1
  obtain ⟨a, b, hin⟩ := gate_pair_inputs (hmono gl[1] (List.getElem_mem h1)).2
  by_contra hneither
  push_neg at hneither
  obtain ⟨hm, hz⟩ := hneither
  rcases (hmono gl[1] (List.getElem_mem h1)).1 with hop | hop
  · have ha_lt : a < 7 := by
      by_contra hge
      apply hz; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, hge, GateOp.eval]
    have hb_lt : b < 7 := by
      by_contra hge
      apply hz; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, hge, GateOp.eval]
    have ha6 : a = 6 := by
      by_contra hne
      obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl a (by omega)
      apply hz; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, ha_lt, hv, GateOp.eval]
    have hb6 : b = 6 := by
      by_contra hne
      obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl b (by omega)
      apply hz; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, hb_lt, hv, GateOp.eval]
    have heq : ∀ x, wireVal gl x 7 = wireVal gl x 6 := by
      intro x; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, ha6, hb6, GateOp.eval]
    rcases h0_p with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hm ⟨v, by dsimp only; rw [heq]; exact hv⟩
    · exact hz ⟨v, by dsimp only; rw [heq]; exact hv⟩
  · have ha_nm : a < 7 → ¬ hasM1 (fun x => wireVal gl x a) := by
      intro hlt ⟨v, hv⟩
      apply hm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, hlt, hv, GateOp.eval]
    have hb_nm : b < 7 → ¬ hasM1 (fun x => wireVal gl x b) := by
      intro hlt ⟨v, hv⟩
      apply hm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]; simp [hop, hin, hlt, hv, GateOp.eval]
    have ha6 : a < 7 → a = 6 := fun hlt => by
      by_contra hne; exact ha_nm hlt (wireVal_input_hasM1 gl a (by omega))
    have hb6 : b < 7 → b = 6 := fun hlt => by
      by_contra hne; exact hb_nm hlt (wireVal_input_hasM1 gl b (by omega))
    by_cases hlt_a : a < 7
    · have haeq := ha6 hlt_a
      have h0_nm : ¬ hasM1 (fun x => wireVal gl x 6) := fun ⟨v, hv⟩ => ha_nm hlt_a ⟨v, by dsimp only; rw [haeq]; exact hv⟩
      have h0_z : hasZ1 (fun x => wireVal gl x 6) := h0_p.resolve_left h0_nm
      obtain ⟨v, hv⟩ := h0_z
      apply hz; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]
      by_cases hlt_b : b < 7
      · have hbeq := hb6 hlt_b; simp [hop, hin, haeq, hbeq, hv, GateOp.eval]
      · simp [hop, hin, haeq, hlt_b, hv, GateOp.eval]
    · by_cases hlt_b : b < 7
      · have hbeq := hb6 hlt_b
        have h0_nm : ¬ hasM1 (fun x => wireVal gl x 6) := fun ⟨v, hv⟩ => hb_nm hlt_b ⟨v, by dsimp only; rw [hbeq]; exact hv⟩
        have h0_z : hasZ1 (fun x => wireVal gl x 6) := h0_p.resolve_left h0_nm
        obtain ⟨v, hv⟩ := h0_z
        apply hz; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]
        simp [hop, hin, hlt_a, hbeq, hv, GateOp.eval]
      · apply hz; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 h1]
        simp [hop, hin, hlt_a, hlt_b, GateOp.eval]

private lemma mono_bin_k_ge_five (gl : List Gate)
    (hmono : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (u : ℕ) (hu : u < 6 + gl.length)
    (hm : ¬ hasM1 (fun x => wireVal gl x u))
    (hz : ¬ hasZ2 (fun x => wireVal gl x u)) :
    5 ≤ gl.length := by
  have hm_op : ∀ g ∈ gl, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmono g hg).1
  by_contra hlt5
  have hle4 : gl.length ≤ 4 := by omega
  have hu6 : 6 ≤ u := by
    by_contra hlt6; exact hm (wireVal_input_hasM1 gl u (by omega))
  have hex : ∃ j, j < gl.length ∧ ¬ hasM1 (fun x => wireVal gl x (6 + j)) ∧ ¬ hasZ2 (fun x => wireVal gl x (6 + j)) :=
    ⟨u - 6, by omega, by simpa [show 6 + (u - 6) = u by omega] using hm,
      by simpa [show 6 + (u - 6) = u by omega] using hz⟩
  classical
  let j := Nat.find hex
  have hj_spec := Nat.find_spec hex
  have hj_lt : j < gl.length := hj_spec.1
  have hjm : ¬ hasM1 (fun x => wireVal gl x (6 + j)) := hj_spec.2.1
  have hjz : ¬ hasZ2 (fun x => wireVal gl x (6 + j)) := hj_spec.2.2
  have hmin : ∀ j' < j, hasM1 (fun x => wireVal gl x (6 + j')) ∨ hasZ2 (fun x => wireVal gl x (6 + j')) := by
    intro j' hj'
    have hnot := Nat.find_min hex hj'
    push_neg at hnot
    by_cases hm' : hasM1 (fun x => wireVal gl x (6 + j'))
    · exact Or.inl hm'
    · exact Or.inr (hnot (by omega) hm')
  have h0_p := gate_0_props gl hmono (by omega)
  obtain ⟨a, b, hin⟩ := gate_pair_inputs (hmono gl[j] (List.getElem_mem hj_lt)).2
  have hj_le3 : j ≤ 3 := by omega
  have h_and_noZ2 : (gl[j]).op = GateOp.and →
      a < 6 + j ∧ b < 6 + j ∧ ¬ hasZ2 (fun x => wireVal gl x a) ∧ ¬ hasZ2 (fun x => wireVal gl x b) := by
    intro hop
    have ha_lt : a < 6 + j := by
      by_contra hge; apply hjz; refine ⟨0, 0, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, hge, GateOp.eval]
    have hb_lt : b < 6 + j := by
      by_contra hge; apply hjz; refine ⟨0, 0, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, hge, GateOp.eval]
    refine ⟨ha_lt, hb_lt, ?_, ?_⟩
    · rintro ⟨va, vb, hval⟩; apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, ha_lt, hval, GateOp.eval]
    · rintro ⟨va, vb, hval⟩; apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, hb_lt, hval, GateOp.eval]
  have h_or_noM1 : (gl[j]).op = GateOp.or →
      (a < 6 + j → ¬ hasM1 (fun x => wireVal gl x a)) ∧
      (b < 6 + j → ¬ hasM1 (fun x => wireVal gl x b)) := by
    intro hop
    constructor
    · intro ha ⟨v, hv⟩; apply hjm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, ha, hv, GateOp.eval]
    · intro hb ⟨v, hv⟩; apply hjm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl j hj_lt]; simp [hop, hin, hb, hv, GateOp.eval]
  interval_cases j
  · exact hjz h0_p.2
  · rcases (hmono gl[1] (List.getElem_mem hj_lt)).1 with hop | hop
    · obtain ⟨ha_lt, _, ha_nz, _⟩ := h_and_noZ2 hop
      by_cases ha6 : a < 6
      · exact ha_nz (hasZ1_imp_hasZ2 (wireVal_input_hasZ1 gl a ha6))
      · have : a = 6 := by omega
        subst this; exact ha_nz h0_p.2
    · exact (gate_1_hasM1_or_hasZ1 gl hmono hj_lt).elim hjm (fun hz1 => hjz (hasZ1_imp_hasZ2 hz1))
  · rcases (hmono gl[2] (List.getElem_mem hj_lt)).1 with hop | hop
    · obtain ⟨ha_lt, hb_lt, ha_nz, hb_nz⟩ := h_and_noZ2 hop
      have ha7 : a = 7 := by
        by_contra hne
        by_cases ha6 : a < 6
        · exact ha_nz (hasZ1_imp_hasZ2 (wireVal_input_hasZ1 gl a ha6))
        · have : a = 6 := by omega
          subst this; exact ha_nz h0_p.2
      have hb7 : b = 7 := by
        by_contra hne
        by_cases hb6 : b < 6
        · exact hb_nz (hasZ1_imp_hasZ2 (wireVal_input_hasZ1 gl b hb6))
        · have : b = 6 := by omega
          subst this; exact hb_nz h0_p.2
      have h7_nz : ¬ hasZ2 (fun x => wireVal gl x 7) := by rw [← ha7]; exact ha_nz
      have h7_m : hasM1 (fun x => wireVal gl x 7) := (hmin 1 (by omega)).resolve_right h7_nz
      obtain ⟨v, hv⟩ := h7_m
      apply hjm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 hj_lt]
      simp [hop, hin, ha7, hb7, hv, GateOp.eval]
    · obtain ⟨ha_nm, hb_nm⟩ := h_or_noM1 hop
      have ha_z1 : a < 8 → hasZ1 (fun x => wireVal gl x a) := by
        intro ha
        by_cases ha6 : a < 6
        · exact wireVal_input_hasZ1 gl a ha6
        · by_cases ha6' : a = 6
          · subst ha6'; exact h0_p.1.resolve_left (ha_nm ha)
          · have ha7 : a = 7 := by omega
            subst ha7; exact (gate_1_hasM1_or_hasZ1 gl hmono (by omega)).resolve_left (ha_nm ha)
      have hb_z1 : b < 8 → hasZ1 (fun x => wireVal gl x b) := by
        intro hb
        by_cases hb6 : b < 6
        · exact wireVal_input_hasZ1 gl b hb6
        · by_cases hb6' : b = 6
          · subst hb6'; exact h0_p.1.resolve_left (hb_nm hb)
          · have hb7 : b = 7 := by omega
            subst hb7; exact (gate_1_hasM1_or_hasZ1 gl hmono (by omega)).resolve_left (hb_nm hb)
      exact hjz (gate_or_hasZ2_of_hasZ1 gl hm_op 2 hj_lt hop a b hin ha_z1 hb_z1)
  · rcases (hmono gl[3] (List.getElem_mem hj_lt)).1 with hop | hop
    · obtain ⟨ha_lt, hb_lt, ha_nz, hb_nz⟩ := h_and_noZ2 hop
      have hmem78 : ∀ w, w < 9 → ¬ hasZ2 (fun x => wireVal gl x w) → w = 7 ∨ w = 8 := by
        intro w hw hwnz
        by_cases hw6 : w < 6
        · exact absurd (hasZ1_imp_hasZ2 (wireVal_input_hasZ1 gl w hw6)) hwnz
        · by_cases hw6' : w = 6
          · subst hw6'; exact absurd h0_p.2 hwnz
          · omega
      have ha78 := hmem78 a ha_lt ha_nz
      have hb78 := hmem78 b hb_lt hb_nz
      have h7_nz : ¬ hasZ2 (fun x => wireVal gl x 7) := by
        rcases ha78 with rfl | rfl
        · exact ha_nz
        · rcases hb78 with rfl | rfl
          · exact hb_nz
          · exfalso
            have h8m : hasM1 (fun x => wireVal gl x 8) := (hmin 2 (by omega)).resolve_right ha_nz
            obtain ⟨v, hv⟩ := h8m
            apply hjm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, hv, GateOp.eval]
      have h8_nz : ¬ hasZ2 (fun x => wireVal gl x 8) := by
        rcases ha78 with rfl | rfl
        · rcases hb78 with rfl | rfl
          · exfalso
            have h7m : hasM1 (fun x => wireVal gl x 7) := (hmin 1 (by omega)).resolve_right ha_nz
            obtain ⟨v, hv⟩ := h7m
            apply hjm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, hv, GateOp.eval]
          · exact hb_nz
        · exact ha_nz
      have h6_nz1 : ¬ hasZ1 (fun x => wireVal gl x 6) := by
        intro h6z1
        obtain ⟨c1, d1, hin1⟩ := gate_pair_inputs (hmono gl[1] (List.getElem_mem (by omega))).2
        rcases (hmono gl[1] (List.getElem_mem (by omega))).1 with hop1 | hop1
        · apply h7_nz
          by_cases hc1 : c1 < 7
          · by_cases hc6 : c1 < 6
            · exact hasZ1_imp_hasZ2 (by obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl c1 hc6; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hc1, hv, GateOp.eval])
            · have : c1 = 6 := by omega
              subst this; exact hasZ1_imp_hasZ2 (by obtain ⟨v, hv⟩ := h6z1; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hv, GateOp.eval])
          · exact hasZ1_imp_hasZ2 ⟨0, by dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hc1, GateOp.eval]⟩
        · apply h7_nz
          apply gate_or_hasZ2_of_hasZ1 gl hm_op 1 (by omega) hop1 c1 d1 hin1
          · intro hc1
            by_cases hc6 : c1 < 6
            · exact wireVal_input_hasZ1 gl c1 hc6
            · have hc6' : c1 = 6 := by omega
              subst hc6'; exact h6z1
          · intro hd1
            by_cases hd6 : d1 < 6
            · exact wireVal_input_hasZ1 gl d1 hd6
            · have hd6' : d1 = 6 := by omega
              subst hd6'; exact h6z1
      have h6_m1 : hasM1 (fun x => wireVal gl x 6) := h0_p.1.resolve_right h6_nz1
      obtain ⟨p, hp6⟩ := h6_m1
      have hp7 : wireVal gl (eVec p) 7 = true := by
        obtain ⟨c1, d1, hin1⟩ := gate_pair_inputs (hmono gl[1] (List.getElem_mem (by omega))).2
        rcases (hmono gl[1] (List.getElem_mem (by omega))).1 with hop1 | hop1
        · exfalso; apply h7_nz
          by_cases hc1 : c1 < 7
          · by_cases hc6 : c1 < 6
            · obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl c1 hc6
              exact hasZ1_imp_hasZ2 ⟨v, by dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hc1, hv, GateOp.eval]⟩
            · have hc6' : c1 = 6 := by omega
              subst hc6'
              obtain ⟨va, vb, hv⟩ := h0_p.2
              exact ⟨va, vb, by dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hv, GateOp.eval]⟩
          · exact hasZ1_imp_hasZ2 ⟨0, by dsimp only; rw [wireVal_gate_self gl 1 (by omega)]; simp [hop1, hin1, hc1, GateOp.eval]⟩
        · have h6in : c1 = 6 ∨ d1 = 6 := by
            by_contra hne; push_neg at hne
            apply h7_nz
            apply gate_or_hasZ2_of_hasZ1 gl hm_op 1 (by omega) hop1 c1 d1 hin1
            · intro hc1; exact wireVal_input_hasZ1 gl c1 (by omega)
            · intro hd1; exact wireVal_input_hasZ1 gl d1 (by omega)
          rw [wireVal_gate_self gl 1 (by omega)]
          rcases h6in with rfl | rfl <;> simp [hop1, hin1, hp6, GateOp.eval]
      have hp8 : wireVal gl (eVec p) 8 = true := by
        obtain ⟨c2, d2, hin2⟩ := gate_pair_inputs (hmono gl[2] (List.getElem_mem (by omega))).2
        rcases (hmono gl[2] (List.getElem_mem (by omega))).1 with hop2 | hop2
        · have hc7 : c2 = 7 := by
            by_contra hne
            apply h8_nz
            by_cases hc : c2 < 8
            · by_cases hc6 : c2 < 6
              · obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl c2 hc6
                exact hasZ1_imp_hasZ2 ⟨v, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hc, hv, GateOp.eval]⟩
              · have hc6' : c2 = 6 := by omega
                subst hc6'
                obtain ⟨va, vb, hv⟩ := h0_p.2
                exact ⟨va, vb, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hv, GateOp.eval]⟩
            · exact hasZ1_imp_hasZ2 ⟨0, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hc, GateOp.eval]⟩
          have hd7 : d2 = 7 := by
            by_contra hne
            apply h8_nz
            by_cases hd : d2 < 8
            · by_cases hd6 : d2 < 6
              · obtain ⟨v, hv⟩ := wireVal_input_hasZ1 gl d2 hd6
                exact hasZ1_imp_hasZ2 ⟨v, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hd, hv, GateOp.eval]⟩
              · have hd6' : d2 = 6 := by omega
                subst hd6'
                obtain ⟨va, vb, hv⟩ := h0_p.2
                exact ⟨va, vb, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hv, GateOp.eval]⟩
            · exact hasZ1_imp_hasZ2 ⟨0, by dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hd, GateOp.eval]⟩
          rw [wireVal_gate_self gl 2 (by omega)]
          simp [hop2, hin2, hc7, hd7, hp7, GateOp.eval]
        · have h67 : c2 = 6 ∨ c2 = 7 ∨ d2 = 6 ∨ d2 = 7 := by
            by_contra hne; push_neg at hne
            apply h8_nz
            apply gate_or_hasZ2_of_hasZ1 gl hm_op 2 (by omega) hop2 c2 d2 hin2
            · intro hc; exact wireVal_input_hasZ1 gl c2 (by omega)
            · intro hd; exact wireVal_input_hasZ1 gl d2 (by omega)
          rw [wireVal_gate_self gl 2 (by omega)]
          rcases h67 with rfl | rfl | rfl | rfl <;> simp [hop2, hin2, hp6, hp7, GateOp.eval]
      apply hjm; refine ⟨p, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]
      rcases ha78 with rfl | rfl <;> rcases hb78 with rfl | rfl <;> simp [hop, hin, hp7, hp8, GateOp.eval]
    · obtain ⟨ha_nm, hb_nm⟩ := h_or_noM1 hop
      have h_lt8_z1 : ∀ w, w < 8 → (w < 9 → ¬ hasM1 (fun x => wireVal gl x w)) → hasZ1 (fun x => wireVal gl x w) := by
        intro w hw hnm
        by_cases hw6 : w < 6
        · exact wireVal_input_hasZ1 gl w hw6
        · by_cases hw6' : w = 6
          · subst hw6'; exact h0_p.1.resolve_left (hnm (by omega))
          · have hw7 : w = 7 := by omega
            subst hw7; exact (gate_1_hasM1_or_hasZ1 gl hmono (by omega)).resolve_left (hnm (by omega))
      have h8_used : a = 8 ∨ b = 8 := by
        by_contra hne; push_neg at hne
        apply hjz
        apply gate_or_hasZ2_of_hasZ1 gl hm_op 3 hj_lt hop a b hin
        · intro ha; exact h_lt8_z1 a (by omega) ha_nm
        · intro hb; exact h_lt8_z1 b (by omega) hb_nm
      have h8_nm : ¬ hasM1 (fun x => wireVal gl x 8) := by
        rcases h8_used with rfl | rfl
        · exact ha_nm (by omega)
        · exact hb_nm (by omega)
      have h8_z2 : hasZ2 (fun x => wireVal gl x 8) := (hmin 2 (by omega)).resolve_left h8_nm
      have h8_nz1 : ¬ hasZ1 (fun x => wireVal gl x 8) := by
        intro h8z1
        apply hjz
        apply gate_or_hasZ2_of_hasZ1 gl hm_op 3 hj_lt hop a b hin
        · intro ha
          by_cases h8 : a = 8
          · subst h8; exact h8z1
          · exact h_lt8_z1 a (by omega) ha_nm
        · intro hb
          by_cases h8 : b = 8
          · subst h8; exact h8z1
          · exact h_lt8_z1 b (by omega) hb_nm
      have hother : ∃ o, (a = 8 ∧ b = o ∨ b = 8 ∧ a = o) ∧ o < 8 ∧ ¬ hasM1 (fun x => wireVal gl x o) := by
        rcases h8_used with rfl | rfl
        · by_cases hb_lt : b < 9
          · by_cases hb8 : b = 8
            · subst hb8; exfalso
              obtain ⟨va, vb, hv⟩ := h8_z2
              apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, hv, GateOp.eval]
            · exact ⟨b, Or.inl ⟨rfl, rfl⟩, by omega, hb_nm hb_lt⟩
          · exfalso
            obtain ⟨va, vb, hv⟩ := h8_z2
            apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, hb_lt, hv, GateOp.eval]
        · by_cases ha_lt : a < 9
          · by_cases ha8 : a = 8
            · subst ha8; exfalso
              obtain ⟨va, vb, hv⟩ := h8_z2
              apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, hv, GateOp.eval]
            · exact ⟨a, Or.inr ⟨rfl, rfl⟩, by omega, ha_nm ha_lt⟩
          · exfalso
            obtain ⟨va, vb, hv⟩ := h8_z2
            apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]; simp [hop, hin, ha_lt, hv, GateOp.eval]
      obtain ⟨o, ho_eq, ho_lt8, ho_nm⟩ := hother
      have ho_67 : o = 6 ∨ o = 7 := by
        by_contra hne; exact ho_nm (wireVal_input_hasM1 gl o (by omega))
      have ho_z1 : hasZ1 (fun x => wireVal gl x o) := h_lt8_z1 o ho_lt8 (fun _ => ho_nm)
      obtain ⟨p2, q2, hin2⟩ := gate_pair_inputs (hmono gl[2] (List.getElem_mem (by omega))).2
      rcases (hmono gl[2] (List.getElem_mem (by omega))).1 with hop2 | hop2
      · have hp2_lt : p2 < 8 := by
          by_contra hge; apply h8_nz1; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hge, GateOp.eval]
        have hq2_lt : q2 < 8 := by
          by_contra hge; apply h8_nz1; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hge, GateOp.eval]
        have hp2_nz1 : ¬ hasZ1 (fun x => wireVal gl x p2) := by
          rintro ⟨v, hv⟩; apply h8_nz1; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hp2_lt, hv, GateOp.eval]
        have hq2_nz1 : ¬ hasZ1 (fun x => wireVal gl x q2) := by
          rintro ⟨v, hv⟩; apply h8_nz1; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hq2_lt, hv, GateOp.eval]
        have hp2_67 : p2 = 6 ∨ p2 = 7 := by
          by_contra hne; exact hp2_nz1 (wireVal_input_hasZ1 gl p2 (by omega))
        have hq2_67 : q2 = 6 ∨ q2 = 7 := by
          by_contra hne; exact hq2_nz1 (wireVal_input_hasZ1 gl q2 (by omega))
        have hp2_ne : p2 ≠ o := fun h => hp2_nz1 (h ▸ ho_z1)
        have hq2_ne : q2 ≠ o := fun h => hq2_nz1 (h ▸ ho_z1)
        have hpq_eq : p2 = q2 := by omega
        have hp2_m1 : hasM1 (fun x => wireVal gl x p2) := by
          rcases hp2_67 with rfl | rfl
          · exact h0_p.1.resolve_right hp2_nz1
          · exact (gate_1_hasM1_or_hasZ1 gl hmono (by omega)).resolve_right hp2_nz1
        obtain ⟨v, hv⟩ := hp2_m1
        apply h8_nm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]
        simp [hop2, hin2, hpq_eq.symm, hp2_lt, hv, GateOp.eval]
      · have hp2_nm : p2 < 8 → ¬ hasM1 (fun x => wireVal gl x p2) := by
          intro hp ⟨v, hv⟩; apply h8_nm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hp, hv, GateOp.eval]
        have hq2_nm : q2 < 8 → ¬ hasM1 (fun x => wireVal gl x q2) := by
          intro hq ⟨v, hv⟩; apply h8_nm; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]; simp [hop2, hin2, hq, hv, GateOp.eval]
        have habsorb : (p2 = o ∨ q2 = o) → False := by
          intro hor
          obtain ⟨va, vb, hv⟩ := h8_z2
          have hvo : wireVal gl (z2Vec va vb) o = false := by
            have h8f : wireVal gl (z2Vec va vb) 8 = false := hv
            rw [wireVal_gate_self gl 2 (by omega)] at h8f
            rcases hor with rfl | rfl
            · simp [hop2, hin2, ho_lt8, GateOp.eval] at h8f; exact h8f.1
            · simp [hop2, hin2, ho_lt8, GateOp.eval] at h8f; exact h8f.2
          apply hjz; refine ⟨va, vb, ?_⟩; dsimp only; rw [wireVal_gate_self gl 3 hj_lt]
          rcases ho_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hop, hin, ho_lt8, hv, hvo, GateOp.eval]
        have hp2_ne : p2 ≠ o := fun h => habsorb (Or.inl h)
        have hq2_ne : q2 ≠ o := fun h => habsorb (Or.inr h)
        have hp2_z1 : p2 < 8 → hasZ1 (fun x => wireVal gl x p2) := fun hp => h_lt8_z1 p2 hp (fun _ => hp2_nm hp)
        have hq2_z1 : q2 < 8 → hasZ1 (fun x => wireVal gl x q2) := fun hq => h_lt8_z1 q2 hq (fun _ => hq2_nm hq)
        have hp2_eq_or_ge : p2 < 8 → (p2 = 6 ∨ p2 = 7) := fun hp => by
          by_contra hne; exact hp2_nm hp (wireVal_input_hasM1 gl p2 (by omega))
        have hq2_eq_or_ge : q2 < 8 → (q2 = 6 ∨ q2 = 7) := fun hq => by
          by_contra hne; exact hq2_nm hq (wireVal_input_hasM1 gl q2 (by omega))
        by_cases hp : p2 < 8
        · have hp_z := hp2_z1 hp
          obtain ⟨v, hv⟩ := hp_z
          apply h8_nz1; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]
          by_cases hq : q2 < 8
          · have hpq : p2 = q2 := by
              have := hp2_eq_or_ge hp; have := hq2_eq_or_ge hq; omega
            simp [hop2, hin2, hp, hpq.symm, hv, GateOp.eval]
          · simp [hop2, hin2, hp, hq, hv, GateOp.eval]
        · by_cases hq : q2 < 8
          · obtain ⟨v, hv⟩ := hq2_z1 hq
            apply h8_nz1; refine ⟨v, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]
            simp [hop2, hin2, hp, hq, hv, GateOp.eval]
          · apply h8_nz1; refine ⟨0, ?_⟩; dsimp only; rw [wireVal_gate_self gl 2 (by omega)]
            simp [hop2, hin2, hp, hq, GateOp.eval]

private lemma mono_k_ge_five (gl : List Gate)
    (hmono : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (u : ℕ) (hu : u < 6 + gl.length)
    (hm : ¬ hasM1 (fun x => wireVal gl x u))
    (hz : ¬ hasZ2 (fun x => wireVal gl x u)) :
    5 ≤ gl.length := by
  have hvalid : ∀ j (hj : j < gl.length),
      (j ≠ gl.length → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2 :=
    fun j hj => ⟨fun _ => (hmono gl[j] (List.getElem_mem hj)).1, (hmono gl[j] (List.getElem_mem hj)).2⟩
  have hinv := simpStep_invariants gl gl.length false (fun _ => none) hvalid
    (fun _ hlt => absurd hlt (Nat.lt_irrefl _)) gl.length (le_refl _)
  set res := runSimpTake gl gl.length false (fun _ => none) gl.length
  have heval_u : ∀ x, evalSym res.1 x (res.2.1.getD u (Sum.inl false)) = wireVal gl x u := by
    intro x
    have h1 := hinv.2.2.2.2.2 x u hu
    have hrho : applyRho (fun _ => none) x = x := by funext i; rfl
    rw [hrho] at h1
    exact h1
  cases hru : res.2.1.getD u (Sum.inl false) with
  | inl b =>
    cases b
    · exfalso; apply hz; refine ⟨0, 0, ?_⟩; dsimp only; rw [← heval_u, hru]; rfl
    · exfalso; apply hm; refine ⟨0, ?_⟩; dsimp only; rw [← heval_u, hru]; rfl
  | inr u' =>
    have hu'_lt : u' < 6 + res.1.length := by
      have hlen_u : u < res.2.1.length := by rw [hinv.1]; exact hu
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen_u, Option.getD_some] at hru
      exact hinv.2.2.2.2.1 res.2.1[u] (List.getElem_mem hlen_u) u' hru
    have heq' : ∀ x, wireVal res.1 x u' = wireVal gl x u := by
      intro x; have := heval_u x; rw [hru] at this; exact this
    have h5 := mono_bin_k_ge_five res.1 hinv.2.2.2.1 u' hu'_lt
      (fun ⟨v, hv⟩ => hm ⟨v, by dsimp only; rw [← heq']; exact hv⟩)
      (fun ⟨va, vb, hv⟩ => hz ⟨va, vb, by dsimp only; rw [← heq']; exact hv⟩)
    have hle : res.1.length ≤ gl.length := by have := hinv.2.2.1; omega
    omega

private lemma main
    (hmono : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      ∀ (gates : List Gate) (out : Fin m → ℕ),
        (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ (w : Fin m) (x : Fin n → Bool),
          Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
        ∑ w, ((S w).card - 1) ≤ gates.length)
    (gl : List Gate) (ol : Fin 4 → ℕ)
    (hgl : ∀ gg ∈ gl, (gg.op = GateOp.and ∨ gg.op = GateOp.or ∨ gg.op = GateOp.not) ∧ gg.inputs.length ≤ 2)
    (hnot1 : ∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = GateOp.not → ∃ ka : Fin 1, ι ka = qa)
    (heval : ∀ (oa : Fin 4) (xa : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ pasch oa, xa va = true)) :
    8 ≤ gl.length := by
  have heval' : ∀ (oa : Fin 4) (xa : Fin 6 → Bool),
      wireVal gl xa (ol oa) = decide (∃ va ∈ pasch oa, xa va = true) := heval
  by_contra hlt8
  have h7 : gl.length ≤ 7 := by omega
  obtain ⟨ι, hι⟩ := hnot1
  have hno_not : (∀ g ∈ gl, g.op ≠ GateOp.not) → False := by
    intro hnn
    have hm : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      have := hgl g hg
      exact ⟨by rcases this.1 with h | h | h; exact Or.inl h; exact Or.inr h; exact absurd h (hnn g hg), this.2⟩
    have h8 := hmono 6 4 pasch pasch_inter gl ol hm heval
    rw [pasch_sum] at h8
    omega
  by_cases hk_not : (gl.get (ι 0)).op = GateOp.not
  · set k := (ι 0).val
    have hk : k < gl.length := (ι 0).isLt
    have hk_op : (gl[k]).op = GateOp.not := by simpa [k] using hk_not
    have hvalid : ∀ j (hj : j < gl.length),
        (j ≠ k → ((gl[j]).op = GateOp.and ∨ (gl[j]).op = GateOp.or)) ∧ (gl[j]).inputs.length ≤ 2 := by
      intro j hj
      have hgj := hgl gl[j] (List.getElem_mem hj)
      refine ⟨fun hne => ?_, hgj.2⟩
      rcases hgj.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨ka, hka⟩ := hι ⟨j, hj⟩ (by simpa using h)
        have : ka = 0 := Fin.eq_zero ka
        subst this
        exact absurd (congrArg Fin.val hka).symm hne
    have hmono_pre : ∀ g ∈ gl.take k, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
      rw [List.getElem_take]
      have hlt : idx < k := by rw [List.length_take] at hidx; omega
      exact ⟨(hvalid idx (by omega)).1 (by omega), (hvalid idx (by omega)).2⟩
    let fu : (Fin 6 → Bool) → Bool := fun x =>
      match (gl[k]).inputs with
      | [] => false
      | a :: _ => if a < 6 + k then wireVal gl x a else false
    have hnot_eval : ∀ x, wireVal gl x (6 + k) = !(fu x) := by
      intro x
      rw [wireVal_gate_self gl k hk x, hk_op]
      simp only [fu, GateOp.eval]
      cases (gl[k]).inputs <;> simp
    have hfu_mono : ∀ x y : Fin 6 → Bool, (∀ i, BoolLe (x i) (y i)) → BoolLe (fu x) (fu y) := by
      intro x y hxy
      simp only [fu]
      cases (gl[k]).inputs with
      | nil => simp [BoolLe]
      | cons a rest =>
        by_cases ha : a < 6 + k
        · simp only [ha, ↓reduceIte]
          rw [wireVal_take gl k x a (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; exact ha),
              wireVal_take gl k y a (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; exact ha)]
          exact wireVal_mono (gl.take k) (fun g hg => (hmono_pre g hg).1) hxy a
        · simp [ha, BoolLe]
    have hfu_nonconst : ∀ b : Bool, ¬ (∀ x, fu x = b) := by
      intro b hconst
      let g' : Gate := if b then ⟨GateOp.or, []⟩ else ⟨GateOp.and, []⟩
      have hrep : ∀ x w, wireVal (gl.set k g') x w = wireVal gl x w := by
        intro x
        apply eval_replace_gate gl k hk g' x
        rw [hnot_eval x, hconst x]
        cases b <;> rfl
      have hm' : ∀ g ∈ gl.set k g', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
        have hidx' : idx < gl.length := by simpa using hidx
        by_cases hjk : idx = k
        · subst hjk; rw [List.getElem_set_self hidx]; cases b <;> simp [g']
        · rw [List.getElem_set_ne (Ne.symm hjk) hidx]; exact ⟨(hvalid idx hidx').1 hjk, (hvalid idx hidx').2⟩
      have h8 := hmono 6 4 pasch pasch_inter (gl.set k g') ol hm' (fun w x => by
        change wireVal (gl.set k g') x (ol w) = _
        rw [hrep x (ol w)]; exact heval' w x)
      rw [pasch_sum, List.length_set] at h8
      omega
    have hfu_zero : fu (fun _ => false) = false := by
      cases h : fu (fun _ => false) with
      | false => rfl
      | true =>
        exfalso; apply hfu_nonconst true
        intro x; exact hfu_mono (fun _ => false) x (fun _ => by simp [BoolLe]) h
    have hol_ne_not : ∀ oa : Fin 4, ol oa ≠ 6 + k := by
      intro oa heq
      have h0 := heval' oa (fun _ => false)
      rw [heq, hnot_eval, hfu_zero] at h0
      simp at h0
    have hol_lt : ∀ oa : Fin 4, ol oa < 6 + gl.length := by
      intro oa
      by_contra hge
      have h1 := wireVal_ge_len gl (fun _ => true) (ol oa) (by omega)
      rw [heval' oa (fun _ => true)] at h1
      obtain ⟨v, hv⟩ := (pasch_erase1 0).2.1 oa
      have : decide (∃ va ∈ pasch oa, (fun _ : Fin 6 => true) va = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨v, Finset.mem_of_mem_erase hv, by simp⟩
      rw [this] at h1; simp at h1
    have hol_ge6 : ∀ oa : Fin 4, 6 ≤ ol oa := by
      intro oa
      by_contra hlt6
      obtain ⟨u, hu_mem, hu_ne⟩ := pasch_ne_single oa ⟨ol oa, by omega⟩
      have h1 := heval' oa (eVec u)
      have h2 := wireVal_input gl (eVec u) ⟨ol oa, by omega⟩
      dsimp only at h2
      rw [h2] at h1
      have hl : eVec u ⟨ol oa, by omega⟩ = false := by
        simp only [eVec, decide_eq_false_iff_not]
        intro h; exact hu_ne h.symm
      have hr : decide (∃ va ∈ pasch oa, eVec u va = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨u, hu_mem, by simp [eVec]⟩
      rw [hl, hr] at h1; simp at h1
    have hol_inj : Function.Injective ol := by
      intro w1 w2 heq
      by_contra hne
      obtain ⟨v, hv1, hv2⟩ := pasch_diff w1 w2 hne
      have h1 := heval' w1 (eVec v)
      have h2 := heval' w2 (eVec v)
      rw [heq] at h1
      rw [h1] at h2
      have ht1 : decide (∃ va ∈ pasch w1, eVec v va = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨v, hv1, by simp [eVec]⟩
      have ht2 : decide (∃ va ∈ pasch w2, eVec v va = true) = false := by
        simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro va hva hve; simp only [eVec, decide_eq_true_eq] at hve; subst hve; exact hv2 hva
      rw [ht1, ht2] at h2; simp at h2
    have hcontra_if_not_unused : ∀ (gl2 : List Gate),
        gl2.length = gl.length →
        (∀ j (hj : j < gl2.length), (j ≠ k → ((gl2[j]).op = GateOp.and ∨ (gl2[j]).op = GateOp.or)) ∧ (gl2[j]).inputs.length ≤ 2) →
        (∀ j (hj : j < gl2.length), k < j → 6 + k ∉ (gl2[j]).inputs) →
        (∀ oa x, wireVal gl2 x (ol oa) = decide (∃ va ∈ pasch oa, x va = true)) →
        False := by
      intro gl2 hlen2 hval2 hunused2 hev2
      have hk2 : k < gl2.length := by omega
      have hrep := eval_replace_unused_gate gl2 k hk2 ⟨GateOp.or, []⟩ hunused2
      have hm' : ∀ g ∈ gl2.set k ⟨GateOp.or, []⟩, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
        have hidx' : idx < gl2.length := by simpa using hidx
        by_cases hjk : idx = k
        · subst hjk; rw [List.getElem_set_self hidx]; simp
        · rw [List.getElem_set_ne (Ne.symm hjk) hidx]; exact ⟨(hval2 idx hidx').1 hjk, (hval2 idx hidx').2⟩
      have h8 := hmono 6 4 pasch pasch_inter (gl2.set k ⟨GateOp.or, []⟩) ol hm' (fun w x => by
        change wireVal (gl2.set k ⟨GateOp.or, []⟩) x (ol w) = _
        rw [hrep x (ol w) (hol_ne_not w)]; exact hev2 w x)
      rw [pasch_sum, List.length_set, hlen2] at h8
      omega
    have hjnot_ex : ∃ jnot, ∃ hjnot : jnot < gl.length, k < jnot ∧ 6 + k ∈ (gl[jnot]'hjnot).inputs := by
      by_contra hnone
      push_neg at hnone
      exact hcontra_if_not_unused gl rfl hvalid (fun j hj hkj => hnone j hj hkj) heval'
    obtain ⟨jnot, hjnot_lt, hk_lt_jnot, hjnot_mem⟩ := hjnot_ex
    by_cases hz1 : hasZ1 fu
    · obtain ⟨v, hv⟩ := hz1
      let ρ : Fin 6 → Option Bool := fun i => if i = v then some false else none
      have hbnot : ∀ x : Fin 6 → Bool, k < gl.length → wireVal gl (applyRho ρ x) (6 + k) = true := by
        intro x _
        rw [hnot_eval]
        have hle : BoolLe (fu (applyRho ρ x)) (fu (z1Vec v)) := by
          apply hfu_mono
          intro i hi
          by_cases hiv : i = v
          · subst hiv; simp [applyRho, ρ] at hi
          · simp [z1Vec, hiv]
        cases h : fu (applyRho ρ x) with
        | false => rfl
        | true => have := hle h; rw [hv] at this; simp at this
      have hinv := simpStep_invariants gl k true ρ hvalid hbnot gl.length (le_refl _)
      have h6 : 6 ≤ (runSimpTake gl k true ρ gl.length).1.length := by
        have hp := pasch_erase1 v
        rw [← hp.2.2]
        apply apply_hmono_simp hmono gl k true ρ hvalid hbnot 4 (fun w => (pasch w).erase v) ol hp.1 hp.2.1
        intro w x
        rw [heval' w (applyRho ρ x)]
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨u, hu, hxu⟩
          have huv : u ≠ v := by intro heq; subst heq; simp [applyRho, ρ] at hxu
          exact ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, by simpa [applyRho, ρ, huv] using hxu⟩
        · rintro ⟨u, hu, hxu⟩
          obtain ⟨huv, hu'⟩ := Finset.mem_erase.mp hu
          exact ⟨u, hu', by simpa [applyRho, ρ, huv] using hxu⟩
      have hk_in := (simp_mem_elim_k gl k hk true ρ).1
      have hk_env := (simp_mem_elim_k gl k hk true ρ).2
      have hjnot_in := simp_mem_elim_of_const_input gl k true ρ hvalid jnot hjnot_lt (6 + k) hjnot_mem (by omega) true hk_env
      have hcard2 : 2 ≤ (runSimpTake gl k true ρ gl.length).2.2.card := by
        have hsub : ({k, jnot} : Finset ℕ) ⊆ (runSimpTake gl k true ρ gl.length).2.2 := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl; exact hk_in; exact hjnot_in
        have hc : ({k, jnot} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
        exact hc ▸ Finset.card_le_card hsub
      have hsum := hinv.2.2.1
      omega
    · by_cases hm1 : hasM1 fu
      · obtain ⟨v, hv⟩ := hm1
        let ρ : Fin 6 → Option Bool := fun i => if i = v then some true else none
        have hbnot : ∀ x : Fin 6 → Bool, k < gl.length → wireVal gl (applyRho ρ x) (6 + k) = false := by
          intro x _
          rw [hnot_eval]
          have hle : BoolLe (fu (eVec v)) (fu (applyRho ρ x)) := by
            apply hfu_mono
            intro i hi
            simp only [eVec, decide_eq_true_eq] at hi
            subst hi; simp [applyRho, ρ]
          rw [hle hv]; rfl
        have hinv := simpStep_invariants gl k false ρ hvalid hbnot gl.length (le_refl _)
        obtain ⟨w1, w2, hw12, hv1, hv2⟩ := pasch_not_mem_two v
        have h4 : 4 ≤ (runSimpTake gl k false ρ gl.length).1.length := by
          let S2 : Fin 2 → Finset (Fin 6) := ![pasch w1, pasch w2]
          let out2 : Fin 2 → ℕ := ![ol w1, ol w2]
          have hsum2 : ∑ w : Fin 2, ((S2 w).card - 1) = 4 := by
            simp [Fin.sum_univ_two, S2, pasch_card]
          rw [← hsum2]
          apply apply_hmono_simp hmono gl k false ρ hvalid hbnot 2 S2 out2
          · intro i j hij
            fin_cases i <;> fin_cases j
            · exact absurd rfl hij
            · exact pasch_inter w1 w2 hw12
            · exact pasch_inter w2 w1 hw12.symm
            · exact absurd rfl hij
          · intro w; fin_cases w
            · exact (pasch_erase1 v).2.1 w1 |>.mono (Finset.erase_subset v _)
            · exact (pasch_erase1 v).2.1 w2 |>.mono (Finset.erase_subset v _)
          · intro w x
            have hnv : v ∉ S2 w := by
              fin_cases w
              · exact hv1
              · exact hv2
            have hev : wireVal gl (applyRho ρ x) (out2 w) = decide (∃ va ∈ S2 w, applyRho ρ x va = true) := by
              fin_cases w
              · exact heval' w1 (applyRho ρ x)
              · exact heval' w2 (applyRho ρ x)
            rw [hev]
            apply decide_eq_decide.mpr
            constructor
            · rintro ⟨u, hu, hxu⟩
              have huv : u ≠ v := fun heq => hnv (heq ▸ hu)
              exact ⟨u, hu, by simpa [applyRho, ρ, huv] using hxu⟩
            · rintro ⟨u, hu, hxu⟩
              have huv : u ≠ v := fun heq => hnv (heq ▸ hu)
              exact ⟨u, hu, by simpa [applyRho, ρ, huv] using hxu⟩
        have helim_le3 : (runSimpTake gl k false ρ gl.length).2.2.card ≤ 3 := by
          have hsum := hinv.2.2.1; omega
        have hkin_ne_v : ∀ a rest, (gl[k]).inputs = a :: rest → a ≠ v.val := by
          intro a rest hin heq
          apply hz1; refine ⟨v, ?_⟩
          simp only [fu, hin, heq]
          have hvlt : v.val < 6 + k := by have := v.isLt; omega
          simp only [hvlt, ↓reduceIte]
          rw [wireVal_input gl (z1Vec v) v]
          simp [z1Vec]
        have hg1_ex : ∃ g1, ∃ hg1 : g1 < k, v.val ∈ (gl[g1]'(by omega)).inputs := by
          by_contra hno
          push_neg at hno
          have hfeq : fu (eVec v) = fu (fun _ => false) := by
            simp only [fu]
            cases hin : (gl[k]).inputs with
            | nil => rfl
            | cons a rest =>
              by_cases ha : a < 6 + k
              · simp only [ha, ↓reduceIte]
                exact wireVal_indep_of_no_reader gl k (Nat.le_of_lt hk) v hno (eVec v) (fun _ => false)
                  (fun i hi => by simp [eVec, hi]) a ha (hkin_ne_v a rest hin)
              · simp [ha]
          rw [hv, hfu_zero] at hfeq; simp at hfeq
        obtain ⟨g1, hg1_lt, hg1_mem⟩ := hg1_ex
        have hv_env : (runSimpTake gl k false ρ gl.length).2.1.getD v.val (Sum.inl false) = Sum.inl true := by
          rw [simp_env_input]; simp [ρ]
        have hk_in := (simp_mem_elim_k gl k hk false ρ).1
        have hk_env := (simp_mem_elim_k gl k hk false ρ).2
        have hjnot_in := simp_mem_elim_of_const_input gl k false ρ hvalid jnot hjnot_lt (6 + k) hjnot_mem (by omega) false hk_env
        have hg1_in := simp_mem_elim_of_const_input gl k false ρ hvalid g1 (by omega) v.val hg1_mem (by have := v.isLt; omega) true hv_env
        have helim_eq : (runSimpTake gl k false ρ gl.length).2.2 = {g1, k, jnot} := by
          have hsub : ({g1, k, jnot} : Finset ℕ) ⊆ (runSimpTake gl k false ρ gl.length).2.2 := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl; exact hg1_in; exact hk_in; exact hjnot_in
          have hcard3 : ({g1, k, jnot} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
          exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
        have hno_other_v_pre : ∀ j (hj : j < k), j ≠ g1 → v.val ∉ (gl[j]'(by omega)).inputs := by
          intro j hj hne hmem
          have jin := simp_mem_elim_of_const_input gl k false ρ hvalid j (by omega) v.val hmem (by omega) true hv_env
          rw [helim_eq] at jin
          simp only [Finset.mem_insert, Finset.mem_singleton] at jin
          omega
        have hg1_const : ∃ b, (runSimpTake gl k false ρ gl.length).2.1.getD (6 + g1) (Sum.inl false) = Sum.inl b := by
          rcases (hvalid g1 (by omega)).1 (by omega) with hop | hop
          · by_cases hall : ∀ a ∈ (gl[g1]'(by omega)).inputs, a < 6 + g1 →
                ∃ b, (runSimpTake gl k false ρ gl.length).2.1.getD a (Sum.inl false) = Sum.inl b
            · exact simp_env_const_of_all_const gl k false ρ hvalid g1 (by omega) (by omega) hall
            · exfalso
              have hg1_0 : wireVal gl (eVec v) (6 + g1) = false := by
                push_neg at hall
                obtain ⟨a, ha_mem, ha_lt, ha_nc⟩ := hall
                have hav : a ≠ v.val := fun h => ha_nc true (h ▸ hv_env)
                have ha_eq : wireVal gl (eVec v) a = wireVal gl (fun _ => false) a :=
                  wireVal_indep_of_no_reader gl g1 (by omega) v (fun j hj => hno_other_v_pre j (by omega) (by omega))
                    (eVec v) (fun _ => false) (fun i hi => by simp [eVec, hi]) a ha_lt hav
                cases ha0 : wireVal gl (fun _ => false) a with
                | false =>
                  rw [wireVal_gate_self gl g1 (by omega) (eVec v), hop]
                  simp only [GateOp.eval, List.all_eq_false]
                  exact ⟨false, List.mem_map.mpr ⟨a, ha_mem, by simp [ha_lt, ha_eq, ha0]⟩, by simp⟩
                | true =>
                  exact absurd (simp_env_true_of_zero_true gl k hk false ρ hvalid a (by omega) ha0) (ha_nc true)
              have hfu_eq : fu (eVec v) = fu (fun _ => false) := by
                have hg1_both : wireVal gl (eVec v) (6 + g1) = wireVal gl (fun _ => false) (6 + g1) := by
                  rw [hg1_0]
                  cases h0 : wireVal gl (fun _ => false) (6 + g1) with
                  | false => rfl
                  | true =>
                    have h1 := wireVal_take gl k (fun _ => false) (6 + g1) (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; omega)
                    have h2 := wireVal_take gl k (eVec v) (6 + g1) (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; omega)
                    have hm := wireVal_mono (gl.take k) (fun g hg => (hmono_pre g hg).1)
                      (x := fun _ => false) (y := eVec v) (fun _ => by simp [BoolLe]) (6 + g1)
                    rw [← h1, ← h2] at hm
                    have := hm h0; rw [hg1_0] at this; simp at this
                have hall_eq : ∀ w < 6 + k, w ≠ v.val → wireVal gl (eVec v) w = wireVal gl (fun _ => false) w := by
                  intro w hw hnev
                  induction w using Nat.strong_induction_on with
                  | ind w ih =>
                    by_cases hw6 : w < 6
                    · rw [wireVal_input gl _ ⟨w, hw6⟩, wireVal_input gl _ ⟨w, hw6⟩]
                      have : (⟨w, hw6⟩ : Fin 6) ≠ v := fun h => hnev (by simpa using congrArg Fin.val h)
                      simp [eVec, this]
                    · by_cases hwg1 : w = 6 + g1
                      · rw [hwg1]; exact hg1_both
                      · set j := w - 6
                        have hj : j < k := by omega
                        rw [show w = 6 + j by omega, wireVal_gate_self gl j (by omega), wireVal_gate_self gl j (by omega)]
                        congr 1
                        apply List.map_congr_left
                        intro i hi_mem
                        by_cases hi : i < 6 + j
                        · simp only [hi, ite_true]
                          have hiv : i ≠ v.val := fun h => hno_other_v_pre j hj (by omega) (h ▸ hi_mem)
                          exact ih i (by omega) (by omega) hiv
                        · simp [hi]
                simp only [fu]
                cases hin : (gl[k]).inputs with
                | nil => rfl
                | cons a rest =>
                  by_cases ha : a < 6 + k
                  · simp only [ha, ↓reduceIte]
                    exact hall_eq a ha (hkin_ne_v a rest hin)
                  · simp [ha]
              rw [hv, hfu_zero] at hfu_eq; simp at hfu_eq
          · exact ⟨true, simp_env_const_of_or_true gl k false ρ hvalid g1 (by omega) (by omega) hop v.val hg1_mem (by omega) hv_env⟩
        obtain ⟨bg1, hbg1⟩ := hg1_const
        have hno_g1_other : ∀ j (hj : j < gl.length), g1 < j → j ≠ k → j ≠ jnot → 6 + g1 ∉ (gl[j]).inputs := by
          intro j hj hgj hjk hjj hmem
          have jin := simp_mem_elim_of_const_input gl k false ρ hvalid j hj (6 + g1) hmem (by omega) bg1 hbg1
          rw [helim_eq] at jin
          simp only [Finset.mem_insert, Finset.mem_singleton] at jin
          omega
        have hno_k_other : ∀ j (hj : j < gl.length), k < j → j ≠ jnot → 6 + k ∉ (gl[j]).inputs := by
          intro j hj hkj hjj hmem
          have jin := simp_mem_elim_of_const_input gl k false ρ hvalid j hj (6 + k) hmem (by omega) false hk_env
          rw [helim_eq] at jin
          simp only [Finset.mem_insert, Finset.mem_singleton] at jin
          omega
        have hkin_eq_g1 : ∀ x, fu x = wireVal gl x (6 + g1) := by
          have hhead : ∃ rest, (gl[k]).inputs = (6 + g1) :: rest := by
            cases hin : (gl[k]).inputs with
            | nil => exfalso; simp [fu, hin] at hv
            | cons a rest =>
              by_cases ha : a = 6 + g1
              · exact ⟨rest, by rw [ha]⟩
              · exfalso
                have hfeq : fu (eVec v) = fu (fun _ => false) := by
                  simp only [fu, hin]
                  by_cases halt : a < 6 + k
                  · simp only [halt, ↓reduceIte]
                    exact wireVal_indep_of_no_reader_gate gl k (Nat.le_of_lt hk) v g1 hg1_lt
                      hno_other_v_pre (fun j hj hgj => hno_g1_other j (by omega) hgj (by omega) (by omega))
                      (eVec v) (fun _ => false) (fun i hi => by simp [eVec, hi]) a halt
                      (hkin_ne_v a rest hin) ha
                  · simp [halt]
                rw [hv, hfu_zero] at hfeq; simp at hfeq
          obtain ⟨rest, hrest⟩ := hhead
          intro x
          simp only [fu, hrest, show 6 + g1 < 6 + k by omega, ↓reduceIte]
        have hkill_jnot : ∀ g' : Gate,
            (g'.op = GateOp.and ∨ g'.op = GateOp.or) → g'.inputs = [] →
            (∀ oa x, wireVal (gl.set jnot g') x (ol oa) = decide (∃ va ∈ pasch oa, x va = true)) →
            False := by
          intro g' hop' hin' hev'
          apply hcontra_if_not_unused (gl.set jnot g') (List.length_set)
          · intro j hj
            have hj' : j < gl.length := by simpa using hj
            by_cases hjj : j = jnot
            · subst hjj; rw [List.getElem_set_self hj]; exact ⟨fun _ => hop', by simp [hin']⟩
            · rw [List.getElem_set_ne (Ne.symm hjj) hj]; exact hvalid j hj'
          · intro j hj hkj
            have hj' : j < gl.length := by simpa using hj
            by_cases hjj : j = jnot
            · subst hjj; rw [List.getElem_set_self hj]; simp [hin']
            · rw [List.getElem_set_ne (Ne.symm hjj) hj]; exact hno_k_other j hj' hkj hjj
          · exact hev'
        by_cases hjnot_g1 : 6 + g1 ∈ (gl[jnot]).inputs
        · have hjnot_len := (hvalid jnot hjnot_lt).2
          have hjnot_op := (hvalid jnot hjnot_lt).1 (by omega)
          have hjnot_const : ∃ bc : Bool, ∀ x, wireVal gl x (6 + jnot) = bc := by
            cases hinj : (gl[jnot]).inputs with
            | nil => simp [hinj] at hjnot_mem
            | cons u1 r1 =>
              cases r1 with
              | nil =>
                rw [hinj] at hjnot_mem hjnot_g1; simp at hjnot_mem hjnot_g1; omega
              | cons u2 r2 =>
                cases r2 with
                | nil =>
                  rw [hinj] at hjnot_mem hjnot_g1
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjnot_mem hjnot_g1
                  rcases hjnot_op with hop | hop
                  · refine ⟨false, fun x => ?_⟩
                    rw [wireVal_gate_self gl jnot hjnot_lt x, hop, hinj]
                    rcases hjnot_mem with rfl | rfl <;> rcases hjnot_g1 with h1 | h1
                    · omega
                    · subst h1; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, show 6 + g1 < 6 + jnot by omega, hnot_eval, hkin_eq_g1]
                    · subst h1; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, show 6 + g1 < 6 + jnot by omega, hnot_eval, hkin_eq_g1]
                    · omega
                  · refine ⟨true, fun x => ?_⟩
                    rw [wireVal_gate_self gl jnot hjnot_lt x, hop, hinj]
                    rcases hjnot_mem with rfl | rfl <;> rcases hjnot_g1 with h1 | h1
                    · omega
                    · subst h1; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, show 6 + g1 < 6 + jnot by omega, hnot_eval, hkin_eq_g1]
                    · subst h1; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, show 6 + g1 < 6 + jnot by omega, hnot_eval, hkin_eq_g1]
                    · omega
                | cons u3 r3 => simp [hinj] at hjnot_len
          obtain ⟨bc, hbc⟩ := hjnot_const
          let g' : Gate := if bc then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩
          apply hkill_jnot g' (by cases bc <;> simp [g']) (by cases bc <;> rfl)
          intro oa x
          rw [eval_replace_gate gl jnot hjnot_lt g' x (by rw [hbc x]; cases bc <;> rfl) (ol oa)]
          exact heval' oa x
        · by_cases hjnot_v : v.val ∈ (gl[jnot]).inputs
          · have hjnot_len := (hvalid jnot hjnot_lt).2
            have hjnot_op := (hvalid jnot hjnot_lt).1 (by omega)
            have hjnot_pair : (gl[jnot]).inputs = [6 + k, v.val] ∨ (gl[jnot]).inputs = [v.val, 6 + k] := by
              cases hinj : (gl[jnot]).inputs with
              | nil => simp [hinj] at hjnot_mem
              | cons u1 r1 =>
                cases r1 with
                | nil => rw [hinj] at hjnot_mem hjnot_v; simp at hjnot_mem hjnot_v; omega
                | cons u2 r2 =>
                  cases r2 with
                  | nil =>
                    rw [hinj] at hjnot_mem hjnot_v
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hjnot_mem hjnot_v
                    rcases hjnot_mem with rfl | rfl <;> rcases hjnot_v with h1 | h1
                    · omega
                    · subst h1; exact Or.inl rfl
                    · subst h1; exact Or.inr rfl
                    · omega
                  | cons u3 r3 => simp [hinj] at hjnot_len
            rcases hjnot_op with hop | hop
            · have hjnot_false : ∀ x, wireVal gl x (6 + jnot) = false := by
                intro x
                rw [wireVal_gate_self gl jnot hjnot_lt x, hop]
                have hpair : (!fu x && x v) = false := by
                  cases hxv : x v with
                  | false => simp
                  | true =>
                    have hle : BoolLe (fu (eVec v)) (fu x) := by
                      apply hfu_mono; intro i hi; simp only [eVec, decide_eq_true_eq] at hi; subst hi; exact hxv
                    rw [hle hv]; rfl
                rcases hjnot_pair with hinj | hinj
                · rw [hinj]; simp only [List.map_cons, List.map_nil, show 6 + k < 6 + jnot by omega, show v.val < 6 + jnot by have := v.isLt; omega, ↓reduceIte, hnot_eval, wireVal_input, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]; exact hpair
                · rw [hinj]; simp only [List.map_cons, List.map_nil, show 6 + k < 6 + jnot by omega, show v.val < 6 + jnot by have := v.isLt; omega, ↓reduceIte, hnot_eval, wireVal_input, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]; rw [Bool.and_comm]; exact hpair
              apply hkill_jnot ⟨GateOp.or, []⟩ (Or.inr rfl) rfl
              intro oa x
              rw [eval_replace_gate gl jnot hjnot_lt ⟨GateOp.or, []⟩ x (by rw [hjnot_false x]; rfl) (ol oa)]
              exact heval' oa x
            · have hjnot_env : (runSimpTake gl k false ρ gl.length).2.1.getD (6 + jnot) (Sum.inl false) = Sum.inl true :=
                simp_env_const_of_or_true gl k false ρ hvalid jnot hjnot_lt (by omega) hop v.val hjnot_v (by omega) hv_env
              have hjnot_unused : ∀ j (hj : j < gl.length), jnot < j → 6 + jnot ∉ (gl[j]).inputs := by
                intro j hj hlt hmem
                have jin := simp_mem_elim_of_const_input gl k false ρ hvalid j hj (6 + jnot) hmem (by omega) true hjnot_env
                rw [helim_eq] at jin; simp only [Finset.mem_insert, Finset.mem_singleton] at jin; omega
              have hol_ne_jnot : ∀ oa : Fin 4, ol oa ≠ 6 + jnot := by
                intro oa heq
                have h0 := heval' oa (fun _ => false)
                rw [heq, wireVal_gate_self gl jnot hjnot_lt (fun _ => false), hop] at h0
                rcases hjnot_pair with hinj | hinj
                · rw [hinj] at h0; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, hnot_eval, hfu_zero] at h0
                · rw [hinj] at h0; simp [GateOp.eval, show 6 + k < 6 + jnot by omega, hnot_eval, hfu_zero] at h0
              apply hkill_jnot ⟨GateOp.or, []⟩ (Or.inr rfl) rfl
              intro oa x
              rw [eval_replace_unused_gate gl jnot hjnot_lt ⟨GateOp.or, []⟩ hjnot_unused x (ol oa) (hol_ne_jnot oa)]
              exact heval' oa x
          · have hno_v_all : ∀ j (hj : j < gl.length), j ≠ g1 → j ≠ k → v.val ∉ (gl[j]).inputs := by
              intro j hj hjg1 hjk hmem
              by_cases hjj : j = jnot
              · subst hjj; exact hjnot_v hmem
              · have jin := simp_mem_elim_of_const_input gl k false ρ hvalid j hj v.val hmem (by omega) true hv_env
                rw [helim_eq] at jin; simp only [Finset.mem_insert, Finset.mem_singleton] at jin; omega
            have hno_g1_all : ∀ j (hj : j < gl.length), g1 < j → j ≠ k → 6 + g1 ∉ (gl[j]).inputs := by
              intro j hj hgj hjk
              by_cases hjj : j = jnot
              · subst hjj; exact hjnot_g1
              · exact hno_g1_other j hj hgj hjk hjj
            obtain ⟨m1, m2, hm12, hvm1, hvm2⟩ := pasch_mem_two v
            have hex_ne : ∃ w : Fin 4, v ∈ pasch w ∧ ol w ≠ 6 + g1 := by
              by_cases h1 : ol m1 = 6 + g1
              · exact ⟨m2, hvm2, fun h2 => hm12 (hol_inj (h1.trans h2.symm))⟩
              · exact ⟨m1, hvm1, h1⟩
            obtain ⟨wm, hvwm, hol_ne_g1⟩ := hex_ne
            have hanti := wireVal_antimono_of_only_via_not gl k hk (fun j hj => (hvalid j hj).1) hk_op
              v g1 hg1_lt hno_v_all hno_g1_all (fun _ => false) (ol wm) (by have := hol_ge6 wm; omega) hol_ne_g1
            have hupd1 : Function.update (fun _ : Fin 6 => false) v true = eVec v := by
              funext i; by_cases hi : i = v <;> simp [hi, eVec]
            have hupd0 : Function.update (fun _ : Fin 6 => false) v false = (fun _ => false) := by
              funext i; by_cases hi : i = v <;> simp [hi]
            rw [hupd1, hupd0, heval' wm (eVec v), heval' wm (fun _ => false)] at hanti
            have ht : decide (∃ va ∈ pasch wm, eVec v va = true) = true := by
              simp only [decide_eq_true_eq]; exact ⟨v, hvwm, by simp [eVec]⟩
            have hf : decide (∃ va ∈ pasch wm, (fun _ : Fin 6 => false) va = true) = false := by simp
            rw [ht, hf] at hanti
            have := hanti rfl
            simp at this
      · by_cases hz2 : hasZ2 fu
        · obtain ⟨a, b, hab_val⟩ := hz2
          have hab : a ≠ b := by
            intro heq; subst heq
            apply hz1; refine ⟨a, ?_⟩
            have : z2Vec a a = z1Vec a := by funext i; simp [z2Vec, z1Vec]
            rw [← this]; exact hab_val
          let ρ : Fin 6 → Option Bool := fun i => if i = a ∨ i = b then some false else none
          have hbnot : ∀ x : Fin 6 → Bool, k < gl.length → wireVal gl (applyRho ρ x) (6 + k) = true := by
            intro x _
            rw [hnot_eval]
            have hle : BoolLe (fu (applyRho ρ x)) (fu (z2Vec a b)) := by
              apply hfu_mono
              intro i hi
              by_cases hiab : i = a ∨ i = b
              · simp [applyRho, ρ, hiab] at hi
              · push_neg at hiab; simp [z2Vec, hiab.1, hiab.2]
            cases h : fu (applyRho ρ x) with
            | false => rfl
            | true => have := hle h; rw [hab_val] at this; simp at this
          have hinv := simpStep_invariants gl k true ρ hvalid hbnot gl.length (le_refl _)
          have h4 : 4 ≤ (runSimpTake gl k true ρ gl.length).1.length := by
            have hp := pasch_erase2 a b hab
            rw [← hp.2.2]
            apply apply_hmono_simp hmono gl k true ρ hvalid hbnot 4 (fun w => ((pasch w).erase a).erase b) ol hp.1 hp.2.1
            intro w x
            rw [heval' w (applyRho ρ x)]
            apply decide_eq_decide.mpr
            constructor
            · rintro ⟨u, hu, hxu⟩
              have huab : u ≠ a ∧ u ≠ b := by
                constructor <;> (intro heq; subst heq; simp [applyRho, ρ] at hxu)
              exact ⟨u, Finset.mem_erase.mpr ⟨huab.2, Finset.mem_erase.mpr ⟨huab.1, hu⟩⟩,
                by simpa [applyRho, ρ, huab.1, huab.2] using hxu⟩
            · rintro ⟨u, hu, hxu⟩
              obtain ⟨hub, hu'⟩ := Finset.mem_erase.mp hu
              obtain ⟨hua, hu''⟩ := Finset.mem_erase.mp hu'
              exact ⟨u, hu'', by simpa [applyRho, ρ, hua, hub] using hxu⟩
          have helim_le3 : (runSimpTake gl k true ρ gl.length).2.2.card ≤ 3 := by
            have hsum := hinv.2.2.1; omega
          have hkin_ne_ab : ∀ u rest, (gl[k]).inputs = u :: rest → u ≠ a.val ∧ u ≠ b.val := by
            intro u rest hin
            constructor
            · intro heq; apply hz1; refine ⟨a, ?_⟩
              simp only [fu, hin, heq, show a.val < 6 + k by have := a.isLt; omega, ↓reduceIte]
              rw [wireVal_input gl (z1Vec a) a]; simp [z1Vec]
            · intro heq; apply hz1; refine ⟨b, ?_⟩
              simp only [fu, hin, heq, show b.val < 6 + k by have := b.isLt; omega, ↓reduceIte]
              rw [wireVal_input gl (z1Vec b) b]; simp [z1Vec]
          have hga_ex : ∃ ga, ∃ hga : ga < k, a.val ∈ (gl[ga]'(by omega)).inputs := by
            by_contra hno; push_neg at hno
            have hfeq : fu (z2Vec a b) = fu (z1Vec b) := by
              simp only [fu]
              cases hin : (gl[k]).inputs with
              | nil => rfl
              | cons u rest =>
                by_cases hu : u < 6 + k
                · simp only [hu, ↓reduceIte]
                  exact wireVal_indep_of_no_reader gl k (Nat.le_of_lt hk) a hno (z2Vec a b) (z1Vec b)
                    (fun i hi => by simp [z2Vec, z1Vec, hi]) u hu (hkin_ne_ab u rest hin).1
                · simp [hu]
            rw [hab_val] at hfeq
            exact hz1 ⟨b, hfeq.symm⟩
          have hgb_ex : ∃ gb, ∃ hgb : gb < k, b.val ∈ (gl[gb]'(by omega)).inputs := by
            by_contra hno; push_neg at hno
            have hfeq : fu (z2Vec a b) = fu (z1Vec a) := by
              simp only [fu]
              cases hin : (gl[k]).inputs with
              | nil => rfl
              | cons u rest =>
                by_cases hu : u < 6 + k
                · simp only [hu, ↓reduceIte]
                  exact wireVal_indep_of_no_reader gl k (Nat.le_of_lt hk) b hno (z2Vec a b) (z1Vec a)
                    (fun i hi => by simp [z2Vec, z1Vec, hi]) u hu (hkin_ne_ab u rest hin).2
                · simp [hu]
            rw [hab_val] at hfeq
            exact hz1 ⟨a, hfeq.symm⟩
          obtain ⟨ga, hga_lt, hga_mem⟩ := hga_ex
          obtain ⟨gb, hgb_lt, hgb_mem⟩ := hgb_ex
          have ha_env : (runSimpTake gl k true ρ gl.length).2.1.getD a.val (Sum.inl false) = Sum.inl false := by
            rw [simp_env_input]; simp [ρ]
          have hb_env : (runSimpTake gl k true ρ gl.length).2.1.getD b.val (Sum.inl false) = Sum.inl false := by
            rw [simp_env_input]; simp [ρ]
          have hk_in := (simp_mem_elim_k gl k hk true ρ).1
          have hk_env := (simp_mem_elim_k gl k hk true ρ).2
          have hjnot_in := simp_mem_elim_of_const_input gl k true ρ hvalid jnot hjnot_lt (6 + k) hjnot_mem (by omega) true hk_env
          have hga_in := simp_mem_elim_of_const_input gl k true ρ hvalid ga (by omega) a.val hga_mem (by omega) false ha_env
          have hgb_in := simp_mem_elim_of_const_input gl k true ρ hvalid gb (by omega) b.val hgb_mem (by omega) false hb_env
          by_cases hgab : ga = gb
          · subst hgab
            have hall_ga : ∀ w ∈ (gl[ga]'(by omega)).inputs, w < 6 + ga →
                ∃ c, (runSimpTake gl k true ρ gl.length).2.1.getD w (Sum.inl false) = Sum.inl c := by
              have hlen_ga := (hvalid ga (by omega)).2
              cases hin : (gl[ga]'(by omega)).inputs with
              | nil => intro w hw; simp at hw
              | cons u1 r1 =>
                cases r1 with
                | nil =>
                  rw [hin] at hga_mem hgb_mem; simp at hga_mem hgb_mem
                  exact absurd (Fin.ext (hga_mem.trans hgb_mem.symm)) hab
                | cons u2 r2 =>
                  cases r2 with
                  | nil =>
                    rw [hin] at hga_mem hgb_mem
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hga_mem hgb_mem
                    have hne_val : a.val ≠ b.val := fun h => hab (Fin.ext h)
                    intro w hw _
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
                    rcases hga_mem with rfl | rfl <;> rcases hgb_mem with h1 | h1
                    · exact absurd h1.symm hne_val
                    · subst h1; rcases hw with rfl | rfl; exact ⟨false, ha_env⟩; exact ⟨false, hb_env⟩
                    · subst h1; rcases hw with rfl | rfl; exact ⟨false, hb_env⟩; exact ⟨false, ha_env⟩
                    · exact absurd h1.symm hne_val
                  | cons u3 r3 => simp [hin] at hlen_ga
            obtain ⟨bga, hbga⟩ := simp_env_const_of_all_const gl k true ρ hvalid ga (by omega) (by omega) hall_ga
            have hkin_ne_ga : ∀ u rest, (gl[k]).inputs = u :: rest → u ≠ 6 + ga := by
              intro u rest hin heq
              have hlen_ga := (hvalid ga (by omega)).2
              cases hinga : (gl[ga]'(by omega)).inputs with
              | nil => simp [hinga] at hga_mem
              | cons u1 r1 =>
                cases r1 with
                | nil =>
                  rw [hinga] at hga_mem hgb_mem; simp at hga_mem hgb_mem
                  exact absurd (Fin.ext (hga_mem.trans hgb_mem.symm)) hab
                | cons u2 r2 =>
                  cases r2 with
                  | nil =>
                    rw [hinga] at hga_mem hgb_mem
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hga_mem hgb_mem
                    rcases (hvalid ga (by omega)).1 (by omega) with hop | hop
                    · apply hz1; refine ⟨a, ?_⟩
                      simp only [fu, hin, heq, show 6 + ga < 6 + k by omega, ↓reduceIte]
                      rw [wireVal_gate_self gl ga (by omega) (z1Vec a), hop, hinga]
                      rcases hga_mem with rfl | rfl <;> simp [GateOp.eval, show a.val < 6 + ga by omega, wireVal_input, z1Vec]
                    · apply hm1; refine ⟨a, ?_⟩
                      simp only [fu, hin, heq, show 6 + ga < 6 + k by omega, ↓reduceIte]
                      rw [wireVal_gate_self gl ga (by omega) (eVec a), hop, hinga]
                      rcases hga_mem with rfl | rfl <;> simp [GateOp.eval, show a.val < 6 + ga by omega, wireVal_input, eVec]
                  | cons u3 r3 => simp [hinga] at hlen_ga
            have helim_eq : (runSimpTake gl k true ρ gl.length).2.2 = {ga, k, jnot} := by
              have hsub : ({ga, k, jnot} : Finset ℕ) ⊆ (runSimpTake gl k true ρ gl.length).2.2 := by
                intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl | rfl; exact hga_in; exact hk_in; exact hjnot_in
              have hcard3 : ({ga, k, jnot} : Finset ℕ).card = 3 := by
                rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
              exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
            have hno_a_pre : ∀ j (hj : j < k), j ≠ ga → a.val ∉ (gl[j]'(by omega)).inputs := by
              intro j hj hne hmem
              have jin := simp_mem_elim_of_const_input gl k true ρ hvalid j (by omega) a.val hmem (by omega) false ha_env
              rw [helim_eq] at jin; simp only [Finset.mem_insert, Finset.mem_singleton] at jin; omega
            have hno_ga_pre : ∀ j (hj : j < k), ga < j → 6 + ga ∉ (gl[j]'(by omega)).inputs := by
              intro j hj hlt hmem
              have jin := simp_mem_elim_of_const_input gl k true ρ hvalid j (by omega) (6 + ga) hmem (by omega) bga hbga
              rw [helim_eq] at jin; simp only [Finset.mem_insert, Finset.mem_singleton] at jin; omega
            have hfeq : fu (z2Vec a b) = fu (z1Vec b) := by
              simp only [fu]
              cases hin : (gl[k]).inputs with
              | nil => rfl
              | cons u rest =>
                by_cases hu : u < 6 + k
                · simp only [hu, ↓reduceIte]
                  exact wireVal_indep_of_no_reader_gate gl k (Nat.le_of_lt hk) a ga hga_lt hno_a_pre hno_ga_pre
                    (z2Vec a b) (z1Vec b) (fun i hi => by simp [z2Vec, z1Vec, hi]) u hu
                    (hkin_ne_ab u rest hin).1 (hkin_ne_ga u rest hin)
                · simp [hu]
            rw [hab_val] at hfeq
            exact hz1 ⟨b, hfeq.symm⟩
          · have hsub : ({ga, gb, k, jnot} : Finset ℕ) ⊆ (runSimpTake gl k true ρ gl.length).2.2 := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl | rfl; exact hga_in; exact hgb_in; exact hk_in; exact hjnot_in
            have hcard4 : ({ga, gb, k, jnot} : Finset ℕ).card = 4 := by
              rw [Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_insert_of_notMem (by simp; omega),
                  Finset.card_pair (by omega)]
            have := Finset.card_le_card hsub
            omega
        · have hk5 : 5 ≤ k := by
            cases hin : (gl[k]).inputs with
            | nil =>
              exfalso; apply hz2; refine ⟨0, 0, ?_⟩; simp [fu, hin]
            | cons a rest =>
              by_cases ha : a < 6 + k
              · have ha_len : a < 6 + (gl.take k).length := by
                  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]; exact ha
                have hfeq : ∀ x, wireVal (gl.take k) x a = fu x := by
                  intro x; simp only [fu, hin, ha, ↓reduceIte]
                  exact (wireVal_take gl k x a (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; exact ha)).symm
                have h5 := mono_k_ge_five (gl.take k) hmono_pre a ha_len
                  (fun ⟨v, hv⟩ => hm1 ⟨v, by rw [← hfeq]; exact hv⟩)
                  (fun ⟨va, vb, hv⟩ => hz2 ⟨va, vb, by rw [← hfeq]; exact hv⟩)
                rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at h5
                exact h5
              · exfalso; apply hz2; refine ⟨0, 0, ?_⟩; simp [fu, hin, ha]
          have hpre_outputs : 3 ≤ (Finset.univ.filter fun w : Fin 4 => ol w < 6 + k).card := by
            have hgt : (Finset.univ.filter fun w : Fin 4 => ¬ (ol w < 6 + k)).card ≤ 1 := by
              by_contra hge2
              have h2 : 1 < (Finset.univ.filter fun w : Fin 4 => ¬ (ol w < 6 + k)).card := by omega
              obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp h2
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hw1 hw2
              have h1 := hol_lt w1
              have h2' := hol_lt w2
              have hne1 := hol_ne_not w1
              have hne2 := hol_ne_not w2
              have : ol w1 = ol w2 := by omega
              exact hne (hol_inj this)
            have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
              (p := fun w => ol w < 6 + k)
            simp only [Finset.card_univ, Fintype.card_fin] at htot
            omega
          obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hpre_outputs
          let e := T.equivFinOfCardEq hT_card
          let S3 : Fin 3 → Finset (Fin 6) := fun i => pasch (e.symm i).val
          let out3 : Fin 3 → ℕ := fun i => ol (e.symm i).val
          have h6 : 6 ≤ (gl.take k).length := by
            have hsum3 : ∑ i : Fin 3, ((S3 i).card - 1) = 6 := by
              simp [S3, pasch_card]
            rw [← hsum3]
            apply hmono 6 3 S3 ?_ (gl.take k) out3 hmono_pre ?_
            · intro i j hij
              apply pasch_inter
              intro heq
              exact hij (e.symm.injective (Subtype.ext heq))
            · intro i x
              have hmem : (e.symm i).val ∈ Finset.univ.filter fun w : Fin 4 => ol w < 6 + k :=
                hT_sub (e.symm i).property
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
              change wireVal (gl.take k) x (ol (e.symm i).val) = _
              rw [← wireVal_take gl k x (ol (e.symm i).val) (by rw [Nat.min_eq_left (Nat.le_of_lt hk)]; exact hmem)]
              exact heval' (e.symm i).val x
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at h6
          omega
  · apply hno_not
    intro g hg hop
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨ka, hka⟩ := hι ⟨idx, hidx⟩ (by simpa using hop)
    have : ka = 0 := Fin.eq_zero ka
    subst this
    rw [hka] at hk_not
    exact hk_not (by simpa using hop)

end PEqualNP.Outside.L_meta_1042_aux

theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  exact PEqualNP.Outside.L_meta_1042_aux.main
