import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (x : List Bool) :
    (gs.foldl gateStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, gateStep, List.length_append,
      List.length_nil]
    omega

lemma foldl_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (gs.foldl gateStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlen : i < (gateStep x g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (gateStep x g) hlen]
    simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_length C.gates x

lemma wires_getD_input (C : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_getD_lt C.gates x hi

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) {j : ℕ} (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have h1 := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgate]
  set w0 := (C.gates.take j).foldl gateStep x
  have hw0_len : w0.length = n + j := by
    rw [foldl_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hW_eq : C.wires x = (C.gates.drop (j + 1)).foldl gateStep (gateStep w0 C.gates[j]) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW_prefix : ∀ i < n + j, (C.wires x).getD i false = w0.getD i false := by
    intro i hi
    have hi0 : i < w0.length := by omega
    have hi1 : i < (gateStep w0 C.gates[j]).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [hW_eq, foldl_getD_lt _ _ hi1]
    simp only [gateStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
  have hnj_lt : n + j < (gateStep w0 C.gates[j]).length := by
    simp only [gateStep, List.length_append, List.length_singleton]
    omega
  conv_lhs => rw [hW_eq]
  rw [foldl_getD_lt _ _ hnj_lt]
  have hget : (gateStep w0 C.gates[j]).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) := by
    simp only [gateStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hw0_len]
    simp
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := by
    have := hrb j hj i
    rw [hgate] at this
    exact this hi
  rw [hW_prefix i hilt]

def activeStep (n : ℕ) (C : Circuit) (j : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if n + j ∈ S then S.erase (n + j) ∪ (gateAt C j).inputs.toFinset else S

def activeSet (n : ℕ) (C : Circuit) : ℕ → Finset ℕ
  | 0 => {C.output}
  | t + 1 => activeStep n C (C.gates.length - 1 - t) (activeSet n C t)

lemma activeSet_card_le (n : ℕ) (C : Circuit) (hmono : Monotone2 C) :
    ∀ t ≤ C.gates.length, (activeSet n C t).card ≤ t + 1 := by
  intro t ht
  induction t with
  | zero => simp [activeSet]
  | succ t ih =>
    have ht' : t ≤ C.gates.length := by omega
    have hj : C.gates.length - 1 - t < C.gates.length := by omega
    have hih := ih ht'
    simp only [activeSet, activeStep]
    split_ifs with hmem
    · have hcard_in : (gateAt C (C.gates.length - 1 - t)).inputs.toFinset.card ≤ 2 := by
        have h1 : (gateAt C (C.gates.length - 1 - t)).inputs.toFinset.card ≤
            (gateAt C (C.gates.length - 1 - t)).inputs.length := List.toFinset_card_le _
        have hmem_g : gateAt C (C.gates.length - 1 - t) ∈ C.gates := by
          have : gateAt C (C.gates.length - 1 - t) = C.gates[C.gates.length - 1 - t] := by
            simp [gateAt, List.getD_eq_getElem?_getD, hj]
          rw [this]
          exact List.getElem_mem hj
        have h2 := (hmono _ hmem_g).2
        omega
      have herase : ((activeSet n C t).erase (n + (C.gates.length - 1 - t))).card =
          (activeSet n C t).card - 1 := Finset.card_erase_of_mem hmem
      have hpos : 1 ≤ (activeSet n C t).card := Finset.one_le_card.mpr ⟨_, hmem⟩
      have hunion := Finset.card_union_le
        ((activeSet n C t).erase (n + (C.gates.length - 1 - t)))
        (gateAt C (C.gates.length - 1 - t)).inputs.toFinset
      omega
    · omega

lemma activeSet_lt (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hout : C.output < n + C.gates.length) :
    ∀ t ≤ C.gates.length, ∀ u ∈ activeSet n C t, u < n + (C.gates.length - t) := by
  intro t ht
  induction t with
  | zero =>
    intro u hu
    simp only [activeSet, Finset.mem_singleton] at hu
    subst hu
    simpa using hout
  | succ t ih =>
    intro u hu
    have ht' : t ≤ C.gates.length := by omega
    have hj : C.gates.length - 1 - t < C.gates.length := by omega
    have hih := ih ht'
    simp only [activeSet, activeStep] at hu
    split_ifs at hu with hmem
    · rcases Finset.mem_union.mp hu with hu1 | hu2
      · have hne : u ≠ n + (C.gates.length - 1 - t) := (Finset.mem_erase.mp hu1).1
        have hlt := hih u (Finset.mem_erase.mp hu1).2
        omega
      · have hmem_in : u ∈ (gateAt C (C.gates.length - 1 - t)).inputs :=
          List.mem_toFinset.mp hu2
        have hlt := hrb (C.gates.length - 1 - t) hj u hmem_in
        omega
    · have hne : u ≠ n + (C.gates.length - 1 - t) := fun heq => hmem (heq ▸ hu)
      have hlt := hih u hu
      omega

lemma activeSet_agree (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    ∀ t ≤ C.gates.length,
      (∀ u ∈ activeSet n C t, (C.wires x).getD u false = (C.wires y).getD u false) →
      C.eval x = C.eval y := by
  intro t ht
  induction t with
  | zero =>
    intro h
    exact h C.output (by simp [activeSet])
  | succ t ih =>
    intro h
    have ht' : t ≤ C.gates.length := by omega
    have hj : C.gates.length - 1 - t < C.gates.length := by omega
    apply ih ht'
    intro u hu
    by_cases heq : u = n + (C.gates.length - 1 - t)
    · subst heq
      rw [wires_getD_gate n C hrb x hx hj, wires_getD_gate n C hrb y hy hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply h i
      simp only [activeSet, activeStep, hu, ↓reduceIte, Finset.mem_union, List.mem_toFinset]
      exact Or.inr hi
    · apply h u
      simp only [activeSet, activeStep]
      split_ifs with hmem
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨heq, hu⟩))
      · exact hu

lemma output_lt_of_eval_true (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n)
    (htrue : C.eval x = true) : C.output < n + C.gates.length := by
  by_contra hge
  have hge' : (C.wires x).length ≤ C.output := by
    rw [wires_length, hx]
    omega
  have hfalse : C.eval x = false := by
    simp only [Circuit.eval, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hge']
    rfl
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

lemma mem_activeSet_of_sens (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hout : C.output < n + C.gates.length) (k : Fin n)
    (z0 z1 : Fin n → Bool) (hdiff : ∀ j : Fin n, j ≠ k → z0 j = z1 j)
    (h0 : circuitFun n C z0 = false) (h1 : circuitFun n C z1 = true) :
    k.val ∈ activeSet n C C.gates.length := by
  by_contra hnot
  have hagree : ∀ u ∈ activeSet n C C.gates.length,
      (C.wires (List.ofFn z0)).getD u false = (C.wires (List.ofFn z1)).getD u false := by
    intro u hu
    have hult : u < n := by
      have := activeSet_lt n C hrb hout C.gates.length le_rfl u hu
      omega
    rw [wires_getD_input C (List.ofFn z0) (by simpa using hult),
        wires_getD_input C (List.ofFn z1) (by simpa using hult)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hult, ↓reduceDIte, Option.getD_some]
    apply hdiff ⟨u, hult⟩
    intro heq
    apply hnot
    have : k.val = u := by simpa using congrArg Fin.val heq.symm
    exact this ▸ hu
  have heq := activeSet_agree n C hrb (List.ofFn z0) (List.ofFn z1)
    (by simp) (by simp) C.gates.length le_rfl hagree
  change circuitFun n C z0 = circuitFun n C z1 at heq
  rw [h0, h1] at heq
  exact Bool.false_ne_true heq

lemma exists_line_of_point (q N : ℕ) (I : Fin N → Fin N → Prop)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0)
    (p : Fin N) : ∃ l : Fin N, I p l := by
  have hN2 : 2 ≤ N := by omega
  by_cases hp0 : p.val = 0
  · let p' : Fin N := ⟨1, by omega⟩
    have hne : p ≠ p' := fun h => by
      have := congrArg Fin.val h
      dsimp [p'] at this
      omega
    obtain ⟨l, ⟨hlp, _⟩, _⟩ := huniq p p' hne
    exact ⟨l, hlp⟩
  · let p' : Fin N := ⟨0, by omega⟩
    have hne : p ≠ p' := fun h => by
      have := congrArg Fin.val h
      dsimp [p'] at this
      omega
    obtain ⟨l, ⟨hlp, _⟩, _⟩ := huniq p p' hne
    exact ⟨l, hlp⟩

lemma exists_point_of_line (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1)
    (l : Fin N) : ∃ p : Fin N, I p l := by
  have hpos : 0 < (Finset.univ.filter (fun p0 => I p0 l)).card := by
    rw [hcard l]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (Finset.mem_filter.mp hp).2⟩

lemma main_proof (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1)
    (huniq : ∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0)
    (hmono : Monotone2 C) (hrb : ReadsBack (N + N) C)
    (hacc : ∀ p1 l1 : Fin N, I p1 l1 →
      circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true)
    (hsound : ∀ z1 : Fin (N + N) → Bool,
      (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q →
      (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧
        z1 (Fin.natAdd N l1c) = true) →
      circuitFun (N + N) C z1 = false) :
    2 * N ≤ C.size + 1 := by
  have hNpos : 0 < N := by omega
  obtain ⟨p0, hp0⟩ := exists_point_of_line q N I hcard ⟨0, hNpos⟩
  have hout : C.output < (N + N) + C.gates.length :=
    output_lt_of_eval_true (N + N) C
      (List.ofFn (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p0 ∨ k1 = Fin.natAdd N ⟨0, hNpos⟩)))
      (by simp) (hacc p0 ⟨0, hNpos⟩ hp0)
  have hsub : Finset.range (N + N) ⊆ activeSet (N + N) C C.gates.length := by
    intro i hi
    have hilt : i < N + N := Finset.mem_range.mp hi
    by_cases hiN : i < N
    · let p : Fin N := ⟨i, hiN⟩
      obtain ⟨l, hpl⟩ := exists_line_of_point q N I hq hN huniq p
      let z1 : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      let z0 : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
      have hz1 : circuitFun (N + N) C z1 = true := hacc p l hpl
      have hz0 : circuitFun (N + N) C z0 = false := by
        apply hsound z0
        · have hf : Finset.univ.filter (fun l1b : Fin N => z0 (Fin.natAdd N l1b) = true) = {l} := by
            ext l1b
            simp [z0]
          rw [hf, Finset.card_singleton]
          omega
        · rintro ⟨p1c, l1c, _, hp1c, _⟩
          simp only [z0, decide_eq_true_eq] at hp1c
          have hval := congrArg Fin.val hp1c
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
          omega
      have hdiff : ∀ j : Fin (N + N), j ≠ Fin.castAdd N p → z0 j = z1 j := by
        intro j hj
        simp only [z0, z1, hj, false_or]
      have hmem := mem_activeSet_of_sens (N + N) C hrb hout (Fin.castAdd N p) z0 z1 hdiff hz0 hz1
      simpa [p] using hmem
    · let l : Fin N := ⟨i - N, by omega⟩
      obtain ⟨p, hpl⟩ := exists_point_of_line q N I hcard l
      let z1 : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      let z0 : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
      have hz1 : circuitFun (N + N) C z1 = true := hacc p l hpl
      have hz0 : circuitFun (N + N) C z0 = false := by
        apply hsound z0
        · have hf : Finset.univ.filter (fun l1b : Fin N => z0 (Fin.natAdd N l1b) = true) = ∅ := by
            ext l1b
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
              iff_false, z0, decide_eq_true_eq]
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
            omega
          rw [hf, Finset.card_empty]
          omega
        · rintro ⟨p1c, l1c, _, _, hl1c⟩
          simp only [z0, decide_eq_true_eq] at hl1c
          have hval := congrArg Fin.val hl1c
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
          omega
      have hdiff : ∀ j : Fin (N + N), j ≠ Fin.natAdd N l → z0 j = z1 j := by
        intro j hj
        simp only [z0, z1, hj, or_false]
      have hmem := mem_activeSet_of_sens (N + N) C hrb hout (Fin.natAdd N l) z0 z1 hdiff hz0 hz1
      have hval : (Fin.natAdd N l).val = i := by
        simp only [Fin.val_natAdd, l]
        omega
      rw [hval] at hmem
      exact hmem
  have hcard_le := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard_le
  have hact := activeSet_card_le (N + N) C hmono C.gates.length le_rfl
  change C.gates.length + 1 ≥ 2 * N
  omega

end PEqualNP.Outside.L_meta_1660_aux

theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 :=
  PEqualNP.Outside.L_meta_1660_aux.main_proof
