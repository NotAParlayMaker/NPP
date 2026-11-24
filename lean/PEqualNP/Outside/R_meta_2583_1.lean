import Mathlib.Tactic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs

-- Take a least circuit for incidence and, among those, one with as few gates as possible that are not
-- OR gates below the function. A gate reading a wire below the function is then itself an OR gate
-- below the function: otherwise drop the gate and OR the wire to the output. So the circuit is an OR
-- of blocks (the AND gates below the function), k blocks using at least k - 1 OR gates at the top.
-- If the other gates pay for a star cover of the edges of every block (first hypothesis), there
-- are at least N * (q + 2) - 1 gates, which is what the read-1 star circuit has (second hypothesis).
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2583_1
    (blockCost : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (B top : ℕ → Prop),
      2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, ∃ s : Finset (Fin N), s.card = q + 1 ∧ ∀ p, p ∈ s ↔ I p l) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C' → PEqualNP.MetaComplexity.circuitFun (N + N) C' = PEqualNP.MetaComplexity.circuitFun (N + N) C → C.size ≤ C'.size) →
      (∀ w, B w ↔ ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD w false = true → PEqualNP.MetaComplexity.circuitFun (N + N) C z = true) →
      (∀ j, top j ↔ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = .or ∧ B (N + N + j)) →
      (∀ j < C.size, (∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, B w) → top j) →
      ∃ (O : ℕ → Finset ℕ) (S T : ℕ → Finset (Fin N)) (E : ℕ → Finset (Fin N × Fin N)),
        (∀ b g, g ∈ O b → g < C.size ∧ ¬ top g) ∧ (∀ b b', b ≠ b' → Disjoint (O b) (O b')) ∧
        (∀ p l, I p l → ∃ b < C.size, ¬ top b ∧ B (N + N + b) ∧
          (C.wires (List.ofFn (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)))).getD (N + N + b) false = true ∧
          (p ∈ S b ∨ l ∈ T b) ∧ (p, l) ∈ E b) ∧
        ∀ b, (S b).card + (T b).card + (E b).card ≤ (O b).card + 1)
    (starCircuit : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, ∃ s : Finset (Fin N), s.card = q + 1 ∧ ∀ p, p ∈ s ↔ I p l) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ D.size + 1 ≤ N * (q + 2) ∧
        PEqualNP.ReadK.IsReadK (N + N) D 1) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  have wnil : ∀ (o : ℕ) (x : List Bool), PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[], o⟩ x = x := fun _ _ => rfl
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
  have run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length ∧
      (∀ i < x.length, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false) ∧
      ∀ (j : ℕ) (h : j < gs.length), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false else false) := by
    intro gs o x
    induction gs using List.reverseRecOn with
    | nil => refine ⟨by rw [wnil]; simp, fun i _ => by rw [wnil], fun j h => absurd h (Nat.not_lt_zero _)⟩
    | append_singleton gs g ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x =
          PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
            [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
        wsnoc gs g o x
      rw [e]
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x = W at h1 h2 h3 ⊢
      generalize hval : g.op.eval (g.inputs.map fun i => W.getD i false) = val
      have old : ∀ i < W.length, (W ++ [val]).getD i false = W.getD i false := fun i hi =>
        List.getD_append _ _ _ _ hi
      refine ⟨by simp [h1]; omega, fun i hi => by rw [old i (by omega)]; exact h2 i hi, ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · rw [old _ (by omega), h3 j hlt, List.getElem_append_left hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · rfl
      · have hj' : j = gs.length := by simp at hj; omega
        subst hj'
        rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_concat_length]
        refine hval.symm.trans ?_
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · exact List.getD_eq_default _ _ (by omega)
  intro q N I inst C0 hq hN hline hpt hC0 hcomp0
  have hline' : ∀ l : Fin N, ∃ s : Finset (Fin N), s.card = q + 1 ∧ ∀ p, p ∈ s ↔ I p l :=
    fun l => ⟨_, hline l, fun p => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  obtain ⟨D, hD, hDc, hDs, hDr⟩ := starCircuit q N I hq hN hline' hpt
  refine ⟨D, hD, hDc, ?_, hDr⟩
  -- abbreviations
  obtain ⟨n, hn⟩ : ∃ n, n = N + N := ⟨_, rfl⟩
  let V : PEqualNP.CircuitLowerBounds.Circuit → (Fin (N + N) → Bool) → ℕ → Bool := fun C x i => (C.wires (List.ofFn x)).getD i false
  let G : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := fun C j => PEqualNP.MetaComplexity.NestedCover.gateAt C j
  let P : (Fin (N + N) → Bool) → Prop := fun z => (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
  have hNpos : 0 < N := by rw [hN]; positivity
  have GD : ∀ C j, G C j = C.gates.getD j ⟨.or, []⟩ := fun _ _ => rfl
  have gmem : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), j < C.size → G C j ∈ C.gates := by
    intro C j hj
    have hj' : j < C.gates.length := hj
    rw [GD, List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have aop : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → ∀ j < C.size, (G C j).op = .and ∨ (G C j).op = .or :=
    fun C h j hj => h.1 _ (gmem C j hj)
  have alen : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → ∀ j < C.size, (G C j).inputs.length = 2 :=
    fun C h j hj => h.2.2 _ (gmem C j hj)
  have ardr : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → ∀ j < C.size, ∀ i ∈ (G C j).inputs, i < N + N + j :=
    fun C h j hj i hi => h.2.1 j hj i hi
  have vin : ∀ C x i, i < N + N → V C x i = (List.ofFn x).getD i false := by
    intro C x i hi
    exact (run C.gates C.output (List.ofFn x)).2.1 i (by rw [List.length_ofFn]; exact hi)
  have vout : ∀ C x i, N + N + C.size ≤ i → V C x i = false := by
    intro C x i hi
    have h := (run C.gates C.output (List.ofFn x)).1
    rw [List.length_ofFn] at h
    have hs : C.gates.length = C.size := rfl
    show List.getD _ _ _ = false
    exact List.getD_eq_default _ _ (by rw [show C.wires (List.ofFn x) =
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates, C.output⟩ (List.ofFn x) from rfl, h, hs]; exact hi)
  have vgate : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → ∀ x j, j < C.size →
      V C x (N + N + j) = (G C j).op.eval ((G C j).inputs.map (V C x)) := by
    intro C hC x j hj
    have hj' : j < C.gates.length := hj
    have h := (run C.gates C.output (List.ofFn x)).2.2 j hj'
    rw [List.length_ofFn] at h
    refine h.trans ?_
    have hg : C.gates[j] = G C j := by rw [GD, List.getD_eq_getElem _ _ hj']
    rw [hg]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [if_pos (ardr C hC j hj i hi)]
  -- dropping gate j, with wire r in its place
  let ρ : ℕ → ℕ → ℕ → ℕ := fun j r k => if k < N + N + j then k else if k = N + N + j then r else k - 1
  let σ : ℕ → ℕ → ℕ := fun j i => if i < j then i else i + 1
  let M : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Gate := fun C j r i => ⟨(G C (σ j i)).op, (G C (σ j i)).inputs.map (ρ j r)⟩
  have ρlt : ∀ j r k, k < N + N + j → ρ j r k = k := fun j r k h => if_pos h
  have ρeq : ∀ j r, ρ j r (N + N + j) = r := fun j r => by simp [ρ]
  have ρgt : ∀ j r k, N + N + j < k → ρ j r k = k - 1 := fun j r k h => by
    simp only [ρ]; rw [if_neg (by omega), if_neg (by omega)]
  have agree : ∀ C C', PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.TopForm.IsAO2 (N + N) C' → ∀ j r, j < C.size →
      r < N + N + j → C.size ≤ C'.size + 1 → (∀ i, i + 1 < C.size → G C' i = M C j r i) →
      ∀ x k, k < N + N + C.size → k ≠ N + N + j →
      (k < N + N + j ∨ V C x r = V C x (N + N + j) ∨ ∀ i < C.size, ∀ w ∈ (G C i).inputs, w ≠ N + N + j) →
      V C' x (ρ j r k) = V C x k := by
    intro C C' hC hC' j r hj hr hsz hg x k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hkj hh
      rcases Nat.lt_or_ge k (N + N) with h | h
      · rw [ρlt j r k (by omega), vin _ _ _ h, vin _ _ _ h]
      · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
        have key : ∀ i', i' + 1 < C.size → σ j i' = i → ρ j r (N + N + i) = N + N + i' →
            V C' x (ρ j r (N + N + i)) = V C x (N + N + i) := by
          intro i' h1 h2 h3
          rw [h3, vgate C' hC' x i' (by omega), hg i' h1, vgate C hC x i (by omega)]
          show (G C (σ j i')).op.eval (((G C (σ j i')).inputs.map (ρ j r)).map (V C' x)) = _
          rw [h2, List.map_map]
          congr 1
          apply List.map_congr_left
          intro w hw
          have hwi := ardr C hC i (by omega) w hw
          show V C' x (ρ j r w) = V C x w
          by_cases hwj : w = N + N + j
          · have hVr : V C x r = V C x (N + N + j) := by
              rcases hh with h | h | h
              · omega
              · exact h
              · exact absurd hwj (h i (by omega) w hw)
            rw [hwj, ρeq, ← hVr]
            have := ih r (by omega) (by omega) (by omega) (Or.inl hr)
            rwa [ρlt j r r hr] at this
          · refine ih w hwi (by omega) hwj ?_
            rcases hh with h | h
            · exact Or.inl (by omega)
            · exact Or.inr h
        rcases Nat.lt_or_ge i j with h' | h'
        · exact key i (by omega) (if_pos h') (ρlt _ _ _ (by omega))
        · have hne : i ≠ j := fun e => hkj (by rw [e])
          refine key (i - 1) (by omega) ?_ ?_
          · show (if i - 1 < j then i - 1 else i - 1 + 1) = i
            rw [if_neg (by omega)]; omega
          · rw [ρgt _ _ _ (by omega)]; omega
  -- circuits given by their gates
  have mkG : ∀ (m : ℕ) (f : ℕ → PEqualNP.CircuitLowerBounds.Gate) (o i : ℕ), i < m → G ⟨(List.range m).map f, o⟩ i = f i := by
    intro m f o i hi
    rw [GD]
    show ((List.range m).map f).getD i _ = _
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  have mkS : ∀ (m : ℕ) (f : ℕ → PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (PEqualNP.CircuitLowerBounds.Circuit.mk ((List.range m).map f) o).size = m := by
    intro m f o
    show ((List.range m).map f).length = m
    rw [List.length_map, List.length_range]
  have mkA : ∀ (m : ℕ) (f : ℕ → PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ i < m, ((f i).op = .and ∨ (f i).op = .or) ∧
      (∀ w ∈ (f i).inputs, w < N + N + i) ∧ (f i).inputs.length = 2) →
      PEqualNP.TopForm.IsAO2 (N + N) ⟨(List.range m).map f, o⟩ := by
    intro m f o h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      exact (h i (List.mem_range.1 hi)).1
    · intro j hj w hw
      have hj' : j < m := by
        have : j < ((List.range m).map f).length := hj
        rwa [List.length_map, List.length_range] at this
      have e := mkG m f o j hj'
      have hw' : w ∈ (G ⟨(List.range m).map f, o⟩ j).inputs := hw
      rw [e] at hw'
      exact (h j hj').2.1 w hw'
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
      exact (h i (List.mem_range.1 hi)).2.2
  have Mok : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → ∀ j r, j < C.size → r < N + N + j → ∀ i, i + 1 < C.size →
      ((M C j r i).op = .and ∨ (M C j r i).op = .or) ∧ (∀ w ∈ (M C j r i).inputs, w < N + N + i) ∧
      (M C j r i).inputs.length = 2 := by
    intro C hC j r hj hr i hi
    have hσ : σ j i < C.size := by simp only [σ]; split <;> omega
    refine ⟨aop C hC _ hσ, ?_, ?_⟩
    · intro w hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hw
      have hlt := ardr C hC _ hσ w' hw'
      rcases Nat.lt_trichotomy w' (N + N + j) with h | h | h
      · rw [ρlt _ _ _ h]
        simp only [σ] at hlt
        split at hlt <;> omega
      · rw [h, ρeq]
        simp only [σ] at hlt
        split at hlt <;> omega
      · rw [ρgt _ _ _ h]
        simp only [σ] at hlt
        split at hlt <;> omega
    · show ((G C (σ j i)).inputs.map (ρ j r)).length = 2
      rw [List.length_map]
      exact alen C hC _ hσ
  -- good circuits
  let Good : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C => PEqualNP.TopForm.IsAO2 (N + N) C ∧ ∀ z, V C z C.output = true ↔ P z
  have goodOf : ∀ C, PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → Good C := by
    intro C h1 h2
    refine ⟨h1, fun z => ?_⟩
    have h3 : V C z C.output = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := h2 z
    rw [h3]
    exact decide_eq_true_iff
  have goodTo : ∀ C, Good C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) := by
    intro C h z
    have h3 : V C z C.output = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact h.2 z
    exact h3
  have hedge : ∃ p l, I p l := by
    have h := hline ⟨0, hNpos⟩
    have h0 : 0 < (Finset.univ.filter (fun p => I p ⟨0, hNpos⟩)).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.1 h0
    exact ⟨p, _, (Finset.mem_filter.1 hp).2⟩
  have hPt : P (fun _ => true) := by
    obtain ⟨p, l, h⟩ := hedge
    exact ⟨p, l, h, rfl, rfl⟩
  have outlt : ∀ C, Good C → C.output < N + N + C.size := by
    intro C h
    by_contra hcon
    have h1 := (h.2 (fun _ => true)).2 hPt
    rw [vout C _ _ (by omega)] at h1
    exact absurd h1 (by decide)
  let Bel : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun C w => ∀ z, V C z w = true → P z
  let top : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun C j => (G C j).op = .or ∧ Bel C (N + N + j)
  let non : PEqualNP.CircuitLowerBounds.Circuit → Finset ℕ := fun C => (Finset.range C.size).filter (fun j => ¬ top C j)
  have ex1 : ∃ s, ∃ C, Good C ∧ C.size = s := ⟨_, C0, goodOf C0 hC0 hcomp0, rfl⟩
  obtain ⟨C1, hC1, hC1s⟩ := Nat.find_spec ex1
  have min1 : ∀ C, Good C → Nat.find ex1 ≤ C.size := fun C h => Nat.find_min' ex1 ⟨C, h, rfl⟩
  have ex2 : ∃ m, ∃ C, (Good C ∧ C.size = Nat.find ex1) ∧ (non C).card = m := ⟨_, C1, ⟨hC1, hC1s⟩, rfl⟩
  obtain ⟨C, ⟨hC, hCs⟩, hCm⟩ := Nat.find_spec ex2
  have min2 : ∀ C', Good C' → C'.size = C.size → (non C).card ≤ (non C').card := by
    intro C' h1 h2
    rw [hCm]
    exact Nat.find_min' ex2 ⟨C', ⟨h1, h2.trans hCs⟩, rfl⟩
  have least : ∀ C', Good C' → C.size ≤ C'.size := fun C' h => hCs ▸ min1 C' h
  clear hCm hCs min1
  refine le_trans ?_ (least C0 (goodOf C0 hC0 hcomp0))
  have hA := hC.1
  have ho := outlt C hC
  -- every gate but the output is read
  have read : ∀ j < C.size, N + N + j ≠ C.output → ∃ i < C.size, N + N + j ∈ (G C i).inputs := by
    intro j hj hjo
    by_contra hcon
    push_neg at hcon
    have hun : ∀ i < C.size, ∀ w ∈ (G C i).inputs, w ≠ N + N + j := by
      intro i hi w hw e
      exact hcon i hi (e ▸ hw)
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨(List.range (C.size - 1)).map (M C j 0), ρ j 0 C.output⟩
    have hA' : PEqualNP.TopForm.IsAO2 (N + N) C' :=
      mkA _ _ _ (fun i hi => Mok C hA j 0 hj (by omega) i (by omega))
    have hs' : C'.size = C.size - 1 := mkS _ _ _
    have hg' : Good C' := by
      refine ⟨hA', fun z => ?_⟩
      have := agree C C' hA hA' j 0 hj (by omega) (by omega)
        (fun i hi => mkG _ _ _ i (by omega)) z C.output ho (fun e => hjo e.symm) (Or.inr (Or.inr hun))
      show V C' z (ρ j 0 C.output) = true ↔ P z
      rw [this]
      exact hC.2 z
    have := least C' hg'
    omega
  -- the normal form
  have nf : ∀ j < C.size, (∃ w ∈ (G C j).inputs, Bel C w) → top C j := by
    rintro j hj ⟨w, hw, hwB⟩
    by_contra htop
    have hlw := ardr C hA j hj w hw
    obtain ⟨r, hr, hrV⟩ : ∃ r < N + N + j, ∀ x, V C x w = false → V C x r = V C x (N + N + j) := by
      obtain ⟨u, v, huv⟩ := List.length_eq_two.1 (alen C hA j hj)
      have hgv : ∀ x, V C x (N + N + j) = (G C j).op.eval [V C x u, V C x v] := by
        intro x
        rw [vgate C hA x j hj, huv]
        rfl
      have hu : u < N + N + j := ardr C hA j hj u (by rw [huv]; simp)
      have hv : v < N + N + j := ardr C hA j hj v (by rw [huv]; simp)
      rw [huv] at hw
      have hw2 : w = u ∨ w = v := by simpa using hw
      rcases aop C hA j hj with hop | hop
      · refine ⟨w, hlw, fun x hx => ?_⟩
        rw [hgv, hop, hx]
        show _ = (V C x u && (V C x v && true))
        rcases hw2 with rfl | rfl <;> simp [hx]
      · rcases hw2 with rfl | rfl
        · refine ⟨v, hv, fun x hx => ?_⟩
          rw [hgv, hop, hx]
          show _ = (false || (V C x v || false))
          simp
        · refine ⟨u, hu, fun x hx => ?_⟩
          rw [hgv, hop, hx]
          show _ = (V C x u || (false || false))
          simp
    let f : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun i => if i + 1 < C.size then M C j r i else ⟨.or, [ρ j r C.output, w]⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨(List.range C.size).map f, N + N + (C.size - 1)⟩
    have hf : ∀ i, i + 1 < C.size → f i = M C j r i := fun i hi => if_pos hi
    have hfl : f (C.size - 1) = ⟨.or, [ρ j r C.output, w]⟩ := if_neg (by omega)
    have hρo : ρ j r C.output < N + N + (C.size - 1) := by
      rcases Nat.lt_trichotomy C.output (N + N + j) with h | h | h
      · rw [ρlt _ _ _ h]; omega
      · rw [h, ρeq]; omega
      · rw [ρgt _ _ _ h]; omega
    have hA' : PEqualNP.TopForm.IsAO2 (N + N) C' := by
      apply mkA
      intro i hi
      by_cases hi' : i + 1 < C.size
      · rw [hf i hi']
        exact Mok C hA j r hj hr i hi'
      · have e : i = C.size - 1 := by omega
        rw [e, hfl]
        refine ⟨Or.inr rfl, ?_, rfl⟩
        intro w' hw'
        have : w' = ρ j r C.output ∨ w' = w := by simpa using hw'
        rcases this with rfl | rfl
        · exact hρo
        · omega
    have hs' : C'.size = C.size := mkS _ _ _
    have hgM : ∀ i, i + 1 < C.size → G C' i = M C j r i := fun i hi => (mkG _ _ _ i (by omega)).trans (hf i hi)
    have ag := agree C C' hA hA' j r hj hr (by omega) hgM
    have agw : ∀ x, V C' x w = V C x w := by
      intro x
      have := ag x w (by omega) (by omega) (Or.inl hlw)
      rwa [ρlt _ _ _ hlw] at this
    have ag0 : ∀ x, V C x w = false → ∀ k < N + N + C.size, V C' x (ρ j r k) = V C x k := by
      intro x hx k hk
      by_cases hkj : k = N + N + j
      · rw [hkj, ρeq, ← hrV x hx]
        have := ag x r (by omega) (by omega) (Or.inl hr)
        rwa [ρlt _ _ _ hr] at this
      · exact ag x k hk hkj (Or.inr (Or.inl (hrV x hx)))
    have hlast : ∀ x, V C' x (N + N + (C.size - 1)) = (V C' x (ρ j r C.output) || V C x w) := by
      intro x
      rw [vgate C' hA' x (C.size - 1) (by omega), mkG _ _ _ _ (by omega), hfl]
      show (V C' x (ρ j r C.output) || (V C' x w || false)) = _
      rw [agw, Bool.or_false]
    have hgood : Good C' := by
      refine ⟨hA', fun z => ?_⟩
      show V C' z (N + N + (C.size - 1)) = true ↔ P z
      rw [hlast]
      cases hz : V C z w with
      | true => simp [hwB z hz]
      | false =>
        rw [ag0 z hz _ ho, Bool.or_false]
        exact hC.2 z
    have hle := min2 C' hgood hs'
    have hjn : j ∈ non C := Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, htop⟩
    have hinj : (non C').card ≤ ((non C).erase j).card := by
      apply Finset.card_le_card_of_injOn (σ j)
      · intro i hi
        obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
        have hi1' := Finset.mem_range.1 hi1
        rw [hs'] at hi1'
        have hi3 : i + 1 < C.size := by
          by_contra hcon
          have e : i = C.size - 1 := by omega
          apply hi2
          refine ⟨?_, ?_⟩
          · rw [e, mkG _ _ _ _ (by omega), hfl]
          · intro z hz
            rw [e] at hz
            exact (hgood.2 z).1 hz
        have hσ1 : σ j i < C.size := by simp only [σ]; split <;> omega
        have hσ2 : σ j i ≠ j := by simp only [σ]; split <;> omega
        have hσ3 : ρ j r (N + N + σ j i) = N + N + i := by
          simp only [σ]
          split
          · exact ρlt _ _ _ (by omega)
          · rw [ρgt _ _ _ (by omega)]; omega
        refine Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hσ2, Finset.mem_filter.2 ⟨Finset.mem_range.2 hσ1, ?_⟩⟩)
        rintro ⟨h1, h2⟩
        apply hi2
        refine ⟨?_, ?_⟩
        · rw [hgM i hi3]
          exact h1
        · intro z hz
          cases hzw : V C z w with
          | true => exact hwB z hzw
          | false =>
            apply h2 z
            rw [← ag0 z hzw _ (by omega), hσ3]
            exact hz
      · intro a _ b _ hab
        simp only [σ] at hab
        split at hab <;> split at hab <;> omega
    rw [Finset.card_erase_of_mem hjn] at hinj
    have : 0 < (non C).card := Finset.card_pos.2 ⟨j, hjn⟩
    omega
  -- few blocks
  let tops : Finset ℕ := (Finset.range C.size).filter (fun j => top C j)
  let blk : Finset ℕ := (Finset.range C.size).filter (fun j => (G C j).op = .and ∧ Bel C (N + N + j))
  have hsplit : tops.card + (non C).card = C.size := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.range C.size) (fun j => top C j)
    rwa [Finset.card_range] at this
  have hdisj : Disjoint tops blk := by
    rw [Finset.disjoint_left]
    intro a h1 h2
    have e1 := (Finset.mem_filter.1 h1).2.1
    have e2 := (Finset.mem_filter.1 h2).2.1
    rw [e1] at e2
    cases e2
  have hfew : blk.card ≤ tops.card + 1 := by
    have hsub : tops ∪ blk ⊆ {C.output - (N + N)} ∪ tops.biUnion (fun i => (G C i).inputs.toFinset.image (· - (N + N))) := by
      intro a ha
      have ha' : a < C.size ∧ Bel C (N + N + a) := by
        rcases Finset.mem_union.1 ha with h | h
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
          exact ⟨Finset.mem_range.1 h1, h2.2⟩
        · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
          exact ⟨Finset.mem_range.1 h1, h2.2⟩
      by_cases hao : N + N + a = C.output
      · apply Finset.mem_union_left
        rw [Finset.mem_singleton]
        omega
      · obtain ⟨i, hi, hmem⟩ := read a ha'.1 hao
        apply Finset.mem_union_right
        refine Finset.mem_biUnion.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, nf i hi ⟨_, hmem, ha'.2⟩⟩, ?_⟩
        exact Finset.mem_image.2 ⟨_, List.mem_toFinset.2 hmem, by omega⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have h2 := Finset.card_union_le {C.output - (N + N)}
      (tops.biUnion (fun i => (G C i).inputs.toFinset.image (· - (N + N))))
    have h3 : (tops.biUnion (fun i => (G C i).inputs.toFinset.image (· - (N + N)))).card ≤ tops.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro i hi
      have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
      exact le_trans Finset.card_image_le (le_trans (List.toFinset_card_le _) (le_of_eq (alen C hA i hi')))
    rw [Finset.card_singleton] at h2
    omega
  -- the block cost
  obtain ⟨O, S, T, Eb, hO, hOd, hβ0, hcost0⟩ := blockCost q N I C (Bel C) (top C) hq hN hline' hpt hA (goodTo C hC)
    (fun C' h1 h2 => least C' (goodOf C' h1 (fun z => (congrFun h2 z).trans (goodTo C hC z))))
    (fun w => ⟨fun h z hz => (hC.2 z).2 (h z hz), fun h z hz => (hC.2 z).1 (h z hz)⟩) (fun _ => Iff.rfl) nf
  have hβ1 : ∀ p l, ∃ b, I p l → b < C.size ∧ (G C b).op = .and ∧ Bel C (N + N + b) ∧
      (p ∈ S b ∨ l ∈ T b) ∧ (p, l) ∈ Eb b := by
    intro p l
    by_cases h : I p l
    · obtain ⟨b, h1, h2, h3, _, h4, h5⟩ := hβ0 p l h
      refine ⟨b, fun _ => ⟨h1, ?_, h3, h4, h5⟩⟩
      rcases aop C hA _ h1 with h6 | h6
      · exact h6
      · exact absurd ⟨h6, h3⟩ h2
    · exact ⟨0, fun h' => absurd h' h⟩
  choose β hβ using hβ1
  have hcost : ∀ b, (S b).card + (T b).card +
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ β e.1 e.2 = b)).card ≤ (O b).card + 1 := by
    intro b
    refine le_trans (Nat.add_le_add_left (Finset.card_le_card ?_) _) (hcost0 b)
    intro e he
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 he
    have h3 := (hβ e.1 e.2 h1).2.2.2.2
    rw [h2] at h3
    exact h3
  -- degrees
  have hdeg : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
    intro p
    have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun (p' l : Fin N) => I p' l)
      (s := Finset.univ.erase p) (t := Finset.univ.filter (fun l => I p l))
    have e1 : ∀ p' ∈ Finset.univ.erase p,
        (Finset.bipartiteAbove (fun (p' l : Fin N) => I p' l) (Finset.univ.filter (fun l => I p l)) p').card = 1 := by
      intro p' hp'
      obtain ⟨l, hl, hu⟩ := hpt p p' (Finset.ne_of_mem_erase hp').symm
      rw [Finset.card_eq_one]
      refine ⟨l, ?_⟩
      ext l'
      rw [Finset.mem_bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, h1⟩, h2⟩
        exact hu l' ⟨h1, h2⟩
      · rintro rfl
        exact ⟨⟨Finset.mem_univ _, hl.1⟩, hl.2⟩
    have e2 : ∀ l ∈ Finset.univ.filter (fun l => I p l),
        (Finset.bipartiteBelow (fun (p' l : Fin N) => I p' l) (Finset.univ.erase p) l).card = q := by
      intro l hl
      have hl' := (Finset.mem_filter.1 hl).2
      have : Finset.bipartiteBelow (fun (p' l : Fin N) => I p' l) (Finset.univ.erase p) l =
          (Finset.univ.filter (fun p' => I p' l)).erase p := by
        ext p'
        rw [Finset.mem_bipartiteBelow, Finset.mem_erase, Finset.mem_erase, Finset.mem_filter]
        tauto
      rw [this, Finset.card_erase_of_mem (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hl'⟩), hline]
      rfl
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul] at h
    have h' : (q + 1) * q = (Finset.univ.filter (fun l => I p l)).card * q := by
      rw [← h, show N - 1 = q ^ 2 + q by omega]; ring
    exact (Nat.eq_of_mul_eq_mul_right (by omega) h').symm
  -- edges
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have hE : E.card = N * (q + 1) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ) (f := Prod.snd)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [h, Finset.sum_congr rfl (g := fun _ => q + 1), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    intro l _
    rw [← hline l]
    refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
    · intro e he
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 he
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← h2]
      exact (Finset.mem_filter.1 h1).2
    · intro a ha b hb hab
      exact Prod.ext hab ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
    · intro p hp
      exact ⟨(p, l), Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2⟩, rfl⟩, rfl⟩
  have hEb : E.card = ∑ b ∈ blk, (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ β e.1 e.2 = b)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := blk) (f := fun e => β e.1 e.2) (by
      intro e he
      obtain ⟨h1, h2, h3, _⟩ := hβ e.1 e.2 (Finset.mem_filter.1 (Finset.mem_coe.1 he)).2
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2, h3⟩))
    rw [h]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.filter_filter]
  let U : Finset (Fin N) := blk.biUnion S
  let W : Finset (Fin N) := blk.biUnion T
  have hcov : E ⊆ U.biUnion (fun p => (Finset.univ.filter (fun l => I p l)).image (fun l => (p, l))) ∪
      W.biUnion (fun l => (Finset.univ.filter (fun p => I p l)).image (fun p => (p, l))) := by
    rintro ⟨p, l⟩ he
    have hI : I p l := (Finset.mem_filter.1 he).2
    obtain ⟨h1, h2, h3, h4, _⟩ := hβ p l hI
    have hb : β p l ∈ blk := Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2, h3⟩
    rcases h4 with h | h
    · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨p, Finset.mem_biUnion.2 ⟨_, hb, h⟩, ?_⟩)
      exact Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hI⟩, rfl⟩
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨l, Finset.mem_biUnion.2 ⟨_, hb, h⟩, ?_⟩)
      exact Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hI⟩, rfl⟩
  have hcovc : N ≤ U.card + W.card := by
    have h1 := le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
    have h2 : (U.biUnion (fun p => (Finset.univ.filter (fun l => I p l)).image (fun l => (p, l)))).card ≤ U.card * (q + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun p _ => le_trans Finset.card_image_le (le_of_eq (hdeg p)))
    have h3 : (W.biUnion (fun l => (Finset.univ.filter (fun p => I p l)).image (fun p => (p, l)))).card ≤ W.card * (q + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun l _ => le_trans Finset.card_image_le (le_of_eq (hline l)))
    rw [hE] at h1
    have h4 : N * (q + 1) ≤ (U.card + W.card) * (q + 1) := by
      rw [Nat.add_mul]; omega
    exact Nat.le_of_mul_le_mul_right h4 (Nat.succ_pos q)
  have hU : U.card ≤ ∑ b ∈ blk, (S b).card := Finset.card_biUnion_le
  have hW : W.card ≤ ∑ b ∈ blk, (T b).card := Finset.card_biUnion_le
  have hOs : ∑ b ∈ blk, (O b).card ≤ (non C).card := by
    rw [← Finset.card_biUnion (fun a _ b _ hab => hOd a b hab)]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨h1, h2⟩ := hO b g hb
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
  have hsum : ∑ b ∈ blk, ((S b).card + (T b).card +
      (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ β e.1 e.2 = b)).card) ≤ ∑ b ∈ blk, ((O b).card + 1) :=
    Finset.sum_le_sum (fun b _ => hcost b)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← hEb, hE, Finset.sum_const,
    smul_eq_mul, Nat.mul_one] at hsum
  have hfin : N * (q + 2) = N * (q + 1) + N := by ring
  omega
