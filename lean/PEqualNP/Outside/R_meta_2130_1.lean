import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2130_1 (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true }) (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 1 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → ∀ p : Fin N, Fintype.card {l : Fin N // I p l} ≤ q + 1) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true } := by
  intro q N I inst C hq hN hcol huniq hmin hsound
  by_cases hq86 : q ≤ 86
  swap
  · exact @h1 q N I inst C (by omega) hN hcol huniq hmin hsound
  classical
  intro D edge T hT
  have hgm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have h := (hmin.1 g hg).1
    simpa using h
  have hg2 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hmin.1 g hg).2
  have hsnoc : ∀ (w : List Bool) (b : Bool) (i : ℕ), (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
    intro w b i
    split_ifs with h1 h2
    · exact List.getD_append w [b] false i h1
    · subst h2; simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
      rw [hk]; simp
  have hev : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ f f' : ℕ → Bool, (∀ i, f i = true → f' i = true) → g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
    intro g hop f f' hff h
    rcases hop with h1 | h1
    · rw [h1] at h ⊢
      change (g.inputs.map f).all id = true at h
      change (g.inputs.map f').all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp_apply, id] at h ⊢
      exact fun i hi => hff i (h i hi)
    · rw [h1] at h ⊢
      change (g.inputs.map f).any id = true at h
      change (g.inputs.map f').any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp_apply, id] at h ⊢
      obtain ⟨i, hi, hfi⟩ := h
      exact ⟨i, hi, hff i hfi⟩
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl step x := fun x => rfl
  have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append w _ false i hi
  have hstepmono : ∀ g : PEqualNP.CircuitLowerBounds.Gate, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ w w' : List Bool, w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) → ∀ i, (step w g).getD i false = true → (step w' g).getD i false = true := by
    intro g hop w w' hl hww i hi
    change (w ++ [_]).getD i false = true at hi
    change (w' ++ [_]).getD i false = true
    rw [hsnoc] at hi ⊢
    rw [← hl]
    split_ifs at hi ⊢ with h1 h2 <;> first | exact hww i hi | exact hev g hop _ _ hww hi
  have hmono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ w w' : List Bool, w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) → ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step w').getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ w w' _ hww; exact hww
    | cons g gs ih =>
      intro hgs w w' hl hww
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (step w g) (step w' g)
      · simp [step, hl]
      · exact hstepmono g (hgs g (List.mem_cons_self)) w w' hl hww
  have hdiff : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool) (k : ℕ), w.length = w'.length → (∀ i, i ≠ k → w.getD i false = w'.getD i false) → ∀ i, w.length ≤ i → (gs.foldl step w).getD i false ≠ (gs.foldl step w').getD i false → ∃ j, ∃ hj : j < gs.length, k ∈ (gs[j]'hj).inputs ∧ (gs.foldl step w).getD (w.length + j) false ≠ (gs.foldl step w').getD (w.length + j) false := by
    intro gs
    induction gs with
    | nil =>
      intro w w' k hl _ i hi hne
      exfalso
      apply hne
      change w.getD i false = w'.getD i false
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    | cons g gs ih =>
      intro w w' k hl hag i hi hne
      rw [List.foldl_cons, List.foldl_cons] at hne
      have hv : (step w g).length = w.length + 1 := by simp [step]
      have hv' : (step w' g).length = w.length + 1 := by simp [step, hl]
      have hb : ∀ gs' : List PEqualNP.CircuitLowerBounds.Gate, (gs'.foldl step (step w g)).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        intro gs'
        rw [hpre _ _ _ (by omega)]
        change (w ++ [_]).getD w.length false = _
        simp
      have hb' : ∀ gs' : List PEqualNP.CircuitLowerBounds.Gate, (gs'.foldl step (step w' g)).getD w.length false = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        intro gs'
        rw [hpre _ _ _ (by omega)]
        change (w' ++ [_]).getD w.length false = _
        rw [hl]; simp
      by_cases hbb : g.op.eval (g.inputs.map fun i => w.getD i false) = g.op.eval (g.inputs.map fun i => w'.getD i false)
      · have hi1 : w.length + 1 ≤ i := by
          by_contra hcon
          have : i = w.length := by omega
          subst this
          exact hne ((hb gs).trans (hbb.trans (hb' gs).symm))
        obtain ⟨j, hj, hk, hd⟩ := ih (step w g) (step w' g) k (by rw [hv, hv']) (by
          intro i' hi'
          change (w ++ [_]).getD i' false = (w' ++ [_]).getD i' false
          rw [hsnoc, hsnoc, ← hl]
          split_ifs
          · exact hag i' hi'
          · exact hbb
          · rfl) i (by omega) hne
        refine ⟨j + 1, by simp; omega, by simpa using hk, ?_⟩
        rw [List.foldl_cons, List.foldl_cons]
        rw [hv] at hd
        rwa [show w.length + (j + 1) = w.length + 1 + j by omega]
      · have hk : k ∈ g.inputs := by
          by_contra hk
          apply hbb
          congr 1
          apply List.map_congr_left
          intro i' hi'
          exact hag i' (fun h => hk (h ▸ hi'))
        refine ⟨0, by simp, by simpa using hk, ?_⟩
        rw [List.foldl_cons, List.foldl_cons, Nat.add_zero, hb, hb']
        exact hbb
  have hn : ∀ x : Fin (N + N) → Bool, (List.ofFn x).length = N + N := fun x => List.length_ofFn
  have hof : ∀ (x : Fin (N + N) → Bool) (i : ℕ) (h : i < N + N), (List.ofFn x).getD i false = x ⟨i, h⟩ := by
    intro x i h; simp [List.getD_eq_getElem?_getD, h]
  have hof' : ∀ (x : Fin (N + N) → Bool) (i : ℕ), ¬ i < N + N → (List.ofFn x).getD i false = false := by
    intro x i h; simp [List.getD_eq_getElem?_getD, h]
  have hCm : ∀ x y : Fin (N + N) → Bool, (∀ k, x k = true → y k = true) → ∀ i, (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
    intro x y hxy i hi
    rw [hwires] at hi ⊢
    refine hmono C.gates hgm _ _ (by rw [hn, hn]) ?_ i hi
    intro i' hi'
    by_cases h : i' < N + N
    · rw [hof _ _ h] at hi' ⊢; exact hxy _ hi'
    · rw [hof' _ _ h] at hi'; exact absurd hi' (by simp)
  have leaf_count : ∀ (n : ℕ) (G : Finset ℕ) (ins : ℕ → List ℕ) (out : ℕ) (hout : out ∈ G) (hclos : ∀ j ∈ G, j ≠ out → ∃ j' ∈ G, n + j ∈ ins j') (hlen : ∀ j ∈ G, (ins j).length ≤ 2), ((G.biUnion (fun j => (ins j).toFinset)).filter (fun i => i < n)).card ≤ G.card + 1 := by
    intro n G ins out hout hclos hlen
    classical
    set Rd := G.biUnion (fun j => (ins j).toFinset) with hRd
    have h1 : Rd.card ≤ 2 * G.card := by
      calc Rd.card ≤ ∑ j ∈ G, (ins j).toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ _j ∈ G, 2 := Finset.sum_le_sum (fun j hj => (List.toFinset_card_le _).trans (hlen j hj))
        _ = 2 * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hd : Disjoint (Rd.filter (fun i => i < n)) ((G.erase out).image (fun j => n + j)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      have := (Finset.mem_filter.mp ha).2
      omega
    have hs : Rd.filter (fun i => i < n) ∪ (G.erase out).image (fun j => n + j) ⊆ Rd := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_filter.mp ha).1
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hne, hjG⟩ := Finset.mem_erase.mp hj
        obtain ⟨j', hj', hr⟩ := hclos j hjG hne
        exact Finset.mem_biUnion.mpr ⟨j', hj', List.mem_toFinset.mpr hr⟩
    have h2 := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (fun a b h => by simpa using h),
      Finset.card_erase_of_mem hout] at h2
    have : 1 ≤ G.card := Finset.card_pos.mpr ⟨out, hout⟩
    omega
  have pair_glue : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1) (hcol : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (T : Fin N → Finset (Fin N)) (hTI : ∀ l p, p ∈ T l → I p l) (P L : Finset (Fin N)) (hpt : ∀ l p, p ∈ T l → p ∈ P) (hln : ∀ l p, p ∈ T l → l ∈ L), 2 * ∑ l, (T l).card ≤ (q + 1) * (P.card + L.card) ∧ ∑ l, (T l).card ≤ P.card * L.card := by
    intro q N I instDR hq hN hcol huniq T hTI P L hpt hln
    classical
    have hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
      intro p
      have hdeg := h2 q N I hq hN hcol huniq p
      rwa [Fintype.card_subtype] at hdeg
    have hsubL : ∑ l, (T l).card = ∑ l ∈ L, (T l).card := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      exact hl (hln l p hp)
    have hline : ∑ l, (T l).card ≤ (q + 1) * L.card := by
      have hT : ∀ l, (T l).card ≤ q + 1 := by
        intro l
        have h := hcol l
        rw [Fintype.card_subtype] at h
        rw [← h]
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTI l p hp⟩
      rw [hsubL]
      calc ∑ l ∈ L, (T l).card ≤ ∑ _l ∈ L, (q + 1) := Finset.sum_le_sum (fun l _ => hT l)
        _ = (q + 1) * L.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hprod : ∑ l, (T l).card ≤ P.card * L.card := by
      rw [hsubL]
      calc ∑ l ∈ L, (T l).card ≤ ∑ _l ∈ L, P.card :=
            Finset.sum_le_sum (fun l _ => Finset.card_le_card (fun p hp => hpt l p hp))
        _ = P.card * L.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hpoint : ∑ l, (T l).card ≤ (q + 1) * P.card := by
      have hsw : ∑ l, (T l).card = ∑ p, (Finset.univ.filter (fun l => p ∈ T l)).card := by
        have e1 : ∀ l, (T l).card = ∑ p, if p ∈ T l then 1 else 0 := by
          intro l
          rw [Finset.sum_boole]
          simp
        have e2 : ∀ p, (Finset.univ.filter (fun l => p ∈ T l)).card = ∑ l, if p ∈ T l then 1 else 0 := by
          intro p
          rw [Finset.sum_boole]
          simp
        rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_comm]
        exact Finset.sum_congr rfl (fun p _ => (e2 p).symm)
      rw [hsw]
      calc ∑ p, (Finset.univ.filter (fun l => p ∈ T l)).card
          = ∑ p ∈ P, (Finset.univ.filter (fun l => p ∈ T l)).card := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro p _ hp
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro l hl
            exact hp (hpt l p (Finset.mem_filter.mp hl).2)
        _ ≤ ∑ _p ∈ P, (q + 1) := by
            apply Finset.sum_le_sum
            intro p _
            refine le_trans (Finset.card_le_card ?_) (hrow p)
            intro l hl
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTI l p (Finset.mem_filter.mp hl).2⟩
        _ = (q + 1) * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    exact ⟨by nlinarith, hprod⟩
  have final_arith : ∀ (q t a b r : ℕ) (hq : q ≤ 86) (h1 : 2 * t ≤ (q + 1) * (a + b)) (h2 : t ≤ a * b) (h3 : a + b ≤ r + 1), t ≤ 44 * r := by
    intro q t a b r hq h1 h2 h3
    rcases Nat.lt_or_ge r 87 with hr | hr
    · have hab : a * b ≤ 44 * r ∨ r = 0 := by
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · exact Or.inr h0
        · left
          have : 4 * (a * b) ≤ (a + b) * (a + b) := by nlinarith [sq_nonneg ((a : ℤ) - b)]
          have hr2 : (r + 1) * (r + 1) ≤ 176 * r := by nlinarith
          nlinarith
      rcases hab with hab | h0
      · exact h2.trans hab
      · subst h0
        have : a * b = 0 := by
          rcases Nat.eq_zero_or_pos a with ha | ha
          · simp [ha]
          · have : b = 0 := by omega
            simp [this]
        omega
    · nlinarith
  have crit_closure : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (hgm : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) {ι : Type} (S : Finset ι) (lo hi : ι → Fin n → Bool) (hout : n ≤ C.output) (hC : ∀ a ∈ S, (C.wires (List.ofFn (hi a))).getD C.output false = true ∧ (C.wires (List.ofFn (lo a))).getD C.output false = false) (hS : S.Nonempty), ∃ G : Finset ℕ, (∀ j ∈ G, ∃ hj : j < C.gates.length, ∃ a ∈ S, (C.wires (List.ofFn (hi a))).getD (n + j) false = true ∧ (C.wires (List.ofFn (lo a))).getD (n + j) false = false) ∧ (C.output - n) ∈ G ∧ (∀ j ∈ G, j ≠ C.output - n → ∃ j' ∈ G, ∃ hj' : j' < C.gates.length, n + j ∈ (C.gates[j']'hj').inputs) ∧ ∀ a ∈ S, ∃ j ∈ G, ∃ hj : j < C.gates.length, ∃ i : Fin n, lo a i = false ∧ hi a i = true ∧ i.val ∈ (C.gates[j]'hj).inputs := by
    intro n C hgm ι S lo hi hout hC hS
    classical
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl step x := fun x => rfl
    have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp [step]; omega
    have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i _; rfl
      | cons g gs ih =>
        intro w i hi
        rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
        exact List.getD_append w _ false i hi
    have hn : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => List.length_ofFn
    have hof : ∀ (x : Fin n → Bool) (i : ℕ) (h : i < n), (List.ofFn x).getD i false = x ⟨i, h⟩ := by
      intro x i h; simp [List.getD_eq_getElem?_getD, h]
    have hgate : ∀ (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length), (C.wires (List.ofFn x)).getD (n + j) false = (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
      intro x j hj
      have hsplit : C.gates = C.gates.take j ++ (C.gates[j]'hj :: C.gates.drop (j + 1)) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      let w0 := (C.gates.take j).foldl step (List.ofFn x)
      have hw0 : w0.length = n + j := by
        simp only [w0]; rw [hlen, hn, List.length_take]; omega
      have hall : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl step (step w0 (C.gates[j]'hj)) := by
        rw [hwires]
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hlt : ∀ i, i < n + j → (C.wires (List.ofFn x)).getD i false = w0.getD i false := by
        intro i hi
        rw [hall, hpre _ _ _ (by simp [step]; omega)]
        exact List.getD_append _ _ false i (by omega)
      rw [hall, hpre _ _ _ (by simp [step]; omega)]
      change (w0 ++ [_]).getD (n + j) false = _
      rw [← hw0, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [← hall, hlt i (by omega)]
      · exact List.getD_eq_default _ _ (by omega)
    have hbig : ∀ (x : Fin n → Bool) (w : ℕ), (C.wires (List.ofFn x)).getD w false = true → w < n + C.gates.length := by
      intro x w h
      by_contra hc
      rw [List.getD_eq_default _ _ (by rw [hwires, hlen, hn]; omega)] at h
      exact absurd h (by simp)
    let Crit : ι → ℕ → Prop := fun a w => (C.wires (List.ofFn (hi a))).getD w false = true ∧ (C.wires (List.ofFn (lo a))).getD w false = false
    let Step : ι → ℕ → ℕ → Prop := fun a u w => Crit a u ∧ Crit a w ∧ ∃ j, ∃ hj : j < C.gates.length, w = n + j ∧ u ∈ (C.gates[j]'hj).inputs
    let G : Finset ℕ := (Finset.range C.gates.length).filter (fun j => ∃ a ∈ S, Crit a (n + j) ∧ Relation.ReflTransGen (Step a) (n + j) C.output)
    have hcritin : ∀ a w, Crit a w → n ≤ w → ∃ u, u < w ∧ Crit a u ∧ ∃ j, ∃ hj : j < C.gates.length, w = n + j ∧ u ∈ (C.gates[j]'hj).inputs := by
      intro a w hw hnw
      have hwl := hbig _ _ hw.1
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have h1 := hw.1
      have h0 := hw.2
      rw [hgate _ _ hj] at h1 h0
      have hop := hgm _ (List.getElem_mem hj)
      obtain ⟨u, hu, hu1, hu0⟩ : ∃ u ∈ (C.gates[j]'hj).inputs, (if u < n + j then (C.wires (List.ofFn (hi a))).getD u false else false) = true ∧ (if u < n + j then (C.wires (List.ofFn (lo a))).getD u false else false) = false := by
        rcases hop with hop | hop
        · rw [hop] at h1 h0
          change (List.map _ _).all id = true at h1
          change (List.map _ _).all id = false at h0
          simp only [List.all_map, List.all_eq_true, List.all_eq_false, Function.comp_apply, id, Bool.not_eq_true] at h1 h0
          obtain ⟨u, hu, hu0⟩ := h0
          exact ⟨u, hu, h1 u hu, hu0⟩
        · rw [hop] at h1 h0
          change (List.map _ _).any id = true at h1
          change (List.map _ _).any id = false at h0
          simp only [List.any_map, List.any_eq_true, List.any_eq_false, Function.comp_apply, id, Bool.not_eq_true] at h1 h0
          obtain ⟨u, hu, hu1⟩ := h1
          exact ⟨u, hu, hu1, h0 u hu⟩
      have hlt : u < n + j := by
        by_contra hc
        rw [if_neg hc] at hu1
        exact absurd hu1 (by simp)
      rw [if_pos hlt] at hu1 hu0
      exact ⟨u, hlt, ⟨hu1, hu0⟩, j, hj, rfl, hu⟩
    have hread : ∀ a ∈ S, ∀ w, Crit a w → n ≤ w → Relation.ReflTransGen (Step a) w C.output → ∃ j ∈ G, ∃ hj : j < C.gates.length, ∃ i : Fin n, lo a i = false ∧ hi a i = true ∧ i.val ∈ (C.gates[j]'hj).inputs := by
      intro a ha w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hnw hr
        obtain ⟨u, hu, hcu, j, hj, rfl, hin⟩ := hcritin a w hw hnw
        by_cases hun : u < n
        · have hjG : j ∈ G := by
            simp only [G, Finset.mem_filter, Finset.mem_range]
            exact ⟨hj, a, ha, hw, hr⟩
          refine ⟨j, hjG, hj, ⟨u, hun⟩, ?_, ?_, hin⟩
          · have := hcu.2; rwa [hwires, hpre _ _ _ (by rw [hn]; exact hun), hof _ _ hun] at this
          · have := hcu.1; rwa [hwires, hpre _ _ _ (by rw [hn]; exact hun), hof _ _ hun] at this
        · exact ih u hu hcu (by omega) (Relation.ReflTransGen.head ⟨hcu, hw, j, hj, rfl, hin⟩ hr)
    obtain ⟨a0, ha0⟩ := hS
    refine ⟨G, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [G, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hj, a, ha, hc, -⟩ := hj
      exact ⟨hj, a, ha, hc⟩
    · simp only [G, Finset.mem_filter, Finset.mem_range]
      have hc := hC a0 ha0
      have := hbig _ _ hc.1
      refine ⟨by omega, a0, ha0, ?_, ?_⟩
      · rw [Nat.add_sub_cancel' hout]; exact hc
      · rw [Nat.add_sub_cancel' hout]
    · intro j hj hne
      simp only [G, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjl, a, ha, hc, hr⟩ := hj
      rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨-, hcc, j', hj', rfl, hin⟩, hr'⟩
      · exact absurd (by omega) hne
      · refine ⟨j', ?_, hj', hin⟩
        simp only [G, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj', a, ha, hcc, hr'⟩
    · intro a ha
      exact hread a ha C.output (hC a ha) hout Relation.ReflTransGen.refl
  have hzp : ∀ p : Fin N, PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p)) = false := by
    intro p
    let zp : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
    show PEqualNP.MetaComplexity.circuitFun (N + N) C zp = false
    apply hsound zp
    · have : Fintype.card {x : Fin N // zp (Fin.natAdd N x) = true} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        constructor
        rintro ⟨x, hx⟩
        simp [zp, Fin.ext_iff] at hx
        omega
      omega
    · rintro ⟨a, b, -, -, hb⟩
      simp [zp, Fin.ext_iff] at hb
      omega
  have hzl : ∀ l : Fin N, PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.natAdd N l)) = false := by
    intro l
    let zl : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
    show PEqualNP.MetaComplexity.circuitFun (N + N) C zl = false
    apply hsound zl
    · have : Fintype.card {x : Fin N // zl (Fin.natAdd N x) = true} = 1 := by
        simp [zl]
      omega
    · rintro ⟨a, b, -, ha, -⟩
      simp [zl, Fin.ext_iff] at ha
      omega
  let Act : Finset (Fin C.size) := Finset.univ.filter (fun a : Fin C.size => (C.wires (List.replicate (N + N) false)).getD (N + N + a.val) false = false ∧ ∃ l, ∃ p ∈ T l, (C.wires (List.ofFn (edge p l))).getD (N + N + a.val) false = true)
  have hAct : Fintype.card {a : Fin C.size // (C.wires (List.replicate (N + N) false)).getD (N + N + a.val) false = false ∧ ∃ l, ∃ p ∈ T l, (C.wires (List.ofFn (edge p l))).getD (N + N + a.val) false = true} = Act.card := Fintype.card_subtype _
  rw [hAct]
  by_cases hTe : ∀ l p, p ∉ T l
  · have : ∀ l, (T l).card = 0 := by
      intro l
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      exact hTe l
    simp [this]
  simp only [not_forall, not_not] at hTe
  obtain ⟨l0, p0, hp0⟩ := hTe
  have hout : N + N ≤ C.output := by
    have hCe' : (C.wires (List.ofFn (edge p0 l0))).getD C.output false = true := (hT l0 p0 hp0).2.1
    have hzp' : (C.wires (List.ofFn (fun k => decide (k = Fin.castAdd N p0)))).getD C.output false = false := hzp p0
    have hzl' : (C.wires (List.ofFn (fun k => decide (k = Fin.natAdd N l0)))).getD C.output false = false := hzl l0
    by_contra ho
    replace ho := Nat.lt_of_not_le ho
    rw [hwires, hpre _ _ _ (by rw [hn]; exact ho), hof _ _ ho] at hCe' hzp' hzl'
    simp only [edge, decide_eq_true_eq, decide_eq_false_iff_not] at hCe' hzp' hzl'
    rcases hCe' with h | h
    · exact hzp' h
    · exact hzl' h
  let S : Finset (Fin N × Fin N × Bool) := Finset.univ.filter (fun a => a.2.1 ∈ T a.1)
  let lo : Fin N × Fin N × Bool → Fin (N + N) → Bool := fun a => cond a.2.2 (fun k => decide (k = Fin.castAdd N a.2.1)) (fun k => decide (k = Fin.natAdd N a.1))
  let hi : Fin N × Fin N × Bool → Fin (N + N) → Bool := fun a => edge a.2.1 a.1
  obtain ⟨G, hG1, hG2, hG3, hG4⟩ := crit_closure (N + N) C hgm S lo hi hout (by
      intro a ha
      obtain ⟨l, p, b⟩ := a
      have hpa : p ∈ T l := by simpa [S] using ha
      cases b
      · exact ⟨(hT l p hpa).2.1, hzl l⟩
      · exact ⟨(hT l p hpa).2.1, hzp p⟩) ⟨(l0, p0, true), by simpa [S] using hp0⟩
  have hGact : G ⊆ Act.image (fun a => a.val) := by
    intro j hj
    obtain ⟨hjl, a, ha, h1, h0⟩ := hG1 j hj
    rw [Finset.mem_image]
    refine ⟨⟨j, hjl⟩, ?_, rfl⟩
    have hpa : a.2.1 ∈ T a.1 := by simpa [S] using ha
    simp only [Act, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, a.1, a.2.1, hpa, h1⟩
    rw [← List.ofFn_const]
    by_contra h2
    simp only [Bool.not_eq_false] at h2
    have := hCm (fun _ => false) (lo a) (by intro k hk; simp at hk) _ h2
    rw [h0] at this
    exact absurd this (by simp)
  have hGcard : G.card ≤ Act.card := (Finset.card_le_card hGact).trans Finset.card_image_le
  let ins : ℕ → List ℕ := fun j => if h : j < C.gates.length then (C.gates[j]'h).inputs else []
  have hleaf := leaf_count (N + N) G ins (C.output - (N + N)) hG2 (by
      intro j hj hne
      obtain ⟨j', hj'G, hj', hr⟩ := hG3 j hj hne
      refine ⟨j', hj'G, ?_⟩
      simp only [ins, dif_pos hj']
      exact hr) (by
      intro j _
      simp only [ins]
      split_ifs with h
      · exact hg2 _ (List.getElem_mem h)
      · simp)
  let P : Finset (Fin N) := Finset.univ.filter (fun p => ∃ l, p ∈ T l)
  let L : Finset (Fin N) := Finset.univ.filter (fun l => ∃ p, p ∈ T l)
  have hPL : P.card + L.card ≤ ((G.biUnion (fun j => (ins j).toFinset)).filter (fun i => i < N + N)).card := by
    rw [← Finset.card_disjSum]
    apply Finset.card_le_card_of_injOn (Sum.elim (fun p : Fin N => p.val) (fun l : Fin N => N + l.val))
    · intro x hx
      rcases x with p | l
      · have hx' := Finset.mem_coe.mp hx
        rw [Finset.inl_mem_disjSum] at hx'
        obtain ⟨l, hl⟩ : ∃ l, p ∈ T l := by simpa [P] using hx'
        obtain ⟨j, hjG, hj, i, hlo, hhi, hin⟩ := hG4 (l, p, false) (by simpa [S] using hl)
        simp only [lo, hi, edge, Bool.cond_false, decide_eq_false_iff_not, decide_eq_true_eq] at hlo hhi
        have hip : i = Fin.castAdd N p := by
          rcases hhi with h | h
          · exact h
          · exact absurd h hlo
        apply Finset.mem_coe.mpr
        simp only [Finset.mem_filter, Sum.elim_inl, Finset.mem_biUnion]
        refine ⟨⟨j, hjG, ?_⟩, by omega⟩
        simp only [ins, dif_pos hj, List.mem_toFinset]
        rw [hip] at hin
        simpa using hin
      · have hx' := Finset.mem_coe.mp hx
        rw [Finset.inr_mem_disjSum] at hx'
        obtain ⟨p, hp⟩ : ∃ p, p ∈ T l := by simpa [L] using hx'
        obtain ⟨j, hjG, hj, i, hlo, hhi, hin⟩ := hG4 (l, p, true) (by simpa [S] using hp)
        simp only [lo, hi, edge, Bool.cond_true, decide_eq_false_iff_not, decide_eq_true_eq] at hlo hhi
        have hil : i = Fin.natAdd N l := by
          rcases hhi with h | h
          · exact absurd h hlo
          · exact h
        apply Finset.mem_coe.mpr
        simp only [Finset.mem_filter, Sum.elim_inr, Finset.mem_biUnion]
        refine ⟨⟨j, hjG, ?_⟩, by omega⟩
        simp only [ins, dif_pos hj, List.mem_toFinset]
        rw [hil] at hin
        simpa [Nat.add_comm] using hin
    · intro x _ y _ hxy
      rcases x with p | l <;> rcases y with p' | l'
      · simp only [Sum.elim_inl] at hxy
        rw [Fin.ext hxy]
      · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
      · simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
      · simp only [Sum.elim_inr] at hxy
        rw [Fin.ext (by omega : l.val = l'.val)]
  have hpg := pair_glue q N I (by omega) hN hcol huniq T (fun l p hp => (hT l p hp).1) P L (by
      intro l p hp
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨l, hp⟩) (by
      intro l p hp
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hp⟩)
  exact final_arith q _ P.card L.card Act.card hq86 hpg.1 hpg.2 (by omega)
