import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2846_1
    (sub1 :
      ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        PEqualNP.TopForm.IsAO2 (Np + Nl) C →
        (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) →
        (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) →
        ∀ (P L : Finset ℕ),
          (∀ w, w ∈ P ↔ w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) →
          (∀ w, w ∈ L ↔ (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) →
          ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs,
            (¬ ∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) ∧
            (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches (Np + Nl) C w g →
              (¬ ∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD (Np + Nl + g) false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
          ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)))
    (sub2 :
      ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        PEqualNP.TopForm.IsAO2 (Np + Nl) C →
        (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
        (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) →
        (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) →
        ∀ (P L : Finset ℕ),
          (∀ w, w ∈ P ↔ w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) →
          (∀ w, w ∈ L ↔ (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) →
          ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ j < i, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) →
          (∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs,
            (¬ ∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) ∧
            (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches (Np + Nl) C w g →
              ¬ ∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD (Np + Nl + g) false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
          ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, ∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches (Np + Nl) C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  classical
  intro Np Nl I _ C hnoC4 hao hfun hleast hT_ex
  let n := Np + Nl
  let F : (Fin n → Bool) → Bool := fun z =>
    decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)
  have hfun' : ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C z = F z := hfun
  have hleast' : ∀ D, PEqualNP.TopForm.IsAO2 n D → (∀ z, PEqualNP.MetaComplexity.circuitFun n D z = F z) → C.size ≤ D.size := hleast
  let gateAt := PEqualNP.MetaComplexity.NestedCover.gateAt
  let pureSet (base : Finset ℕ) : ℕ → Finset ℕ := fun m =>
    Nat.rec base (fun k S =>
      if k < C.gates.length ∧ (gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (gateAt C k).inputs, u ∈ S
      then insert (n + k) S else S) m
  have pureSet_mono (base : Finset ℕ) : ∀ {a b}, a ≤ b → pureSet base a ⊆ pureSet base b := by
    intro a b hab
    induction hab with
    | refl => exact Finset.Subset.rfl
    | step _ ih =>
      intro x hx
      dsimp only [pureSet]
      split_ifs
      · exact Finset.mem_insert_of_mem (ih hx)
      · exact ih hx
  have pureSet_lt (base : Finset ℕ) (hb : ∀ w ∈ base, w < n) :
      ∀ k w, w ∈ pureSet base k → w < n + k := by
    intro k
    induction k with
    | zero =>
      intro w hw
      simpa only [Nat.add_zero] using hb w hw
    | succ k ih =>
      intro w hw
      dsimp only [pureSet] at hw
      split_ifs at hw
      · rcases Finset.mem_insert.mp hw with rfl | hw'
        · omega
        · exact Nat.lt_trans (ih w hw') (Nat.lt_succ_self _)
      · exact Nat.lt_trans (ih w hw) (Nat.lt_succ_self _)
  have pureSet_mem_of_le (base : Finset ℕ) :
      ∀ {k m w : ℕ}, k ≤ m → w < n + k → (w ∈ pureSet base m ↔ w ∈ pureSet base k) := by
    intro k m w hkm hw
    constructor
    · intro hwm
      induction hkm with
      | refl => exact hwm
      | @step m' hle ih =>
        have hle' : k ≤ m' := hle
        dsimp only [pureSet] at hwm
        split_ifs at hwm
        · rcases Finset.mem_insert.mp hwm with heq | hwm'
          · omega
          · exact ih hwm'
        · exact ih hwm
    · exact fun h => pureSet_mono base hkm h
  have pureSet_iff (base : Finset ℕ) (_hb : ∀ w ∈ base, w < n) :
      let P := pureSet base C.gates.length
      ∀ w, w ∈ P ↔ w ∈ base ∨
        ∃ i < C.gates.length, w = n + i ∧ (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (gateAt C i).inputs, u ∈ P := by
    intro P w
    constructor
    · intro hw
      suffices ∀ k ≤ C.gates.length, w ∈ pureSet base k →
          w ∈ base ∨ ∃ i < k, w = n + i ∧ (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∀ u ∈ (gateAt C i).inputs, u ∈ P from this C.gates.length le_rfl hw
      intro k hk hwk
      induction k with
      | zero => exact Or.inl hwk
      | succ k ih =>
        dsimp only [pureSet] at hwk
        split_ifs at hwk with hcond
        · rcases Finset.mem_insert.mp hwk with rfl | hwk'
          · refine Or.inr ⟨k, Nat.lt_succ_self _, rfl, hcond.2.1, fun u hu => ?_⟩
            exact pureSet_mono base (Nat.le_of_lt hk) (hcond.2.2 u hu)
          · rcases ih (Nat.le_of_lt hk) hwk' with hb0 | ⟨i, hi, heq, hop, hin⟩
            · exact Or.inl hb0
            · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, heq, hop, hin⟩
        · rcases ih (Nat.le_of_lt hk) hwk with hb0 | ⟨i, hi, heq, hop, hin⟩
          · exact Or.inl hb0
          · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, heq, hop, hin⟩
    · rintro (hw | ⟨i, hi, rfl, hop, hin⟩)
      · exact pureSet_mono base (Nat.zero_le _) hw
      · have hin_i : ∀ u ∈ (gateAt C i).inputs, u ∈ pureSet base i := by
          intro u hu
          have hlt_u : u < n + i := hao.2.1 i hi u hu
          exact (pureSet_mem_of_le base (Nat.le_of_lt hi) hlt_u).mp (hin u hu)
        have h_in_succ : n + i ∈ pureSet base (i + 1) := by
          dsimp only [pureSet]
          split_ifs
          exact Finset.mem_insert_self _ _
        exact pureSet_mono base hi h_in_succ
  let baseP := Finset.range Np
  let baseL := (Finset.range Nl).image (fun l => Np + l)
  let P := pureSet baseP C.gates.length
  let L := pureSet baseL C.gates.length
  have hbP : ∀ w ∈ baseP, w < n := by
    intro w hw
    have := Finset.mem_range.mp hw
    omega
  have hbL : ∀ w ∈ baseL, w < n := by
    intro w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    have := Finset.mem_range.mp hl
    omega
  have hP_iff : ∀ w, w ∈ P ↔ w < Np ∨ ∃ i < C.gates.length, w = n + i ∧
      (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ∀ u ∈ (gateAt C i).inputs, u ∈ P := by
    intro w
    simpa [P, baseP, Finset.mem_range] using pureSet_iff baseP hbP w
  have hL_iff : ∀ w, w ∈ L ↔ (Np ≤ w ∧ w < n) ∨ ∃ i < C.gates.length, w = n + i ∧
      (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ∀ u ∈ (gateAt C i).inputs, u ∈ L := by
    intro w
    have hiff := pureSet_iff baseL hbL w
    have hbase : w ∈ baseL ↔ Np ≤ w ∧ w < n := by
      simp only [baseL, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨l, hl, rfl⟩; omega
      · intro ⟨h1, h2⟩; exact ⟨w - Np, by omega, by omega⟩
    simpa [L, hbase] using hiff
  refine ⟨P, L, fun w hw => (hP_iff w).mp hw, fun w hw => (hL_iff w).mp hw, ?_⟩
  have gateAt_eq_getElem : ∀ {D : PEqualNP.CircuitLowerBounds.Circuit} {i : ℕ},
      i < D.gates.length → gateAt D i = D.gates[i] := by
    intro D i hi
    change D.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = D.gates[i]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have list_split_at : ∀ (l : List PEqualNP.CircuitLowerBounds.Gate) (i : ℕ), i < l.length →
      l = l.take i ++ [l[i]] ++ l.drop (i + 1) := by
    intro l i hi
    induction l generalizing i with
    | nil => simp at hi
    | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
          List.cons_append]
        congr 1
        exact ih i (by simpa using hi)
  let remap (k0 w u : ℕ) : ℕ := if u = k0 then w else if k0 < u then u - 1 else u
  have remap_lt : ∀ {k0 w u m : ℕ}, w < k0 → u < k0 + 1 + m → remap k0 w u < k0 + m := by
    intro k0 w u m hw hu
    dsimp only [remap]
    split_ifs <;> omega
  have remap_end : ∀ {k0 w t : ℕ}, remap k0 w (k0 + 1 + t) = k0 + t := by
    intro k0 w t
    dsimp only [remap]
    split_ifs <;> omega
  have gateEval_mono : ∀ {op : PEqualNP.CircuitLowerBounds.GateOp},
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ {xs ys : List Bool}, xs.length = ys.length →
      (∀ k < xs.length, xs.getD k false = true → ys.getD k false = true) →
      op.eval xs = true → op.eval ys = true := by
    intro op hop xs ys hlen hle
    rcases hop with rfl | rfl
    · change xs.all id = true → ys.all id = true
      simp only [List.all_eq_true, id_eq]
      intro h y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
      have hk' : k < xs.length := by omega
      have hys : ys[k] = ys.getD k false := by simp [List.getD_eq_getElem?_getD, hk]
      rw [hys]
      apply hle k hk'
      simpa [List.getD_eq_getElem?_getD, hk'] using h (xs[k]) (List.getElem_mem hk')
    · change xs.any id = true → ys.any id = true
      simp only [List.any_eq_true, id_eq]
      rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
      have hk' : k < ys.length := by omega
      refine ⟨ys[k], List.getElem_mem hk', ?_⟩
      have := hle k hk (by simpa [List.getD_eq_getElem?_getD, hk] using hkx)
      simpa [List.getD_eq_getElem?_getD, hk'] using this
  have foldl_wires_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
        init.length + gs.length := by
    intro gs init
    induction gs generalizing init with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have foldl_wires_take_eq : ∀ {gs : List PEqualNP.CircuitLowerBounds.Gate} {init : List Bool} {u : ℕ},
      u < init.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD u false =
        init.getD u false := by
    intro gs init u hu
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (by simp; omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hu]
  have getD_append_singleton_lt : ∀ {xs : List Bool} {b : Bool} {k : ℕ},
      k < xs.length → (xs ++ [b]).getD k false = xs.getD k false := by
    intro xs b k hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  have getD_append_singleton_eq : ∀ {xs : List Bool} {b : Bool},
      (xs ++ [b]).getD xs.length false = b := by
    intro xs b
    simp [List.getD_eq_getElem?_getD]
  have foldl_remap_eq : ∀ (k0 w : ℕ), w < k0 →
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (t : ℕ) (wC wD : List Bool),
      wC.length = k0 + 1 + t → wD.length = k0 + t →
      (∀ (j : ℕ), j < gs.length → ∀ u ∈ gs[j]!.inputs, u < k0 + 1 + t + j) →
      (∀ u < wC.length, wD.getD (remap k0 w u) false = wC.getD u false) →
      let wC' := gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wC
      let wD' := (gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        (⟨g.op, g.inputs.map (remap k0 w)⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
        (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wD
      ∀ u < wC'.length, wD'.getD (remap k0 w u) false = wC'.getD u false := by
    intro k0 w hw gs
    induction gs with
    | nil => intro t wC wD _ _ _ hinv; exact hinv
    | cons g gs ih =>
      intro t wC wD hlenC hlenD hrb hinv
      simp only [List.map_cons, List.foldl_cons]
      have hg_inputs : ∀ u ∈ g.inputs, u < wC.length := by
        intro u hu
        have := hrb 0 (by simp) u (by simpa using hu)
        omega
      have hbit : g.op.eval ((g.inputs.map (remap k0 w)).map fun i => wD.getD i false) =
          g.op.eval (g.inputs.map fun i => wC.getD i false) := by
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro u hu
        exact hinv u (hg_inputs u hu)
      let wC1 := wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)]
      let wD1 := wD ++ [g.op.eval ((g.inputs.map (remap k0 w)).map fun i => wD.getD i false)]
      have hinv1 : ∀ u < wC1.length, wD1.getD (remap k0 w u) false = wC1.getD u false := by
        intro u hu
        have hu' : u < wC.length + 1 := by simpa [wC1] using hu
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu') with hlt | rfl
        · have hlt_d : remap k0 w u < wD.length := by
            rw [hlenD]
            exact remap_lt hw (by omega)
          dsimp only [wC1, wD1]
          rw [getD_append_singleton_lt hlt, getD_append_singleton_lt hlt_d]
          exact hinv u hlt
        · have hidx_eq : remap k0 w wC.length = wD.length := by
            rw [hlenC, hlenD]
            exact remap_end
          dsimp only [wC1, wD1]
          rw [hidx_eq, getD_append_singleton_eq, getD_append_singleton_eq]
          exact hbit
      exact ih (t + 1) wC1 wD1 (by simp [wC1, hlenC]; omega) (by simp [wD1, hlenD]; omega)
        (fun j hj u hu => by
          have := hrb (j + 1) (Nat.succ_lt_succ hj) u (by simpa using hu)
          omega)
        hinv1
  have foldl_remap_mono : ∀ (k0 w : ℕ), w < k0 →
      ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      ∀ (t : ℕ) (wC wD : List Bool), wC.length = k0 + 1 + t → wD.length = k0 + t →
      (∀ (j : ℕ), j < gs.length → ∀ u ∈ gs[j]!.inputs, u < k0 + 1 + t + j) →
      (∀ u < wC.length, wC.getD u false = true → wD.getD (remap k0 w u) false = true) →
      let wC' := gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wC
      let wD' := (gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        (⟨g.op, g.inputs.map (remap k0 w)⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
        (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wD
      ∀ u < wC'.length, wC'.getD u false = true → wD'.getD (remap k0 w u) false = true := by
    intro k0 w hw gs
    induction gs with
    | nil => intro _ t wC wD _ _ _ hinv; exact hinv
    | cons g gs ih =>
      intro hao_gs t wC wD hlenC hlenD hrb hinv
      simp only [List.map_cons, List.foldl_cons]
      have hg_inputs : ∀ u ∈ g.inputs, u < wC.length := by
        intro u hu
        have := hrb 0 (by simp) u (by simpa using hu)
        omega
      have hbit : g.op.eval (g.inputs.map fun i => wC.getD i false) = true →
          g.op.eval ((g.inputs.map (remap k0 w)).map fun i => wD.getD i false) = true := by
        apply gateEval_mono (hao_gs g (by simp))
        · simp
        · intro k hk hxk
          have hlt_k : k < g.inputs.length := by simpa using hk
          have hu_mem : g.inputs[k] ∈ g.inputs := List.getElem_mem hlt_k
          have hrhs : ((g.inputs.map (remap k0 w)).map fun i => wD.getD i false).getD k false =
              wD.getD (remap k0 w (g.inputs[k])) false := by
            simp [List.getD_eq_getElem?_getD, hlt_k]
          rw [hrhs]
          apply hinv _ (hg_inputs _ hu_mem)
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt_k] at hxk
          simpa [List.getD_eq_getElem?_getD, hlt_k] using hxk
      let wC1 := wC ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)]
      let wD1 := wD ++ [g.op.eval ((g.inputs.map (remap k0 w)).map fun i => wD.getD i false)]
      apply ih (fun g' hg' => hao_gs g' (by simp [hg'])) (t + 1) wC1 wD1
        (by simp [wC1, hlenC]; omega) (by simp [wD1, hlenD]; omega)
        (fun j hj u hu => by
          have := hrb (j + 1) (Nat.succ_lt_succ hj) u (by simpa using hu)
          omega)
      intro u hu hu_true
      have hu' : u < wC.length + 1 := by simpa [wC1] using hu
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu') with hlt | rfl
      · have hlt_d : remap k0 w u < wD.length := by
          rw [hlenD]
          exact remap_lt hw (by omega)
        dsimp only [wD1]
        rw [getD_append_singleton_lt hlt_d]
        apply hinv u hlt
        dsimp only [wC1] at hu_true
        rwa [getD_append_singleton_lt hlt] at hu_true
      · have hidx_eq : remap k0 w wC.length = wD.length := by
          rw [hlenC, hlenD]
          exact remap_end
        dsimp only [wD1]
        rw [hidx_eq, getD_append_singleton_eq]
        apply hbit
        dsimp only [wC1] at hu_true
        rwa [getD_append_singleton_eq] at hu_true
  have hnoBelowDirect : ∀ i < C.gates.length,
      (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ w ∈ (gateAt C i).inputs,
        ¬ ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true →
          ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true := by
    intro i hi hand w hw hbelow
    have hbelow' : ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → F z = true := by
      intro z hz
      simp only [F, decide_eq_true_eq]
      exact hbelow z hz
    have hrb := hao.2.1
    have hlt_w : w < n + i := hrb i hi w hw
    have hlen2 : (gateAt C i).inputs.length = 2 := hao.2.2 (gateAt C i) (by
      rw [gateAt_eq_getElem hi]; exact List.getElem_mem hi)
    obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C i).inputs = [a, b] := by
      rcases hlist : (gateAt C i).inputs with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
      · simp [hlist] at hlen2
      · simp [hlist] at hlen2
      · exact ⟨x, y, rfl⟩
      · simp [hlist] at hlen2
    have hwab : w = a ∨ w = b := by simpa [hab] using hw
    let suff := C.gates.drop (i + 1)
    let pref := C.gates.take i
    let k0 := n + i
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨pref ++ suff.map (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        (⟨g.op, g.inputs.map (remap k0 w)⟩ : PEqualNP.CircuitLowerBounds.Gate)), remap k0 w C.output⟩
    have hD_ao2 : PEqualNP.TopForm.IsAO2 n D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hp | hs
        · exact hao.1 g (List.mem_of_mem_take hp)
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hs
          exact hao.1 g' (List.mem_of_mem_drop hg')
      · intro j hj u hu
        have hj' : j < pref.length + suff.length := by simpa [D] using hj
        have hplen : pref.length = i := List.length_take_of_le (Nat.le_of_lt hi)
        rw [gateAt_eq_getElem hj] at hu
        by_cases hjp : j < pref.length
        · have hgD : D.gates[j] = pref[j] := by simp [D, List.getElem_append_left hjp]
          rw [hgD] at hu
          have hgC : gateAt C j = pref[j] := by
            rw [gateAt_eq_getElem (by omega)]
            exact (List.getElem_take (h := hjp)).symm
          exact hrb j (by omega) u (by simpa [hgC] using hu)
        · have hjs : j - pref.length < suff.length := by omega
          have hgD : D.gates[j] =
              (⟨suff[j - pref.length].op, suff[j - pref.length].inputs.map (remap k0 w)⟩ :
                PEqualNP.CircuitLowerBounds.Gate) := by
            simp [D, List.getElem_append_right (Nat.le_of_not_lt hjp)]
          rw [hgD] at hu
          obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hu
          have hlt_C : i + 1 + (j - pref.length) < C.gates.length := by
            have : suff.length = C.gates.length - (i + 1) := List.length_drop
            omega
          have hsuff_eq : suff[j - pref.length] = C.gates[i + 1 + (j - pref.length)] := by simp [suff]
          have hu'_lt : u' < n + (i + 1 + (j - pref.length)) := by
            apply hrb (i + 1 + (j - pref.length)) hlt_C
            rw [gateAt_eq_getElem hlt_C, ← hsuff_eq]
            exact hu'
          have hremap : remap k0 w u' < k0 + (j - pref.length) := remap_lt hlt_w (by omega)
          omega
      · intro g hg
        rcases List.mem_append.mp hg with hp | hs
        · exact hao.2.2 g (List.mem_of_mem_take hp)
        · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hs
          simpa using hao.2.2 g' (List.mem_of_mem_drop hg')
    have hD_fun : ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D z = F z := by
      intro z
      have hCeq : PEqualNP.MetaComplexity.circuitFun n C z = F z := hfun' z
      have hsplit : C.gates = pref ++ [C.gates[i]] ++ suff := list_split_at C.gates i hi
      let wPref := pref.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn z)
      have hplen : pref.length = i := List.length_take_of_le (Nat.le_of_lt hi)
      have hlenPref : wPref.length = k0 := by
        rw [foldl_wires_length, List.length_ofFn, hplen]
      let gi := C.gates[i]
      have hgi_eq : gi = gateAt C i := (gateAt_eq_getElem hi).symm
      let wCi := wPref ++ [gi.op.eval (gi.inputs.map fun i => wPref.getD i false)]
      have hlenCi : wCi.length = k0 + 1 := by simp [wCi, hlenPref]
      have hC_wires : C.wires (List.ofFn z) =
          suff.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wCi := by
        change C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn z) = _
        nth_rw 1 [hsplit]
        rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hD_wires : D.wires (List.ofFn z) =
          (suff.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            (⟨g.op, g.inputs.map (remap k0 w)⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
            (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) wPref := by
        change D.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (List.ofFn z) = _
        dsimp only [D]
        rw [List.foldl_append]
      have hsuff_rb : ∀ (j : ℕ), j < suff.length → ∀ u ∈ suff[j]!.inputs, u < k0 + 1 + 0 + j := by
        intro j hj u hu
        have hlt_C : i + 1 + j < C.gates.length := by
          have : suff.length = C.gates.length - (i + 1) := List.length_drop
          omega
        have hidx_s : suff[j]! = C.gates[i + 1 + j] := by
          simp [suff, getElem!_pos suff j hj]
        have := hrb (i + 1 + j) hlt_C u (by rw [gateAt_eq_getElem hlt_C, ← hidx_s]; exact hu)
        omega
      have hsuff_ao : ∀ g ∈ suff, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
        intro g hg
        exact hao.1 g (List.mem_of_mem_drop hg)
      by_cases hFz : F z = true
      · have hCtrue : (C.wires (List.ofFn z)).getD C.output false = true := by
          simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, hFz] using hCeq
        by_cases hOut : C.output < (C.wires (List.ofFn z)).length
        · have hinv0 : ∀ u < wCi.length, wCi.getD u false = true →
              wPref.getD (remap k0 w u) false = true := by
            intro u hu hutrue
            have hu' : u < wPref.length + 1 := by simpa [wCi] using hu
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu') with hlt | rfl
            · have hlt' : u < k0 := by omega
              have hrem : remap k0 w u = u := by dsimp only [remap]; split_ifs <;> omega
              rw [hrem]
              dsimp only [wCi] at hutrue
              rwa [getD_append_singleton_lt hlt] at hutrue
            · have hrem : remap k0 w wPref.length = w := by
                rw [hlenPref]; dsimp only [remap]; split_ifs <;> omega
              rw [hrem]
              dsimp only [wCi] at hutrue
              rw [getD_append_singleton_eq, hgi_eq, hand, hab] at hutrue
              have hutrue' : (wPref.getD a false && wPref.getD b false) = true := by
                simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hutrue
              rw [Bool.and_eq_true] at hutrue'
              rcases hwab with rfl | rfl
              · exact hutrue'.1
              · exact hutrue'.2
          have hmono := foldl_remap_mono k0 w hlt_w suff hsuff_ao 0 wCi wPref
            (by omega) (by omega) hsuff_rb hinv0
          have hDtrue : (D.wires (List.ofFn z)).getD D.output false = true := by
            rw [hD_wires]
            apply hmono C.output (by rw [← hC_wires]; exact hOut)
            rw [← hC_wires]
            exact hCtrue
          simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, D, hFz] using hDtrue
        · exfalso
          have : (C.wires (List.ofFn z)).getD C.output false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hOut)]
            rfl
          rw [this] at hCtrue
          contradiction
      · have hFzFalse : F z = false := Bool.eq_false_iff.mpr hFz
        have hw_false : (C.wires (List.ofFn z)).getD w false = false := by
          cases hval : (C.wires (List.ofFn z)).getD w false
          · rfl
          · exact False.elim (by have := hbelow' z hval; rw [hFzFalse] at this; contradiction)
        have hwPref_w : wPref.getD w false = false := by
          rw [hC_wires] at hw_false
          have h1 := foldl_wires_take_eq (gs := suff) (init := wCi) (u := w) (by omega)
          have h2 : wCi.getD w false = wPref.getD w false := getD_append_singleton_lt (by omega)
          rw [h1, h2] at hw_false
          exact hw_false
        have hgi_false : gi.op.eval (gi.inputs.map fun idx => wPref.getD idx false) = false := by
          rw [hgi_eq, hand, hab]
          change (wPref.getD a false && (wPref.getD b false && true)) = false
          rcases hwab with rfl | rfl
          · rw [hwPref_w]; rfl
          · rw [hwPref_w]; simp
        have hinv0 : ∀ u < wCi.length, wPref.getD (remap k0 w u) false = wCi.getD u false := by
          intro u hu
          have hu' : u < wPref.length + 1 := by simpa [wCi] using hu
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu') with hlt | rfl
          · have hrem : remap k0 w u = u := by
              have : u < k0 := by omega
              dsimp only [remap]; split_ifs <;> omega
            dsimp only [wCi]
            rw [hrem, getD_append_singleton_lt hlt]
          · have hrem : remap k0 w wPref.length = w := by
              rw [hlenPref]; dsimp only [remap]; split_ifs <;> omega
            dsimp only [wCi]
            rw [hrem, hwPref_w, getD_append_singleton_eq]
            exact hgi_false.symm
        have heq_suff := foldl_remap_eq k0 w hlt_w suff 0 wCi wPref
          (by omega) (by omega) hsuff_rb hinv0
        have hCfalse : (C.wires (List.ofFn z)).getD C.output false = false := by
          simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, hFzFalse] using hCeq
        by_cases hOut : C.output < (C.wires (List.ofFn z)).length
        · have hDfalse : (D.wires (List.ofFn z)).getD D.output false = false := by
            rw [hD_wires, heq_suff C.output (by rw [← hC_wires]; exact hOut), ← hC_wires]
            exact hCfalse
          simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, D, hFzFalse] using hDfalse
        · have hOut_ge : (C.wires (List.ofFn z)).length ≤ C.output := Nat.le_of_not_lt hOut
          have hlenC_tot : (C.wires (List.ofFn z)).length = k0 + 1 + suff.length := by
            rw [hC_wires, foldl_wires_length, hlenCi]
          have hlenD_tot : (D.wires (List.ofFn z)).length = k0 + suff.length := by
            rw [hD_wires, foldl_wires_length, List.length_map, hlenPref]
          have hD_ge : (D.wires (List.ofFn z)).length ≤ D.output := by
            rw [hlenD_tot]
            change k0 + suff.length ≤ remap k0 w C.output
            dsimp only [remap]
            split_ifs <;> omega
          have hDfalse : (D.wires (List.ofFn z)).getD D.output false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hD_ge]
            rfl
          simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval, D, hFzFalse] using hDfalse
    have hle := hleast' D hD_ao2 hD_fun
    have hDsize : D.size + 1 = C.size := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size, D, List.length_append, List.length_map, pref, suff]
      rw [List.length_take_of_le (Nat.le_of_lt hi), List.length_drop]
      omega
    omega
  rcases hT_ex with ⟨T, hT_mem, hT_closed⟩
  have hT_feeds_T : ∀ i ∈ T, ∀ k' < C.gates.length,
      n + i ∈ (gateAt C k').inputs → k' ∈ T := by
    intro i hi k' hk' hmem
    rcases (hT_mem i hi).2.2 with hout | ⟨k, hk, huniq⟩
    · have hbelow_out : ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + i) false = true →
          ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true := by
        intro z hz
        have hFz := hfun z
        rw [hout] at hz
        change PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn z) = true at hz
        change PEqualNP.MetaComplexity.circuitFun n C z = _ at hFz
        unfold PEqualNP.MetaComplexity.circuitFun at hFz
        rw [hz] at hFz
        exact of_decide_eq_true hFz.symm
      rcases hao.1 (gateAt C k') (by
          rw [gateAt_eq_getElem hk']; exact List.getElem_mem hk') with hop | hop
      · exact False.elim (hnoBelowDirect k' hk' hop (n + i) hmem hbelow_out)
      · exact hT_closed (n + i) hbelow_out ⟨k', hk', hop, hmem⟩ k' hk' hmem
    · rw [(huniq k' hk').mp hmem]
      exact hk
  have orSets_take_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp [PEqualNP.CleanedNonEdge.orStep, ih]
  have orSets_take_getElem : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ),
      j < gs1.length →
      ((gs1 ++ gs2).foldl (PEqualNP.CleanedNonEdge.orStep n) [])[j]? =
        (gs1.foldl (PEqualNP.CleanedNonEdge.orStep n) [])[j]? := by
    intro gs1 gs2 j hj
    induction gs2 using List.reverseRecOn with
    | nil => simp
    | append_singleton gs2 g ih =>
      rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : ((gs1 ++ gs2).foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = (gs1 ++ gs2).length :=
        orSets_take_length (gs1 ++ gs2)
      dsimp only [PEqualNP.CleanedNonEdge.orStep]
      rw [List.getElem?_append_left (by simp; omega), ih]
  have orReaches_unfold : ∀ {w g : ℕ}, PEqualNP.CleanedNonEdge.OrReaches n C w g →
      n ≤ w ∧ w - n < C.gates.length ∧
        (w = n + g ∨
          ((gateAt C (w - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∃ u ∈ (gateAt C (w - n)).inputs, n ≤ u ∧ u < w ∧ PEqualNP.CleanedNonEdge.OrReaches n C u g)) := by
    intro w g h
    rcases h with ⟨hnw, hg⟩
    let hidx := w - n
    by_cases hlt : hidx < C.gates.length
    · have hsplit : C.gates = C.gates.take hidx ++ [C.gates[hidx]] ++ C.gates.drop (hidx + 1) :=
        list_split_at C.gates hidx hlt
      let cs0 := (C.gates.take hidx).foldl (PEqualNP.CleanedNonEdge.orStep n) []
      have hcs0_len : cs0.length = hidx := by
        rw [orSets_take_length, List.length_take_of_le (Nat.le_of_lt hlt)]
      have hget : (PEqualNP.CleanedNonEdge.orSets n C).getD hidx [] =
          (PEqualNP.CleanedNonEdge.orStep n cs0 C.gates[hidx]).getD hidx [] := by
        change (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD hidx [] = _
        nth_rw 1 [hsplit]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        have hlen1 : hidx < (C.gates.take hidx ++ [C.gates[hidx]]).length := by
          rw [List.length_append, List.length_take_of_le (Nat.le_of_lt hlt), List.length_singleton]
          omega
        have h1 := orSets_take_getElem (C.gates.take hidx ++ [C.gates[hidx]]) (C.gates.drop (hidx + 1)) hidx hlen1
        rw [h1, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hget] at hg
      dsimp only [PEqualNP.CleanedNonEdge.orStep] at hg
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hcs0_len, Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some] at hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · refine ⟨hnw, hlt, Or.inl ?_⟩
        omega
      · split_ifs at hg' with hop
        · obtain ⟨u, hu_filt, hu_mem⟩ := List.mem_flatMap.mp hg'
          obtain ⟨hu_in, hu_dec⟩ := List.mem_filter.mp hu_filt
          simp only [decide_eq_true_eq] at hu_dec
          have hgate_eq : gateAt C hidx = C.gates[hidx] := gateAt_eq_getElem hlt
          refine ⟨hnw, hlt, Or.inr ⟨by rw [hgate_eq]; exact hop, u, by rw [hgate_eq]; exact hu_in,
            hu_dec.1, by omega, hu_dec.1, ?_⟩⟩
          have hget_u : (PEqualNP.CleanedNonEdge.orSets n C).getD (u - n) [] = cs0.getD (u - n) [] := by
            change (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (u - n) [] = _
            nth_rw 1 [hsplit]
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
            have hu_sub : u - n < (C.gates.take hidx).length := by
              rw [List.length_take_of_le (Nat.le_of_lt hlt)]
              omega
            have h2 := orSets_take_getElem (C.gates.take hidx) ([C.gates[hidx]] ++ C.gates.drop (hidx + 1)) (u - n) hu_sub
            simpa [cs0, List.append_assoc] using congrArg (fun o : Option (List ℕ) => o.getD []) h2
          rw [hget_u]
          exact hu_mem
        · simp at hg'
    · have hlen : (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := orSets_take_length C.gates
      have : (PEqualNP.CleanedNonEdge.orSets n C).getD hidx [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [this] at hg
      simp at hg
  have hOrReaches_belowF : ∀ w g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g →
      (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + g) false = true →
        ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) →
      (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true →
        ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) ∨
      ∃ h ∈ T, w = n + h := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro g hreach hbg
      rcases orReaches_unfold hreach with ⟨hnw, hlt, rfl | ⟨hop, u, hu_in, hnu, hu_lt, hu_reach⟩⟩
      · exact Or.inl hbg
      · rcases ih u hu_lt g hu_reach hbg with hbu | ⟨h, hhT, rfl⟩
        · exact Or.inr ⟨w - n, hT_closed u hbu ⟨w - n, hlt, hop, hu_in⟩ (w - n) hlt hu_in, by omega⟩
        · exact Or.inr ⟨w - n, hT_feeds_T h hhT (w - n) hlt hu_in, by omega⟩
  have hnoBelowOr : ∀ i < C.gates.length,
      (gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ w ∈ (gateAt C i).inputs,
        (¬ ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) ∧
        ∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g →
          ¬ ∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD (n + g) false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true := by
    intro i hi hand w hw
    refine ⟨hnoBelowDirect i hi hand w hw, fun g hreach hbg => ?_⟩
    rcases hOrReaches_belowF w g hreach hbg with hbw | ⟨h, hhT, rfl⟩
    · exact hnoBelowDirect i hi hand w hw hbw
    · have hiT := hT_feeds_T h hhT i hi hw
      have hop := (hT_mem i hiT).2.1
      rw [hand] at hop
      contradiction
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hand
    have h1 := hnoBelowOr i hi hand
    have h2 := sub2 Np Nl I C hnoC4 hao hfun hleast ⟨T, hT_mem, hT_closed⟩ P L hP_iff hL_iff i hi hand
      (fun j hj hjand => ih j hj (Nat.lt_trans hj hi) hjand) h1
    apply sub1 Np Nl I C hnoC4 hao hfun hleast ⟨T, hT_mem, hT_closed⟩ P L hP_iff hL_iff i hi hand
    intro w hw
    exact ⟨(h1 w hw).1, fun g hrg => ⟨(h1 w hw).2 g hrg, h2 w hw g hrg⟩⟩
