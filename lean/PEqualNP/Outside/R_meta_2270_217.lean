import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2270_217
    (h_read1 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        ¬x2.Colorable (2 : ℕ) →
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
        (∃ (u v : Fin x1), u ∉ x3 ∧ v ∉ x3 ∧ x2.Adj u v ∧
          (x5.output :: x5.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count u.val = (1 : ℕ)) →
        ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧
          ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x5.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15)
    (h_read22 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        ¬x2.Colorable (2 : ℕ) →
        (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
        (∃ (u v : Fin x1), u ∉ x3 ∧ v ∉ x3 ∧ x2.Adj u v ∧
          (x5.output :: x5.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count u.val = (2 : ℕ) ∧
          (x5.output :: x5.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).count v.val = (2 : ℕ)) →
        ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧
          ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x5.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → ∃ (x13 : Fin x1) (x14 : Fin x1), x13 ∉ x3 ∧ x14 ∉ x3 ∧ x2.Adj x13 x14 ∧ ∃ (x15 : ℕ), x15 + (7 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x4 (Function.update (Function.update x16 x13 Bool.false) x14 Bool.false)) x15 := by
  classical
  intro n G A f hnonbip hdeg hgirth hc hE hf s hs
  let m : ℕ := Nat.find (⟨s, hs⟩ : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t)
  have hm : PEqualNP.MetaComplexity.HasCircuitSize n f m := Nat.find_spec (⟨s, hs⟩ : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t)
  have hms : m ≤ s := Nat.find_min' (⟨s, hs⟩ : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t) hs
  have hmin_m : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize n f t → m ≤ t :=
    fun t ht => Nat.find_min' (⟨s, hs⟩ : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t) ht
  rcases hm with ⟨C, hfan, hCm, hCev⟩
  have hCfun : PEqualNP.MetaComplexity.circuitFun n C = f := funext hCev
  have hCsize_eq : C.size = m := by
    have hge : m ≤ C.size := hmin_m C.size ⟨C, hfan, le_rfl, hCev⟩
    omega
  have hCs : C.size ≤ s := by omega
  have hmin : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize n f t → C.size ≤ t := by
    intro t ht; have := hmin_m t ht; omega
  have hCmin : PEqualNP.MetaComplexity.IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro D hD hDf
    have hDe : ∀ x, D.eval (List.ofFn x) = f x := fun x => by
      have := congrFun (hDf.trans hCfun) x
      exact this
    exact hmin D.size ⟨D, hD, le_rfl, hDe⟩
  let wiresFrom : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
    fun gs w => gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have wiresFrom_append : ∀ (gs₁ gs₂ : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    intro gs₁ gs₂ w
    exact List.foldl_append
  have wiresFrom_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wiresFrom]
    | cons g gs ih =>
      intro w
      change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = w.length + (gs.length + 1)
      rw [ih]; simp; omega
  have getD_snoc_lt : ∀ (l : List Bool) (x : Bool) (i : ℕ), i < l.length →
      (l ++ [x]).getD i false = l.getD i false := by
    intro l x i hi
    simp [List.getD, List.getElem?_append_left hi]
  have getD_snoc_eq : ∀ (l : List Bool) (x : Bool) (i : ℕ), i = l.length →
      (l ++ [x]).getD i false = x := by
    intro l x i hi
    subst hi; simp [List.getD]
  have wiresFrom_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false = w.getD i false
      rw [ih _ i (by simp; omega), getD_snoc_lt _ _ _ hi]
  have wiresFrom_agree : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (B : Set ℕ) (w₁ w₂ : List Bool),
      w₁.length = w₂.length → (∀ b ∈ B, b < w₁.length) →
      (∀ i ∉ B, w₁.getD i false = w₂.getD i false) →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) →
      (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
      ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    intro gs
    induction gs with
    | nil => intro B w₁ w₂ hlen _ hagree _; exact ⟨hlen, hagree⟩
    | cons g gs ih =>
      intro B w₁ w₂ hlen hB hagree hread
      change (wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).length =
          (wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)])).length ∧
        ∀ i ∉ B, (wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).getD i false =
          (wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)])).getD i false
      have hmap : (g.inputs.map fun i => w₁.getD i false) = (g.inputs.map fun i => w₂.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hagree i (hread g List.mem_cons_self i hi)
      rw [hmap]
      apply ih B
      · simp [hlen]
      · intro b hb; simp; have := hB b hb; omega
      · intro i hi
        by_cases hlt : i < w₁.length
        · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]; exact hagree i hi
        · by_cases heq : i = w₁.length
          · rw [getD_snoc_eq _ _ _ heq, getD_snoc_eq _ _ _ (by omega)]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro g' hg'; exact hread g' (List.mem_cons_of_mem _ hg')
  let OkGate : PEqualNP.CircuitLowerBounds.Gate → Prop :=
    fun g => g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2
  let substWire : ℕ → ℕ → ℕ := fun k i => if i < k then i else if i = k then 0 else i - 1
  let substGate : ℕ → PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun k g => ⟨g.op, g.inputs.map (substWire k)⟩
  let deleteGate : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Circuit :=
    fun D j => ⟨D.gates.take j ++ (D.gates.drop (j + 1)).map (substGate (n + j)), substWire (n + j) D.output⟩
  have deleteDeadGate : ∀ (j : ℕ) (hj : j < C.gates.length),
      C.output ≠ n + j →
      (∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (n + j) ∉ C.gates[j'].inputs) →
      PEqualNP.MetaComplexity.HasCircuitSize n f (C.gates.length - 1) := by
    intro j hj hout hno
    let D := deleteGate C j
    have hDok : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with h1 | h1
      · exact hfan g (List.mem_of_mem_take h1)
      · rcases List.mem_map.mp h1 with ⟨g0, hg0, rfl⟩
        have h0 := hfan g0 (List.mem_of_mem_drop hg0)
        exact ⟨h0.1, by simp [substGate]; exact h0.2⟩
    have hDlen : D.gates.length = C.gates.length - 1 := by
      simp only [D, deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    refine ⟨D, hDok, by change D.gates.length ≤ C.gates.length - 1; omega, ?_⟩
    intro x
    rw [← hCev x]
    change (wiresFrom D.gates (List.ofFn x)).getD (substWire (n + j) C.output) false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
        have h1 := List.take_append_drop j C.gates
        have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
        rw [h2] at h1
        simpa only [List.append_assoc, List.singleton_append] using h1.symm
      set w₂ := wiresFrom (C.gates.take j) (List.ofFn x) with hw₂
      set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
      have hw₂_len : w₂.length = n + j := by
        rw [hw₂, wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
      have hw₁_len : w₁.length = n + j + 1 := by
        rw [hw₁, wiresFrom_length, hw₂_len]; simp
      have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (n + j) ∉ g.inputs := by
        intro g hg
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
        rw [List.getElem_drop]
        exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
      have haux : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w₁' w₂' : List Bool),
          w₁'.length = w₂'.length + 1 → n + j ≤ w₂'.length →
          (∀ g ∈ gs, (n + j) ∉ g.inputs) →
          (∀ i < w₁'.length, i ≠ n + j → w₂'.getD (substWire (n + j) i) false = w₁'.getD i false) →
          ∀ i < (wiresFrom gs w₁').length, i ≠ n + j →
            (wiresFrom (gs.map (substGate (n + j))) w₂').getD (substWire (n + j) i) false =
              (wiresFrom gs w₁').getD i false := by
        intro gs
        induction gs with
        | nil => intro w₁' w₂' _ _ _ hag i hi hne; exact hag i hi hne
        | cons g rest ih =>
          intro w₁' w₂' hlen' hk' hnod hag'
          rw [List.map_cons]
          change ∀ i < (wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)])).length, i ≠ n + j →
            (wiresFrom (rest.map (substGate (n + j))) (w₂' ++ [(substGate (n + j) g).op.eval ((substGate (n + j) g).inputs.map fun i => w₂'.getD i false)])).getD (substWire (n + j) i) false =
            (wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)])).getD i false
          have hmap : ((substGate (n + j) g).inputs.map fun i => w₂'.getD i false) =
              (g.inputs.map fun i => w₁'.getD i false) := by
            simp only [substGate, List.map_map]
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply]
            have hne : i ≠ n + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
            by_cases hlt' : i < w₁'.length
            · exact hag' i hlt' hne
            · have hge : w₂'.length ≤ substWire (n + j) i := by
                dsimp only [substWire]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
          change ∀ i < (wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)])).length, i ≠ n + j →
            (wiresFrom (rest.map (substGate (n + j))) (w₂' ++ [g.op.eval ((substGate (n + j) g).inputs.map fun i => w₂'.getD i false)])).getD (substWire (n + j) i) false =
            (wiresFrom rest (w₁' ++ [g.op.eval (g.inputs.map fun i => w₁'.getD i false)])).getD i false
          rw [hmap]
          apply ih _ _ (by simp [hlen']) (by simp; omega)
            (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
          intro i hi hne
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hlt' : i < w₁'.length
          · have hsublt : substWire (n + j) i < w₂'.length := by
              dsimp only [substWire]; split_ifs <;> omega
            rw [getD_snoc_lt _ _ _ hsublt, getD_snoc_lt _ _ _ hlt']
            exact hag' i hlt' hne
          · have hieq : i = w₁'.length := by omega
            have hsubeq : substWire (n + j) i = w₂'.length := by
              dsimp only [substWire]; split_ifs <;> omega
            rw [getD_snoc_eq _ _ _ hsubeq, getD_snoc_eq _ _ _ hieq]
      change (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (n + j))) (List.ofFn x)).getD (substWire (n + j) C.output) false = _
      rw [wiresFrom_append, ← hw₂]
      conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
      have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = n + C.gates.length := by
        rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
      apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ C.output (by omega) hout
      intro u hu hune
      have hult : u < n + j := by omega
      have hsw : substWire (n + j) u = u := by dsimp only [substWire]; split_ifs <;> omega
      rw [hsw]
      change w₂.getD u false = (w₂ ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w₂.getD i false)]).getD u false
      rw [getD_snoc_lt _ _ _ (by omega)]
    · have hge1 : D.gates.length + n ≤ substWire (n + j) C.output := by
        rw [hDlen]; dsimp only [substWire]; split_ifs <;> omega
      have h1 : (wiresFrom D.gates (List.ofFn x)).length = n + D.gates.length := by
        rw [wiresFrom_length, List.length_ofFn]
      have h2 : (wiresFrom C.gates (List.ofFn x)).length = n + C.gates.length := by
        rw [wiresFrom_length, List.length_ofFn]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  let Bld : ((Fin n → Bool) → Bool) → ℕ → Prop := fun F b =>
    ∀ k, n ≤ k → ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
      (∀ g ∈ gs, OkGate g) ∧ gs.length ≤ b ∧ out < k + gs.length ∧
      ∀ w : List Bool, w.length = k → (wiresFrom gs w).getD out false = F (fun i => w.getD i false)
  have bld_cast (F H : (Fin n → Bool) → Bool) (b b' : ℕ) (h : Bld F b) (hle : b ≤ b') (he : ∀ x, F x = H x) : Bld H b' := by
    intro k hk
    rcases h k hk with ⟨gs, out, hok, hl, ho, hev⟩
    exact ⟨gs, out, hok, le_trans hl hle, ho, fun w hw => by rw [hev w hw, he]⟩
  have bld_var (i : Fin n) : Bld (fun x => x i) 0 := by
    intro k hk
    exact ⟨[], i.val, by simp, le_rfl, by simp; omega, fun w _ => rfl⟩
  have bld_bin (op : PEqualNP.CircuitLowerBounds.GateOp)
      (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
      (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
      (F H : (Fin n → Bool) → Bool) (b1 b2 : ℕ) (h1 : Bld F b1) (h2 : Bld H b2) :
      Bld (fun x => c (F x) (H x)) (b1 + b2 + 1) := by
    intro k hk
    rcases h1 k hk with ⟨gs1, o1, ok1, l1, ho1, ev1⟩
    rcases h2 (k + gs1.length) (by omega) with ⟨gs2, o2, ok2, l2, ho2, ev2⟩
    refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], k + gs1.length + gs2.length, ?_, by simp; omega, by simp; omega, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with (hg | hg) | rfl
      · exact ok1 g hg
      · exact ok2 g hg
      · rcases hop with rfl | rfl <;> exact ⟨by simp, by simp⟩
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set v := wiresFrom gs1 w with hv
      have lv : v.length = k + gs1.length := by rw [hv, wiresFrom_length, hw]
      set u := wiresFrom gs2 v with hu
      have lu : u.length = k + gs1.length + gs2.length := by rw [hu, wiresFrom_length, lv]
      have step_eq : wiresFrom [⟨op, [o1, o2]⟩] u = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
      rw [step_eq, getD_snoc_eq _ _ _ lu.symm]
      simp only [List.map_cons, List.map_nil, hc]
      have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
        rw [hu, wiresFrom_prefix _ _ _ (by omega), hv, ev1 w hw]
      have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
        rw [hu, ev2 v lv]
        congr 1; funext i
        rw [hv, wiresFrom_prefix _ _ _ (by have := i.isLt; omega)]
      rw [e1, e2]
  have bld_or (F H : (Fin n → Bool) → Bool) (b1 b2 : ℕ) (h1 : Bld F b1) (h2 : Bld H b2) :
      Bld (fun x => F x || H x) (b1 + b2 + 1) :=
    bld_bin PEqualNP.CircuitLowerBounds.GateOp.or (Or.inr rfl) (· || ·) (fun a b => by cases a <;> cases b <;> rfl) F H b1 b2 h1 h2
  have bld_and (F H : (Fin n → Bool) → Bool) (b1 b2 : ℕ) (h1 : Bld F b1) (h2 : Bld H b2) :
      Bld (fun x => F x && H x) (b1 + b2 + 1) :=
    bld_bin PEqualNP.CircuitLowerBounds.GateOp.and (Or.inl rfl) (· && ·) (fun a b => by cases a <;> cases b <;> rfl) F H b1 b2 h1 h2
  have bld_anyList : ∀ (vs : List (Fin n)) (v : Fin n),
      Bld (fun x => (v :: vs).any fun j => x j) vs.length := by
    intro vs
    induction vs with
    | nil =>
      intro v
      exact bld_cast (fun x => x v) (fun x => ([v]).any fun j => x j) 0 0 (bld_var v) le_rfl (fun x => by simp)
    | cons w ws ih =>
      intro v
      exact bld_cast (fun x => x v || (w :: ws).any fun j => x j) (fun x => (v :: w :: ws).any fun j => x j)
        (0 + ws.length + 1) (w :: ws).length
        (bld_or (fun x => x v) (fun x => (w :: ws).any fun j => x j) 0 ws.length (bld_var v) (ih w))
        (by simp) (fun x => by simp)
  have bld_anyFinset : ∀ (S : Finset (Fin n)), S.Nonempty →
      Bld (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
    intro S hS
    obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
      cases h : S.toList with
      | nil => simp at h; exact absurd h hS.ne_empty
      | cons v vs => exact ⟨v, vs, rfl⟩
    have hcS : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
    refine bld_cast (fun x => (v :: vs).any fun j => x j) (fun x => decide (∃ v ∈ S, x v = true))
      vs.length (S.card - 1) (bld_anyList vs v) (by omega) ?_
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
    simp
  have bld_edges : ∀ (T : Finset (Fin n)) (E : Finset (Sym2 (Fin n))), E.Nonempty →
      (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
      Bld (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro E hE hcov
      obtain ⟨e, he⟩ := hE
      obtain ⟨t, ht, _⟩ := hcov e he
      simp at ht
    | @insert t T0 htT ih =>
      intro E hE hcov
      set E1 := E.filter (fun e => t ∈ e) with hE1
      set E2 := E.filter (fun e => t ∉ e) with hE2
      have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
      have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
      have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
        intro e he
        rw [hE2, Finset.mem_filter] at he
        obtain ⟨t', ht', hte⟩ := hcov e he.1
        rcases Finset.mem_insert.mp ht' with rfl | h
        · exact absurd hte he.2
        · exact ⟨t', h, hte⟩
      set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
      have hSc : S.card ≤ E1.card := by
        refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
        · intro v hv
          simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
          exact hv
        · intro a _ b _ hab; exact Sym2.congr_right.mp hab
      have star : E1.Nonempty → Bld (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true)) E1.card := by
        intro h1
        have hSne : S.Nonempty := by
          obtain ⟨e, he⟩ := h1
          have he' := he; rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp he'.2
          exact ⟨b, by simp [hS, ← hb, he]⟩
        have hpos := hSne.card_pos
        refine bld_cast (fun x => x t && decide (∃ v ∈ S, x v = true))
          (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
          (0 + (S.card - 1) + 1) E1.card
          (bld_and (fun x => x t) (fun x => decide (∃ v ∈ S, x v = true)) 0 (S.card - 1)
            (bld_var t) (bld_anyFinset S hSne))
          (by omega) ?_
        intro x
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨htx, v, hv, hxv⟩
          refine ⟨s(t, v), (Finset.mem_filter.mp hv).2, ?_⟩
          intro u hu; rcases Sym2.mem_iff.mp hu with rfl | rfl <;> assumption
        · rintro ⟨e, he, hall⟩
          have he' := he; rw [hE1, Finset.mem_filter] at he'
          obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp he'.2
          subst hb
          exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he], hall b (Sym2.mem_mk_right _ _)⟩
      have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true) =
          (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
        intro x
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
        constructor
        · rintro ⟨e, he, h⟩
          by_cases hte : t ∈ e
          · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
          · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
        · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
      rw [hcard]
      by_cases h1 : E1.Nonempty
      · by_cases h2 : E2.Nonempty
        · have hp := h2.card_pos
          exact bld_cast
            (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
            (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
            (E1.card + (E2.card + T0.card - 1) + 1) (E.card + (T0.card + 1) - 1)
            (bld_or (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
              (fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
              E1.card (E2.card + T0.card - 1) (star h1) (ih E2 h2 c2))
            (by omega) (fun x => (key x).symm)
        · rw [Finset.not_nonempty_iff_eq_empty] at h2
          exact bld_cast
            (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
            (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
            E1.card (E.card + (T0.card + 1) - 1)
            (star h1) (by omega) (fun x => by rw [key, h2]; simp)
      · rw [Finset.not_nonempty_iff_eq_empty] at h1
        have h2 : E2.Nonempty := by
          by_contra h2
          rw [Finset.not_nonempty_iff_eq_empty] at h2
          have := hE.card_pos; rw [h1, h2] at hsplit; simp at hsplit; omega
        exact bld_cast
          (fun x => decide (∃ e ∈ E2, ∀ v ∈ e, x v = true))
          (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true))
          (E2.card + T0.card - 1) (E.card + (T0.card + 1) - 1)
          (ih E2 h2 c2) (by omega) (fun x => by rw [key, h1]; simp)
  rcases hE with ⟨w0, w1, hw01⟩
  have hw0_mem : w0 ∈ Aᶜ := Finset.mem_compl.mpr (hc w0 w1 hw01)
  have hw1_mem : w1 ∈ Aᶜ := Finset.mem_compl.mpr (hc w1 w0 hw01.symm)
  have hw01_ne : w0 ≠ w1 := G.ne_of_adj hw01
  have hAc_ge2 : 2 ≤ Aᶜ.card := by
    have hsub : ({w0, w1} : Finset (Fin n)) ⊆ Aᶜ := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hc2 : ({w0, w1} : Finset (Fin n)).card = 2 := Finset.card_pair hw01_ne
    have := Finset.card_le_card hsub
    omega
  let T : Finset (Fin n) := Aᶜ.erase w0
  have hTcard : T.card = Aᶜ.card - 1 := Finset.card_erase_of_mem hw0_mem
  have hEne : G.edgeFinset.Nonempty := ⟨s(w0, w1), by simpa using hw01⟩
  have hEpos : 0 < G.edgeFinset.card := hEne.card_pos
  have hTcov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b he => ?_) e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have ha : a ∈ Aᶜ := Finset.mem_compl.mpr (hc a b he)
    have hb : b ∈ Aᶜ := Finset.mem_compl.mpr (hc b a he.symm)
    by_cases haw : a = w0
    · subst haw
      have hbw : b ≠ a := (G.ne_of_adj he).symm
      exact ⟨b, Finset.mem_erase.mpr ⟨hbw, hb⟩, Sym2.mem_mk_right _ _⟩
    · exact ⟨a, Finset.mem_erase.mpr ⟨haw, ha⟩, Sym2.mem_mk_left _ _⟩
  have hbld_G : Bld (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 1) := by
    refine bld_cast
      (fun x : Fin n → Bool => decide (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true))
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 1) (G.edgeFinset.card + T.card - 1)
      (bld_edges T G.edgeFinset hEne hTcov) le_rfl ?_
    intro x
    rw [decide_eq_decide]
    constructor
    · rintro ⟨e, he, h⟩
      revert he h
      refine Sym2.ind (fun a b he h => ?_) e
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨s(i, j), by simpa using hij, ?_⟩
      intro v hv; rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  have hbld_f : Bld f (A.card + G.edgeFinset.card + Aᶜ.card - 2) := by
    by_cases ha : A.Nonempty
    · have hap := ha.card_pos
      refine bld_cast
        (fun x : Fin n → Bool => decide (∃ v ∈ A, x v = true) || decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
        f ((A.card - 1) + (G.edgeFinset.card + T.card - 1) + 1) (A.card + G.edgeFinset.card + Aᶜ.card - 2)
        (bld_or (fun x : Fin n → Bool => decide (∃ v ∈ A, x v = true))
          (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
          (A.card - 1) (G.edgeFinset.card + T.card - 1) (bld_anyFinset A ha) hbld_G)
        (by omega) ?_
      intro x; rw [Bool.eq_iff_iff, hf]; simp
    · have hae := Finset.not_nonempty_iff_eq_empty.mp ha
      have hA0 : A.card = 0 := by rw [hae]; rfl
      refine bld_cast
        (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
        f (G.edgeFinset.card + T.card - 1) (A.card + G.edgeFinset.card + Aᶜ.card - 2)
        hbld_G (by omega) ?_
      intro x; rw [Bool.eq_iff_iff, hf]; simp [hae]
  have hub_has : PEqualNP.MetaComplexity.HasCircuitSize n f (A.card + G.edgeFinset.card + Aᶜ.card - 2) := by
    rcases hbld_f n le_rfl with ⟨gs, out, hok, hlen, _, hev⟩
    refine ⟨⟨gs, out⟩, hok, hlen, ?_⟩
    intro x
    have e := hev (List.ofFn x) (by simp)
    change (wiresFrom gs (List.ofFn x)).getD out false = f x
    rw [e]; congr 1; funext i; simp
  have hub : C.size ≤ A.card + G.edgeFinset.card + Aᶜ.card - 2 := hmin _ hub_has
  let slots : List ℕ := C.output :: C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
  let cnt : ℕ → ℕ := fun i => slots.count i
  have essentialSlot : ∀ (a : Fin n),
      (∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ f x ≠ f y) → (a : ℕ) ∈ slots := by
    intro a hdep
    rcases hdep with ⟨x, y, hagree, hne⟩
    by_contra hn
    have hout : C.output ≠ (a : ℕ) := fun he => hn (by simp [slots, he])
    have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({(a : ℕ)} : Set ℕ) := by
      intro g hg i hi hia
      have hi' : i = (a : ℕ) := hia
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi' ▸ hi⟩))
    apply hne
    rw [← hCev x, ← hCev y]
    apply (wiresFrom_agree C.gates ({(a : ℕ)} : Set ℕ) (List.ofFn x) (List.ofFn y)
      (by simp) (by simp) ?_ noRead).2 C.output hout
    intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem _ _ (by simp; exact hlt), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simp; exact hlt), List.getElem_ofFn]
      exact hagree ⟨i, hlt⟩ (fun he => hi (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have marked : ∀ a ∈ A, 1 ≤ cnt a := by
    intro a ha
    apply List.count_pos_iff.mpr
    apply essentialSlot a
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a)
    refine ⟨z, y, fun i hi => by simp [z, y, hi], ?_⟩
    have hz : f z ≠ true := by simp [hf, z]
    have hy : f y = true := (hf y).mpr (Or.inl ⟨a, ha, by simp [y]⟩)
    exact fun eq => hz (eq.trans hy)
  have unmarked : ∀ v ∈ Aᶜ, 1 ≤ cnt v := by
    intro v hv
    have hvA : v ∉ A := Finset.mem_compl.mp hv
    have hcard3 : (G.neighborSet v).ncard = 3 := hdeg v hvA
    have hne : (G.neighborSet v).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    rcases hne with ⟨w, hw⟩
    have hvw : G.Adj v w := hw
    have hwA : w ∉ A := hc w v hvw.symm
    apply List.count_pos_iff.mpr
    apply essentialSlot v
    let z : Fin n → Bool := fun i => decide (i = w)
    let y : Fin n → Bool := fun i => decide (i = w ∨ i = v)
    refine ⟨z, y, fun i hi => by simp [z, y, hi], ?_⟩
    have hz : f z ≠ true := by
      intro hzt
      rcases (hf z).mp hzt with ⟨a, ha, hza⟩ | ⟨p, q, hpq, hzp, hzq⟩
      · have : a = w := by simpa [z] using hza
        subst this; exact hwA ha
      · have hp : p = w := by simpa [z] using hzp
        have hq : q = w := by simpa [z] using hzq
        subst hp; subst hq; exact G.ne_of_adj hpq rfl
    have hy : f y = true := (hf y).mpr (Or.inr ⟨v, w, hvw, by simp [y], by simp [y]⟩)
    exact fun eq => hz (eq.trans hy)
  have internal : ∀ i ∈ Finset.range C.gates.length, 1 ≤ cnt (n + i) := by
    intro i hi
    have hil : i < C.gates.length := Finset.mem_range.mp hi
    apply List.count_pos_iff.mpr
    by_contra hn
    have hout : C.output ≠ n + i := fun e => hn (by simp [slots, e])
    have hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → i < j' → n + i ∉ C.gates[j'].inputs := by
      intro j' hj' _ hm'
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hj', hm'⟩))
    have bad := hmin _ (deleteDeadGate i hil hout hno)
    change C.gates.length ≤ C.gates.length - 1 at bad
    omega
  have countBound : ∀ (xs : List ℕ) (S : Finset ℕ), ∑ i ∈ S, xs.count i ≤ xs.length := by
    intro xs
    induction xs with
    | nil => intro S; simp
    | cons a xs ih =>
      intro S
      simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
      have h1 := ih S
      by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega
  have gateSlotBound : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.length ≤ 2) → (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g tail ih =>
      intro h
      have hg := h g List.mem_cons_self
      have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have lowerA := Finset.sum_le_sum marked
  have lowerI := Finset.sum_le_sum internal
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerA lowerI
  have inSum := A.sum_add_sum_compl (fun a : Fin n => cnt a.val)
  rw [Fin.sum_univ_eq_sum_range] at inSum
  have countAll := countBound slots (Finset.range (n + C.gates.length))
  change ∑ i ∈ Finset.range (n + C.gates.length), cnt i ≤ slots.length at countAll
  rw [Finset.sum_range_add] at countAll
  have hlen := gateSlotBound C.gates (fun g hg => (hfan g hg).2)
  simp only [slots, List.length_cons] at countAll
  have dA : ∀ a ∈ A, G.degree a = 0 := by
    intro a ha
    exact (G.degree_eq_zero a).mpr (fun j h => hc a j h ha)
  have dB : ∀ a ∈ Aᶜ, G.degree a = 3 := by
    intro a ha
    rw [← G.ncard_neighborSet]
    exact hdeg a (Finset.mem_compl.mp ha)
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
  have hsumB : ∑ v ∈ Aᶜ, cnt v.val ≤ G.edgeFinset.card + Aᶜ.card - 1 := by
    change C.gates.length ≤ _ at hub
    omega
  have hex_edge : ∃ u ∈ Aᶜ, ∃ v ∈ G.neighborFinset u, cnt u.val + cnt v.val ≤ 4 := by
    by_contra hall
    push Not at hall
    have hge5 : ∀ u ∈ Aᶜ, 5 * 3 ≤ ∑ v ∈ G.neighborFinset u, (cnt u.val + cnt v.val) := by
      intro u hu
      have h1 : ∑ _v ∈ G.neighborFinset u, 5 ≤ ∑ v ∈ G.neighborFinset u, (cnt u.val + cnt v.val) :=
        Finset.sum_le_sum (fun v hv => hall u hu v hv)
      simp only [Finset.sum_const, smul_eq_mul] at h1
      have hdu : (G.neighborFinset u).card = 3 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using dB u hu
      rw [hdu] at h1
      omega
    have hlow : 15 * Aᶜ.card ≤ ∑ u ∈ Aᶜ, ∑ v ∈ G.neighborFinset u, (cnt u.val + cnt v.val) := by
      have h1 := Finset.sum_le_sum hge5
      simp only [Finset.sum_const, smul_eq_mul] at h1
      omega
    have hsplit_sum : ∑ u ∈ Aᶜ, ∑ v ∈ G.neighborFinset u, (cnt u.val + cnt v.val) =
        (∑ u ∈ Aᶜ, ∑ _v ∈ G.neighborFinset u, cnt u.val) +
        (∑ u ∈ Aᶜ, ∑ v ∈ G.neighborFinset u, cnt v.val) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_add_distrib
    have hpart1 : ∑ u ∈ Aᶜ, ∑ _v ∈ G.neighborFinset u, cnt u.val = 3 * ∑ u ∈ Aᶜ, cnt u.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Finset.sum_const, smul_eq_mul]
      have hdu : (G.neighborFinset u).card = 3 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using dB u hu
      rw [hdu]
    have hpart2 : ∑ u ∈ Aᶜ, ∑ v ∈ G.neighborFinset u, cnt v.val = 3 * ∑ v ∈ Aᶜ, cnt v.val := by
      have hswap : ∑ u ∈ Aᶜ, ∑ v ∈ G.neighborFinset u, cnt v.val =
          ∑ u ∈ Aᶜ, ∑ v ∈ Aᶜ, if G.Adj u v then cnt v.val else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext v
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_compl]
        exact ⟨fun h => ⟨hc v u h.symm, h⟩, fun h => h.2⟩
      rw [hswap, Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      have hfilt : (∑ u ∈ Aᶜ, if G.Adj u v then cnt v.val else 0) =
          ∑ _u ∈ G.neighborFinset v, cnt v.val := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr _ (fun _ _ => rfl)
        ext u
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_compl]
        exact ⟨fun h => h.2.symm, fun h => ⟨hc u v h.symm, h.symm⟩⟩
      rw [hfilt]
      simp only [Finset.sum_const, smul_eq_mul]
      have hdv : (G.neighborFinset v).card = 3 := by
        simpa [SimpleGraph.card_neighborFinset_eq_degree] using dB v hv
      rw [hdv]
    rw [hsplit_sum, hpart1, hpart2] at hlow
    omega
  rcases hex_edge with ⟨u, hu, v, hv, huv_sum⟩
  have huv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
  have huA : u ∉ A := Finset.mem_compl.mp hu
  have hvA : v ∉ A := hc v u huv.symm
  have hu1 : 1 ≤ cnt u.val := unmarked u hu
  have hv1 : 1 ≤ cnt v.val := unmarked v (Finset.mem_compl.mpr hvA)
  by_cases hcu1 : cnt u.val = 1
  · rcases h_read1 n G A f C hnonbip hdeg hgirth hc ⟨w0, w1, hw01⟩ hf hCmin hCfun ⟨u, v, huA, hvA, huv, hcu1⟩ with
      ⟨a, b, ha, hb, hab, s', hs', hhas⟩
    exact ⟨a, b, ha, hb, hab, s', by omega, hhas⟩
  · by_cases hcv1 : cnt v.val = 1
    · rcases h_read1 n G A f C hnonbip hdeg hgirth hc ⟨w0, w1, hw01⟩ hf hCmin hCfun ⟨v, u, hvA, huA, huv.symm, hcv1⟩ with
        ⟨a, b, ha, hb, hab, s', hs', hhas⟩
      exact ⟨a, b, ha, hb, hab, s', by omega, hhas⟩
    · have hcu2 : cnt u.val = 2 := by omega
      have hcv2 : cnt v.val = 2 := by omega
      rcases h_read22 n G A f C hnonbip hdeg hgirth hc ⟨w0, w1, hw01⟩ hf hCmin hCfun ⟨u, v, huA, hvA, huv, hcu2, hcv2⟩ with
        ⟨a, b, ha, hb, hab, s', hs', hhas⟩
      exact ⟨a, b, ha, hb, hab, s', by omega, hhas⟩
