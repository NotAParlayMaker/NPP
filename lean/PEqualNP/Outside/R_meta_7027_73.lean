import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_7027_73
    (h15_18 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (15 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (18 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (h19_20 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (19 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (11 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard → {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) → (21 : ℕ) ≤ {x6 : Fin x1.gates.length | (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro C hm hc _h11 h20
  by_cases h15 : (15 : ℕ) ≤ {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard
  · by_cases h18 : {x4 : Fin C.gates.length | (C.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (18 : ℕ)
    · exact h15_18 C hm hc h15 h18
    · exact h19_20 C hm hc (by omega) h20
  · exfalso
    let isAnd : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
      match g.op with
      | .and => true
      | _ => false
    have isAnd_iff : ∀ g : PEqualNP.CircuitLowerBounds.Gate, isAnd g = true ↔ g.op = .and := by
      intro g; cases g with | mk op ins => cases op <;> simp [isAnd]
    let gateValue : PEqualNP.CircuitLowerBounds.Gate → List Bool → Bool := fun g w =>
      g.op.eval (g.inputs.map fun i => w.getD i false)
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
      w ++ [gateValue g w]
    let trace : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
      fun gs => List.rec (fun _ => [])
        (fun g _ ih w => if isAnd g then w.getD (g.inputs.headD w.length) false :: ih (step w g) else ih (step w g)) gs
    have trace_nil : ∀ w, trace [] w = [] := fun _ => rfl
    have trace_cons : ∀ g gs w, trace (g :: gs) w =
        if isAnd g then w.getD (g.inputs.headD w.length) false :: trace gs (step w g) else trace gs (step w g) :=
      fun _ _ _ => rfl
    have traceLength : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (trace gs w).length = gs.countP isAnd := by
      intro gs
      induction gs with
      | nil => intro w; rfl
      | cons g gs ih =>
        intro w
        rw [trace_cons, List.countP_cons]
        split <;> simp [ih]
    have count_eq : C.gates.countP isAnd =
        {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
      let S := Finset.univ.filter (fun i : Fin C.gates.length => isAnd (C.gates.get i) = true)
      have hs : (S : Set (Fin C.gates.length)) = {i | (C.gates.get i).op = .and} := by
        ext i; simp [S, isAnd_iff]
      rw [← hs, Set.ncard_coe_finset]
      calc
        C.gates.countP isAnd = (List.ofFn C.gates.get).countP isAnd :=
          congrArg (List.countP isAnd) (List.ofFn_get C.gates).symm
        _ = S.card := List.countP_ofFn C.gates.get isAnd
    let Bounds : List Bool → List Bool → List Bool → Prop := fun a b z =>
      ∀ i, z.getD i false = true → a.getD i false = true ∨ b.getD i false = true
    have bounds_append : ∀ {a b z : List Bool}, a.length = z.length → b.length = z.length →
        Bounds a b z → ∀ {x y t : Bool}, (t = true → x = true ∨ y = true) →
        Bounds (a ++ [x]) (b ++ [y]) (z ++ [t]) := by
      intro a b z ha hb h x y t hbit i
      by_cases hi : i < z.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (ha ▸ hi),
          List.getD_append _ _ _ _ (hb ▸ hi)]
        exact h i
      · rw [List.getD_append_right _ _ _ _ (by omega : z.length ≤ i),
          List.getD_append_right _ _ _ _ (by omega : a.length ≤ i),
          List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ha, hb]
        cases i - z.length with
        | zero => simpa using hbit
        | succ n => simp
    have and_bounds : ∀ {ins : List ℕ}, ins.length ≤ 2 → ∀ {a b z : List Bool}, Bounds a b z →
        a.getD (ins.headD a.length) false = b.getD (ins.headD b.length) false →
        gateValue ⟨.and, ins⟩ z = true →
          gateValue ⟨.and, ins⟩ a = true ∨ gateValue ⟨.and, ins⟩ b = true := by
      intro ins hlen a b z h heq
      rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ks⟩⟩⟩
      · simp [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · simpa [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval] using h i
      · simp only [List.headD_cons] at heq
        simp only [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true]
        rintro ⟨hi, hj⟩
        have ha : a.getD i false = true := (h i hi).elim id (fun hb => heq.trans hb)
        have hb : b.getD i false = true := heq.symm.trans ha
        exact (h j hj).imp (fun hja => ⟨ha, hja⟩) (fun hjb => ⟨hb, hjb⟩)
      · simp at hlen
    have or_bounds : ∀ {ins : List ℕ} {a b z : List Bool}, Bounds a b z →
        gateValue ⟨.or, ins⟩ z = true →
          gateValue ⟨.or, ins⟩ a = true ∨ gateValue ⟨.or, ins⟩ b = true := by
      intro ins a b z h
      simp only [gateValue, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, hz⟩
      exact (h i hz).imp (fun ha => ⟨_, ⟨i, hi, rfl⟩, ha⟩) (fun hb => ⟨_, ⟨i, hi, rfl⟩, hb⟩)
    have runBounds : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) →
        ∀ (a b z : List Bool), a.length = z.length → b.length = z.length →
        Bounds a b z → trace gs a = trace gs b →
        Bounds (gs.foldl step a) (gs.foldl step b) (gs.foldl step z) := by
      intro gs
      induction gs with
      | nil => intro _ a b z _ _ h _; exact h
      | cons g gs ih =>
        intro hmg a b z ha hb h ht
        obtain ⟨hop, hlen⟩ := hmg g (by simp)
        have htail : ∀ k ∈ gs, k.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ k.inputs.length ≤ 2 :=
          fun k hk => hmg k (List.mem_cons_of_mem _ hk)
        rcases g with ⟨op, ins⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with rfl | rfl
        · change (if isAnd ⟨.and, ins⟩ then a.getD (ins.headD a.length) false :: trace gs (step a ⟨.and, ins⟩) else trace gs (step a ⟨.and, ins⟩)) =
              (if isAnd ⟨.and, ins⟩ then b.getD (ins.headD b.length) false :: trace gs (step b ⟨.and, ins⟩) else trace gs (step b ⟨.and, ins⟩)) at ht
          simp only [isAnd, ite_true, List.cons.injEq] at ht
          exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
            (bounds_append ha hb h (and_bounds hlen h ht.1)) ht.2
        · change (if isAnd ⟨.or, ins⟩ then a.getD (ins.headD a.length) false :: trace gs (step a ⟨.or, ins⟩) else trace gs (step a ⟨.or, ins⟩)) =
              (if isAnd ⟨.or, ins⟩ then b.getD (ins.headD b.length) false :: trace gs (step b ⟨.or, ins⟩) else trace gs (step b ⟨.or, ins⟩)) at ht
          simp only [isAnd, Bool.false_eq_true, ite_false] at ht
          exact ih htail _ _ _ (by simp [step, ha]) (by simp [step, hb])
            (bounds_append ha hb h (or_bounds h)) ht
    have evalBounds : ∀ (a b : Fin 42 → Bool),
        trace C.gates (List.ofFn a) = trace C.gates (List.ofFn b) →
        C.eval (List.ofFn fun i => a i || b i) = true →
        C.eval (List.ofFn a) = true ∨ C.eval (List.ofFn b) = true := by
      intro a b ht hz
      have h : Bounds (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
        intro i hi
        by_cases hi' : i < 42
        · rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn] at hi
          rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn,
            List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn]
          simpa using hi
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi')] at hi
          cases hi
      exact runBounds C.gates hm _ _ _ (by simp) (by simp) h ht C.output hz
    let point : Fin 21 → Fin 42 := Fin.castAdd 21
    let line : Fin 21 → Fin 42 := Fin.natAdd 21
    let offset : Fin 5 → Fin 21 := fun i =>
      match i.val with
      | 0 => 20
      | 1 => 0
      | 2 => 5
      | 3 => 7
      | _ => 17
    let Inc : Fin 21 → Fin 21 → Prop := fun p l => ∃ i : Fin 5, p + offset i = l
    let edgesAt : ℕ → List (ℕ × ℕ) := fun p =>
      [(p, 21 + (p + 20) % 21), (p, 21 + p), (p, 21 + (p + 5) % 21),
       (p, 21 + (p + 7) % 21), (p, 21 + (p + 17) % 21)]
    let edges : List (ℕ × ℕ) := (List.range 21).flatMap edgesAt
    have edgesAt_point : ∀ p : Fin 21,
        edgesAt p.val = List.ofFn (fun i => ((point p).val, (line (p + offset i)).val)) := by
      intro p
      simp [edgesAt, List.ofFn_succ, point, line, offset, Fin.val_add,
        Nat.mod_eq_of_lt p.isLt, Nat.add_comm 21]
    have edge_forward : ∀ {u v : Fin 42}, (u.val, v.val) ∈ edges →
        ∃ p l, u = point p ∧ v = line l ∧ Inc p l := by
      intro u v h
      obtain ⟨n, hn, hmem⟩ := List.mem_flatMap.mp h
      let p : Fin 21 := ⟨n, List.mem_range.mp hn⟩
      change (u.val, v.val) ∈ edgesAt p.val at hmem
      rw [edgesAt_point, List.mem_ofFn] at hmem
      obtain ⟨i, hi⟩ := hmem
      exact ⟨p, p + offset i, Fin.ext (congrArg Prod.fst hi).symm,
        Fin.ext (congrArg Prod.snd hi).symm, i, rfl⟩
    have edge_backward : ∀ {p l : Fin 21}, Inc p l →
        ((point p).val, (line l).val) ∈ edges := by
      intro p l ⟨i, hi⟩
      subst hi
      refine List.mem_flatMap.mpr ⟨p.val, List.mem_range.mpr p.isLt, ?_⟩
      rw [edgesAt_point, List.mem_ofFn]
      exact ⟨i, rfl⟩
    have offset_inj : Function.Injective offset := by
      change ∀ i j : Fin 5,
        (match i.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) =
        (match j.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) → i = j
      decide
    have diff_inj : ∀ (i j i' j' : Fin 5), offset i - offset j = offset i' - offset j' →
        i ≠ j → i = i' ∧ j = j' := by
      change ∀ (i j i' j' : Fin 5),
        (match i.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) -
        (match j.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) =
        (match i'.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) -
        (match j'.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) →
        i ≠ j → i = i' ∧ j = j'
      decide
    have diff_surj : ∀ d : Fin 21, d ≠ 0 → ∃ i j : Fin 5, offset i - offset j = d := by
      change ∀ d : Fin 21, d ≠ 0 → ∃ i j : Fin 5,
        (match i.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) -
        (match j.val with | 0 => (20 : Fin 21) | 1 => 0 | 2 => 5 | 3 => 7 | _ => 17) = d
      decide
    have unique_line : ∀ (p q l1 l2 : Fin 21), p ≠ q → Inc p l1 → Inc q l1 → Inc p l2 → Inc q l2 → l1 = l2 := by
      rintro p q l1 l2 hpq ⟨i1, h1⟩ ⟨j1, h2⟩ ⟨i2, h3⟩ ⟨j2, h4⟩
      have hd1 : offset i1 - offset j1 = q - p := by
        calc offset i1 - offset j1 = (p + offset i1) - (q + offset j1) + (q - p) := by abel
          _ = l1 - l1 + (q - p) := by rw [h1, h2]
          _ = q - p := by abel
      have hd2 : offset i2 - offset j2 = q - p := by
        calc offset i2 - offset j2 = (p + offset i2) - (q + offset j2) + (q - p) := by abel
          _ = l2 - l2 + (q - p) := by rw [h3, h4]
          _ = q - p := by abel
      have hij : i1 ≠ j1 := by
        intro heq; subst heq; rw [sub_self] at hd1; exact hpq (sub_eq_zero.mp hd1.symm).symm
      have hpair := diff_inj i1 j1 i2 j2 (hd1.trans hd2.symm) hij
      rw [← h1, ← h3, hpair.1]
    have unique_inter : ∀ (l1 l2 p q : Fin 21), l1 ≠ l2 → Inc p l1 → Inc p l2 → Inc q l1 → Inc q l2 → p = q := by
      rintro l1 l2 p q hl ⟨i1, h1⟩ ⟨i2, h2⟩ ⟨j1, h3⟩ ⟨j2, h4⟩
      have hd1 : offset i2 - offset i1 = l2 - l1 := by
        calc offset i2 - offset i1 = (p + offset i2) - (p + offset i1) := by abel
          _ = l2 - l1 := by rw [h1, h2]
      have hd2 : offset j2 - offset j1 = l2 - l1 := by
        calc offset j2 - offset j1 = (q + offset j2) - (q + offset j1) := by abel
          _ = l2 - l1 := by rw [h3, h4]
      have hij : i2 ≠ i1 := by
        intro heq; subst heq; rw [sub_self] at hd1; exact hl (sub_eq_zero.mp hd1.symm).symm
      have hpair := diff_inj i2 i1 j2 j1 (hd1.trans hd2.symm) hij
      have hpe : p + offset i1 = q + offset i1 := by rw [h1, ← h3, hpair.2]
      exact add_right_cancel hpe
    have inter_exists : ∀ (l1 l2 : Fin 21), l1 ≠ l2 → ∃ p : Fin 21, Inc p l1 ∧ Inc p l2 := by
      intro l1 l2 hl
      have hd : l2 - l1 ≠ 0 := sub_ne_zero.mpr hl.symm
      obtain ⟨i, j, hij⟩ := diff_surj (l2 - l1) hd
      refine ⟨l1 - offset j, ⟨j, by abel⟩, ⟨i, ?_⟩⟩
      calc (l1 - offset j) + offset i = l1 + (offset i - offset j) := by abel
        _ = l1 + (l2 - l1) := by rw [hij]
        _ = l2 := by abel
    have line_exists : ∀ (p q : Fin 21), p ≠ q → ∃ l : Fin 21, Inc p l ∧ Inc q l := by
      intro p q hpq
      have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
      obtain ⟨i, j, hij⟩ := diff_surj (q - p) hd
      refine ⟨p + offset i, ⟨i, rfl⟩, ⟨j, ?_⟩⟩
      calc q + offset j = p + (q - p) + offset j := by abel
        _ = p + (offset i - offset j) + offset j := by rw [hij]
        _ = p + offset i := by abel
    let IsClosed : Finset (Fin 21) → Prop := fun P =>
      ∀ p ∉ P, ∃ l, Inc p l ∧ ∀ q ∈ P, ¬ Inc q l
    have closed_of_card_le_four : ∀ P : Finset (Fin 21), P.card ≤ 4 → IsClosed P := by
      intro P hP p hp
      by_contra! hn
      have blocks : ∀ i : Fin 5, ∃ q ∈ P, Inc q (p + offset i) := fun i => hn (p + offset i) ⟨i, rfl⟩
      choose f hf hi using blocks
      have hinj : Set.InjOn f (Finset.univ : Finset (Fin 5)) := by
        intro i _ j _ hij
        have hpq : p ≠ f i := fun h => hp (h ▸ hf i)
        have hleq : p + offset i = p + offset j :=
          unique_line p (f i) (p + offset i) (p + offset j) hpq ⟨i, rfl⟩ (hi i) ⟨j, rfl⟩ (hij ▸ hi j)
        exact offset_inj (add_left_cancel hleq)
      have hcard := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 5))) (t := P) f (fun i _ => hf i) hinj
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    let FiveCode := { c : Fin 21 × Finset (Fin 5) × Fin 5 × Fin 5 × Finset (Fin 5) //
      c.2.1.card = 3 ∧ c.2.2.1 ∉ c.2.1 ∧ c.2.2.2.1 ≠ c.2.2.1 ∧ c.2.2.2.2.card = 2 ∧ c.2.2.2.1 ∉ c.2.2.2.2 }
    let mkFive : FiveCode → Finset (Fin 21) := fun c =>
      let l0 := c.1.1
      let Tidx := c.1.2.1
      let ir := c.1.2.2.1
      let j := c.1.2.2.2.1
      let ABidx := c.1.2.2.2.2
      let M := l0 - offset ir + offset j
      (Tidx.image (fun i => l0 - offset i)) ∪ (ABidx.image (fun k => M - offset k))
    have mkFive_card : ∀ c : FiveCode, (mkFive c).card = 5 := by
      rintro ⟨⟨l0, Tidx, ir, j, ABidx⟩, hT3, hir, hjir, hAB2, hjAB⟩
      let M := l0 - offset ir + offset j
      have hMl0 : M ≠ l0 := by
        intro h
        have h1 : offset j = offset ir := by
          have : (l0 - offset ir + offset j) - (l0 - offset ir) = l0 - (l0 - offset ir) := congrArg (· - (l0 - offset ir)) h
          simpa using this
        exact hjir (offset_inj h1)
      have hTinj : Function.Injective (fun i : Fin 5 => l0 - offset i) := by
        intro a b hab
        exact offset_inj (sub_right_inj.mp hab)
      have hABinj : Function.Injective (fun k : Fin 5 => M - offset k) := by
        intro a b hab
        exact offset_inj (sub_right_inj.mp hab)
      have hdisj : Disjoint (Tidx.image (fun i => l0 - offset i)) (ABidx.image (fun k => M - offset k)) := by
        rw [Finset.disjoint_left]
        intro x hxT hxAB
        rcases Finset.mem_image.mp hxT with ⟨i, hiT, rfl⟩
        rcases Finset.mem_image.mp hxAB with ⟨k, hkAB, hk⟩
        have hinc1 : Inc (l0 - offset i) l0 := ⟨i, by abel⟩
        have hinc2 : Inc (l0 - offset i) M := ⟨k, by rw [← hk]; abel⟩
        have hr1 : Inc (l0 - offset ir) l0 := ⟨ir, by abel⟩
        have hr2 : Inc (l0 - offset ir) M := ⟨j, by dsimp only [M]⟩
        have heq := unique_inter l0 M (l0 - offset i) (l0 - offset ir) hMl0.symm hinc1 hinc2 hr1 hr2
        exact hir (hTinj heq ▸ hiT)
      change ((Tidx.image (fun i => l0 - offset i)) ∪ (ABidx.image (fun k => M - offset k))).card = 5
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hTinj,
        Finset.card_image_of_injective _ hABinj, hT3, hAB2]
    have mkFive_closed : ∀ c : FiveCode, IsClosed (mkFive c) := by
      rintro ⟨⟨l0, Tidx, ir, j, ABidx⟩, hT3, hir, hjir, hAB2, hjAB⟩ p hp
      let M := l0 - offset ir + offset j
      let rpt := l0 - offset ir
      let T := Tidx.image (fun i => l0 - offset i)
      let AB := ABidx.image (fun k => M - offset k)
      have hPeq : mkFive ⟨⟨l0, Tidx, ir, j, ABidx⟩, hT3, hir, hjir, hAB2, hjAB⟩ = T ∪ AB := rfl
      rw [hPeq] at hp ⊢
      have hMl0 : M ≠ l0 := by
        intro h
        have h1 : offset j = offset ir := by
          have : (l0 - offset ir + offset j) - (l0 - offset ir) = l0 - (l0 - offset ir) := congrArg (· - (l0 - offset ir)) h
          simpa using this
        exact hjir (offset_inj h1)
      have hTinj : Function.Injective (fun i : Fin 5 => l0 - offset i) := fun a b hab => offset_inj (sub_right_inj.mp hab)
      have hABinj : Function.Injective (fun k : Fin 5 => M - offset k) := fun a b hab => offset_inj (sub_right_inj.mp hab)
      have hTcard : T.card = 3 := by rw [Finset.card_image_of_injective _ hTinj, hT3]
      have hABcard : AB.card = 2 := by rw [Finset.card_image_of_injective _ hABinj, hAB2]
      by_cases hpl0 : Inc p l0
      · obtain ⟨ip, hip⟩ := hpl0
        by_contra! hn
        have blocks : ∀ i : Fin 5, i ≠ ip → ∃ q ∈ AB, Inc q (p + offset i) := by
          intro i hi
          obtain ⟨q, hq, hqi⟩ := hn (p + offset i) ⟨i, rfl⟩
          rcases Finset.mem_union.mp hq with hqT | hqAB
          · exfalso
            rcases Finset.mem_image.mp hqT with ⟨it, hit, rfl⟩
            have hneq : p ≠ l0 - offset it := fun he => hp (Finset.mem_union_left _ (he ▸ Finset.mem_image_of_mem _ hit))
            have hline := unique_line p (l0 - offset it) (p + offset i) l0 hneq ⟨i, rfl⟩ hqi ⟨ip, hip⟩ ⟨it, by abel⟩
            exact hi (offset_inj (add_left_cancel (hline.trans hip.symm)))
          · exact ⟨q, hqAB, hqi⟩
        let S : Finset (Fin 5) := Finset.univ.erase ip
        have hScard : S.card = 4 := by simp [S]
        have hex : ∀ s ∈ S, ∃ q ∈ AB, Inc q (p + offset s) := fun s hs => blocks s (Finset.mem_erase.mp hs).1
        choose f hf hi using hex
        let g : Fin 5 → Fin 21 := fun s => if h : s ∈ S then f s h else 0
        have hg_eq : ∀ s (hs : s ∈ S), g s = f s hs := fun s hs => by dsimp only [g]; split_ifs; rfl
        have hinj : Set.InjOn g (S : Set (Fin 5)) := by
          intro a ha b hb hab
          have ha' : a ∈ S := Finset.mem_coe.mp ha
          have hb' : b ∈ S := Finset.mem_coe.mp hb
          rw [hg_eq a ha', hg_eq b hb'] at hab
          have hneq : p ≠ f a ha' := fun he => hp (Finset.mem_union_right _ (he ▸ hf a ha'))
          have hline := unique_line p (f a ha') (p + offset a) (p + offset b) hneq ⟨a, rfl⟩ (hi a ha') ⟨b, rfl⟩ (hab ▸ hi b hb')
          exact offset_inj (add_left_cancel hline)
        have hle := Finset.card_le_card_of_injOn (s := S) (t := AB) g
          (fun s hs => by rw [hg_eq s (Finset.mem_coe.mp hs)]; exact Finset.mem_coe.mpr (hf s (Finset.mem_coe.mp hs))) hinj
        omega
      · by_cases hpM : Inc p M
        · obtain ⟨ip, hip⟩ := hpM
          by_contra! hn
          have blocks : ∀ i : Fin 5, i ≠ ip → ∃ q ∈ T, Inc q (p + offset i) := by
            intro i hi
            obtain ⟨q, hq, hqi⟩ := hn (p + offset i) ⟨i, rfl⟩
            rcases Finset.mem_union.mp hq with hqT | hqAB
            · exact ⟨q, hqT, hqi⟩
            · exfalso
              rcases Finset.mem_image.mp hqAB with ⟨k, hk, rfl⟩
              have hneq : p ≠ M - offset k := fun he => hp (Finset.mem_union_right _ (he ▸ Finset.mem_image_of_mem _ hk))
              have hline := unique_line p (M - offset k) (p + offset i) M hneq ⟨i, rfl⟩ hqi ⟨ip, hip⟩ ⟨k, by abel⟩
              exact hi (offset_inj (add_left_cancel (hline.trans hip.symm)))
          let S : Finset (Fin 5) := Finset.univ.erase ip
          have hScard : S.card = 4 := by simp [S]
          have hex : ∀ s ∈ S, ∃ q ∈ T, Inc q (p + offset s) := fun s hs => blocks s (Finset.mem_erase.mp hs).1
          choose f hf hi using hex
          let g : Fin 5 → Fin 21 := fun s => if h : s ∈ S then f s h else 0
          have hg_eq : ∀ s (hs : s ∈ S), g s = f s hs := fun s hs => by dsimp only [g]; split_ifs; rfl
          have hinj : Set.InjOn g (S : Set (Fin 5)) := by
            intro a ha b hb hab
            have ha' : a ∈ S := Finset.mem_coe.mp ha
            have hb' : b ∈ S := Finset.mem_coe.mp hb
            rw [hg_eq a ha', hg_eq b hb'] at hab
            have hneq : p ≠ f a ha' := fun he => hp (Finset.mem_union_left _ (he ▸ hf a ha'))
            have hline := unique_line p (f a ha') (p + offset a) (p + offset b) hneq ⟨a, rfl⟩ (hi a ha') ⟨b, rfl⟩ (hab ▸ hi b hb')
            exact offset_inj (add_left_cancel hline)
          have hle := Finset.card_le_card_of_injOn (s := S) (t := T) g
            (fun s hs => by rw [hg_eq s (Finset.mem_coe.mp hs)]; exact Finset.mem_coe.mpr (hf s (Finset.mem_coe.mp hs))) hinj
          omega
        · obtain ⟨k1, k2, hk12, hABeq⟩ := Finset.card_eq_two.mp hAB2
          dsimp only at hABeq
          let a := M - offset k1
          let b := M - offset k2
          have haAB : a ∈ AB := Finset.mem_image_of_mem (fun k => M - offset k) (show k1 ∈ ABidx by rw [hABeq]; simp)
          have hbAB : b ∈ AB := Finset.mem_image_of_mem (fun k => M - offset k) (show k2 ∈ ABidx by rw [hABeq]; simp)
          have hpa : p ≠ a := fun he => hp (Finset.mem_union_right _ (he ▸ haAB))
          have hpb : p ≠ b := fun he => hp (Finset.mem_union_right _ (he ▸ hbAB))
          obtain ⟨la, hpla, hala⟩ := line_exists p a hpa
          obtain ⟨lb, hplb, hblb⟩ := line_exists p b hpb
          have hne_la_lb : la ≠ lb := by
            intro heq
            subst heq
            have hab_ne : a ≠ b := fun h => hk12 (hABinj h)
            have hlaM : la = M := unique_line a b la M hab_ne hala hblb ⟨k1, by dsimp only [a]; abel⟩ ⟨k2, by dsimp only [b]; abel⟩
            exact hpM (hlaM ▸ hpla)
          have hne_la_l0 : la ≠ l0 := fun h => hpl0 (h ▸ hpla)
          have hne_lb_l0 : lb ≠ l0 := fun h => hpl0 (h ▸ hplb)
          obtain ⟨qa, hqa_la, hqa_l0⟩ := inter_exists la l0 hne_la_l0
          obtain ⟨qb, hqb_lb, hqb_l0⟩ := inter_exists lb l0 hne_lb_l0
          have hqa_ne_qb : qa ≠ qb := by
            intro heq
            subst heq
            have hqap := unique_inter la lb qa p hne_la_lb hqa_la hqb_lb hpla hplb
            exact hpl0 (hqap ▸ hqa_l0)
          have hqa_ne_r : qa ≠ rpt := by
            intro heq
            subst heq
            have har : a ≠ rpt := by
              intro h
              have hk1j : k1 = j := by
                have : M - offset k1 = M - offset j := by simpa [a, rpt, M] using h
                exact hABinj this
              exact hjAB (by rw [hABeq, ← hk1j]; simp)
            have hlaM : la = M := unique_line a rpt la M har hala hqa_la ⟨k1, by dsimp only [a]; abel⟩ ⟨j, by dsimp only [M, rpt]⟩
            exact hpM (hlaM ▸ hpla)
          have hqb_ne_r : qb ≠ rpt := by
            intro heq
            subst heq
            have hbr : b ≠ rpt := by
              intro h
              have hk2j : k2 = j := by
                have : M - offset k2 = M - offset j := by simpa [b, rpt, M] using h
                exact hABinj this
              exact hjAB (by rw [hABeq, ← hk2j]; simp)
            have hlbM : lb = M := unique_line b rpt lb M hbr hblb hqb_lb ⟨k2, by dsimp only [b]; abel⟩ ⟨j, by dsimp only [M, rpt]⟩
            exact hpM (hlbM ▸ hplb)
          have hitT : qa ∈ T ∨ qb ∈ T := by
            obtain ⟨ia, hia⟩ := hqa_l0
            obtain ⟨ib, hib⟩ := hqb_l0
            have hia_eq : qa = l0 - offset ia := by rw [← hia]; abel
            have hib_eq : qb = l0 - offset ib := by rw [← hib]; abel
            have h1 : ia ≠ ib := fun h => hqa_ne_qb (by rw [hia_eq, hib_eq, h])
            have h2 : ia ≠ ir := fun h => hqa_ne_r (by rw [hia_eq, h])
            have h3 : ib ≠ ir := fun h => hqb_ne_r (by rw [hib_eq, h])
            by_contra! hnot
            have hia_not : ia ∉ Tidx := fun h => hnot.1 (hia_eq ▸ Finset.mem_image_of_mem _ h)
            have hib_not : ib ∉ Tidx := fun h => hnot.2 (hib_eq ▸ Finset.mem_image_of_mem _ h)
            have hsub : ({ia, ib, ir} : Finset (Fin 5)) ⊆ Finset.univ \ Tidx := by
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl | rfl <;> assumption
            have hc3 : ({ia, ib, ir} : Finset (Fin 5)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [h1, h2]),
                Finset.card_insert_of_notMem (by simp [h3]), Finset.card_singleton]
            have hle := Finset.card_le_card hsub
            have hsd : (Finset.univ \ Tidx).card = 5 - 3 := by
              rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hT3]
            omega
          have hpair_line : ∃ l, Inc p l ∧ ∃ u ∈ T ∪ AB, ∃ v ∈ T ∪ AB, u ≠ v ∧ Inc u l ∧ Inc v l := by
            rcases hitT with hqaT | hqbT
            · have hne : a ≠ qa := by
                intro heq
                rcases Finset.mem_image.mp hqaT with ⟨it, hit, hqt⟩
                have hinc1 : Inc a l0 := ⟨it, by rw [heq, ← hqt]; abel⟩
                have hinc2 : Inc a M := ⟨k1, by dsimp only [a]; abel⟩
                have hr1 : Inc rpt l0 := ⟨ir, by dsimp only [rpt]; abel⟩
                have hr2 : Inc rpt M := ⟨j, by dsimp only [M, rpt]⟩
                have har := unique_inter l0 M a rpt hMl0.symm hinc1 hinc2 hr1 hr2
                exact hqa_ne_r (heq ▸ har)
              exact ⟨la, hpla, a, Finset.mem_union_right _ haAB, qa, Finset.mem_union_left _ hqaT, hne, hala, hqa_la⟩
            · have hne : b ≠ qb := by
                intro heq
                rcases Finset.mem_image.mp hqbT with ⟨it, hit, hqt⟩
                have hinc1 : Inc b l0 := ⟨it, by rw [heq, ← hqt]; abel⟩
                have hinc2 : Inc b M := ⟨k2, by dsimp only [b]; abel⟩
                have hr1 : Inc rpt l0 := ⟨ir, by dsimp only [rpt]; abel⟩
                have hr2 : Inc rpt M := ⟨j, by dsimp only [M, rpt]⟩
                have hbr := unique_inter l0 M b rpt hMl0.symm hinc1 hinc2 hr1 hr2
                exact hqb_ne_r (heq ▸ hbr)
              exact ⟨lb, hplb, b, Finset.mem_union_right _ hbAB, qb, Finset.mem_union_left _ hqbT, hne, hblb, hqb_lb⟩
          obtain ⟨lstar, ⟨istar, histar⟩, u, hu, v, hv, huv, hul, hvl⟩ := hpair_line
          by_contra! hn
          let S : Finset (Fin 5) := Finset.univ.erase istar
          have hScard : S.card = 4 := by simp [S]
          let R : Finset (Fin 21) := (T ∪ AB).erase u |>.erase v
          have hRcard : R.card = 3 := by
            have hcard5 : (T ∪ AB).card = 5 := mkFive_card ⟨⟨l0, Tidx, ir, j, ABidx⟩, hT3, hir, hjir, hAB2, hjAB⟩
            have hv1 : v ∈ (T ∪ AB).erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
            rw [Finset.card_erase_of_mem hv1, Finset.card_erase_of_mem hu, hcard5]
          have hex : ∀ s ∈ S, ∃ q ∈ R, Inc q (p + offset s) := by
            intro s hs
            have hsne : s ≠ istar := (Finset.mem_erase.mp hs).1
            obtain ⟨q, hq, hqi⟩ := hn (p + offset s) ⟨s, rfl⟩
            refine ⟨q, ?_, hqi⟩
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hq⟩⟩
            · intro hqv
              subst hqv
              have hne : p ≠ q := fun he => hp (he ▸ hq)
              have hline := unique_line p q (p + offset s) lstar hne ⟨s, rfl⟩ hqi ⟨istar, histar⟩ hvl
              exact hsne (offset_inj (add_left_cancel (hline.trans histar.symm)))
            · intro hqu
              subst hqu
              have hne : p ≠ q := fun he => hp (he ▸ hq)
              have hline := unique_line p q (p + offset s) lstar hne ⟨s, rfl⟩ hqi ⟨istar, histar⟩ hul
              exact hsne (offset_inj (add_left_cancel (hline.trans histar.symm)))
          choose f hf hi using hex
          let g : Fin 5 → Fin 21 := fun s => if h : s ∈ S then f s h else 0
          have hg_eq : ∀ s (hs : s ∈ S), g s = f s hs := fun s hs => by dsimp only [g]; split_ifs; rfl
          have hinj : Set.InjOn g (S : Set (Fin 5)) := by
            intro s1 hs1 s2 hs2 hab
            have hs1' : s1 ∈ S := Finset.mem_coe.mp hs1
            have hs2' : s2 ∈ S := Finset.mem_coe.mp hs2
            rw [hg_eq s1 hs1', hg_eq s2 hs2'] at hab
            have hqmem : f s1 hs1' ∈ T ∪ AB := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hf s1 hs1'))
            have hneq : p ≠ f s1 hs1' := fun he => hp (he ▸ hqmem)
            have hline := unique_line p (f s1 hs1') (p + offset s1) (p + offset s2) hneq ⟨s1, rfl⟩ (hi s1 hs1') ⟨s2, rfl⟩ (hab ▸ hi s2 hs2')
            exact offset_inj (add_left_cancel hline)
          have hle := Finset.card_le_card_of_injOn (s := S) (t := R) g
            (fun s hs => by rw [hg_eq s (Finset.mem_coe.mp hs)]; exact Finset.mem_coe.mpr (hf s (Finset.mem_coe.mp hs))) hinj
          omega
    have mkFive_inj : Function.Injective mkFive := by
      rintro ⟨⟨l1, T1, ir1, j1, AB1⟩, hT1, hir1, hjir1, hAB1, hjAB1⟩
        ⟨⟨l2, T2, ir2, j2, AB2⟩, hT2, hir2, hjir2, hAB2, hjAB2⟩ heq
      have hsub_inj : ∀ l : Fin 21, Function.Injective (fun i : Fin 5 => l - offset i) :=
        fun l a b hab => offset_inj (sub_right_inj.mp hab)
      have huniq_l : l1 = l2 := by
        by_contra hne
        let P := mkFive ⟨⟨l1, T1, ir1, j1, AB1⟩, hT1, hir1, hjir1, hAB1, hjAB1⟩
        have hT2_in : (T2.image (fun i => l2 - offset i)) ⊆ P := by
          dsimp only [P]; rw [heq]; exact Finset.subset_union_left
        let M1 := l1 - offset ir1 + offset j1
        have hM1l1 : M1 ≠ l1 := by
          intro h
          have h1 : offset j1 = offset ir1 := by
            have : (l1 - offset ir1 + offset j1) - (l1 - offset ir1) = l1 - (l1 - offset ir1) := congrArg (· - (l1 - offset ir1)) h
            simpa using this
          exact hjir1 (offset_inj h1)
        let S1 := (T2.image (fun i => l2 - offset i)) ∩ (T1.image (fun i => l1 - offset i))
        let S2 := (T2.image (fun i => l2 - offset i)) ∩ (AB1.image (fun k => M1 - offset k))
        have hS1_le : S1.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro x hx y hy
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hx).1 with ⟨ix2, _, rfl⟩
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hx).2 with ⟨ix1, _, hx1⟩
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hy).1 with ⟨iy2, _, rfl⟩
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hy).2 with ⟨iy1, _, hy1⟩
          exact unique_inter l2 l1 _ _ (Ne.symm hne) ⟨ix2, by abel⟩ ⟨ix1, by rw [← hx1]; abel⟩ ⟨iy2, by abel⟩ ⟨iy1, by rw [← hy1]; abel⟩
        have hS2_le : S2.card ≤ 2 := by
          calc S2.card ≤ (AB1.image (fun k => M1 - offset k)).card := Finset.card_le_card Finset.inter_subset_right
            _ = 2 := by rw [Finset.card_image_of_injective _ (hsub_inj M1), hAB1]
        have hcov : (T2.image (fun i => l2 - offset i)) ⊆ S1 ∪ S2 := by
          intro x hx
          rcases Finset.mem_union.mp (hT2_in hx) with hx1 | hx2
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hx1⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hx2⟩)
        have hcard3 : (T2.image (fun i => l2 - offset i)).card = 3 := by
          rw [Finset.card_image_of_injective _ (hsub_inj l2), hT2]
        have hsum : 3 ≤ S1.card + S2.card := by
          calc 3 = (T2.image (fun i => l2 - offset i)).card := hcard3.symm
            _ ≤ (S1 ∪ S2).card := Finset.card_le_card hcov
            _ ≤ S1.card + S2.card := Finset.card_union_le _ _
        have hS1_eq : S1.card = 1 := by omega
        have hS2_eq : S2.card = 2 := by omega
        obtain ⟨x, hxS1⟩ := Finset.card_eq_one.mp hS1_eq
        have hxmem : x ∈ S1 := by rw [hxS1]; simp
        obtain ⟨y1, y2, hy12, hS2eq⟩ := Finset.card_eq_two.mp hS2_eq
        have hy1 : y1 ∈ S2 := by rw [hS2eq]; simp
        have hy2 : y2 ∈ S2 := by rw [hS2eq]; simp
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hy1).1 with ⟨iy1, _, rfl⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hy1).2 with ⟨ky1, _, hky1⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hy2).1 with ⟨iy2, _, rfl⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hy2).2 with ⟨ky2, _, hky2⟩
        have hl2M1 : l2 = M1 := unique_line _ _ l2 M1 hy12 ⟨iy1, by abel⟩ ⟨iy2, by abel⟩
          ⟨ky1, by rw [← hky1]; abel⟩ ⟨ky2, by rw [← hky2]; abel⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hxmem).1 with ⟨ix2, _, rfl⟩
        rcases Finset.mem_image.mp (Finset.mem_inter.mp hxmem).2 with ⟨ix1, hix1, hx1⟩
        have hxr := unique_inter l1 M1 (l2 - offset ix2) (l1 - offset ir1) hM1l1.symm
          ⟨ix1, by rw [← hx1]; abel⟩ ⟨ix2, by rw [← hl2M1]; abel⟩ ⟨ir1, by abel⟩ ⟨j1, by dsimp only [M1]⟩
        have hix1_eq : ix1 = ir1 := hsub_inj l1 (hx1.trans hxr)
        exact hir1 (hix1_eq ▸ hix1)
      subst huniq_l
      let M1 := l1 - offset ir1 + offset j1
      let M2 := l1 - offset ir2 + offset j2
      have hM1l1 : M1 ≠ l1 := by
        intro h
        have h1 : offset j1 = offset ir1 := by
          have : (l1 - offset ir1 + offset j1) - (l1 - offset ir1) = l1 - (l1 - offset ir1) := congrArg (· - (l1 - offset ir1)) h
          simpa using this
        exact hjir1 (offset_inj h1)
      have hM2l1 : M2 ≠ l1 := by
        intro h
        have h1 : offset j2 = offset ir2 := by
          have : (l1 - offset ir2 + offset j2) - (l1 - offset ir2) = l1 - (l1 - offset ir2) := congrArg (· - (l1 - offset ir2)) h
          simpa using this
        exact hjir2 (offset_inj h1)
      have hTeq : T1.image (fun i => l1 - offset i) = T2.image (fun i => l1 - offset i) := by
        ext x
        have hnotAB1 : ∀ y ∈ AB1.image (fun k => M1 - offset k), ¬ Inc y l1 := by
          intro y hy hyl1
          rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
          have hyr := unique_inter l1 M1 (M1 - offset k) (l1 - offset ir1) hM1l1.symm hyl1 ⟨k, by abel⟩ ⟨ir1, by abel⟩ ⟨j1, by dsimp only [M1]⟩
          have hkj : k = j1 := hsub_inj M1 (by simpa [M1] using hyr)
          exact hjAB1 (hkj ▸ hk)
        have hnotAB2 : ∀ y ∈ AB2.image (fun k => M2 - offset k), ¬ Inc y l1 := by
          intro y hy hyl1
          rcases Finset.mem_image.mp hy with ⟨k, hk, rfl⟩
          have hyr := unique_inter l1 M2 (M2 - offset k) (l1 - offset ir2) hM2l1.symm hyl1 ⟨k, by abel⟩ ⟨ir2, by abel⟩ ⟨j2, by dsimp only [M2]⟩
          have hkj : k = j2 := hsub_inj M2 (by simpa [M2] using hyr)
          exact hjAB2 (hkj ▸ hk)
        constructor
        · intro hx
          have hxm : x ∈ mkFive ⟨⟨l1, T2, ir2, j2, AB2⟩, hT2, hir2, hjir2, hAB2, hjAB2⟩ := heq ▸ Finset.mem_union_left _ hx
          rcases Finset.mem_union.mp hxm with hx2 | hxAB2
          · exact hx2
          · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
            exact (hnotAB2 _ hxAB2 ⟨i, by abel⟩).elim
        · intro hx
          have hxm : x ∈ mkFive ⟨⟨l1, T1, ir1, j1, AB1⟩, hT1, hir1, hjir1, hAB1, hjAB1⟩ := heq.symm ▸ Finset.mem_union_left _ hx
          rcases Finset.mem_union.mp hxm with hx1 | hxAB1
          · exact hx1
          · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
            exact (hnotAB1 _ hxAB1 ⟨i, by abel⟩).elim
      have hT12 : T1 = T2 := by
        ext i
        constructor
        · intro hi
          have : l1 - offset i ∈ T2.image (fun i => l1 - offset i) := hTeq ▸ Finset.mem_image_of_mem _ hi
          rcases Finset.mem_image.mp this with ⟨i', hi', hii'⟩
          exact (hsub_inj l1 hii') ▸ hi'
        · intro hi
          have : l1 - offset i ∈ T1.image (fun i => l1 - offset i) := hTeq.symm ▸ Finset.mem_image_of_mem _ hi
          rcases Finset.mem_image.mp this with ⟨i', hi', hii'⟩
          exact (hsub_inj l1 hii') ▸ hi'
      subst hT12
      have hABeq : AB1.image (fun k => M1 - offset k) = AB2.image (fun k => M2 - offset k) := by
        have hd1 : Disjoint (T1.image (fun i => l1 - offset i)) (AB1.image (fun k => M1 - offset k)) := by
          rw [Finset.disjoint_left]
          intro x hxT hxAB
          rcases Finset.mem_image.mp hxT with ⟨i, hiT, rfl⟩
          rcases Finset.mem_image.mp hxAB with ⟨k, hkAB, hk⟩
          have hxr := unique_inter l1 M1 (l1 - offset i) (l1 - offset ir1) hM1l1.symm ⟨i, by abel⟩ ⟨k, by rw [← hk]; abel⟩ ⟨ir1, by abel⟩ ⟨j1, by dsimp only [M1]⟩
          exact hir1 (hsub_inj l1 hxr ▸ hiT)
        have hd2 : Disjoint (T1.image (fun i => l1 - offset i)) (AB2.image (fun k => M2 - offset k)) := by
          rw [Finset.disjoint_left]
          intro x hxT hxAB
          rcases Finset.mem_image.mp hxT with ⟨i, hiT, rfl⟩
          rcases Finset.mem_image.mp hxAB with ⟨k, hkAB, hk⟩
          have hxr := unique_inter l1 M2 (l1 - offset i) (l1 - offset ir2) hM2l1.symm ⟨i, by abel⟩ ⟨k, by rw [← hk]; abel⟩ ⟨ir2, by abel⟩ ⟨j2, by dsimp only [M2]⟩
          exact hir2 (hsub_inj l1 hxr ▸ hiT)
        ext x
        constructor
        · intro hx
          have hxm : x ∈ (T1.image (fun i => l1 - offset i)) ∪ (AB2.image (fun k => M2 - offset k)) := by
            change x ∈ mkFive ⟨⟨l1, T1, ir2, j2, AB2⟩, hT2, hir2, hjir2, hAB2, hjAB2⟩
            rw [← heq]
            exact Finset.mem_union_right _ hx
          rcases Finset.mem_union.mp hxm with hxT | hx2
          · exact (Finset.disjoint_left.mp hd1 hxT hx).elim
          · exact hx2
        · intro hx
          have hxm : x ∈ (T1.image (fun i => l1 - offset i)) ∪ (AB1.image (fun k => M1 - offset k)) := by
            change x ∈ mkFive ⟨⟨l1, T1, ir1, j1, AB1⟩, hT1, hir1, hjir1, hAB1, hjAB1⟩
            rw [heq]
            exact Finset.mem_union_right _ hx
          rcases Finset.mem_union.mp hxm with hxT | hx1
          · exact (Finset.disjoint_left.mp hd2 hxT hx).elim
          · exact hx1
      obtain ⟨k1, k2, hk12, hAB1eq⟩ := Finset.card_eq_two.mp hAB1
      dsimp only at hAB1eq
      have hm1 : M1 - offset k1 ∈ AB2.image (fun k => M2 - offset k) := hABeq ▸ Finset.mem_image_of_mem (fun k => M1 - offset k) (show k1 ∈ AB1 by rw [hAB1eq]; simp)
      have hm2 : M1 - offset k2 ∈ AB2.image (fun k => M2 - offset k) := hABeq ▸ Finset.mem_image_of_mem (fun k => M1 - offset k) (show k2 ∈ AB1 by rw [hAB1eq]; simp)
      rcases Finset.mem_image.mp hm1 with ⟨m1, _, hm1eq⟩
      rcases Finset.mem_image.mp hm2 with ⟨m2, _, hm2eq⟩
      have hM12 : M1 = M2 := unique_line (M1 - offset k1) (M1 - offset k2) M1 M2
        (fun h => hk12 (hsub_inj M1 h)) ⟨k1, by abel⟩ ⟨k2, by abel⟩
        ⟨m1, by rw [← hm1eq]; abel⟩ ⟨m2, by rw [← hm2eq]; abel⟩
      have hir12 : ir1 = ir2 := by
        have hreq := unique_inter l1 M1 (l1 - offset ir1) (l1 - offset ir2) hM1l1.symm
          ⟨ir1, by abel⟩ ⟨j1, by dsimp only [M1]⟩ ⟨ir2, by abel⟩ ⟨j2, by rw [hM12]⟩
        exact hsub_inj l1 hreq
      subst hir12
      have hj12 : j1 = j2 := by
        have : offset j1 = offset j2 := add_left_cancel hM12
        exact offset_inj this
      subst hj12
      have hAB12 : AB1 = AB2 := by
        ext k
        constructor
        · intro hk
          have : M1 - offset k ∈ AB2.image (fun k => M1 - offset k) := hABeq ▸ Finset.mem_image_of_mem _ hk
          rcases Finset.mem_image.mp this with ⟨k', hk', hkk'⟩
          exact (hsub_inj M1 hkk') ▸ hk'
        · intro hk
          have : M1 - offset k ∈ AB1.image (fun k => M1 - offset k) := hABeq.symm ▸ Finset.mem_image_of_mem _ hk
          rcases Finset.mem_image.mp this with ⟨k', hk', hkk'⟩
          exact (hsub_inj M1 hkk') ▸ hk'
      subst hAB12
      rfl
    let LocalFive := { c : Finset (Fin 5) × Fin 5 × Fin 5 × Finset (Fin 5) //
      c.1.card = 3 ∧ c.2.1 ∉ c.1 ∧ c.2.2.1 ≠ c.2.1 ∧ c.2.2.2.card = 2 ∧ c.2.2.1 ∉ c.2.2.2 }
    have hLocalFive : Fintype.card LocalFive = 480 := by
      let e : LocalFive ≃ (Σ (T : { s : Finset (Fin 5) // s.card = 3 }),
          Σ (ir : { i : Fin 5 // i ∉ T.1 }),
          Σ (j : { k : Fin 5 // k ≠ ir.1 }),
          { u : Finset (Fin 5) // u.card = 2 ∧ j.1 ∉ u }) :=
        { toFun := fun ⟨⟨T, ir, j, AB⟩, h1, h2, h3, h4, h5⟩ => ⟨⟨T, h1⟩, ⟨ir, h2⟩, ⟨j, h3⟩, ⟨AB, h4, h5⟩⟩
          invFun := fun ⟨⟨T, h1⟩, ⟨ir, h2⟩, ⟨j, h3⟩, ⟨AB, h4, h5⟩⟩ => ⟨⟨T, ir, j, AB⟩, h1, h2, h3, h4, h5⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e]
      simp only [Fintype.card_sigma]
      have hcard4 : ∀ j : Fin 5, Fintype.card { u : Finset (Fin 5) // u.card = 2 ∧ j ∉ u } = 6 := by
        intro j
        have heq : Fintype.card { u : Finset (Fin 5) // u.card = 2 ∧ j ∉ u } =
            ((Finset.univ.erase j).powersetCard 2).card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨u, hu2, hju⟩ => ⟨u, Finset.mem_powersetCard.mpr ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hju (h ▸ hx), Finset.mem_univ _⟩, hu2⟩⟩
              invFun := fun ⟨u, hu⟩ => ⟨u, (Finset.mem_powersetCard.mp hu).2, fun hj => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hu).1 hj)).1 rfl⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [heq, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
        decide
      have hcard3 : ∀ ir : Fin 5, Fintype.card { k : Fin 5 // k ≠ ir } = 4 := by
        intro ir
        have heq : Fintype.card { k : Fin 5 // k ≠ ir } = (Finset.univ.erase ir).card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨k, hk⟩ => ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩⟩
              invFun := fun ⟨k, hk⟩ => ⟨k, (Finset.mem_erase.mp hk).1⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [heq, Finset.card_erase_of_mem (Finset.mem_univ ir), Finset.card_univ, Fintype.card_fin]
      have hcard2 : ∀ T : { s : Finset (Fin 5) // s.card = 3 }, Fintype.card { i : Fin 5 // i ∉ T.1 } = 2 := by
        intro T
        have heq : Fintype.card { i : Fin 5 // i ∉ T.1 } = (Finset.univ \ T.1).card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨i, hi⟩ => ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
              invFun := fun ⟨i, hi⟩ => ⟨i, (Finset.mem_sdiff.mp hi).2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [heq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, T.2]
      have hcard1 : Fintype.card { s : Finset (Fin 5) // s.card = 3 } = 10 := by
        have heq : Fintype.card { s : Finset (Fin 5) // s.card = 3 } =
            ((Finset.univ : Finset (Fin 5)).powersetCard 3).card := by
          rw [← Fintype.card_coe]
          refine Fintype.card_congr
            { toFun := fun ⟨s, hs⟩ => ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hs⟩⟩
              invFun := fun ⟨s, hs⟩ => ⟨s, (Finset.mem_powersetCard.mp hs).2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
        rw [heq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        decide
      simp only [hcard4, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard3, hcard2, hcard1]
    have hFiveCard : Fintype.card FiveCode = 10080 := by
      let e : FiveCode ≃ Fin 21 × LocalFive :=
        { toFun := fun ⟨⟨l, rest⟩, h⟩ => ⟨l, ⟨rest, h⟩⟩
          invFun := fun ⟨l, ⟨rest, h⟩⟩ => ⟨⟨l, rest⟩, h⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, hLocalFive]
    let input : Finset (Fin 21) → Fin 42 → Bool := fun P v =>
      decide ((∃ p ∈ P, point p = v) ∨ (∃ l, line l = v ∧ ∀ q ∈ P, ¬ Inc q l))
    have point_inj : Function.Injective point := fun _ _ h => Fin.ext (congrArg (fun v : Fin 42 => v.val) h)
    have line_inj : Function.Injective line := by
      intro a b h; apply Fin.ext; have hv := congrArg Fin.val h; change 21 + a.val = 21 + b.val at hv; omega
    have point_ne_line : ∀ p l : Fin 21, point p ≠ line l := by
      intro p l h; have hv := congrArg Fin.val h; change p.val = 21 + l.val at hv; omega
    have input_point : ∀ (P : Finset (Fin 21)) (p : Fin 21), input P (point p) = true ↔ p ∈ P := by
      intro P p; simp only [input, decide_eq_true_eq]
      constructor
      · rintro (⟨q, hq, he⟩ | ⟨l, he, _⟩)
        · exact (point_inj he) ▸ hq
        · exact (point_ne_line p l he.symm).elim
      · exact fun h => Or.inl ⟨p, h, rfl⟩
    have input_line : ∀ (P : Finset (Fin 21)) (l : Fin 21), input P (line l) = true ↔ ∀ q ∈ P, ¬ Inc q l := by
      intro P l; simp only [input, decide_eq_true_eq]
      constructor
      · rintro (⟨p, _, he⟩ | ⟨k, he, h⟩)
        · exact (point_ne_line p l he).elim
        · exact (line_inj he) ▸ h
      · exact fun h => Or.inr ⟨l, rfl, h⟩
    have negative : ∀ P : Finset (Fin 21), C.eval (List.ofFn (input P)) ≠ true := by
      intro P h
      obtain ⟨u, v, he, hu, hv⟩ := (hc _).mp h
      obtain ⟨p, l, rfl, rfl, hi⟩ := edge_forward he
      exact (input_line P l).mp hv p ((input_point P p).mp hu) hi
    have union_positive : ∀ {P Q : Finset (Fin 21)}, IsClosed P → IsClosed Q → P ≠ Q →
        C.eval (List.ofFn fun i => input P i || input Q i) = true := by
      intro P Q hP hQ hne
      by_cases hPQ : P ⊆ Q
      · have hQP : ¬ Q ⊆ P := fun h => hne (Finset.Subset.antisymm hPQ h)
        obtain ⟨q, hqQ, hqP⟩ : ∃ q ∈ Q, q ∉ P := by simpa [Finset.subset_iff] using hQP
        obtain ⟨l, he, hl⟩ := hP q hqP
        exact (hc _).mpr ⟨point q, line l, edge_backward he,
          by simp [(input_point Q q).mpr hqQ], by simp [(input_line P l).mpr hl]⟩
      · obtain ⟨p, hpP, hpQ⟩ : ∃ p ∈ P, p ∉ Q := by simpa [Finset.subset_iff] using hPQ
        obtain ⟨l, he, hl⟩ := hQ p hpQ
        exact (hc _).mpr ⟨point p, line l, edge_backward he,
          by simp [(input_point P p).mpr hpP], by simp [(input_line Q l).mpr hl]⟩
    let ClosedFam := ((Finset.univ : Finset (Fin 21)).powersetCard 3) ⊕
      ((Finset.univ : Finset (Fin 21)).powersetCard 4) ⊕ FiveCode
    let toSet : ClosedFam → Finset (Fin 21)
      | Sum.inl x => x.val
      | Sum.inr (Sum.inl y) => y.val
      | Sum.inr (Sum.inr z) => mkFive z
    have toSet_closed : ∀ u : ClosedFam, IsClosed (toSet u) := by
      rintro (x | y | z)
      · exact closed_of_card_le_four x.val (by have := (Finset.mem_powersetCard.mp x.property).2; omega)
      · exact closed_of_card_le_four y.val (by have := (Finset.mem_powersetCard.mp y.property).2; omega)
      · exact mkFive_closed z
    have toSet_inj : Function.Injective toSet := by
      rintro (x1 | y1 | z1) (x2 | y2 | z2) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · dsimp only [toSet] at h
        have h1 := (Finset.mem_powersetCard.mp x1.property).2
        have h2 := (Finset.mem_powersetCard.mp y2.property).2
        have := congrArg Finset.card h; omega
      · dsimp only [toSet] at h
        have h1 := (Finset.mem_powersetCard.mp x1.property).2
        have h2 := mkFive_card z2
        have := congrArg Finset.card h; omega
      · dsimp only [toSet] at h
        have h1 := (Finset.mem_powersetCard.mp y1.property).2
        have h2 := (Finset.mem_powersetCard.mp x2.property).2
        have := congrArg Finset.card h; omega
      · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext h)
      · dsimp only [toSet] at h
        have h1 := (Finset.mem_powersetCard.mp y1.property).2
        have h2 := mkFive_card z2
        have := congrArg Finset.card h; omega
      · dsimp only [toSet] at h
        have h1 := mkFive_card z1
        have h2 := (Finset.mem_powersetCard.mp x2.property).2
        have := congrArg Finset.card h; omega
      · dsimp only [toSet] at h
        have h1 := mkFive_card z1
        have h2 := (Finset.mem_powersetCard.mp y2.property).2
        have := congrArg Finset.card h; omega
      · exact congrArg (Sum.inr ∘ Sum.inr) (mkFive_inj h)
    let k := C.gates.countP isAnd
    let f : ClosedFam → Fin k → Bool := fun u i =>
      (trace C.gates (List.ofFn (input (toSet u)))).getD i.val false
    have hf : Function.Injective f := by
      intro u v he
      by_contra hn
      have hne : toSet u ≠ toSet v := fun h => hn (toSet_inj h)
      have plen := traceLength C.gates (List.ofFn (input (toSet u)))
      have qlen := traceLength C.gates (List.ofFn (input (toSet v)))
      have ht : trace C.gates (List.ofFn (input (toSet u))) =
          trace C.gates (List.ofFn (input (toSet v))) := by
        apply List.ext_getElem (plen.trans qlen.symm)
        intro i hi hj
        have hz := congrFun he (⟨i, by simpa only [k, ← plen] using hi⟩ : Fin k)
        simpa only [f, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hz
      exact (evalBounds _ _ ht (union_positive (toSet_closed u) (toSet_closed v) hne)).elim
        (negative (toSet u)) (negative (toSet v))
    have hcard := Fintype.card_le_of_injective f hf
    have hFamCard : Fintype.card ClosedFam = 17395 := by
      simp only [ClosedFam, Fintype.card_sum, Fintype.card_coe, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, hFiveCard]
      decide
    simp only [hFamCard, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
    have hk14 : k ≤ 14 := by
      have : k = {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := count_eq
      omega
    have hpow : 2 ^ k ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) hk14
    omega
