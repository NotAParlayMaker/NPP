import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 50000 in
theorem PEqualNP.Outside.R_meta_4835_29
  (faceBound :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ (v : Fin 11) (E : Circuit), v.val < 4 → IsAO2 11 E →
      (∀ x : Fin 11 → Bool, x v = false → circuitFun 11 E x = graphFun G ∅ x) →
      19 ≤ E.size)
  (sharedTypeA :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card → D.size ≤ 21 →
      2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card <
        2 * (Ustar G D).card →
      (∀ u : Fin 11, u.val < 4 →
        ((Finset.range D.size).filter (fun k => u.val ∈ (gateAt D k).inputs)).card ≤ 2) →
      (∃ (v : Fin 11) (h g r : ℕ), v.val < 4 ∧ h < g ∧ g < r ∧ r < D.size ∧
        (gateAt D g).op = GateOp.and ∧ (gateAt D r).op = GateOp.or ∧
        (∀ k < D.size, v.val ∈ (gateAt D k).inputs ↔ k = g) ∧
        (∀ k < D.size, 11 + g ∈ (gateAt D k).inputs ↔ k = r) ∧
        11 + h ∈ (gateAt D g).inputs ∧
        (∃ k < D.size, k ≠ g ∧ 11 + h ∈ (gateAt D k).inputs) ∧
        (∀ w : Fin 11, G.Adj v w → gateVal 11 D h (pairInput w w) = true)) →
      False)
  (allTypeB :
    let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
      (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card → D.size ≤ 21 →
      2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card <
        2 * (Ustar G D).card →
      (∀ v : Fin 11, v.val < 4 →
        (∀ k < D.size, v.val ∈ (gateAt D k).inputs → (gateAt D k).op = GateOp.or) ∧
        1 ≤ ((Finset.range D.size).filter (fun k => v.val ∈ (gateAt D k).inputs)).card ∧
        ((Finset.range D.size).filter (fun k => v.val ∈ (gateAt D k).inputs)).card ≤ 2 ∧
        (∀ h < D.size, (∀ k < D.size, v.val ∈ (gateAt D k).inputs ↔ k = h) →
          h ∈ orN G D \ lam G D) ∧
        (∀ t ∈ tops G D, ∀ b : Fin 2, side D t b = {v} →
          ∃ m ∈ orN G D \ lam G D, orIn 11 D (11 + m) = {v})) →
      False) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             ∃ (x8 : Fin (11 : ℕ)),               ↑x8 < (4 : ℕ) ∧                 have x9 : ℕ → Prop := fun (x9 : ℕ) => ∃ x10 < (11 : ℕ) + x9, ∀ (x11 : Fin (11 : ℕ) → Bool), x11 x8 = Bool.false → PEqualNP.ReadTwo.wval x2 x11 ((11 : ℕ) + x9) = PEqualNP.ReadTwo.wval x2 x11 x10;                 ∃ (x10 : ℕ) (x11 : ℕ) (x12 : ℕ), x10 < x11 ∧ x11 < x12 ∧ x12 < x2.size ∧ x9 x10 ∧ x9 x11 ∧ x9 x12 := by
  intro G D hm ht hj hsz hnum
  letI : DecidableEq GateOp := gateOpDecEq
  have mem_orIn : ∀ (w : ℕ) (i : Fin 11), i ∈ orIn 11 D w ↔
      (i : ℕ) = w ∨ ∃ k < D.gates.length,
        OrReaches 11 D w k ∧ (gateAt D k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt D k).inputs :=
    fun _ i => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
  have opnd_def : ∀ (k : ℕ) (b : Fin 2), opnd D k b = (gateAt D k).inputs.getD b 0 :=
    fun _ _ => rfl
  have mem_orN : ∀ (k : ℕ), k ∈ orN G D ↔
      k < D.gates.length ∧ (gateAt D k).op = GateOp.or ∧ ¬ BelowF G D k :=
    fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
  have mem_tops : ∀ (k : ℕ), k ∈ tops G D ↔
      k < D.gates.length ∧ (gateAt D k).op = GateOp.and ∧ BelowF G D k :=
    fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
  have mem_lam : ∀ (k : ℕ), k ∈ lam G D ↔
      k ∈ orN G D ∧ (orIn 11 D (opnd D k 0)).Nonempty ∧ (orIn 11 D (opnd D k 1)).Nonempty ∧
      ∃ a ∈ tops G D, ∃ b : Fin 2, (side (n := 11) D a (1 - b)).card = 1 ∧
        OrReaches 11 D (opnd D a b) k :=
    fun _ => Finset.mem_filter
  classical
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
      (gs.foldl stepWire w).getD (w.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
    induction gs generalizing w j with
    | nil => simp at hj
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases j with
      | zero =>
        have h1 : w.length < (stepWire w g).length := by simp [stepWire]
        rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
        simp only [List.getElem_cons_zero]
        have h2 : (stepWire w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          simp [stepWire, List.getD_eq_getElem?_getD]
        rw [h2]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
          simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
      | succ j =>
        have hj' : j < gs.length := by simpa using hj
        have key := ih (stepWire w g) j hj'
        have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hl] at key
        have e : w.length + (j + 1) = w.length + 1 + j := by omega
        simp only [List.getElem_cons_succ]
        rw [e]
        exact key

  let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

  have eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

  have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    simp [List.getD_eq_getElem?_getD, hj]

  have gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    rw [gateAt_eq hj]; exact List.getElem_mem hj

  have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
      val C x u = x.getD u false := by
    unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

  have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
      (hu : n + C.gates.length ≤ u) : val C x u = false := by
    unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

  have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
      (hj : j < C.gates.length) :
      val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then val C x i else false) := by
    subst hx
    rw [gateAt_eq hj]
    exact foldl_getD_gate C.gates x j hj

  let OpMono (R : Bool → Bool → Prop) : Prop :=
    ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
      (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

  have opMono_eq : OpMono Eq := by
    intro op _ l f g h
    rw [List.map_congr_left h]

  have val_prefix {n : ℕ} {C1 C2 : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
      (hm1 : m ≤ C1.gates.length) (hm2 : m ≤ C2.gates.length)
      (hg : ∀ k < m, gateAt C2 k = gateAt C1 k) : ∀ u, u < n + m → val C2 x u = val C1 x u := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      by_cases hun : u < n
      · rw [val_input hx hun, val_input hx hun]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < m := by omega
        rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < n + k
        · rw [ite_eq_left hi, ite_eq_left hi]; exact ih i hi (by omega)
        · rw [ite_eq_right hi, ite_eq_right hi]

  let aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

  let aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

  let bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
    ⟨(List.range (C.gates.length - 1)).map (fun k =>
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
      aliasWire (n + r) i C.output⟩

  have bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

  have bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
      (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

  have gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
      gateAt (bypass n C r i) k =
        if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
    have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
    rw [gateAt_eq hk']
    simp [bypass]

  have bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
      (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
    apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
    intro k hk
    rw [gateAt_bypass (by omega), ite_eq_left hk]

  have aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

  have aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

  have aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
    unfold aliasWire; rw [ite_eq_right (by omega), ite_eq_left hu]

  have bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
      {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
      (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
        R (val C x (n + r)) (val C x i)) :
      ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hne
      by_cases hlt : u < n + r
      · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
      · rw [aliasWire_gt_self (by omega)]
        by_cases hge : n + C.gates.length ≤ u
        · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
          have hk1 : k + 1 < C.gates.length := by omega
          have hkr : ¬ k < r := by omega
          have e : n + (k + 1) - 1 = n + k := by omega
          rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
            gateAt_bypass (by omega), ite_eq_right hkr]
          simp only [aliasGate, List.map_map]
          refine hmono _ (hAO _ hk1) _ _ _ ?_
          intro i' hi'
          simp only [Function.comp_apply]
          by_cases h1 : i' = n + r
          · subst h1
            rw [aliasWire_self, ite_eq_left (by omega)]
            have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
              rcases hi with hi | hi
              · rw [ite_eq_left (by omega), bypass_val_lt hx hr i hi]
              · rw [ite_eq_right (by omega), val_ge hx hi]
            rw [hgi]
            exact hR ⟨k + 1, by omega, hk1, hi'⟩
          · by_cases h2 : i' < n + r
            · rw [aliasWire_lt_self h2, ite_eq_left (by omega), ite_eq_left (by omega),
                bypass_val_lt hx hr i' h2]
              exact hrefl _
            · by_cases h3 : i' < n + (k + 1)
              · have key := ih i' h3 h1
                rw [aliasWire_gt_self (by omega)] at key
                rw [aliasWire_gt_self (by omega), ite_eq_left h3, ite_eq_left (by omega)]
                exact key
              · rw [aliasWire_gt_self (by omega), ite_eq_right h3, ite_eq_right (by omega)]
                exact hrefl _

  have bypass_ok {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
      (hAO : ∀ k < C.gates.length,
        (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
      {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r)
      (hR : ((∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) ∨
        C.output = n + r) → val C x (n + r) = val C x i) :
      (bypass n C r i).eval x = C.eval x := by
    rw [eval_eq_val, eval_eq_val, bypass_output]
    by_cases h : C.output = n + r
    · rw [h, aliasWire_self, bypass_val_lt hx hr i hi]
      exact (hR (Or.inr h)).symm
    · exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr (Or.inl hi)
        (fun hk => hR (Or.inl hk)) _ h).symm

  have bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
      ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
        g.inputs.length = g'.inputs.length := by
    intro g hg
    simp only [bypass, List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    split_ifs with h
    · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
    · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

  have aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
      aliasWire w i u < m := by
    unfold aliasWire; split_ifs <;> omega

  have bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
      (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
      ∀ k < (bypass n C r i).gates.length,
        ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
    intro k hk u hu
    rw [bypass_length] at hk
    rw [gateAt_bypass hk] at hu
    split_ifs at hu with h
    · exact hRB k (by omega) u hu
    · simp only [aliasGate, List.mem_map] at hu
      obtain ⟨u', hu', rfl⟩ := hu
      have := hRB (k + 1) (by omega) u' hu'
      exact aliasWire_lt hi (by omega) (by omega)

  have bypass_isAO2 {n : ℕ} {C : Circuit} {r i : ℕ} (hAO : IsAO2 n C) (hi : i < n + r) :
      IsAO2 n (bypass n C r i) := by
    refine ⟨?_, bypass_readsBack hi hAO.2.1, ?_⟩
    · intro g hg
      obtain ⟨g', hmem, hop, _⟩ := bypass_mem g hg
      rw [hop]
      exact hAO.1 g' hmem
    · intro g hg
      obtain ⟨g', hmem, _, hlen⟩ := bypass_mem g hg
      exact hlen.trans (hAO.2.2 g' hmem)

  have dropG : ∀ (C : Circuit) (r w : ℕ), IsAO2 11 C → r < C.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < C.gates.length ∧ 11 + r ∈ (gateAt C k).inputs) ∨ C.output = 11 + r) →
        ∀ x : Fin 11 → Bool, wval C x (11 + r) = wval C x w) →
      ∃ E : Circuit, IsAO2 11 E ∧ E.gates.length + 1 = C.gates.length ∧
        circuitFun 11 E = circuitFun 11 C := by
    intro C r w model hr hw heq
    have ops : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and ∨
        (gateAt C j).op = GateOp.or := fun j hj => model.1 _ (gateAt_mem hj)
    refine ⟨bypass 11 C r w, bypass_isAO2 model hw, ?_, ?_⟩
    · rw [bypass_length]; omega
    · funext x
      exact bypass_ok List.length_ofFn ops hr hw (fun h => heq h x)

  have hAO2 : IsAO2 11 D := hm.1
  have hfun : circuitFun 11 D = graphFun G ∅ := hm.2.1
  have noRep : ∀ r w : ℕ, r < D.gates.length → w < 11 + r →
      (((∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs) ∨ D.output = 11 + r) →
        ∀ x : Fin 11 → Bool, wval D x (11 + r) = wval D x w) → False := by
    intro r w hr hw heq
    obtain ⟨E, mE, lE, fE⟩ := dropG D r w hAO2 hr hw heq
    have hle := hm.2.2 E mE (fE.trans hfun)
    change D.gates.length ≤ E.gates.length at hle
    omega

  have hasReader : ∀ r, r < D.gates.length → D.output ≠ 11 + r →
      ∃ k, r < k ∧ k < D.gates.length ∧ 11 + r ∈ (gateAt D k).inputs := by
    intro r hr hout
    by_contra hno
    refine noRep r 0 hr (by omega) ?_
    rintro (h | h)
    · exact absurd h hno
    · exact absurd h hout

  have hRB : ∀ k < D.gates.length, ∀ u ∈ (gateAt D k).inputs, u < 11 + k := hAO2.2.1
  have hops : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and ∨
      (gateAt D k).op = GateOp.or := fun k hk => hAO2.1 _ (gateAt_mem hk)
  have hlen2 : ∀ k < D.gates.length, (gateAt D k).inputs.length = 2 :=
    fun k hk => hAO2.2.2 _ (gateAt_mem hk)
  have andE : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
    intro a b; cases a <;> cases b <;> rfl
  have orE : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
    intro a b; cases a <;> cases b <;> rfl

  have gsem : ∀ k < D.gates.length, ∃ p q : ℕ, (gateAt D k).inputs = [p, q] ∧ p < 11 + k ∧
      q < 11 + k ∧ (∀ x : Fin 11 → Bool,
        wval D x (11 + k) = (gateAt D k).op.eval [wval D x p, wval D x q]) := by
    intro k hk
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen2 k hk)
    have hp : p < 11 + k := hRB k hk p (by rw [hpq]; simp)
    have hq : q < 11 + k := hRB k hk q (by rw [hpq]; simp)
    refine ⟨p, q, hpq, hp, hq, fun x => ?_⟩
    have hv := val_gate (C := D) (x := List.ofFn x) List.length_ofFn hk
    rw [hpq] at hv
    simp only [List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq] at hv
    exact hv

  have hin : ∀ (v : Fin 11) (x : Fin 11 → Bool), wval D x v.val = x v := by
    intro v x
    have hv := val_input (C := D) (x := List.ofFn x) List.length_ofFn v.isLt
    refine hv.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _

  have zv : ∀ (v : Fin 11) (x : Fin 11 → Bool), x v = false → wval D x v.val = false :=
    fun v x hx => (hin v x).trans hx

  have zand : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → (gateAt D k).op = GateOp.and →
      u ∈ (gateAt D k).inputs → (∀ x : Fin 11 → Bool, x v = false → wval D x u = false) →
      ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + k) = false := by
    intro v k u hk hop hu hz x hx
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    rw [hpq, List.mem_pair] at hu
    rw [hs x, hop, andE]
    have hzz := hz x hx
    rcases hu with h | h <;> subst h <;> simp [hzz]

  have rep1 : ∀ (v : Fin 11) (k u : ℕ), k < D.gates.length → u ∈ (gateAt D k).inputs →
      (∀ x : Fin 11 → Bool, x v = false → wval D x u = false) →
      ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + k) = wval D x w := by
    intro v k u hk hu hz
    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
    have hu' := hu
    rw [hpq, List.mem_pair] at hu'
    rcases hops k hk with hop | hop
    · refine ⟨u, hRB k hk u hu, fun x hx => ?_⟩
      rw [zand v k u hk hop hu hz x hx, hz x hx]
    · rcases hu' with h | h
      · subst h
        refine ⟨q, hq, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]
      · subst h
        refine ⟨p, hp, fun x hx => ?_⟩
        have hzz := hz x hx
        rw [hs x, hop, orE]
        simp [hzz]

  have outNZ : ∀ (v : Fin 11) (g : ℕ), v.val < 4 →
      (∀ x : Fin 11 → Bool, x v = false → wval D x (11 + g) = false) → D.output ≠ 11 + g := by
    intro v g hv hz hout
    have e1 := hz (fun i : Fin 11 => decide (4 ≤ i.val)) (by simpa using hv)
    have e0 : graphFun G ∅ (fun i : Fin 11 => decide (4 ≤ i.val)) = true := by
      dsimp [G]; decide +kernel
    have e2 : circuitFun 11 D (fun i : Fin 11 => decide (4 ≤ i.val)) = true := by
      rw [hfun]; exact e0
    have e3 : circuitFun 11 D (fun i : Fin 11 => decide (4 ≤ i.val)) =
        wval D (fun i : Fin 11 => decide (4 ≤ i.val)) D.output := rfl
    rw [e3, hout, e1] at e2
    exact Bool.false_ne_true e2

  have finGoal : ∀ (v : Fin 11), v.val < 4 → ∀ a b c : ℕ, a ≠ b → a ≠ c → b ≠ c →
      a < D.gates.length → b < D.gates.length → c < D.gates.length →
      (∃ w < 11 + a, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + a) = wval D x w) →
      (∃ w < 11 + b, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + b) = wval D x w) →
      (∃ w < 11 + c, ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + c) = wval D x w) →
      ∃ x8 : Fin 11, x8.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.size ∧
        (∃ w < 11 + i, ∀ x : Fin 11 → Bool, x x8 = false → wval D x (11 + i) = wval D x w) ∧
        (∃ w < 11 + j, ∀ x : Fin 11 → Bool, x x8 = false → wval D x (11 + j) = wval D x w) ∧
        (∃ w < 11 + k, ∀ x : Fin 11 → Bool, x x8 = false → wval D x (11 + k) = wval D x w) := by
    intro v hv a b c hab hac hbc ha hb hc ra rb rc
    refine ⟨v, hv, ?_⟩
    rcases lt_or_gt_of_ne hab with o1 | o1 <;> rcases lt_or_gt_of_ne hac with o2 | o2 <;>
      rcases lt_or_gt_of_ne hbc with o3 | o3 <;>
      first
      | exact ⟨a, b, c, by omega, by omega, hc, ra, rb, rc⟩
      | exact ⟨a, c, b, by omega, by omega, hb, ra, rc, rb⟩
      | exact ⟨b, a, c, by omega, by omega, hc, rb, ra, rc⟩
      | exact ⟨b, c, a, by omega, by omega, ha, rb, rc, ra⟩
      | exact ⟨c, a, b, by omega, by omega, hb, rc, ra, rb⟩
      | exact ⟨c, b, a, by omega, by omega, ha, rc, rb, ra⟩
      | (exfalso; omega)

  have pairInput_def : ∀ u w z : Fin 11, pairInput u w z = decide (z = u ∨ z = w) := fun _ _ _ => rfl

  have graphFun_def : ∀ x : Fin 11 → Bool,
      graphFun G ∅ x = (decide (∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ||
        decide (∃ a b : Fin 11, G.Adj a b ∧ x a = true ∧ x b = true)) := fun _ => rfl

  have graphFun_pair_self : ∀ w : Fin 11, graphFun G ∅ (pairInput w w) = false := by
    intro w
    rw [graphFun_def]
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_exists, not_and]
    refine ⟨fun a ha => by simp at ha, fun a b hab ha hb => ?_⟩
    rw [pairInput_def] at ha hb
    simp only [decide_eq_true_eq, or_self] at ha hb
    subst ha; subst hb
    exact G.loopless.irrefl _ hab

  have graphFun_adj_true : ∀ (u w : Fin 11) (x : Fin 11 → Bool),
      G.Adj u w → x u = true → x w = true → graphFun G ∅ x = true := by
    intro u w x hadj hu hw
    rw [graphFun_def]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨u, w, hadj, hu, hw⟩

  have graphFun_pair_imp_adj : ∀ u w : Fin 11, graphFun G ∅ (pairInput u w) = true → G.Adj u w := by
    intro u w h
    rw [graphFun_def] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and,
      exists_false, false_or] at h
    obtain ⟨a, b, hab, ha, hb⟩ := h
    rw [pairInput_def] at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim

  have outNeInput : ∀ v : Fin 11, D.output ≠ v.val := by
    intro v hout
    have h1 : circuitFun 11 D (pairInput v v) = false := by
      rw [hfun]; exact graphFun_pair_self v
    have h2 : circuitFun 11 D (pairInput v v) = wval D (pairInput v v) D.output := rfl
    rw [h2, hout, hin v (pairInput v v), pairInput_def] at h1
    simp at h1

  have twoNbrs : ∀ v : Fin 11, v.val < 4 → ∃ a b : Fin 11, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
    dsimp [G]; decide +kernel

  have noC4Deg2 : ∀ v a b w : Fin 11, v.val < 4 → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → w = v := by
    dsimp [G]; decide +kernel

  have deg2HasReader : ∀ v : Fin 11, v.val < 4 → ∃ k < D.gates.length, v.val ∈ (gateAt D k).inputs := by
    intro v hv
    by_contra hno
    push Not at hno
    obtain ⟨a, _, _, hva, _⟩ := twoNbrs v hv
    have hav : a ≠ v := G.ne_of_adj hva.symm
    have hsame : ∀ u < 11 + D.gates.length, u ≠ v.val →
        wval D (pairInput v a) u = wval D (pairInput a a) u := by
      intro u
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        intro hu hnev
        by_cases hun : u < 11
        · let ui : Fin 11 := ⟨u, hun⟩
          change wval D (pairInput v a) ui.val = wval D (pairInput a a) ui.val
          rw [hin ui, hin ui, pairInput_def, pairInput_def]
          have hne : ui ≠ v := fun h => hnev (congrArg Fin.val h)
          simp [hne]
        · obtain ⟨k, rfl⟩ : ∃ k, u = 11 + k := ⟨u - 11, by omega⟩
          have hk : k < D.gates.length := by omega
          obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
          have hnv : v.val ∉ (gateAt D k).inputs := hno k hk
          rw [hpq, List.mem_pair, not_or] at hnv
          rw [hs, hs, ih p (by omega) (by omega) (Ne.symm hnv.1),
            ih q (by omega) (by omega) (Ne.symm hnv.2)]
    have hout : circuitFun 11 D (pairInput v a) = circuitFun 11 D (pairInput a a) := by
      change wval D (pairInput v a) D.output = wval D (pairInput a a) D.output
      by_cases hlt : D.output < 11 + D.gates.length
      · exact hsame D.output hlt (outNeInput v)
      · change val D (List.ofFn (pairInput v a)) D.output = val D (List.ofFn (pairInput a a)) D.output
        rw [val_ge (C := D) List.length_ofFn (by omega), val_ge (C := D) List.length_ofFn (by omega)]
    rw [hfun, graphFun_adj_true v a (pairInput v a) hva (by rw [pairInput_def]; simp)
      (by rw [pairInput_def]; simp), graphFun_pair_self a] at hout
    cases hout

  have card_le_two_of_no3 : ∀ (S : Finset ℕ),
      (∀ i j k : ℕ, i < j → j < k → i ∈ S → j ∈ S → k ∉ S) → S.card ≤ 2 := by
    intro S hno3
    by_contra hgt
    have h3 : 3 ≤ S.card := by omega
    obtain ⟨T, hTS, hT3⟩ := Finset.exists_subset_card_eq h3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT3
    have ha : a ∈ S := hTS (by simp)
    have hb : b ∈ S := hTS (by simp)
    have hc : c ∈ S := hTS (by simp)
    rcases lt_or_gt_of_ne hab with o1 | o1 <;> rcases lt_or_gt_of_ne hac with o2 | o2 <;>
      rcases lt_or_gt_of_ne hbc with o3 | o3 <;>
      first
      | exact hno3 a b c (by omega) (by omega) ha hb hc
      | exact hno3 a c b (by omega) (by omega) ha hc hb
      | exact hno3 b a c (by omega) (by omega) hb ha hc
      | exact hno3 b c a (by omega) (by omega) hb hc ha
      | exact hno3 c a b (by omega) (by omega) hc ha hb
      | exact hno3 c b a (by omega) (by omega) hc hb ha
      | omega

  by_cases hC : ∃ v : Fin 11, v.val < 4 ∧ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < D.gates.length ∧
      v.val ∈ (gateAt D i).inputs ∧ v.val ∈ (gateAt D j).inputs ∧ v.val ∈ (gateAt D k).inputs
  · obtain ⟨v, hv, i, j, k, hij, hjk, hk, hi, hj', hk'⟩ := hC
    exact finGoal v hv i j k (by omega) (by omega) (by omega) (by omega) (by omega) hk
      (rep1 v i v.val (by omega) hi (zv v)) (rep1 v j v.val (by omega) hj' (zv v))
      (rep1 v k v.val hk hk' (zv v))
  · have hcard2 : ∀ u : Fin 11, u.val < 4 →
        ((Finset.range D.size).filter (fun k => u.val ∈ (gateAt D k).inputs)).card ≤ 2 := by
      intro u hu
      apply card_le_two_of_no3
      intro i j k hij hjk hi hj' hk'
      simp only [Finset.mem_filter, Finset.mem_range] at hi hj' hk'
      exact hC ⟨u, hu, i, j, k, hij, hjk, hk'.1, hi.2, hj'.2, hk'.2⟩
    by_cases hA : ∃ v : Fin 11, v.val < 4 ∧ ∃ g, g < D.gates.length ∧
        (gateAt D g).op = GateOp.and ∧ v.val ∈ (gateAt D g).inputs
    · obtain ⟨v, hv, g, hg, hgop, hgv⟩ := hA
      have zg := zand v g v.val hg hgop hgv (zv v)
      have rg := rep1 v g v.val hg hgv (zv v)
      obtain ⟨r, hgr, hr, hrg⟩ := hasReader g hg (outNZ v g hv zg)
      have rr := rep1 v r (11 + g) hr hrg zg
      rcases hops r hr with hrop | hrop
      · have zr := zand v r (11 + g) hr hrop hrg zg
        obtain ⟨s, hrs, hs, hsr⟩ := hasReader r hr (outNZ v r hv zr)
        exact finGoal v hv g r s (by omega) (by omega) (by omega) hg hr hs rg rr
          (rep1 v s (11 + r) hs hsr zr)
      · by_cases hB : ∃ k, k < D.gates.length ∧ k ≠ g ∧ k ≠ r ∧
            (v.val ∈ (gateAt D k).inputs ∨ 11 + g ∈ (gateAt D k).inputs)
        · obtain ⟨k, hk, hkg, hkr, hkin⟩ := hB
          have rk : ∃ w < 11 + k, ∀ x : Fin 11 → Bool, x v = false →
              wval D x (11 + k) = wval D x w := by
            rcases hkin with h | h
            · exact rep1 v k v.val hk h (zv v)
            · exact rep1 v k (11 + g) hk h zg
          exact finGoal v hv g r k (by omega) (Ne.symm hkg) (Ne.symm hkr) hg hr hk rg rr rk
        · have hvr : v.val ∉ (gateAt D r).inputs := by
            intro hvr
            refine noRep r v.val hr (by omega) (fun _ x => ?_)
            obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem r hr
            have hvr' := hvr
            have hrg' := hrg
            rw [hpq, List.mem_pair] at hvr' hrg'
            rw [hs x, hrop, orE]
            cases hxv : wval D x v.val with
            | false =>
              have hz2 : wval D x (11 + g) = false := by
                obtain ⟨p', q', hpq', _, _, hs'⟩ := gsem g hg
                have hgv' := hgv
                rw [hpq', List.mem_pair] at hgv'
                rw [hs' x, hgop, andE]
                rcases hgv' with h | h <;> subst h <;> simp [hxv]
              rcases hvr' with h | h <;> rcases hrg' with h' | h' <;>
                first
                | (exfalso; omega)
                | (subst h; subst h'; simp [hxv, hz2])
            | true =>
              rcases hvr' with h | h <;> rcases hrg' with h' | h' <;>
                first
                | (exfalso; omega)
                | (subst h; subst h'; simp [hxv])
          have u1 : ∀ k < D.size, (v.val ∈ (gateAt D k).inputs ↔ k = g) := by
            intro k hk
            constructor
            · intro h
              by_contra hne
              by_cases hkr : k = r
              · exact hvr (hkr ▸ h)
              · exact hB ⟨k, hk, hne, hkr, Or.inl h⟩
            · intro h; rw [h]; exact hgv
          have u2 : ∀ k < D.size, (11 + g ∈ (gateAt D k).inputs ↔ k = r) := by
            intro k hk
            constructor
            · intro h
              by_contra hne
              have hkg : k ≠ g := fun e => by have := hRB k hk _ h; omega
              exact hB ⟨k, hk, hkg, hne, Or.inr h⟩
            · intro h; rw [h]; exact hrg
          obtain ⟨gp, gq, hgpq, hgp, hgq, hgs⟩ := gsem g hg
          have hgv' := hgv
          rw [hgpq, List.mem_pair] at hgv'
          obtain ⟨u, hu_lt, hu_mem, hu_sem⟩ : ∃ u < 11 + g, u ∈ (gateAt D g).inputs ∧
              ∀ x : Fin 11 → Bool, wval D x (11 + g) = (wval D x v.val && wval D x u) := by
            rcases hgv' with h | h
            · refine ⟨gq, hgq, by rw [hgpq]; simp, fun x => ?_⟩
              rw [hgs x, hgop, andE, h]
            · refine ⟨gp, hgp, by rw [hgpq]; simp, fun x => ?_⟩
              rw [hgs x, hgop, andE, h, Bool.and_comm]
          have hu_ne_v : u ≠ v.val := by
            intro huv
            refine noRep g v.val hg (by omega) (fun _ x => ?_)
            rw [hu_sem x, huv, Bool.and_self]
          have hu_true_nbr : ∀ w : Fin 11, G.Adj v w → wval D (pairInput w w) u = true := by
            intro w hvw
            by_contra hfalse
            have huf : wval D (pairInput w w) u = false := Bool.eq_false_iff.mpr hfalse
            have hsame_lt : ∀ z < 11 + g, z ≠ v.val →
                wval D (pairInput v w) z = wval D (pairInput w w) z := by
              intro z
              induction z using Nat.strong_induction_on with
              | _ z ih =>
                intro hz hnev
                by_cases hzn : z < 11
                · let zi : Fin 11 := ⟨z, hzn⟩
                  change wval D (pairInput v w) zi.val = wval D (pairInput w w) zi.val
                  rw [hin zi, hin zi, pairInput_def, pairInput_def]
                  have hne : zi ≠ v := fun h => hnev (congrArg Fin.val h)
                  simp [hne]
                · obtain ⟨k, rfl⟩ : ∃ k, z = 11 + k := ⟨z - 11, by omega⟩
                  have hk : k < D.gates.length := by omega
                  obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
                  have hnv : v.val ∉ (gateAt D k).inputs := fun hm => by
                    have := (u1 k hk).mp hm; omega
                  rw [hpq, List.mem_pair, not_or] at hnv
                  rw [hs, hs, ih p (by omega) (by omega) (Ne.symm hnv.1),
                    ih q (by omega) (by omega) (Ne.symm hnv.2)]
            have hg_same : wval D (pairInput v w) (11 + g) = wval D (pairInput w w) (11 + g) := by
              rw [hu_sem, hu_sem, hsame_lt u hu_lt hu_ne_v, huf, Bool.and_false, Bool.and_false]
            have hsame_all : ∀ z < 11 + D.gates.length, z ≠ v.val →
                wval D (pairInput v w) z = wval D (pairInput w w) z := by
              intro z
              induction z using Nat.strong_induction_on with
              | _ z ih =>
                intro hz hnev
                by_cases hzn : z < 11
                · exact hsame_lt z (by omega) hnev
                · obtain ⟨k, rfl⟩ : ∃ k, z = 11 + k := ⟨z - 11, by omega⟩
                  by_cases hkg : k = g
                  · subst hkg; exact hg_same
                  · have hk : k < D.gates.length := by omega
                    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
                    have hnv : v.val ∉ (gateAt D k).inputs := fun hm => hkg ((u1 k hk).mp hm)
                    rw [hpq, List.mem_pair, not_or] at hnv
                    rw [hs, hs, ih p (by omega) (by omega) (Ne.symm hnv.1),
                      ih q (by omega) (by omega) (Ne.symm hnv.2)]
            have hout : circuitFun 11 D (pairInput v w) = circuitFun 11 D (pairInput w w) := by
              change wval D (pairInput v w) D.output = wval D (pairInput w w) D.output
              by_cases hlt : D.output < 11 + D.gates.length
              · exact hsame_all D.output hlt (outNeInput v)
              · change val D (List.ofFn (pairInput v w)) D.output = val D (List.ofFn (pairInput w w)) D.output
                rw [val_ge (C := D) List.length_ofFn (by omega),
                  val_ge (C := D) List.length_ofFn (by omega)]
            rw [hfun, graphFun_adj_true v w (pairInput v w) hvw (by rw [pairInput_def]; simp)
              (by rw [pairInput_def]; simp), graphFun_pair_self w] at hout
            cases hout
          have hu_ge11 : 11 ≤ u := by
            by_contra hlt11
            obtain ⟨a, b, hab, hva, hvb⟩ := twoNbrs v hv
            let ui : Fin 11 := ⟨u, by omega⟩
            have ha := hu_true_nbr a hva
            have hb := hu_true_nbr b hvb
            change wval D (pairInput a a) ui.val = true at ha
            change wval D (pairInput b b) ui.val = true at hb
            rw [hin ui, pairInput_def] at ha hb
            simp only [decide_eq_true_eq, or_self] at ha hb
            exact hab (ha.symm.trans hb)
          let h := u - 11
          have h_eq : u = 11 + h := by omega
          have h_lt_g : h < g := by omega
          have hh_mem : 11 + h ∈ (gateAt D g).inputs := h_eq ▸ hu_mem
          have hh_nbr : ∀ w : Fin 11, G.Adj v w → gateVal 11 D h (pairInput w w) = true := by
            intro w hvw
            have := hu_true_nbr w hvw
            rwa [h_eq] at this
          by_cases hshared : ∃ k < D.size, k ≠ g ∧ 11 + h ∈ (gateAt D k).inputs
          · exfalso
            exact sharedTypeA D hm ht hj hsz hnum hcard2
              ⟨v, h, g, r, hv, h_lt_g, hgr, hr, hgop, hrop, u1, u2, hh_mem, hshared, hh_nbr⟩
          · exfalso
            push Not at hshared
            change ∀ k < D.gates.length, k ≠ g → 11 + h ∉ (gateAt D k).inputs at hshared
            have hout_ne_h : D.output ≠ 11 + h := by
              intro hout
              obtain ⟨a, _, _, hva, _⟩ := twoNbrs v hv
              have ha := hh_nbr a hva
              have h1 : circuitFun 11 D (pairInput a a) = false := by
                rw [hfun]; exact graphFun_pair_self a
              have h2 : circuitFun 11 D (pairInput a a) = wval D (pairInput a a) D.output := rfl
              rw [h2, hout] at h1
              change gateVal 11 D h (pairInput a a) = false at h1
              rw [ha] at h1
              cases h1
            obtain ⟨rp, rq, hrpq, hrp, hrq, hrs⟩ := gsem r hr
            have hrg' := hrg
            rw [hrpq, List.mem_pair] at hrg'
            obtain ⟨wr, hwr_lt, hwr_mem, hwr_eq⟩ : ∃ wr < 11 + r, wr ∈ (gateAt D r).inputs ∧
                ∀ x : Fin 11 → Bool, x v = false → wval D x (11 + r) = wval D x wr := by
              rcases hrg' with h' | h'
              · refine ⟨rq, hrq, by rw [hrpq]; simp, fun x hx => ?_⟩
                rw [hrs x, hrop, orE, ← h', zg x hx]; simp
              · refine ⟨rp, hrp, by rw [hrpq]; simp, fun x hx => ?_⟩
                rw [hrs x, hrop, orE, ← h', zg x hx]; simp
            have hwr_ne_h : wr ≠ 11 + h := by
              intro hEq
              have : 11 + h ∈ (gateAt D r).inputs := hEq ▸ hwr_mem
              exact hshared r hr (by omega) this
            let E1 := bypass 11 D r wr
            have mE1 : IsAO2 11 E1 := bypass_isAO2 hAO2 hwr_lt
            have lE1 : E1.gates.length + 1 = D.gates.length := by
              dsimp [E1]; rw [bypass_length]; omega
            have oE1 : ∀ x : Fin 11 → Bool, x v = false → circuitFun 11 E1 x = circuitFun 11 D x := by
              intro x hx
              exact bypass_ok List.length_ofFn hops hr hwr_lt (fun _ => hwr_eq x hx)
            have pE1 : ∀ (x : Fin 11 → Bool) (u0 : ℕ), u0 < 11 + r → wval E1 x u0 = wval D x u0 :=
              fun x u0 hu0 => bypass_val_lt List.length_ofFn hr u0 hu0
            have hE1_out_ne_h : E1.output ≠ 11 + h := by
              change aliasWire (11 + r) wr D.output ≠ 11 + h
              unfold aliasWire
              split_ifs <;> omega
            have hE1_readers_h : ∀ k < E1.gates.length, 11 + h ∈ (gateAt E1 k).inputs → k = g := by
              intro k hk hmem
              have hk' : k < D.gates.length - 1 := by omega
              rw [gateAt_bypass hk'] at hmem
              split_ifs at hmem with hkr
              · by_contra hkg
                exact hshared k (by omega) hkg hmem
              · simp only [aliasGate, List.mem_map] at hmem
                obtain ⟨u', hu', hu'eq⟩ := hmem
                have hne : u' ≠ 11 + h := fun heq => hshared (k + 1) (by omega) (by omega) (heq ▸ hu')
                unfold aliasWire at hu'eq
                split_ifs at hu'eq <;> omega
            let E2 := bypass 11 E1 g v.val
            have mE2 : IsAO2 11 E2 := bypass_isAO2 mE1 (by omega)
            have lE2 : E2.gates.length + 1 = E1.gates.length := by
              dsimp [E2]; rw [bypass_length]; omega
            have opsE1 : ∀ j < E1.gates.length, (gateAt E1 j).op = GateOp.and ∨
                (gateAt E1 j).op = GateOp.or := fun j hj => mE1.1 _ (gateAt_mem hj)
            have oE2 : ∀ x : Fin 11 → Bool, x v = false → circuitFun 11 E2 x = circuitFun 11 E1 x := by
              intro x hx
              refine bypass_ok List.length_ofFn opsE1 (by omega) (by omega) (fun _ => ?_)
              change wval E1 x (11 + g) = wval E1 x v.val
              rw [pE1 x (11 + g) (by omega), pE1 x v.val (by omega), zg x hx, zv v x hx]
            have hE2_out_ne_h : E2.output ≠ 11 + h := by
              change aliasWire (11 + g) v.val E1.output ≠ 11 + h
              unfold aliasWire
              split_ifs <;> omega
            have hE2_no_readers_h : ∀ k < E2.gates.length, 11 + h ∉ (gateAt E2 k).inputs := by
              intro k hk hmem
              have hk' : k < E1.gates.length - 1 := by omega
              rw [gateAt_bypass hk'] at hmem
              split_ifs at hmem with hkg
              · have := hE1_readers_h k (by omega) hmem; omega
              · simp only [aliasGate, List.mem_map] at hmem
                obtain ⟨u', hu', hu'eq⟩ := hmem
                have hne : u' ≠ 11 + h := fun heq => by
                  have := hE1_readers_h (k + 1) (by omega) (heq ▸ hu'); omega
                unfold aliasWire at hu'eq
                split_ifs at hu'eq <;> omega
            let E3 := bypass 11 E2 h 0
            have mE3 : IsAO2 11 E3 := bypass_isAO2 mE2 (by omega)
            have lE3 : E3.gates.length + 1 = E2.gates.length := by
              dsimp [E3]; rw [bypass_length]; omega
            have opsE2 : ∀ j < E2.gates.length, (gateAt E2 j).op = GateOp.and ∨
                (gateAt E2 j).op = GateOp.or := fun j hj => mE2.1 _ (gateAt_mem hj)
            have oE3 : ∀ x : Fin 11 → Bool, x v = false → circuitFun 11 E3 x = circuitFun 11 E2 x := by
              intro x _
              refine bypass_ok List.length_ofFn opsE2 (by omega) (by omega) ?_
              rintro (⟨k, _, hk, hmem⟩ | hout)
              · exact absurd hmem (hE2_no_readers_h k hk)
              · exact absurd hout hE2_out_ne_h
            have hbound := faceBound v E3 hv mE3 (fun x hx =>
              (oE3 x hx).trans ((oE2 x hx).trans ((oE1 x hx).trans (congrFun hfun x))))
            change 19 ≤ E3.gates.length at hbound
            change D.gates.length ≤ 21 at hsz
            omega
    · exfalso
      have allOr : ∀ v : Fin 11, v.val < 4 → ∀ k < D.size,
          v.val ∈ (gateAt D k).inputs → (gateAt D k).op = GateOp.or := by
        intro v hv k hk hkv
        rcases hops k hk with hop | hop
        · exact absurd ⟨v, hv, k, hk, hop, hkv⟩ hA
        · exact hop
      have foldl_spec : ∀ {α β : Type} (f : List α → β → α) (l : List β) (acc : List α),
          (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
          (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
          (∀ (j : ℕ) (b : β), l[j]? = some b →
            (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
              some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
        intro α β f l
        induction l with
        | nil => intro acc; refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
        | cons a t ih =>
          intro acc
          have h1 := ih (acc ++ [f acc a])
          refine ⟨?_, ?_, ?_⟩
          · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]; omega
          · intro i hi
            simp only [List.foldl_cons]
            rw [h1.2.1 i (by simp; omega), List.getElem?_append_left hi]
          · intro j b hj
            cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
              simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
              rw [h1.2.1 acc.length (by simp), List.getElem?_append_right (le_refl _)]; simp
            | succ j' =>
              simp only [List.getElem?_cons_succ] at hj
              simp only [List.foldl_cons, List.take_succ_cons]
              have hstep := h1.2.2 j' b hj
              simp only [List.length_append, List.length_singleton] at hstep
              have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
              rw [heq]; exact hstep
      have foldl_take_getD : ∀ {α β : Type} (f : List α → β → α) (d : α) (l : List β)
          (acc : List α) (k i : ℕ), i < acc.length + k → k ≤ l.length →
          ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
            (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
        intro α β f d l acc k i hi hk
        have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
        conv_rhs => rw [hsplit, List.foldl_append]
        have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
          rw [(foldl_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
        have hget := (foldl_spec f (l.drop k) ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
        simp only [List.getD_eq_getElem?_getD, hget]
      let isOrOp : GateOp → Bool := GateOp.rec false true false (fun _ => false) false
      let orStepE (cs : List (List ℕ)) (g : Gate) : List ℕ :=
        cs.length :: cond (isOrOp g.op)
            ((g.inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + cs.length))).flatMap
              (fun w => cs.getD (w - 11) []))
            []
      have orSets_eq : orSets 11 D = D.gates.foldl (fun cs g => cs ++ [orStepE cs g]) [] := by
        change D.gates.foldl (orStep 11) [] = _
        have hfn : orStep 11 = fun cs g => cs ++ [orStepE cs g] := by
          funext cs g
          change cs ++ [cs.length :: (if g.op = GateOp.or then _ else [])] = cs ++ [orStepE cs g]
          dsimp only [orStepE, isOrOp]
          cases g.op <;> rfl
        rw [hfn]
      have orSets_len : (orSets 11 D).length = D.gates.length := by
        rw [orSets_eq]; simpa using (foldl_spec orStepE D.gates []).1
      have orSets_getD : ∀ k < D.gates.length, (orSets 11 D).getD k [] =
          k :: cond (isOrOp (gateAt D k).op)
              (((gateAt D k).inputs.filter (fun w => decide (11 ≤ w ∧ w < 11 + k))).flatMap
                (fun w => (orSets 11 D).getD (w - 11) []))
              [] := by
        intro k hk
        have hgetg : D.gates[k]? = some (gateAt D k) := by
          rw [gateAt_eq hk, List.getElem?_eq_getElem hk]
        have hstep := (foldl_spec orStepE D.gates []).2.2 k (gateAt D k) hgetg
        have hlen : ((D.gates.take k).foldl (fun w x => w ++ [orStepE w x]) []).length = k := by
          rw [(foldl_spec orStepE (D.gates.take k) []).1, List.length_nil, Nat.zero_add,
            List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
        simp only [List.length_nil, Nat.zero_add] at hstep
        rw [orSets_eq, List.getD_eq_getElem?_getD, hstep, Option.getD_some]
        generalize hacc : (D.gates.take k).foldl (fun w x => w ++ [orStepE w x]) [] = acc
        rw [hacc] at hlen
        dsimp only [orStepE]
        rw [hlen]
        congr 1
        cases (gateAt D k).op <;> try rfl
        dsimp only [isOrOp, cond]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        rw [← hacc]
        exact foldl_take_getD orStepE [] D.gates [] k (w - 11) (by simp; omega) (Nat.le_of_lt hk)
      have orReaches_lt : ∀ w g, OrReaches 11 D w g → w - 11 < D.gates.length := by
        intro w g h
        by_contra hge
        have hnone : (orSets 11 D)[w - 11]? = none := List.getElem?_eq_none (by omega)
        have hm := h.2
        simp [List.getD_eq_getElem?_getD, hnone] at hm
      have orReaches_self : ∀ k < D.gates.length, OrReaches 11 D (11 + k) k := by
        intro k hk
        refine ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel_left, orSets_getD k hk]; simp
      have orReaches_iff : ∀ k g, k < D.gates.length →
          (OrReaches 11 D (11 + k) g ↔
            g = k ∨ ((gateAt D k).op = GateOp.or ∧
              ∃ u ∈ (gateAt D k).inputs, u < 11 + k ∧ OrReaches 11 D u g)) := by
        intro k g hk
        change (11 ≤ 11 + k ∧ g ∈ (orSets 11 D).getD (11 + k - 11) []) ↔ _
        rw [Nat.add_sub_cancel_left, orSets_getD k hk]
        constructor
        · rintro ⟨_, hmem⟩
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact Or.inl rfl
          · cases hop : (gateAt D k).op <;> rw [hop] at hmem
            · simp [isOrOp] at hmem
            · dsimp only [isOrOp, cond] at hmem
              rw [List.mem_flatMap] at hmem
              obtain ⟨u, hu, hgu⟩ := hmem
              simp only [List.mem_filter, decide_eq_true_eq] at hu
              exact Or.inr ⟨rfl, u, hu.1, hu.2.2, hu.2.1, hgu⟩
            · simp [isOrOp] at hmem
            · simp [isOrOp] at hmem
            · simp [isOrOp] at hmem
        · rintro (rfl | ⟨hop, u, hu, hult, hge, hgu⟩)
          · exact ⟨by omega, by simp⟩
          · refine ⟨by omega, ?_⟩
            rw [hop]
            dsimp only [isOrOp, cond]
            simp only [List.mem_cons, List.mem_flatMap]
            exact Or.inr ⟨u, by simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hu, hge, hult⟩, hgu⟩
      have orReaches_le : ∀ k g, OrReaches 11 D (11 + k) g → g ≤ k := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro g hg
          have hk : k < D.gates.length := by have := orReaches_lt (11 + k) g hg; omega
          rw [orReaches_iff k g hk] at hg
          rcases hg with rfl | ⟨_, u, _, hult, hge, hgu⟩
          · exact le_rfl
          · have hu_eq : u = 11 + (u - 11) := by omega
            have := ih (u - 11) (by omega) g (by rw [← hu_eq]; exact ⟨hge, hgu⟩)
            omega
      have orReaches_trans : ∀ k m g, OrReaches 11 D (11 + k) m → OrReaches 11 D (11 + m) g →
          OrReaches 11 D (11 + k) g := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro m g hkm hmg
          have hk : k < D.gates.length := by have := orReaches_lt (11 + k) m hkm; omega
          rw [orReaches_iff k m hk] at hkm
          rcases hkm with rfl | ⟨hop, u, hu, hult, hge, hgu⟩
          · exact hmg
          · rw [orReaches_iff k g hk]
            refine Or.inr ⟨hop, u, hu, hult, ?_⟩
            have hu_eq : u = 11 + (u - 11) := by omega
            rw [hu_eq]
            exact ih (u - 11) (by omega) m g (by rw [← hu_eq]; exact ⟨hge, hgu⟩) hmg
      have orReaches_val : ∀ (x : Fin 11 → Bool) (k g : ℕ),
          OrReaches 11 D (11 + k) g → wval D x (11 + g) = true → wval D x (11 + k) = true := by
        intro x k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro g hg hval
          have hk : k < D.gates.length := by have := orReaches_lt (11 + k) g hg; omega
          rw [orReaches_iff k g hk] at hg
          rcases hg with rfl | ⟨hop, u, hu, hult, hge, hgu⟩
          · exact hval
          · obtain ⟨p, q, hpq, _, _, hs⟩ := gsem k hk
            have hu_eq : u = 11 + (u - 11) := by omega
            have hgv := ih (u - 11) (by omega) g (by rw [← hu_eq]; exact ⟨hge, hgu⟩) hval
            rw [← hu_eq] at hgv
            rw [hpq, List.mem_pair] at hu
            rw [hs x, hop, orE]
            rcases hu with rfl | rfl <;> simp [hgv]
      have orIn_val : ∀ (x : Fin 11 → Bool) (w : ℕ) (i : Fin 11),
          i ∈ orIn 11 D w → x i = true → wval D x w = true := by
        intro x w i hi hxi
        rw [mem_orIn] at hi
        rcases hi with rfl | ⟨k, hk, hr, hop, hmem⟩
        · exact (hin i x).trans hxi
        · have hgv : wval D x (11 + k) = true := by
            obtain ⟨p, q, hpq, _, _, hs⟩ := gsem k hk
            rw [hpq, List.mem_pair] at hmem
            rw [hs x, hop, orE]
            rcases hmem with h0 | h1
            · rw [← h0, hin i x, hxi]; simp
            · rw [← h1, hin i x, hxi]; simp
          have hge := hr.1
          have hweq : w = 11 + (w - 11) := by omega
          rw [hweq]
          exact orReaches_val x (w - 11) k (by rwa [← hweq]) hgv
      have orIn_sub_or : ∀ k < D.gates.length, (gateAt D k).op = GateOp.or →
          ∀ u ∈ (gateAt D k).inputs, u < 11 + k → orIn 11 D u ⊆ orIn 11 D (11 + k) := by
        intro k hk hop u hu hult i hi
        rw [mem_orIn] at hi ⊢
        rcases hi with rfl | ⟨m, hm, hr, hopm, hmemm⟩
        · exact Or.inr ⟨k, hk, orReaches_self k hk, hop, hu⟩
        · refine Or.inr ⟨m, hm, ?_, hopm, hmemm⟩
          rw [orReaches_iff k m hk]
          exact Or.inr ⟨hop, u, hu, hult, hr⟩
      have opnd_inputs : ∀ k < D.gates.length, (gateAt D k).inputs = [opnd D k 0, opnd D k 1] := by
        intro k hk
        obtain ⟨p, q, hpq, _, _, _⟩ := gsem k hk
        have h0 : opnd D k 0 = p := by rw [opnd_def, hpq]; rfl
        have h1 : opnd D k 1 = q := by rw [opnd_def, hpq]; rfl
        rw [h0, h1, hpq]
      refine allTypeB D hm ht hj hsz hnum (fun v hv => ⟨allOr v hv, ?_, hcard2 v hv, ?_, ?_⟩)
      · obtain ⟨k, hk, hkv⟩ := deg2HasReader v hv
        exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkv⟩⟩
      · intro h hh huniq
        have hop : (gateAt D h).op = GateOp.or := allOr v hv h hh ((huniq h hh).mpr rfl)
        have hhv : v.val ∈ (gateAt D h).inputs := (huniq h hh).mpr rfl
        have h_orN : h ∈ orN G D := by
          rw [mem_orN]
          refine ⟨hh, hop, fun hbf => ?_⟩
          have hval : gateVal 11 D h (pairInput v v) = true := by
            obtain ⟨p, q, hpq, _, _, hs⟩ := gsem h hh
            have hhv' := hhv; rw [hpq, List.mem_pair] at hhv'
            change wval D (pairInput v v) (11 + h) = true
            rw [hs, hop, orE]
            rcases hhv' with h0 | h1
            · rw [← h0, hin v, pairInput_def]; simp
            · rw [← h1, hin v, pairInput_def]; simp
          have hf := hbf (pairInput v v) hval
          rw [graphFun_pair_self v] at hf
          exact Bool.false_ne_true hf
        have h_not_lam : h ∉ lam G D := by
          rw [mem_lam]
          rintro ⟨_, hne0, hne1, _⟩
          have hinp := opnd_inputs h hh
          have hhv' := hhv; rw [hinp, List.mem_pair] at hhv'
          obtain ⟨u, hu_lt, hu_ne, hu_or, hu_sem⟩ : ∃ u < 11 + h, (orIn 11 D u).Nonempty ∧
              (∀ x : Fin 11 → Bool, wval D x (11 + h) = (wval D x v.val || wval D x u)) ∧
              u ∈ (gateAt D h).inputs := by
            obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem h hh
            have h0 : opnd D h 0 = p := by rw [opnd_def, hpq]; rfl
            have h1 : opnd D h 1 = q := by rw [opnd_def, hpq]; rfl
            rcases hhv' with h0' | h1'
            · refine ⟨opnd D h 1, by omega, hne1, fun x => ?_, by rw [hinp]; simp⟩
              rw [hs x, hop, orE, ← h0, ← h1, h0']
            · refine ⟨opnd D h 0, by omega, hne0, fun x => ?_, by rw [hinp]; simp⟩
              rw [hs x, hop, orE, ← h0, ← h1, h1', Bool.or_comm]
          obtain ⟨w, hw⟩ := hu_ne
          have hw_ne_v : w ≠ v := by
            intro hwv
            subst w
            rw [mem_orIn] at hw
            rcases hw with heq | ⟨k, hk, hr, _, hkv⟩
            · refine noRep h v.val hh (by omega) (fun _ x => ?_)
              rw [hu_or x, ← heq, Bool.or_self]
            · have hkh : k = h := (huniq k hk).mp hkv
              subst k
              have hge : 11 ≤ u := hr.1
              have hle := orReaches_le (u - 11) h (by rwa [show 11 + (u - 11) = u by omega])
              omega
          obtain ⟨a, b, hab, hva, hvb⟩ := twoNbrs v hv
          have adj_of : ∀ c : Fin 11, G.Adj v c → G.Adj w c := by
            intro c hvc
            let x0 : Fin 11 → Bool := pairInput w c
            let x1 : Fin 11 → Bool := fun i => x0 i || decide (i = v)
            have hux0 : wval D x0 u = true := orIn_val x0 u w hw (by dsimp [x0]; rw [pairInput_def]; simp)
            have hux1 : wval D x1 u = true := orIn_val x1 u w hw (by dsimp [x1, x0]; rw [pairInput_def]; simp)
            have hsame : ∀ z < 11 + D.gates.length, z ≠ v.val → wval D x1 z = wval D x0 z := by
              intro z
              induction z using Nat.strong_induction_on with
              | _ z ih =>
                intro hz hnev
                by_cases hzn : z < 11
                · let zi : Fin 11 := ⟨z, hzn⟩
                  change wval D x1 zi.val = wval D x0 zi.val
                  rw [hin zi, hin zi]
                  have hne : zi ≠ v := fun e => hnev (congrArg Fin.val e)
                  simp [x1, hne]
                · obtain ⟨k, rfl⟩ : ∃ k, z = 11 + k := ⟨z - 11, by omega⟩
                  by_cases hkh : k = h
                  · subst hkh; rw [hu_or x1, hu_or x0, hux1, hux0]; simp
                  · have hk : k < D.gates.length := by omega
                    obtain ⟨p, q, hpq, hp, hq, hs⟩ := gsem k hk
                    have hnv : v.val ∉ (gateAt D k).inputs := fun hm => hkh ((huniq k hk).mp hm)
                    rw [hpq, List.mem_pair, not_or] at hnv
                    rw [hs, hs, ih p (by omega) (by omega) (Ne.symm hnv.1),
                      ih q (by omega) (by omega) (Ne.symm hnv.2)]
            have hout : circuitFun 11 D x1 = circuitFun 11 D x0 := by
              change wval D x1 D.output = wval D x0 D.output
              by_cases hlt : D.output < 11 + D.gates.length
              · exact hsame D.output hlt (outNeInput v)
              · change val D (List.ofFn x1) D.output = val D (List.ofFn x0) D.output
                rw [val_ge (C := D) List.length_ofFn (by omega),
                  val_ge (C := D) List.length_ofFn (by omega)]
            have hx1_true : graphFun G ∅ x1 = true :=
              graphFun_adj_true v c x1 hvc (by simp [x1]) (by dsimp [x1, x0]; rw [pairInput_def]; simp)
            rw [hfun, hx1_true] at hout
            exact graphFun_pair_imp_adj w c hout.symm
          exact hw_ne_v (noC4Deg2 v a b w hv hab hva hvb (adj_of a hva) (adj_of b hvb))
        exact Finset.mem_sdiff.mpr ⟨h_orN, h_not_lam⟩
      · intro t ht b hside
        have htmem := (mem_tops t).mp ht
        have htlt : t < D.gates.length := htmem.1
        have htop : (gateAt D t).op = GateOp.and := htmem.2.1
        have hmem_v : v ∈ orIn 11 D (opnd D t b) := by
          change v ∈ side D t b; rw [hside]; simp
        have hne_v : opnd D t b ≠ v.val := by
          intro heq
          have hinp := opnd_inputs t htlt
          have hvt : v.val ∈ (gateAt D t).inputs := by
            rw [hinp, ← heq]; fin_cases b <;> simp
          have hor := allOr v hv t htlt hvt
          rw [htop] at hor; cases hor
        rw [mem_orIn] at hmem_v
        rcases hmem_v with hEq | ⟨k0, hk0, hr0, hop0, hkv0⟩
        · exact absurd hEq.symm hne_v
        · let P : ℕ → Prop := fun m => m < D.gates.length ∧ (gateAt D m).op = GateOp.or ∧
            OrReaches 11 D (opnd D t b) m ∧ v ∈ orIn 11 D (11 + m)
          have hex : ∃ m, P m := by
            refine ⟨k0, hk0, hop0, hr0, ?_⟩
            rw [mem_orIn]
            exact Or.inr ⟨k0, hk0, orReaches_self k0 hk0, hop0, hkv0⟩
          let m := Nat.find hex
          obtain ⟨hmlt, hmop, hrm, hvm⟩ := Nat.find_spec hex
          have hm_min : ∀ m' < m, ¬ P m' := fun m' hlt => Nat.find_min hex hlt
          have hm_orIn : orIn 11 D (11 + m) = {v} := by
            ext u
            simp only [Finset.mem_singleton]
            constructor
            · intro hu
              have huw : u ∈ orIn 11 D (opnd D t b) := by
                rw [mem_orIn] at hu ⊢
                rcases hu with hEq | ⟨k, hk, hrk, hopk, huk⟩
                · omega
                · refine Or.inr ⟨k, hk, ?_, hopk, huk⟩
                  have hge := hrm.1
                  have hweq : opnd D t b = 11 + (opnd D t b - 11) := by omega
                  rw [hweq]
                  exact orReaches_trans (opnd D t b - 11) m k (by rwa [← hweq]) hrk
              have hu' : u ∈ ({v} : Finset (Fin 11)) := by
                change u ∈ side D t b at huw; rwa [hside] at huw
              simpa using hu'
            · rintro rfl; exact hvm
          have hm_orN : m ∈ orN G D := by
            rw [mem_orN]
            refine ⟨hmlt, hmop, fun hbf => ?_⟩
            have hval : gateVal 11 D m (pairInput v v) = true :=
              orIn_val (pairInput v v) (11 + m) v hvm (by rw [pairInput_def]; simp)
            have hf := hbf (pairInput v v) hval
            rw [graphFun_pair_self v] at hf
            exact Bool.false_ne_true hf
          have hm_not_lam : m ∉ lam G D := by
            rw [mem_lam]
            rintro ⟨_, hne0, hne1, _⟩
            have hinp := opnd_inputs m hmlt
            have hlt0 : opnd D m 0 < 11 + m := hRB m hmlt _ (by rw [hinp]; simp)
            have hlt1 : opnd D m 1 < 11 + m := hRB m hmlt _ (by rw [hinp]; simp)
            have sub0 : orIn 11 D (opnd D m 0) ⊆ {v} := by
              rw [← hm_orIn]; exact orIn_sub_or m hmlt hmop _ (by rw [hinp]; simp) hlt0
            have sub1 : orIn 11 D (opnd D m 1) ⊆ {v} := by
              rw [← hm_orIn]; exact orIn_sub_or m hmlt hmop _ (by rw [hinp]; simp) hlt1
            have opnd_eq_v : ∀ c : Fin 2, (orIn 11 D (opnd D m c)).Nonempty →
                orIn 11 D (opnd D m c) ⊆ {v} → opnd D m c < 11 + m → opnd D m c = v.val := by
              intro c hne hsub hltc
              obtain ⟨u, hu⟩ := hne
              have huv : u = v := Finset.mem_singleton.mp (hsub hu)
              subst huv
              have hu' := hu
              rw [mem_orIn] at hu'
              rcases hu' with hEq | ⟨k, hk, hrk, hopk, hkv⟩
              · exact hEq.symm
              · exfalso
                let m' := opnd D m c - 11
                have hm'_eq : opnd D m c = 11 + m' := by have := hrk.1; omega
                have hm'_lt : m' < m := by omega
                have hm'_ltD : m' < D.gates.length := by omega
                have hm'_op : (gateAt D m').op = GateOp.or := by
                  have hrk' : OrReaches 11 D (11 + m') k := by rwa [← hm'_eq]
                  rw [orReaches_iff m' k hm'_ltD] at hrk'
                  rcases hrk' with rfl | ⟨hor, _⟩
                  · exact hopk
                  · exact hor
                have hm'_reach : OrReaches 11 D (opnd D t b) m' := by
                  have hge := hrm.1
                  have hweq : opnd D t b = 11 + (opnd D t b - 11) := by omega
                  rw [hweq]
                  apply orReaches_trans (opnd D t b - 11) m m' (by rwa [← hweq])
                  rw [orReaches_iff m m' hmlt]
                  refine Or.inr ⟨hmop, opnd D m c, ?_, hltc, ?_⟩
                  · rw [hinp]; fin_cases c <;> simp
                  · rw [hm'_eq]; exact orReaches_self m' hm'_ltD
                exact hm_min m' hm'_lt ⟨hm'_ltD, hm'_op, hm'_reach, by rwa [← hm'_eq]⟩
            have eq0 := opnd_eq_v 0 hne0 sub0 hlt0
            have eq1 := opnd_eq_v 1 hne1 sub1 hlt1
            refine noRep m v.val hmlt (by omega) (fun _ x => ?_)
            obtain ⟨p, q, hpq, _, _, hs⟩ := gsem m hmlt
            have hp0 : p = v.val := by
              have : opnd D m 0 = p := by rw [opnd_def, hpq]; rfl
              omega
            have hq1 : q = v.val := by
              have : opnd D m 1 = q := by rw [opnd_def, hpq]; rfl
              omega
            rw [hs x, hmop, orE, hp0, hq1, Bool.or_self]
          exact ⟨m, Finset.mem_sdiff.mpr ⟨hm_orN, hm_not_lam⟩, hm_orIn⟩
