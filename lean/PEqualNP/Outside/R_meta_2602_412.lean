import Mathlib
import PEqualNP.Defs

-- Equality in the clean counting argument of L1407 forces one whole side
-- of the plane to have a first-order witness at each incidence.
-- The general union count is already proved in L1407.
open PEqualNP.CircuitLowerBounds Fin.NatCast in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 7000000 in
theorem PEqualNP.Outside.R_meta_2602_412
    (unionBound : ∀ (n : ℕ) (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
    (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
    (R.biUnion f).card ≤ R.card + B.card)
    (dirtyCase : let tr := fun (C : Circuit) (i k : ℕ) (v : ℕ → Bool) =>
    (∀ j < 26, v j = decide (j=k)) ∧
    (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
      let p := C.wires (List.ofFn fun t : Fin 26 => decide (t.val=i))
      (g.op = GateOp.and → v (26+j) = ((p.getD a false && v b) || (v a && p.getD b false))) ∧
      (g.op = GateOp.or → v (26+j) = (v a || v b))) ∧ v C.output = false
  ∀ (C : Circuit) (v w : ℕ → Bool), 63 ≤ C.size → C.size ≤ 64 →
    PEqualNP.MinimumComplex.Strict 26 C → PEqualNP.EdgeOwnership.AndOrOnly C →
    (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 13,
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
    tr C 0 13 v → tr C 13 0 w →
    (∃ (k : Fin 14) (j : Fin C.gates.length), (C.gates.get j).op = GateOp.and ∧
      let rows : List ℕ := [15860,23529,38867,69543,139086,269981,531771,1055351,2102511,
        4196831,8393662,16779133,33558266,67100672]
      (C.wires (List.ofFn fun i : Fin 26 => (rows.getD k.val 0).testBit i.val)).getD (26+j.val) false = true) →
    False)
    : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  classical
  have eval_and (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have eval_or (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let decideTrue (v : Bool) : Decidable (v = true) := inferInstance
  let andFlag (op : GateOp) : Bool :=
    GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false op
  have dag_union_bound {n : ℕ} (f : ℕ → Finset (Fin n)) (R B : Finset ℕ)
      (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
      (R.biUnion f).card ≤ R.card + B.card := unionBound n f R B step
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

  have wires_eq (C : Circuit) (xs : List Bool) : C.wires xs = wiresFrom C.gates xs := rfl

  have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    simp [wiresFrom, List.foldl_append]

  have wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp

  have length_wiresFrom (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]

  have getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wiresFrom gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]

  have getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega

  have getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
    simp

  have getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp

  have gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
      (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
      op.eval l₁ = true → op.eval l₂ = true := by
    rcases hop with rfl | rfl
    · simp only [eval_and, List.all_eq_true, id_eq]
      intro h b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        have hi1 : i < l₁.length := by omega
        rw [List.getD_eq_getElem _ _ hi1]
        exact h _ (List.getElem_mem hi1)
      have h2 := hle i h1
      rwa [List.getD_eq_getElem _ _ hi] at h2
    · simp only [eval_or, List.any_eq_true, id_eq]
      rintro ⟨b, hb, rfl⟩
      obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
      have h1 : l₁.getD i false = true := by
        rw [List.getD_eq_getElem _ _ hi]; exact hbi
      have h2 := hle i h1
      have hi2 : i < l₂.length := by omega
      rw [List.getD_eq_getElem _ _ hi2] at h2
      exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

  have wiresFrom_mono (gs : List Gate)
      (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
        (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
        ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
    induction gs with
    | nil =>
      intro w₁ w₂ _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro w₁ w₂ hlen hle i hi
      have hstep1 : wiresFrom (g :: gs) w₁ =
          wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
      have hstep2 : wiresFrom (g :: gs) w₂ =
          wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
      rw [hstep1] at hi
      rw [hstep2]
      apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < w₁.length
      · rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hle j hj
      · by_cases heq : j = w₁.length
        · subst heq
          rw [getD_snoc_eq] at hj
          rw [hlen, getD_snoc_eq]
          exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
            (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
            (by simp) (by
              intro t ht
              by_cases ht_lt : t < g.inputs.length
              · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
                rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
                simp only [List.getElem_map] at ht ⊢
                exact hle _ ht
              · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
                exact Bool.noConfusion ht) hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj


  let posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
    Nat.casesOn w false (fun i => (wiresFrom gs (List.ofFn x)).getD i false)

  let clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

  let gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
    gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

  let firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
    clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

  let secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
    clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

  let andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
    andFlag (gateAtPos n gs w).op

  have clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
    unfold clampWire
    split <;> omega

  have pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
      posRead gs (clampWire lim i) x =
      (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
    simp only [clampWire]
    split <;> rfl

  have pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
      posRead gs (i+1) x = x ⟨i,hi⟩ := by
    change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
    rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
    rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

  have pos_mono {n : ℕ} (gs : List Gate)
      (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
      posRead gs w x = true → posRead gs w y = true := by
    cases w with
    | zero => simp [posRead]
    | succ i =>
      apply wiresFrom_mono gs ops _ _ (by simp)
      intro j h
      by_cases hj : j < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
        exact le _ h
      · rw [List.getD_eq_default _ _ (by simp; omega)] at h
        contradiction

  let edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

  let singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
  let pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

  have edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
      ¬ edgeTrue G (singletonBits u) := by
    rintro ⟨i,j,h,hi,hj⟩
    simp only [singletonBits, decide_eq_true_eq] at hi hj
    subst i
    subst j
    exact G.loopless.irrefl u h

  have edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
      edgeTrue G (pairBits u v) ↔ G.Adj u v := by
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      simp only [pairBits, decide_eq_true_eq] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact (G.loopless.irrefl _ h).elim
      · exact h
      · exact h.symm
      · exact (G.loopless.irrefl _ h).elim
    · intro h
      exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

  have binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
      (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
      (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
      op.eval (l.map v) =
        (if (andFlag op) then
          v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
         else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
    cases l with
    | nil =>
      rcases hop with rfl | rfl
      · exact (nonempty rfl rfl).elim
      · simp [eval_and, eval_or, andFlag,vd]
    | cons i t =>
      cases t with
      | nil => rcases hop with rfl | rfl <;> simp [eval_and, eval_or, andFlag]
      | cons j t =>
        have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
        subst t
        rcases hop with rfl | rfl <;> simp [eval_and, eval_or, andFlag]

  let supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
    @Finset.filter (Fin n) (fun u => posRead (n := n) gs w (singletonBits u) = true)
      (fun u => decideTrue (posRead (n := n) gs w (singletonBits u))) Finset.univ

  have mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
      u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


  let cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
    ∀ (j : Fin gs.length) (x : Fin n → Bool), (gs.get j).op = GateOp.and →
      (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

  let binaryOps (gs : List Gate) : Prop :=
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

  have gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      gateAtPos n gs (n+j+1) = gs[j] := by
    unfold gateAtPos
    rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

  have pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
      (ops : binaryOps gs) (clean : cleanOn G gs)
      (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
      posRead gs w x =
        (if andPos n gs w then
          posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
         else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
    let j := w-(n+1)
    have hj : j < gs.length := by dsimp [j]; omega
    have hw : w = n+j+1 := by dsimp [j]; omega
    have hg := ops _ (List.getElem_mem hj)
    have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
      intro ha hempty
      let z : Fin n → Bool := fun _ => false
      have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
      simp only [List.length_ofFn, hempty, List.map_nil, ha, eval_and, eval_or, andFlag, List.all_nil] at eqg
      obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z ha eqg
      contradiction
    rw [hw]
    simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
    change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
    have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
    simp only [List.length_ofFn] at h
    rw [h]
    exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
      (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
      (n+j) (by simp)

  have pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
      (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
      (ha : andPos n gs w = true) (x : Fin n → Bool) :
      posRead gs w x = true → edgeTrue G x := by
    let j := w-(n+1)
    have hj : j < gs.length := by dsimp [j]; omega
    have hw : w = n+j+1 := by dsimp [j]; omega
    rw [hw] at ha ⊢
    simp only [andPos, gateAt_index gs j hj] at ha
    have hop : gs[j].op = GateOp.and := by
      cases h : gs[j].op <;> first | rfl | (rw [h] at ha; contradiction)
    exact clean ⟨j,hj⟩ x hop

  have support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
      (supports (n:=n) gs w).card ≤ 1 := by
    cases w with
    | zero => simp [supports,posRead]
    | succ i =>
      have hi : i < n := by omega
      have hs : supports gs (i+1) = {⟨i,hi⟩} := by
        ext u
        simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
      simp [hs]

  have hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
      posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
    cases w with
    | zero => simp [posRead]
    | succ i =>
      have hi : i<n := by omega
      simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

  have support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
      (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
      (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact edge_single G u (pos_clean G gs clean w lo hi ha _ ((mem_support gs w u).mp hu))

  have support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
      (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
      (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
      supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
    ext u
    simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
    simp

  have cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
      (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
      (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
      (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
      (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
    apply (edge_pair G u v).mp
    apply pos_clean G gs clean w lo hi ha
    rw [pos_gate G gs ops clean w lo hi,ha]
    simp only [ite_true, Bool.and_eq_true]
    have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
    constructor
    · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
      intro i ht
      simp only [singletonBits,decide_eq_true_eq] at ht
      simp [pairBits,ht]
    · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
      intro i ht
      simp only [singletonBits,decide_eq_true_eq] at ht
      simp [pairBits,ht]


  have root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
      posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
    rw [pos_clamp]
    change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
    split_ifs with h
    · rfl
    · symm
      apply List.getD_eq_default
      simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

  have root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
    unfold clampWire
    split <;> omega

  have root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
      (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
      supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u h
    apply edge_single G u
    apply (heval _).mp
    rw [← root_read]
    exact (mem_support _ _ _).mp h

  have root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
      (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
      ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
    intro u v h
    rw [root_read,heval]
    exact (edge_pair G u v).mpr h

  have gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
      ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
      ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
        1 < (S w).card)).card +
      ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
        (S w).card ≤ 1)).card ≤ len := by
    classical
    let gates := Finset.range (n + 1 + len)
    let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
    let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
    change ands.card + large.card + small.card ≤ len
    have hdis : Disjoint ands large := by
      apply Finset.disjoint_left.mpr
      intro w h₁ h₂
      have a := (Finset.mem_filter.mp h₁).2.2
      have b := (Finset.mem_filter.mp h₂).2.2.1
      exact Bool.noConfusion (a.symm.trans b)
    have hdis' : Disjoint (ands ∪ large) small := by
      apply Finset.disjoint_left.mpr
      intro w h₁ h₂
      have b := (Finset.mem_filter.mp h₂).2.2
      rcases Finset.mem_union.mp h₁ with ha | hl
      · have a := (Finset.mem_filter.mp ha).2.2
        exact Bool.noConfusion (a.symm.trans b.1)
      · have a := (Finset.mem_filter.mp hl).2.2.2
        exact (Nat.not_lt_of_ge b.2) a
    have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · rcases Finset.mem_union.mp h with h | h <;>
          exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
            Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
      · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
    simpa using Finset.card_le_card hsub

  have edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
      (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
      (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
      (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
      (ha : ∀ w, k ≤ w → w < N → a w < w)
      (hb : ∀ w, k ≤ w → w < N → b w < w)
      (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
      (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
        H (a w) u v ∨ H (b w) u v)
      (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
        H (a w) u v ∧ H (b w) u v)
      (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
      ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
        ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
    induction r using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hkw : k ≤ w
      · have hia := ha w hkw hr
        have hib := hb w hkw hr
        cases hop : A w with
        | false =>
          have hSw := horS w hkw hr hop
          rw [hSw, Finset.mem_union] at hx hy
          rcases horH w x y hkw hr hop hxy with h | h
          · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
          · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
        | true =>
          have htrue := handH w x y hkw hr hop hxy
          by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
          · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
            · refine ⟨w, hkw, hr, hop, ?_⟩
              have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
              rcases hsa with hax | hay <;> rcases hsb with hbx | hby
              · exact False.elim (hd hax hbx)
              · exact Or.inl ⟨hax, hby⟩
              · exact Or.inr ⟨hay, hbx⟩
              · exact False.elim (hd hay hby)
            · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
          · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
      · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
        · exact False.elim (hx h)
        · exact False.elim (hy h)

  have tight_cover (n k N r : ℕ) (G : SimpleGraph (Fin n))
      (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
      (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
      (hrH : ∀ u v, G.Adj u v → H r u v)
      (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
      (ha : ∀ w, k ≤ w → w < N → a w < w)
      (hb : ∀ w, k ≤ w → w < N → b w < w)
      (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
      (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
        H (a w) u v ∨ H (b w) u v)
      (handS : ∀ w, k ≤ w → w < N → A w = true →
        (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
      (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
        H (a w) u v ∧ H (b w) u v)
      (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
      (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
        (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
          (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
        (R.biUnion f).card ≤ R.card + B.card) :
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        T.card ≤ 1 + (((Finset.range N).filter fun w =>
          k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).filter fun w => S w ⊆ T).card := by
    classical
    let stepF (w : ℕ) (prev : ∀ i, i < w → Finset (Fin n)) : Finset (Fin n) :=
      if (S w).card ≤ 1 then
        if hg : k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then prev (a w) (ha w hg.1 hg.2)
            else prev (b w) (hb w hg.1 hg.2)
          else prev (a w) (ha w hg.1 hg.2) ∪ prev (b w) (hb w hg.1 hg.2)
        else S w
      else ∅
    let f : ℕ → Finset (Fin n) := WellFounded.fix Nat.lt_wfRel.wf stepF
    let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
    have feq (w : ℕ) : f w =
        if (S w).card ≤ 1 then
          if k ≤ w ∧ w < N then
            if A w = true then
              if (S (a w)).card ≤ 1 then f (a w) else f (b w)
            else f (a w) ∪ f (b w)
          else S w
        else ∅ := by
      conv_lhs => rw [show f w = stepF w (fun i _ => f i) from WellFounded.fix_eq ..]
      rfl
    have hit : ∀ w, w < N → (S w).card ≤ 1 →
        ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw ht u v hwuv
        rw [feq, ite_eq_left ht]
        by_cases hkw : k ≤ w
        · rw [ite_eq_left ⟨hkw, hw⟩]
          cases hg : A w with
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have heq := horS w hkw hw hg
            have hta : (S (a w)).card ≤ 1 := by
              apply (Finset.card_le_card _).trans ht
              rw [heq]
              exact Finset.subset_union_left
            have htb : (S (b w)).card ≤ 1 := by
              apply (Finset.card_le_card _).trans ht
              rw [heq]
              exact Finset.subset_union_right
            have hia := ha w hkw hw
            have hib := hb w hkw hw
            rcases horH w u v hkw hw hg hwuv with h | h
            · have hitA := ih _ hia (hia.trans hw) hta u v h
              simp only [Finset.mem_union]
              tauto
            · have hitB := ih _ hib (hib.trans hw) htb u v h
              simp only [Finset.mem_union]
              tauto
          | true =>
            simp only [ite_true]
            have hz := handH w u v hkw hw hg hwuv
            by_cases htA : (S (a w)).card ≤ 1
            · rw [ite_eq_left htA]
              have hl := ha w hkw hw
              exact ih _ hl (hl.trans hw) htA u v hz.1
            · rw [ite_eq_right htA]
              have hl := hb w hkw hw
              exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
        · rw [ite_eq_right (fun h => hkw h.1)]
          exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv

    have smallSub (w : ℕ) : (S w).card ≤ 1 → S w ⊆ f w := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro ht
        rw [feq, ite_eq_left ht]
        by_cases hg : k ≤ w ∧ w < N
        · rw [ite_eq_left hg]
          cases hop : A w with
          | true => simp [hzero w hg.1 hg.2 hop]
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have hu := horS w hg.1 hg.2 hop
            rw [hu] at ht ⊢
            apply Finset.union_subset_union
            · exact ih _ (ha _ hg.1 hg.2) ((Finset.card_le_card Finset.subset_union_left).trans ht)
            · exact ih _ (hb _ hg.1 hg.2) ((Finset.card_le_card Finset.subset_union_right).trans ht)
        · rw [ite_eq_right hg]
    let T := f r
    let F (w : ℕ) := if f w ⊆ T then f w else ∅
    let restricted := B.filter (fun w => S w ⊆ T)
    have step (w : ℕ) (hw : 1 < (F w).card) :
        (∃ j < w, F w ⊆ F j) ∨
          (w ∈ restricted ∧ ∃ i < w, ∃ j < w, F w ⊆ F i ∪ F j) := by
      have allowed : f w ⊆ T := by by_contra h; simp [F,h] at hw
      have keep : F w = f w := ite_eq_left allowed
      rw [keep] at hw ⊢
      have ht : (S w).card ≤ 1 := by
        by_contra h
        rw [feq, ite_eq_right h] at hw
        simp at hw
      have hg : k ≤ w ∧ w < N := by
        by_contra h
        rw [feq, ite_eq_left ht, ite_eq_right h] at hw
        omega
      have hia := ha w hg.1 hg.2
      have hib := hb w hg.1 hg.2
      cases hop : A w with
      | false =>
        have eq : f w = f (a w) ∪ f (b w) := by
          rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
          simp
        have incl : f (a w) ∪ f (b w) ⊆ T := eq ▸ allowed
        have ka : F (a w) = f (a w) := ite_eq_left (fun _ h => incl (Finset.mem_union_left _ h))
        have kb : F (b w) = f (b w) := ite_eq_left (fun _ h => incl (Finset.mem_union_right _ h))
        refine Or.inr ⟨?_, a w, hia, b w, hib, ?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
            fun _ h => allowed (smallSub w ht h)⟩
        · rw [ka,kb,eq] <;> exact fun _ h => h
      | true =>
        have follow (z : ℕ) (hz : z < w) (eq : f w = f z) : ∃ j < w, f w ⊆ F j := by
          have ok : f z ⊆ T := eq ▸ allowed
          exact ⟨z,hz,by rw [show F z = f z from ite_eq_left ok, eq] <;> exact fun _ h => h⟩
        left
        by_cases h : (S (a w)).card ≤ 1
        · exact follow _ hia (by rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left h])
        · exact follow _ hib (by rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right h])
    refine ⟨T, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
    have total := hdag F {r} restricted step
    simpa [F, T, restricted, B] using total

  have tight_edges (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
      (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
      (hsmall : ∀ w < k, (S w).card ≤ 1)
      (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
      (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
      (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
      (hjoin : ∀ w, k ≤ w → w < N → A w = true →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
      (hside : ∀ w, k ≤ w → w < N → A w = true →
        (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
      (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
        ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
      G.edgeFinset.card ≤
        (((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).filter
          fun w => (S (a w)).Nonempty ∧ (S (b w)).Nonempty).card +
        (((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).filter
          fun w => (S (a w)).Nonempty ∧ (S (b w)).Nonempty).card := by
    classical
    cases isEmpty_or_nonempty (Fin n) with
    | inl h =>
      have := h
      have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
      simp [he]
    | inr hn =>
      let z := Classical.choice hn
      let AS := ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).filter
        fun w => (S (a w)).Nonempty ∧ (S (b w)).Nonempty
      let OS := ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).filter
        fun w => (S (a w)).Nonempty ∧ (S (b w)).Nonempty
      let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
      let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
      have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
          ∀ u ∈ S (a w), ∀ v ∈ S (b w),
            (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
        intro w
        by_cases hw : w ∈ AS
        · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa using (Finset.mem_filter.mp hw).1
          obtain ⟨ha,hb⟩ := hparents w hk hN
          have hJ := hjoin w hk hN hA
          rcases hside w hk hN hA with h | h
          · by_cases hne : (S (a w)).Nonempty
            · obtain ⟨c,hc⟩ := hne
              have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
              exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
            · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
          · by_cases hne : (S (b w)).Nonempty
            · obtain ⟨c,hc⟩ := hne
              have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
              exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
            · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
        · exact ⟨z, 0, fun h => (hw h).elim⟩
      choose cOf jOf spec using pick
      let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
      have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
        have hex : ∃ c, adj c w := ⟨c,h⟩
        have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
        by_contra hne
        obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
        exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
      let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
      let B (c : Fin n) := OS.filter (fun w => oc w = c)
      have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
        apply dag_union_bound
        intro i hi
        by_cases hgood : i < N ∧ adj c i
        · have hf : F c i = S i := ite_eq_left hgood
          rw [hf] at hi
          have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
          have hA : A i = false := by
            cases he : A i with
            | false => rfl
            | true => simp [hzero i hk hgood.1 he] at hi
          obtain ⟨ha,hb⟩ := hparents i hk hgood.1
          have hu := hunion i hk hgood.1 hA
          have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
            fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
          have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
            fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
          by_cases nonA : (S (a i)).Nonempty
          case neg =>
            left
            refine ⟨b i,hb,?_⟩
            rw [hf,hfb,hu,Finset.not_nonempty_iff_eq_empty.mp nonA,Finset.empty_union]
          by_cases nonB : (S (b i)).Nonempty
          case neg =>
            left
            refine ⟨a i,ha,?_⟩
            rw [hf,hfa,hu,Finset.not_nonempty_iff_eq_empty.mp nonB,Finset.union_empty]
          right
          refine ⟨?_, a i, ha, b i, hb, ?_⟩
          · simp [B, OS, hgood.1, hk, hA, hi, nonA, nonB, owner_eq i c hi hgood.2]
          · rw [hf,hfa,hfb,hu]
        · simp [F,hgood] at hi
      let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
      have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
        intro e
        induction e using Sym2.inductionOn with
        | _ u v =>
          intro he
          have huv : G.Adj u v := G.mem_edgeFinset.mp he
          obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
          have hw : w ∈ AS := by
            apply Finset.mem_filter.mpr
            refine ⟨by simp [hN,hk,hA], ?_⟩
            rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
            · exact ⟨⟨_,hu⟩,⟨_,hv⟩⟩
            · exact ⟨⟨_,hv⟩,⟨_,hu⟩⟩
          have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
          have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
              s(cOf w,t) ∈ Finset.univ.biUnion E :=
            Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
              Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
          rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
          · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
            · simpa only [he] using member v ht
            · simpa only [he, Sym2.eq_swap] using member u ht
          · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
            · simpa only [he, Sym2.eq_swap] using member u ht
            · simpa only [he] using member v ht
      have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
        (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
      have hbs : (∑ c, (B c).card) = OS.card :=
        (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
      calc
        G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
        _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
        _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
        _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]


  let point (i : Fin 13) := Fin.castAdd 13 i
  let line (i : Fin 13) := Fin.natAdd 13 i
  let label (a : Fin 26) : Fin 13 := ⟨a.val % 13, Nat.mod_lt _ (by decide)⟩
  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let forward (a b : Fin 26) : Prop := a.val < 13 ∧ 13 ≤ b.val ∧ inc (label a) (label b)
  let plane : SimpleGraph (Fin 26) := {
    Adj a b := forward a b ∨ forward b a
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨by intro a h; rcases h with h | h <;> exact (Nat.not_le_of_lt h.1) h.2.1⟩

  }
  letI plane_dec : DecidableRel plane.Adj := fun a b => by
    unfold plane forward inc
    infer_instance

  have labels (l : Fin 13) : label (point l) = l ∧ label (line l) = l := by
    revert l
    decide

  have endpoints (a : Fin 26) : (a.val < 13 → a = point (label a)) ∧
      (13 ≤ a.val → a = line (label a)) := by
    revert a
    decide

  have incidence_iff (x : Fin 26 → Bool) : edgeTrue plane x ↔
      ∃ p l : Fin 13, inc p l ∧ x (point p) = true ∧ x (line l) = true := by
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      have visit (a b : Fin 26) (h : forward a b) (ha : x a = true) (hb : x b = true) :
          ∃ p l, inc p l ∧ x (point p) = true ∧ x (line l) = true :=
        ⟨label a,label b,h.2.2,(endpoints a).1 h.1 ▸ ha,(endpoints b).2 h.2.1 ▸ hb⟩
      rcases hab with h | h
      · exact visit a b h ha hb
      · exact visit b a h hb ha
    · rintro ⟨p,l,h,hp,hl⟩
      exact ⟨point p,line l,Or.inl ⟨p.isLt,by simp [line],by simpa only [(labels p).1,(labels l).2]⟩,hp,hl⟩

  have unique_meet : ∀ p q l k : Fin 13, inc p l → inc q l → inc q k → inc p k →
      p = q ∨ l = k := by
    unfold inc
    decide +kernel

  have plane_c4 : ∀ a b c d : Fin 26, a ≠ c → b ≠ d →
      ¬(plane.Adj a b ∧ plane.Adj b c ∧ plane.Adj c d ∧ plane.Adj d a) := by
    have rect (p l q k : Fin 26) (hpl : forward p l) (hql : forward q l)
        (hqk : forward q k) (hpk : forward p k) : p = q ∨ l = k := by
      rcases unique_meet (label p) (label q) (label l) (label k)
        hpl.2.2 hql.2.2 hqk.2.2 hpk.2.2 with e | e
      · exact Or.inl (((endpoints p).1 hpl.1).trans ((congrArg point e).trans ((endpoints q).1 hql.1).symm))
      · exact Or.inr (((endpoints l).2 hpl.2.1).trans ((congrArg line e).trans ((endpoints k).2 hqk.2.1).symm))
    have lineNext {p l z : Fin 26} (hp : forward p l) (h : plane.Adj l z) : forward z l :=
      h.resolve_left (fun hz => (Nat.not_le_of_lt hz.1) hp.2.1)
    have pointNext {p l z : Fin 26} (hp : forward p l) (h : plane.Adj p z) : forward p z :=
      h.resolve_right (fun hz => (Nat.not_le_of_lt hp.1) hz.2.1)
    rintro a b c d hac hbd ⟨ab,bc,cd,da⟩
    rcases ab with ab | ba
    · have cb := lineNext ab bc
      have ad := pointNext ab da.symm
      exact (rect a b c d ab cb (pointNext cb cd) ad).elim hac hbd
    · have bc' := pointNext ba bc
      have da' := lineNext ba da.symm
      exact (rect b c d a bc' (lineNext bc' cd) da' ba).elim hbd hac.symm

  have plane_edges : plane.edgeFinset.card = 52 := by decide +kernel

  have ring_edges : ∀ i : Fin 13, plane.Adj (point i) (line i) ∧
      plane.Adj (point (i + 1)) (line i) ∧ point i ≠ line i := by decide

  have covering_labels (T : Finset (Fin 26))
      (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T) : T.image label = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    rcases cover _ _ (ring_edges i).1 with h | h
    · exact Finset.mem_image.mpr ⟨_,h,(labels i).1⟩
    · exact Finset.mem_image.mpr ⟨_,h,(labels i).2⟩

  have min_cover (T : Finset (Fin 26)) (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T) :
      13 ≤ T.card := by
    have h := Finset.card_image_le (f := label) (s := T)
    simpa [covering_labels T cover] using h

  -- A diagonal perfect matching forces one choice per pair. The next thirteen
  -- incidence edges propagate that choice once around the cycle.
  have cover_side (T : Finset (Fin 26)) (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T)
      (size : T.card ≤ 13) :
      (∀ i : Fin 13, point i ∈ T ∧ line i ∉ T) ∨
      (∀ i : Fin 13, line i ∈ T ∧ point i ∉ T) := by
    have full : T.card = 13 := Nat.le_antisymm size (min_cover T cover)
    have inj : Set.InjOn label (T : Set (Fin 26)) := Finset.card_image_iff.mp (by
      rw [covering_labels T cover, full]; rfl)
    have disj (i : Fin 13) (hp : point i ∈ T) (hl : line i ∈ T) : False :=
      (ring_edges i).2.2 (inj hp hl ((labels i).1.trans (labels i).2.symm))
    by_cases first : ∃ i : Fin 13, point i ∈ T
    · obtain ⟨a,ha⟩ := first
      have next (i : Fin 13) (hp : point i ∈ T) : point (i+1) ∈ T :=
        (cover _ _ (ring_edges i).2.1).resolve_right (disj i hp)
      have walk : ∀ j : ℕ, point (a + (j : Fin 13)) ∈ T := by
        intro j
        induction j with
        | zero => simpa using ha
        | succ j ih => simpa only [Nat.cast_succ, ← add_assoc] using next _ ih
      left
      intro b
      have hp : point b ∈ T := by simpa using walk (b-a).val
      exact ⟨hp,disj b hp⟩
    · right
      intro i
      have hp : point i ∉ T := fun h => first ⟨i,h⟩
      exact ⟨(cover _ _ (ring_edges i).1).resolve_left hp,hp⟩

  have crosses_cover (T : Finset (Fin 26)) (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T)
      (size : T.card ≤ 13) {a b : Fin 26} (edge : plane.Adj a b) : a ∈ T → b ∉ T := by
    have separate (a b : Fin 26) (h : forward a b) : ¬(a ∈ T ∧ b ∈ T) := by
      rcases cover_side T cover size with side | side
      · exact fun h2 => (side (label b)).2 ((endpoints b).2 h.2.1 ▸ h2.2)
      · exact fun h2 => (side (label a)).2 ((endpoints a).1 h.1 ▸ h2.1)
    intro ha hb
    rcases edge with h | h
    · exact separate a b h ⟨ha,hb⟩
    · exact separate b a h ⟨hb,ha⟩

  have count_all (U : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
      (h : U.card ≤ (U.filter P).card) : ∀ w ∈ U, P w := by
    have eq := Finset.eq_of_subset_of_card_le (Finset.filter_subset P U) h
    intro w hw
    have hw' : w ∈ U.filter P := eq.symm ▸ hw
    exact (Finset.mem_filter.mp hw').2

  let tightAt (gs : List Gate) (T : Finset (Fin 26)) : Prop :=
    let S := supports (n := 26) gs
    let nonempty := fun w => (S (firstWire 26 gs w)).Nonempty ∧ (S (secondWire 26 gs w)).Nonempty
    ∀ w, 27 ≤ w → w < 27 + gs.length →
      (andPos 26 gs w = true → nonempty w) ∧
      (andPos 26 gs w = false → 1 < (S w).card → nonempty w) ∧
      (andPos 26 gs w = false → (S w).card ≤ 1 → S w ⊆ T)

  have equality_orientation (gs : List Gate) (out : ℕ)
      (small : gs.length ≤ 64) (ops : binaryOps gs) (clean : cleanOn plane gs)
      (he : ∀ x : Fin 26 → Bool, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue plane x) :
      ∃ T : Finset (Fin 26), (∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card = 13 ∧ tightAt gs T := by
    classical
    let N : ℕ := 27 + gs.length
    let S := supports (n := 26) gs
    let A : ℕ → Bool := andPos 26 gs
    let a := firstWire 26 gs
    let b := secondWire 26 gs
    let r := clampWire (26 + gs.length) out
    let H (w : ℕ) (u v : Fin 26) := posRead gs w (pairBits u v) = true
    let live (w : ℕ) := (S (a w)).Nonempty ∧ (S (b w)).Nonempty
    let decideAndGate (k w : ℕ) (v : Bool) : Decidable (k ≤ w ∧ v = true) := inferInstance
    let decideLargeGate (k w c : ℕ) (v : Bool) : Decidable (k ≤ w ∧ v = false ∧ 1 < c) := inferInstance
    let decideSmallGate (k w c : ℕ) (v : Bool) : Decidable (k ≤ w ∧ v = false ∧ c ≤ 1) := inferInstance
    let predAS : ℕ → Prop := fun (w : ℕ) => 27 ≤ w ∧ A w = true
    let decAS : DecidablePred predAS := fun (w : ℕ) => decideAndGate 27 w (A w)
    let AS : Finset ℕ := @Finset.filter ℕ predAS decAS (Finset.range N)
    let predOS : ℕ → Prop := fun (w : ℕ) => 27 ≤ w ∧ A w = false ∧ 1 < (S w).card
    let decOS : DecidablePred predOS := fun (w : ℕ) => decideLargeGate 27 w (S w).card (A w)
    let OS : Finset ℕ := @Finset.filter ℕ predOS decOS (Finset.range N)
    let predXS : ℕ → Prop := fun (w : ℕ) => 27 ≤ w ∧ A w = false ∧ (S w).card ≤ 1
    let decXS : DecidablePred predXS := fun (w : ℕ) => decideSmallGate 27 w (S w).card (A w)
    let XS : Finset ℕ := @Finset.filter ℕ predXS decXS (Finset.range N)
    have hr : r < N := root_bound 26 gs.length out
    have hrS : S r = ∅ := root_support_empty plane gs out he
    have hrH : ∀ u v, plane.Adj u v → H r u v := root_hits plane gs out he
    have ha (w : ℕ) (lo : 27 ≤ w) (_hi : w < N) : a w < w := clamp_lt w _ (by omega)
    have hb (w : ℕ) (lo : 27 ≤ w) (_hi : w < N) : b w < w := clamp_lt w _ (by omega)
    have hzero : ∀ w, 27 ≤ w → w < N → A w = true → S w = ∅ := support_and plane gs clean
    have horS : ∀ w, 27 ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w) :=
      support_or plane gs ops clean
    have hjoin : ∀ w, 27 ≤ w → w < N → A w = true →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w), plane.Adj u v := cross_support plane gs ops clean
    have hinput : ∀ w u v, w < 27 → H w u v → u ∈ S w ∨ v ∈ S w := hit_base gs
    have ho (w : ℕ) (u v : Fin 26) (lo : 27 ≤ w) (hi : w < N) (h : A w = false) :
        H w u v → H (a w) u v ∨ H (b w) u v := by
      change andPos 26 gs w = false at h
      intro z
      simpa only [H,pos_gate plane gs ops clean w lo hi,h,Bool.false_eq_true,ite_false,Bool.or_eq_true]
        using z
    have hiAnd (w : ℕ) (u v : Fin 26) (lo : 27 ≤ w) (hi : w < N) (h : A w = true) :
        H w u v → H (a w) u v ∧ H (b w) u v := by
      change andPos 26 gs w = true at h
      intro z
      simpa only [H,pos_gate plane gs ops clean w lo hi,h,ite_true,Bool.and_eq_true] using z
    have hd (w : ℕ) (lo : 27 ≤ w) (hi : w < N) (h : A w = true) :
        Disjoint (S (a w)) (S (b w)) := by
      exact Finset.disjoint_left.mpr fun t ht ht' => plane.loopless.irrefl t (hjoin w lo hi h t ht t ht')
    have hside (w : ℕ) (lo : 27 ≤ w) (hi : w < N) (h : A w = true) :
        (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
      by_contra! hf
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
      obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
      have hj := hjoin w lo hi h
      exact plane_c4 u x v y huv hxy ⟨hj u hu x hx,(hj v hv x hx).symm,hj v hv y hy,(hj u hu y hy).symm⟩
    have births (u v : Fin 26) (huv : plane.Adj u v) := edge_birth 26 27 N r S H a b A u v hr
      (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS ho hiAnd hd
    have edges : 52 ≤ (AS.filter live).card + (OS.filter live).card := by
      rw [← plane_edges]
      exact tight_edges 26 27 N plane S a b A plane_c4 (support_base gs)
        (fun w lo hi => ⟨ha w lo hi, hb w lo hi⟩) hzero horS hjoin hside births
    obtain ⟨T,cover,hT⟩ := tight_cover 26 27 N r plane S H a b A hr hrS hrH hinput ha hb
      horS ho hside hiAnd hzero (fun f R B step => dag_union_bound f R B step)
    change T.card ≤ 1 + (XS.filter fun w => S w ⊆ T).card at hT
    have partition : AS.card + OS.card + XS.card ≤ gs.length := gate_partition_count 26 gs.length A S
    have lb := min_cover T cover
    have ac := Finset.card_filter_le AS live
    have oc := Finset.card_filter_le OS live
    have xc := Finset.card_filter_le XS (fun w => S w ⊆ T)
    refine ⟨T,cover,by omega,?_⟩
    intro w lo hi
    refine ⟨?_,?_,?_⟩
    · intro h
      exact count_all AS live (by omega) w (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,lo,h⟩)
    · intro h large
      exact count_all OS live (by omega) w (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,lo,h,large⟩)
    · intro h little
      exact count_all XS (fun w => S w ⊆ T) (by omega) w (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,lo,h,little⟩)

  have outside_eval (gs : List Gate) (ops : binaryOps gs) (clean : cleanOn plane gs)
      (T : Finset (Fin 26)) (tight : tightAt gs T) (u m : Fin 26) (hm : m ∈ T) (w : ℕ) :
      w < 27 + gs.length →
      (supports (n := 26) gs w).Nonempty →
      (∀ v ∈ supports (n := 26) gs w, v ∉ T) →
      posRead gs w (pairBits u m) = true → posRead gs w (singletonBits u) = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hi nonempty outside hit
      by_cases lo : 27 ≤ w
      · have ta := tight w lo hi
        cases ha : andPos 26 gs w with
        | true =>
          rw [support_and plane gs clean w lo hi ha] at nonempty
          simpa using nonempty
        | false =>
          have large : 1 < (supports (n := 26) gs w).card := by
            by_contra! h
            obtain ⟨v,hv⟩ := nonempty
            exact outside v hv (ta.2.2 ha h hv)
          have ne := ta.2.1 ha large
          have union := support_or plane gs ops clean w lo hi ha
          have a_lt : firstWire 26 gs w < w := clamp_lt w _ (by omega)
          have b_lt : secondWire 26 gs w < w := clamp_lt w _ (by omega)
          rw [pos_gate plane gs ops clean w lo hi, ha] at hit ⊢
          simp only [Bool.false_eq_true,ite_false,Bool.or_eq_true] at hit ⊢
          rcases hit with h | h
          · left
            exact ih _ a_lt (a_lt.trans hi) ne.1
              (fun v hv => outside v (union ▸ Finset.mem_union_left _ hv)) h
          · right
            exact ih _ b_lt (b_lt.trans hi) ne.2
              (fun v hv => outside v (union ▸ Finset.mem_union_right _ hv)) h
      · rcases hit_base gs w u m (by omega) hit with h | h
        · exact (mem_support gs w u).mp h
        · exact (outside m h hm).elim

  -- Position zero denotes a wire outside the circuit. Other positions are
  -- shifted by one, matching the representation in the public counting proof.
  let derivative (gs : List Gate) (u m : Fin 26) (D : ℕ → Bool) : Prop :=
    D 0 = false ∧ (∀ i : Fin 26, D (i.val + 1) = decide (i = m)) ∧
    ∀ w, 27 ≤ w → w < 27 + gs.length →
      let a := firstWire 26 gs w
      let b := secondWire 26 gs w
      D w = if andPos 26 gs w then
        ((posRead gs a (singletonBits u) && D b) || (D a && posRead gs b (singletonBits u)))
      else D a || D b

  have active_or_trace (gs : List Gate) (ops : binaryOps gs) (clean : cleanOn plane gs)
      (T : Finset (Fin 26)) (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T)
      (card : T.card = 13) (tight : tightAt gs T)
      (u m : Fin 26) (hm : m ∈ T) (D : ℕ → Bool) (deriv : derivative gs u m D) (w : ℕ) :
      w < 27 + gs.length → posRead gs w (pairBits u m) = true →
      posRead gs w (singletonBits u) = true ∨ D w = true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hi hit
      by_cases lo : 27 ≤ w
      · let a := firstWire 26 gs w
        let b := secondWire 26 gs w
        have ha : a < w := clamp_lt w _ (by omega)
        have hb : b < w := clamp_lt w _ (by omega)
        have dav := deriv.2.2 w lo hi
        rw [pos_gate plane gs ops clean w lo hi] at hit ⊢
        cases hand : andPos 26 gs w with
        | false =>
          simp only [hand, Bool.false_eq_true,ite_false,Bool.or_eq_true] at hit dav ⊢
          rw [dav,Bool.or_eq_true]
          rcases hit with h | h
          · rcases ih a ha (ha.trans hi) h with h | h <;> tauto
          · rcases ih b hb (hb.trans hi) h with h | h <;> tauto
        | true =>
          simp only [hand,ite_true,Bool.and_eq_true] at hit ⊢
          simp only [hand,ite_true] at dav
          rw [dav,Bool.or_eq_true,Bool.and_eq_true,Bool.and_eq_true]
          obtain ⟨na,nb⟩ := (tight w lo hi).1 hand
          obtain ⟨x,hx⟩ := na
          obtain ⟨y,hy⟩ := nb
          have cross := cross_support plane gs ops clean w lo hi hand
          have both := cover x y (cross x hx y hy)
          rcases both with h | h
          · have sole := outside_eval gs ops clean T tight u m hm b (hb.trans hi) ⟨y,hy⟩
              (fun z hz => crosses_cover T cover card.le (cross x hx z hz) h) hit.2
            rcases ih a ha (ha.trans hi) hit.1 with h | h <;> tauto
          · have sole := outside_eval gs ops clean T tight u m hm a (ha.trans hi) ⟨x,hx⟩
              (fun z hz => crosses_cover T cover card.le (cross z hz y hy).symm h) hit.1
            rcases ih b hb (hb.trans hi) hit.2 with h | h <;> tauto
      · cases w with
        | zero => simp [posRead] at hit
        | succ j =>
          have hj : j < 26 := by omega
          rw [pos_input gs j hj] at hit ⊢
          have din := deriv.2.1 (⟨j,hj⟩ : Fin 26)
          simp only [pairBits,decide_eq_true_eq] at hit
          rcases hit with h | h
          · exact Or.inl (by simpa only [singletonBits,decide_eq_true_eq] using h)
          · exact Or.inr (din.trans (decide_eq_true h))

  have root_has_trace (gs : List Gate) (out : ℕ)
      (ops : binaryOps gs) (clean : cleanOn plane gs)
      (he : ∀ x : Fin 26 → Bool, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue plane x)
      (T : Finset (Fin 26)) (cover : ∀ u v, plane.Adj u v → u ∈ T ∨ v ∈ T)
      (card : T.card = 13) (tight : tightAt gs T) (u m : Fin 26)
      (edge : plane.Adj u m) (hm : m ∈ T) (D : ℕ → Bool) (deriv : derivative gs u m D) :
      D (clampWire (26 + gs.length) out) = true := by
    let r := clampWire (26 + gs.length) out
    have pair := root_hits plane gs out he u m edge
    rcases active_or_trace gs ops clean T cover card tight u m hm D deriv r
        (root_bound 26 gs.length out) pair with h | h
    · rw [root_read] at h
      exact (edge_single plane u ((he _).mp h)).elim
    · exact h

  let Strict (C : Circuit) : Prop :=
    ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j

  let RawTrace (C : Circuit) (i k : ℕ) (v : ℕ → Bool) : Prop :=
    (∀ j < 26, v j = decide (j = k)) ∧
    (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
      let base := C.wires (List.ofFn fun t : Fin 26 => decide (t.val = i))
      (g.op = GateOp.and → v (26+j) = ((base.getD a false && v b) || (v a && base.getD b false))) ∧
      (g.op = GateOp.or → v (26+j) = (v a || v b))) ∧ v C.output = false

  let lifted (v : ℕ → Bool) (w : ℕ) : Bool := Nat.casesOn w false v

  have shifted_trace (C : Circuit) (strict : Strict C) (u m : Fin 26) (v : ℕ → Bool)
      (trace : RawTrace C u.val m.val v) : derivative C.gates u m (lifted v) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro i
      simpa only [lifted, Fin.ext_iff] using trace.1 i.val i.isLt
    · intro w lo hi
      let j := w - 27
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hw : w = 26+j+1 := by dsimp [j]; omega
      rw [hw]
      have get := List.getElem?_eq_getElem (l := C.gates) hj
      obtain ⟨hop,a,b,ins,_,ha,hb⟩ := strict j _ get
      have pa : firstWire 26 C.gates (26+j+1) = a+1 := by
        simp [firstWire, gateAt_index C.gates j hj, ins, clampWire, ha]
      have pb : secondWire 26 C.gates (26+j+1) = b+1 := by
        simp [secondWire, gateAt_index C.gates j hj, ins, clampWire, hb]
      rw [pa,pb]
      have single : (fun t : Fin 26 => decide (t.val = u.val)) = singletonBits u := by
        funext t
        simp [singletonBits,Fin.ext_iff]
      have e := trace.2.1 j C.gates[j] a b get ins
      dsimp only at e
      rw [single] at e
      rcases hop with h | h
      · have op : andPos 26 C.gates (26+j+1) = true := by simp [andPos, gateAt_index C.gates j hj, h, andFlag]
        simpa only [op,ite_true,lifted,posRead,wires_eq] using e.1 h
      · have op : andPos 26 C.gates (26+j+1) = false := by simp [andPos, gateAt_index C.gates j hj, h, andFlag]
        simpa only [op,Bool.false_eq_true,ite_false,lifted,posRead] using e.2 h

  let Dirty (C : Circuit) : Prop := ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
    ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26+j) false = true ∧
      C.eval (List.ofFn x) = false

  -- At the fixed incidence, at least one endpoint has a first-order witness
  -- in any clean circuit of size at most 64. Hence a candidate must contain
  -- an AND which fires on an input rejected by the output.
  have fixed_pair_forces_dirty (C : Circuit) (small : C.size ≤ 64)
      (strict : Strict C) (exactC : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, inc p l ∧ x (point p) = true ∧ x (line l) = true)
      (v w : ℕ → Bool) (vTrace : RawTrace C 0 13 v) (wTrace : RawTrace C 13 0 w) : Dirty C := by
    classical
    by_contra h
    have he (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔ edgeTrue plane x :=
      (exactC x).trans (incidence_iff x).symm
    have clean : cleanOn plane C.gates := by
      intro j x op hit
      by_contra miss
      have off : C.eval (List.ofFn x) = false := Bool.eq_false_iff.mpr ((he x).not.mpr miss)
      exact h ⟨j.val,C.gates[j.val],List.getElem?_eq_getElem j.isLt,op,x,hit,off⟩
    have ops : binaryOps C.gates := by
      intro g hg
      obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hg
      subst g
      obtain ⟨op,a,b,ins,_⟩ := strict j _ (List.getElem?_eq_getElem hj)
      exact ⟨op,by simp [ins]⟩
    obtain ⟨T,cover,card,tight⟩ := equality_orientation C.gates C.output small ops clean he
    have cannot (a b : Fin 26) (eab : plane.Adj a b) (hb : b ∈ T) (d : ℕ → Bool)
        (hd : RawTrace C a.val b.val d) : False := by
      have der := shifted_trace C strict a b d hd
      have atRoot := root_has_trace C.gates C.output ops clean he T cover card tight a b eab hb (lifted d) der
      unfold clampWire at atRoot
      split at atRoot <;> simp [lifted,hd.2.2] at atRoot
    have edge : plane.Adj 0 13 := by decide
    rcases cover 0 13 edge with hp | hl
    · exact cannot 13 0 edge.symm hp w wTrace
    · exact cannot 0 13 edge hl v vTrace

  let rowMasks : List ℕ :=
    [15860,23529,38867,69543,139086,269981,531771,1055351,2102511,4196831,
     8393662,16779133,33558266,67100672]
  let lineTest (k : Fin 14) (v : Fin 26) : Bool := (rowMasks.getD k.val 0).testBit v.val

  have row_rejected : ∀ k : Fin 14, ¬ edgeTrue plane (lineTest k) := by
    dsimp only [edgeTrue,plane,forward,inc,label,lineTest,rowMasks]
    decide

  have hits_nonedges : ∀ u v : Fin 26, ¬plane.Adj u v →
      ∃ k : Fin 14, lineTest k u = true ∧ lineTest k v = true := by
    dsimp only [plane,forward,inc,label,lineTest,rowMasks]
    decide

  let valAt (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
    (wiresFrom C.gates (List.ofFn x)).getD w false

  have raw_at (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (h : w < 26) :
      valAt C x w = x ⟨w,h⟩ := pos_input C.gates w h x

  have binary_at (C : Circuit) (x : Fin 26 → Bool) (j : ℕ) (hj : j < C.gates.length)
      (a b : ℕ) (ins : C.gates[j].inputs = [a,b]) (ha : a < 26+j) (hb : b < 26+j) :
      (C.gates[j].op = GateOp.and →
        valAt C x (26+j) = (valAt C x a && valAt C x b)) ∧
      (C.gates[j].op = GateOp.or →
        valAt C x (26+j) = (valAt C x a || valAt C x b)) := by
    have h := getD_wiresFrom_gate C.gates (List.ofFn x) j hj
    constructor <;> intro op <;>
      simpa only [List.length_ofFn,ins,List.map_cons,List.map_nil,ha,hb,ite_true,op,eval_and, eval_or, andFlag,
        List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false,valAt] using h

  have dirty_on_row (C : Circuit) (strict : Strict C)
      (he : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ edgeTrue plane x)
      (dirty : Dirty C) :
      ∃ (k : Fin 14) (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        (C.wires (List.ofFn (lineTest k))).getD (26+j) false = true := by
    classical
    obtain ⟨t,g,get,hop,x,fire,off⟩ := dirty
    obtain ⟨ht,eg⟩ := List.getElem?_eq_some_iff.mp get
    subst g
    let on (j : ℕ) : Prop := ∃ hj : j < C.gates.length,
      C.gates[j].op = GateOp.and ∧ valAt C x (26+j) = true
    have ex : ∃ j, on j := ⟨t,ht,hop,fire⟩
    let j := Nat.find ex
    obtain ⟨hj,op,hit⟩ := Nat.find_spec ex
    have leaf (w : ℕ) : w < 26+j → valAt C x w = true →
        ∃ v : Fin 26, x v = true ∧ ∀ y : Fin 26 → Bool, y v = true → valAt C y w = true := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw yes
        by_cases raw : w < 26
        · exact ⟨⟨w,raw⟩,(raw_at C x w raw).symm.trans yes,
            fun y hy => (raw_at C y w raw).trans hy⟩
        let i := w - 26
        have early : i < j := by dsimp [i]; omega
        have old : i < C.gates.length := early.trans hj
        have ew : w = 26+i := by dsimp [i]; omega
        obtain ⟨alt,a,b,ins,_,ha,hb⟩ := strict i _ (List.getElem?_eq_getElem old)
        rcases alt with haOp | hoOp
        · exact ((Nat.find_min ex early) ⟨old,haOp,ew ▸ yes⟩).elim
        · rw [ew,(binary_at C x i old a b ins ha hb).2 hoOp,Bool.or_eq_true] at yes
          rcases yes with yes | yes
          · obtain ⟨v,hv,pure⟩ := ih a (by omega) (by omega) yes
            exact ⟨v,hv,fun y hy => by rw [ew,(binary_at C y i old a b ins ha hb).2 hoOp,
              pure y hy,Bool.true_or]⟩
          · obtain ⟨v,hv,pure⟩ := ih b (by omega) (by omega) yes
            exact ⟨v,hv,fun y hy => by rw [ew,(binary_at C y i old a b ins ha hb).2 hoOp,
              pure y hy,Bool.or_true]⟩
    obtain ⟨_,a,b,ins,_,ha,hb⟩ := strict j _ (List.getElem?_eq_getElem hj)
    change valAt C x (26+j) = true at hit
    rw [(binary_at C x j hj a b ins ha hb).1 op,Bool.and_eq_true] at hit
    obtain ⟨u,hu,left⟩ := leaf a ha hit.1
    obtain ⟨v,hv,right⟩ := leaf b hb hit.2
    have nonEdge : ¬ plane.Adj u v := fun edge =>
      Bool.noConfusion (off.symm.trans ((he x).mpr ⟨u,v,edge,hu,hv⟩))
    obtain ⟨k,hku,hkv⟩ := hits_nonedges u v nonEdge
    refine ⟨k,j,C.gates[j],List.getElem?_eq_getElem hj,op,?_⟩
    change valAt C (lineTest k) (26+j) = true
    rw [(binary_at C _ j hj a b ins ha hb).1 op, left _ hku, right _ hkv]
    rfl

  have fourteen_forced (C : Circuit) (small : C.size ≤ 64) (strict : Strict C)
      (exactC : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, inc p l ∧ x (point p) = true ∧ x (line l) = true)
      (v w : ℕ → Bool) (h₁ : RawTrace C 0 13 v) (h₂ : RawTrace C 13 0 w) :
      ∃ (k : Fin 14) (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        (C.wires (List.ofFn (lineTest k))).getD (26+j) false = true ∧
          C.eval (List.ofFn (lineTest k)) = false := by
    have he (x : Fin 26 → Bool) := (exactC x).trans (incidence_iff x).symm
    obtain ⟨k,j,g,hg,ho,yes⟩ := dirty_on_row C strict he
      (fixed_pair_forces_dirty C small strict exactC v w h₁ h₂)
    refine ⟨k,j,g,hg,ho,yes,Bool.eq_false_iff.mpr ?_⟩
    intro h
    exact row_rejected k ((he _).mp h)

  rintro ⟨C,lo,hi,basis,eq,⟨v,hv⟩,w,hw⟩
  obtain ⟨k,j,g,get,op,fire,_⟩ := fourteen_forced C hi basis eq v w hv hw
  obtain ⟨hj,e⟩ := List.getElem?_eq_some_iff.mp get
  subst g
  have std : PEqualNP.MinimumComplex.Strict 26 C := by
    intro t ht
    obtain ⟨ops,a,b,inputs,distinct,ha,hb⟩ := basis t _ (List.getElem?_eq_getElem ht)
    refine Or.inl ⟨ops,by simp [inputs],by simpa [inputs] using distinct,?_⟩
    intro i mem
    simp [inputs] at mem
    rcases mem with rfl | rfl <;> assumption
  have ao : PEqualNP.EdgeOwnership.AndOrOnly C := by
    intro gate mem
    obtain ⟨t,ht,eg⟩ := List.getElem_of_mem mem
    exact (basis t gate (by simp only [List.getElem?_eq_getElem ht,eg])).1
  exact dirtyCase C v w lo hi std ao eq hv hw ⟨k,⟨j,hj⟩,op,fire⟩
