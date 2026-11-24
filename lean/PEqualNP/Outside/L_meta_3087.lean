import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3087

-- Dead gate deletion and slot accounting are adapted from the proof of L-meta-1975.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private def slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

private lemma countBound (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

private lemma essentialSlot {n : ℕ} (C : Circuit) (a : Fin n)
    (dep : ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
    (a : ℕ) ∈ slots C := by
  obtain ⟨x, y, hagree, hne⟩ := dep
  by_contra hn
  have hout : C.output ≠ (a : ℕ) := by
    intro he
    exact hn (by simp [slots, he])
  have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({↑a} : Set ℕ) := by
    intro g hg i hi hia
    have hi' : i = (a : ℕ) := hia
    exact hn (by apply List.mem_cons_of_mem; exact List.mem_flatMap.mpr ⟨g,hg,hi' ▸ hi⟩)
  apply hne
  apply (wiresFrom_agree C.gates ({↑a} : Set ℕ) (List.ofFn x) (List.ofFn y)
    (by simp) (by simp) ?_ noRead).2 C.output hout
  intro i hi
  by_cases h : i < n
  · rw [ofFn_getD_lt _ _ _ h, ofFn_getD_lt _ _ _ h]
    exact hagree _ (fun he => hi (congrArg Fin.val he))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
    (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (i : ℕ) (hi : i < C.gates.length) : n+i ∈ slots C := by
  by_contra hn
  have hout : C.output ≠ n+i := fun e => hn (by simp [slots,e])
  have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
    intro j hj _ hm
    exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
  have bad := hmin _ (deleteDeadGate C hC i hi hout hno)
  change C.gates.length ≤ C.gates.length - 1 at bad
  omega

private def isNot (g : Gate) : Bool := g.op.eval [false] && !g.op.eval [true]

private def trimGate (bound : ℕ) (g : Gate) : Gate :=
  ⟨g.op, (if isNot g then g.inputs.take 1 else g.inputs).map (min bound)⟩

private lemma readMin (w : List Bool) (bound i : ℕ) (h : w.length ≤ bound) :
    w.getD (min bound i) false = w.getD i false := by
  by_cases hi : i ≤ bound
  · rw [min_eq_right hi]
  · rw [min_eq_left (by omega : bound ≤ i), List.getD_eq_default _ _ h,
      List.getD_eq_default _ _ (by omega)]

private lemma trimStep (bound : ℕ) (g : Gate) (w : List Bool)
    (h : w.length ≤ bound) (hg : OkGate g) :
    (trimGate bound g).op.eval ((trimGate bound g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hm (xs : List ℕ) : ((xs.map (min bound)).map fun i => w.getD i false) =
      xs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact readMin w bound i h
  change g.op.eval (((if isNot g then g.inputs.take 1 else g.inputs).map (min bound)).map
    fun i => w.getD i false) = _
  rw [hm]
  have hop := hg.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · simp [isNot, hop, GateOp.eval]
  · simp [isNot, hop, GateOp.eval]
  · cases g.inputs <;> simp [isNot, hop, GateOp.eval]

private lemma trimArity (bound : ℕ) (g : Gate) (h : OkGate g) :
    (trimGate bound g).inputs.length + (if isNot (trimGate bound g) then 1 else 0) ≤ 2 := by
  change ((if isNot g then g.inputs.take 1 else g.inputs).map (min bound)).length +
    (if isNot g then 1 else 0) ≤ 2
  rw [List.length_map]
  by_cases hn : isNot g = true
  · have ht : (g.inputs.take 1).length ≤ 1 := by simp
    simp only [hn, ite_true]
    omega
  · simpa [hn] using h.2

private lemma trimOk (bound : ℕ) (g : Gate) (h : OkGate g) : OkGate (trimGate bound g) :=
  ⟨h.1, (Nat.le_add_right _ _).trans (trimArity bound g h)⟩

private lemma trimWires (bound : ℕ) (gs : List Gate) (w : List Bool)
    (h : w.length + gs.length ≤ bound) (hok : ∀ g ∈ gs, OkGate g) :
    wiresFrom (gs.map (trimGate bound)) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g tail ih =>
    have hw : w.length ≤ bound := by omega
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, trimStep bound g w hw (hok g (by simp))]
    apply ih
    · simp at h ⊢
      omega
    · intro a ha
      exact hok a (List.mem_cons_of_mem _ ha)

private def trimCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (trimGate (n + C.size)), min (n + C.size) C.output⟩

private lemma trimSize (n : ℕ) (C : Circuit) : (trimCircuit n C).size = C.size := by
  simp [trimCircuit, Circuit.size]

private lemma trimFan (n : ℕ) (C : Circuit) (h : FanInTwo C) : FanInTwo (trimCircuit n C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  exact trimOk _ a (h a ha)

private lemma trimFun (n : ℕ) (C : Circuit) (h : FanInTwo C) :
    circuitFun n (trimCircuit n C) = circuitFun n C := by
  funext x
  change (wiresFrom (C.gates.map (trimGate (n + C.size))) (List.ofFn x)).getD
    (min (n + C.size) C.output) false = (wiresFrom C.gates (List.ofFn x)).getD C.output false
  rw [trimWires _ _ _ (by simp [Circuit.size]) h]
  apply readMin
  simp [wiresFrom_length, Circuit.size]

private lemma trimBounds (n : ℕ) (C : Circuit) :
    (trimCircuit n C).output ≤ n + (trimCircuit n C).size ∧
      ∀ g ∈ (trimCircuit n C).gates, ∀ i ∈ g.inputs, i ≤ n + (trimCircuit n C).size := by
  rw [trimSize]
  refine ⟨Nat.min_le_left _ _, ?_⟩
  intro g hg i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_left _ _

private lemma slotLength (gs : List Gate)
    (h : ∀ g ∈ gs, g.inputs.length + (if isNot g then 1 else 0) ≤ 2) :
    (gs.flatMap Gate.inputs).length + (gs.filter isNot).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tail ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.filter_cons]
    by_cases hn : isNot g = true
    · rw [if_pos hn] at hg
      rw [if_pos hn, List.length_cons]
      omega
    · rw [if_neg hn] at hg ⊢
      omega

private lemma totalExcess (C : Circuit)
    (h : ∀ i < 10 + C.size, i ∈ slots C)
    (ha : ∀ g ∈ C.gates, g.inputs.length + (if isNot g then 1 else 0) ≤ 2) :
    9 + (C.gates.filter isNot).length +
        ∑ i ∈ Finset.range (10 + C.size), ((slots C).count i - 1) ≤ C.size := by
  let R := Finset.range (10 + C.size)
  have hp (i : ℕ) (hi : i ∈ R) : 1 ≤ (slots C).count i :=
    List.count_pos_iff.mpr (h i (Finset.mem_range.mp hi))
  have hsum : (∑ i ∈ R, ((slots C).count i - 1)) + (10 + C.size) =
      ∑ i ∈ R, (slots C).count i := by
    calc
      _ = ∑ i ∈ R, ((slots C).count i - 1 + 1) := by
        rw [Finset.sum_add_distrib]
        simp [R]
      _ = _ := Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hp i hi))
  have hcounts : (∑ i ∈ R, (slots C).count i) ≤ (C.gates.flatMap Gate.inputs).length + 1 :=
    countBound (slots C) R
  have hslots := slotLength C.gates ha
  change (C.gates.flatMap Gate.inputs).length + (C.gates.filter isNot).length ≤ 2 * C.size at hslots
  change 9 + (C.gates.filter isNot).length + ∑ i ∈ R, ((slots C).count i - 1) ≤ C.size
  omega

end PEqualNP.Outside.L_meta_3087

open PEqualNP.Outside.L_meta_3087


theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  classical
  intro C hC hEssential
  have ex : ∃ s, HasCircuitSize 10 (circuitFun 10 C) s :=
    ⟨C.size, C, hC, le_rfl, fun _ => rfl⟩
  obtain ⟨D, hD, hDsize, hDF⟩ := Nat.find_spec ex
  let E := trimCircuit 10 D
  have hEsize : E.size = D.size := trimSize _ _
  have hEfan : FanInTwo E := trimFan _ _ hD
  have hEq : circuitFun 10 E = circuitFun 10 C := (trimFun _ _ hD).trans (funext hDF)
  have hmin (s : ℕ) (hs : HasCircuitSize 10 (circuitFun 10 E) s) : E.size ≤ s := by
    rw [hEsize]
    exact hDsize.trans (Nat.find_min' ex (by simpa only [hEq] using hs))
  have coverage (i : ℕ) (hi : i < 10 + E.size) : i ∈ slots E := by
    by_cases hin : i < 10
    · apply essentialSlot E (⟨i, hin⟩ : Fin 10)
      rw [hEq]
      exact hEssential ⟨i, hin⟩
    · have hj : i - 10 < E.gates.length := by
        change i < 10 + E.gates.length at hi
        omega
      have hh := internalSlot E hEfan hmin (i - 10) hj
      rwa [Nat.add_sub_of_le (by omega : 10 ≤ i)] at hh
  have arity (g : Gate) (hg : g ∈ E.gates) :
      g.inputs.length + (if isNot g then 1 else 0) ≤ 2 := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact trimArity _ a (hD a ha)
  refine ⟨E, hEfan, hEq, hmin C.size ?_, trimBounds 10 D, coverage, totalExcess E coverage arity⟩
  rw [hEq]
  exact ⟨C, hC, le_rfl, fun _ => rfl⟩
