import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3580

-- Gate deletion and evaluation agreement adapted from upstream L-meta-1975 and L-meta-522.
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

private def reads (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

private def trim (g : Gate) : Gate := ⟨g.op, reads g⟩

private lemma trim_ok (g : Gate) (h : OkGate g) : OkGate (trim g) := by
  refine ⟨h.1, ?_⟩
  have hlen := h.2
  simp only [trim, reads, List.length_take]
  omega

private lemma trim_id (g : Gate) : reads (trim g) = (trim g).inputs := by
  simp [trim, reads, List.take_take]

private lemma trim_eq (g : Gate) (h : OkGate g) (w : List Bool) :
    (trim g).op.eval ((trim g).inputs.map fun i => w.getD i false) =
    g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hl := h.2
  rcases (show g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not by
    simpa [OkGate] using h.1) with hop | hop | hop
  · simp [trim, reads, hop, GateOp.eval, List.take_of_length_le hl]
  · simp [trim, reads, hop, GateOp.eval, List.take_of_length_le hl]
  · cases hlist : g.inputs with
    | nil => simp [trim, reads, hop, GateOp.eval, hlist]
    | cons a l => simp [trim, reads, hop, GateOp.eval, hlist]

private lemma trim_wires (gs : List Gate) (hok : ∀ g ∈ gs, OkGate g) (w : List Bool) :
    wiresFrom (gs.map trim) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, trim_eq g (hok g List.mem_cons_self)]
    exact ih (fun a ha => hok a (List.mem_cons_of_mem _ ha)) _

private lemma minClean (n : ℕ) (C : Circuit) (hC : FanInTwo C)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j : Fin n, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    ∃ E : Circuit, E.size ≤ C.size ∧ FanInTwo E ∧ circuitFun n E = circuitFun n C ∧
      ∀ w < n + E.size, w ≠ E.output → w ∈ E.gates.flatMap reads := by
  classical
  let P : ℕ → Prop := fun s =>
    ∃ D : Circuit, FanInTwo D ∧ D.size = s ∧ circuitFun n D = circuitFun n C
  have hex : ∃ s, P s := ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨D, hD, hDs, hDe⟩ := Nat.find_spec hex
  let E : Circuit := ⟨D.gates.map trim, D.output⟩
  have hEs : E.size = D.size := by simp [E, Circuit.size]
  have hE : FanInTwo E := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    exact trim_ok q (hD q hq)
  have hDE : circuitFun n E = circuitFun n D := by
    funext x
    change (wiresFrom (D.gates.map trim) (List.ofFn x)).getD D.output false =
      (wiresFrom D.gates (List.ofFn x)).getD D.output false
    rw [trim_wires D.gates hD]
  have hEe : circuitFun n E = circuitFun n C := hDE.trans hDe
  have hmin (F : Circuit) (hf : FanInTwo F) (hfe : circuitFun n F = circuitFun n C) :
      E.size ≤ F.size := by
    rw [hEs, hDs]
    exact Nat.find_min' hex (show P F.size from ⟨F, hf, rfl, hfe⟩)
  refine ⟨E, hmin C hC rfl, hE, hEe, ?_⟩
  intro w hw hout
  by_contra hm
  have hno : ∀ g ∈ E.gates, w ∉ g.inputs := by
    intro g hg hm'
    have hid : reads g = g.inputs := by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact trim_id q
    exact hm (List.mem_flatMap.mpr ⟨g, hg, hid.symm ▸ hm'⟩)
  by_cases hin : w < n
  · let i : Fin n := ⟨w, hin⟩
    obtain ⟨x, y, hag, hxy⟩ := he i
    apply hxy
    rw [← hEe]
    have hm2 : ∀ j ∉ ({w} : Set ℕ), (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
      intro j hj
      by_cases hjn : j < n
      · rw [ofFn_getD_lt _ _ _ hjn, ofFn_getD_lt _ _ _ hjn]
        apply hag
        intro heq
        exact hj (Set.mem_singleton_iff.mpr (congrArg Fin.val heq))
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hjn),
            List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hjn)]
    have hr := wiresFrom_agree E.gates ({w} : Set ℕ) (List.ofFn x) (List.ofFn y)
      (by simp) (by intro j hj; have hjw : j = w := Set.mem_singleton_iff.mp hj; simpa [hjw] using hin)
      hm2 (by intro g hg j hj hs; exact hno g hg (Set.mem_singleton_iff.mp hs ▸ hj))
    exact hr.2 E.output (by simpa using Ne.symm hout)
  · let j := w - n
    have hjw : n + j = w := by dsimp [j]; omega
    have hj : j < E.gates.length := by change w < n + E.gates.length at hw; omega
    obtain ⟨F, hf, hfs, hfe⟩ := deleteDeadGate (m := n) E hE j hj (by simpa [hjw] using Ne.symm hout)
      (fun j' hj' hjlt => by rw [hjw]; exact hno _ (List.getElem_mem hj'))
    have hfeq : circuitFun n F = circuitFun n C :=
      (funext hfe).trans hEe
    have hle := hmin F hf hfeq
    change E.gates.length ≤ F.gates.length at hle
    change F.gates.length ≤ E.gates.length - 1 at hfs
    omega

private theorem readsBound (gates : List PEqualNP.CircuitLowerBounds.Gate) :
    (gates.flatMap (fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2))).length +
      (gates.filter (fun g => g.op.eval [false])).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp
  | cons g gs ih =>
    cases h : g.op.eval [false] <;>
      simp [List.flatMap_cons, h, List.length_take] at * <;> omega

private theorem readsCardBound (reads : List ℕ) (k output : ℕ)
    (hc : ∀ i < k, i ≠ output → i ∈ reads) : k ≤ reads.toFinset.card + 1 := by
  classical
  have hsub : Finset.range k ⊆ insert output reads.toFinset := by
    intro i hi
    by_cases h : i = output
    · simp [h]
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (hc i (Finset.mem_range.mp hi) h))
  have hcard : k ≤ (insert output reads.toFinset).card := by simpa using Finset.card_le_card hsub
  exact hcard.trans (Finset.card_insert_le _ _)

theorem countUsed (n : ℕ) (c : PEqualNP.CircuitLowerBounds.Circuit)
    (hc : ∀ i < n + c.size, i ≠ c.output →
      i ∈ c.gates.flatMap (fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2))) :
    let reads := c.gates.flatMap (fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2))
    (c.gates.filter (fun g => g.op.eval [false])).length +
      (reads.length - reads.toFinset.card) ≤ c.size + 1 - n := by
  dsimp only
  let reads := c.gates.flatMap (fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2))
  change (c.gates.filter (fun g => g.op.eval [false])).length +
    (reads.length - reads.toFinset.card) ≤ c.size + 1 - n
  have hb := readsBound c.gates
  change reads.length + (c.gates.filter (fun g => g.op.eval [false])).length ≤ 2*c.size at hb
  have hd : n + c.size ≤ reads.toFinset.card + 1 := readsCardBound reads (n+c.size) c.output hc
  have hl : reads.toFinset.card ≤ reads.length := List.toFinset_card_le reads
  omega

end PEqualNP.Outside.L_meta_3580

theorem PEqualNP.Outside.L_meta_3580 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin x1), ∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), (∀ (x8 : Fin x1), x8 ≠ x5 → x6 x8 = x7 x8) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x6 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x7) →         ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),           x6.size ≤ x2.size ∧             PEqualNP.MetaComplexity.FanInTwo x6 ∧               PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧                 have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs) x6.gates;                 (∀ x8 < x1 + x6.size, x8 ≠ x6.output → x8 ∈ x7) ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x6.gates).length + (x7.length - x7.toFinset.card) ≤ x6.size + (1 : ℕ) - x1 := by
  intro n C hn hC he
  obtain ⟨E, hs, hf, hfn, hused⟩ := PEqualNP.Outside.L_meta_3580.minClean n C hC he
  refine ⟨E, hs, hf, hfn, hused, ?_⟩
  exact PEqualNP.Outside.L_meta_3580.countUsed n E hused

