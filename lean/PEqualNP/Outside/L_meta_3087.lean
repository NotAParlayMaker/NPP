import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3087

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma getD_append_lt (w u : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ u).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_append_len (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def ins (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

lemma eval_take_not (l : List Bool) : GateOp.not.eval (l.take 1) = GateOp.not.eval l := by
  cases l <;> rfl

lemma eval_ins (g : Gate) (f : ℕ → Bool) : g.op.eval ((ins g).map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp only [ins]
  rw [List.map_take, eval_take_not]

lemma ins_len (g : Gate) : (ins g).length ≤ g.inputs.length := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [ins]

lemma ins_len_not (g : Gate) (h : g.op = GateOp.not) : (ins g).length ≤ 1 := by
  obtain ⟨op, l⟩ := g
  subst h
  simp [ins]

def normGate (N k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, (ins g).map (fun i => if i < k then i else N)⟩

def normGates (N : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => normGate N k g :: normGates N (k + 1) gs

lemma normGates_length (N k : ℕ) (gs : List Gate) : (normGates N k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [normGates, ih]

lemma step_normGate (N : ℕ) (w : List Bool) (g : Gate) (hN : w.length ≤ N) :
    step w (normGate N w.length g) = step w g := by
  have key : (fun i => w.getD i false) ∘ (fun i => if i < w.length then i else N) =
      fun i => w.getD i false := by
    funext i
    simp only [Function.comp]
    split_ifs with h
    · rfl
    · rw [getD_ge w N hN, getD_ge w i (by omega)]
  unfold step normGate
  dsimp only
  rw [List.map_map, key, eval_ins]

lemma foldl_normGates (N : ℕ) (gs : List Gate) (w : List Bool) (hN : w.length + gs.length ≤ N) :
    (normGates N w.length gs).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons] at hN
    simp only [normGates, List.foldl_cons]
    rw [step_normGate N w g (by omega)]
    have hl : (step w g).length = w.length + 1 := by simp [step]
    rw [← hl]
    exact ih (step w g) (by rw [hl]; omega)

def normC (C : Circuit) : Circuit :=
  ⟨normGates (10 + C.gates.length) 10 C.gates,
    if C.output < 10 + C.gates.length then C.output else 10 + C.gates.length⟩

lemma normC_fun (C : Circuit) : circuitFun 10 (normC C) = circuitFun 10 C := by
  funext x
  unfold circuitFun Circuit.eval
  rw [wires_eq, wires_eq]
  have hx : (List.ofFn x).length = 10 := List.length_ofFn
  have h1 : (normC C).gates.foldl step (List.ofFn x) = C.gates.foldl step (List.ofFn x) := by
    show (normGates (10 + C.gates.length) 10 C.gates).foldl step (List.ofFn x) = _
    have := foldl_normGates (10 + C.gates.length) C.gates (List.ofFn x) (by rw [hx])
    rwa [hx] at this
  rw [h1]
  have hl : (C.gates.foldl step (List.ofFn x)).length = 10 + C.gates.length := by
    rw [length_foldl, hx]
  show (C.gates.foldl step (List.ofFn x)).getD
    (if C.output < 10 + C.gates.length then C.output else 10 + C.gates.length) false = _
  split_ifs with h
  · rfl
  · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]

def GoodGate (N : ℕ) (g : Gate) : Prop :=
  (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    (g.op = GateOp.not → g.inputs.length ≤ 1) ∧ ∀ i ∈ g.inputs, i ≤ N

lemma normGates_good (N : ℕ) (gs : List Gate) (k : ℕ)
    (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hk : k + gs.length ≤ N) : ∀ g ∈ normGates N k gs, GoodGate N g := by
  induction gs generalizing k with
  | nil => simp [normGates]
  | cons g gs ih =>
    intro g' hg'
    simp only [List.length_cons] at hk
    simp only [normGates, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · have hg := hf g (by simp)
      refine ⟨⟨hg.1, ?_⟩, ?_, ?_⟩
      · simp only [normGate, List.length_map]
        exact le_trans (ins_len g) hg.2
      · intro h
        simp only [normGate, List.length_map] at h ⊢
        exact ins_len_not g h
      · intro i hi
        simp only [normGate, List.mem_map] at hi
        obtain ⟨j, _, rfl⟩ := hi
        split_ifs <;> omega
    · exact ih (k + 1) (fun g h => hf g (by simp [h])) (by omega) g' hg'

def sh (m i : ℕ) : ℕ := if m < i then i - 1 else i

def shGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh m)⟩

lemma foldl_del (m : ℕ) (gs : List Gate) (u u' : List Bool) (hm : m < u.length)
    (hl : u.length = u'.length + 1)
    (hr : ∀ i, i ≠ m → u.getD i false = u'.getD (sh m i) false)
    (hg : ∀ g ∈ gs, m ∉ g.inputs) :
    ∀ i, i ≠ m → (gs.foldl step u).getD i false =
      ((gs.map (shGate m)).foldl step u').getD (sh m i) false := by
  induction gs generalizing u u' with
  | nil => exact hr
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hv : g.op.eval (g.inputs.map fun i => u.getD i false) =
        (shGate m g).op.eval ((shGate m g).inputs.map fun i => u'.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hr i (fun h => hg g (by simp) (h ▸ hi))
    apply ih
    · simp [step]; omega
    · simp [step]; omega
    · intro i hi
      unfold step
      rw [hv]
      rcases lt_trichotomy i u.length with h | h | h
      · rw [getD_append_lt _ _ _ h, getD_append_lt, hr i hi]
        unfold sh
        split_ifs <;> omega
      · subst h
        have : sh m u.length = u'.length := by
          unfold sh
          split_ifs <;> omega
        rw [this, getD_append_len, getD_append_len]
      · rw [getD_ge, getD_ge]
        · simp only [List.length_append, List.length_singleton]
          unfold sh
          split_ifs <;> omega
        · simp only [List.length_append, List.length_singleton]
          omega
    · exact fun g h => hg g (by simp [h])

def delC (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (shGate (10 + j)), sh (10 + j) C.output⟩

lemma delC_fun (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (ho : 10 + j ≠ C.output)
    (hg : ∀ g ∈ C.gates, 10 + j ∉ g.inputs) :
    circuitFun 10 (delC C j) = circuitFun 10 C := by
  funext x
  unfold circuitFun Circuit.eval
  rw [wires_eq, wires_eq]
  have hx : (List.ofFn x).length = 10 := List.length_ofFn
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  show ((C.gates.take j ++ (C.gates.drop (j + 1)).map (shGate (10 + j))).foldl step
    (List.ofFn x)).getD (sh (10 + j) C.output) false = _
  have hwl : ((C.gates.take j).foldl step (List.ofFn x)).length = 10 + j := by
    rw [length_foldl, hx, List.length_take]
    omega
  generalize hw : (C.gates.take j).foldl step (List.ofFn x) = w at hwl
  conv_rhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, hw]
  symm
  apply foldl_del (10 + j) (C.gates.drop (j + 1)) (step w C.gates[j]) w
  · simp [step]; omega
  · simp [step]
  · intro i hi
    unfold step
    rcases lt_or_ge i w.length with h | h
    · rw [getD_append_lt _ _ _ h]
      unfold sh
      split_ifs <;> first | rfl | omega
    · rw [getD_ge, getD_ge]
      · unfold sh
        split_ifs <;> omega
      · simp only [List.length_append, List.length_singleton]
        omega
  · intro g hg'
    exact hg g (List.mem_of_mem_drop hg')
  · exact ho.symm

lemma getD_ofFn (x : Fin 10 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  · exact getD_ge _ _ (by simp; omega)

lemma foldl_indep (v : ℕ) (gs : List Gate) (u u' : List Bool) (hl : u.length = u'.length)
    (hr : ∀ i, i ≠ v → u.getD i false = u'.getD i false) (hg : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ i, i ≠ v → (gs.foldl step u).getD i false = (gs.foldl step u').getD i false := by
  induction gs generalizing u u' with
  | nil => exact hr
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hv : (g.inputs.map fun i => u.getD i false) = (g.inputs.map fun i => u'.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hr i (fun h => hg g (by simp) (h ▸ hi))
    apply ih
    · simp [step, hl]
    · intro i hi
      unfold step
      rw [hv]
      rcases lt_trichotomy i u.length with h | h | h
      · rw [getD_append_lt _ _ _ h, getD_append_lt _ _ _ (hl ▸ h), hr i hi]
      · subst h
        rw [getD_append_len, hl, getD_append_len]
      · rw [getD_ge, getD_ge]
        · simp only [List.length_append, List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton]
          omega
    · exact fun g h => hg g (by simp [h])

lemma sum_count_le (M : ℕ) (L : List ℕ) : ∑ v ∈ Finset.range M, L.count v ≤ L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, List.length_cons]
    have : ∑ v ∈ Finset.range M, (if (a == v) = true then 1 else 0) ≤ 1 := by
      simp only [beq_iff_eq]
      rw [Finset.sum_ite_eq]
      split_ifs <;> omega
    omega

lemma sum_sub (M : ℕ) (L : List ℕ) (h : ∀ v < M, v ∈ L) :
    ∑ v ∈ Finset.range M, (L.count v - 1) + M = ∑ v ∈ Finset.range M, L.count v := by
  have e : ∑ v ∈ Finset.range M, (L.count v - 1 + 1) = ∑ v ∈ Finset.range M, L.count v := by
    apply Finset.sum_congr rfl
    intro v hv
    have := List.count_pos_iff.mpr (h v (Finset.mem_range.mp hv))
    omega
  rw [Finset.sum_add_distrib] at e
  simpa using e

lemma len_bound (N : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, GoodGate N g) :
    (List.flatMap Gate.inputs gs).length +
      (List.filter (fun (x5 : Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) gs).length
      ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have ih' := ih (fun g' hg' => h g' (by simp [hg']))
    obtain ⟨⟨hop, h2⟩, hnot, _⟩ := hg
    simp only [List.flatMap_cons, List.length_append, List.filter_cons]
    split_ifs with hp
    · have hn : g.op = GateOp.not := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop | hop <;> rw [hop] at hp ⊢ <;> first | rfl | simp [GateOp.eval] at hp
      have := hnot hn
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

lemma delC_fan (C : Circuit) (j : ℕ) (h : FanInTwo C) : FanInTwo (delC C j) := by
  unfold FanInTwo at h ⊢
  intro g hg
  simp only [delC, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact h g (List.mem_of_mem_take hg)
  · have := h g0 (List.mem_of_mem_drop hg0)
    simpa [shGate] using this

lemma delC_size (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (delC C j).size + 1 = C.size := by
  simp [delC, Circuit.size]
  omega

lemma main : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  classical
  intro C hC hdep
  have hex : ∃ m, ∃ D : Circuit, FanInTwo D ∧ circuitFun 10 D = circuitFun 10 C ∧ D.size = m :=
    ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨D, hDf, hDc, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, FanInTwo D' → circuitFun 10 D' = circuitFun 10 C →
      Nat.find hex ≤ D'.size :=
    fun D' h1 h2 => Nat.find_min' hex ⟨D', h1, h2, rfl⟩
  have hEs : (normC D).size = D.size := normGates_length _ _ _
  have hEg : (normC D).size = (normC D).gates.length := rfl
  have hgood : ∀ g ∈ (normC D).gates, GoodGate (10 + (normC D).size) g := by
    have := normGates_good (10 + D.gates.length) D.gates 10 hDf (le_refl _)
    rw [hEs]
    exact this
  have hEc : circuitFun 10 (normC D) = circuitFun 10 C := by rw [normC_fun, hDc]
  have hEf : FanInTwo (normC D) := fun g hg => (hgood g hg).1
  have hcov : ∀ v < 10 + (normC D).size,
      v ∈ (normC D).output :: List.flatMap Gate.inputs (normC D).gates := by
    intro v hv
    by_contra hn
    have hno : v ≠ (normC D).output := fun h => hn (by simp [h])
    have hng : ∀ g ∈ (normC D).gates, v ∉ g.inputs := fun g hg hi =>
      hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g, hg, hi⟩))
    rcases lt_or_ge v 10 with h10 | h10
    · obtain ⟨x4, x5, hagree, hne⟩ := hdep ⟨v, h10⟩
      apply hne
      rw [← hEc]
      unfold circuitFun Circuit.eval
      rw [wires_eq, wires_eq]
      refine foldl_indep v _ _ _ (by simp) ?_ hng _ (Ne.symm hno)
      intro i hi
      rw [getD_ofFn, getD_ofFn]
      split_ifs with h
      · exact hagree _ (fun e => hi (congrArg Fin.val e))
      · rfl
    · obtain ⟨j, rfl⟩ : ∃ j, v = 10 + j := ⟨v - 10, by omega⟩
      have hj : j < (normC D).gates.length := by omega
      have h1 := hmin (delC (normC D) j) (delC_fan _ j hEf)
        (by rw [delC_fun _ j hj hno hng, hEc])
      have h2 := delC_size (normC D) j hj
      omega
  refine ⟨normC D, hEf, hEc, ?_, ⟨?_, ?_⟩, hcov, ?_⟩
  · rw [hEs, hDs]
    exact Nat.find_min' hex ⟨C, hC, rfl, rfl⟩
  · rw [hEs]
    show (if D.output < 10 + D.gates.length then D.output else 10 + D.gates.length) ≤ 10 + D.size
    have : D.size = D.gates.length := rfl
    split_ifs <;> omega
  · exact fun g hg i hi => (hgood g hg).2.2 i hi
  · have hlen := len_bound _ _ hgood
    have hs := sum_sub (10 + (normC D).size) _ hcov
    have hc := sum_count_le (10 + (normC D).size)
      ((normC D).output :: List.flatMap Gate.inputs (normC D).gates)
    simp only [List.length_cons] at hc
    omega

end PEqualNP.Outside.L_meta_3087

theorem PEqualNP.Outside.L_meta_3087 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ)), ∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), (∀ (x6 : Fin (10 : ℕ)), x6 ≠ x3 → x4 x6 = x5 x6) ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x4 ≠ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 x5) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 ∧ x4.size ≤ x1.size ∧ (x4.output ≤ (10 : ℕ) + x4.size ∧ ∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x4.size) ∧ (∀ x5 < (10 : ℕ) + x4.size, x5 ∈ x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∧ (9 : ℕ) + (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op.eval [Bool.false] && !x5.op.eval [Bool.true]) x4.gates).length + ∑ x5 ∈ Finset.range ((10 : ℕ) + x4.size), (List.count x5 (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) - (1 : ℕ)) ≤ x4.size := by
  exact PEqualNP.Outside.L_meta_3087.main
