import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4047

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace Del

-- Gate deletion and evaluation agreement adapted from the upstream L-meta-522 proof.
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

end Del


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


-- Reading wire i inside gate k: the value of i if it exists by then, else false.
def rdv (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k i : ℕ) : Bool :=
  decide (i < n + k) && val gates i x

theorem rd_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = rdv gates x k i := by
  apply Bool.eq_iff_iff.2
  rw [iv_eq gates x k hk i]
  simp [rdv]

theorem gval (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length) :
    val gates (n + k) x = gates[k].op.eval (gates[k].inputs.map (rdv gates x k)) := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  congr 1
  apply List.map_congr_left
  intro i _
  exact rd_eq gates x k (Nat.le_of_lt hk) i

-- Fixing wire w to the constant c inside one gate.
def core (w : ℕ) (op : GateOp) (c : Bool) (ins : List ℕ) : Gate :=
  match op, c with
  | GateOp.and, true => ⟨GateOp.and, ins.filter (fun i => i != w)⟩
  | GateOp.and, false => ⟨GateOp.or, []⟩
  | GateOp.or, true => ⟨GateOp.and, []⟩
  | GateOp.or, false => ⟨GateOp.or, ins.filter (fun i => i != w)⟩
  | GateOp.not, true =>
    if ins.head? = some w then ⟨GateOp.or, []⟩ else ⟨GateOp.not, ins.filter (fun i => i != w)⟩
  | GateOp.not, false =>
    if ins.head? = some w then ⟨GateOp.and, []⟩ else ⟨GateOp.not, ins.filter (fun i => i != w)⟩
  | _, _ => ⟨GateOp.or, []⟩

def absorb (w : ℕ) (c : Bool) (g : Gate) : Gate :=
  if w ∈ g.inputs then core w g.op c g.inputs else g

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
  g.inputs.length ≤ 2

theorem ok_of_fan (C : Circuit) (h : FanInTwo C) : ∀ g ∈ C.gates, Ok g := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1

theorem fan_of_ok (C : Circuit) (h : ∀ g ∈ C.gates, Ok g) : FanInTwo C := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1

theorem filter_len (l : List ℕ) (w : ℕ) : (l.filter (fun i => i != w)).length ≤ l.length :=
  List.length_filter_le _ _

theorem mem_filt (l : List ℕ) (w i : ℕ) (h : i ∈ l.filter (fun j => j != w)) : i ≠ w ∧ i ∈ l := by
  rw [List.mem_filter] at h
  exact ⟨by simpa using h.2, h.1⟩

theorem absorb_ok (w : ℕ) (c : Bool) (g : Gate) (h : Ok g) : Ok (absorb w c g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h2⟩ := h
  have hf := filter_len ins w
  by_cases hw : w ∈ ins
  · rw [absorb, if_pos hw]
    rcases h1 with h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;> cases c
    · exact ⟨Or.inr (Or.inl rfl), by show ([] : List ℕ).length ≤ 2; simp⟩
    · exact ⟨Or.inl rfl, by show (ins.filter (fun i => i != w)).length ≤ 2; simp only at h2; omega⟩
    · exact ⟨Or.inr (Or.inl rfl), by show (ins.filter (fun i => i != w)).length ≤ 2; simp only at h2; omega⟩
    · exact ⟨Or.inl rfl, by show ([] : List ℕ).length ≤ 2; simp⟩
    · by_cases hh : ins.head? = some w
      · show Ok (if ins.head? = some w then _ else _); rw [if_pos hh]
        exact ⟨Or.inl rfl, by simp⟩
      · show Ok (if ins.head? = some w then _ else _); rw [if_neg hh]
        exact ⟨Or.inr (Or.inr rfl), by simp only at h2 ⊢; omega⟩
    · by_cases hh : ins.head? = some w
      · show Ok (if ins.head? = some w then _ else _); rw [if_pos hh]
        exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · show Ok (if ins.head? = some w then _ else _); rw [if_neg hh]
        exact ⟨Or.inr (Or.inr rfl), by simp only at h2 ⊢; omega⟩
  · rw [absorb, if_neg hw]
    exact ⟨h1, h2⟩

theorem absorb_inputs (w : ℕ) (c : Bool) (g : Gate) :
    ∀ i ∈ (absorb w c g).inputs, i ≠ w ∧ i ∈ g.inputs := by
  obtain ⟨op, ins⟩ := g
  intro i hi
  by_cases hw : w ∈ ins
  · rw [absorb, if_pos hw] at hi
    simp only at hi ⊢
    cases op <;> cases c
    all_goals first
      | exact absurd hi (List.not_mem_nil)
      | exact mem_filt ins w i hi
      | (by_cases hh : ins.head? = some w
         · have hi' : i ∈ (if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
              ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs := hi
           rw [if_pos hh] at hi'
           exact absurd hi' (List.not_mem_nil)
         · have hi' : i ∈ (if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
              ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs := hi
           rw [if_neg hh] at hi'
           exact mem_filt ins w i hi')
      | (by_cases hh : ins.head? = some w
         · have hi' : i ∈ (if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
              ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs := hi
           rw [if_pos hh] at hi'
           exact absurd hi' (List.not_mem_nil)
         · have hi' : i ∈ (if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
              ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs := hi
           rw [if_neg hh] at hi'
           exact mem_filt ins w i hi')
  · rw [absorb, if_neg hw] at hi
    exact ⟨fun e => hw (e ▸ hi), hi⟩

theorem all_filter (l : List ℕ) (w : ℕ) (r : ℕ → Bool) (hr : r w = true) :
    ((l.filter (fun i => i != w)).map r).all id = (l.map r).all id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = w
    · subst ha; simp [hr, ih]
    · simp [List.filter_cons, ha, ih]

theorem any_filter (l : List ℕ) (w : ℕ) (r : ℕ → Bool) (hr : r w = false) :
    ((l.filter (fun i => i != w)).map r).any id = (l.map r).any id := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a = w
    · subst ha; simp [hr, ih]
    · simp [List.filter_cons, ha, ih]

theorem all_false (l : List ℕ) (w : ℕ) (r : ℕ → Bool) (hw : w ∈ l) (hr : r w = false) :
    (l.map r).all id = false := by
  cases h : (l.map r).all id
  · rfl
  · rw [List.all_eq_true] at h
    have := h (r w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp [hr] at this

theorem any_true (l : List ℕ) (w : ℕ) (r : ℕ → Bool) (hw : w ∈ l) (hr : r w = true) :
    (l.map r).any id = true := by
  rw [List.any_eq_true]
  exact ⟨r w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hr]⟩

theorem not_head (ins : List ℕ) (w : ℕ) (r : ℕ → Bool) (hh : ¬ ins.head? = some w) :
    ((ins.filter (fun i => i != w)).map r).headD false = (ins.map r).headD false := by
  cases ins with
  | nil => rfl
  | cons a t =>
    have ha : a ≠ w := fun e => hh (by simp [e])
    simp [List.filter_cons, ha]

theorem absorb_eval (w : ℕ) (c : Bool) (g : Gate) (hg : Ok g) (r : ℕ → Bool) (hr : r w = c) :
    (absorb w c g).op.eval ((absorb w c g).inputs.map r) = g.op.eval (g.inputs.map r) := by
  obtain ⟨op, ins⟩ := g
  by_cases hw : w ∈ ins
  · rw [absorb, if_pos hw]
    simp only
    rcases hg.1 with h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;> cases c
    · show GateOp.or.eval (([] : List ℕ).map r) = GateOp.and.eval (ins.map r)
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      exact (all_false ins w r hw hr).symm
    · show GateOp.and.eval ((ins.filter (fun i => i != w)).map r) = GateOp.and.eval (ins.map r)
      simp only [GateOp.eval]
      exact all_filter ins w r hr
    · show GateOp.or.eval ((ins.filter (fun i => i != w)).map r) = GateOp.or.eval (ins.map r)
      simp only [GateOp.eval]
      exact any_filter ins w r hr
    · show GateOp.and.eval (([] : List ℕ).map r) = GateOp.or.eval (ins.map r)
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      exact (any_true ins w r hw hr).symm
    · by_cases hh : ins.head? = some w
      · show (if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).op.eval
            ((if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs.map r) = GateOp.not.eval (ins.map r)
        rw [if_pos hh]
        obtain ⟨t, rfl⟩ : ∃ t, ins = w :: t := by
          cases ins with
          | nil => simp at hh
          | cons a t => simp at hh; exact ⟨t, by rw [hh]⟩
        simp [GateOp.eval, hr]
      · show (if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).op.eval
            ((if ins.head? = some w then (⟨GateOp.and, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs.map r) = GateOp.not.eval (ins.map r)
        rw [if_neg hh]
        simp only [GateOp.eval]
        rw [not_head ins w r hh]
    · by_cases hh : ins.head? = some w
      · show (if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).op.eval
            ((if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs.map r) = GateOp.not.eval (ins.map r)
        rw [if_pos hh]
        obtain ⟨t, rfl⟩ : ∃ t, ins = w :: t := by
          cases ins with
          | nil => simp at hh
          | cons a t => simp at hh; exact ⟨t, by rw [hh]⟩
        simp [GateOp.eval, hr]
      · show (if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).op.eval
            ((if ins.head? = some w then (⟨GateOp.or, []⟩ : Gate) else
            ⟨GateOp.not, ins.filter (fun i => i != w)⟩).inputs.map r) = GateOp.not.eval (ins.map r)
        rw [if_neg hh]
        simp only [GateOp.eval]
        rw [not_head ins w r hh]
  · rw [absorb, if_neg hw]

-- Absorbing a constant from gate k0 on.
def absorbFrom (gs : List Gate) (w : ℕ) (c : Bool) (k0 : ℕ) : List Gate :=
  gs.mapIdx (fun k g => if k0 ≤ k then absorb w c g else g)

theorem absorbFrom_len (gs : List Gate) (w : ℕ) (c : Bool) (k0 : ℕ) :
    (absorbFrom gs w c k0).length = gs.length := by
  simp [absorbFrom]

theorem absorbFrom_get (gs : List Gate) (w : ℕ) (c : Bool) (k0 k : ℕ)
    (hk : k < (absorbFrom gs w c k0).length) :
    (absorbFrom gs w c k0)[k] = if k0 ≤ k then absorb w c (gs[k]'(by rw [absorbFrom_len] at hk; exact hk))
      else gs[k]'(by rw [absorbFrom_len] at hk; exact hk) := by
  simp [absorbFrom]

theorem absorbFrom_ok (gs : List Gate) (w : ℕ) (c : Bool) (k0 : ℕ) (h : ∀ g ∈ gs, Ok g) :
    ∀ g ∈ absorbFrom gs w c k0, Ok g := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  rw [absorbFrom_get]
  have hk' : k < gs.length := by rw [absorbFrom_len] at hk; exact hk
  split_ifs
  · exact absorb_ok w c _ (h _ (List.getElem_mem hk'))
  · exact h _ (List.getElem_mem hk')

theorem absorb_val (gs : List Gate) (n w : ℕ) (c : Bool) (k0 : ℕ) (hok : ∀ g ∈ gs, Ok g)
    (hlt : w < n + k0) (hbefore : ∀ k < k0, n + k ≤ w)
    (x x' : Fin n → Bool) (hxx : ∀ i : Fin n, i.val ≠ w → x i = x' i)
    (hw : val gs w x' = c) :
    ∀ i, i ≠ w → val (absorbFrom gs w c k0) i x = val gs i x' := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hiw
    by_cases hin : i < n
    · rw [val_input _ _ i hin, val_input _ _ i hin]
      exact hxx ⟨i, hin⟩ hiw
    by_cases hbig : n + gs.length ≤ i
    · rw [val_big _ _ i hbig, val_big _ _ i (by rw [absorbFrom_len]; exact hbig)]
    have hk : i - n < gs.length := by omega
    have hk' : i - n < (absorbFrom gs w c k0).length := by rw [absorbFrom_len]; exact hk
    have he : n + (i - n) = i := by omega
    rw [← he, gval _ x _ hk', gval _ x' _ hk]
    -- reads agree off w
    have hagree : ∀ j, j ≠ w → rdv (absorbFrom gs w c k0) x (i - n) j = rdv gs x' (i - n) j := by
      intro j hj
      simp only [rdv]
      by_cases hjl : j < n + (i - n)
      · rw [ih j (by omega) hj]
      · simp [hjl]
    rw [absorbFrom_get]
    split_ifs with hk0
    · rw [List.map_congr_left (fun j hj => hagree j (absorb_inputs w c _ j hj).1)]
      apply absorb_eval w c _ (hok _ (List.getElem_mem hk))
      simp only [rdv]
      rw [hw]
      have : w < n + (i - n) := by omega
      simp [this]
    · congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j = w
      · subst hj
        have := hbefore (i - n) (by omega)
        simp only [rdv]
        have h2 : ¬ j < n + (i - n) := by omega
        simp [h2]
      · exact hagree j hj

-- Redirecting reads of wire w to wire d from gate k0 on.
def redirect (w d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => if i = w then d else i)⟩

def redirectFrom (gs : List Gate) (w d k0 : ℕ) : List Gate :=
  gs.mapIdx (fun k g => if k0 ≤ k then redirect w d g else g)

theorem redirectFrom_len (gs : List Gate) (w d k0 : ℕ) :
    (redirectFrom gs w d k0).length = gs.length := by
  simp [redirectFrom]

theorem redirectFrom_get (gs : List Gate) (w d k0 k : ℕ)
    (hk : k < (redirectFrom gs w d k0).length) :
    (redirectFrom gs w d k0)[k] = if k0 ≤ k then redirect w d (gs[k]'(by rw [redirectFrom_len] at hk; exact hk))
      else gs[k]'(by rw [redirectFrom_len] at hk; exact hk) := by
  simp [redirectFrom]

theorem redirectFrom_ok (gs : List Gate) (w d k0 : ℕ) (h : ∀ g ∈ gs, Ok g) :
    ∀ g ∈ redirectFrom gs w d k0, Ok g := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  rw [redirectFrom_get]
  have hk' : k < gs.length := by rw [redirectFrom_len] at hk; exact hk
  split_ifs
  · obtain ⟨h1, h2⟩ := h _ (List.getElem_mem hk')
    exact ⟨h1, by simp [redirect]; exact h2⟩
  · exact h _ (List.getElem_mem hk')

theorem redirect_val (gs : List Gate) (n w d k0 : ℕ) (hd : d < w) (hlt : w < n + k0)
    (x : Fin n → Bool) (hw : val gs w x = val gs d x) :
    ∀ i, val (redirectFrom gs w d k0) i x = val gs i x := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hin : i < n
    · rw [val_input _ _ i hin, val_input _ _ i hin]
    by_cases hbig : n + gs.length ≤ i
    · rw [val_big _ _ i hbig, val_big _ _ i (by rw [redirectFrom_len]; exact hbig)]
    have hk : i - n < gs.length := by omega
    have hk' : i - n < (redirectFrom gs w d k0).length := by rw [redirectFrom_len]; exact hk
    have he : n + (i - n) = i := by omega
    rw [← he, gval _ x _ hk', gval _ x _ hk]
    have hagree : ∀ j, rdv (redirectFrom gs w d k0) x (i - n) j = rdv gs x (i - n) j := by
      intro j
      simp only [rdv]
      by_cases hjl : j < n + (i - n)
      · rw [ih j (by omega)]
      · simp [hjl]
    rw [redirectFrom_get]
    split_ifs with hk0
    · simp only [redirect, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      by_cases hj : j = w
      · subst hj
        simp only [if_true]
        rw [hagree d]
        simp only [rdv]
        have h1 : d < n + (i - n) := by omega
        have h2 : j < n + (i - n) := by omega
        simp [h1, h2, hw]
      · simp only [hj, if_false]
        exact hagree j
    · congr 1
      apply List.map_congr_left
      intro j _
      exact hagree j

-- A gate that reads v where it matters.
def Rel (v : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ v ∈ g.inputs) ∨
    (g.op = GateOp.not ∧ g.inputs.head? = some v)

theorem absorb_indep (v : ℕ) (g : Gate) (h : ¬ Rel v g) : absorb v true g = absorb v false g := by
  obtain ⟨op, ins⟩ := g
  by_cases hv : v ∈ ins
  · rw [absorb, absorb, if_pos hv, if_pos hv]
    simp only
    cases op with
    | and => exact absurd (Or.inl ⟨Or.inl rfl, hv⟩) h
    | or => exact absurd (Or.inl ⟨Or.inr rfl, hv⟩) h
    | not =>
      have hh : ¬ ins.head? = some v := fun e => h (Or.inr ⟨rfl, e⟩)
      show (if ins.head? = some v then (⟨GateOp.or, []⟩ : Gate) else
          ⟨GateOp.not, ins.filter (fun i => i != v)⟩) =
        (if ins.head? = some v then (⟨GateOp.and, []⟩ : Gate) else
          ⟨GateOp.not, ins.filter (fun i => i != v)⟩)
      rw [if_neg hh, if_neg hh]
    | mod m => rfl
    | maj => rfl
  · rw [absorb, absorb, if_neg hv, if_neg hv]

theorem filter_one (l : List ℕ) (v : ℕ) (hv : v ∈ l) (hl : l.length ≤ 2) :
    (l.filter (fun i => i != v)).length ≤ 1 := by
  have : (l.filter (fun i => i != v)).length < l.length :=
    List.length_filter_lt_length_iff_exists.2 ⟨v, hv, by simp⟩
  omega

-- After absorbing, a gate that read v where it matters is AND or OR of at most one wire.
theorem absorb_rel (v : ℕ) (c : Bool) (g : Gate) (hg : Ok g) (h : Rel v g) :
    ((absorb v c g).op = GateOp.and ∨ (absorb v c g).op = GateOp.or) ∧
      (absorb v c g).inputs.length ≤ 1 := by
  obtain ⟨op, ins⟩ := g
  have hf := filter_one ins v
  have h2 : ins.length ≤ 2 := hg.2
  rcases h with ⟨hop, hv⟩ | ⟨hop, hh⟩
  · rw [absorb, if_pos hv]
    simp only at hop ⊢
    rcases hop with rfl | rfl <;> cases c
    · exact ⟨Or.inr rfl, by show ([] : List ℕ).length ≤ 1; simp⟩
    · exact ⟨Or.inl rfl, hf hv h2⟩
    · exact ⟨Or.inr rfl, hf hv h2⟩
    · exact ⟨Or.inl rfl, by show ([] : List ℕ).length ≤ 1; simp⟩
  · simp only at hop hh
    subst hop
    have hv : v ∈ ins := by
      cases ins with
      | nil => simp at hh
      | cons a t => simp at hh; simp [hh]
    rw [absorb, if_pos hv]
    cases c <;> simp [core, hh]

theorem small_list (l : List ℕ) (hl : l.length ≤ 1) : l = [] ∨ ∃ d, l = [d] := by
  match l, hl with
  | [], _ => exact Or.inl rfl
  | [d], _ => exact Or.inr ⟨d, rfl⟩
  | a :: b :: t, hl => simp at hl

theorem main (m : ℕ) (f : (Fin m → Bool) → Bool) (v : Fin m) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x v (!x v)) ≠ f x)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x v b) ≠ f (Function.update y v b))
    (hC : HasCircuitSize m f (s + 1)) :
    HasCircuitSize m (fun x => f (Function.update x v b)) s := by
  classical
  obtain ⟨C, hF, hs, hCf⟩ := hC
  have hok := ok_of_fan C hF
  have hfC : ∀ x, val C.gates C.output x = f x := hCf
  set F : (Fin m → Bool) → Bool := fun x => f (Function.update x v b) with hFdef
  obtain ⟨x7, x8, h78⟩ := hnc
  -- the output is not the input v
  have hout_v : C.output ≠ v.val := by
    intro e
    apply h78
    rw [← hfC, ← hfC, e, val_input _ _ _ v.isLt, val_input _ _ _ v.isLt]
    simp
  -- step 1: fix v to b everywhere
  let gb := absorbFrom C.gates v.val b 0
  have hgb_ok := absorbFrom_ok C.gates v.val b 0 hok
  have hgb_len : gb.length = C.gates.length := absorbFrom_len _ _ _ _
  have hgb : ∀ x, ∀ i, i ≠ v.val → val gb i x = val C.gates i (Function.update x v b) := by
    intro x
    apply absorb_val C.gates m v.val b 0 hok (by simp) (fun k hk => absurd hk (by omega))
    · intro i hi
      rw [Function.update_of_ne (fun e => hi (congrArg Fin.val e))]
    · rw [val_input _ _ _ v.isLt]
      simp
  have hFb : ∀ x, val gb C.output x = F x := by
    intro x
    rw [hgb x _ hout_v, hfC]
  by_cases hsmall : C.gates.length ≤ s
  · exact ⟨⟨gb, C.output⟩, fan_of_ok _ hgb_ok, by show gb.length ≤ s; omega, hFb⟩
  have hlen : C.gates.length = s + 1 := by
    have : C.size ≤ s + 1 := hs
    show C.gates.length = s + 1
    simp only [Circuit.size] at this
    omega
  -- step 2: some gate reads v where it matters
  obtain ⟨k0, hk0, hrel⟩ : ∃ k0, ∃ hk0 : k0 < C.gates.length, Rel v.val C.gates[k0] := by
    by_contra hno
    push Not at hno
    have heq : absorbFrom C.gates v.val true 0 = absorbFrom C.gates v.val false 0 := by
      apply List.ext_getElem (by simp [absorbFrom_len])
      intro k h1 h2
      rw [absorbFrom_get, absorbFrom_get]
      simp only [Nat.zero_le, if_true]
      exact absorb_indep v.val _ (hno k (by rw [absorbFrom_len] at h1; exact h1))
    obtain ⟨x6, h6⟩ := hdep
    apply h6
    have hboth : ∀ x, f (Function.update x v true) = f (Function.update x v false) := by
      intro x
      have ht := absorb_val C.gates m v.val true 0 hok (by simp)
        (fun k hk => absurd hk (by omega)) x (Function.update x v true)
        (fun i hi => by rw [Function.update_of_ne (fun e => hi (congrArg Fin.val e))])
        (by rw [val_input _ _ _ v.isLt]; simp) C.output hout_v
      have hf' := absorb_val C.gates m v.val false 0 hok (by simp)
        (fun k hk => absurd hk (by omega)) x (Function.update x v false)
        (fun i hi => by rw [Function.update_of_ne (fun e => hi (congrArg Fin.val e))])
        (by rw [val_input _ _ _ v.isLt]; simp) C.output hout_v
      rw [← hfC, ← hfC, ← ht, ← hf', heq]
    have hself : f x6 = f (Function.update x6 v (x6 v)) := by rw [Function.update_eq_self]
    rw [hself]
    cases hx : x6 v
    · simp only [Bool.not_false]; exact hboth x6
    · simp only [Bool.not_true]; exact (hboth x6).symm
  -- step 3: the gate k0 of gb is a constant or a copy
  have hk0' : k0 < gb.length := by rw [hgb_len]; exact hk0
  have hg0 : gb[k0] = absorb v.val b C.gates[k0] := by
    rw [absorbFrom_get]; simp
  obtain ⟨hop0, hlen0⟩ := absorb_rel v.val b _ (hok _ (List.getElem_mem hk0)) hrel
  set w0 := m + k0 with hw0
  have hval0 : ∀ x, val gb w0 x = gb[k0].op.eval (gb[k0].inputs.map (rdv gb x k0)) :=
    fun x => gval gb x k0 hk0'
  -- the final deletion of a gate nobody reads
  have finish : ∀ gs : List Gate, ∀ out : ℕ, (∀ g ∈ gs, Ok g) → gs.length = s + 1 →
      k0 < gs.length → out ≠ w0 →
      (∀ j', (hj' : j' < gs.length) → k0 < j' → w0 ∉ gs[j'].inputs) →
      (∀ x, val gs out x = F x) → HasCircuitSize m F s := by
    intro gs out hgok hgl hk hout hno hval
    have hdel := Del.deleteDeadGate (m := m) ⟨gs, out⟩ hgok k0 hk hout hno
    have hfun : circuitFun m ⟨gs, out⟩ = F := funext hval
    rw [hfun] at hdel
    simpa [hgl] using hdel
  rw [← hg0] at hop0 hlen0
  rcases small_list _ hlen0 with hnil | ⟨d, hd⟩
  · -- a constant gate
    obtain ⟨c, hconst⟩ : ∃ c, ∀ x : Fin m → Bool, val gb w0 x = c := by
      rcases hop0 with h | h
      · exact ⟨true, fun x => by rw [hval0, hnil, h]; rfl⟩
      · exact ⟨false, fun x => by rw [hval0, hnil, h]; rfl⟩
    have hout0 : C.output ≠ w0 := by
      intro e
      apply h78
      have h1 := hFb x7
      have h2 := hFb x8
      rw [e, hconst] at h1 h2
      exact h1.symm.trans h2
    let g2 := absorbFrom gb w0 c (k0 + 1)
    have hg2 : ∀ x : Fin m → Bool, ∀ i, i ≠ w0 → val g2 i x = val gb i x := by
      intro x
      exact absorb_val gb m w0 c (k0 + 1) hgb_ok (by omega) (fun k hk => by omega) x x
        (fun _ _ => rfl) (hconst x)
    apply finish g2 C.output (absorbFrom_ok _ _ _ _ hgb_ok)
      (by rw [absorbFrom_len]; omega) (by rw [absorbFrom_len]; exact hk0') hout0
    · intro j' hj' hlt hmem
      rw [absorbFrom_get] at hmem
      rw [if_pos (by omega)] at hmem
      exact (absorb_inputs w0 c _ w0 hmem).1 rfl
    · intro x
      rw [hg2 x _ hout0, hFb]
  · -- a copy of wire d
    by_cases hdl : d < w0
    · have hcopy : ∀ x : Fin m → Bool, val gb w0 x = val gb d x := by
        intro x
        have hdl' : d < m + k0 := by omega
        rw [hval0, hd]
        rcases hop0 with h | h <;> simp [h, GateOp.eval, rdv, hdl']
      let g3 := redirectFrom gb w0 d (k0 + 1)
      let out3 := if C.output = w0 then d else C.output
      have hg3 : ∀ x : Fin m → Bool, ∀ i, val g3 i x = val gb i x := by
        intro x
        exact redirect_val gb m w0 d (k0 + 1) hdl (by omega) x (hcopy x)
      apply finish g3 out3 (redirectFrom_ok _ _ _ _ hgb_ok)
        (by rw [redirectFrom_len]; omega) (by rw [redirectFrom_len]; exact hk0')
      · simp only [out3]
        split_ifs <;> omega
      · intro j' hj' hlt hmem
        rw [redirectFrom_get] at hmem
        rw [if_pos (by omega)] at hmem
        simp only [redirect, List.mem_map] at hmem
        obtain ⟨i, _, hi⟩ := hmem
        split_ifs at hi <;> omega
      · intro x
        rw [hg3]
        simp only [out3]
        split_ifs with ho
        · rw [← hcopy, ← ho, hFb]
        · rw [hFb]
    · -- reading a wire that does not exist yet: a constant false gate
      have hconst : ∀ x : Fin m → Bool, val gb w0 x = false := by
        intro x
        have hdl' : ¬ d < m + k0 := by omega
        rw [hval0, hd]
        rcases hop0 with h | h <;> simp [h, GateOp.eval, rdv, hdl']
      have hout0 : C.output ≠ w0 := by
        intro e
        apply h78
        have h1 := hFb x7
        have h2 := hFb x8
        rw [e, hconst] at h1 h2
        exact h1.symm.trans h2
      let g2 := absorbFrom gb w0 false (k0 + 1)
      have hg2 : ∀ x : Fin m → Bool, ∀ i, i ≠ w0 → val g2 i x = val gb i x := by
        intro x
        exact absorb_val gb m w0 false (k0 + 1) hgb_ok (by omega) (fun k hk => by omega) x x
          (fun _ _ => rfl) (hconst x)
      apply finish g2 C.output (absorbFrom_ok _ _ _ _ hgb_ok)
        (by rw [absorbFrom_len]; omega) (by rw [absorbFrom_len]; exact hk0') hout0
      · intro j' hj' hlt hmem
        rw [absorbFrom_get] at hmem
        rw [if_pos (by omega)] at hmem
        exact (absorb_inputs w0 false _ w0 hmem).1 rfl
      · intro x
        rw [hg2 x _ hout0, hFb]

end PEqualNP.Outside.L_meta_4047

theorem PEqualNP.Outside.L_meta_4047 : ∀ (x1 : ℕ) (x2 : (Fin (x1 + (1 : ℕ)) → Bool) → Bool) (x3 : Fin (x1 + (1 : ℕ))) (x4 : Bool) (x5 : ℕ), (∃ (x6 : Fin (x1 + (1 : ℕ)) → Bool), x2 (Function.update x6 x3 !x6 x3) ≠ x2 x6) → (∃ (x7 : Fin (x1 + (1 : ℕ)) → Bool) (x8 : Fin (x1 + (1 : ℕ)) → Bool), x2 (Function.update x7 x3 x4) ≠ x2 (Function.update x8 x3 x4)) → PEqualNP.MetaComplexity.HasCircuitSize (x1 + (1 : ℕ)) x2 (x5 + (1 : ℕ)) → PEqualNP.MetaComplexity.HasCircuitSize (x1 + (1 : ℕ)) (fun (x9 : Fin (x1 + (1 : ℕ)) → Bool) => x2 (Function.update x9 x3 x4)) x5 := by
  intro x1 x2 x3 x4 x5 h1 h2 h3
  exact PEqualNP.Outside.L_meta_4047.main (x1 + 1) x2 x3 x4 x5 h1 h2 h3
