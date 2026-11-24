import Mathlib
import PEqualNP.Defs

-- Bypass helpers adapted from willakone, L-meta-1499, PR 3112.
namespace PEqualNP.Outside.L_meta_2642

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
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
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
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
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not)
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
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k, r < k → k < C.gates.length → n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hrk, hk, hm⟩ => absurd hm (hno k hrk hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or ∨ (gateAt (bypass n C r i) k).op = GateOp.not := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
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


lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma bypass_fan {n : ℕ} {C : Circuit} {r i : ℕ} (hC : FanInTwo C) :
    FanInTwo (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hC g' hg'

lemma fan_ops {C : Circuit} (hC : FanInTwo C) :
    ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or ∨ (gateAt C k).op = GateOp.not := by
  intro k hk
  exact (hC _ (gateAt_mem hk)).1

lemma erase_properties (n : ℕ) (C : Circuit) (r i : ℕ)
    (hC : FanInTwo C) (hr : r < C.size) (hi : i < n + r ∨ n + C.size ≤ i) :
    FanInTwo (PEqualNP.CircuitMoves.eraseGate n C r i) ∧
    (PEqualNP.CircuitMoves.eraseGate n C r i).size + 1 = C.size ∧
    ∀ x : List Bool, x.length = n →
      ((val C x (n + r) = val C x i) ∨
        C.output ≠ n + r ∧ ∀ g ∈ C.gates.drop (r + 1), n + r ∉ g.inputs) →
      (PEqualNP.CircuitMoves.eraseGate n C r i).eval x = C.eval x := by
  rw [erase_eq_bypass n C r i hr]
  refine ⟨bypass_fan hC, ?_, ?_⟩
  · change (bypass n C r i).gates.length + 1 = C.gates.length
    rw [bypass_length]
    change r < C.gates.length at hr
    omega
  · intro x hx h
    rcases h with he | ⟨hout, hno⟩
    · exact bypass_eval_eq hx (fan_ops hC) hr hi he
    · apply bypass_eval_unread hx (fan_ops hC) hr hi hout
      intro k hrk hk
      apply hno
      rw [gateAt_eq hk]
      have hkdrop : k - (r + 1) < (C.gates.drop (r + 1)).length := by simp; omega
      have h : (C.gates.drop (r + 1))[k - (r + 1)] = C.gates[k] := by
        rw [List.getElem_drop]
        congr 1
        omega
      rw [← h]
      exact List.getElem_mem (by simp; omega)

def zeroWire (n z : ℕ) (a b : Fin n) (u : ℕ) : ℕ :=
  if u = a.val ∨ u = b.val then n + z else u

def zeroCircuit (n : ℕ) (C : Circuit) (a b : Fin n) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (zeroWire n C.size a b)⟩),
    zeroWire n C.size a b C.output⟩

lemma zero_length (n : ℕ) (C : Circuit) (a b : Fin n) :
    (zeroCircuit n C a b).gates.length = C.gates.length := by simp [zeroCircuit]

lemma zero_fan (n : ℕ) (C : Circuit) (a b : Fin n) (hC : FanInTwo C) :
    FanInTwo (zeroCircuit n C a b) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  have h := hC g' hg'
  exact ⟨h.1, by simpa using h.2⟩

lemma zero_gate (n : ℕ) (C : Circuit) (a b : Fin n) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (zeroCircuit n C a b) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (zeroWire n C.size a b)⟩ := by
  rw [gateAt_eq (by simpa [zero_length] using hk), gateAt_eq hk]
  simp [zeroCircuit]

lemma zero_val (n : ℕ) (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
    ∀ u, val (zeroCircuit n C a b) (List.ofFn x) (zeroWire n C.size a b u) =
      val C (List.ofFn (Function.update (Function.update x a false) b false)) u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun]
      by_cases hz : u = a.val ∨ u = b.val
      · rw [zeroWire, if_pos hz, val_ge (n := n) (by simp) (by simp [Circuit.size, zero_length])]
        rcases hz with rfl | rfl
        · simp [Function.update]
        · simp
      · rw [zeroWire, if_neg hz, val_input (n := n) (by simp) hun]
        have ha : (⟨u, hun⟩ : Fin n) ≠ a := by intro h; exact hz (Or.inl (congrArg Fin.val h))
        have hb : (⟨u, hun⟩ : Fin n) ≠ b := by intro h; exact hz (Or.inr (congrArg Fin.val h))
        simp [hun, Function.update_of_ne, ha, hb]
    · have hfix : zeroWire n C.size a b u = u := by
        simp only [zeroWire]
        rw [if_neg (by have := a.isLt; have := b.isLt; omega)]
      rw [hfix]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) (by simpa [zero_length] using hge), val_ge (n := n) (by simp) hge]
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) (by simpa [zero_length] using hk), val_gate (n := n) (by simp) hk,
          zero_gate n C a b k hk]
        simp only [List.map_map, Function.comp_apply]
        congr 1
        apply List.map_congr_left
        intro j hj
        simp only [Function.comp_apply]
        by_cases hjlt : j < n + k
        · have h := ih j hjlt
          rw [if_pos hjlt]
          by_cases hjz : zeroWire n C.size a b j < n + k
          · rw [if_pos hjz]; exact h
          · rw [if_neg hjz]
            have hlarge : n + C.gates.length ≤ zeroWire n C.size a b j := by
              unfold zeroWire at hjz ⊢
              split_ifs at hjz ⊢ <;> simp_all [Circuit.size] <;> omega
            rw [val_ge (n := n) (by simp) (by simpa [zero_length] using hlarge)] at h
            exact h
        · have hjid : zeroWire n C.size a b j = j := by
            simp only [zeroWire]
            rw [if_neg (by have := a.isLt; have := b.isLt; omega)]
          rw [hjid, if_neg hjlt, if_neg hjlt]

lemma zero_eval (n : ℕ) (C : Circuit) (a b : Fin n) (x : Fin n → Bool) :
    (zeroCircuit n C a b).eval (List.ofFn x) =
      C.eval (List.ofFn (Function.update (Function.update x a false) b false)) :=
  zero_val n C a b x C.output

end PEqualNP.Outside.L_meta_2642

open PEqualNP.Outside.L_meta_2642 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2642 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo (x5 (0 : ℕ)) →     (∀ x7 < x2,         ∃ (x9 : ℕ) (x10 : ℕ),           x9 < (x5 x7).size ∧             (x10 < x1 + x9 ∨ x1 + (x5 x7).size ≤ x10) ∧               x5 (x7 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x5 x7) x9 x10 ∧                 ((∀ (x11 : Fin x1 → Bool),                     have x12 : List Bool := (x5 x7).wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                     x12.getD (x1 + x9) Bool.false = x12.getD x10 Bool.false) ∨                   (x5 x7).output ≠ x1 + x9 ∧ ∀ x11 ∈ List.drop (x9 + (1 : ℕ)) (x5 x7).gates, x1 + x9 ∉ x11.inputs)) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x2 = (x5 (0 : ℕ)).size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = (x5 (0 : ℕ)).eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false)) := by
  intro n s a b F hF hsteps
  have iter : ∀ k ≤ s, FanInTwo (F k) ∧ (F k).size + k = (F 0).size ∧
      ∀ x : Fin n → Bool,
        (F k).eval (List.ofFn (Function.update (Function.update x a false) b false)) =
          (F 0).eval (List.ofFn (Function.update (Function.update x a false) b false)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨hF, by simp, fun _ => rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨hfan, hsize, heval⟩ := ih (by omega)
      obtain ⟨r, i, hr, hi, hf, hsem⟩ := hsteps k (by omega)
      have hp := erase_properties n (F k) r i hfan hr hi
      have hfan' : FanInTwo (F (k + 1)) := by rw [hf]; exact hp.1
      have hsize' : (F (k + 1)).size + 1 = (F k).size := by rw [hf]; exact hp.2.1
      refine ⟨hfan', by omega, ?_⟩
      intro x
      trans (F k).eval (List.ofFn (Function.update (Function.update x a false) b false))
      · rw [hf]
        apply hp.2.2 _ (by simp)
        rcases hsem with h | h
        · exact Or.inl (h x)
        · exact Or.inr h
      · exact heval x
  obtain ⟨hfan, hsize, heval⟩ := iter s le_rfl
  refine ⟨zeroCircuit n (F s) a b, zero_fan n (F s) a b hfan, ?_, ?_⟩
  · simpa only [Circuit.size, zero_length] using hsize
  · intro x
    exact (zero_eval n (F s) a b x).trans (heval x)
