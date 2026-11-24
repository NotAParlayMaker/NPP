import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3297

-- The cone and OR closure characterisations below are taken from the accepted file L_meta_1491.
open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩


-- The wire list of a gate list started on the list w.
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_app (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length
  | [], w => by simp [run]
  | g :: gs, w => by rw [run_cons, run_len gs]; simp; omega

theorem run_pre : ∀ (gs : List Gate) (w : List Bool) (r : ℕ), r < w.length →
    (run gs w).getD r false = w.getD r false
  | [], _, _, _ => rfl
  | g :: gs, w, r, hr => by
    rw [run_cons, run_pre gs _ r (by simp; omega), List.getD_append _ _ _ _ hr]

theorem run_high (gs : List Gate) (w : List Bool) (r : ℕ) (hr : w.length + gs.length ≤ r) :
    (run gs w).getD r false = false :=
  List.getD_eq_default _ _ (by rw [run_len]; omega)

theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs w).getD (w.length + j) false = gs[j].op.eval (gs[j].inputs.map fun r =>
      if r < w.length + j then (run gs w).getD r false else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hul : (run (gs.take j) w).length = w.length + j := by
    rw [run_len, List.length_take]; omega
  have hall : run gs w = run (gs.drop (j + 1)) (run (gs.take j) w ++
      [gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) w).getD i false)]) := by
    conv_lhs => rw [hsplit]
    rw [run_app, run_cons]
  have key : ∀ r, (if r < w.length + j then (run gs w).getD r false else false) =
      (run (gs.take j) w).getD r false := by
    intro r
    split_ifs with h
    · rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    · exact (List.getD_eq_default _ _ (by omega)).symm
  simp only [key]
  rw [hall, run_pre _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
  simp only [hul, Nat.sub_self, List.getD_cons_zero]


open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

def V (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool := (run C.gates (List.ofFn x)).getD w false

theorem V_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    V C n x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then V C n x i else false) := by
  have h := run_gate C.gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  have hg : gateAt C k = C.gates[k] := by simp [gateAt, List.getElem?_eq_getElem hk]
  rw [hg]; exact h

theorem V_low (C : Circuit) (D : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    V C n x w = V D n x w := by
  simp only [V]; rw [run_pre _ _ _ (by simpa using hw), run_pre _ _ _ (by simpa using hw)]

theorem V_high (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    V C n x w = false := by
  simp only [V]; exact run_high _ _ _ (by simpa using hw)

-- The substituted circuit gate by gate.
theorem sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by simp [substReads]

theorem sub_gate (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (substReads C n c sigma) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
  simp [gateAt, substReads, List.getElem?_eq_getElem hk]


-- Gates of the OR closure lie above c, and each reaches a reader of c through OR gates.
theorem clos_above (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (c : ℕ) :
    ∀ k, OrReaches n C (n + k) c → c ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    rcases (orReaches_iff n C k c).mp h with ⟨hk, rfl | ⟨_, i, hi, hlt, hr⟩⟩
    · exact le_rfl
    · have hni : n ≤ i := hr.1
      have := ih (i - n) (by omega) (by rwa [show n + (i - n) = i by omega])
      omega

theorem clos_reader (n : ℕ) (C : Circuit) (c : ℕ) :
    ∀ k, k ≠ c → OrReaches n C (n + k) c → ∃ r ∈ readers n C c, OrReaches n C (n + k) r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hne h
    obtain ⟨hk, hc | ⟨hop, i, hi, hlt, hr⟩⟩ := (orReaches_iff n C k c).mp h
    · exact absurd hc.symm hne
    · have hni : n ≤ i := hr.1
      by_cases hic : i = n + c
      · refine ⟨k, ?_, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩⟩
        simp only [readers, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk, hic ▸ hi⟩
      · have hr' : OrReaches n C (n + (i - n)) c := by rwa [show n + (i - n) = i by omega]
        obtain ⟨r, hrm, hrr⟩ := ih (i - n) (by omega) (by omega) hr'
        refine ⟨r, hrm, (orReaches_iff n C k r).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, ?_⟩⟩⟩
        rwa [show n + (i - n) = i by omega] at hrr

-- Through OR gates a wire is at least the gate it reaches.
theorem or_below (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ) :
    ∀ k, OrReaches n C (n + k) g → V C n x (n + g) = true → V C n x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h hv
    obtain ⟨hk, rfl | ⟨hop, i, hi, hlt, hr⟩⟩ := (orReaches_iff n C k g).mp h
    · exact hv
    · have hni : n ≤ i := hr.1
      have hvi : V C n x i = true := by
        have := ih (i - n) (by omega) (by rwa [show n + (i - n) = i by omega]) hv
        rwa [show n + (i - n) = i by omega] at this
      rw [V_gate C n x k hk, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨_, ⟨i, hi, rfl⟩, by rw [if_pos hlt]; exact hvi⟩


theorem bool_key (vu vu' vy va vb vs : Bool) (h1 : vu = true → vu' = true)
    (h2 : vu' = true → vu = true ∨ vs = true) (hsa : vs = true → vy = true → va = true ∧ vb = true)
    (hcu : va = true → vb = true → vu = true) : (vu' && vy) = (vu && vy) := by
  cases vu <;> cases vu' <;> cases vy <;> cases va <;> cases vb <;> cases vs <;> simp_all

-- The values of the substituted circuit, wire by wire.
theorem sem (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hAO : IsAO2 n C)
    (hc : c < C.gates.length) (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (hfr : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ readers n C c,
        (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true))
    (hcons : ∀ g2 ∈ frontier n C c, ∀ u2 ∈ (gateAt C g2).inputs, ∀ r1 ∈ readers n C c,
      ∀ r2 ∈ readers n C c, OrReaches n C u2 r1 → OrReaches n C u2 r2 → sigma r1 = sigma r2)
    (x : Fin n → Bool) :
    ∀ w, ((∀ k ∈ insert c (orClosure n C c), w ≠ n + k) →
        V (substReads C n c sigma) n x w = V C n x w) ∧
      (∀ k ∈ insert c (orClosure n C c), w = n + k → ∀ s, (s = a ∨ s = b) →
        (∀ r ∈ readers n C c, OrReaches n C w r → sigma r = s) →
        (V C n x w = true → V (substReads C n c sigma) n x w = true) ∧
        (V (substReads C n c sigma) n x w = true → V C n x w = true ∨ V C n x s = true)) := by
  obtain ⟨hAnd, hRB, h2⟩ := hAO
  have hlen := sub_len C n c sigma
  have ha : a < n + c := hRB c hc a (by rw [hcin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hcin]; simp)
  have memO : ∀ k, k ∈ insert c (orClosure n C c) ↔
      k = c ∨ (k < C.gates.length ∧ k ≠ c ∧ OrReaches n C (n + k) c) := by
    intro k; simp [orClosure]
  have oclAbove : ∀ k ∈ insert c (orClosure n C c), c ≤ k := by
    intro k hk
    rcases (memO k).mp hk with rfl | ⟨_, _, h⟩
    · exact le_rfl
    · exact clos_above n C hRB c k h
  have notOcl : ∀ w, w < n + c → ∀ k ∈ insert c (orClosure n C c), w ≠ n + k := by
    intro w hw k hk e; have := oclAbove k hk; omega
  have reachSelf : ∀ k, k < C.gates.length → OrReaches n C (n + k) k :=
    fun k hk => (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩
  have valC : V C n x (n + c) = (V C n x a && V C n x b) := by
    rw [V_gate C n x c hc, hcop, hcin]
    simp [GateOp.eval, ha, hb]
  have twoIn : ∀ k, k < C.gates.length → ∃ p q, (gateAt C k).inputs = [p, q] := by
    intro k hk
    have hl := h2 _ (List.getElem_mem hk)
    have hg : gateAt C k = C.gates[k] := by simp [gateAt, List.getElem?_eq_getElem hk]
    rw [hg]
    match hm : C.gates[k].inputs, hl with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have opAO : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
    intro k hk
    have hg : gateAt C k = C.gates[k] := by simp [gateAt, List.getElem?_eq_getElem hk]
    rw [hg]; exact hAnd _ (List.getElem_mem hk)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hwn : w < n
  · refine ⟨fun _ => V_low _ _ n x w hwn, fun k _ hk => by omega⟩
  by_cases hwh : n + C.gates.length ≤ w
  · refine ⟨fun _ => by rw [V_high _ n x w (by rw [hlen]; exact hwh), V_high _ n x w hwh], ?_⟩
    intro k hk hwk
    rcases (memO k).mp hk with rfl | ⟨hkl, _, _⟩ <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  obtain ⟨p, q, hpq⟩ := twoIn k hk
  have hp : p < n + k := hRB k hk p (by rw [hpq]; simp)
  have hq : q < n + k := hRB k hk q (by rw [hpq]; simp)
  -- a read of n + c by gate k is a read of c by a reader
  have rdr : (p = n + c ∨ q = n + c) → k ∈ readers n C c := by
    intro h
    simp only [readers, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk, ?_⟩
    rw [hpq]; rcases h with rfl | rfl <;> simp
  -- the substituted read and its value
  have star : ∀ i, i < n + k → (i = p ∨ i = q) → ∃ i', i' = (if i = n + c then sigma k else i) ∧ i' < n + k := by
    intro i hi hiq
    refine ⟨_, rfl, ?_⟩
    split_ifs with h
    · have hr := rdr (by rcases hiq with rfl | rfl <;> simp_all)
      rcases hsig k hr with e | e <;> rw [e] <;> omega
    · exact hi
  have gC := V_gate C n x k hk
  have gC' := V_gate (substReads C n c sigma) n x k (by rw [hlen]; exact hk)
  rw [sub_gate C n c sigma k hk] at gC'
  simp only [hpq, List.map_cons, List.map_nil] at gC gC'
  rw [if_pos hp, if_pos hq] at gC
  obtain ⟨p', hp'e, hp'⟩ := star p hp (Or.inl rfl)
  obtain ⟨q', hq'e, hq'⟩ := star q hq (Or.inr rfl)
  rw [← hp'e, ← hq'e, if_pos hp', if_pos hq'] at gC'
  by_cases hkO : k ∈ insert c (orClosure n C c)
  · refine ⟨fun h => absurd rfl (h k hkO), ?_⟩
    intro k2 hk2 hkk s hs hreach
    have hkk' : k2 = k := by omega
    subst hkk'
    rcases (memO k2).mp hk2 with rfl | ⟨_, hne, hreachc⟩
    · -- the gate c itself keeps its reads
      have hpa : p = a ∧ q = b := by
        rw [hcin] at hpq; simp only [List.cons.injEq, and_true] at hpq; exact ⟨hpq.1.symm, hpq.2.symm⟩
      obtain ⟨rfl, rfl⟩ := hpa
      have e1 : p' = p := by rw [hp'e, if_neg (by omega)]
      have e2 : q' = q := by rw [hq'e, if_neg (by omega)]
      rw [e1, e2, (ih p hp).1 (notOcl p ha), (ih q hq).1 (notOcl q hb), ← gC] at gC'
      rw [gC']
      exact ⟨id, Or.inl⟩
    · -- an OR gate of the closure
      have hop : (gateAt C k2).op = GateOp.or := by
        rcases ((orReaches_iff n C k2 c).mp hreachc).2 with h | ⟨h, _⟩
        · exact absurd h.symm hne
        · exact h
      have claim : ∀ i i', i < n + k2 → (i = p ∨ i = q) → i' = (if i = n + c then sigma k2 else i) →
          (V C n x i = true → V (substReads C n c sigma) n x i' = true) ∧
          (V (substReads C n c sigma) n x i' = true → V C n x i = true ∨ V C n x s = true) := by
        intro i i' hi hiq hi'e
        by_cases hic : i = n + c
        · rw [if_pos hic] at hi'e
          have hkr := rdr (by rcases hiq with rfl | rfl <;> simp_all)
          have hsk : sigma k2 = s := hreach k2 hkr (reachSelf k2 hk)
          have hslt : s < n + c := by rcases hs with rfl | rfl <;> assumption
          have hsv := (ih s (by omega)).1 (notOcl s hslt)
          rw [hi'e, hsk, hsv, hic, valC]
          constructor
          · intro h
            simp only [Bool.and_eq_true] at h
            rcases hs with rfl | rfl
            · exact h.1
            · exact h.2
          · exact Or.inr
        · rw [if_neg hic] at hi'e
          rw [hi'e]
          by_cases hio : ∃ k3 ∈ insert c (orClosure n C c), i = n + k3
          · obtain ⟨k3, hk3, rfl⟩ := hio
            refine (ih (n + k3) hi).2 k3 hk3 rfl s hs (fun r hr hrr => hreach r hr ?_)
            refine (orReaches_iff n C k2 r).mpr ⟨hk, Or.inr ⟨hop, n + k3, ?_, hi, hrr⟩⟩
            rw [hpq]; rcases hiq with h | h <;> simp [h]
          · push_neg at hio
            rw [(ih i hi).1 (fun k3 hk3 e => hio k3 hk3 e)]
            exact ⟨id, Or.inl⟩
      obtain ⟨cp1, cp2⟩ := claim p p' hp (Or.inl rfl) hp'e
      obtain ⟨cq1, cq2⟩ := claim q q' hq (Or.inr rfl) hq'e
      rw [hop] at gC gC'
      simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false] at gC gC'
      rw [gC, gC']
      constructor
      · intro h
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact Or.inl (cp1 h)
        · exact Or.inr (cq1 h)
      · intro h
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · rcases cp2 h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr h'
        · rcases cq2 h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
  · refine ⟨fun _ => ?_, fun k2 hk2 hkk => absurd hk2 (by rw [show k2 = k by omega]; exact hkO)⟩
    have hkc : k ≠ c := fun e => hkO (e ▸ Finset.mem_insert_self _ _)
    have hkno : k ∉ orClosure n C c := fun h => hkO (Finset.mem_insert_of_mem h)
    by_cases hfro : (∃ k3 ∈ insert c (orClosure n C c), p = n + k3) ∨
        (∃ k3 ∈ insert c (orClosure n C c), q = n + k3)
    · have hkfr : k ∈ frontier n C c := by
        simp only [PEqualNP.FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
        refine ⟨hk, hkc, hkno, ?_⟩
        rcases hfro with ⟨k3, hk3, e⟩ | ⟨k3, hk3, e⟩
        · exact ⟨k3, hk3, by rw [hpq, ← e]; simp⟩
        · exact ⟨k3, hk3, by rw [hpq, ← e]; simp⟩
      have hand : (gateAt C k).op = GateOp.and := by
        rcases opAO k hk with h | h
        · exact h
        · exfalso
          apply hkno
          have reach3 : ∀ k3 ∈ insert c (orClosure n C c), OrReaches n C (n + k3) c := by
            intro k3 hk3
            rcases (memO k3).mp hk3 with rfl | ⟨_, _, h3⟩
            · exact reachSelf k3 hc
            · exact h3
          simp only [orClosure, Finset.mem_filter, Finset.mem_range]
          refine ⟨hk, hkc, (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨h, ?_⟩⟩⟩
          rcases hfro with ⟨k3, hk3, e⟩ | ⟨k3, hk3, e⟩
          · exact ⟨p, by rw [hpq]; simp, hp, e ▸ reach3 k3 hk3⟩
          · exact ⟨q, by rw [hpq]; simp, hq, e ▸ reach3 k3 hk3⟩
      -- the core equation at a frontier AND reading u (in the closure) and y (outside)
      have core : ∀ u u' y, u < n + k → (u = p ∨ u = q) → u' = (if u = n + c then sigma k else u) →
          (∃ k3 ∈ insert c (orClosure n C c), u = n + k3) →
          (∀ r ∈ readers n C c, (r = k ∨ OrReaches n C u r) →
            (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
            (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true)) →
          (V (substReads C n c sigma) n x u' && V C n x y) = (V C n x u && V C n x y) := by
        intro u u' y hu huq hu'e hocl hrd
        obtain ⟨k3, hk3, rfl⟩ := hocl
        by_cases hk3c : k3 = c
        · subst hk3c
          rw [if_pos rfl] at hu'e
          have hkr := rdr (by rcases huq with h | h <;> simp [h])
          have hs0 := hsig k hkr
          have hslt : sigma k < n + k3 := by rcases hs0 with h | h <;> rw [h] <;> assumption
          have hsv := (ih (sigma k) (by omega)).1 (notOcl _ hslt)
          obtain ⟨hb', ha'⟩ := hrd k hkr (Or.inl rfl)
          rw [hu'e, hsv]
          apply bool_key _ _ _ (V C n x a) (V C n x b) (V C n x (sigma k))
          · intro h; rw [valC] at h; simp only [Bool.and_eq_true] at h
            rcases hs0 with e | e <;> rw [e] <;> simp [h]
          · exact Or.inr
          · intro hsv' hyv
            rcases hs0 with e | e
            · rw [e] at hsv'; exact ⟨hsv', ha' e x hyv⟩
            · rw [e] at hsv'; exact ⟨hb' e x hyv, hsv'⟩
          · intro h1 h2'; rw [valC]; simp [h1, h2']
        · have hk3O := (memO k3).mp hk3
          rcases hk3O with h | ⟨hk3l, _, hk3r⟩
          · exact absurd h hk3c
          rw [if_neg (by omega)] at hu'e
          subst hu'e
          obtain ⟨r0, hr0, hr0r⟩ := clos_reader n C c k3 hk3c hk3r
          have hmem : n + k3 ∈ (gateAt C k).inputs := by rw [hpq]; rcases huq with h | h <;> simp [h]
          have hall : ∀ r ∈ readers n C c, OrReaches n C (n + k3) r → sigma r = sigma r0 :=
            fun r hr hrr => (hcons k hkfr (n + k3) hmem r0 hr0 r hr hr0r hrr).symm
          have hs := hsig r0 hr0
          obtain ⟨b1, b2⟩ := (ih (n + k3) hu).2 k3 hk3 rfl (sigma r0) hs hall
          obtain ⟨hb', ha'⟩ := hrd r0 hr0 (Or.inr hr0r)
          apply bool_key _ _ _ (V C n x a) (V C n x b) (V C n x (sigma r0)) b1 b2
          · intro hsv' hyv
            rcases hs with e | e
            · have := e; rw [e] at hsv'; exact ⟨hsv', ha' this x hyv⟩
            · have := e; rw [e] at hsv'; exact ⟨hb' this x hyv, hsv'⟩
          · intro h1 h2'
            exact or_below n C x c k3 hk3r (by rw [valC]; simp [h1, h2'])
      rw [hand] at gC gC'
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] at gC gC'
      rw [gC, gC']
      rcases hfro with ⟨k3, hk3, e⟩ | ⟨k3, hk3, e⟩
      · obtain ⟨hy, hrd⟩ := hfr k hkfr hand p q (Or.inl hpq) ⟨k3, hk3, e⟩
        have hqc : q ≠ n + c := hy c (Finset.mem_insert_self _ _)
        have e2 : q' = q := by rw [hq'e, if_neg hqc]
        rw [e2, (ih q hq).1 hy]
        exact core p p' q hp (Or.inl rfl) hp'e ⟨k3, hk3, e⟩ hrd
      · obtain ⟨hy, hrd⟩ := hfr k hkfr hand q p (Or.inr hpq) ⟨k3, hk3, e⟩
        have hpc : p ≠ n + c := hy c (Finset.mem_insert_self _ _)
        have e1 : p' = p := by rw [hp'e, if_neg hpc]
        rw [e1, (ih p hp).1 hy, Bool.and_comm, Bool.and_comm (V C n x p)]
        exact core q q' p hq (Or.inr rfl) hq'e ⟨k3, hk3, e⟩ hrd
    · push_neg at hfro
      obtain ⟨hpn, hqn⟩ := hfro
      have hpc : p ≠ n + c := hpn c (Finset.mem_insert_self _ _)
      have hqc : q ≠ n + c := hqn c (Finset.mem_insert_self _ _)
      have e1 : p' = p := by rw [hp'e, if_neg hpc]
      have e2 : q' = q := by rw [hq'e, if_neg hqc]
      rw [e1, e2, (ih p hp).1 (fun k3 hk3 e => hpn k3 hk3 e), (ih q hq).1 (fun k3 hk3 e => hqn k3 hk3 e),
        ← gC] at gC'
      exact gC'


-- Cones of the substituted circuit lie in the old cones and never contain c.
theorem cone_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j i, InCone n (substReads C n c sigma) i j → InCone n C i j ∧ i ≠ c := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨hj, k, hkj, hmem, hik⟩ := (inCone_iff n _ i j).mp h
    rw [sub_len] at hj
    rw [sub_gate C n c sigma j hj] at hmem
    simp only [List.mem_map] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have below : (i = k ∨ InCone n C i k) ∧ (i = k ∨ i ≠ c) := by
      rcases hik with rfl | hik
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · obtain ⟨h1, h2⟩ := ih k hkj i hik
        exact ⟨Or.inr h1, Or.inr h2⟩
    by_cases hpc : p = n + c
    · rw [if_pos hpc] at hpe
      have hjr : j ∈ readers n C c := by
        simp only [readers, Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hpc ▸ hp⟩
      have hkin : n + k ∈ (gateAt C c).inputs := by
        rw [hcin, ← hpe]; rcases hsig j hjr with e | e <;> simp [e]
      have hkc : k < c := by have := hRB c hc _ hkin; omega
      have hcj : c < j := by have := hRB j hj _ (hpc ▸ hp); omega
      have hic : InCone n C i c := (inCone_iff n C i c).mpr ⟨hc, k, hkc, hkin, below.1⟩
      refine ⟨(inCone_iff n C i j).mpr ⟨hj, c, hcj, hpc ▸ hp, Or.inr hic⟩, ?_⟩
      rcases below.2 with rfl | h
      · omega
      · exact h
    · rw [if_neg hpc] at hpe
      subst hpe
      refine ⟨(inCone_iff n C i j).mpr ⟨hj, k, hkj, hp, below.1⟩, ?_⟩
      rcases below.2 with rfl | h
      · intro e; exact hpc (by rw [e])
      · exact h

theorem live_drop (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (hout : C.output ≠ n + c) (hlive : c ∈ liveGates n C) :
    liveSize n (substReads C n c sigma) + 1 ≤ liveSize n C := by
  have hcone := cone_sub n C c a b sigma hRB hc hcin hsig
  have hsub : liveGates n (substReads C n c sigma) ⊆ liveGates n C := by
    intro j hj
    simp only [liveGates, Finset.mem_filter, Finset.mem_range, sub_len] at hj ⊢
    obtain ⟨hjl, hn, h⟩ := hj
    refine ⟨hjl, hn, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (hcone _ _ h).1
  have hnot : c ∉ liveGates n (substReads C n c sigma) := by
    simp only [liveGates, Finset.mem_filter, Finset.mem_range, sub_len]
    rintro ⟨_, hn, h | h⟩
    · exact hout (by simp only [substReads] at h hn; omega)
    · exact (hcone _ _ h).2 rfl
  have := Finset.card_lt_card ⟨hsub, fun h => hnot (h hlive)⟩
  simp only [liveSize]; omega

end PEqualNP.Outside.L_meta_3297

open PEqualNP.Outside.L_meta_3297 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hcop hcin hsig hfr hcons hout hlive
  refine ⟨?_, live_drop n C c a b sigma hAO.2.1 hc hcin hsig (hout c (Finset.mem_insert_self _ _)) hlive⟩
  intro k hk hkc hko z
  have h := (sem n C c a b sigma hAO hc hcop hcin hsig hfr hcons z (n + k)).1 (by
    intro k' hk' e
    have : k' = k := by omega
    subst this
    rcases Finset.mem_insert.mp hk' with h | h
    · exact hkc h
    · exact hko h)
  exact h
