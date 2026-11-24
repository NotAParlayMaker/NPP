import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · exact List.getD_eq_default _ false (by omega)

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
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

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
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

def wire {n : ℕ} (C : Circuit) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma gateVal_eq {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wire C (n + j) x := by
  simp [gateVal, wire, Circuit.wires, wiresFrom]

lemma wire_input {n : ℕ} (C : Circuit) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wire C i x = x ⟨i, hi⟩ := by
  rw [wire, getD_wiresFrom_lt _ _ _ (by simpa [List.length_ofFn] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hi), List.getElem_ofFn]

lemma wire_gate {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    wire C (n + k) x =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
        if i < n + k then wire C i x else false) := by
  simpa [wire, List.length_ofFn] using getD_wiresFrom_gate C.gates (List.ofFn x) k hk

lemma mono_ops {C : Circuit} (hm : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm g hg).1

lemma mono_len {C : Circuit} (hm : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    (C.gates[k]).inputs.length ≤ 2 :=
  (hm _ (List.getElem_mem hk)).2

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma wire_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (hle : ∀ t, x t = true → y t = true) (i : ℕ) :
    wire C i x = true → wire C i y = true := by
  intro hi
  apply wiresFrom_mono C.gates (fun g hg => mono_ops hm hg) (List.ofFn x) (List.ofFn y)
    (by simp [List.length_ofFn]) ?_ i hi
  intro k hk
  by_cases hk' : k < n
  · rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hk'), List.getElem_ofFn] at hk
    rw [List.getD_eq_getElem _ _ (by simpa [List.length_ofFn] using hk'), List.getElem_ofFn]
    exact hle _ hk
  · rw [List.getD_eq_default _ _ (by simpa [List.length_ofFn] using Nat.le_of_not_lt hk')] at hk
    exact Bool.noConfusion hk

def conePrefix (n : ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (coneStep n) []

lemma cones_eq (n : ℕ) (C : Circuit) : cones n C = conePrefix n C.gates := rfl

def coneCell (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    coneStep n cs g = cs ++ [coneCell n cs g] := rfl

lemma foldl_cone_append (n : ℕ) (cs : List (List ℕ)) :
    ∀ gs : List Gate, ∃ t : List (List ℕ),
      gs.foldl (coneStep n) cs = cs ++ t ∧ t.length = gs.length := by
  intro gs
  induction gs generalizing cs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (cs ++ [coneCell n cs g])
    refine ⟨coneCell n cs g :: t, ?_, ?_⟩
    · rw [List.foldl_cons, coneStep_eq, ht, List.append_assoc]
      rfl
    · rw [List.length_cons, hl, List.length_cons]

lemma conePrefix_length (n : ℕ) (gs : List Gate) :
    (conePrefix n gs).length = gs.length := by
  obtain ⟨t, ht, hl⟩ := foldl_cone_append n [] gs
  simp [conePrefix, ht, hl]

lemma foldl_cone_getD (n : ℕ) (cs : List (List ℕ)) (gs : List Gate) (i : ℕ)
    (hi : i < cs.length) :
    (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
  obtain ⟨_, ht, _⟩ := foldl_cone_append n cs gs
  rw [ht, List.getD_append _ _ _ _ hi]

lemma conePrefix_append (n : ℕ) (gs₁ gs₂ : List Gate) :
    conePrefix n (gs₁ ++ gs₂) = gs₂.foldl (coneStep n) (conePrefix n gs₁) := by
  simp [conePrefix, List.foldl_append]

lemma getD_take_list (l : List (List ℕ)) (i k : ℕ) (hi : i < k) :
    (l.take k).getD i [] = l.getD i [] := by
  by_cases h : i < l.length
  · have hi' : i < (l.take k).length := by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨hi, h⟩
    rw [List.getD_eq_getElem _ _ hi', List.getElem_take, List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default (l.take k) [] (by rw [List.length_take]; omega),
      List.getD_eq_default l [] (Nat.le_of_not_lt h)]

lemma conePrefix_take (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) :
    (conePrefix n gs).take k = conePrefix n (gs.take k) := by
  have hs : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  obtain ⟨t, ht, _⟩ := foldl_cone_append n (conePrefix n (gs.take k)) (gs.drop k)
  have hlen : (conePrefix n (gs.take k)).length = k := by
    rw [conePrefix_length, List.length_take, Nat.min_eq_left hk]
  have heq : conePrefix n gs = conePrefix n (gs.take k) ++ t := by
    have happ : conePrefix n gs =
        (gs.drop k).foldl (coneStep n) (conePrefix n (gs.take k)) := by
      conv_lhs => rw [hs]
      exact conePrefix_append n (gs.take k) (gs.drop k)
    rw [happ, ht]
  rw [heq]
  have hle : k ≤ (conePrefix n (gs.take k)).length := by rw [hlen]
  rw [List.take_append_of_le_length hle]
  have hidx : (conePrefix n (gs.take k)).take k =
      (conePrefix n (gs.take k)).take (conePrefix n (gs.take k)).length :=
    congrArg (fun i => (conePrefix n (gs.take k)).take i) hlen.symm
  rw [hidx, List.take_length]

lemma conePrefix_get (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (conePrefix n gs)[j]'(by rw [conePrefix_length]; exact hj) =
      ((gs[j]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (conePrefix n gs).getD (w - n) []) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    rw [List.drop_eq_getElem_cons hj] at h1
    exact h1
  let cs := conePrefix n (gs.take j)
  have hlen : cs.length = j := by
    dsimp [cs]
    rw [conePrefix_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : conePrefix n gs =
      (gs.drop (j + 1)).foldl (coneStep n) (coneStep n cs gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [conePrefix_append]
    rfl
  have hidx : j < (coneStep n cs gs[j]).length := by
    rw [coneStep_eq, List.length_append, List.length_singleton, hlen]
    omega
  have hstay : (conePrefix n gs).getD j [] = (coneStep n cs gs[j]).getD j [] := by
    rw [heq]
    exact foldl_cone_getD n (coneStep n cs gs[j]) (gs.drop (j + 1)) j hidx
  have hcell : (coneStep n cs gs[j]).getD j [] = coneCell n cs gs[j] := by
    rw [coneStep_eq, List.getD_append_right _ _ _ _ (by omega), hlen]
    simp
  have hpre : cs = (conePrefix n gs).take j := by
    dsimp [cs]
    exact (conePrefix_take n gs j (Nat.le_of_lt hj)).symm
  have hget : ∀ i < j, cs.getD i [] = (conePrefix n gs).getD i [] := by
    intro i hi
    rw [hpre]
    exact getD_take_list (conePrefix n gs) i j hi
  have hsame : coneCell n cs gs[j] =
      ((gs[j]).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (conePrefix n gs).getD (w - n) []) := by
    unfold coneCell
    rw [hlen]
    unfold List.flatMap
    congr 1
    apply List.map_congr_left
    intro w hw
    have hw' := (List.mem_filter.mp hw).2
    simp only [decide_eq_true_eq] at hw'
    have hwn : w - n < j := by omega
    rw [hget _ hwn]
  have hlenj : j < (conePrefix n gs).length := by rw [conePrefix_length]; exact hj
  rw [List.getD_eq_getElem _ _ hlenj] at hstay
  rw [hstay, hcell, hsame]

lemma mem_conePrefix (n : ℕ) (gs : List Gate) (i j : ℕ) (hj : j < gs.length) :
    i ∈ (conePrefix n gs).getD j [] ↔
      ∃ w ∈ (gs[j]).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (conePrefix n gs).getD (w - n) []) := by
  have hlen : j < (conePrefix n gs).length := by rw [conePrefix_length]; exact hj
  rw [List.getD_eq_getElem _ _ hlen, conePrefix_get n gs j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, hw, hmem⟩
    exact ⟨w, hw.1, hw.2.1, hw.2.2, hmem⟩
  · rintro ⟨w, hw, h1, h2, hmem⟩
    exact ⟨w, ⟨hw, h1, h2⟩, hmem⟩

lemma mem_cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (hj : j < gs.length)
    (hi : i ∈ (conePrefix n gs).getD j []) : i < j := by
  induction j using Nat.strong_induction_on generalizing i with
  | ind j ih =>
    rw [mem_conePrefix n gs i j hj] at hi
    obtain ⟨w, _, hlo, hhi, hmem⟩ := hi
    rcases hmem with rfl | hmem
    · omega
    · have hlt : w - n < j := by omega
      have hlen : w - n < gs.length := by omega
      exact Nat.lt_trans (ih (w - n) hlt i hlen hmem) hlt

lemma mem_cone_trans (n : ℕ) (gs : List Gate) (a b c : ℕ) (hc : c < gs.length)
    (hab : a ∈ (conePrefix n gs).getD b [])
    (hbc : b ∈ (conePrefix n gs).getD c []) :
    a ∈ (conePrefix n gs).getD c [] := by
  induction c using Nat.strong_induction_on generalizing a b with
  | ind c ih =>
    rw [mem_conePrefix n gs b c hc] at hbc
    obtain ⟨w, hw, hlo, hhi, hmem⟩ := hbc
    rw [mem_conePrefix n gs a c hc]
    rcases hmem with rfl | hmem
    · exact ⟨w, hw, hlo, hhi, Or.inr hab⟩
    · have hlt : w - n < c := by omega
      have hlen : w - n < gs.length := by omega
      exact ⟨w, hw, hlo, hhi, Or.inr (ih (w - n) hlt a b hlen hab hmem)⟩

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ i ∈ (conePrefix n C.gates).getD j [] := by
  simp [InCone, cones_eq]

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : i < j := by
  have hmem : i ∈ (conePrefix n C.gates).getD j [] := (inCone_iff n C i j).mp h
  have hj : j < C.gates.length := by
    by_contra hge
    have hempty : (conePrefix n C.gates).getD j [] = [] :=
      List.getD_eq_default (conePrefix n C.gates) [] (by rw [conePrefix_length]; omega)
    rw [hempty] at hmem
    simp at hmem
  exact mem_cone_lt n C.gates i j hj hmem

lemma inCone_trans {n : ℕ} {C : Circuit} {a b c : ℕ}
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  have hmem_b : b ∈ (conePrefix n C.gates).getD c [] := (inCone_iff n C b c).mp hbc
  have hc : c < C.gates.length := by
    by_contra hge
    have hempty : (conePrefix n C.gates).getD c [] = [] :=
      List.getD_eq_default (conePrefix n C.gates) [] (by rw [conePrefix_length]; omega)
    rw [hempty] at hmem_b
    simp at hmem_b
  rw [inCone_iff] at hab hbc ⊢
  exact mem_cone_trans n C.gates a b c hc hab hbc

lemma reads_inCone {n : ℕ} {C : Circuit} {j w : ℕ} (hj : j < C.gates.length)
    (hw : w ∈ (C.gates[j]).inputs) (h : n ≤ w ∧ w < n + j) :
    InCone n C (w - n) j := by
  rw [inCone_iff, mem_conePrefix n C.gates (w - n) j hj]
  exact ⟨w, hw, h.1, h.2, Or.inl rfl⟩

def singleton {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun z => decide (z = u)

def clamped {n : ℕ} (C : Circuit) (j w : ℕ) (x : Fin n → Bool) : Bool :=
  if w < n + j then wire C w x else false

lemma clamped_true {n : ℕ} {C : Circuit} {j w : ℕ} {x : Fin n → Bool}
    (h : clamped C j w x = true) : w < n + j ∧ wire C w x = true := by
  simp only [clamped] at h
  by_cases hlt : w < n + j
  · simp [hlt] at h
    exact ⟨hlt, h⟩
  · simp [hlt] at h

def supp (n : ℕ) (C : Circuit) (j w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun t => clamped C j w (singleton t) = true

lemma mem_supp {n : ℕ} {C : Circuit} {j w : ℕ} {t : Fin n} :
    t ∈ supp n C j w ↔ clamped C j w (singleton t) = true := by
  simp [supp]

lemma graphFun_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · intro h
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨a, ha, _⟩ := h
      simp at ha
    · exact h
  · intro h
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr h

lemma not_on_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ)
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    (t : Fin n) : wire C (n + j) (singleton t) = false := by
  cases hval : wire C (n + j) (singleton t) with
  | false => rfl
  | true =>
    exfalso
    have hg := hclean _ (by simpa [gateVal_eq] using hval)
    rw [graphFun_iff] at hg
    obtain ⟨u, v, huv, hu, hv⟩ := hg
    simp only [singleton, decide_eq_true_eq] at hu hv
    subst hu
    subst hv
    exact G.irrefl huv

lemma and_zero {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (hin : (C.gates[j]).inputs = [])
    (x : Fin n → Bool) : wire C (n + j) x = true := by
  rw [wire_gate C j hj, ha, hin]
  simp [GateOp.eval]

lemma and_one {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a : ℕ) (hin : (C.gates[j]).inputs = [a])
    (x : Fin n → Bool) : wire C (n + j) x = clamped C j a x := by
  rw [wire_gate C j hj, ha, hin, List.map_cons, List.map_nil]
  simp only [GateOp.eval]
  rw [List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rfl

lemma and_bin {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (x : Fin n → Bool) :
    wire C (n + j) x = (clamped C j a x && clamped C j b x) := by
  rw [wire_gate C j hj, ha, hin, List.map_cons, List.map_cons, List.map_nil]
  simp only [GateOp.eval]
  rw [List.all_cons, List.all_cons, List.all_nil, id_eq, id_eq, Bool.and_true]
  rfl

lemma direct_dep {n : ℕ} (C : Circuit) (j w : ℕ) (hj : j < C.gates.length)
    (hw : w ∈ (C.gates[j]).inputs) (hlt : w < n + j) :
    w < n ∨ n ≤ w ∧ InCone n C (w - n) j := by
  by_cases h : w < n
  · exact Or.inl h
  · exact Or.inr ⟨Nat.le_of_not_lt h, reads_inCone hj hw ⟨Nat.le_of_not_lt h, hlt⟩⟩

lemma witness {n : ℕ} (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool)
    (hno : ∀ i, i < j → InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i x = false)
    (w : ℕ) (hw : w < n + j)
    (hdep : w < n ∨ n ≤ w ∧ InCone n C (w - n) j)
    (htrue : wire C w x = true) :
    ∃ t : Fin n, x t = true ∧ wire C w (singleton t) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [wire_input C w hwn] at htrue
        exact htrue
      · rw [wire_input C w hwn]
        simp [singleton]
    · have hge : n ≤ w := Nat.le_of_not_lt hwn
      rcases hdep with hdep | hdep
      · omega
      · let k := w - n
        have hk : k < j := by dsimp [k]; omega
        have hklen : k < C.gates.length := by omega
        have hwire : wire C (n + k) x = true := by
          rw [show n + k = w by dsimp [k]; omega]
          exact htrue
        have hcone : InCone n C k j := by
          simpa [k] using hdep.2
        have hop := mono_ops hm (List.getElem_mem hklen)
        have hnot : (C.gates[k]).op ≠ GateOp.and := by
          intro ha
          have hgv : gateVal n C k x = true := by simpa [gateVal_eq] using hwire
          have hfalse := hno k hk hcone (by rw [gateAt_eq C k hklen]; exact ha)
          rw [hgv] at hfalse
          exact Bool.noConfusion hfalse
        have hor : (C.gates[k]).op = GateOp.or := by
          rcases hop with h | h
          · exact (hnot h).elim
          · exact h
        rw [wire_gate C k hklen, hor, GateOp.eval, List.any_eq_true] at hwire
        obtain ⟨b, hbmem, hb⟩ := hwire
        obtain ⟨p, hpmem, hpfeq⟩ := List.mem_map.mp hbmem
        have hpval : (if p < n + k then wire C p x else false) = true := by
          have hb' : b = true := by simpa using hb
          rw [← hpfeq] at hb'
          exact hb'
        have hplt : p < n + k := by
          by_contra hge'
          simp [hge'] at hpval
        have hpwire : wire C p x = true := by
          simpa [hplt] using hpval
        have hpdep : p < n ∨ n ≤ p ∧ InCone n C (p - n) j := by
          by_cases hp : p < n
          · exact Or.inl hp
          · refine Or.inr ⟨Nat.le_of_not_lt hp, ?_⟩
            have hsub : InCone n C (p - n) k :=
              reads_inCone hklen hpmem ⟨Nat.le_of_not_lt hp, hplt⟩
            exact inCone_trans hsub hcone
        have hp_lt : p < w := by dsimp [k] at hplt; omega
        obtain ⟨t, ht, hsing⟩ := ih p hp_lt (by omega) hpdep hpwire
        refine ⟨t, ht, ?_⟩
        rw [show w = n + k by dsimp [k]; omega]
        rw [wire_gate C k hklen, hor, GateOp.eval, List.any_eq_true]
        refine ⟨true, ?_, rfl⟩
        have hmem : (if p < n + k then wire C p (singleton t) else false) ∈
            ((C.gates[k]).inputs.map fun i =>
              if i < n + k then wire C i (singleton t) else false) :=
          List.mem_map.mpr ⟨p, hpmem, rfl⟩
        simpa [hplt, hsing] using hmem

lemma clamped_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (j w : ℕ)
    (x y : Fin n → Bool) (hle : ∀ t, x t = true → y t = true) :
    clamped C j w x = true → clamped C j w y = true := by
  intro h
  obtain ⟨hlt, hw⟩ := clamped_true h
  have hy := wire_mono C hm x y hle w hw
  simp [clamped, hlt, hy]

lemma supp_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    Disjoint (supp n C j a) (supp n C j b) := by
  rw [Finset.disjoint_left]
  intro t hta htb
  have hga : clamped C j a (singleton t) = true := (mem_supp).mp hta
  have hgb : clamped C j b (singleton t) = true := (mem_supp).mp htb
  have hgate : wire C (n + j) (singleton t) = true := by
    rw [and_bin C j hj ha a b hin, hga, hgb]
    rfl
  have hnot := not_on_singleton G C j hclean t
  rw [hgate] at hnot
  exact Bool.noConfusion hnot

lemma cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    {p q : Fin n} (hp : p ∈ supp n C j a) (hq : q ∈ supp n C j b) : G.Adj p q := by
  have hp' : clamped C j a (pairInput p q) = true :=
    clamped_mono C hm j a (singleton p) (pairInput p q)
      (by intro t ht; simp only [singleton, decide_eq_true_eq] at ht; simp [pairInput, ht])
      ((mem_supp).mp hp)
  have hq' : clamped C j b (pairInput p q) = true :=
    clamped_mono C hm j b (singleton q) (pairInput p q)
      (by intro t ht; simp only [singleton, decide_eq_true_eq] at ht; simp [pairInput, ht])
      ((mem_supp).mp hq)
  have hgate : wire C (n + j) (pairInput p q) = true := by
    rw [and_bin C j hj ha a b hin, hp', hq']
    rfl
  have hg := hclean _ (by simpa [gateVal_eq] using hgate)
  rw [graphFun_iff] at hg
  obtain ⟨u, v, huv, hu, hv⟩ := hg
  simp only [pairInput, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (G.irrefl huv).elim
  · exact huv
  · exact huv.symm
  · exact (G.irrefl huv).elim

lemma not_two_big {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (h0 : 1 < (supp n C j a).card) (h1 : 1 < (supp n C j b).card) : False := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h0
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp h1
  exact hc4 p r q s hpq hrs
    ⟨cross_adj G C hm j hj ha a b hin hclean hp hr,
     (cross_adj G C hm j hj ha a b hin hclean hq hr).symm,
     cross_adj G C hm j hj ha a b hin hclean hq hs,
     (cross_adj G C hm j hj ha a b hin hclean hp hs).symm⟩

lemma owned_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    {u v : Fin n} (hown : Owns n C j u v) :
    (u ∈ supp n C j a ∧ v ∈ supp n C j b) ∨ (v ∈ supp n C j a ∧ u ∈ supp n C j b) := by
  rcases hown with ⟨_, _, hval, hno⟩
  have hpair : wire C (n + j) (pairInput u v) = true := by simpa [gateVal_eq] using hval
  rw [and_bin C j hj ha a b hin] at hpair
  simp only [Bool.and_eq_true] at hpair
  obtain ⟨hca, hcb⟩ := hpair
  obtain ⟨hlta, hwa⟩ := clamped_true hca
  obtain ⟨hltb, hwb⟩ := clamped_true hcb
  have hamem : a ∈ (C.gates[j]).inputs := by simp [hin]
  have hbmem : b ∈ (C.gates[j]).inputs := by simp [hin]
  obtain ⟨t, ht, hta⟩ := witness C hm j hj (pairInput u v) hno a hlta
    (direct_dep C j a hj hamem hlta) hwa
  obtain ⟨s, hs, hsb⟩ := witness C hm j hj (pairInput u v) hno b hltb
    (direct_dep C j b hj hbmem hltb) hwb
  have hts : t ∈ supp n C j a := by
    rw [mem_supp]
    simp [clamped, hlta, hta]
  have hss : s ∈ supp n C j b := by
    rw [mem_supp]
    simp [clamped, hltb, hsb]
  have htuv : t = u ∨ t = v := by simpa [pairInput, decide_eq_true_eq] using ht
  have hsuv : s = u ∨ s = v := by simpa [pairInput, decide_eq_true_eq] using hs
  have hne : t ≠ s := by
    intro heq
    exact Finset.disjoint_left.mp
      (supp_disjoint G C j hj ha a b hin hclean) hts (heq ▸ hss)
  rcases htuv with rfl | rfl <;> rcases hsuv with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl ⟨hts, hss⟩
  · exact Or.inr ⟨hts, hss⟩
  · exact (hne rfl).elim

lemma conclude {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ 1)
    (hown : ∀ u v : Fin n, Owns n C j u v → u ∈ S ∨ v ∈ S) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  by_cases hE : S = ∅
  · left
    intro u v _ h
    have hmem := hown u v h
    simp [hE] at hmem
  · right
    have hcard : S.card = 1 := by
      have hpos : S.card ≠ 0 := by
        intro h0
        exact hE (Finset.card_eq_zero.mp h0)
      omega
    obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hcard
    refine ⟨s, ?_⟩
    intro p q _ h
    rcases hown p q h with hp | hq
    · exact Or.inl (by simpa [hs, Finset.mem_singleton] using hp)
    · exact Or.inr (by simpa [hs, Finset.mem_singleton] using hq)

lemma one_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a : ℕ) (hin : (C.gates[j]).inputs = [a])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    ∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v := by
  intro u v _ hown
  rcases hown with ⟨_, _, hval, hno⟩
  have hpair : clamped C j a (pairInput u v) = true := by
    have hw : wire C (n + j) (pairInput u v) = true := by simpa [gateVal_eq] using hval
    rw [and_one C j hj ha a hin] at hw
    exact hw
  obtain ⟨hlt, hwire⟩ := clamped_true hpair
  have hamem : a ∈ (C.gates[j]).inputs := by simp [hin]
  obtain ⟨t, _, hsing⟩ := witness C hm j hj (pairInput u v) hno a hlt
    (direct_dep C j a hj hamem hlt) hwire
  have hgate : wire C (n + j) (singleton t) = true := by
    rw [and_one C j hj ha a hin]
    simp [clamped, hlt, hsing]
  have hnot := not_on_singleton G C j hclean t
  rw [hgate] at hnot
  exact Bool.noConfusion hnot

lemma two_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (a b : ℕ) (hin : (C.gates[j]).inputs = [a, b])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  by_cases h0 : (supp n C j a).card ≤ 1
  · exact conclude G C j (supp n C j a) h0 (fun u v h => by
      rcases owned_cross G C hm j hj ha a b hin hclean h with ⟨hu, _⟩ | ⟨hu, _⟩
      · exact Or.inl hu
      · exact Or.inr hu)
  · by_cases h1 : (supp n C j b).card ≤ 1
    · exact conclude G C j (supp n C j b) h1 (fun u v h => by
        rcases owned_cross G C hm j hj ha a b hin hclean h with ⟨_, hv⟩ | ⟨_, hv⟩
        · exact Or.inr hv
        · exact Or.inl hv)
    · exact False.elim (not_two_big G C hm j hj ha a b hin hclean hc4 (by omega) (by omega))

lemma zero_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (ha : (C.gates[j]).op = GateOp.and) (hin : (C.gates[j]).inputs = [])
    (hclean : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    False := by
  have htrue := and_zero (n := n) C j hj ha hin (fun _ => false)
  have hg := hclean _ (by simpa [gateVal_eq] using htrue)
  rw [graphFun_iff] at hg
  obtain ⟨u, _, _, hu, _⟩ := hg
  simp at hu

lemma result : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ C : Circuit, Monotone2 C → ∀ j : ℕ, j < C.gates.length →
      (gateAt C j).op = GateOp.and →
      (∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) →
      (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
        ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  intro n G _ hc4 C hm j hj hop hclean
  have ha : (C.gates[j]).op = GateOp.and := by rw [← gateAt_eq C j hj]; exact hop
  have hlen := mono_len hm j hj
  cases hinputs : (C.gates[j]).inputs with
  | nil =>
    exact False.elim (zero_false G C j hj ha hinputs hclean)
  | cons a rest =>
    cases rest with
    | nil =>
      exact Or.inl (one_clean G C hm j hj ha a hinputs hclean)
    | cons b rest2 =>
      have hrest : rest2 = [] := by
        have hlen' : rest2.length + 2 ≤ 2 := by simpa [hinputs] using hlen
        have : rest2.length = 0 := by omega
        exact List.length_eq_zero_iff.mp this
      subst hrest
      exact two_star G C hm j hj ha a b hinputs hclean hc4

end PEqualNP.Outside.L_meta_1600

theorem PEqualNP.Outside.L_meta_1600 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s :=
  PEqualNP.Outside.L_meta_1600.result
