import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1751_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)


def Rd (C : Circuit) (n : ℕ) (a b : ℕ) : Prop :=
  b < a ∧ ∃ h : Gate, C.gates[a]? = some h ∧ n + b ∈ h.inputs

def Lin (C : Circuit) (n : ℕ) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C n x w = true ↔ ∃ i : Fin n, x i = true ∧ val C n (e1 i) w = true

def Low (C : Circuit) (n : ℕ) (A : Finset ℕ) (b : ℕ) : Prop :=
  b ∉ A ∧ ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) b i

def Sing (C : Circuit) (n : ℕ) (w : ℕ) : Prop :=
  ∃ t : Fin n, ∀ i : Fin n, val C n (e1 i) w = true ↔ i = t

def Subst (C : Circuit) (n : ℕ) (k : ℕ) : Prop :=
  (∃ x : Fin n → Bool, val C n x (n + k) = true) ∧ ¬ Sing C n (n + k)

def InS (C : Circuit) (n : ℕ) (o g : ℕ) : Prop :=
  Relation.ReflTransGen (fun a b => Rd C n a b ∧ Subst C n b) o g

theorem card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (Q : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b ∈ t, Q a b)
    (h2 : ∀ a1 ∈ s, ∀ a2 ∈ s, ∀ b, Q a1 b → Q a2 b → a1 = a2) : s.card ≤ t.card := by
  classical
  have hsub : s ⊆ t.biUnion (fun b => s.filter (fun a => Q a b)) := by
    intro a ha
    obtain ⟨b, hb, hq⟩ := h1 a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hq⟩⟩
  calc s.card ≤ (t.biUnion fun b => s.filter fun a => Q a b).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => Q a b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ t, 1 := Finset.sum_le_sum (fun b _ => Finset.card_le_one.mpr (by
        intro a1 h1' a2 h2'
        rw [Finset.mem_filter] at h1' h2'
        exact h2 a1 h1'.1 a2 h2'.1 b h1'.2 h2'.2))
    _ = t.card := by simp

theorem two_mem (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ w ∈ l, w = a ∨ w = b := by
  intro w hw
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hw
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hw
    omega
  · simp at hl

theorem gate_or (C : Circuit) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hj : j ∉ A) : h.op = GateOp.or := by
  have hmem : h ∈ C.gates := List.mem_of_getElem? hg
  have hop := (hMono h hmem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop
  · exact absurd ((hA j).mpr ⟨h, hg, hop⟩) hj
  · exact hop

theorem input_e1 (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) (t : Fin n)
    (hv : val C n (e1 t) w = true) : (⟨w, hw⟩ : Fin n) = t := by
  rw [val_input C n _ w hw] at hv
  simpa [e1] using hv

theorem lin_input (C : Circuit) (n : ℕ) (w : ℕ) (hw : w < n) : Lin C n w := by
  intro x
  rw [val_input C n x w hw]
  constructor
  · intro hx
    exact ⟨⟨w, hw⟩, hx, by rw [val_input C n _ w hw]; simp [e1]⟩
  · rintro ⟨i, hi, hv⟩
    rw [input_e1 C n w hw i hv]
    exact hi

theorem low_down (C : Circuit) (n : ℕ) (A : Finset ℕ) (b k : ℕ)
    (hb : Low C n A b) (hr : Rd C n b k) : Low C n A k :=
  ⟨fun hk => hb.2 k hk (Relation.TransGen.single hr),
   fun i hi ht => hb.2 i hi (Relation.TransGen.head hr ht)⟩

theorem low_lin (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and) :
    ∀ (b : ℕ) (h : Gate), C.gates[b]? = some h → Low C n A b → Lin C n (n + b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hg hlow
    have hop := gate_or C A hMono hA b h hg hlow.1
    have hread : ∀ w ∈ h.inputs, w < n + b → Lin C n w := by
      intro w hw hlt
      by_cases hwn : w < n
      · exact lin_input C n w hwn
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hkb : k < b := by omega
        have hblen : b < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
        have hklen : k < C.gates.length := by omega
        exact ih k hkb _ (List.getElem?_eq_getElem hklen)
          (low_down C n A b k hlow ⟨hkb, h, hg, hw⟩)
    intro x
    constructor
    · intro hx
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n x b h hg hop).mp hx
      obtain ⟨i, hi, hiv⟩ := (hread w hw hlt x).mp hv
      exact ⟨i, hi, (val_or C n _ b h hg hop).mpr ⟨w, hw, hlt, hiv⟩⟩
    · rintro ⟨i, hi, hiv⟩
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n _ b h hg hop).mp hiv
      exact (val_or C n x b h hg hop).mpr ⟨w, hw, hlt, (hread w hw hlt x).mpr ⟨i, hi, hv⟩⟩

theorem and_reads_low (C : Circuit) (n : ℕ) (A : Finset ℕ)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hjA : j ∈ A)
    (k : ℕ) (hw : n + k ∈ h.inputs) (hkj : k < j) : Low C n A k :=
  ⟨fun hk => h5 j hjA k hk (Relation.TransGen.single ⟨hkj, h, hg, hw⟩),
   fun i hi ht => h5 j hjA i hi (Relation.TransGen.head ⟨hkj, h, hg, hw⟩ ht)⟩

theorem and_reads_lin (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hjA : j ∈ A)
    (w : ℕ) (hw : w ∈ h.inputs) (hlt : w < n + j) : Lin C n w := by
  by_cases hwn : w < n
  · exact lin_input C n w hwn
  · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hkj : k < j := by omega
    have hjlen : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
    have hklen : k < C.gates.length := by omega
    exact low_lin C n A hMono hA k _ (List.getElem?_eq_getElem hklen)
      (and_reads_low C n A h5 j h hg hjA k hw hkj)

theorem upper (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (o : ℕ) (x : Fin n → Bool) :
    ∀ g : ℕ, InS C n o g → (∀ i : Fin n, val C n (e1 i) (n + g) ≠ true) →
      val C n x (n + g) = true → ∃ j ∈ A, InS C n o j ∧ val C n x (n + j) = true := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hS hV hx
    by_cases hgA : g ∈ A
    · exact ⟨g, hgA, hS, hx⟩
    · cases hg : C.gates[g]? with
      | none =>
        rw [val_none C n x g hg] at hx
        simp at hx
      | some h =>
        have hop := gate_or C A hMono hA g h hg hgA
        obtain ⟨w, hw, hlt, hv⟩ := (val_or C n x g h hg hop).mp hx
        have hup : ∀ y : Fin n → Bool, val C n y w = true → val C n y (n + g) = true :=
          fun y hy => (val_or C n y g h hg hop).mpr ⟨w, hw, hlt, hy⟩
        by_cases hwn : w < n
        · exfalso
          refine hV ⟨w, hwn⟩ (hup _ ?_)
          rw [val_input C n _ w hwn]
          simp [e1]
        · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
          have hsub : Subst C n k :=
            ⟨⟨x, hv⟩, fun ⟨t, ht⟩ => hV t (hup _ ((ht t).mpr rfl))⟩
          exact ih k (by omega) (hS.tail ⟨⟨by omega, h, hg, hw⟩, hsub⟩)
            (fun i hi => hV i (hup _ hi)) hv

theorem leaf (C : Circuit) (n : ℕ) (A : Finset ℕ) (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (adj : Fin n → Fin n → Prop) (o : ℕ) (c t : Fin n) :
    ∀ k : ℕ, InS C n o k → Low C n A k →
      (∀ i : Fin n, val C n (e1 i) (n + k) = true → adj c i) →
      val C n (e1 t) (n + k) = true →
      (∃ t' : Fin n, t' ≠ t ∧ val C n (e1 t') (n + k) = true) →
      ∃ g w : ℕ, InS C n o g ∧ g ∉ A ∧
        (∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs ∧ w < n + g) ∧
        (∀ i : Fin n, val C n (e1 i) w = true ↔ i = t) ∧
        (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + g) = true ∧
          val C n (e1 b) (n + g) = true) ∧
        (∀ i : Fin n, val C n (e1 i) (n + g) = true → adj c i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hS hlow hadj ht hex
    cases hg : C.gates[k]? with
    | none =>
      rw [val_none C n _ k hg] at ht
      simp at ht
    | some h =>
      have hop := gate_or C A hMono hA k h hg hlow.1
      obtain ⟨w, hw, hlt, hv⟩ := (val_or C n _ k h hg hop).mp ht
      have hup : ∀ y : Fin n → Bool, val C n y w = true → val C n y (n + k) = true :=
        fun y hy => (val_or C n y k h hg hop).mpr ⟨w, hw, hlt, hy⟩
      by_cases hs : ∀ i : Fin n, val C n (e1 i) w = true → i = t
      · obtain ⟨t', ht', hv'⟩ := hex
        exact ⟨k, w, hS, hlow.1, ⟨h, hg, hw, hlt⟩,
          fun i => ⟨hs i, fun hi => by rw [hi]; exact hv⟩, ⟨t', t, ht', hv', ht⟩, hadj⟩
      · push Not at hs
        obtain ⟨t2, ht2v, ht2⟩ := hs
        have hwn : ¬ w < n := by
          intro hwn
          have a1 := input_e1 C n w hwn t hv
          have a2 := input_e1 C n w hwn t2 ht2v
          exact ht2 (a2.symm.trans a1)
        obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have hr : Rd C n k k' := ⟨by omega, h, hg, hw⟩
        have hsub : Subst C n k' :=
          ⟨⟨_, hv⟩, fun ⟨t0, ht0⟩ => ht2 (((ht0 t2).mp ht2v).trans ((ht0 t).mp hv).symm)⟩
        exact ih k' (by omega) (hS.tail ⟨hr, hsub⟩) (low_down C n A k k' hlow hr)
          (fun i hi => hadj i (hup _ hi)) hv ⟨t2, ht2, ht2v⟩


-- A circuit of AND and OR gates is monotone in its input.
theorem val_mono (C : Circuit) (n : ℕ) (hMono : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C n x w = true → val C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hwn : w < n
    · rw [val_input C n x w hwn] at hx
      rw [val_input C n y w hwn]
      exact hxy _ hx
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      cases hg : C.gates[k]? with
      | none =>
        rw [val_none C n x k hg] at hx
        simp at hx
      | some h =>
        have hop := (hMono h (List.mem_of_getElem? hg)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · refine (val_and C n y k h hg hop).mpr (fun w' hw' => ?_)
          obtain ⟨hlt, hv⟩ := (val_and C n x k h hg hop).mp hx w' hw'
          exact ⟨hlt, ih w' hlt hv⟩
        · obtain ⟨w', hw', hlt, hv⟩ := (val_or C n x k h hg hop).mp hx
          exact (val_or C n y k h hg hop).mpr ⟨w', hw', hlt, ih w' hlt hv⟩

theorem list_two (l : List ℕ) (hl : l.length ≤ 2) :
    l = [] ∨ ∃ a b : ℕ, a ∈ l ∧ b ∈ l ∧ ∀ u ∈ l, u = a ∨ u = b := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, x, by simp, by simp, by simp⟩
  · exact Or.inr ⟨x, y, by simp, by simp, by simp⟩
  · simp at hl

-- Below the output and above every AND gate, all gates reached are false on the rejected inputs.
theorem top_qf (C : Circuit) (n : ℕ) (A : Finset ℕ) (R : (Fin n → Bool) → Prop)
    (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (o : ℕ) (hrej : ∀ q : Fin n → Bool, R q → val C n q (n + o) = false) :
    ∀ g : ℕ, InS C n o g → (∀ i ∈ A, ¬ Relation.TransGen (Rd C n) i g) →
      ∀ q : Fin n → Bool, R q → val C n q (n + g) = false := by
  intro g hS
  unfold InS at hS
  induction hS with
  | refl =>
    intro _
    exact hrej
  | @tail b c hab hbc ih =>
    intro hc q hq
    obtain ⟨⟨hlt, h, hg, hmem⟩, _⟩ := hbc
    have hbA : b ∉ A := fun hb => hc b hb (Relation.TransGen.single ⟨hlt, h, hg, hmem⟩)
    have hb' : ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) i b :=
      fun i hi ht => hc i hi (Relation.TransGen.tail ht ⟨hlt, h, hg, hmem⟩)
    have hop := gate_or C A hMono hA b h hg hbA
    have hvb := ih hb' q hq
    cases hv : val C n q (n + c) with
    | false => rfl
    | true =>
      have hvt : val C n q (n + b) = true :=
        (val_or C n q b h hg hop).mpr ⟨n + c, hmem, by omega, hv⟩
      rw [hvb] at hvt
      exact absurd hvt Bool.false_ne_true

-- An AND gate that is false on the rejected inputs and true somewhere reads a wire whose
-- single inputs are exactly one input: its centre.
theorem star_center (C : Circuit) (n : ℕ) (A : Finset ℕ) (adj : Fin n → Fin n → Prop)
    (R : (Fin n → Bool) → Prop)
    (hC4 : ∀ c1 c2 a b : Fin n, c1 ≠ c2 → a ≠ b → adj c1 a → adj c1 b → adj c2 a →
      adj c2 b → False)
    (hR : ∀ i i' : Fin n, ¬ adj i i' → ∃ q : Fin n → Bool, R q ∧ q i = true ∧ q i' = true)
    (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and)
    (q0 : Fin n → Bool) (hq0 : R q0)
    (hqf : ∀ q : Fin n → Bool, R q → val C n q (n + j) = false)
    (x0 : Fin n → Bool) (hx0 : val C n x0 (n + j) = true) :
    ∃ c : Fin n, ∃ w ∈ h.inputs, w < n + j ∧
      ∀ i : Fin n, val C n (e1 i) w = true ↔ i = c := by
  have hjA : j ∈ A := (hA j).mpr ⟨h, hg, hop⟩
  have hall := (val_and C n x0 j h hg hop).mp hx0
  have hlin : ∀ w ∈ h.inputs, w < n + j → Lin C n w :=
    fun w hw hlt => and_reads_lin C n A hMono hA h5 j h hg hjA w hw hlt
  have hsing : ∀ w ∈ h.inputs, ∃ i : Fin n, val C n (e1 i) w = true := by
    intro w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    obtain ⟨i, _, hi⟩ := (hlin w hw hlt x0).mp hv
    exact ⟨i, hi⟩
  by_contra hne
  have htwo : ∀ w ∈ h.inputs, ∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) w = true ∧
      val C n (e1 b) w = true := by
    intro w hw
    obtain ⟨i0, hi0⟩ := hsing w hw
    by_contra hno
    apply hne
    refine ⟨i0, w, hw, (hall w hw).1, fun i => ⟨fun hi => ?_, fun hi => by rw [hi]; exact hi0⟩⟩
    by_contra hii
    exact hno ⟨i, i0, hii, hi, hi0⟩
  have hadj : ∀ w ∈ h.inputs, ∀ w' ∈ h.inputs, (∀ u ∈ h.inputs, u = w ∨ u = w') →
      ∀ i i' : Fin n, val C n (e1 i) w = true → val C n (e1 i') w' = true → adj i i' := by
    intro w hw w' hw' hcov i i' hi hi'
    by_contra hna
    obtain ⟨q, hq, hqi, hqi'⟩ := hR i i' hna
    have hv : val C n q (n + j) = true := by
      refine (val_and C n q j h hg hop).mpr (fun u hu => ?_)
      rcases hcov u hu with hu' | hu'
      · subst hu'
        exact ⟨(hall u hu).1, (hlin u hu (hall u hu).1 q).mpr ⟨i, hqi, hi⟩⟩
      · subst hu'
        exact ⟨(hall u hu).1, (hlin u hu (hall u hu).1 q).mpr ⟨i', hqi', hi'⟩⟩
    rw [hqf q hq] at hv
    exact absurd hv Bool.false_ne_true
  rcases list_two h.inputs (hMono h (List.mem_of_getElem? hg)).2 with hnil | ⟨a, b, ha, hb, hcov⟩
  · have hv : val C n q0 (n + j) = true := by
      refine (val_and C n q0 j h hg hop).mpr (fun u hu => ?_)
      rw [hnil] at hu
      simp at hu
    rw [hqf q0 hq0] at hv
    exact absurd hv Bool.false_ne_true
  · obtain ⟨i1, i2, h12, hi1, hi2⟩ := htwo a ha
    obtain ⟨j1, j2, hj12, hj1, hj2⟩ := htwo b hb
    exact hC4 i1 i2 j1 j2 h12 hj12 (hadj a ha b hb hcov i1 j1 hi1 hj1)
      (hadj a ha b hb hcov i1 j2 hi1 hj2) (hadj a ha b hb hcov i2 j1 hi2 hj1)
      (hadj a ha b hb hcov i2 j2 hi2 hj2)

-- A pair (centre, leaf) accepted by a star AND gate is charged to a read position.
theorem edge_pair (C : Circuit) (n : ℕ) (A : Finset ℕ) (adj : Fin n → Fin n → Prop)
    (R : (Fin n → Bool) → Prop)
    (hirr : ∀ i : Fin n, ¬ adj i i)
    (hR : ∀ i i' : Fin n, ¬ adj i i' → ∃ q : Fin n → Bool, R q ∧ q i = true ∧ q i' = true)
    (hMono : Monotone2 C)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i)
    (o j : ℕ) (h : Gate) (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and)
    (hS : InS C n o j)
    (hqf : ∀ q : Fin n → Bool, R q → val C n q (n + j) = false)
    (c : Fin n) (w1 : ℕ) (hw1 : w1 ∈ h.inputs) (hlt1 : w1 < n + j)
    (hiff1 : ∀ i : Fin n, val C n (e1 i) w1 = true ↔ i = c)
    (t : Fin n) (hadj : adj c t)
    (hx : val C n (e2 c t) (n + j) = true) :
    ∃ g w : ℕ, InS C n o g ∧
      (∃ h' : Gate, C.gates[g]? = some h' ∧ w ∈ h'.inputs ∧ w < n + g) ∧
      (∀ i : Fin n, val C n (e1 i) w = true ↔ i = t) ∧
      (g = j ∨ (g ∉ A ∧
        (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + g) = true ∧
          val C n (e1 b) (n + g) = true) ∧
        (∀ i : Fin n, val C n (e1 i) (n + g) = true → adj c i))) := by
  have hjA : j ∈ A := (hA j).mpr ⟨h, hg, hop⟩
  have hall := (val_and C n _ j h hg hop).mp hx
  have hlin : ∀ w ∈ h.inputs, w < n + j → Lin C n w :=
    fun w hw hlt => and_reads_lin C n A hMono hA h5 j h hg hjA w hw hlt
  have hct : c ≠ t := fun hEq => hirr t (hEq ▸ hadj)
  have hw0 : ∃ w0 ∈ h.inputs, val C n (e1 t) w0 = true := by
    by_contra hno
    have hc : val C n (e1 c) (n + j) = true := by
      refine (val_and C n _ j h hg hop).mpr (fun w hw => ?_)
      obtain ⟨hlt, hv⟩ := hall w hw
      obtain ⟨i, hi, hiv⟩ := (hlin w hw hlt _).mp hv
      have hi' : i = c ∨ i = t := by simpa [e2] using hi
      rcases hi' with hi' | hi'
      · rw [hi'] at hiv
        exact ⟨hlt, hiv⟩
      · rw [hi'] at hiv
        exact absurd ⟨w, hw, hiv⟩ hno
    obtain ⟨q, hq, hqc, _⟩ := hR c c (hirr c)
    have hv := val_mono C n hMono (e1 c) q (fun k hk => by
      have hk' : k = c := by simpa [e1] using hk
      rw [hk']
      exact hqc) (n + j) hc
    rw [hqf q hq] at hv
    exact absurd hv Bool.false_ne_true
  obtain ⟨w0, hw0, hv0⟩ := hw0
  obtain ⟨hlt0, _⟩ := hall w0 hw0
  by_cases hs : ∀ i : Fin n, val C n (e1 i) w0 = true → i = t
  · exact ⟨j, w0, hS, ⟨h, hg, hw0, hlt0⟩,
      fun i => ⟨hs i, fun hi => by rw [hi]; exact hv0⟩, Or.inl rfl⟩
  · push Not at hs
    obtain ⟨t2, ht2v, ht2⟩ := hs
    have hwn : ¬ w0 < n := by
      intro hwn
      have a1 := input_e1 C n w0 hwn t hv0
      have a2 := input_e1 C n w0 hwn t2 ht2v
      exact ht2 (a2.symm.trans a1)
    obtain ⟨k, rfl⟩ : ∃ k, w0 = n + k := ⟨w0 - n, by omega⟩
    have hkj : k < j := by omega
    have hlowk : Low C n A k := and_reads_low C n A h5 j h hg hjA k hw0 hkj
    have hne01 : n + k ≠ w1 := by
      intro heq
      rw [← heq] at hiff1
      exact hct ((hiff1 t).mp hv0).symm
    have hmem : ∀ w ∈ h.inputs, w = n + k ∨ w = w1 :=
      two_mem h.inputs (hMono h (List.mem_of_getElem? hg)).2 (n + k) w1 hw0 hw1 hne01
    have hadjk : ∀ i : Fin n, val C n (e1 i) (n + k) = true → adj c i := by
      intro i hi
      by_contra hna
      obtain ⟨q, hq, hqc, hqi⟩ := hR c i hna
      have hv : val C n q (n + j) = true := by
        refine (val_and C n _ j h hg hop).mpr (fun w hw => ?_)
        rcases hmem w hw with hww | hww
        · rw [hww]
          exact ⟨hlt0, (hlin _ hw0 hlt0 _).mpr ⟨i, hqi, hi⟩⟩
        · rw [hww]
          exact ⟨hlt1, (hlin _ hw1 hlt1 _).mpr ⟨c, hqc, (hiff1 _).mpr rfl⟩⟩
      rw [hqf q hq] at hv
      exact absurd hv Bool.false_ne_true
    have hsub : Subst C n k :=
      ⟨⟨_, hv0⟩, fun ⟨t0, ht0⟩ => ht2 (((ht0 t2).mp ht2v).trans ((ht0 t).mp hv0).symm)⟩
    have hSk : InS C n o k := hS.tail ⟨⟨hkj, h, hg, hw0⟩, hsub⟩
    obtain ⟨g, w, hSg, hgA, hrd, hiff, hab, hadjg⟩ :=
      leaf C n A hMono hA adj o c t k hSk hlowk hadjk hv0 ⟨t2, ht2, ht2v⟩
    exact ⟨g, w, hSg, hrd, hiff, Or.inr ⟨hgA, hab, hadjg⟩⟩

-- The count: the pairs of E, the star AND gates and the gates reached are paid by read positions.
theorem main_thm (n : ℕ) (adj : Fin n → Fin n → Prop) (R : (Fin n → Bool) → Prop)
    (C : Circuit) (A : Finset ℕ) (E : Finset (Fin n × Fin n))
    (hirr : ∀ i : Fin n, ¬ adj i i)
    (hC4 : ∀ c1 c2 a b : Fin n, c1 ≠ c2 → a ≠ b → adj c1 a → adj c1 b → adj c2 a →
      adj c2 b → False)
    (hR : ∀ i i' : Fin n, ¬ adj i i' → ∃ q : Fin n → Bool, R q ∧ q i = true ∧ q i' = true)
    (hMono : Monotone2 C)
    (hE : ∀ e ∈ E, adj e.1 e.2 ∧ adj e.2 e.1)
    (hEanti : ∀ e ∈ E, ∀ e' ∈ E, e.1 = e'.2 → e.2 = e'.1 → False)
    (hacc : ∀ e ∈ E, val C n (e2 e.1 e.2) C.output = true)
    (hrej : ∀ q : Fin n → Bool, R q → val C n q C.output = false)
    (hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and)
    (h5 : ∀ j ∈ A, ∀ i ∈ A, ¬ Relation.TransGen (Rd C n) j i) :
    ∃ K : Finset (Fin n), (∀ e ∈ E, e.1 ∈ K ∨ e.2 ∈ K) ∧ E.card + K.card ≤ C.size + 1 := by
  classical
  by_cases hE0 : E = ∅
  · refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      simp at he
    · rw [hE0]
      simp
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE0
    obtain ⟨q0, hq0, _, _⟩ := hR e0.1 e0.1 (hirr _)
    have hnosingle : ∀ w : ℕ, (∀ q : Fin n → Bool, R q → val C n q w = false) →
        ∀ i : Fin n, val C n (e1 i) w ≠ true := by
      intro w hw i hi
      obtain ⟨q, hq, hqi, _⟩ := hR i i (hirr i)
      have hv := val_mono C n hMono (e1 i) q (fun k hk => by
        have hk' : k = i := by simpa [e1] using hk
        rw [hk']
        exact hqi) w hi
      rw [hw q hq] at hv
      exact absurd hv Bool.false_ne_true
    have hout : ¬ C.output < n := by
      intro hlt
      refine hnosingle C.output hrej ⟨C.output, hlt⟩ ?_
      rw [val_input C n _ _ hlt]
      simp [e1]
    obtain ⟨o, ho⟩ : ∃ o, C.output = n + o := ⟨C.output - n, by omega⟩
    rw [ho] at hacc hrej
    have hx0 : val C n (e2 e0.1 e0.2) (n + o) = true := hacc e0 he0
    have hVo : ∀ i : Fin n, val C n (e1 i) (n + o) ≠ true := hnosingle (n + o) hrej
    have hsubo : Subst C n o := ⟨⟨_, hx0⟩, fun ⟨t, ht⟩ => hVo t ((ht t).mpr rfl)⟩
    have hSsub : ∀ g, InS C n o g → Subst C n g := by
      intro g hg
      rcases Relation.ReflTransGen.cases_tail hg with heq | ⟨p, _, hr⟩
      · rw [heq]; exact hsubo
      · exact hr.2
    have hSgate : ∀ g, InS C n o g → ∃ h : Gate, C.gates[g]? = some h := by
      intro g hg
      obtain ⟨⟨x, hx⟩, _⟩ := hSsub g hg
      cases hgg : C.gates[g]? with
      | none =>
        rw [val_none C n x g hgg] at hx
        simp at hx
      | some h => exact ⟨h, rfl⟩
    let S : Finset ℕ := (Finset.range C.size).filter (fun g => InS C n o g)
    have hSmem : ∀ g, g ∈ S ↔ InS C n o g := by
      intro g
      simp only [S, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      intro hg
      obtain ⟨h, hh⟩ := hSgate g hg
      exact (List.getElem?_eq_some_iff.mp hh).1
    let rd : ℕ → Finset ℕ := fun g =>
      (Finset.range (n + g)).filter (fun w => ∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs)
    have hrd : ∀ g, (rd g).card ≤ 2 := by
      intro g
      cases hgg : C.gates[g]? with
      | none =>
        have : rd g = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro w hw
          simp only [rd, Finset.mem_filter, hgg] at hw
          obtain ⟨_, h, hh, _⟩ := hw
          exact absurd hh (by simp)
        rw [this]; simp
      | some h =>
        have hsub : rd g ⊆ h.inputs.toFinset := by
          intro w hw
          simp only [rd, Finset.mem_filter, hgg] at hw
          obtain ⟨_, h', hh, hw'⟩ := hw
          rw [← Option.some.inj hh] at hw'
          exact List.mem_toFinset.mpr hw'
        calc (rd g).card ≤ h.inputs.toFinset.card := Finset.card_le_card hsub
          _ ≤ h.inputs.length := List.toFinset_card_le _
          _ ≤ 2 := (hMono h (List.mem_of_getElem? hgg)).2
    let Z : Finset (ℕ × ℕ) := S.biUnion (fun g => (rd g).image (fun w => (g, w)))
    have hZcard : Z.card ≤ 2 * S.card := by
      calc Z.card ≤ ∑ g ∈ S, ((rd g).image (fun w => (g, w))).card := Finset.card_biUnion_le
        _ ≤ ∑ g ∈ S, 2 := Finset.sum_le_sum (fun g _ => Finset.card_image_le.trans (hrd g))
        _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hZmem : ∀ g w, InS C n o g →
        (∃ h : Gate, C.gates[g]? = some h ∧ w ∈ h.inputs ∧ w < n + g) → (g, w) ∈ Z := by
      intro g w hg hr
      obtain ⟨h, hh, hw, hlt⟩ := hr
      refine Finset.mem_biUnion.mpr ⟨g, (hSmem g).mpr hg, Finset.mem_image.mpr ⟨w, ?_, rfl⟩⟩
      simp only [rd, Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, h, hh, hw⟩
    have hqfA : ∀ j ∈ A, InS C n o j → ∀ q : Fin n → Bool, R q →
        val C n q (n + j) = false :=
      fun j hjA hjS => top_qf C n A R hMono hA o hrej j hjS (fun i hi => h5 i hi j hjA)
    have hcenEx : ∀ j : ℕ, ∃ c : Fin n, j ∈ A → InS C n o j →
        ∃ h : Gate, C.gates[j]? = some h ∧ ∃ w ∈ h.inputs, w < n + j ∧
          ∀ i : Fin n, val C n (e1 i) w = true ↔ i = c := by
      intro j
      by_cases hj : j ∈ A ∧ InS C n o j
      · obtain ⟨hjA, hjS⟩ := hj
        obtain ⟨h, hg, hop⟩ := (hA j).mp hjA
        obtain ⟨⟨x, hx⟩, _⟩ := hSsub j hjS
        obtain ⟨c, w, hw, hlt, hiff⟩ := star_center C n A adj R hC4 hR hMono hA h5 j h hg hop
          q0 hq0 (hqfA j hjA hjS) x hx
        exact ⟨c, fun _ _ => ⟨h, hg, w, hw, hlt, hiff⟩⟩
      · exact ⟨e0.1, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
    choose cen hcen using hcenEx
    have hcov : ∀ e ∈ E, ∃ j ∈ A, InS C n o j ∧ val C n (e2 e.1 e.2) (n + j) = true ∧
        (cen j = e.1 ∨ cen j = e.2) := by
      intro e he
      obtain ⟨j, hjA, hjS, hjx⟩ :=
        upper C n A hMono hA o (e2 e.1 e.2) o Relation.ReflTransGen.refl hVo (hacc e he)
      refine ⟨j, hjA, hjS, hjx, ?_⟩
      obtain ⟨h, hg, w, hw, hlt, hiff⟩ := hcen j hjA hjS
      obtain ⟨h', hg', hop⟩ := (hA j).mp hjA
      have hh : h' = h := Option.some.inj (hg'.symm.trans hg)
      rw [hh] at hop
      obtain ⟨_, hv⟩ := (val_and C n _ j h hg hop).mp hjx w hw
      have hl := and_reads_lin C n A hMono hA h5 j h hg hjA w hw hlt
      obtain ⟨i, hi, hiv⟩ := (hl _).mp hv
      have hic : i = cen j := (hiff i).mp hiv
      have hi' : i = e.1 ∨ i = e.2 := by simpa [e2] using hi
      rw [hic] at hi'
      exact hi'
    let P2 : ℕ × ℕ → Prop := fun z =>
      z.1 ∈ A ∧ ∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = cen z.1
    let Z1 : Finset (ℕ × ℕ) := Z.filter (fun z => ¬ Sing C n z.2)
    let Zs : Finset (ℕ × ℕ) := Z.filter (fun z => Sing C n z.2)
    let Z2 : Finset (ℕ × ℕ) := Zs.filter (fun z => P2 z)
    let Z3 : Finset (ℕ × ℕ) := Zs.filter (fun z => ¬ P2 z)
    have hsplit1 : Zs.card + Z1.card = Z.card :=
      Finset.card_filter_add_card_filter_not (s := Z) (fun z : ℕ × ℕ => Sing C n z.2)
    have hsplit2 : Z2.card + Z3.card = Zs.card :=
      Finset.card_filter_add_card_filter_not (s := Zs) (fun z : ℕ × ℕ => P2 z)
    have hoS : o ∈ S := (hSmem o).mpr Relation.ReflTransGen.refl
    have hb1 : (S.erase o).card ≤ Z1.card := by
      apply card_le_of_rel _ _ (fun k z => z.2 = n + k)
      · intro k hk
        obtain ⟨hko, hkS⟩ := Finset.mem_erase.mp hk
        have hkS' := (hSmem k).mp hkS
        rcases Relation.ReflTransGen.cases_tail hkS' with heq | ⟨p, hp, hr⟩
        · exact absurd heq hko
        · obtain ⟨⟨hlt, h, hh, hmem⟩, hsub⟩ := hr
          refine ⟨(p, n + k), Finset.mem_filter.mpr ⟨hZmem p (n + k) hp ⟨h, hh, hmem, by omega⟩, hsub.2⟩, rfl⟩
      · intro k1 _ k2 _ z hz1 hz2
        have : n + k1 = n + k2 := hz1.symm.trans hz2
        omega
    have hb2 : (A ∩ S).card ≤ Z2.card := by
      apply card_le_of_rel _ _ (fun j z => z.1 = j)
      · intro j hj
        obtain ⟨hjA, hjS⟩ := Finset.mem_inter.mp hj
        have hjS' := (hSmem j).mp hjS
        obtain ⟨h, hg, w, hw, hlt, hiff⟩ := hcen j hjA hjS'
        refine ⟨(j, w), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZmem j w hjS' ⟨h, hg, hw, hlt⟩, ⟨cen j, hiff⟩⟩, hjA, hiff⟩
      · intro j1 _ j2 _ z hz1 hz2
        exact hz1.symm.trans hz2
    have hb3 : E.card ≤ Z3.card := by
      apply card_le_of_rel _ _ (fun (e : Fin n × Fin n) (z : ℕ × ℕ) => ∃ c t : Fin n,
        (e = (c, t) ∨ e = (t, c)) ∧ (∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = t) ∧
        ((z.1 ∈ A ∧ cen z.1 = c) ∨ (z.1 ∉ A ∧
          (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + z.1) = true ∧
            val C n (e1 b) (n + z.1) = true) ∧
          (∀ i : Fin n, val C n (e1 i) (n + z.1) = true → adj c i))))
      · intro e he
        obtain ⟨j, hjA, hjS, hjx, hcj⟩ := hcov e he
        obtain ⟨h, hg, w1, hw1, hlt1, hiff1⟩ := hcen j hjA hjS
        obtain ⟨h', hg', hop⟩ := (hA j).mp hjA
        have hh : h' = h := Option.some.inj (hg'.symm.trans hg)
        rw [hh] at hop
        have key : ∀ t : Fin n, adj (cen j) t → val C n (e2 (cen j) t) (n + j) = true →
            ∃ z ∈ Z3, (∀ i : Fin n, val C n (e1 i) z.2 = true ↔ i = t) ∧
              ((z.1 ∈ A ∧ cen z.1 = cen j) ∨ (z.1 ∉ A ∧
                (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + z.1) = true ∧
                  val C n (e1 b) (n + z.1) = true) ∧
                (∀ i : Fin n, val C n (e1 i) (n + z.1) = true → adj (cen j) i))) := by
          intro t hadjct hval
          obtain ⟨g, w, hSg, hrdw, hiff, hor⟩ :=
            edge_pair C n A adj R hirr hR hMono hA h5 o j h hg hop hjS (hqfA j hjA hjS)
              (cen j) w1 hw1 hlt1 hiff1 t hadjct hval
          have hor' : (g ∈ A ∧ cen g = cen j) ∨ (g ∉ A ∧
              (∃ a b : Fin n, a ≠ b ∧ val C n (e1 a) (n + g) = true ∧
                val C n (e1 b) (n + g) = true) ∧
              (∀ i : Fin n, val C n (e1 i) (n + g) = true → adj (cen j) i)) := by
            rcases hor with hgj | hr
            · left
              rw [hgj]
              exact ⟨hjA, rfl⟩
            · right
              exact hr
          refine ⟨(g, w), ?_, hiff, hor'⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hZmem g w hSg hrdw, ⟨t, hiff⟩⟩, ?_⟩
          rintro ⟨hgA, hcg⟩
          rcases hor' with ⟨_, hc'⟩ | ⟨hng, _⟩
          · have htc : t = cen g := (hcg t).mp ((hiff t).mpr rfl)
            rw [hc'] at htc
            rw [← htc] at hadjct
            exact hirr t hadjct
          · exact hng hgA
        rcases hcj with hc | hc
        · have hadj1 : adj (cen j) e.2 := by
            rw [hc]
            exact (hE e he).1
          have hjx' : val C n (e2 (cen j) e.2) (n + j) = true := by
            rw [hc]
            exact hjx
          obtain ⟨z, hz, hiff, hor⟩ := key e.2 hadj1 hjx'
          exact ⟨z, hz, cen j, e.2, Or.inl (by rw [hc]), hiff, hor⟩
        · have hadj2 : adj (cen j) e.1 := by
            rw [hc]
            exact (hE e he).2
          have hswap : e2 e.2 e.1 = e2 e.1 e.2 := by
            funext i
            simp [e2, or_comm]
          have hjx' : val C n (e2 (cen j) e.1) (n + j) = true := by
            rw [hc, hswap]
            exact hjx
          obtain ⟨z, hz, hiff, hor⟩ := key e.1 hadj2 hjx'
          exact ⟨z, hz, cen j, e.1, Or.inr (by rw [hc]), hiff, hor⟩
      · rintro ea hea eb heb z ⟨c1, t1, hf1, hi1, hor1⟩ ⟨c2, t2, hf2, hi2, hor2⟩
        have ht : t1 = t2 := (hi2 t1).mp ((hi1 t1).mpr rfl)
        have hc : c1 = c2 := by
          rcases hor1 with ⟨hzA1, hc1⟩ | ⟨hzA1, ⟨a, b, hab, hva, hvb⟩, hadj1⟩
          · rcases hor2 with ⟨_, hc2⟩ | ⟨hzA2, _, _⟩
            · exact hc1.symm.trans hc2
            · exact absurd hzA1 hzA2
          · rcases hor2 with ⟨hzA2, _⟩ | ⟨_, _, hadj2⟩
            · exact absurd hzA2 hzA1
            · by_contra hne
              exact hC4 c1 c2 a b hne hab (hadj1 a hva) (hadj1 b hvb) (hadj2 a hva)
                (hadj2 b hvb)
        subst ht
        subst hc
        rcases hf1 with hf1 | hf1 <;> rcases hf2 with hf2 | hf2
        · rw [hf1, hf2]
        · exact (hEanti ea hea eb heb (by rw [hf1, hf2]) (by rw [hf1, hf2])).elim
        · exact (hEanti ea hea eb heb (by rw [hf1, hf2]) (by rw [hf1, hf2])).elim
        · rw [hf1, hf2]
    refine ⟨(A ∩ S).image cen, ?_, ?_⟩
    · intro e he
      obtain ⟨j, hjA, hjS, _, hcj⟩ := hcov e he
      have hjK : cen j ∈ (A ∩ S).image cen :=
        Finset.mem_image.mpr ⟨j, Finset.mem_inter.mpr ⟨hjA, (hSmem j).mpr hjS⟩, rfl⟩
      rcases hcj with hc | hc
      · left
        rw [← hc]
        exact hjK
      · right
        rw [← hc]
        exact hjK
    · have himg : ((A ∩ S).image cen).card ≤ (A ∩ S).card := Finset.card_image_le
      have hSle : S.card ≤ C.size := by
        have h := Finset.card_le_card
          (Finset.filter_subset (fun g => InS C n o g) (Finset.range C.size))
        rwa [Finset.card_range] at h
      have hero : (S.erase o).card = S.card - 1 := Finset.card_erase_of_mem hoS
      have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨o, hoS⟩
      omega

-- The cone lists of the definitions root, read through the reads of the gates.
def cn (n : ℕ) (gs : List Gate) (j : ℕ) : List ℕ :=
  (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j []

theorem cones_fold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cn_snoc_old (n : ℕ) (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    cn n (gs ++ [g]) j = cn n gs j := by
  unfold cn
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [PEqualNP.EdgeOwnership.coneStep]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [cones_fold_length]; simpa using hj)]

theorem cn_snoc_new (n : ℕ) (gs : List Gate) (g : Gate) :
    cn n (gs ++ [g]) gs.length =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
        (fun w => (w - n) :: cn n gs (w - n)) := by
  unfold cn
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [PEqualNP.EdgeOwnership.coneStep]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [cones_fold_length]; simp)]
  simp [cones_fold_length]

theorem cn_mem (n : ℕ) (gs : List Gate) (j : ℕ) (h : Gate) (hg : gs[j]? = some h) (i : ℕ) :
    i ∈ cn n gs j ↔
      ∃ w ∈ h.inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ cn n gs (w - n)) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hg
  | append_singleton gs g0 ih =>
    obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hg
    simp only [List.length_append, List.length_cons, List.length_nil] at hjlt
    have hold : ∀ w, n ≤ w → w < n + j → cn n (gs ++ [g0]) (w - n) = cn n gs (w - n) :=
      fun w _ _ => cn_snoc_old n gs g0 (w - n) (by omega)
    by_cases hjl : j = gs.length
    · subst hjl
      have hgg : g0 = h := by
        simpa using hg
      subst hgg
      rw [cn_snoc_new]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2]; exact h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, ⟨hw, h1, h2⟩, by rw [hold w h1 h2] at h3; exact h3⟩
    · have hj' : j < gs.length := by omega
      have hg' : gs[j]? = some h := by
        rw [List.getElem?_append_left hj'] at hg
        exact hg
      rw [cn_snoc_old n gs g0 j hj', ih hg']
      constructor
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2]; exact h3⟩
      · rintro ⟨w, hw, h1, h2, h3⟩
        exact ⟨w, hw, h1, h2, by rw [hold w h1 h2] at h3; exact h3⟩

theorem rd_cone (C : Circuit) (n : ℕ) (j k : ℕ) (hr : Rd C n j k) :
    PEqualNP.EdgeOwnership.InCone n C k j ∧
      ∀ i, PEqualNP.EdgeOwnership.InCone n C i k → PEqualNP.EdgeOwnership.InCone n C i j := by
  obtain ⟨hlt, h, hg, hmem⟩ := hr
  constructor
  · exact (cn_mem n C.gates j h hg k).mpr ⟨n + k, hmem, by omega, by omega, Or.inl (by omega)⟩
  · intro i hi
    refine (cn_mem n C.gates j h hg i).mpr ⟨n + k, hmem, by omega, by omega, Or.inr ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact hi

theorem tg_cone (C : Circuit) (n : ℕ) (j i : ℕ) (ht : Relation.TransGen (Rd C n) j i) :
    PEqualNP.EdgeOwnership.InCone n C i j := by
  induction ht using Relation.TransGen.head_induction_on with
  | single h => exact (rd_cone C n _ _ h).1
  | head h' _ ih => exact (rd_cone C n _ _ h').2 _ ih

theorem gateAt_and (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (hop : g.op = GateOp.and) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem?_getD, hg]
  exact hop

-- The plane of order 3: points are the inputs 0..12, lines the inputs 13..25.
def pt (p : Fin 13) : Fin 26 := ⟨p.val, by have := p.isLt; omega⟩

def ln (l : Fin 13) : Fin 26 := ⟨13 + l.val, by have := l.isLt; omega⟩

theorem pt_ne_ln (p l : Fin 13) : pt p ≠ ln l := by
  intro h
  have h2 := congrArg Fin.val h
  simp only [pt, ln] at h2
  have := p.isLt
  omega

theorem pt_inj (p p' : Fin 13) (h : pt p = pt p') : p = p' := by
  have h2 := congrArg Fin.val h
  simp only [pt] at h2
  exact Fin.ext h2

theorem ln_inj (l l' : Fin 13) (h : ln l = ln l') : l = l' := by
  have h2 := congrArg Fin.val h
  simp only [ln] at h2
  exact Fin.ext (by omega)

theorem cases26 (i : Fin 26) : (∃ p : Fin 13, i = pt p) ∨ (∃ l : Fin 13, i = ln l) := by
  by_cases h : i.val < 13
  · exact Or.inl ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · have := i.isLt
    refine Or.inr ⟨⟨i.val - 13, by omega⟩, Fin.ext ?_⟩
    simp only [ln]
    omega

def adj (i j : Fin 26) : Prop :=
  ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
    ((i = pt p ∧ j = ln l) ∨ (i = ln l ∧ j = pt p))

theorem adj_pl (p l : Fin 13) :
    adj (pt p) (ln l) ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  constructor
  · rintro ⟨a, b, hab, (⟨h1, h2⟩ | ⟨h1, _⟩)⟩
    · rw [pt_inj _ _ h1, ln_inj _ _ h2]
      exact hab
    · exact absurd h1 (pt_ne_ln p b)
  · intro h
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

theorem adj_lp (l p : Fin 13) :
    adj (ln l) (pt p) ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  constructor
  · rintro ⟨a, b, hab, (⟨h1, _⟩ | ⟨h1, h2⟩)⟩
    · exact absurd h1.symm (pt_ne_ln a l)
    · rw [pt_inj _ _ h2, ln_inj _ _ h1]
      exact hab
  · intro h
    exact ⟨p, l, h, Or.inr ⟨rfl, rfl⟩⟩

theorem adj_pp (p p' : Fin 13) : ¬ adj (pt p) (pt p') := by
  rintro ⟨a, b, _, (⟨_, h2⟩ | ⟨h1, _⟩)⟩
  · exact pt_ne_ln p' b h2
  · exact pt_ne_ln p b h1

theorem adj_ll (l l' : Fin 13) : ¬ adj (ln l) (ln l') := by
  rintro ⟨a, b, _, (⟨h1, _⟩ | ⟨_, h2⟩)⟩
  · exact pt_ne_ln a l h1.symm
  · exact pt_ne_ln a l' h2.symm

-- Two points lie on at most one common line (checked by cases).
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem quad_aux : ∀ p1 l1 : Fin 13, p1 - l1 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    ∀ l2 : Fin 13, p1 - l2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    ∀ p2 : Fin 13, p2 - l1 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
    p2 - l2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → p1 = p2 ∨ l1 = l2 := by
  decide

theorem adj_irr (i : Fin 26) : ¬ adj i i := by
  rcases cases26 i with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · exact adj_pp p p
  · exact adj_ll l l

theorem adj_c4 (c1 c2 a b : Fin 26) (hc : c1 ≠ c2) (hab : a ≠ b) (h1 : adj c1 a)
    (h2 : adj c1 b) (h3 : adj c2 a) (h4 : adj c2 b) : False := by
  rcases cases26 c1 with ⟨p1, rfl⟩ | ⟨l1, rfl⟩
  · rcases cases26 a with ⟨pa, rfl⟩ | ⟨l1, rfl⟩
    · exact adj_pp _ _ h1
    rcases cases26 b with ⟨pb, rfl⟩ | ⟨l2, rfl⟩
    · exact adj_pp _ _ h2
    rcases cases26 c2 with ⟨p2, rfl⟩ | ⟨lc, rfl⟩
    · rcases quad_aux p1 l1 ((adj_pl _ _).mp h1) l2 ((adj_pl _ _).mp h2) p2
        ((adj_pl _ _).mp h3) ((adj_pl _ _).mp h4) with h | h
      · exact hc (by rw [h])
      · exact hab (by rw [h])
    · exact adj_ll _ _ h3
  · rcases cases26 a with ⟨p1, rfl⟩ | ⟨la, rfl⟩
    swap
    · exact adj_ll _ _ h1
    rcases cases26 b with ⟨p2, rfl⟩ | ⟨lb, rfl⟩
    swap
    · exact adj_ll _ _ h2
    rcases cases26 c2 with ⟨pc, rfl⟩ | ⟨l2, rfl⟩
    · exact adj_pp _ _ h3
    · rcases quad_aux p1 l1 ((adj_lp _ _).mp h1) l2 ((adj_lp _ _).mp h3) p2
        ((adj_lp _ _).mp h2) ((adj_lp _ _).mp h4) with h | h
      · exact hab (by rw [h])
      · exact hc (by rw [h])

-- Quadrangles through two points, off two lines, through a point and off a line:
-- one table entry for each difference, moved by a translation.
def tpp (d : Fin 13) : Fin 13 × Fin 13 × Fin 13 × Fin 13 :=
  match d.val with
  | 0 => (0, 1, 2, 5)
  | 1 => (0, 1, 2, 5)
  | 2 => (0, 1, 2, 5)
  | 3 => (0, 2, 3, 4)
  | 4 => (0, 1, 4, 6)
  | 5 => (0, 1, 2, 5)
  | 6 => (0, 1, 2, 6)
  | 7 => (0, 1, 2, 7)
  | 8 => (0, 1, 4, 8)
  | 9 => (0, 2, 4, 9)
  | 10 => (0, 1, 5, 10)
  | 11 => (0, 1, 2, 11)
  | _ => (0, 1, 4, 12)

def tll (d : Fin 13) : Fin 13 × Fin 13 × Fin 13 × Fin 13 :=
  match d.val with
  | 0 => (2, 4, 5, 6)
  | 1 => (5, 6, 7, 11)
  | 2 => (4, 6, 7, 8)
  | 3 => (2, 5, 7, 8)
  | 4 => (2, 6, 8, 10)
  | 5 => (2, 4, 7, 11)
  | 6 => (4, 5, 8, 10)
  | 7 => (2, 4, 5, 6)
  | 8 => (2, 5, 6, 10)
  | 9 => (2, 4, 6, 8)
  | 10 => (2, 4, 5, 8)
  | 11 => (2, 4, 5, 6)
  | _ => (4, 5, 6, 10)

def tpl (d : Fin 13) : Fin 13 × Fin 13 × Fin 13 × Fin 13 :=
  match d.val with
  | 0 => (0, 1, 2, 5)
  | 1 => (0, 1, 2, 5)
  | 2 => (2, 4, 5, 6)
  | 3 => (0, 1, 2, 5)
  | 4 => (2, 4, 5, 6)
  | 5 => (2, 4, 5, 6)
  | 6 => (2, 4, 5, 6)
  | 7 => (2, 4, 7, 8)
  | 8 => (2, 4, 5, 8)
  | 9 => (0, 1, 2, 5)
  | 10 => (2, 5, 6, 10)
  | 11 => (2, 4, 6, 11)
  | _ => (2, 4, 5, 12)

def tr (q : Fin 13 × Fin 13 × Fin 13 × Fin 13) (s : Fin 13) : Finset (Fin 13) :=
  {q.1 + s, q.2.1 + s, q.2.2.1 + s, q.2.2.2 + s}

def Qpp (p p' : Fin 13) : Finset (Fin 13) := tr (tpp (p' - p)) p

def Qll (l l' : Fin 13) : Finset (Fin 13) := tr (tll (l' - l)) l

def Qpl (p l : Fin 13) : Finset (Fin 13) := tr (tpl (p - l)) l

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem qpp_ok : ∀ p p' : Fin 13, ((Qpp p p').card = 4 ∧
    ∀ x5 : Fin 13, ((Qpp p p').filter
      (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qpp p p' ∧ p' ∈ Qpp p p' := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem qll_ok : ∀ l l' : Fin 13, ((Qll l l').card = 4 ∧
    ∀ x5 : Fin 13, ((Qll l l').filter
      (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    (∀ x7 ∈ Qll l l', x7 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) ∧
    (∀ x7 ∈ Qll l l', x7 - l' ∉ ({0, 1, 3, 9} : Finset (Fin 13))) := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem qpl_ok : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    ((Qpl p l).card = 4 ∧
    ∀ x5 : Fin 13, ((Qpl p l).filter
      (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qpl p l ∧ (∀ x7 ∈ Qpl p l, x7 - l ∉ ({0, 1, 3, 9} : Finset (Fin 13))) := by
  decide

-- An input on 26 wires from its point half and its line half.
def glue (f g : Fin 13 → Bool) : Fin 26 → Bool :=
  fun i => if h : i.val < 13 then f ⟨i.val, h⟩ else g ⟨i.val - 13, by have := i.isLt; omega⟩

theorem glue_list (f g : Fin 13 → Bool) :
    List.ofFn f ++ List.ofFn g = List.ofFn (glue f g) := by
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]
  · intro k h1 h2
    by_cases hk : k < 13
    · rw [List.getElem_append_left (by rw [List.length_ofFn]; exact hk), List.getElem_ofFn,
        List.getElem_ofFn]
      simp only [glue, dite_eq_left hk]
    · rw [List.getElem_append_right (by rw [List.length_ofFn]; omega), List.getElem_ofFn,
        List.getElem_ofFn]
      simp only [glue, dite_eq_right hk, List.length_ofFn]

theorem glue_pt (f g : Fin 13 → Bool) (p : Fin 13) : glue f g (pt p) = f p := by
  simp [glue, pt]

theorem glue_ln (f g : Fin 13 → Bool) (l : Fin 13) : glue f g (ln l) = g l := by
  simp [glue, ln]

theorem e2_glue (p l : Fin 13) :
    glue (fun x6 => decide (x6 = p)) (fun x6 => decide (x6 = l)) = e2 (pt p) (ln l) := by
  funext i
  rcases cases26 i with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [glue_pt]
    simp only [e2]
    by_cases h : a = p
    · subst h
      simp
    · have h1 : pt a ≠ pt p := fun hh => h (pt_inj _ _ hh)
      have h2 : pt a ≠ ln l := pt_ne_ln a l
      simp [h, h1, h2]
  · rw [glue_ln]
    simp only [e2]
    by_cases h : b = l
    · subst h
      simp
    · have h1 : ln b ≠ ln l := fun hh => h (ln_inj _ _ hh)
      have h2 : ln b ≠ pt p := fun hh => pt_ne_ln p b hh.symm
      simp [h, h1, h2]

-- The rejected inputs: the quadrangle inputs.
def Rq (q : Fin 26 → Bool) : Prop :=
  ∃ Q : Finset (Fin 13), Q.card = 4 ∧
    (∀ x5 : Fin 13, (Q.filter
      (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    q = glue (fun x6 => decide (x6 ∈ Q))
      (fun x6 => decide (∀ x7 ∈ Q, x7 - x6 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

-- Every pair of inputs that is not an incident pair lies in a quadrangle input.
theorem rq_cover (i i' : Fin 26) (hna : ¬ adj i i') :
    ∃ q : Fin 26 → Bool, Rq q ∧ q i = true ∧ q i' = true := by
  rcases cases26 i with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;> rcases cases26 i' with ⟨p', rfl⟩ | ⟨l', rfl⟩
  · obtain ⟨hgood, hp, hp'⟩ := qpp_ok p p'
    refine ⟨_, ⟨Qpp p p', hgood.1, hgood.2, rfl⟩, ?_, ?_⟩
    · exact (glue_pt _ _ _).trans (decide_eq_true hp)
    · exact (glue_pt _ _ _).trans (decide_eq_true hp')
  · have hnd : p - l' ∉ ({0, 1, 3, 9} : Finset (Fin 13)) :=
      fun h => hna ((adj_pl p l').mpr h)
    obtain ⟨hgood, hp, hm⟩ := qpl_ok p l' hnd
    refine ⟨_, ⟨Qpl p l', hgood.1, hgood.2, rfl⟩, ?_, ?_⟩
    · exact (glue_pt _ _ _).trans (decide_eq_true hp)
    · exact (glue_ln _ _ _).trans (decide_eq_true hm)
  · have hnd : p' - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) :=
      fun h => hna ((adj_lp l p').mpr h)
    obtain ⟨hgood, hp, hm⟩ := qpl_ok p' l hnd
    refine ⟨_, ⟨Qpl p' l, hgood.1, hgood.2, rfl⟩, ?_, ?_⟩
    · exact (glue_ln _ _ _).trans (decide_eq_true hm)
    · exact (glue_pt _ _ _).trans (decide_eq_true hp)
  · obtain ⟨hgood, hm, hm'⟩ := qll_ok l l'
    refine ⟨_, ⟨Qll l l', hgood.1, hgood.2, rfl⟩, ?_, ?_⟩
    · exact (glue_ln _ _ _).trans (decide_eq_true hm)
    · exact (glue_ln _ _ _).trans (decide_eq_true hm')

-- The 52 incident pairs, as pairs of inputs (point first).
def E26 : Finset (Fin 26 × Fin 26) :=
  ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
    (fun e => e.1 - e.2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).image
    (fun e => (pt e.1, ln e.2))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem e13_card : ((Finset.univ : Finset (Fin 13 × Fin 13)).filter
    (fun e => e.1 - e.2 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 52 := by
  decide

theorem e26_card : E26.card = 52 := by
  unfold E26
  rw [Finset.card_image_of_injective, e13_card]
  intro e e' h
  have h1 := pt_inj _ _ (congrArg Prod.fst h)
  have h2 := ln_inj _ _ (congrArg Prod.snd h)
  exact Prod.ext h1 h2

theorem e26_mem (e : Fin 26 × Fin 26) (he : e ∈ E26) :
    ∃ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ e = (pt p, ln l) := by
  unfold E26 at he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact ⟨a.1, a.2, (Finset.mem_filter.mp ha).2, rfl⟩

theorem e26_diag (l : Fin 13) : (pt l, ln l) ∈ E26 := by
  unfold E26
  refine Finset.mem_image.mpr ⟨(l, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  simp

-- The 13 pairs (point l, line l) are disjoint, so a cover has at least 13 inputs.
theorem cover13 (K : Finset (Fin 26)) (hK : ∀ e ∈ E26, e.1 ∈ K ∨ e.2 ∈ K) :
    13 ≤ K.card := by
  classical
  have hinj : Function.Injective (fun l : Fin 13 => if pt l ∈ K then pt l else ln l) := by
    intro l l' h
    simp only at h
    by_cases h1 : pt l ∈ K <;> by_cases h2 : pt l' ∈ K
    · rw [ite_eq_left h1, ite_eq_left h2] at h
      exact pt_inj _ _ h
    · rw [ite_eq_left h1, ite_eq_right h2] at h
      exact absurd h (pt_ne_ln l l')
    · rw [ite_eq_right h1, ite_eq_left h2] at h
      exact absurd h.symm (pt_ne_ln l' l)
    · rw [ite_eq_right h1, ite_eq_right h2] at h
      exact ln_inj _ _ h
  have hsub : (Finset.univ : Finset (Fin 13)).image
      (fun l : Fin 13 => if pt l ∈ K then pt l else ln l) ⊆ K := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases h1 : pt l ∈ K
    · simp only [ite_eq_left h1]
      exact h1
    · simp only [ite_eq_right h1]
      rcases hK _ (e26_diag l) with h | h
      · exact absurd h h1
      · exact h
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
  exact hc

end PEqualNP.Outside.L_meta_1751_aux

theorem PEqualNP.Outside.L_meta_1751 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → ¬x3 x4 → (64 : ℕ) ≤ x4.size := by
  intro x1 x2 x3 C hMono _ hx2 hx3
  classical
  obtain ⟨hacc, hrej⟩ := hx2
  let A : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧
      g.op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hA : ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate,
      C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro j
    simp only [A, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    rintro ⟨g, hg, _⟩
    exact (List.getElem?_eq_some_iff.mp hg).1
  have h5 : ∀ j ∈ A, ∀ i ∈ A,
      ¬ Relation.TransGen (PEqualNP.Outside.L_meta_1751_aux.Rd C 26) j i := by
    intro j hj i hi ht
    obtain ⟨gj, hgj, hopj⟩ := (hA j).mp hj
    obtain ⟨gi, hgi, hopi⟩ := (hA i).mp hi
    exact hx3 ⟨i, j, PEqualNP.Outside.L_meta_1751_aux.gateAt_and C i gi hgi hopi,
      PEqualNP.Outside.L_meta_1751_aux.gateAt_and C j gj hgj hopj,
      PEqualNP.Outside.L_meta_1751_aux.tg_cone C 26 j i ht⟩
  have hE : ∀ e ∈ PEqualNP.Outside.L_meta_1751_aux.E26,
      PEqualNP.Outside.L_meta_1751_aux.adj e.1 e.2 ∧
        PEqualNP.Outside.L_meta_1751_aux.adj e.2 e.1 := by
    intro e he
    obtain ⟨p, l, hpl, rfl⟩ := PEqualNP.Outside.L_meta_1751_aux.e26_mem e he
    exact ⟨(PEqualNP.Outside.L_meta_1751_aux.adj_pl p l).mpr hpl,
      (PEqualNP.Outside.L_meta_1751_aux.adj_lp l p).mpr hpl⟩
  have hEanti : ∀ e ∈ PEqualNP.Outside.L_meta_1751_aux.E26,
      ∀ e' ∈ PEqualNP.Outside.L_meta_1751_aux.E26, e.1 = e'.2 → e.2 = e'.1 → False := by
    intro e he e' he' h1 _
    obtain ⟨p, l, _, rfl⟩ := PEqualNP.Outside.L_meta_1751_aux.e26_mem e he
    obtain ⟨p', l', _, rfl⟩ := PEqualNP.Outside.L_meta_1751_aux.e26_mem e' he'
    exact PEqualNP.Outside.L_meta_1751_aux.pt_ne_ln p l' h1
  have hacc' : ∀ e ∈ PEqualNP.Outside.L_meta_1751_aux.E26,
      PEqualNP.Outside.L_meta_1751_aux.val C 26
        (PEqualNP.Outside.L_meta_1751_aux.e2 e.1 e.2) C.output = true := by
    intro e he
    obtain ⟨p, l, hpl, rfl⟩ := PEqualNP.Outside.L_meta_1751_aux.e26_mem e he
    have h := hacc p l hpl
    rw [PEqualNP.Outside.L_meta_1751_aux.glue_list,
      PEqualNP.Outside.L_meta_1751_aux.e2_glue] at h
    exact h
  have hrej' : ∀ q : Fin 26 → Bool, PEqualNP.Outside.L_meta_1751_aux.Rq q →
      PEqualNP.Outside.L_meta_1751_aux.val C 26 q C.output = false := by
    rintro q ⟨Q, hQ4, hQ2, rfl⟩
    have h := hrej Q hQ4 hQ2
    rw [PEqualNP.Outside.L_meta_1751_aux.glue_list] at h
    exact h
  obtain ⟨K, hK, hcard⟩ := PEqualNP.Outside.L_meta_1751_aux.main_thm 26
    PEqualNP.Outside.L_meta_1751_aux.adj PEqualNP.Outside.L_meta_1751_aux.Rq C A
    PEqualNP.Outside.L_meta_1751_aux.E26 PEqualNP.Outside.L_meta_1751_aux.adj_irr
    PEqualNP.Outside.L_meta_1751_aux.adj_c4 PEqualNP.Outside.L_meta_1751_aux.rq_cover
    hMono hE hEanti hacc' hrej' hA h5
  have h13 := PEqualNP.Outside.L_meta_1751_aux.cover13 K hK
  rw [PEqualNP.Outside.L_meta_1751_aux.e26_card] at hcard
  have hsz : C.size = C.gates.length := rfl
  omega
