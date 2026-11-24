import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs

-- Adapts the wire-dependency argument from L_meta_2074 to fan-in at most two.
namespace PEqualNP.Outside.L_meta_2862

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

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
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

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

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

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length ≤ 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)))
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

-- Starting at the output and expanding each live gate adds at most one wire.
lemma input_bound (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (essential : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ j ≠ i, x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        circuitFun n C x = circuitFun n C y := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => (hC _ (gateAt_mem hj)).2)
        C.gates.length le_rfl {C.output} (by simpa using ho)
      exact ⟨T, by simpa [Circuit.size] using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        change val C (List.ofFn x) C.output = val C (List.ofFn y) C.output
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hall : T = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    obtain ⟨x, y, hxy, hne⟩ := essential i
    exact hne (hdep x y (fun j hj => hxy j (fun e => hi (e ▸ hj))))
  simpa [hall] using hT

lemma singleton_rejected (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hq : 1 ≤ q)
    (reject : ∀ x : Fin (N + N) → Bool,
      Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N + N) C x = false) (z : Fin (N + N)) :
    circuitFun (N + N) C (fun i => decide (i = z)) = false := by
  apply reject
  · apply le_trans _ hq
    rw [← Fintype.card_fin 1]
    exact Fintype.card_le_of_injective (fun _ => (0 : Fin 1)) (by
      intro a b _
      apply Subtype.ext
      apply Fin.ext
      have ha : Fin.natAdd N a.val = z := of_decide_eq_true a.property
      have hb : Fin.natAdd N b.val = z := of_decide_eq_true b.property
      have hh := congrArg Fin.val (ha.trans hb.symm)
      simp only [Fin.val_natAdd] at hh
      omega)
  · rintro ⟨p, l, _, hp, hl⟩
    have h1 : Fin.castAdd N p = z := of_decide_eq_true hp
    have h2 : Fin.natAdd N l = z := of_decide_eq_true hl
    have hh := congrArg Fin.val (h1.trans h2.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    have := p.isLt
    omega

end PEqualNP.Outside.L_meta_2862

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2862 in
theorem PEqualNP.Outside.L_meta_2862 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x1 < (200 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) → (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C hq hq' hN hline hpair hC accept reject
  have hNlarge : 100 ≤ N := by omega
  have point_has_line (p : Fin N) : ∃ l : Fin N, I p l := by
    let a : Fin N := ⟨0, by omega⟩
    let b : Fin N := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro e
      have ev := congrArg Fin.val e
      simp [a, b] at ev
    obtain ⟨r, hr⟩ : ∃ r : Fin N, p ≠ r := by
      by_cases ha : p = a
      · exact ⟨b, ha ▸ hab⟩
      · exact ⟨a, ha⟩
    obtain ⟨l, hp, _⟩ := hpair p r hr
    exact ⟨l, hp.1⟩
  have line_has_point (l : Fin N) : ∃ p : Fin N, I p l := by
    have hcard : 0 < Fintype.card {p : Fin N // I p l} := by rw [hline]; omega
    obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hcard
    exact ⟨p, hp⟩
  have hsize : N + N ≤ C.size + 1 := by
    apply input_bound (N + N) C hC
    intro i
    by_cases hi : i.val < N
    · let p : Fin N := ⟨i.val, hi⟩
      have hip : i = Fin.castAdd N p := Fin.ext rfl
      obtain ⟨l, hl⟩ := point_has_line p
      refine ⟨fun j => decide (j = Fin.natAdd N l),
        fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l), ?_, ?_⟩
      · intro j hj
        simp [← hip, hj]
      · rw [singleton_rejected q N I C (by omega) reject, accept p l hl]
        decide
    · let l : Fin N := ⟨i.val - N, by have := i.isLt; omega⟩
      have hil : i = Fin.natAdd N l := by apply Fin.ext; simp [l]; omega
      obtain ⟨p, hp⟩ := line_has_point l
      refine ⟨fun j => decide (j = Fin.castAdd N p),
        fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l), ?_, ?_⟩
      · intro j hj
        have hne : j ≠ Fin.natAdd N l := fun he => hj (he.trans hil.symm)
        simp only [hne, or_false]
      · rw [singleton_rejected q N I C (by omega) reject, accept p l hp]
        decide
  have hqbound := Nat.mul_le_mul_left N (show q ≤ 199 by omega)
  omega
