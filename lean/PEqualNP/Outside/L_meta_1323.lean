import Mathlib
import PEqualNP.Defs

-- Along an inclusion chain of inputs, read the inputs of the NOT gates as a binary number,
-- the earliest NOT gate as the highest digit. At each step, the earliest NOT gate whose read
-- changes sees, before it, only gates whose NOT reads did not change, so the wires before it
-- are monotone in the input and its read goes from false to true. Hence the number grows at
-- every step. It lies below 2 to the number of NOT gates, which is at most s.

namespace PEqualNP.Outside.L_meta_1323_proof

open PEqualNP.CircuitLowerBounds

-- The wires of the first t gates on input x.
def W {n : ℕ} (gates : List Gate) (t : ℕ) (x : Fin n → Bool) : List Bool :=
  Circuit.wires ⟨gates.take t, 0⟩ (List.ofFn x)

-- The value read by gate t (its first input) on input x.
def rd {n : ℕ} (gates : List Gate) (t : Fin gates.length) (x : Fin n → Bool) : Bool :=
  ((gates.get t).inputs.map (fun k : ℕ => (W gates t.val x).getD k false)).headD false

-- Whether an operation is NOT.
def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem isNot_iff (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

theorem W_zero {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : W gates 0 x = List.ofFn x := by
  simp [W, Circuit.wires]

theorem W_succ {n : ℕ} (gates : List Gate) (t : ℕ) (ht : t < gates.length)
    (x : Fin n → Bool) :
    W gates (t + 1) x = W gates t x ++
      [gates[t].op.eval (gates[t].inputs.map fun k => (W gates t x).getD k false)] := by
  unfold W Circuit.wires
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem W_length {n : ℕ} (gates : List Gate) (x : Fin n → Bool) :
    ∀ t : ℕ, t ≤ gates.length → (W gates t x).length = n + t := by
  intro t
  induction t with
  | zero => intro _; simp [W_zero]
  | succ t ih =>
    intro ht
    rw [W_succ gates t (by omega), List.length_append, ih (by omega)]
    simp
    omega

theorem getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

theorem all_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).all id = true → (ks.map g).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id]
  rintro h b ⟨k, hk, rfl⟩
  exact hfg k (h (f k) ⟨k, hk, rfl⟩)

theorem any_mono (ks : List ℕ) (f g : ℕ → Bool) (hfg : ∀ k, f k = true → g k = true) :
    (ks.map f).any id = true → (ks.map g).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id]
  rintro ⟨b, ⟨k, hk, rfl⟩, hb⟩
  exact ⟨g k, ⟨k, hk, rfl⟩, hfg k hb⟩

-- Monotonicity of the wires before t, when no NOT read before t changes.
theorem W_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ t : ℕ, t ≤ gates.length →
      (∀ t' : Fin gates.length, t'.val < t → (gates.get t').op = GateOp.not →
        rd gates t' x = rd gates t' y) →
      ∀ k, (W gates t x).getD k false = true → (W gates t y).getD k false = true := by
  intro t
  induction t with
  | zero =>
    intro _ _ k hk
    rw [W_zero, ofFn_getD] at hk ⊢
    split_ifs at hk ⊢ with h
    · exact hxy _ hk
  | succ t ih =>
    intro ht heq k hk
    have htl : t < gates.length := by omega
    have ih' := ih (by omega) (fun t' h1 h2 => heq t' (by omega) h2)
    rw [W_succ gates t htl, getD_snoc] at hk ⊢
    rw [W_length gates x t (by omega)] at hk
    rw [W_length gates y t (by omega)]
    split_ifs at hk ⊢ with h1 h2
    · exact ih' k hk
    · rcases hops _ (List.getElem_mem htl) with hop | hop | hop
      · rw [hop] at hk ⊢
        exact all_mono _ _ _ ih' hk
      · rw [hop] at hk ⊢
        exact any_mono _ _ _ ih' hk
      · have hr := heq ⟨t, htl⟩ (by simp) (by simpa using hop)
        unfold rd at hr
        simp only [List.get_eq_getElem] at hr
        rw [hop] at hk ⊢
        simp only [GateOp.eval] at hk ⊢
        rw [← hr]
        exact hk

-- The read of gate t goes up when no NOT read before it changes.
theorem rd_mono {n : ℕ} (gates : List Gate)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (t : Fin gates.length)
    (heq : ∀ t' : Fin gates.length, t' < t → (gates.get t').op = GateOp.not →
      rd gates t' x = rd gates t' y) :
    rd gates t x = true → rd gates t y = true := by
  have hm := W_mono gates hops x y hxy t.val t.isLt.le (fun t' h1 h2 => heq t' h1 h2)
  unfold rd
  cases hin : (gates.get t).inputs with
  | nil => simp
  | cons k ks =>
    simp only [List.map_cons, List.headD_cons]
    exact hm k

-- The weight of position t in A: two to the number of later members of A.
def wt {L : ℕ} (A : Finset (Fin L)) (t : Fin L) : ℕ := 2 ^ (A.filter (fun t' => t < t')).card

theorem sum_wt {L : ℕ} (A : Finset (Fin L)) : (∑ t ∈ A, wt A t) + 1 = 2 ^ A.card := by
  refine Finset.induction_on_max A ?_ ?_
  · simp
  · intro a s ha ih
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.sum_insert hna, Finset.card_insert_of_notMem hna]
    have h1 : wt (insert a s) a = 1 := by
      unfold wt
      have h : (insert a s).filter (fun t' => a < t') = ∅ := by
        apply Finset.filter_false_of_mem
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact lt_irrefl _
        · exact not_lt.2 (ha t ht).le
      rw [h]
      simp
    have h2 : ∀ t ∈ s, wt (insert a s) t = 2 * wt s t := by
      intro t ht
      unfold wt
      rw [Finset.filter_insert, if_pos (ha t ht), Finset.card_insert_of_notMem (by simp [hna]),
        pow_succ]
      ring
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, pow_succ, ← ih]
    ring

-- The binary number of the NOT reads.
def pot {n : ℕ} (gates : List Gate) (A : Finset (Fin gates.length)) (x : Fin n → Bool) : ℕ :=
  ∑ t ∈ A, if rd gates t x = true then wt A t else 0

theorem pot_le {n : ℕ} (gates : List Gate) (A : Finset (Fin gates.length)) (x : Fin n → Bool) :
    pot gates A x + 1 ≤ 2 ^ A.card := by
  rw [← sum_wt A]
  have : pot gates A x ≤ ∑ t ∈ A, wt A t := by
    apply Finset.sum_le_sum
    intro t _
    split_ifs <;> simp
  omega

theorem pot_lt {n : ℕ} (gates : List Gate) (A : Finset (Fin gates.length)) (x y : Fin n → Bool)
    (t0 : Fin gates.length) (ht0 : t0 ∈ A)
    (heq : ∀ t ∈ A, t < t0 → rd gates t x = rd gates t y)
    (hx : rd gates t0 x = false) (hy : rd gates t0 y = true) :
    pot gates A x < pot gates A y := by
  set f := fun (z : Fin n → Bool) (t : Fin gates.length) =>
    if rd gates t z = true then wt A t else 0 with hf
  set B := A.filter (fun t => t < t0) with hB
  set A' := A.filter (fun t => ¬ t < t0) with hA'
  set Cc := A'.erase t0 with hCc
  have ht0' : t0 ∈ A' := Finset.mem_filter.2 ⟨ht0, lt_irrefl _⟩
  have hsplit : ∀ z, pot gates A z = (∑ t ∈ B, f z t) + (f z t0 + ∑ t ∈ Cc, f z t) := by
    intro z
    unfold pot
    rw [← Finset.sum_filter_add_sum_filter_not A (fun t => t < t0), Finset.add_sum_erase _ _ ht0']
  have hmemC : ∀ t, t ∈ Cc ↔ t ∈ A ∧ t0 < t := by
    intro t
    rw [hCc, Finset.mem_erase, hA', Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, lt_of_le_of_ne (not_lt.1 h3) (Ne.symm h1)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨ne_of_gt h2, h1, not_lt.2 h2.le⟩
  have hB_eq : ∑ t ∈ B, f x t = ∑ t ∈ B, f y t := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hB, Finset.mem_filter] at ht
    simp only [hf, heq t ht.1 ht.2]
  have hwC : ∀ t ∈ Cc, wt A t = wt Cc t := by
    intro t ht
    unfold wt
    congr 1
    apply Finset.card_bij (fun a _ => a)
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨(hmemC a).2 ⟨ha.1, lt_trans ((hmemC t).1 ht).2 ha.2⟩, ha.2⟩
    · intro a _ b _ h
      exact h
    · intro b hb
      rw [Finset.mem_filter] at hb
      exact ⟨b, Finset.mem_filter.2 ⟨((hmemC b).1 hb.1).1, hb.2⟩, rfl⟩
  have hw0 : wt A t0 = 2 ^ Cc.card := by
    unfold wt
    congr 1
    apply Finset.card_bij (fun a _ => a)
    · intro a ha
      rw [Finset.mem_filter] at ha
      exact (hmemC a).2 ha
    · intro a _ b _ h
      exact h
    · intro b hb
      exact ⟨b, Finset.mem_filter.2 ((hmemC b).1 hb), rfl⟩
  have hCle : ∑ t ∈ Cc, f x t ≤ ∑ t ∈ Cc, wt Cc t := by
    rw [← Finset.sum_congr rfl hwC]
    apply Finset.sum_le_sum
    intro t _
    simp only [hf]
    split_ifs <;> simp
  have hsum := sum_wt Cc
  have hfx0 : f x t0 = 0 := by simp [hf, hx]
  have hfy0 : f y t0 = wt A t0 := by simp [hf, hy]
  rw [hsplit x, hsplit y, hfx0, hfy0, hB_eq, hw0]
  generalize 2 ^ Cc.card = c at hsum
  omega

end PEqualNP.Outside.L_meta_1323_proof

open PEqualNP.Outside.L_meta_1323_proof in
theorem PEqualNP.Outside.L_meta_1323 : ∀ (n s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → ∀ (r : ℕ) (x : ℕ → Fin n → Bool), (∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true) → (∀ i : ℕ, i < r → ∃ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) → r + 1 ≤ 2 ^ s := by
  intro n s gates hg ⟨ι, hι⟩ r x hchain hchg
  have hops : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not := fun g h => (hg g h).1
  set A : Finset (Fin gates.length) :=
    Finset.univ.filter (fun t => isNot (gates.get t).op = true) with hA
  have hAcard : A.card ≤ s := by
    have hsub : A ⊆ Finset.univ.image ι := by
      intro t ht
      rw [hA, Finset.mem_filter, isNot_iff] at ht
      obtain ⟨j, hj⟩ := hι t ht.2
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    calc A.card ≤ (Finset.univ.image ι).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by simp
  have hstep : ∀ i, i < r → pot gates A (x i) < pot gates A (x (i + 1)) := by
    intro i hi
    obtain ⟨t, htn, htd⟩ := hchg i hi
    change rd gates t (x i) ≠ rd gates t (x (i + 1)) at htd
    set Ch := A.filter (fun t => rd gates t (x i) ≠ rd gates t (x (i + 1))) with hCh
    have hne : Ch.Nonempty :=
      ⟨t, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (isNot_iff _).2 htn⟩, htd⟩⟩
    have ht0 : Ch.min' hne ∈ Ch := Finset.min'_mem _ _
    replace ht0 := Finset.mem_filter.1 ht0
    have heq : ∀ t' ∈ A, t' < Ch.min' hne → rd gates t' (x i) = rd gates t' (x (i + 1)) := by
      intro t' ht' hlt
      by_contra hc
      have hmem : t' ∈ Ch := Finset.mem_filter.2 ⟨ht', hc⟩
      exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
    have hmono := rd_mono gates hops (x i) (x (i + 1)) (hchain i hi) (Ch.min' hne)
      (fun t' h1 h2 => heq t' (Finset.mem_filter.2 ⟨Finset.mem_univ _, (isNot_iff _).2 h2⟩) h1)
    have hx : rd gates (Ch.min' hne) (x i) = false := by
      by_contra hc
      have h1 : rd gates (Ch.min' hne) (x i) = true := by simpa using hc
      exact ht0.2 (by rw [h1, hmono h1])
    have hy : rd gates (Ch.min' hne) (x (i + 1)) = true := by
      have h := ht0.2
      rw [hx] at h
      simpa using (Ne.symm h)
    exact pot_lt gates A (x i) (x (i + 1)) (Ch.min' hne) ht0.1 heq hx hy
  have hgrow : ∀ i, i ≤ r → pot gates A (x 0) + i ≤ pot gates A (x i) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep i (by omega)
      omega
  have h1 := hgrow r le_rfl
  have h2 := pot_le gates A (x r)
  have h3 : 2 ^ A.card ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hAcard
  omega
