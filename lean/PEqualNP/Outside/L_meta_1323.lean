import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1323

open PEqualNP.CircuitLowerBounds

private def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

private theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = .not := by
  cases g with
  | mk op ins => cases op <;> simp [isNot]

private def wiresAt {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gates 0).wires (List.ofFn x)

private def readGate {n : ℕ} (gates : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  (g.inputs.map (fun k => (wiresAt gates x).getD k false)).headD false

private def readAt {n : ℕ} (gates : List Gate) (t : Fin gates.length) (x : Fin n → Bool) : Bool :=
  readGate (gates.take t.val) (gates.get t) x

private def bit (b : Bool) : ℕ := if b then 1 else 0

-- The first NOT read is the most significant bit.
private def code {n : ℕ} (gates : List Gate) (x : Fin n → Bool) : ℕ :=
  gates.reverseRecOn 0 fun gs g c => if isNot g then 2 * c + bit (readGate gs g x) else c

private theorem codeSnoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    code (gs ++ [g]) x = if isNot g then 2 * code gs x + bit (readGate gs g x) else code gs x := by
  simp only [code, List.reverseRecOn_concat]

private theorem bitBound (b : Bool) : bit b < 2 := by cases b <;> decide

private theorem codeBound {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    code gs x < 2 ^ gs.countP isNot := by
  induction gs using List.reverseRecOn with
  | nil => simp [code]
  | append_singleton gs g ih =>
    rw [codeSnoc, List.countP_append, List.countP_singleton]
    by_cases h : isNot g = true
    · simp only [h, ite_true, pow_succ]
      have hb := bitBound (readGate gs g x)
      omega
    · simpa [h] using ih

private def WireOrder (u v : List Bool) : Prop :=
  ∀ k : ℕ, u.getD k false = true → v.getD k false = true

private def ReadAgreement {n : ℕ} (gs : List Gate) (x y : Fin n → Bool) : Prop :=
  ∀ t : Fin gs.length, (gs.get t).op = .not → readAt gs t x = readAt gs t y

private theorem wiresSnoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wiresAt (gs ++ [g]) x =
      wiresAt gs x ++ [g.op.eval (g.inputs.map fun k => (wiresAt gs x).getD k false)] := by
  simp only [wiresAt, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem wiresLength {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (wiresAt gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresAt, Circuit.wires]
  | append_singleton gs g ih => rw [wiresSnoc]; simp [ih, Nat.add_assoc]

private theorem inputOrder {n : ℕ} {x y : Fin n → Bool}
    (xy : ∀ k, x k = true → y k = true) : WireOrder (List.ofFn x) (List.ofFn y) := by
  intro k h
  by_cases hk : k < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk] using
      xy ⟨k, hk⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hk] using h)
  · simp [List.getD_eq_getElem?_getD, hk] at h

private theorem orderAppend {u v : List Bool} {a b : Bool} (hl : u.length = v.length)
    (h : WireOrder u v) (hab : a = true → b = true) :
    WireOrder (u ++ [a]) (v ++ [b]) := by
  intro k hk
  by_cases hi : k < u.length
  · rw [List.getD_append _ _ _ _ hi] at hk
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h k hk
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hk
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    by_cases heq : k = u.length
    · subst k
      simpa using hab (by simpa using hk)
    · have hpos : 1 ≤ k - u.length := by omega
      rw [List.getD_eq_default _ _ (by simpa using hpos)] at hk
      contradiction

private theorem monotoneRead {n : ℕ} (gs : List Gate) (g : Gate) {x y : Fin n → Bool}
    (h : WireOrder (wiresAt gs x) (wiresAt gs y)) :
    readGate gs g x = true → readGate gs g y = true := by
  unfold readGate
  cases g.inputs with
  | nil => simp
  | cons k ins =>
    simpa only [List.map_cons, List.headD_cons] using h k

private theorem positiveStep (g : Gate) {u v : List Bool} (h : WireOrder u v)
    (hop : g.op = .and ∨ g.op = .or) :
    g.op.eval (g.inputs.map fun k => u.getD k false) = true →
      g.op.eval (g.inputs.map fun k => v.getD k false) = true := by
  rcases hop with ha | ho
  · simp only [ha, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hp z hz
    obtain ⟨k, hk, rfl⟩ := hz
    exact h k (hp _ ⟨k, hk, rfl⟩)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨z, ⟨k, hk, rfl⟩, hz⟩
    exact ⟨_, ⟨k, hk, rfl⟩, h k hz⟩

private theorem oldGate (gs : List Gate) (g : Gate) (t : Fin (gs ++ [g]).length)
    (h : t.val < gs.length) : (gs ++ [g]).get t = gs.get ⟨t.val, h⟩ := by
  exact List.getElem_append_left h

private theorem lastGate (gs : List Gate) (g : Gate) :
    (gs ++ [g]).get ⟨gs.length, by simp⟩ = g := by
  simp [List.get_eq_getElem, List.getElem_append_right]

private theorem agreeAppend {n : ℕ} (gs : List Gate) (g : Gate) (x y : Fin n → Bool)
    (agree : ReadAgreement gs x y) (last : g.op = .not → readGate gs g x = readGate gs g y) :
    ReadAgreement (gs ++ [g]) x y := by
  intro t ht
  by_cases h : t.val < gs.length
  · have e := oldGate gs g t h
    have heq := agree ⟨t.val, h⟩ (e ▸ ht)
    simpa only [readAt, e, List.take_append_of_le_length (Nat.le_of_lt h)] using heq
  · have htlen : t.val = gs.length := by have hlt := t.isLt; simp at hlt; omega
    have et : t = ⟨gs.length, by simp⟩ := Fin.ext htlen
    subst t
    rw [lastGate] at ht
    simpa only [readAt, lastGate, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length] using last ht

-- Equal codes preserve every earlier NOT read and the wire values are ordered.
private theorem codeOrder {n : ℕ} (gs : List Gate) (x y : Fin n → Bool)
    (xy : ∀ k, x k = true → y k = true)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    code gs x ≤ code gs y ∧ (code gs x = code gs y →
      WireOrder (wiresAt gs x) (wiresAt gs y) ∧ ReadAgreement gs x y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨by simp [code], fun _ => ⟨?_, ?_⟩⟩
    · simpa [wiresAt, Circuit.wires] using inputOrder xy
    · intro t
      exact Fin.elim0 t
  | append_singleton gs g ih =>
    obtain ⟨hle, he⟩ := ih (fun q hq => allowed q (List.mem_append_left _ hq))
    have hg := allowed g (List.mem_append_right _ (by simp))
    have hlen : (wiresAt gs x).length = (wiresAt gs y).length := by simp [wiresLength]
    by_cases hflag : isNot g = true
    · have hn := (isNot_iff g).mp hflag
      simp only [codeSnoc, hflag, ite_true]
      have hx := bitBound (readGate gs g x)
      have hy := bitBound (readGate gs g y)
      constructor
      · by_cases hc : code gs x = code gs y
        · have hr := monotoneRead gs g (he hc).1
          cases hx' : readGate gs g x <;> cases hy' : readGate gs g y <;> simp [bit, hx', hy'] at hr ⊢ <;> omega
        · omega
      · intro hsame
        have hp : code gs x = code gs y := by omega
        have hb : bit (readGate gs g x) = bit (readGate gs g y) := by omega
        have hr : readGate gs g x = readGate gs g y := by
          cases hx' : readGate gs g x <;> cases hy' : readGate gs g y <;> simp [bit, hx', hy'] at hb ⊢
        refine ⟨?_, agreeAppend gs g x y (he hp).2 (fun _ => hr)⟩
        rw [wiresSnoc, wiresSnoc]
        apply orderAppend hlen (he hp).1
        rw [hn]
        change (!readGate gs g x) = true → (!readGate gs g y) = true
        rw [hr]
        exact id
    · simp only [codeSnoc, hflag]
      refine ⟨hle, fun hp => ⟨?_, ?_⟩⟩
      · rw [wiresSnoc, wiresSnoc]
        apply orderAppend hlen (he hp).1
        apply positiveStep g (he hp).1
        exact hg.elim Or.inl (fun hor => hor.elim Or.inr (fun hn => (hflag ((isNot_iff g).mpr hn)).elim))
      · exact agreeAppend gs g x y (he hp).2 (fun hn => (hflag ((isNot_iff g).mpr hn)).elim)

private theorem countPositions (gs : List Gate) :
    gs.countP isNot = (Finset.univ.filter (fun t : Fin gs.length => isNot (gs.get t))).card := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [Finset.card_filter] at ih
    simp only [Finset.card_filter, List.length_cons, Fin.sum_univ_succ, List.countP_cons,
      List.get_eq_getElem]
    rw [ih]
    ac_rfl

private theorem countBound (gs : List Gate) (s : ℕ) (cover : Fin s → Fin gs.length)
    (hc : ∀ t : Fin gs.length, (gs.get t).op = .not → ∃ k : Fin s, cover k = t) :
    gs.countP isNot ≤ s := by
  rw [countPositions]
  have h : Finset.univ.filter (fun t : Fin gs.length => isNot (gs.get t)) ⊆
      Finset.univ.image cover := by
    intro t ht
    obtain ⟨k, hk⟩ := hc t ((isNot_iff _).mp (Finset.mem_filter.mp ht).2)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  exact (Finset.card_le_card h).trans (by simpa using (Finset.card_image_le (s := Finset.univ) (f := cover)))

end PEqualNP.Outside.L_meta_1323

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1323 : ∀ (n s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → ∀ (r : ℕ) (x : ℕ → Fin n → Bool), (∀ i : ℕ, i < r → ∀ p : Fin n, x i p = true → x (i + 1) p = true) → (∀ i : ℕ, i < r → ∃ t : Fin gates.length, (gates.get t).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x i))).getD k false)).headD false ≠ ((gates.get t).inputs.map (fun k : ℕ => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take t.val, 0⟩ (List.ofFn (x (i + 1)))).getD k false)).headD false) → r + 1 ≤ 2 ^ s := by
  open PEqualNP.Outside.L_meta_1323 in
  intro n s gates hgate
  rintro ⟨cover, hcover⟩ r x hx hchanges
  have increase (i : ℕ) (hi : i < r) : code gates (x i) < code gates (x (i + 1)) := by
    obtain ⟨hle, he⟩ := codeOrder gates (x i) (x (i + 1)) (hx i hi) (fun g hg => (hgate g hg).1)
    obtain ⟨t, ht, hne⟩ := hchanges i hi
    exact lt_of_le_of_ne hle (fun hc => hne ((he hc).2 t ht))
  have chain (i : ℕ) (hi : i ≤ r) : i ≤ code gates (x i) := by
    induction i with
    | zero => omega
    | succ i ih =>
      have := increase i (by omega)
      have := ih (by omega)
      omega
  have hb := (codeBound gates (x r)).trans_le (Nat.pow_le_pow_right (by decide) (countBound gates s cover hcover))
  have hr := chain r (le_refl _)
  omega
