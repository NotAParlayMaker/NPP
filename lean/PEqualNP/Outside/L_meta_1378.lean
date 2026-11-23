import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1378

private def hit {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ p ∈ A, x p = true)

private def point {n : ℕ} (p : Fin n) (i : Fin n) : Bool := decide (i = p)

private def avoid {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∉ A)

private theorem hit_point {n : ℕ} (A : Finset (Fin n)) (p : Fin n) :
    hit A (point p) = true ↔ p ∈ A := by
  simp [hit, point]

private theorem hit_zero {n : ℕ} (A : Finset (Fin n)) :
    hit A (fun _ => false) = false := by simp [hit]

private theorem points {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card) :
    ∃ p ∈ A, ∃ q ∈ A, p ≠ q := Finset.one_lt_card.mp (by omega)

private theorem hit_top {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card) :
    hit A (fun _ => true) = true := by
  obtain ⟨p, hp, _, _, _⟩ := points hA
  exact decide_eq_true ⟨p, hp, rfl⟩

private theorem hit_avoid {n : ℕ} (A : Finset (Fin n)) :
    hit A (avoid A) = false := by simp [hit, avoid]

private theorem hit_cross {n : ℕ} {A B : Finset (Fin n)}
    (hA : 3 ≤ A.card) (hAB : (A ∩ B).card ≤ 1) :
    hit A (avoid B) = true := by
  by_contra h
  have hsub : A ⊆ A ∩ B := by
    intro p hp
    refine Finset.mem_inter.mpr ⟨hp, ?_⟩
    by_contra hn
    exact h (decide_eq_true ⟨p, hp, by simp [avoid, hn]⟩)
  have hcard := Finset.card_le_card hsub
  omega

private def addWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldSuffix (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, gs.foldl addWire w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨tail, ht, hl⟩ := ih (addWire w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tail, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [addWire, List.append_assoc]

private theorem foldLen (gs : List Gate) (w : List Bool) :
    (gs.foldl addWire w).length = w.length + gs.length := by
  obtain ⟨tail, ht, hl⟩ := foldSuffix gs w
  simp [ht, hl]

private theorem foldGet (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl addWire w).getD i false = w.getD i false := by
  obtain ⟨tail, ht, _⟩ := foldSuffix gs w
  simp only [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getOutside (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

private def wire {n : ℕ} (gs : List Gate) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl addWire (List.ofFn x)).getD i false

private theorem wireInput {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    wire gs i x = x ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [wire, foldGet gs _ i hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
  simp

-- A gate sees only its input wires and the gates that came before it.
private def earlier {n : ℕ} (gs : List Gate) (g i : ℕ) (x : Fin n → Bool) : Bool :=
  if i < g then wire gs i x else false

private theorem wireGate {n : ℕ} (gs : List Gate) (j : Fin gs.length) (x : Fin n → Bool) :
    wire gs (n + j.val) x =
      gs[j.val].op.eval (gs[j.val].inputs.map fun i => earlier gs (n + j.val) i x) := by
  let w := (gs.take j.val).foldl addWire (List.ofFn x)
  let g := gs[j.val]
  let rest := gs.drop (j.val + 1)
  have hw : w.length = n + j.val := by
    simp [w, foldLen]
  have hsplit : gs.take j.val ++ g :: rest = gs := by
    dsimp [g, rest]
    rw [← List.drop_eq_getElem_cons j.isLt, List.take_append_drop]
  have hfold : gs.foldl addWire (List.ofFn x) = rest.foldl addWire (addWire w g) := by
    conv_lhs => rw [← hsplit]
    simp [w, List.foldl_append]
  have hget (i : ℕ) : w.getD i false = earlier gs (n + j.val) i x := by
    by_cases hi : i < n + j.val
    · have hwi : i < w.length := by simpa [hw] using hi
      have hlen : (addWire w g).length = n + j.val + 1 := by simp [addWire, hw]
      have hgi : i < (addWire w g).length := by omega
      rw [earlier, ite_eq_left hi, wire, hfold, foldGet rest (addWire w g) i hgi]
      simp only [addWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hwi]
    · rw [earlier, ite_eq_right hi, getOutside _ _ (by omega)]
  have hj : n + j.val < (addWire w g).length := by simp [addWire, hw]
  unfold wire
  rw [hfold, foldGet _ _ _ hj]
  have hat : (addWire w g).getD (n + j.val) false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [addWire, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), show n + j.val - w.length = 0 by omega]
    rfl
  rw [hat]
  change g.op.eval (g.inputs.map fun i => w.getD i false) = _
  simp only [hget, g]

private theorem gateRef {n : ℕ} (gs : List Gate) (j i : ℕ) (x y : Fin n → Bool)
    (hx : earlier gs j i x = true) (hy : earlier gs j i y = true)
    (hxy : ∀ p, x p = true → y p = false) :
    n ≤ i ∧ i < j := by
  have hij : i < j := by
    by_contra hn
    simp [earlier, hn] at hx
  refine ⟨?_, hij⟩
  by_contra hn
  have hin : i < n := by omega
  rw [earlier, ite_eq_left hij, wireInput gs i hin] at hx hy
  exact Bool.false_ne_true ((hxy ⟨i, hin⟩ hx).symm.trans hy)

private theorem pointSeparate {n : ℕ} {p q : Fin n} (hpq : p ≠ q) :
    ∀ i, point p i = true → point q i = false := by
  intro i hi
  have h : i = p := of_decide_eq_true hi
  simp [point, h, hpq]

-- Two singleton witnesses keep an OR child specific to one output set.
private def OrChild {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = true → hit A x = true) ∧
  ∃ p q : Fin n, p ≠ q ∧ f (point p) = true ∧ f (point q) = true

-- An AND child rejects the assignment where exactly the outside points are true.
private def AndChild {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, hit A x = true → f x = true) ∧ f (avoid A) = false

private def Auxiliary {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  OrChild A f ∨ AndChild A f ∨ ∀ x, f x = !hit A x

private theorem chooseOr {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card)
    (f g : (Fin n → Bool) → Bool) (h : ∀ x, (f x || g x) = hit A x) :
    OrChild A f ∨ OrChild A g := by
  let B := A.filter fun p => f (point p) = true
  let D := A.filter fun p => g (point p) = true
  have hcover : A ⊆ B ∪ D := by
    intro p hp
    have h' := h (point p)
    rw [(hit_point A p).2 hp, Bool.or_eq_true] at h'
    exact Finset.mem_union.mpr (h'.imp (fun t => Finset.mem_filter.mpr ⟨hp, t⟩)
      (fun t => Finset.mem_filter.mpr ⟨hp, t⟩))
  have hbd := (Finset.card_le_card hcover).trans (Finset.card_union_le B D)
  have hbig : 1 < B.card ∨ 1 < D.card := by omega
  rcases hbig with hB | hD
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hB
    left
    refine ⟨?_, p, q, hpq, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hq).2⟩
    intro x hx
    simpa [hx] using (h x).symm
  · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hD
    right
    refine ⟨?_, p, q, hpq, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hq).2⟩
    intro x hx
    simpa [hx] using (h x).symm

private theorem chooseAnd {n : ℕ} (A : Finset (Fin n))
    (f g : (Fin n → Bool) → Bool) (h : ∀ x, (f x && g x) = hit A x) :
    AndChild A f ∨ AndChild A g := by
  have hboth (x) (hx : hit A x = true) : f x = true ∧ g x = true :=
    by simpa using (h x).trans hx
  cases hf : f (avoid A)
  · exact Or.inl ⟨fun x hx => (hboth x hx).1, hf⟩
  · have h' := h (avoid A)
    rw [hf, hit_avoid] at h'
    exact Or.inr ⟨fun x hx => (hboth x hx).2, h'⟩

private theorem chooseGate {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card)
    (op : GateOp) (is : List ℕ) (v : ℕ → (Fin n → Bool) → Bool)
    (hop : op = .and ∨ op = .or ∨ op = .not) (hlen : is.length ≤ 2)
    (h : ∀ x, op.eval (is.map (fun i => v i x)) = hit A x) :
    ∃ i, Auxiliary A (v i) := by
  rcases hop with rfl | rfl | rfl
  · rcases is with _ | ⟨i, rest⟩
    · have ha := h (avoid A)
      simp [GateOp.eval, hit_avoid] at ha
    · rcases rest with _ | ⟨j, rest⟩
      · exact ⟨i, Or.inr (Or.inl ⟨fun x hx => (by simpa [GateOp.eval] using (h x).trans hx),
          by simpa [GateOp.eval, hit_avoid] using h (avoid A)⟩)⟩
      · have hr : rest = [] := List.eq_nil_of_length_eq_zero (by
          have hl : rest.length + 1 + 1 ≤ 2 := hlen
          omega)
        subst rest
        rcases chooseAnd A (v i) (v j) (fun x => by simpa [GateOp.eval] using h x) with hi | hj
        · exact ⟨i, Or.inr (Or.inl hi)⟩
        · exact ⟨j, Or.inr (Or.inl hj)⟩
  · rcases is with _ | ⟨i, rest⟩
    · have ha := h (fun _ => true)
      simp [GateOp.eval, hit_top hA] at ha
    · rcases rest with _ | ⟨j, rest⟩
      · have he (x) : v i x = hit A x := by simpa [GateOp.eval] using h x
        obtain ⟨p, hp, q, hq, hpq⟩ := points hA
        exact ⟨i, Or.inl ⟨fun x hx => (he x).symm.trans hx, p, q, hpq,
          (he _).trans ((hit_point A p).2 hp), (he _).trans ((hit_point A q).2 hq)⟩⟩
      · have hr : rest = [] := List.eq_nil_of_length_eq_zero (by
          have hl : rest.length + 1 + 1 ≤ 2 := hlen
          omega)
        subst rest
        rcases chooseOr hA (v i) (v j) (fun x => by simpa [GateOp.eval] using h x) with hi | hj
        · exact ⟨i, Or.inl hi⟩
        · exact ⟨j, Or.inl hj⟩
  · rcases is with _ | ⟨i, rest⟩
    · have ha := h (fun _ => false)
      simp [GateOp.eval, hit_zero] at ha
    · refine ⟨i, Or.inr (Or.inr ?_)⟩
      intro x
      have he := h x
      change (!(v i x)) = hit A x at he
      rw [← he, Bool.not_not]

private theorem auxiliaryEarlier {n : ℕ} {A : Finset (Fin n)} (hA : 3 ≤ A.card)
    (gs : List Gate) (j i : ℕ) (h : Auxiliary A (earlier gs j i)) : n ≤ i ∧ i < j := by
  rcases h with ⟨_, p, q, hpq, hp, hq⟩ | h | h
  · exact gateRef gs j i (point p) (point q) hp hq (pointSeparate hpq)
  · obtain ⟨p, hp, q, hq, hpq⟩ := points hA
    exact gateRef gs j i (point p) (point q) (h.1 _ ((hit_point A p).2 hp))
      (h.1 _ ((hit_point A q).2 hq)) (pointSeparate hpq)
  · have h0 : earlier gs j i (fun _ : Fin n => false) = true := by simp [h, hit_zero]
    exact gateRef gs j i (fun _ => false) (fun _ => false) h0 h0 (fun _ _ => rfl)

private theorem auxiliariesDiffer {n : ℕ} {A B : Finset (Fin n)} (hA : 3 ≤ A.card)
    (hB : 3 ≤ B.card) (hAB : (A ∩ B).card ≤ 1) (f : (Fin n → Bool) → Bool)
    (ha : Auxiliary A f) (hb : Auxiliary B f) : False := by
  have crossA := hit_cross hA hAB
  have crossB := hit_cross (A := B) (B := A) hB (by simpa only [Finset.inter_comm B A] using hAB)
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · obtain ⟨p, q, hpq, hp, hq⟩ := ha.2
    exact hpq (Finset.card_le_one.mp hAB p (Finset.mem_inter.mpr
      ⟨(hit_point A p).1 (ha.1 _ hp), (hit_point B p).1 (hb.1 _ hp)⟩)
      q (Finset.mem_inter.mpr
      ⟨(hit_point A q).1 (ha.1 _ hq), (hit_point B q).1 (hb.1 _ hq)⟩))
  · exact Bool.false_ne_true ((hit_avoid A).symm.trans (ha.1 _ (hb.1 _ crossB)))
  · have hzero : f (fun _ => false) = true := by simp [hb, hit_zero]
    exact Bool.false_ne_true ((hit_zero A).symm.trans (ha.1 _ hzero))
  · exact Bool.false_ne_true ((hit_avoid B).symm.trans (hb.1 _ (ha.1 _ crossA)))
  · exact Bool.false_ne_true (ha.2.symm.trans (hb.1 _ crossB))
  · have htop : f (fun _ => true) = false := by simp [hb, hit_top hB]
    exact Bool.false_ne_true (htop.symm.trans (ha.1 _ (hit_top hA)))
  · have hzero : f (fun _ => false) = true := by simp [ha, hit_zero]
    exact Bool.false_ne_true ((hit_zero B).symm.trans (hb.1 _ hzero))
  · have htop : f (fun _ => true) = false := by simp [ha, hit_top hA]
    exact Bool.false_ne_true (htop.symm.trans (hb.1 _ (hit_top hB)))
  · have htrue : f (avoid A) = true := by simp [ha, hit_avoid]
    have hfalse : f (avoid A) = false := by simp [hb, crossB]
    exact Bool.false_ne_true (hfalse.symm.trans htrue)

private theorem auxiliaryNotOutput {n : ℕ} {A B : Finset (Fin n)} (hA : 3 ≤ A.card)
    (hB : 3 ≤ B.card) (hAB : (A ∩ B).card ≤ 1) (h : Auxiliary A (hit B)) : False := by
  rcases h with h | h | h
  · have crossB := hit_cross (A := B) (B := A) hB (by simpa only [Finset.inter_comm B A] using hAB)
    exact Bool.false_ne_true ((hit_avoid A).symm.trans (h.1 _ crossB))
  · exact Bool.false_ne_true ((hit_avoid B).symm.trans (h.1 _ (hit_cross hA hAB)))
  · have he := h (fun _ => false)
    simp [hit_zero] at he

private theorem countGates {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ w, 3 ≤ (S w).card)
    (hshare : ∀ u v, u ≠ v → (S u ∩ S v).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ w x, wire gs (out w) x = hit (S w) x) :
    2 * m ≤ gs.length := by
  classical
  have hoBound (w) : out w < n + gs.length := by
    by_contra! h
    have he := heval w (fun _ => true)
    rw [wire, getOutside _ _ (by simpa [foldLen] using h), hit_top (hsize w)] at he
    contradiction
  have hoLow (w) : n ≤ out w := by
    obtain ⟨p, hp, q, hq, hpq⟩ := points (hsize w)
    have hp' : earlier gs (n + gs.length) (out w) (point p) = true := by
      simp [earlier, hoBound w, heval, hit_point, hp]
    have hq' : earlier gs (n + gs.length) (out w) (point q) = true := by
      simp [earlier, hoBound w, heval, hit_point, hq]
    exact (gateRef gs _ _ _ _ hp' hq' (pointSeparate hpq)).1
  have auxExists (w) : ∃ i, n ≤ i ∧ i < out w ∧ Auxiliary (S w) (wire gs i) := by
    let j : Fin gs.length := ⟨out w - n, by have := hoBound w; have := hoLow w; omega⟩
    have hj' : n + j.val = out w := by dsimp [j]; have := hoLow w; omega
    let g := gs[j.val]
    have hg := hops g (List.getElem_mem j.isLt)
    have he (x) : g.op.eval (g.inputs.map fun i => earlier gs (out w) i x) = hit (S w) x := by
      have h := wireGate gs j x
      rw [hj', heval] at h
      exact h.symm
    obtain ⟨i, hi⟩ := chooseGate (hsize w) g.op g.inputs (fun k => earlier gs (out w) k)
      hg.1 hg.2 he
    have hi' := auxiliaryEarlier (hsize w) gs (out w) i hi
    have hfun : @earlier n gs (out w) i = wire gs i := by
      funext x
      simp only [earlier, ite_eq_left hi'.2]
    exact ⟨i, hi'.1, hi'.2, hfun ▸ hi⟩
  choose aux haux using auxExists
  have outputDistinct : Function.Injective out := by
    intro a b heq
    by_contra hab
    have e := heval a (avoid (S b))
    rw [heq, heval, hit_avoid, hit_cross (hsize a) (hshare a b hab)] at e
    contradiction
  have auxDistinct : Function.Injective aux := by
    intro a b heq
    by_contra hab
    have ha := (haux a).2.2
    rw [heq] at ha
    exact auxiliariesDiffer (hsize a) (hsize b) (hshare a b hab) _ ha (haux b).2.2
  have noOverlap (a b) : aux a ≠ out b := by
    intro heq
    by_cases hab : a = b
    · subst b
      exact (Nat.ne_of_lt (haux a).2.1) heq
    · have ha := (haux a).2.2
      rw [heq, show wire gs (out b) = hit (S b) from funext (heval b)] at ha
      exact auxiliaryNotOutput (hsize a) (hsize b) (hshare a b hab) ha
  -- The output gates and the chosen children give two disjoint copies of the outputs.
  let label : Fin m ⊕ Fin m → ℕ := Sum.elim out aux
  have labelLow (a) : n ≤ label a := by
    cases a with
    | inl w => exact hoLow w
    | inr w => exact (haux w).1
  have labelBound (a) : label a < n + gs.length := by
    cases a with
    | inl w => exact hoBound w
    | inr w => exact (haux w).2.1.trans (hoBound w)
  have labelInj : Function.Injective label := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (outputDistinct hab)
    · exact False.elim (noOverlap b a hab.symm)
    · exact False.elim (noOverlap a b hab)
    · exact congrArg Sum.inr (auxDistinct hab)
  let emb (a : Fin m ⊕ Fin m) : Fin gs.length :=
    ⟨label a - n, by have := labelBound a; have := labelLow a; omega⟩
  have embInj : Function.Injective emb := by
    intro a b h
    have e := congrArg Fin.val h
    change label a - n = label b - n at e
    have ha := labelLow a
    have hb := labelLow b
    exact labelInj (by omega)
  simpa [Fintype.card_sum, two_mul] using Fintype.card_le_of_injective emb embInj

end PEqualNP.Outside.L_meta_1378

theorem PEqualNP.Outside.L_meta_1378 :
    ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ m →
      (∀ i : Fin m, 3 ≤ (S i).card) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
        (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
        (∀ (w : Fin m) (x : Fin n → Bool),
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
            decide (∃ v ∈ S w, x v = true)) → 2 * m ≤ gates.length := by
  intro n m S _ hsize hshare gs out hops heval
  exact PEqualNP.Outside.L_meta_1378.countGates S hsize hshare gs out hops heval
