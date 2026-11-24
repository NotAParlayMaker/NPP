import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2422

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem eval_eq (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    circuitFun n C x = val C.gates C.output x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs w x = x ⟨w, hw⟩ := by
  rw [val, fd_keep stB false gs _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)

theorem or_path (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ) (h : Rr n C a b) :
    val C.gates a x = true → val C.gates b x = true := by
  unfold Rr at h
  induction h with
  | refl => exact id
  | tail _ hs ih =>
    intro ha
    obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := hs
    rw [gateAt_eq C rj hj] at hop hin
    exact (val_or C.gates x rj hj hop).2 ⟨_, hin, hlt, ih ha⟩

theorem and_true (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : val C.gates ((gateAt C j).inputs.getD 0 0) x = true)
    (h1 : val C.gates ((gateAt C j).inputs.getD 1 0) x = true) :
    val C.gates (n + j) x = true := by
  obtain ⟨_, hrb, hlen⟩ := hC
  have hrbj := hrb j hj
  rw [gateAt_eq C j hj] at hop h0 h1 hrbj
  have hl := hlen C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  rw [hab] at h0 h1
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  apply (val_and C.gates x j hj hop).2
  intro i hi
  refine ⟨hrbj i hi, ?_⟩
  rw [hab] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h0
  · exact h1

theorem and_true2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j s t : ℕ)
    (hj : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ((((gateAt C j).inputs.getD 0 0) = s ∧ ((gateAt C j).inputs.getD 1 0) = t) ∨
        (((gateAt C j).inputs.getD 0 0) = t ∧ ((gateAt C j).inputs.getD 1 0) = s)))
    (hs : val C.gates s x = true) (ht : val C.gates t x = true) :
    val C.gates (n + j) x = true := by
  obtain ⟨hlt, hop, hst⟩ := hj
  rcases hst with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact and_true n C hC x j hlt hop (by rw [e0]; exact hs) (by rw [e1]; exact ht)
  · exact and_true n C hC x j hlt hop (by rw [e0]; exact ht) (by rw [e1]; exact hs)

theorem core (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (g c cb : ℕ)
    (hg : g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      ((((gateAt C g).inputs.getD 0 0) = c ∧ ((gateAt C g).inputs.getD 1 0) = cb) ∨
        (((gateAt C g).inputs.getD 0 0) = cb ∧ ((gateAt C g).inputs.getD 1 0) = c)))
    (hRg : Rr n C (n + g) C.output) (h1 a v h2 u b : ℕ)
    (hh1 : h1 < C.gates.length ∧ (gateAt C h1).op = GateOp.and ∧
      ((((gateAt C h1).inputs.getD 0 0) = a ∧ ((gateAt C h1).inputs.getD 1 0) = v) ∨
        (((gateAt C h1).inputs.getD 0 0) = v ∧ ((gateAt C h1).inputs.getD 1 0) = a)))
    (hR1 : Rr n C (n + h1) c)
    (hh2 : h2 < C.gates.length ∧ (gateAt C h2).op = GateOp.and ∧
      ((((gateAt C h2).inputs.getD 0 0) = u ∧ ((gateAt C h2).inputs.getD 1 0) = b) ∨
        (((gateAt C h2).inputs.getD 0 0) = b ∧ ((gateAt C h2).inputs.getD 1 0) = u)))
    (hR2 : Rr n C (n + h2) cb) (wp wm wz wl : ℕ)
    (hpa : Rr n C wp a) (hmv : Rr n C wm v) (hzu : Rr n C wz u) (hlb : Rr n C wl b)
    (vp : val C.gates wp x = true) (vm : val C.gates wm x = true)
    (vz : val C.gates wz x = true) (vl : val C.gates wl x = true) :
    val C.gates C.output x = true := by
  apply or_path n C x _ _ hRg
  apply and_true2 n C hC x g c cb hg
  · apply or_path n C x _ _ hR1
    exact and_true2 n C hC x h1 a v hh1 (or_path n C x _ _ hpa vp) (or_path n C x _ _ hmv vm)
  · apply or_path n C x _ _ hR2
    exact and_true2 n C hC x h2 u b hh2 (or_path n C x _ _ hzu vz) (or_path n C x _ _ hlb vl)

theorem main (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C) (hpn : ∀ p2 : Fin N, pw p2 < n) (hln : ∀ l2 : Fin M, lw l2 < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (g c cb : ℕ)
    (hg : g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧
      ((((gateAt C g).inputs.getD 0 0) = c ∧ ((gateAt C g).inputs.getD 1 0) = cb) ∨
        (((gateAt C g).inputs.getD 0 0) = cb ∧ ((gateAt C g).inputs.getD 1 0) = c)))
    (hRg : Rr n C (n + g) C.output) (p : Fin N) (lq : Fin M) (h1 a v h2 u b : ℕ)
    (hh1 : h1 < C.gates.length ∧ (gateAt C h1).op = GateOp.and ∧
      ((((gateAt C h1).inputs.getD 0 0) = a ∧ ((gateAt C h1).inputs.getD 1 0) = v) ∨
        (((gateAt C h1).inputs.getD 0 0) = v ∧ ((gateAt C h1).inputs.getD 1 0) = a)))
    (hpa : Rr n C (pw p) a) (hR1 : Rr n C (n + h1) c)
    (hh2 : h2 < C.gates.length ∧ (gateAt C h2).op = GateOp.and ∧
      ((((gateAt C h2).inputs.getD 0 0) = u ∧ ((gateAt C h2).inputs.getD 1 0) = b) ∨
        (((gateAt C h2).inputs.getD 0 0) = b ∧ ((gateAt C h2).inputs.getD 1 0) = u)))
    (hlb : Rr n C (lw lq) b) (hR2 : Rr n C (n + h2) cb) (hpl : ¬ I p lq)
    (m : Fin M) (hmv : Rr n C (lw m) v) (hpm : ¬ I p m)
    (z : Fin N) (hzu : Rr n C (pw z) u) (hzl : ¬ I z lq) : I z m := by
  by_contra hzm
  have hno : ∀ p3 ∈ ({p, z} : Finset (Fin N)), ∀ l3 ∈ ({m, lq} : Finset (Fin M)), ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp3 hl3
    rcases hp3 with e | e <;> rcases hl3 with f | f <;> rw [e, f] <;> assumption
  have hs := hsound {p, z} {m, lq} Finset.card_le_two Finset.card_le_two hno
  rw [eval_eq] at hs
  have htrue := core n C hC (fun k3 : Fin n => decide (k3.val ∈
      ({p, z} : Finset (Fin N)).image pw ∪ ({m, lq} : Finset (Fin M)).image lw))
    g c cb hg hRg h1 a v h2 u b hh1 hR1 hh2 hR2 (pw p) (lw m) (pw z) (lw lq) hpa hmv hzu hlb
    (by
      rw [val_input _ _ _ (hpn p)]
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw
        (Finset.mem_insert_self p _))))
    (by
      rw [val_input _ _ _ (hln m)]
      exact decide_eq_true (Finset.mem_union_right _ (Finset.mem_image_of_mem lw
        (Finset.mem_insert_self m _))))
    (by
      rw [val_input _ _ _ (hpn z)]
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self z)))))
    (by
      rw [val_input _ _ _ (hln lq)]
      exact decide_eq_true (Finset.mem_union_right _ (Finset.mem_image_of_mem lw
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self lq)))))
  rw [htrue] at hs
  exact Bool.noConfusion hs

end PEqualNP.Outside.L_meta_2422

theorem PEqualNP.Outside.L_meta_2422 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ (g c cb : ℕ), (g < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = c ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = cb) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = cb ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = c))) → R (n + g) C.output → ∀ (p : Fin N) (l' : Fin M) (h1 a v h2 u b : ℕ), (h1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = v) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = v ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {p} → (∃ m1 : Fin M, R (lw m1) v ∧ ¬ I p m1) → R (n + h1) c → (h2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = u ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = u))) → {y1 : Fin M | R (lw y1) b} = {l'} → (∃ z1 : Fin N, R (pw z1) u ∧ ¬ I z1 l') → R (n + h2) cb → ¬ I p l' → ∀ m : Fin M, R (lw m) v → ¬ I p m → ∀ z : Fin N, R (pw z) u → ¬ I z l' → I z m := by
  intro n N M pw lw I C hC _ _ _ hpn hln hsound R hR g c cb hg hRg p lq h1 a v h2 u b hh1 _ hR1 hh2 hbl _ hR2 hpl m hmv hpm z hzu hzl
  subst hR
  have hpa := (Set.ext_iff.1 hh1.2 p).2 (Set.mem_singleton p)
  have hlb := (Set.ext_iff.1 hbl lq).2 (Set.mem_singleton lq)
  exact PEqualNP.Outside.L_meta_2422.main n N M pw lw I C hC hpn hln hsound g c cb hg hRg p lq h1 a v h2 u b hh1.1 hpa hR1 hh2 hlb hR2 hpl m hmv hpm z hzu hzl
