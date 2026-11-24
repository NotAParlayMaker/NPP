import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2355

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

def Tt (n : ℕ) (C : Circuit) : ℕ → List (ℕ × ℕ) → Prop :=
  fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
    (∀ (qv qt : ℕ), qv < n → Rr n C qv qt → Q qt [(qt, qv)]) →
    (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
      (gateAt C qj).op = GateOp.and → Rr n C (n + qj) qt →
      Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
      Q qt (qL1 ++ qL2)) → Q tt tL

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

theorem leaves (n : ℕ) (C : Circuit) (t : ℕ) (L : List (ℕ × ℕ)) (h : Tt n C t L) :
    ∀ gv ∈ L, Rr n C gv.2 gv.1 := by
  apply h (fun _ L => ∀ gv ∈ L, Rr n C gv.2 gv.1)
  · intro qv qt _ hR gv hgv
    rw [List.mem_singleton.1 hgv]
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 gv hgv
    rcases List.mem_append.1 hgv with h | h
    · exact h1 gv h
    · exact h2 gv h

theorem transv (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (t : ℕ)
    (L : List (ℕ × ℕ)) (h : Tt n C t L) :
    (∀ gv ∈ L, val C.gates gv.1 x = true) → val C.gates t x = true := by
  apply h (fun t L => (∀ gv ∈ L, val C.gates gv.1 x = true) → val C.gates t x = true)
  · intro qv qt _ _ hall
    exact hall (qt, qv) (List.mem_singleton.2 rfl)
  · intro qj qt L1 L2 hj hop hR h1 h2 hall
    apply or_path n C x _ _ hR
    apply and_true n C hC x qj hj hop
    · exact h1 (fun gv hgv => hall gv (List.mem_append_left _ hgv))
    · exact h2 (fun gv hgv => hall gv (List.mem_append_right _ hgv))

theorem main (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : Circuit) (hC : IsAO2 n C) (hpn : ∀ p2 : Fin N, pw p2 < n) (hln : ∀ l2 : Fin M, lw l2 < n)
    (hsound : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
      (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) →
      circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false)
    (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ))
    (htree : (∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧
        (gateAt C j0).op = GateOp.and ∧ Rr n C (n + j0) C.output ∧
        Tt n C ((gateAt C j0).inputs.getD 0 0) L1 ∧ Tt n C ((gateAt C j0).inputs.getD 1 0) L2 ∧
        L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧
      (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧
      (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) :
    ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, Rr n C (pw q) gv.1 → I q l := by
  obtain ⟨⟨j0, L1, L2, hj0, hop0, hR0, hT1, hT2, hL⟩, hvars, hcp, _⟩ := htree
  by_contra hcon
  have key : ∀ gv ∈ L, gv.2 = pw p → ∃ q : Fin N, Rr n C (pw q) gv.1 ∧ ¬ I q l := by
    intro gv hgv hp
    by_contra hne
    apply hcon
    refine ⟨gv, hgv, hp, fun q hq => ?_⟩
    by_contra hI
    exact hne ⟨q, hq, hI⟩
  haveI : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using key
  have hleafR : ∀ gv ∈ L, Rr n C gv.2 gv.1 := by
    intro gv hgv
    rw [hL] at hgv
    rcases List.mem_append.1 hgv with h | h
    · exact leaves n C _ L1 hT1 gv h
    · exact leaves n C _ L2 hT2 gv h
  have hPcard : (((L.filter (fun e1 => decide (e1.2 = pw p))).map f).toFinset).card ≤ 2 := by
    refine le_trans (List.toFinset_card_le _) ?_
    rw [List.length_map]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcp
    omega
  have hYcard : ({l} : Finset (Fin M)).card ≤ 2 := by simp
  have hno : ∀ p3 ∈ ((L.filter (fun e1 => decide (e1.2 = pw p))).map f).toFinset,
      ∀ l3 ∈ ({l} : Finset (Fin M)), ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton.1 hl3]
    obtain ⟨gv, hgv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp3)
    obtain ⟨hgvL, hgvp⟩ := List.mem_filter.1 hgv
    exact (hf gv hgvL (of_decide_eq_true hgvp)).2
  have hs := hsound _ _ hPcard hYcard hno
  rw [eval_eq] at hs
  have hleaf : ∀ gv ∈ L, val C.gates gv.1 (fun k3 : Fin n => decide (k3.val ∈
      (((L.filter (fun e1 => decide (e1.2 = pw p))).map f).toFinset).image pw ∪
        ({l} : Finset (Fin M)).image lw)) = true := by
    intro gv hgv
    rcases hvars gv hgv with hp | hl
    · apply or_path n C _ _ _ (hf gv hgv hp).1
      rw [val_input _ _ _ (hpn _)]
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw
        (List.mem_toFinset.2 (List.mem_map.2
          ⟨gv, List.mem_filter.2 ⟨hgv, decide_eq_true hp⟩, rfl⟩))))
    · have hR := hleafR gv hgv
      rw [hl] at hR
      apply or_path n C _ _ _ hR
      rw [val_input _ _ _ (hln _)]
      exact decide_eq_true (Finset.mem_union_right _ (Finset.mem_image_of_mem lw
        (Finset.mem_singleton_self l)))
  have htrue : val C.gates C.output (fun k3 : Fin n => decide (k3.val ∈
      (((L.filter (fun e1 => decide (e1.2 = pw p))).map f).toFinset).image pw ∪
        ({l} : Finset (Fin M)).image lw)) = true := by
    apply or_path n C _ _ _ hR0
    apply and_true n C hC _ j0 hj0 hop0
    · exact transv n C hC _ _ L1 hT1 (fun gv hgv => hleaf gv (by rw [hL]; exact List.mem_append_left _ hgv))
    · exact transv n C hC _ _ L2 hT2 (fun gv hgv => hleaf gv (by rw [hL]; exact List.mem_append_right _ hgv))
  rw [htrue] at hs
  exact Bool.noConfusion hs

end PEqualNP.Outside.L_meta_2355

theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  intro n N M pw lw I C hC _ _ _ hpn hln hsound R hR T hT p l L _ htree
  subst hR
  subst hT
  exact PEqualNP.Outside.L_meta_2355.main n N M pw lw I C hC hpn hln hsound p l L htree
