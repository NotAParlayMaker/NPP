import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

theorem gen : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ i < n, ∃ x : List Bool, x.length = n ∧ C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) → n ≤ C.size + 1 := by
  intro n C hfan hdep
  let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have hsub : Finset.range n ⊆ S := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hni
    obtain ⟨x, hx, hne⟩ := hdep i hi
    apply hne
    let y := x.set i (!(x.getD i false))
    have hy : y.length = n := by simp [y, hx]
    have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y D0
      (by simp [D0, hx]) (by simp [D0, hy]) ?_ C.output ?_
    · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [wires_eq, wires_eq]; exact key
    · intro w hw
      by_cases hwn : w < n
      · apply hw w
        simp [D0, List.getD_eq_getElem?_getD, hwn]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · intro j hj
      have hji : j ≠ i := fun e => hni (e ▸ hj)
      simp only [y]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hji)]
  have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have := Finset.card_le_card hsub
  rw [Finset.card_range] at this
  change n ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at this
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega

theorem set_ofFn {n : ℕ} (z : Fin n → Bool) (k : Fin n) (b : Bool) :
    (List.ofFn z).set k.val b = List.ofFn (Function.update z k b) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
    by_cases h : k.val = i
    · subst h; simp
    · rw [if_neg h, Function.update_of_ne]
      intro e; apply h; rw [← e]

theorem flip_ofFn {n : ℕ} (z : Fin n → Bool) (k : Fin n) :
    (List.ofFn z).set k.val (!((List.ofFn z).getD k.val false)) =
      List.ofFn (Function.update z k (!(z k))) := by
  have h : (List.ofFn z).getD k.val false = z k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]; simp
  rw [h]; exact set_ofFn z k _

theorem dep (N q : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hq : 1 ≤ q)
    (hacc : ∀ p1 l1 : Fin N, I p1 l1 → C.eval (List.ofFn (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1))) = true)
    (hsound : ∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → C.eval (List.ofFn z1) = false)
    (p l : Fin N) (hI : I p l) (k : Fin (N + N)) (hk : k = Fin.castAdd N p ∨ k = Fin.natAdd N l) :
    ∃ x : List Bool, x.length = N + N ∧ C.eval x ≠ C.eval (x.set k.val (!(x.getD k.val false))) := by
  refine ⟨List.ofFn (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)), by simp, ?_⟩
  rw [flip_ofFn, hacc p l hI]
  have hne : ∀ (a b : Fin N), Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b e
    have := congrArg Fin.val e
    simp at this
    omega
  suffices h : C.eval (List.ofFn (Function.update (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)) k (!(decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))))) = false by
    rw [h]; simp
  rcases hk with hk | hk
  · subst hk
    have hzp : ∀ p1 : Fin N, Function.update (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)) (Fin.castAdd N p) (!(decide (Fin.castAdd N p = Fin.castAdd N p ∨ Fin.castAdd N p = Fin.natAdd N l))) (Fin.castAdd N p1) = false := by
      intro p1
      rw [Function.update_apply]
      split_ifs with h
      · simp
      · rw [decide_eq_false_iff_not]
        rintro (h1 | h1)
        · exact h h1
        · exact hne _ _ h1
    have hzl : ∀ l1 : Fin N, Function.update (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)) (Fin.castAdd N p) (!(decide (Fin.castAdd N p = Fin.castAdd N p ∨ Fin.castAdd N p = Fin.natAdd N l))) (Fin.natAdd N l1) = true → l1 = l := by
      intro l1
      rw [Function.update_apply, if_neg (fun e => hne _ _ e.symm), decide_eq_true_iff]
      rintro (h1 | h1)
      · exact absurd h1.symm (hne _ _)
      · have := congrArg Fin.val h1
        simp at this
        exact Fin.ext this
    apply hsound
    · refine le_trans (Finset.card_le_card (t := {l}) ?_) (by simpa using hq)
      intro l1 hl1
      rw [Finset.mem_filter] at hl1
      rw [Finset.mem_singleton]
      exact hzl l1 hl1.2
    · rintro ⟨p1, l1, _, h1, _⟩
      rw [hzp p1] at h1
      exact Bool.false_ne_true h1
  · subst hk
    have hzl : ∀ l1 : Fin N, Function.update (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)) (Fin.natAdd N l) (!(decide (Fin.natAdd N l = Fin.castAdd N p ∨ Fin.natAdd N l = Fin.natAdd N l))) (Fin.natAdd N l1) = false := by
      intro l1
      rw [Function.update_apply]
      split_ifs with h
      · simp
      · rw [decide_eq_false_iff_not]
        rintro (h1 | h1)
        · exact hne _ _ h1.symm
        · exact h h1
    apply hsound
    · have : (Finset.univ.filter (fun l1b : Fin N => Function.update (fun k1 : Fin (N + N) => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)) (Fin.natAdd N l) (!(decide (Fin.natAdd N l = Fin.castAdd N p ∨ Fin.natAdd N l = Fin.natAdd N l))) (Fin.natAdd N l1b) = true)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro l1 _
        rw [hzl l1]
        exact Bool.false_ne_true
      rw [this]
      simp
    · rintro ⟨p1, l1, _, _, h1⟩
      rw [hzl l1] at h1
      exact Bool.false_ne_true h1

end PEqualNP.Outside.L_meta_1660

open PEqualNP.Outside.L_meta_1660 in
theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hline huniq hmono hrb hacc hsound
  have hgen := gen (N + N) C (fun g hg => (hmono g hg).2) ?_
  · omega
  have hN2 : 2 ≤ N := by
    have : 0 ≤ q ^ 2 := Nat.zero_le _
    omega
  have hpt : ∀ p : Fin N, ∃ l, I p l := by
    intro p
    obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p ≠ p' := by
      by_cases h : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun e => by have := congrArg Fin.val e; simp at this; omega⟩
    obtain ⟨l, ⟨hl, _⟩, _⟩ := huniq p p' hp'
    exact ⟨l, hl⟩
  have hln : ∀ l : Fin N, ∃ p, I p l := by
    intro l
    have h1 := hline l
    have hpos : 0 < (Finset.univ.filter (fun p0 => I p0 l)).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  intro i hi
  by_cases hiN : i < N
  · obtain ⟨l, hl⟩ := hpt ⟨i, hiN⟩
    exact dep N q I C (by omega) hacc hsound ⟨i, hiN⟩ l hl ⟨i, hi⟩ (Or.inl (Fin.ext rfl))
  · obtain ⟨p, hp⟩ := hln ⟨i - N, by omega⟩
    exact dep N q I C (by omega) hacc hsound p ⟨i - N, by omega⟩ hp ⟨i, hi⟩
      (Or.inr (Fin.ext (by simp; omega)))
