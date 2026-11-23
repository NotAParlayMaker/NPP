import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta792

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma foldl_wiresStep_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    (gs.foldl wiresStep w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl wiresStep w).getD i false else false) := by
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
    have hget : gs[j] = g := (List.getElem?_eq_some_iff.mp hj).2
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hlt, hget]
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
  have hlen_take : (gs.take j).length = j := List.length_take_of_le hlt.le
  let wj := (gs.take j).foldl wiresStep w
  have hwj_len : wj.length = w.length + j := by
    rw [foldl_wiresStep_length, hlen_take]
  have hwj_lt : ∀ i < w.length + j, (gs.foldl wiresStep w).getD i false = wj.getD i false := by
    intro i hi
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact foldl_wiresStep_getD_lt _ _ i (hwj_len ▸ hi)
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_wiresStep_getD_lt _ _ _ (by change w.length + j < (wiresStep wj g).length; simp [wiresStep, hwj_len])]
  change (wiresStep wj g).getD (w.length + j) false = _
  simp only [wiresStep]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hwj_len])]
  simp only [hwj_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + j
  · simp only [hi, ↓reduceIte, hwj_lt i hi]
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length wj i (by rw [hwj_len]; omega)

private lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  change (C.gates.foldl wiresStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [foldl_wiresStep_getD_lt _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private lemma wires_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_wiresStep_gate C.gates (List.ofFn x) j g hg
  change (C.gates.foldl wiresStep (List.ofFn x)).getD (n + j) false =
    g.op.eval (g.inputs.map fun i =>
      if i < n + j then (C.gates.foldl wiresStep (List.ofFn x)).getD i false else false)
  simpa only [List.length_ofFn] using h

private def L {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

private inductive Reach (n : ℕ) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool) (r : ℕ) : ℕ → Prop
  | root : Reach n C Q ψ r (n + r)
  | step {j w : ℕ} (hj : j ∈ Q) (hreach : Reach n C Q ψ r (n + j))
      (g : Gate) (hg : C.gates[j]? = some g)
      (hw : w ∈ g.inputs) (hlt : w < n + j) (hψw : ψ w = false) :
      Reach n C Q ψ r w

private lemma reach_lt {n r : ℕ} {C : Circuit} {Q : Finset ℕ} {ψ : ℕ → Bool}
    (hQ : ∀ j ∈ Q, j < C.size) (hr : r ∈ Q) :
    ∀ w, Reach n C Q ψ r w → w < n + C.size := by
  intro w hw
  induction hw with
  | root =>
    have := hQ r hr
    omega
  | step hj _ g hg _ hlt _ =>
    have := hQ _ hj
    omega

private lemma reach_false {n r : ℕ} {C : Circuit} {Q : Finset ℕ} {ψ : ℕ → Bool}
    (hψr : ψ (n + r) = false) :
    ∀ w, Reach n C Q ψ r w → ψ w = false := by
  intro w hw
  induction hw with
  | root => exact hψr
  | step _ _ _ _ _ _ hψw => exact hψw

private lemma main_proof (n r : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ)
    (ψ : ℕ → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrQ : r ∈ Q)
    (hQ : ∀ j ∈ Q, j < C.size ∧ L (n := n) C (n + j) ⊆ S ∧ 2 ≤ (L (n := n) C (n + j)).card)
    (hclosed : ∀ j ∈ Q, ∀ j' : ℕ, j' < j →
      (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
      L (n := n) C (n + j') ⊆ S → 2 ≤ (L (n := n) C (n + j')).card → j' ∈ Q)
    (hψ : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false)))
    (hexit : ∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → L (n := n) C w ⊆ S)
    (hψr : ψ (n + r) = false) :
    (L (n := n) C (n + r)).card ≤ Q.card + 1 := by
  classical
  let V : Finset ℕ := (Finset.range (n + C.size)).filter (fun w => Reach n C Q ψ r w)
  let R : Finset ℕ := Q.filter (fun j => Reach n C Q ψ r (n + j))
  let E : Finset ℕ := V.filter (fun w => ∀ j ∈ Q, w ≠ n + j)
  have hV_mem : ∀ w, w ∈ V ↔ Reach n C Q ψ r w := by
    intro w
    simp only [V, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    exact reach_lt (fun j hj => (hQ j hj).1) hrQ w
  have hE_mem : ∀ w, w ∈ E ↔ Reach n C Q ψ r w ∧ ∀ j ∈ Q, w ≠ n + j := by
    intro w
    simp only [E, Finset.mem_filter, hV_mem]
  have hR_sub : R ⊆ Q := Finset.filter_subset _ _
  have hR_card : R.card ≤ Q.card := Finset.card_le_card hR_sub
  have hrR : r ∈ R := Finset.mem_filter.mpr ⟨hrQ, Reach.root⟩
  have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨r, hrR⟩
  have hV_eq : V = R.image (fun j => n + j) ∪ E := by
    ext w
    simp only [Finset.mem_union, Finset.mem_image, hV_mem, hE_mem, R, Finset.mem_filter]
    constructor
    · intro hw
      by_cases hq : ∃ j ∈ Q, w = n + j
      · obtain ⟨j, hj, rfl⟩ := hq
        exact Or.inl ⟨j, ⟨hj, hw⟩, rfl⟩
      · push Not at hq
        exact Or.inr ⟨hw, hq⟩
    · rintro (⟨j, ⟨_, hjr⟩, rfl⟩ | ⟨hw, _⟩) <;> assumption
  have hdisj : Disjoint (R.image (fun j => n + j)) E := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw1
    exact ((hE_mem (n + j)).mp hw2).2 j (hR_sub hj) rfl
  have hR_img_card : (R.image (fun j => n + j)).card = R.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    dsimp only at hab
    omega
  have hV_card : V.card = R.card + E.card := by
    rw [hV_eq, Finset.card_union_of_disjoint hdisj, hR_img_card]
  have hV_erase_card : (V.erase (n + r)).card ≤ 2 * R.card := by
    let ch : ℕ → Finset ℕ := fun j =>
      match C.gates[j]? with
      | some g => g.inputs.toFinset
      | none => ∅
    have hsub : V.erase (n + r) ⊆ R.biUnion ch := by
      intro w hw
      obtain ⟨hne, hwV⟩ := Finset.mem_erase.mp hw
      have hwr := (hV_mem w).mp hwV
      cases hwr with
      | root => exact absurd rfl hne
      | @step j _ hj hrj g hg hw_in _ _ =>
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hrj⟩, ?_⟩
        simp only [ch, hg]
        exact List.mem_toFinset.mpr hw_in
    have hch_card : ∀ j ∈ R, (ch j).card ≤ 2 := by
      intro j hj
      have hjQ := hR_sub hj
      have hjlt : j < C.gates.length := (hQ j hjQ).1
      let g := C.gates[j]'hjlt
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      simp only [ch, hg]
      have hlen := (hC g (List.mem_of_getElem? hg)).2
      exact (List.toFinset_card_le g.inputs).trans (by omega)
    calc (V.erase (n + r)).card
        ≤ (R.biUnion ch).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ R, (ch j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ R, 2 := Finset.sum_le_sum hch_card
      _ = 2 * R.card := by simp [mul_comm]
  have hnr_mem : n + r ∈ V := (hV_mem (n + r)).mpr Reach.root
  have hV_erase_eq : (V.erase (n + r)).card + 1 = V.card := Finset.card_erase_add_one hnr_mem
  have hE_le_Q : E.card ≤ Q.card + 1 := by omega
  have hL_exit : ∀ w ∈ E, (L (n := n) C w).card ≤ 1 := by
    intro w hwE
    obtain ⟨hwr, hnotQ⟩ := (hE_mem w).mp hwE
    have hψw : ψ w = false := reach_false hψr w hwr
    by_cases hwn : w < n
    · have hsub : L (n := n) C w ⊆ ({⟨w, hwn⟩} : Finset (Fin n)) := by
        intro p hp
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [wires_input C _ w hwn] at hp
        simp only [decide_eq_true_eq] at hp
        simp [hp]
      exact (Finset.card_le_card hsub).trans (by simp)
    · cases hwr with
      | root => exact absurd rfl (hnotQ r hrQ)
      | @step j _ hjQ _ g hg hw_in hlt _ =>
        obtain ⟨j', rfl⟩ : ∃ j', w = n + j' := ⟨w - n, by omega⟩
        have hj'notQ : j' ∉ Q := fun hj'Q => hnotQ j' hj'Q rfl
        have hsubS : L (n := n) C (n + j') ⊆ S := hexit (n + j') hnotQ hψw
        have hj'lt : j' < j := by omega
        by_contra h2
        push Not at h2
        exact hj'notQ (hclosed j hjQ j' hj'lt ⟨g, hg, hw_in⟩ hsubS h2)
  have hL_cover : ∀ w, Reach n C Q ψ r w → L (n := n) C w ⊆ E.biUnion (L (n := n) C) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwr
      by_cases hq : ∃ j ∈ Q, w = n + j
      · obtain ⟨j, hjQ, rfl⟩ := hq
        have hjlt : j < C.gates.length := (hQ j hjQ).1
        let g := C.gates[j]'hjlt
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hψj := hψ j hjQ g hg
        have hψnj : ψ (n + j) = false := reach_false hψr (n + j) hwr
        rw [hψnj] at hψj
        have hg_prop := hC g (List.mem_of_getElem? hg)
        rcases hg_prop.1 with hand | hor
        · rw [hand] at hψj
          replace hψj := hψj.symm
          simp only [GateOp.eval, List.all_map] at hψj
          rw [← Bool.not_eq_true, List.all_eq_true] at hψj
          push Not at hψj
          obtain ⟨u, hu_in, hu_false⟩ := hψj
          simp only [Function.comp_apply, id_eq, Bool.not_eq_true] at hu_false
          have hult : u < n + j := by
            by_contra hge
            have hL2 := (hQ j hjQ).2.2
            have hLempty : L (n := n) C (n + j) = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro p hp
              simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hp
              rw [wires_gate C _ j g hg, hand] at hp
              simp only [GateOp.eval, List.all_map, Function.comp_apply, id_eq,
                List.all_eq_true] at hp
              have := hp u hu_in
              simp [hge] at this
            rw [hLempty, Finset.card_empty] at hL2
            omega
          simp only [hult, ↓reduceIte] at hu_false
          have hur : Reach n C Q ψ r u := Reach.step hjQ hwr g hg hu_in hult hu_false
          have hsub : L (n := n) C (n + j) ⊆ L (n := n) C u := by
            intro p hp
            simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
            rw [wires_gate C _ j g hg, hand] at hp
            simp only [GateOp.eval, List.all_map, Function.comp_apply, id_eq,
              List.all_eq_true] at hp
            have := hp u hu_in
            simpa [hult] using this
          exact hsub.trans (ih u hult hur)
        · rw [hor] at hψj
          replace hψj := hψj.symm
          simp only [GateOp.eval, List.any_map] at hψj
          rw [← Bool.not_eq_true, List.any_eq_true] at hψj
          push Not at hψj
          intro p hp
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rw [wires_gate C _ j g hg, hor] at hp
          simp only [GateOp.eval, List.any_map, Function.comp_apply, id_eq,
            List.any_eq_true] at hp
          obtain ⟨u, hu_in, hup⟩ := hp
          by_cases hult : u < n + j
          · simp only [hult, ↓reduceIte] at hup
            have hu_false : ψ u = false := by
              have := hψj u hu_in
              simpa [hult, Bool.not_eq_true] using this
            have hur : Reach n C Q ψ r u := Reach.step hjQ hwr g hg hu_in hult hu_false
            exact ih u hult hur (by simpa [L] using hup)
          · simp [hult] at hup
      · push Not at hq
        have hwE : w ∈ E := (hE_mem w).mpr ⟨hwr, hq⟩
        exact Finset.subset_biUnion_of_mem (L (n := n) C) hwE
  calc (L (n := n) C (n + r)).card
      ≤ (E.biUnion (L (n := n) C)).card := Finset.card_le_card (hL_cover (n + r) Reach.root)
    _ ≤ ∑ w ∈ E, (L (n := n) C w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ E, 1 := Finset.sum_le_sum hL_exit
    _ = E.card := by simp
    _ ≤ Q.card + 1 := hE_le_Q

end PEqualNP.Outside.LMeta792

theorem PEqualNP.Outside.L_meta_792 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) → r ∈ Q → (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) → (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = false → (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 := by
  intro n r S C Q ψ hC _ hrQ hQ hclosed hψ hexit hψr
  exact PEqualNP.Outside.LMeta792.main_proof n r S C Q ψ hC hrQ hQ hclosed hψ hexit hψr
