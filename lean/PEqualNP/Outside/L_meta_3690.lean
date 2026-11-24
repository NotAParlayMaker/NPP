import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3690

open PEqualNP.CircuitLowerBounds

def run {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs : List Gate) (w : List α) :
    List α :=
  gs.foldl (fun w g => w ++ [f w.length g (g.inputs.map fun i => w.getD i d)]) w

theorem run_cons {α : Type} (f : ℕ → Gate → List α → α) (d : α) (g : Gate) (gs : List Gate)
    (w : List α) :
    run f d (g :: gs) w = run f d gs (w ++ [f w.length g (g.inputs.map fun i => w.getD i d)]) :=
  rfl

theorem run_append {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs1 gs2 : List Gate)
    (w : List α) : run f d (gs1 ++ gs2) w = run f d gs2 (run f d gs1 w) := by
  simp only [run, List.foldl_append]

theorem run_length {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs : List Gate)
    (w : List α) : (run f d gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem run_getD_lt {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs : List Gate)
    (w : List α) (i : ℕ) (hi : i < w.length) : (run f d gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem run_getD_ge {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs : List Gate)
    (w : List α) (i : ℕ) (hi : w.length + gs.length ≤ i) : (run f d gs w).getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [run_length]; omega)]
  rfl

theorem run_getD_gate {α : Type} (f : ℕ → Gate → List α → α) (d : α) (gs : List Gate)
    (w : List α) (j : ℕ) (hj : j < gs.length) (hread : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (run f d gs w).getD (w.length + j) d =
      f (w.length + j) gs[j] (gs[j].inputs.map fun i => (run f d gs w).getD i d) := by
  have hsplit : run f d gs w = run f d (gs.drop (j + 1))
      (run f d (gs.take j) w ++ [f (run f d (gs.take j) w).length gs[j]
        (gs[j].inputs.map fun i => (run f d (gs.take j) w).getD i d)]) := by
    calc run f d gs w = run f d (gs.take j ++ (gs[j] :: gs.drop (j + 1))) w := by
          rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
      _ = _ := by rw [run_append, run_cons]
  have hl1 : (run f d (gs.take j) w).length = w.length + j := by
    rw [run_length, List.length_take, Nat.min_eq_left hj.le]
  have hv : ∀ v : α, (run f d (gs.take j) w ++ [v]).getD (w.length + j) d = v := by
    intro v
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl1]
    simp
  rw [hsplit, run_getD_lt f d (gs.drop (j + 1)) _ (w.length + j)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega), hv, hl1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hr := hread i hi
  rw [run_getD_lt f d (gs.drop (j + 1)) _ i
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
    List.getD_append _ _ _ _ (by omega)]

theorem mem_U {l : List (Finset ℕ)} {a : ℕ} :
    a ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, a ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

def SpL (N : ℕ) (C : Circuit) : List (Finset ℕ) :=
  run (fun _ _ ss => ss.foldr (· ∪ ·) ∅) ∅ C.gates ((List.range N).map fun i => ({i} : Finset ℕ))

def KcL (N : ℕ) (C : Circuit) : List (Finset ℕ) :=
  run (fun len _ ks => insert (len - N) (ks.foldr (· ∪ ·) ∅)) ∅ C.gates (List.replicate N ∅)

theorem wires_eq_run (C : Circuit) (x : List Bool) :
    C.wires x = run (fun _ g vs => g.op.eval vs) false C.gates x := rfl

theorem gateAt_eq (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]

theorem len_sp (N : ℕ) : ((List.range N).map fun i => ({i} : Finset ℕ)).length = N := by simp

theorem Sp_in (N : ℕ) (C : Circuit) (u : ℕ) (hu : u < N) : (SpL N C).getD u ∅ = {u} := by
  rw [SpL, run_getD_lt _ _ _ _ _ (by rw [len_sp]; exact hu)]
  simp [List.getD_eq_getElem?_getD, hu]

theorem Sp_ge (N : ℕ) (C : Circuit) (u : ℕ) (hu : N + C.gates.length ≤ u) :
    (SpL N C).getD u ∅ = ∅ :=
  run_getD_ge _ _ _ _ _ (by rw [len_sp]; exact hu)

theorem Sp_gate (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j)
    (j : ℕ) (hj : j < C.gates.length) :
    (SpL N C).getD (N + j) ∅ =
      (C.gates[j].inputs.map fun i => (SpL N C).getD i ∅).foldr (· ∪ ·) ∅ := by
  have h := run_getD_gate (fun _ _ ss => ss.foldr (· ∪ ·) ∅) (∅ : Finset ℕ) C.gates
    ((List.range N).map fun i => ({i} : Finset ℕ)) j hj (by rw [len_sp]; exact H j hj)
  rw [len_sp] at h
  exact h

theorem Kc_in (N : ℕ) (C : Circuit) (u : ℕ) (hu : u < N) : (KcL N C).getD u ∅ = ∅ := by
  rw [KcL, run_getD_lt _ _ _ _ _ (by rw [List.length_replicate]; exact hu)]
  simp [List.getD_eq_getElem?_getD, hu]

theorem Kc_ge (N : ℕ) (C : Circuit) (u : ℕ) (hu : N + C.gates.length ≤ u) :
    (KcL N C).getD u ∅ = ∅ :=
  run_getD_ge _ _ _ _ _ (by rw [List.length_replicate]; exact hu)

theorem Kc_gate (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j)
    (j : ℕ) (hj : j < C.gates.length) :
    (KcL N C).getD (N + j) ∅ =
      insert j ((C.gates[j].inputs.map fun i => (KcL N C).getD i ∅).foldr (· ∪ ·) ∅) := by
  have h := run_getD_gate (fun len _ ks => insert (len - N) (ks.foldr (· ∪ ·) ∅))
    (∅ : Finset ℕ) C.gates (List.replicate N ∅) j hj
    (by rw [List.length_replicate]; exact H j hj)
  rw [List.length_replicate] at h
  rw [KcL, h]
  simp only [Nat.add_sub_cancel_left]

theorem V_in (N : ℕ) (C : Circuit) (x : Fin N → Bool) (u : ℕ) (hu : u < N) :
    (C.wires (List.ofFn x)).getD u false = x ⟨u, hu⟩ := by
  rw [wires_eq_run, run_getD_lt _ _ _ _ _ (by rw [List.length_ofFn]; exact hu)]
  simp [List.getD_eq_getElem?_getD, hu]

theorem V_ge (N : ℕ) (C : Circuit) (x : Fin N → Bool) (u : ℕ) (hu : N + C.gates.length ≤ u) :
    (C.wires (List.ofFn x)).getD u false = false := by
  rw [wires_eq_run]
  exact run_getD_ge _ _ _ _ _ (by rw [List.length_ofFn]; exact hu)

theorem V_gate (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j)
    (x : Fin N → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (N + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have h := run_getD_gate (fun _ g vs => g.op.eval vs) false C.gates (List.ofFn x) j hj
    (by rw [List.length_ofFn]; exact H j hj)
  rw [List.length_ofFn] at h
  rw [wires_eq_run]
  exact h

theorem sem (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j)
    (x y : Fin N → Bool) (u : ℕ)
    (hag : ∀ i (hi : i < N), i ∈ (SpL N C).getD u ∅ → x ⟨i, hi⟩ = y ⟨i, hi⟩) :
    (C.wires (List.ofFn x)).getD u false = (C.wires (List.ofFn y)).getD u false := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u < N
    · rw [V_in N C x u hu, V_in N C y u hu]
      exact hag u hu (by rw [Sp_in N C u hu]; simp)
    by_cases hu2 : N + C.gates.length ≤ u
    · rw [V_ge N C x u hu2, V_ge N C y u hu2]
    obtain ⟨j, rfl⟩ : ∃ j, u = N + j := ⟨u - N, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [V_gate N C H x j hj, V_gate N C H y j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply ih i (H j hj i hi)
    intro i' hi' hmem
    apply hag i' hi'
    rw [Sp_gate N C H j hj]
    exact mem_U.2 ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hmem⟩

theorem KcRange (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j) (u : ℕ) :
    (KcL N C).getD u ∅ ⊆ Finset.range (u + 1 - N) := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u < N
    · rw [Kc_in N C u hu]; exact Finset.empty_subset _
    by_cases hu2 : N + C.gates.length ≤ u
    · rw [Kc_ge N C u hu2]; exact Finset.empty_subset _
    obtain ⟨j, rfl⟩ : ∃ j, u = N + j := ⟨u - N, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [Kc_gate N C H j hj]
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · simp only [Finset.mem_range]; omega
    · obtain ⟨s, hs, hzs⟩ := mem_U.1 hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
      have hlt := H j hj i hi
      have h3 := ih i hlt hzs
      simp only [Finset.mem_range] at h3 ⊢
      omega

theorem count (N : ℕ) (C : Circuit)
    (H : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < N + j)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (k : ℕ) (hk : k ≤ C.gates.length)
    (W : Finset ℕ) (hW : ∀ u ∈ W, u < N + k) :
    (W.biUnion fun u => (SpL N C).getD u ∅).card ≤
      (W.biUnion fun u => (KcL N C).getD u ∅).card + W.card := by
  induction k generalizing W with
  | zero =>
    calc (W.biUnion fun u => (SpL N C).getD u ∅).card
        ≤ ∑ u ∈ W, ((SpL N C).getD u ∅).card := Finset.card_biUnion_le
      _ = ∑ u ∈ W, 1 := Finset.sum_congr rfl (fun u hu => by
          rw [Sp_in N C u (by have := hW u hu; omega)]; simp)
      _ = W.card := by simp
      _ ≤ _ := Nat.le_add_left _ _
  | succ k ih =>
    by_cases hmem : N + k ∈ W
    · have hkl : k < C.gates.length := by omega
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h2 _ (List.getElem_mem hkl))
      have ha : a < N + k := H k hkl a (by rw [hab]; simp)
      have hb : b < N + k := H k hkl b (by rw [hab]; simp)
      have hSpk : (SpL N C).getD (N + k) ∅ = (SpL N C).getD a ∅ ∪ (SpL N C).getD b ∅ := by
        rw [Sp_gate N C H k hkl, hab]; simp
      have hKck : (KcL N C).getD (N + k) ∅ =
          insert k ((KcL N C).getD a ∅ ∪ (KcL N C).getD b ∅) := by
        rw [Kc_gate N C H k hkl, hab]; simp
      have hW' : ∀ u ∈ insert a (insert b (W.erase (N + k))), u < N + k := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_erase] at hu
        rcases hu with rfl | rfl | ⟨hne, hu⟩
        · exact ha
        · exact hb
        · have := hW u hu; omega
      have ih' := ih (by omega) _ hW'
      have hsub : (W.biUnion fun u => (SpL N C).getD u ∅) ⊆
          ((insert a (insert b (W.erase (N + k)))).biUnion fun u => (SpL N C).getD u ∅) := by
        intro z hz
        obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.1 hz
        by_cases hu' : u = N + k
        · subst hu'
          rw [hSpk] at hzu
          rcases Finset.mem_union.1 hzu with h | h
          · exact Finset.mem_biUnion.2 ⟨a, by simp, h⟩
          · exact Finset.mem_biUnion.2 ⟨b, by simp, h⟩
        · exact Finset.mem_biUnion.2 ⟨u, by simp [hu, hu'], hzu⟩
      have hcone : insert k ((insert a (insert b (W.erase (N + k)))).biUnion
          fun u => (KcL N C).getD u ∅) ⊆ (W.biUnion fun u => (KcL N C).getD u ∅) := by
        intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hz
        · exact Finset.mem_biUnion.2 ⟨N + z, hmem, by rw [hKck]; simp⟩
        · obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.1 hz
          simp only [Finset.mem_insert, Finset.mem_erase] at hu
          rcases hu with rfl | rfl | ⟨_, hu⟩
          · exact Finset.mem_biUnion.2 ⟨N + k, hmem, by
              rw [hKck]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hzu)⟩
          · exact Finset.mem_biUnion.2 ⟨N + k, hmem, by
              rw [hKck]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hzu)⟩
          · exact Finset.mem_biUnion.2 ⟨u, hu, hzu⟩
      have hknot : k ∉ ((insert a (insert b (W.erase (N + k)))).biUnion
          fun u => (KcL N C).getD u ∅) := by
        intro hz
        obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.1 hz
        have h3 := KcRange N C H u hzu
        have h4 := hW' u hu
        simp only [Finset.mem_range] at h3
        omega
      have hc1 := Finset.card_le_card hcone
      rw [Finset.card_insert_of_notMem hknot] at hc1
      have hcW : (insert a (insert b (W.erase (N + k)))).card ≤ W.card + 1 := by
        have e1 := Finset.card_insert_le a (insert b (W.erase (N + k)))
        have e2 := Finset.card_insert_le b (W.erase (N + k))
        have e3 := Finset.card_erase_of_mem hmem
        have e4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      have hs := Finset.card_le_card hsub
      omega
    · exact ih (by omega) W (fun u hu => by
        have h5 := hW u hu
        have h6 : u ≠ N + k := fun h => hmem (h ▸ hu)
        omega)

end PEqualNP.Outside.L_meta_3690

theorem PEqualNP.Outside.L_meta_3690 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), (x5, x3 x5) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), (x8, x9) ∈ x2 ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 hmatch hAO hfun
  unfold PEqualNP.TopForm.IsAO2 at hAO
  obtain ⟨_, hrb, h2⟩ := hAO
  have H : ∀ j (hj : j < x4.gates.length), ∀ i ∈ x4.gates[j].inputs, i < (x1 + x1) + j :=
    fun j hj i hi => hrb j hj i (by rw [PEqualNP.Outside.L_meta_3690.gateAt_eq x4 hj]; exact hi)
  have hne : ∀ a b : Fin x1, Fin.castAdd x1 a ≠ Fin.natAdd x1 b := by
    intro a b h
    have := congrArg Fin.val h
    simp at this
    omega
  have hsingle : ∀ v : Fin (x1 + x1),
      PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 (fun i => decide (i = v)) = false := by
    intro v
    rw [hfun]
    simp only [decide_eq_false_iff_not]
    rintro ⟨a, b, _, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    exact hne a b (ha.trans hb.symm)
  have ess : ∀ u v : Fin (x1 + x1),
      PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 (fun i => decide (i = u ∨ i = v)) = true →
      u.val ∈ (PEqualNP.Outside.L_meta_3690.SpL (x1 + x1) x4).getD x4.output ∅ := by
    intro u v h1
    by_contra hno
    have heq : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 (fun i => decide (i = u ∨ i = v)) =
        PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 (fun i => decide (i = v)) :=
      PEqualNP.Outside.L_meta_3690.sem (x1 + x1) x4 H _ _ x4.output (by
        intro i hi hiS
        have hn : (⟨i, hi⟩ : Fin (x1 + x1)) ≠ u := fun h => hno (by rw [← h]; exact hiS)
        simp [hn])
    rw [heq, hsingle] at h1
    exact Bool.false_ne_true h1
  have hall : ∀ p : Fin (x1 + x1),
      p.val ∈ (PEqualNP.Outside.L_meta_3690.SpL (x1 + x1) x4).getD x4.output ∅ := by
    intro p
    induction p using Fin.addCases with
    | left a =>
      apply ess _ (Fin.natAdd x1 (x3 a))
      rw [hfun]
      exact decide_eq_true ⟨a, x3 a, hmatch a, by simp, by simp⟩
    | right b =>
      apply ess _ (Fin.castAdd x1 (x3.symm b))
      rw [hfun]
      refine decide_eq_true ⟨x3.symm b, b, ?_, by simp, by simp⟩
      have hm := hmatch (x3.symm b)
      rwa [Equiv.apply_symm_apply] at hm
  have hcardT : x1 + x1 ≤ ((PEqualNP.Outside.L_meta_3690.SpL (x1 + x1) x4).getD x4.output ∅).card := by
    have hs : Finset.range (x1 + x1) ⊆
        (PEqualNP.Outside.L_meta_3690.SpL (x1 + x1) x4).getD x4.output ∅ := by
      intro i hi
      exact hall ⟨i, Finset.mem_range.1 hi⟩
    simpa using Finset.card_le_card hs
  show 2 * x1 ≤ x4.gates.length + 1
  by_cases ho : x4.output < x1 + x1 + x4.gates.length
  · have hc := PEqualNP.Outside.L_meta_3690.count (x1 + x1) x4 H h2 x4.gates.length le_rfl
      {x4.output} (by intro u hu; rw [Finset.mem_singleton] at hu; omega)
    simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
    have hK := Finset.card_le_card (PEqualNP.Outside.L_meta_3690.KcRange (x1 + x1) x4 H x4.output)
    rw [Finset.card_range] at hK
    omega
  · rw [PEqualNP.Outside.L_meta_3690.Sp_ge (x1 + x1) x4 _ (by omega)] at hcardT
    simp at hcardT
    omega
