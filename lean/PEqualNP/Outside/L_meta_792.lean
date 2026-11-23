import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_792

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

def sset (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

lemma sset_input_card (n : ℕ) (C : Circuit) (c : ℕ) (hc : c < n) :
    (sset n C c).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and, wires_input C _ c hc,
    decide_eq_true_eq] at ha hb
  exact ha.symm.trans hb

lemma gate_cover (n : ℕ) (C : Circuit) (ψ : ℕ → Bool) (k : ℕ) (g : Gate)
    (hg : C.gates[k]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hψ : ψ (n + k) = g.op.eval (g.inputs.map (fun w => if w < n + k then ψ w else false)))
    (hf : ψ (n + k) = false) (p : Fin n) (hp : p ∈ sset n C (n + k)) :
    ∃ c ∈ g.inputs, c < n + k ∧ ψ c = false ∧ p ∈ sset n C c := by
  simp only [sset, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  rw [wires_gate_ofFn C _ k g hg] at hp
  rw [hf] at hψ
  rcases hop with h | h
  · rw [h] at hp hψ
    simp only [GateOp.eval, List.all_map] at hp hψ
    rw [List.all_eq_true] at hp
    obtain ⟨c, hc, hcf⟩ := List.all_eq_false.mp hψ.symm
    have hv := hp c hc
    by_cases hlt : c < n + k
    · simp only [Function.comp_apply, hlt, ↓reduceIte, id_eq] at hv hcf
      exact ⟨c, hc, hlt, by simpa using hcf, hv⟩
    · simp [hlt] at hv
  · rw [h] at hp hψ
    simp only [GateOp.eval, List.any_map] at hp hψ
    obtain ⟨c, hc, hv⟩ := List.any_eq_true.mp hp
    have hcf := List.any_eq_false.mp hψ.symm c hc
    by_cases hlt : c < n + k
    · simp only [Function.comp_apply, hlt, ↓reduceIte, id_eq] at hv hcf
      exact ⟨c, hc, hlt, by simpa using hcf, hv⟩
    · simp [hlt] at hv

theorem main (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool)
    (h1 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h4 : ∀ j ∈ Q, j < C.gates.length)
    (h5 : ∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
      sset n C (n + j') ⊆ S → 2 ≤ (sset n C (n + j')).card → j' ∈ Q)
    (h6 : ∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
      ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false)))
    (h7 : ∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → sset n C w ⊆ S) :
    ∀ k : ℕ, ∀ F : Finset ℕ,
      (∀ w ∈ F, (∃ j ∈ Q, w = n + j ∧ j < k ∧ ψ w = false) ∨ (sset n C w).card ≤ 1) →
      (F.biUnion (sset n C)).card ≤ F.card + (Q.filter (· < k)).card := by
  intro k
  induction k with
  | zero =>
    intro F hF
    have hF' : ∀ w ∈ F, (sset n C w).card ≤ 1 := by
      intro w hw
      rcases hF w hw with ⟨j, _, _, hj, _⟩ | h
      · omega
      · exact h
    calc (F.biUnion (sset n C)).card ≤ ∑ w ∈ F, (sset n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ F, 1 := Finset.sum_le_sum hF'
      _ = F.card := by simp
      _ ≤ _ := Nat.le_add_right _ _
  | succ k ih =>
    intro F hF
    have hmono : (Q.filter (· < k)).card ≤ (Q.filter (· < k + 1)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    by_cases hk : k ∈ Q ∧ n + k ∈ F ∧ ψ (n + k) = false
    · obtain ⟨hkQ, hkF, hkψ⟩ := hk
      have hklt : k < C.gates.length := h4 k hkQ
      have hg : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hklt
      have hgmem : C.gates[k] ∈ C.gates := List.getElem_mem hklt
      obtain ⟨hop, hlen⟩ := h1 _ hgmem
      have hDcard : ((C.gates[k]).inputs.toFinset.filter
          (fun c => c < n + k ∧ ψ c = false)).card ≤ 2 := by
        calc _ ≤ (C.gates[k]).inputs.toFinset.card := Finset.card_filter_le _ _
          _ ≤ (C.gates[k]).inputs.length := List.toFinset_card_le _
          _ = 2 := hlen
      have hF'card : (F.erase (n + k) ∪ (C.gates[k]).inputs.toFinset.filter
          (fun c => c < n + k ∧ ψ c = false)).card ≤ F.card + 1 := by
        have h1' := Finset.card_union_le (F.erase (n + k))
          ((C.gates[k]).inputs.toFinset.filter (fun c => c < n + k ∧ ψ c = false))
        have h2' := Finset.card_erase_of_mem hkF
        have h3' : 0 < F.card := Finset.card_pos.mpr ⟨_, hkF⟩
        omega
      have hF'hyp : ∀ w ∈ F.erase (n + k) ∪ (C.gates[k]).inputs.toFinset.filter
          (fun c => c < n + k ∧ ψ c = false),
          (∃ j ∈ Q, w = n + j ∧ j < k ∧ ψ w = false) ∨ (sset n C w).card ≤ 1 := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨hne, hwF⟩ := Finset.mem_erase.mp hw
          rcases hF w hwF with ⟨j, hjQ, rfl, hjk, hψw⟩ | h
          · left
            have hjne : j ≠ k := fun h => hne (by rw [h])
            exact ⟨j, hjQ, rfl, by omega, hψw⟩
          · right; exact h
        · simp only [Finset.mem_filter, List.mem_toFinset] at hw
          obtain ⟨hwin, hwlt, hwψ⟩ := hw
          by_cases hq : ∃ j ∈ Q, w = n + j
          · obtain ⟨j, hjQ, rfl⟩ := hq
            left; exact ⟨j, hjQ, rfl, by omega, hwψ⟩
          · right
            push Not at hq
            have hsub := h7 w hq hwψ
            by_contra hc
            push Not at hc
            by_cases hwn : w < n
            · have := sset_input_card n C w hwn
              omega
            · obtain ⟨j', rfl⟩ : ∃ j', w = n + j' := ⟨w - n, by omega⟩
              have hj'Q := h5 k hkQ j' (by omega) ⟨_, hg, hwin⟩ hsub hc
              exact hq j' hj'Q rfl
      have hsub : F.biUnion (sset n C) ⊆ (F.erase (n + k) ∪ (C.gates[k]).inputs.toFinset.filter
          (fun c => c < n + k ∧ ψ c = false)).biUnion (sset n C) := by
        intro p hp
        obtain ⟨w, hwF, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases hwk : w = n + k
        · subst hwk
          obtain ⟨c, hc, hclt, hcψ, hpc⟩ :=
            gate_cover n C ψ k _ hg hop (h6 k hkQ _ hg) hkψ p hpw
          refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_right _ ?_, hpc⟩
          simp only [Finset.mem_filter, List.mem_toFinset]
          exact ⟨hc, hclt, hcψ⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hwF⟩), hpw⟩
      have hQ : (Q.filter (· < k)).card + 1 ≤ (Q.filter (· < k + 1)).card := by
        have hins : insert k (Q.filter (· < k)) ⊆ Q.filter (· < k + 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_filter] at hx ⊢
          rcases hx with rfl | ⟨hxQ, hxk⟩
          · exact ⟨hkQ, by omega⟩
          · exact ⟨hxQ, by omega⟩
        have hnot : k ∉ Q.filter (· < k) := by simp
        have hc := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hnot] at hc
        exact hc
      have hih := ih _ hF'hyp
      have hle := Finset.card_le_card hsub
      omega
    · have hF2 : ∀ w ∈ F,
          (∃ j ∈ Q, w = n + j ∧ j < k ∧ ψ w = false) ∨ (sset n C w).card ≤ 1 := by
        intro w hw
        rcases hF w hw with ⟨j, hjQ, rfl, hjk, hψw⟩ | h
        · left
          have hjne : j ≠ k := fun h => hk ⟨h ▸ hjQ, h ▸ hw, h ▸ hψw⟩
          exact ⟨j, hjQ, rfl, by omega, hψw⟩
        · right; exact h
      have hih := ih F hF2
      omega

end PEqualNP.Outside.L_meta_792

theorem PEqualNP.Outside.L_meta_792 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true → p ∈ S) → r ∈ Q → (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) → (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = false → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = false → (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (n + r) false = true)).card ≤ Q.card + 1 := by
  intro n r S C Q ψ h1 h2 h3 h4 h5 h6 h7 h8
  have key := PEqualNP.Outside.L_meta_792.main n S C Q ψ h1 (fun j hj => (h4 j hj).1) h5 h6 h7
    C.size {n + r} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      subst hw
      left
      exact ⟨r, h3, rfl, (h4 r h3).1, h8⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at key
  have hfl : (Q.filter (· < C.size)).card ≤ Q.card := Finset.card_filter_le _ _
  show (PEqualNP.Outside.L_meta_792.sset n C (n + r)).card ≤ Q.card + 1
  omega
