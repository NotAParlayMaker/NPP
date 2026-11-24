import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4039_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

lemma mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hk)
        generalize gs[k] = g at hi hop hlen ⊢
        obtain ⟨op, ins⟩ := g
        simp only at hi hop hlen ⊢
        have rd : ∀ a : ℕ, (if a < n + k then val gs x a else false) = true →
            (if a < n + k then val gs x' a else false) = true := by
          intro a ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)
        match ins, hlen with
        | [], _ =>
          rcases hop with rfl | rfl
          · simp [GateOp.eval]
          · simp [GateOp.eval] at hi
        | [a], _ =>
          rcases hop with rfl | rfl
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
          · have h := rd a (by simpa [GateOp.eval] using hi)
            simpa [GateOp.eval] using h
        | [a, b], _ =>
          rcases hop with rfl | rfl
          · have h : (if a < n + k then val gs x a else false) = true ∧
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            have h1 := rd a h.1
            have h2 := rd b h.2
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              Bool.and_true, id_eq, Bool.and_eq_true]
            exact ⟨h1, h2⟩
          · have h : (if a < n + k then val gs x a else false) = true ∨
                (if b < n + k then val gs x b else false) = true := by
              simpa [GateOp.eval] using hi
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              Bool.or_false, id_eq, Bool.or_eq_true]
            rcases h with h | h
            · exact Or.inl (rd a h)
            · exact Or.inr (rd b h)
        | _ :: _ :: _ :: _, h => simp at h


def ind {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ S)

lemma ind_mono {n : ℕ} (S T : Finset (Fin n)) (h : S ⊆ T) :
    ∀ v, ind S v = true → ind T v = true := by
  intro v hv
  simp only [ind, decide_eq_true_eq] at hv ⊢
  exact h hv

-- below the first true AND gate, a true wire is already true at one element of S
lemma single {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (k0 : ℕ)
    (hmin : ∀ j, j < k0 → ∀ hj : j < gs.length, gs[j].op = GateOp.and →
      val gs (ind S) (n + j) ≠ true) :
    ∀ w, w < n + k0 → val gs (ind S) w = true →
      ∃ i ∈ S, val gs (ind {i}) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hi
    by_cases h1 : w < n
    · rw [val_lt gs _ w h1] at hi
      refine ⟨⟨w, h1⟩, ?_, ?_⟩
      · simpa [ind] using hi
      · rw [val_lt gs _ w h1]
        simp [ind]
    · by_cases h2 : n + gs.length ≤ w
      · rw [val_ge gs _ w h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gs.length := by omega
        have hk0 : k < k0 := by omega
        rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
        · exact absurd hi (hmin k hk0 hk hop)
        · rw [val_gate gs _ k hk, hop] at hi
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi
          obtain ⟨b, ⟨a, ha, hab⟩, hb⟩ := hi
          subst hab
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at hb
            obtain ⟨i, hiS, hv⟩ := ih a hlt (by omega) hb
            refine ⟨i, hiS, ?_⟩
            rw [val_gate gs _ k hk, hop]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            exact ⟨_, ⟨a, ha, rfl⟩, by rw [if_pos hlt]; exact hv⟩
          · rw [if_neg hlt] at hb
            exact absurd hb (by simp)

lemma gather {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (l : List ℕ)
    (h : ∀ a ∈ l, ∃ i ∈ S, val gs (ind {i}) a = true) :
    ∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≤ l.length ∧ ∀ a ∈ l, val gs (ind T) a = true := by
  induction l with
  | nil => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | cons a l ih =>
    obtain ⟨T, hTS, hTc, hT⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    obtain ⟨i, hiS, hv⟩ := h a (List.mem_cons_self)
    refine ⟨insert i T, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hiS hTS
    · have := Finset.card_insert_le i T
      simp only [List.length_cons]
      omega
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact mono gs hg _ _ (ind_mono _ _ (by simp)) _ hv
      · exact mono gs hg _ _ (ind_mono _ _ (Finset.subset_insert _ _)) _ (hT b hb)

lemma core {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (k : ℕ) (hk : k < gs.length) (hop : gs[k].op = GateOp.and)
    (hv : val gs (ind S) (n + k) = true) :
    ∃ T ⊆ S, T.card ≤ 2 ∧ ∃ k', ∃ hk' : k' < gs.length, gs[k'].op = GateOp.and ∧
      val gs (ind T) (n + k') = true := by
  classical
  have hex : ∃ j, ∃ hj : j < gs.length, gs[j].op = GateOp.and ∧ val gs (ind S) (n + j) = true :=
    ⟨k, hk, hop, hv⟩
  obtain ⟨hk0, hop0, hv0⟩ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → ∀ hj : j < gs.length, gs[j].op = GateOp.and →
      val gs (ind S) (n + j) ≠ true := by
    intro j hj hjl hjop hjv
    exact Nat.find_min hex hj ⟨hjl, hjop, hjv⟩
  generalize Nat.find hex = k0 at hk0 hop0 hv0 hmin
  have hall : ∀ a ∈ gs[k0].inputs, a < n + k0 ∧ val gs (ind S) a = true := by
    intro a ha
    rw [val_gate gs _ k0 hk0, hop0] at hv0
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hv0
    have h := hv0 _ ⟨a, ha, rfl⟩
    by_cases hlt : a < n + k0
    · rw [if_pos hlt] at h
      exact ⟨hlt, h⟩
    · rw [if_neg hlt] at h
      exact absurd h (by simp)
  obtain ⟨T, hTS, hTc, hT⟩ := gather gs hg S gs[k0].inputs
    (fun a ha => single gs hg S k0 hmin a (hall a ha).1 (hall a ha).2)
  refine ⟨T, hTS, le_trans hTc (hg _ (List.getElem_mem hk0)).2, k0, hk0, hop0, ?_⟩
  rw [val_gate gs _ k0 hk0, hop0]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  rintro b ⟨a, ha, rfl⟩
  rw [if_pos (hall a ha).1]
  exact hT a ha

lemma main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 x2 →
    ∀ (x5 : Finset (Fin x1)),
      (∃ (x5' : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5']? = Option.some x6 ∧
        x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x5))).getD (x1 + x5') Bool.false = Bool.true) →
      ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧
        ∃ (x5' : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5']? = Option.some x6 ∧
          x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (x2.wires (List.ofFn fun (x8 : Fin x1) => Decidable.decide (x8 ∈ x7))).getD (x1 + x5') Bool.false = Bool.true := by
  intro n C hM S ⟨k, g, hkg, hop, hv⟩
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    obtain ⟨h1, h2⟩ := hM g hgm
    refine ⟨?_, h2⟩
    simpa using h1
  obtain ⟨hk, hkeq⟩ := List.getElem?_eq_some_iff.mp hkg
  subst hkeq
  have hv' : val C.gates (ind S) (n + k) = true := hv
  obtain ⟨T, hTS, hTc, k', hk', hop', hv''⟩ := core C.gates hg S k hk hop hv'
  exact ⟨T, hTS, hTc, k', C.gates[k'], List.getElem?_eq_getElem hk', hop', hv''⟩

end PEqualNP.Outside.L_meta_4039_aux

theorem PEqualNP.Outside.L_meta_4039 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x4))).getD (x1 + x5) Bool.false = Bool.true;     ∀ (x5 : Finset (Fin x1)), x4 x5 → ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧ x4 x7 := by
  exact PEqualNP.Outside.L_meta_4039_aux.main
