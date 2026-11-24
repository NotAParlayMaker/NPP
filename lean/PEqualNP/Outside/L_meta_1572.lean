import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1572_aux

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


lemma descend {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∀ w, val gs x w = true → ∃ Y : ℕ,
      (∀ S : Set ℕ, w ∈ S → (∀ i : Fin gs.length, n + (i : ℕ) ∈ S →
        (gs.get i).op = GateOp.or → ∀ a ∈ (gs.get i).inputs, a ∈ S) → Y ∈ S) ∧
      val gs x Y = true ∧
      (Y < n ∨ ∃ i : Fin gs.length, Y = n + (i : ℕ) ∧ (gs.get i).op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · exact ⟨w, fun S hS _ => hS, hw, Or.inl h1⟩
    · by_cases h2 : w < n + gs.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gs.length := by omega
        rcases (hg gs[k] (List.getElem_mem hk)).1 with hop | hop
        · exact ⟨n + k, fun S hS _ => hS, hw, Or.inr ⟨⟨k, hk⟩, rfl, hop⟩⟩
        · rw [val_gate gs x k hk, hop] at hw
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hw
          obtain ⟨a, ha, hav⟩ := hw
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at hav
            obtain ⟨Y, hY1, hY2, hY3⟩ := ih a hlt hav
            exact ⟨Y, fun S hS hcl => hY1 S (hcl ⟨k, hk⟩ hS hop a ha) hcl, hY2, hY3⟩
          · rw [if_neg hlt] at hav
            exact absurd hav (by simp)
      · rw [val_ge gs x w (by omega)] at hw
        exact absurd hw (by simp)

lemma below {n : ℕ} (gs : List Gate)
    (hrb : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < n + (i : ℕ)) (g Y : ℕ)
    (hY : ∀ S : Set ℕ, g ∈ S → (∀ i : Fin gs.length, n + (i : ℕ) ∈ S →
        (gs.get i).op = GateOp.or → ∀ a ∈ (gs.get i).inputs, a ∈ S) → Y ∈ S) :
    ∀ x' : Fin n → Bool, val gs x' Y = true → val gs x' g = true := by
  have h := hY {w | ∀ x' : Fin n → Bool, val gs x' w = true → val gs x' g = true}
    (fun x' h => h) (by
      intro i hi hop a ha x' hax
      apply hi x'
      have hop' : gs[(i : ℕ)].op = GateOp.or := hop
      have ha' : a ∈ gs[(i : ℕ)].inputs := ha
      rw [val_gate gs x' i i.2, hop']
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
      exact ⟨a, ha', by rw [if_pos ((hrb i).2 a ha)]; exact hax⟩)
  exact h

lemma core (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrb : ∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧
      ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) (g : ℕ) (A B : Finset (Fin 13)) (c z e : Fin 13)
    (hAB : A ∩ B = {c}) (hzB : z ∉ B) (heA : e ∉ A)
    (hA : val gates (fun v : Fin 13 => decide (v ∉ A)) g = false)
    (hB : val gates (fun v : Fin 13 => decide (v ∉ B)) g = false)
    (h2 : 2 ≤ (A.filter (fun p =>
      val gates (fun v : Fin 13 => decide (v = p ∨ (p ≠ z ∧ v = e))) g = true)).card) :
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ z ∧ p ≠ c ∧
        val gates (fun v : Fin 13 => decide (v = p ∨ (p ≠ z ∧ v = e))) Y = true := by
  obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (A.filter (fun p =>
      val gates (fun v : Fin 13 => decide (v = p ∨ (p ≠ z ∧ v = e))) g = true)).card)
  rw [Finset.mem_filter] at hp hp'
  have hcA : c ∈ A := by
    have : c ∈ A ∩ B := by rw [hAB]; simp
    exact (Finset.mem_inter.mp this).1
  have hz : ∀ q : Fin 13,
      val gates (fun v : Fin 13 => decide (v = q ∨ (q ≠ z ∧ v = e))) g = true → q ≠ z := by
    intro q hq hqz
    subst hqz
    have := mono gates hg _ (fun v : Fin 13 => decide (v ∉ B)) (by
      intro v hv
      simp at hv
      simp [hv, hzB]) g hq
    rw [hB] at this
    exact absurd this (by simp)
  have main : ∀ q : Fin 13, q ∈ A →
      val gates (fun v : Fin 13 => decide (v = q ∨ (q ≠ z ∧ v = e))) g = true → q ≠ c →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
        (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
      (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
      ∃ p ∈ A, p ≠ z ∧ p ≠ c ∧
        val gates (fun v : Fin 13 => decide (v = p ∨ (p ≠ z ∧ v = e))) Y = true := by
    intro q hqA hq hqc
    obtain ⟨Y, hY1, hY2, hY3⟩ := descend gates hg _ g hq
    have hle := below gates hrb g Y hY1
    rcases hY3 with hlt | hand
    · exfalso
      have hYA : (⟨Y, hlt⟩ : Fin 13) ∈ A := by
        by_contra hn
        have := hle (fun v : Fin 13 => decide (v ∉ A)) (by rw [val_lt _ _ Y hlt]; simp [hn])
        rw [hA] at this
        exact absurd this (by simp)
      have hYB : (⟨Y, hlt⟩ : Fin 13) ∈ B := by
        by_contra hn
        have := hle (fun v : Fin 13 => decide (v ∉ B)) (by rw [val_lt _ _ Y hlt]; simp [hn])
        rw [hB] at this
        exact absurd this (by simp)
      have hYc : (⟨Y, hlt⟩ : Fin 13) = c := by
        have : (⟨Y, hlt⟩ : Fin 13) ∈ A ∩ B := Finset.mem_inter.mpr ⟨hYA, hYB⟩
        rw [hAB] at this
        simpa using this
      rw [val_lt _ _ Y hlt] at hY2
      simp only [decide_eq_true_eq] at hY2
      rcases hY2 with h | ⟨_, h⟩
      · exact hqc (h.symm.trans hYc)
      · exact heA (by rw [← h, hYc]; exact hcA)
    · exact ⟨Y, hY1, hand, q, hqA, hz q hq, hqc, hY2⟩
  by_cases hpc : p = c
  · exact main p' hp'.1 hp'.2 (fun h => hne (hpc.trans h.symm))
  · exact main p hp.1 hp.2 hpc

lemma zero_notin (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (m : Fin 13) (hm : m ∈ ({1, 5, 11} : Finset (Fin 13))) : (0 : Fin 13) ∉ L m := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl <;> rw [hL] <;> decide

lemma one_notin (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (l : Fin 13) (hl : l ∈ ({4, 10, 12} : Finset (Fin 13))) : (1 : Fin 13) ∉ L l := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl <;> rw [hL] <;> decide

end PEqualNP.Outside.L_meta_1572_aux

theorem PEqualNP.Outside.L_meta_1572 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (l m c : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → l ∈ ({4, 10, 12} : Finset (Fin 13)) → m ∈ ({1, 5, 11} : Finset (Fin 13)) → L l ∩ L m = {c} →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
    (2 ≤ ((L l).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L l, p ≠ 0 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) ∧
    (2 ≤ ((L m).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true)).card →
      ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∃ p ∈ L m, p ≠ 1 ∧ p ≠ c ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) := by
  intro L hL gates g l m c hg hrb hl hm hlm hgl hgm
  exact ⟨fun h2 => PEqualNP.Outside.L_meta_1572_aux.core gates hg hrb g (L l) (L m) c 0 1 hlm
      (PEqualNP.Outside.L_meta_1572_aux.zero_notin L hL m hm)
      (PEqualNP.Outside.L_meta_1572_aux.one_notin L hL l hl) hgl hgm h2,
    fun h2 => PEqualNP.Outside.L_meta_1572_aux.core gates hg hrb g (L m) (L l) c 1 0
      (by rw [Finset.inter_comm]; exact hlm)
      (PEqualNP.Outside.L_meta_1572_aux.one_notin L hL l hl)
      (PEqualNP.Outside.L_meta_1572_aux.zero_notin L hL m hm) hgm hgl h2⟩
