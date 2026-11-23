import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1356

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then b else false := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by simp; omega), getD_snoc, ite_eq_left h]

theorem fold_le (p : ℕ) : ∀ (gs : List Gate) (w0 w1 : List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p ∉ g.inputs) →
    w0.length = w1.length →
    (∀ i, i ≠ p → w1.getD i false = true → w0.getD i false = true) →
    ∀ i, i ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD
        i false = true := by
  intro gs
  induction gs with
  | nil => intro w0 w1 _ _ hle; exact hle
  | cons g gs ih =>
    intro w0 w1 hg hlen hle
    simp only [List.foldl_cons]
    apply ih
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · simp [hlen]
    · intro i hi h1
      obtain ⟨hop, hp⟩ := hg g (by simp)
      have key : ∀ j ∈ g.inputs, w1.getD j false = true → w0.getD j false = true := by
        intro j hj
        exact hle j (fun h => hp (h ▸ hj))
      rw [getD_snoc] at h1 ⊢
      rw [← hlen] at h1
      by_cases ha : i < w0.length
      · rw [ite_eq_left ha] at h1 ⊢
        exact hle i hi h1
      · rw [ite_eq_right ha] at h1 ⊢
        by_cases hb : i = w0.length
        · rw [ite_eq_left hb] at h1 ⊢
          rcases hop with hop | hop
          · rw [hop] at h1 ⊢
            simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply,
              id_eq] at h1 ⊢
            intro j hj
            exact key j hj (h1 j hj)
          · rw [hop] at h1 ⊢
            simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply,
              id_eq] at h1 ⊢
            obtain ⟨j, hj, h⟩ := h1
            exact ⟨j, hj, key j hj h⟩
        · rw [ite_eq_right hb] at h1
          exact absurd h1 (by simp)

theorem fold_eq (p : ℕ) : ∀ (gs : List Gate) (w0 w1 : List Bool),
    (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p ∉ g.inputs) ∨
      g.op = GateOp.not) →
    gs.Pairwise (fun a b => ¬ (a.op = GateOp.not ∧ b.op = GateOp.not)) →
    w0.length = w1.length → p < w0.length →
    (w0.getD p false = true → w1.getD p false = true) →
    (∀ i, i ≠ p → w0.getD i false = w1.getD i false) →
    ∀ i, i ≠ p →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD
        i false = true := by
  intro gs
  induction gs with
  | nil =>
    intro w0 w1 _ _ _ _ _ heq i hi h
    simp only [List.foldl_nil] at h ⊢
    rw [heq i hi]
    exact h
  | cons g gs ih =>
    intro w0 w1 hg hpw hlen hplt hpmono heq
    rw [List.pairwise_cons] at hpw
    obtain ⟨hhead, htail⟩ := hpw
    simp only [List.foldl_cons]
    by_cases hnot : g.op = GateOp.not
    · apply fold_le p gs
      · intro b hb
        rcases hg b (List.mem_cons_of_mem _ hb) with h | h
        · exact h
        · exact absurd ⟨hnot, h⟩ (hhead b hb)
      · simp [hlen]
      · intro i hi h1
        rw [getD_snoc] at h1 ⊢
        rw [← hlen] at h1
        by_cases ha : i < w0.length
        · rw [ite_eq_left ha] at h1 ⊢
          rw [heq i hi]
          exact h1
        · rw [ite_eq_right ha] at h1 ⊢
          by_cases hb : i = w0.length
          · rw [ite_eq_left hb] at h1 ⊢
            rw [hnot] at h1 ⊢
            simp only [GateOp.eval] at h1 ⊢
            cases hin : g.inputs with
            | nil => simp
            | cons j rest =>
              rw [hin] at h1
              simp only [List.map_cons, List.headD_cons, Bool.not_eq_eq_eq_not,
                Bool.not_true] at h1 ⊢
              by_cases hjp : j = p
              · subst hjp
                cases h0 : w0.getD j false
                · rfl
                · rw [hpmono h0] at h1
                  exact absurd h1 (by simp)
              · rw [heq j hjp]
                exact h1
          · rw [ite_eq_right hb] at h1
            exact absurd h1 (by simp)
    · have hgate : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p ∉ g.inputs := by
        rcases hg g (by simp) with h | h
        · exact h
        · exact absurd h hnot
      have hmap : (g.inputs.map fun i => w0.getD i false)
          = (g.inputs.map fun i => w1.getD i false) := by
        apply List.map_congr_left
        intro j hj
        exact heq j (fun h => hgate.2 (h ▸ hj))
      apply ih
      · intro b hb
        exact hg b (List.mem_cons_of_mem _ hb)
      · exact htail
      · simp [hlen]
      · simp; omega
      · intro h0
        rw [getD_snoc, ite_eq_left hplt] at h0
        rw [getD_snoc, ← hlen, ite_eq_left hplt]
        exact hpmono h0
      · intro i hi
        rw [getD_snoc, getD_snoc, ← hlen, hmap]
        by_cases ha : i < w0.length
        · rw [ite_eq_left ha, ite_eq_left ha, heq i hi]
        · rw [ite_eq_right ha, ite_eq_right ha]

end PEqualNP.Outside.L_meta_1356

theorem PEqualNP.Outside.L_meta_1356 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i9 : Fin m, 2 ≤ (S i9).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ (p : Fin n) (i0 : Fin m), p ∈ S i0 → ∃ a : Fin gates.length, ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ p.val ∈ (gates.get a).inputs := by
  intro n m S hS gates out hgates heval ι hι p i0 hp
  by_contra hcon
  push Not at hcon
  have hg : ∀ g ∈ gates, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ p.val ∉ g.inputs) ∨
      g.op = GateOp.not := by
    intro g hgm
    obtain ⟨a, rfl⟩ := List.mem_iff_get.mp hgm
    rcases (hgates _ hgm).1 with h | h | h
    · exact Or.inl ⟨Or.inl h, hcon a (Or.inl h)⟩
    · exact Or.inl ⟨Or.inr h, hcon a (Or.inr h)⟩
    · exact Or.inr h
  have hpw : gates.Pairwise (fun a b => ¬ (a.op = GateOp.not ∧ b.op = GateOp.not)) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij ⟨h1, h2⟩
    obtain ⟨r1, hr1⟩ := hι ⟨i, hi⟩ (by simpa using h1)
    obtain ⟨r2, hr2⟩ := hι ⟨j, hj⟩ (by simpa using h2)
    have hr : r1 = r2 := Subsingleton.elim _ _
    subst hr
    have : (⟨i, hi⟩ : Fin gates.length) = ⟨j, hj⟩ := hr1.symm.trans hr2
    simp at this
    omega
  have hofFn : ∀ (x : Fin n → Bool) (i : ℕ) (h : i < n),
      (List.ofFn x).getD i false = x ⟨i, h⟩ := by
    intro x i h
    simp [List.getD_eq_getElem?_getD, h]
  have hofFn' : ∀ (x : Fin n → Bool) (i : ℕ), ¬ i < n → (List.ofFn x).getD i false = false := by
    intro x i h
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
  obtain ⟨v, hv, hvp⟩ := Finset.exists_mem_ne (show 1 < (S i0).card by have := hS i0; omega) p
  by_cases hout : out i0 = p.val
  · have h2 := heval i0 (fun u => decide (u = v))
    have hrhs : decide (∃ u ∈ S i0, decide (u = v) = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨v, hv, rfl⟩
    rw [hrhs] at h2
    simp only [Circuit.eval, Circuit.wires, hout] at h2
    rw [PEqualNP.Outside.L_meta_1356.fold_prefix _ _ _ (by simp), hofFn _ _ p.isLt] at h2
    simp only [decide_eq_true_eq] at h2
    exact hvp (by rw [← h2])
  · have h0 := heval i0 (fun _ => false)
    have h1 := heval i0 (fun u => decide (u = p))
    have hr0 : decide (∃ u ∈ S i0, (fun _ : Fin n => false) u = true) = false := by simp
    have hr1 : decide (∃ u ∈ S i0, decide (u = p) = true) = true := by
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, rfl⟩
    rw [hr0] at h0
    rw [hr1] at h1
    simp only [Circuit.eval, Circuit.wires] at h0 h1
    have key := PEqualNP.Outside.L_meta_1356.fold_eq p.val gates
      (List.ofFn fun _ : Fin n => false) (List.ofFn fun u : Fin n => decide (u = p))
      hg hpw (by simp) (by simp) (by intro h; rw [hofFn _ _ p.isLt] at h; exact absurd h (by simp))
      (by
        intro i hi
        by_cases hin : i < n
        · rw [hofFn _ _ hin, hofFn _ _ hin]
          symm
          simp only [decide_eq_false_iff_not]
          intro h
          exact hi (by rw [← h])
        · rw [hofFn' _ _ hin, hofFn' _ _ hin])
      (out i0) hout h1
    rw [h0] at key
    exact absurd key (by simp)
