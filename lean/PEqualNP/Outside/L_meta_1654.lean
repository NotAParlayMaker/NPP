import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1654_aux

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_run (gates : List Gate) (x : List Bool) :
    Circuit.wires ⟨gates, 0⟩ x = run gates x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

lemma getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

lemma ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs with h <;> simp

lemma eval_mono (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hfg : ∀ j, f j = true → g j = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases h with h | h
  · subst h
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id]
    intro H j hj
    exact hfg _ (H j hj)
  · subst h
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
    exact ⟨g j, ⟨j, hj, rfl⟩, hfg _ hb⟩

lemma run_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true)
    (hlen : x.length = y.length) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil =>
    intro i hi
    exact hxy i (by simpa [run] using hi)
  | cons g gs ih =>
    have hg0 : g.op = GateOp.and ∨ g.op = GateOp.or :=
      hg g (List.mem_cons.mpr (Or.inl rfl))
    have hgt : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))
    have hstep :
        g.op.eval (g.inputs.map fun i => x.getD i false) = true →
          g.op.eval (g.inputs.map fun i => y.getD i false) = true :=
      eval_mono g.op hg0 g.inputs (fun i => x.getD i false) (fun i => y.getD i false) hxy
    have hxy' : ∀ i,
        (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).getD i false = true →
          (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).getD i false = true := by
      intro i hi
      by_cases hlt : i < x.length
      · rw [getD_append_left x _ i false hlt] at hi
        rw [getD_append_left y _ i false (by omega)]
        exact hxy i hi
      · by_cases heq : i = x.length
        · subst heq
          rw [getD_append_right x _ x.length false (Nat.le_refl _), Nat.sub_self,
            List.getD_cons_zero] at hi
          rw [hlen]
          rw [getD_append_right y _ y.length false (Nat.le_refl _), Nat.sub_self,
            List.getD_cons_zero]
          exact hstep hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          simp at hi
    have hlen' :
        (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length =
          (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]).length := by simp [hlen]
    intro i hi
    exact ih hgt _ _ hxy' hlen' i (by simpa [run_cons] using hi)

lemma wires_up (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true)
    (hlen : x.length = y.length) (w : ℕ)
    (hx : (Circuit.wires ⟨gates, 0⟩ x).getD w false = true) :
    (Circuit.wires ⟨gates, 0⟩ y).getD w false = true := by
  have hx' : (run gates x).getD w false = true := by simpa [wires_run] using hx
  simpa [wires_run] using run_mono gates hg x y hxy hlen w hx'

lemma ofFn_len {n : ℕ} (f g : Fin n → Bool) :
    (List.ofFn f).length = (List.ofFn g).length := by simp

lemma point_le {n : ℕ} {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    ∀ i, (List.ofFn (fun u : Fin n => decide (u = v))).getD i false = true →
      (List.ofFn (fun u : Fin n => decide (u ∈ S))).getD i false = true := by
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD, dite_eq_left hlt] at hi
    rw [ofFn_getD, dite_eq_left hlt]
    have huv : (⟨i, hlt⟩ : Fin n) = v := by simpa using hi
    simpa using (huv ▸ hv)
  · rw [ofFn_getD, dite_eq_right hlt] at hi
    simp at hi

lemma chi_le {n : ℕ} {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    ∀ i, (List.ofFn (fun u : Fin n => decide (u ∈ A))).getD i false = true →
      (List.ofFn (fun u : Fin n => decide (u ∈ B))).getD i false = true := by
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD, dite_eq_left hlt] at hi
    rw [ofFn_getD, dite_eq_left hlt]
    have hmem : (⟨i, hlt⟩ : Fin n) ∈ A := by simpa using hi
    simpa using hAB hmem
  · rw [ofFn_getD, dite_eq_right hlt] at hi
    simp at hi

lemma disjoint_insert_line {n L : ℕ} {line : Fin L → Finset (Fin n)} {l : Fin L}
    {I : Finset (Fin n)} {v : Fin n}
    (hI : Disjoint I (line l)) (hv : v ∉ line l) :
    Disjoint (insert v I) (line l) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hv
  · exact Finset.disjoint_left.mp hI hx

lemma arc_insert {n L : ℕ} {line : Fin L → Finset (Fin n)} {I : Finset (Fin n)} {v : Fin n}
    (hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j)
    (hsec : ¬ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j) :
    ∀ a ∈ insert v I, ∀ b ∈ insert v I, ∀ c ∈ insert v I, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j := by
  intro a ha b hb c hc hab hac hbc hex
  have ha' : a = v ∨ a ∈ I := Finset.mem_insert.mp ha
  have hb' : b = v ∨ b ∈ I := Finset.mem_insert.mp hb
  have hc' : c = v ∨ c ∈ I := Finset.mem_insert.mp hc
  by_cases hav : a = v
  · subst hav
    rcases hb' with hbv | hbI
    · exact hab.symm hbv
    rcases hc' with hcv | hcI
    · exact hac.symm hcv
    rcases hex with ⟨j, hja, hjb, hjc⟩
    exact hsec ⟨b, hbI, c, hcI, hbc, j, hjb, hjc, hja⟩
  · by_cases hbv : b = v
    · subst hbv
      rcases ha' with hav' | haI
      · exact hab hav'
      rcases hc' with hcv | hcI
      · exact hbc.symm hcv
      rcases hex with ⟨j, hja, hjb, hjc⟩
      exact hsec ⟨a, haI, c, hcI, hac, j, hja, hjc, hjb⟩
    · by_cases hcv : c = v
      · subst hcv
        rcases ha' with hav' | haI
        · exact hac hav'
        rcases hb' with hbv' | hbI
        · exact hbc hbv'
        rcases hex with ⟨j, hja, hjb, hjc⟩
        exact hsec ⟨a, haI, b, hbI, hab, j, hja, hjb, hjc⟩
      · have haI : a ∈ I := by
          rcases ha' with h | h
          · exact (hav h).elim
          · exact h
        have hbI : b ∈ I := by
          rcases hb' with h | h
          · exact (hbv h).elim
          · exact h
        have hcI : c ∈ I := by
          rcases hc' with h | h
          · exact (hcv h).elim
          · exact h
        exact hI a haI b hbI c hcI hab hac hbc hex

end PEqualNP.Outside.L_meta_1654_aux

open PEqualNP.Outside.L_meta_1654_aux

theorem PEqualNP.Outside.L_meta_1654 : ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  intro n L line l gates G K I _hpair _hinter hgates _hwire hno hIdisj hIarc hK v hvline hGv
  have hgop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hgates g hg).1
  have hvI : v ∉ I := by
    intro hvmem
    have hGI :
        (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD G false = true :=
      wires_up gates hgop
        (List.ofFn (fun u : Fin n => decide (u = v)))
        (List.ofFn (fun u : Fin n => decide (u ∈ I)))
        (point_le hvmem) (ofFn_len _ _) G hGv
    exact hno ⟨I, hIdisj, hIarc, hGI, hK⟩
  refine ⟨hvI, ?_⟩
  by_contra hsec
  let X : Finset (Fin n) := insert v I
  have hXdisj : Disjoint X (line l) := disjoint_insert_line hIdisj hvline
  have hXarc : ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j :=
    arc_insert hIarc hsec
  have hGX :
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true :=
    wires_up gates hgop
      (List.ofFn (fun u : Fin n => decide (u = v)))
      (List.ofFn (fun u : Fin n => decide (u ∈ X)))
      (point_le (Finset.mem_insert_self v I)) (ofFn_len _ _) G hGv
  have hKX :
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true :=
    wires_up gates hgop
      (List.ofFn (fun u : Fin n => decide (u ∈ I)))
      (List.ofFn (fun u : Fin n => decide (u ∈ X)))
      (chi_le (Finset.subset_insert v I)) (ofFn_len _ _) K hK
  exact hno ⟨X, hXdisj, hXarc, hGX, hKX⟩
