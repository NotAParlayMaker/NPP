import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5502
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (G : List Gate) (x : List Bool) :
    (G.foldl step x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp
  | cons g G ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_snoc (W : List Bool) (v : Bool) (w : ℕ) :
    (W ++ [v]).getD w false = if w = W.length then v else W.getD w false := by
  rcases lt_trichotomy w W.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _), if_pos rfl]
    simp
  · rw [List.getD_append_right _ _ _ _ (le_of_lt h), if_neg (Nat.ne_of_gt h)]
    have h1 : 1 ≤ w - W.length := by omega
    rw [List.getD_eq_default _ _ (by simpa using h1), List.getD_eq_default _ _ (le_of_lt h)]

lemma step_getD (W : List Bool) (g : Gate) (w : ℕ) :
    (step W g).getD w false =
      if w = W.length then g.op.eval (g.inputs.map fun i => W.getD i false) else W.getD w false :=
  getD_snoc W _ w

lemma key (n : ℕ) (G : List Gate) (hG : ∀ g ∈ G, g.inputs.length ≤ 2) :
    ∀ T : Finset ℕ, ∃ D : Finset ℕ, D.card ≤ T.card + G.length ∧
      ∀ x x' : List Bool, x.length = n → x'.length = n →
        (∀ i ∈ D, x.getD i false = x'.getD i false) →
        ∀ w ∈ T, (G.foldl step x).getD w false = (G.foldl step x').getD w false := by
  induction G using List.reverseRecOn with
  | nil =>
    intro T
    exact ⟨T, by simp, fun x x' _ _ h w hw => by simpa using h w hw⟩
  | append_singleton G g ih =>
    intro T
    have hG' : ∀ g' ∈ G, g'.inputs.length ≤ 2 := fun g' h => hG g' (by simp [h])
    have hg : g.inputs.length ≤ 2 := hG g (by simp)
    by_cases hmT : n + G.length ∈ T
    · obtain ⟨D, hD, hDx⟩ := ih hG' (T.erase (n + G.length) ∪ g.inputs.toFinset)
      refine ⟨D, ?_, ?_⟩
      · have h1 : (T.erase (n + G.length) ∪ g.inputs.toFinset).card ≤ (T.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hmT]
          have := List.toFinset_card_le g.inputs
          omega
        have h2 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hmT⟩
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x x' hx hx' hagree w hw
        have IH := hDx x x' hx hx' hagree
        have hl : (G.foldl step x).length = n + G.length := by rw [foldl_len, hx]
        have hl' : (G.foldl step x').length = n + G.length := by rw [foldl_len, hx']
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [step_getD, step_getD, hl, hl']
        by_cases hwm : w = n + G.length
        · rw [if_pos hwm, if_pos hwm]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact IH i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
        · rw [if_neg hwm, if_neg hwm]
          exact IH w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩))
    · obtain ⟨D, hD, hDx⟩ := ih hG' T
      refine ⟨D, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro x x' hx hx' hagree w hw
        have IH := hDx x x' hx hx' hagree
        have hl : (G.foldl step x).length = n + G.length := by rw [foldl_len, hx]
        have hl' : (G.foldl step x').length = n + G.length := by rw [foldl_len, hx']
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [step_getD, step_getD, hl, hl']
        have hwm : w ≠ n + G.length := fun h => hmT (h ▸ hw)
        rw [if_neg hwm, if_neg hwm]
        exact IH w hw

def fn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) ||
    (x 2 && x 3) || (x 2 && x 4) || (x 2 && x 5)

def base (i : Fin 6) : Fin 6 → Bool :=
  fun j => decide (j = if i.val < 3 then (3 : Fin 6) else (0 : Fin 6))

lemma sens : ∀ i : Fin 6, fn (Function.update (base i) i true) ≠ fn (base i) := by
  decide

lemma ofFn_getD (x x' : Fin 6 → Bool) (i : Fin 6) (h : ∀ j : Fin 6, j ≠ i → x j = x' j)
    (k : ℕ) (hk : k ≠ i.val) :
    (List.ofFn x).getD k false = (List.ofFn x').getD k false := by
  by_cases hk6 : k < 6
  · have e1 : (List.ofFn x).getD k false = x ⟨k, hk6⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hk6)]
      simp only [List.getElem_ofFn]
    have e2 : (List.ofFn x').getD k false = x' ⟨k, hk6⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hk6)]
      simp only [List.getElem_ofFn]
    rw [e1, e2]
    exact h ⟨k, hk6⟩ (fun hc => hk (by rw [← hc]))
  · rw [List.getD_eq_default _ _ (by simpa using hk6), List.getD_eq_default _ _ (by simpa using hk6)]

lemma bound (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = fn x) : 5 ≤ C.size := by
  obtain ⟨D, hD, hDx⟩ := key 6 C.gates (fun g hg => (hF g hg).2) {C.output}
  have hall : ∀ i : Fin 6, i.val ∈ D := by
    intro i
    by_contra hi
    have hagree : ∀ k ∈ D, (List.ofFn (Function.update (base i) i true)).getD k false =
        (List.ofFn (base i)).getD k false := by
      intro k hk
      exact ofFn_getD _ _ i (fun j hj => Function.update_of_ne hj _ _) k (fun hc => hi (hc ▸ hk))
    have h := hDx _ _ (by simp) (by simp) hagree C.output (by simp)
    have h1 := hev (Function.update (base i) i true)
    have h2 := hev (base i)
    unfold Circuit.eval Circuit.wires at h1 h2
    exact sens i (by rw [← h1, ← h2]; exact h)
  have hcard : 6 ≤ D.card := by
    have hsub : (Finset.univ : Finset (Fin 6)).image (fun i : Fin 6 => i.val) ⊆ D := by
      intro k hk
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
      exact hall i
    have h6 : ((Finset.univ : Finset (Fin 6)).image (fun i : Fin 6 => i.val)).card = 6 := by
      rw [Finset.card_image_of_injective _ Fin.val_injective]
      simp
    calc 6 = _ := h6.symm
      _ ≤ D.card := Finset.card_le_card hsub
  have hD' : D.card ≤ 1 + C.gates.length := by simpa using hD
  unfold Circuit.size
  omega

end PEqualNP.Outside.L_meta_5502

theorem PEqualNP.Outside.L_meta_5502 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4) || (x 2 && x 5)) t → 5 ≤ t := by
  intro t ht
  obtain ⟨C, hF, hsz, hev⟩ := ht
  have h := PEqualNP.Outside.L_meta_5502.bound C hF hev
  omega
