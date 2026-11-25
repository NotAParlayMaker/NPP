import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7630_aux

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false = if i = l.length then v else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · subst h
    simp
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem main (n : ℕ) (x2 : Finset ℕ) (hx2 : ∀ a ∈ x2, a < n) : ∀ gs : List Gate,
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ N, gs.length ≤ N → ∃ (gs2 : List Gate) (σ : ℕ → ℕ),
      (∀ g ∈ gs2, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      gs2.length + (List.filter (fun (g : Gate) => g.inputs.any fun (i : ℕ) =>
        Decidable.decide (i ∈ x2)) gs).length = gs.length ∧
      (∀ i, σ i < n + gs2.length ∨ n + N ≤ σ i) ∧
      ∀ x : List Bool, x.length = n → (∀ a ∈ x2, x.getD a false = false) →
        (W gs x).length = n + gs.length ∧ (W gs2 x).length = n + gs2.length ∧
        (∀ a ∈ x2, (W gs x).getD a false = false) ∧
        ∀ i, (W gs2 x).getD (σ i) false = (W gs x).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ N _
    refine ⟨[], fun i => if i < n then i else n + N, by simp, by simp, ?_, ?_⟩
    · intro i
      by_cases h : i < n <;> simp [h]
    · intro x hx hf
      refine ⟨by simp [W, hx], by simp [W, hx], by simpa [W] using hf, ?_⟩
      intro i
      by_cases h : i < n
      · simp [h]
      · simp only [h, if_false, W, List.foldl_nil]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro hmono N hN
    have hlen : gs.length + 1 ≤ N := by simpa using hN
    obtain ⟨gs2, σ, hm2, hcnt, hrange, hval⟩ :=
      ih (fun g hg => hmono g (by simp [hg])) N (by omega)
    have hg := hmono g (by simp)
    by_cases hr : (g.inputs.any fun (i : ℕ) => Decidable.decide (i ∈ x2)) = true
    · have ht : ∃ t, (t < n + gs2.length ∨ n + N ≤ t) ∧
          ∀ x : List Bool, x.length = n → (∀ a ∈ x2, x.getD a false = false) →
            (W gs2 x).getD t false =
              g.op.eval (g.inputs.map fun i => (W gs x).getD i false) := by
        obtain ⟨op, inputs⟩ := g
        obtain ⟨hop, hl⟩ := hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        simp only at hr hl
        rcases hop with rfl | rfl
        · refine ⟨n + N, Or.inr le_rfl, fun x hx hf => ?_⟩
          obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
          rw [List.getD_eq_default _ _ (by omega)]
          obtain ⟨i, hi, hix⟩ := List.any_eq_true.1 hr
          symm
          show List.all _ id = false
          rw [List.all_eq_false]
          exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, by simpa using h3 i (by simpa using hix)⟩
        · match inputs, hr, hl with
          | [], hr, _ => simp at hr
          | [a], hr, _ =>
            refine ⟨n + N, Or.inr le_rfl, fun x hx hf => ?_⟩
            obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
            rw [List.getD_eq_default _ _ (by omega)]
            show false = List.any [(W gs x).getD a false] id
            rw [h3 a (by simpa using hr)]
            rfl
          | [a, b], hr, _ =>
            by_cases ha : a ∈ x2
            · refine ⟨σ b, hrange b, fun x hx hf => ?_⟩
              obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
              show (W gs2 x).getD (σ b) false = List.any [(W gs x).getD a false, (W gs x).getD b false] id
              rw [h3 a ha, h4 b]
              simp
            · have hb : b ∈ x2 := by simpa [ha] using hr
              refine ⟨σ a, hrange a, fun x hx hf => ?_⟩
              obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
              show (W gs2 x).getD (σ a) false = List.any [(W gs x).getD a false, (W gs x).getD b false] id
              rw [h3 b hb, h4 a]
              simp
          | _ :: _ :: _ :: _, _, hl => simp at hl
      obtain ⟨t, htr, htv⟩ := ht
      refine ⟨gs2, Function.update σ (n + gs.length) t, hm2, ?_, ?_, ?_⟩
      · simp only [List.filter_append, List.length_append, List.filter_cons, hr, if_true,
          List.filter_nil, List.length_cons, List.length_nil]
        omega
      · intro i
        by_cases h : i = n + gs.length
        · subst h
          simpa using htr
        · simpa [Function.update, h] using hrange i
      · intro x hx hf
        obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
        refine ⟨by simp [W_snoc, h1]; omega, h2, ?_, ?_⟩
        · intro a ha
          rw [W_snoc, getD_snoc, if_neg (by have := hx2 a ha; omega)]
          exact h3 a ha
        · intro i
          rw [W_snoc, getD_snoc]
          by_cases h : i = n + gs.length
          · subst h
            simp only [Function.update_self, h1, if_true]
            exact htv x hx hf
          · rw [Function.update_of_ne h, if_neg (by omega)]
            exact h4 i
    · refine ⟨gs2 ++ [⟨g.op, g.inputs.map σ⟩],
        Function.update σ (n + gs.length) (n + gs2.length), ?_, ?_, ?_, ?_⟩
      · intro g2 hg2
        rcases List.mem_append.1 hg2 with h | h
        · exact hm2 g2 h
        · simp only [List.mem_singleton] at h
          subst h
          simpa using hg
      · simp only [List.filter_append, List.length_append, List.filter_cons, hr,
          List.filter_nil, List.length_cons, List.length_nil]
        simp
        omega
      · intro i
        by_cases h : i = n + gs.length
        · subst h
          simp
        · rw [Function.update_of_ne h]
          rcases hrange i with h2 | h2
          · left
            simp
            omega
          · exact Or.inr h2
      · intro x hx hf
        obtain ⟨h1, h2, h3, h4⟩ := hval x hx hf
        refine ⟨by simp [W_snoc, h1]; omega, by simp [W_snoc, h2]; omega, ?_, ?_⟩
        · intro a ha
          rw [W_snoc, getD_snoc, if_neg (by have := hx2 a ha; omega)]
          exact h3 a ha
        · intro i
          rw [W_snoc, getD_snoc, W_snoc, getD_snoc]
          have hmap : (List.map (fun i => (W gs2 x).getD i false) (List.map σ g.inputs)) =
              List.map (fun i => (W gs x).getD i false) g.inputs := by
            rw [List.map_map]
            exact List.map_congr_left (fun i _ => h4 i)
          by_cases h : i = n + gs.length
          · subst h
            simp only [Function.update_self, h1, h2, if_true]
            rw [hmap]
          · rw [Function.update_of_ne h, if_neg (by
              rcases hrange i with h5 | h5 <;> omega), if_neg (by
              rcases hrange i with h5 | h5 <;> omega)]
            exact h4 i

end PEqualNP.Outside.L_meta_7630_aux

theorem PEqualNP.Outside.L_meta_7630 : ∀ (x1 : ℕ) (x2 : Finset ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x2, x4 < x1) → PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.inputs.any fun (x8 : ℕ) => Decidable.decide (x8 ∈ x2)) x3.gates).length = x3.size ∧ ∀ (x7 : List Bool), x7.length = x1 → (∀ x9 ∈ x2, x7.getD x9 Bool.false = Bool.false) → x6.eval x7 = x3.eval x7 := by
  intro x1 x2 x3 hx2 hm
  obtain ⟨gs2, σ, hm2, hcnt, _, hval⟩ :=
    PEqualNP.Outside.L_meta_7630_aux.main x1 x2 hx2 x3.gates hm x3.gates.length le_rfl
  refine ⟨⟨gs2, σ x3.output⟩, hm2, hcnt, fun x hx hf => ?_⟩
  exact (hval x hx hf).2.2.2 x3.output
