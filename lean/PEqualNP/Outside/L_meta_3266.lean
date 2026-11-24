import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds

def val (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def stp (w : List Bool) (g : Gate) : List Bool := w ++ [val g w]

lemma getD_one (l : List Bool) (a : Bool) (k : ℕ) :
    (l ++ [a]).getD k false
      = if k < l.length then l.getD k false else if k = l.length then a else false := by
  by_cases h : k < l.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]
    by_cases h2 : k = l.length
    · subst h2
      simp
    · rw [if_neg h2]
      exact List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)

def cp (g : Gate) : Bool := !g.op.eval [false]

def R (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

abbrev FI (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma R_len (g : Gate) (hg : FI g) : (R g).length ≤ 1 + (if cp g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hlen⟩ := hg
  have hlen' : ins.length ≤ 2 := hlen
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · have e : cp (Gate.mk GateOp.and ins) = true := rfl
    rw [if_pos e]
    exact hlen'
  · have e : cp (Gate.mk GateOp.or ins) = true := rfl
    rw [if_pos e]
    exact hlen'
  · show (ins.take 1).length ≤ _
    rw [List.length_take]
    omega

lemma val_agree (g : Gate) (w w' : List Bool)
    (h : ∀ a ∈ R g, w.getD a false = w'.getD a false) : val g w = val g w' := by
  rcases g with ⟨op, ins⟩
  cases op
  case not =>
    rcases ins with _ | ⟨a, t⟩
    · rfl
    · show (!(w.getD a false)) = (!(w'.getD a false))
      rw [h a (by simp [R])]
  all_goals
    show GateOp.eval _ _ = GateOp.eval _ _
    congr 1
    exact List.map_congr_left (fun a ha => h a ha)

lemma dep (gs : List Gate) : (∀ g ∈ gs, FI g) → ∀ (L : ℕ) (T : Finset ℕ),
    ∃ F : Finset ℕ, F.card ≤ List.countP cp gs + T.card ∧
      ∀ w w' : List Bool, w.length = L → w'.length = L →
        (∀ k ∈ F, w.getD k false = w'.getD k false) →
        ∀ t ∈ T, (gs.foldl stp w).getD t false = (gs.foldl stp w').getD t false := by
  induction gs with
  | nil =>
    intro _ L T
    refine ⟨T, by simp, fun w w' _ _ h t ht => h t ht⟩
  | cons g rest ih =>
    intro hF L T
    obtain ⟨F', hc, hag⟩ := ih (fun g' hg' => hF g' (by simp [hg'])) (L + 1) T
    have hR := R_len g (hF g (by simp))
    have hcnt : List.countP cp (g :: rest)
        = List.countP cp rest + (if cp g = true then 1 else 0) := List.countP_cons
    refine ⟨F'.erase L ∪ (if L ∈ F' then (R g).toFinset else ∅), ?_, ?_⟩
    · rw [hcnt]
      have h1 := Finset.card_union_le (F'.erase L) (if L ∈ F' then (R g).toFinset else ∅)
      by_cases hL : L ∈ F'
      · rw [if_pos hL] at h1 ⊢
        have h2 := Finset.card_erase_of_mem hL
        have h3 := List.toFinset_card_le (R g)
        have h4 : 0 < F'.card := Finset.card_pos.mpr ⟨L, hL⟩
        omega
      · rw [if_neg hL] at h1 ⊢
        have h2 := Finset.card_erase_le (s := F') (a := L)
        have h3 : (∅ : Finset ℕ).card = 0 := Finset.card_empty
        omega
    · intro w w' hl hl' h t ht
      show (rest.foldl stp (w ++ [val g w])).getD t false
        = (rest.foldl stp (w' ++ [val g w'])).getD t false
      refine hag (w ++ [val g w]) (w' ++ [val g w'])
        (by simp only [List.length_append, List.length_singleton, hl])
        (by simp only [List.length_append, List.length_singleton, hl']) ?_ t ht
      intro k hk
      rw [getD_one, getD_one, hl, hl']
      split_ifs with h1 h2
      · exact h k (Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨by omega, hk⟩)))
      · subst h2
        refine val_agree g w w' (fun a ha => h a (Finset.mem_union.mpr (Or.inr ?_)))
        rw [if_pos hk]
        exact List.mem_toFinset.mpr ha
      · rfl

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro x1 x2 hF
  obtain ⟨F, hc, hag⟩ := PEqualNP.Outside.L_meta_3266.dep x2.gates (fun g hg => hF g hg) x1
    {x2.output}
  have h1 : ({x2.output} : Finset ℕ).card = 1 := Finset.card_singleton _
  rw [h1] at hc
  exact ⟨F, hc, fun x5 x6 h5 h6 h => hag x5 x6 h5 h6 h x2.output (Finset.mem_singleton_self _)⟩
