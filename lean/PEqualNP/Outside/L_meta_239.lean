import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_239_aux

open PEqualNP.MetaComplexity

def step (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

def run (gs : List BinaryGate) (w : List Bool) : List Bool :=
  gs.foldl step w

def pullFrontier (n : ℕ) : List BinaryGate → Finset ℕ → Finset ℕ
  | [], A => A
  | g :: gs, A =>
    let A' := pullFrontier (n + 1) gs A
    if n ∈ A' then
      (A'.erase n) ∪ (if g.left < n then {g.left} else ∅) ∪ (if g.right < n then {g.right} else ∅)
    else A'

lemma run_cons (g : BinaryGate) (gs : List BinaryGate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

lemma length_run (gs : List BinaryGate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih, show (step w g).length = w.length + 1 by simp [step]]
    simp only [List.length_cons]
    omega

lemma pullFrontier_lt (n : ℕ) (gs : List BinaryGate) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < n + gs.length) :
    ∀ k ∈ pullFrontier n gs A, k < n := by
  induction gs generalizing n A with
  | nil =>
    simpa [pullFrontier] using hA
  | cons g gs ih =>
    have hA' : ∀ k ∈ pullFrontier (n + 1) gs A, k < n + 1 := by
      refine ih (n + 1) A fun k hk => ?_
      have := hA k hk
      simp only [List.length_cons] at this
      omega
    intro k hk
    dsimp only [pullFrontier] at hk
    by_cases hn : n ∈ pullFrontier (n + 1) gs A
    · rw [if_pos hn] at hk
      simp only [Finset.mem_union, Finset.mem_erase] at hk
      rcases hk with (⟨hne, hk'⟩ | hl) | hr
      · have := hA' k hk'; omega
      · by_cases hlt : g.left < n
        · rw [if_pos hlt] at hl
          simp only [Finset.mem_singleton] at hl
          omega
        · rw [if_neg hlt] at hl; simp at hl
      · by_cases hlt : g.right < n
        · rw [if_pos hlt] at hr
          simp only [Finset.mem_singleton] at hr
          omega
        · rw [if_neg hlt] at hr; simp at hr
    · rw [if_neg hn] at hk
      have hne : k ≠ n := fun h => hn (h ▸ hk)
      have := hA' k hk
      omega

lemma card_union_ite_singleton (S : Finset ℕ) (p : Prop) [Decidable p] (a : ℕ) :
    (S ∪ (if p then {a} else ∅)).card ≤ S.card + 1 := by
  by_cases hp : p
  · rw [if_pos hp]
    exact le_trans (Finset.card_union_le S {a}) (by simp)
  · rw [if_neg hp]
    simp

lemma pullFrontier_card (n : ℕ) (gs : List BinaryGate) (A : Finset ℕ) :
    (pullFrontier n gs A).card ≤ A.card + gs.length := by
  induction gs generalizing n A with
  | nil => simp [pullFrontier]
  | cons g gs ih =>
    have hih := ih (n + 1) A
    dsimp only [pullFrontier]
    by_cases hn : n ∈ pullFrontier (n + 1) gs A
    · rw [if_pos hn]
      have h1 := card_union_ite_singleton
        ((pullFrontier (n + 1) gs A).erase n ∪ if g.left < n then {g.left} else ∅)
        (g.right < n) g.right
      have h2 := card_union_ite_singleton
        ((pullFrontier (n + 1) gs A).erase n) (g.left < n) g.left
      have h3 : ((pullFrontier (n + 1) gs A).erase n).card + 1 =
          (pullFrontier (n + 1) gs A).card := Finset.card_erase_add_one hn
      simp only [List.length_cons]
      omega
    · rw [if_neg hn]
      simp only [List.length_cons]
      omega

lemma getD_step_eq_of_lt (w : List Bool) (g : BinaryGate) {k : ℕ} (hk : k < w.length) :
    (step w g).getD k false = w.getD k false := by
  simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_step_self (w : List Bool) (g : BinaryGate) :
    (step w g).getD w.length false = g.op (w.getD g.left false) (w.getD g.right false) := by
  simp [step]

lemma pullFrontier_agree (n : ℕ) (gs : List BinaryGate) (A : Finset ℕ)
    (hA : ∀ k ∈ A, k < n + gs.length)
    (w₁ w₂ : List Bool) (hw₁ : w₁.length = n) (hw₂ : w₂.length = n)
    (hagree : ∀ k ∈ pullFrontier n gs A, w₁.getD k false = w₂.getD k false) :
    ∀ k ∈ A, (run gs w₁).getD k false = (run gs w₂).getD k false := by
  induction gs generalizing n A w₁ w₂ with
  | nil =>
    simpa [run, pullFrontier] using hagree
  | cons g gs ih =>
    simp only [run_cons]
    have hA_next : ∀ k ∈ A, k < (n + 1) + gs.length := by
      intro k hk
      have := hA k hk
      simp only [List.length_cons] at this
      omega
    refine ih (n + 1) A hA_next (step w₁ g) (step w₂ g)
      (by simp [step, hw₁]) (by simp [step, hw₂]) ?_
    intro k hk
    have hk_lt : k < n + 1 := pullFrontier_lt (n + 1) gs A hA_next k hk
    by_cases hkn : k < n
    · rw [getD_step_eq_of_lt w₁ g (by omega), getD_step_eq_of_lt w₂ g (by omega)]
      refine hagree k ?_
      dsimp only [pullFrontier]
      by_cases hn : n ∈ pullFrontier (n + 1) gs A
      · rw [if_pos hn]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨by omega, hk⟩))
      · rw [if_neg hn]
        exact hk
    · have hkeq : k = n := by omega
      have hn' : n ∈ pullFrontier (n + 1) gs A := hkeq ▸ hk
      rw [hkeq]
      have hs1 : (step w₁ g).getD n false = g.op (w₁.getD g.left false) (w₁.getD g.right false) := by
        rw [← hw₁, getD_step_self]
      have hs2 : (step w₂ g).getD n false = g.op (w₂.getD g.left false) (w₂.getD g.right false) := by
        rw [← hw₂, getD_step_self]
      rw [hs1, hs2]
      have hleft : w₁.getD g.left false = w₂.getD g.left false := by
        by_cases hl : g.left < n
        · refine hagree g.left ?_
          dsimp only [pullFrontier]
          rw [if_pos hn']
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hl]))
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      have hright : w₁.getD g.right false = w₂.getD g.right false := by
        by_cases hr : g.right < n
        · refine hagree g.right ?_
          dsimp only [pullFrontier]
          rw [if_pos hn']
          exact Finset.mem_union_right _ (by simp [hr])
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      rw [hleft, hright]

end PEqualNP.Outside.L_meta_239_aux

theorem PEqualNP.Outside.L_meta_239 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 := by
  intro n f hdep s ⟨C, hsize, heval⟩
  let A : Finset ℕ := if C.output < n + C.gates.length then {C.output} else ∅
  have hA_lt : ∀ k ∈ A, k < n + C.gates.length := by
    intro k hk
    dsimp only [A] at hk
    by_cases hlt : C.output < n + C.gates.length
    · rw [if_pos hlt] at hk
      simp only [Finset.mem_singleton] at hk
      omega
    · rw [if_neg hlt] at hk; simp at hk
  have hA_card : A.card ≤ 1 := by
    dsimp only [A]
    by_cases hlt : C.output < n + C.gates.length
    · rw [if_pos hlt]; simp
    · rw [if_neg hlt]; simp
  set F : Finset ℕ := PEqualNP.Outside.L_meta_239_aux.pullFrontier n C.gates A
  have hF_card : F.card ≤ s + 1 := by
    have h1 : F.card ≤ A.card + C.gates.length :=
      PEqualNP.Outside.L_meta_239_aux.pullFrontier_card n C.gates A
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.size] at hsize
    omega
  have hsub : Finset.range n ⊆ F := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    by_contra hnot
    obtain ⟨x, hx⟩ := hdep ⟨i, hin⟩
    let y : Fin n → Bool := Function.update x ⟨i, hin⟩ (!x ⟨i, hin⟩)
    have hagree : ∀ k ∈ F, (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
      intro k hk
      have hkn : k < n := PEqualNP.Outside.L_meta_239_aux.pullFrontier_lt n C.gates A hA_lt k hk
      have hki : k ≠ i := fun h => hnot (h ▸ hk)
      have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨i, hin⟩ := fun h => hki (congrArg Fin.val h)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hkn, dite_true, Option.getD_some]
      exact (Function.update_of_ne hne (!x ⟨i, hin⟩) x).symm
    have heq_eval : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
      change (PEqualNP.Outside.L_meta_239_aux.run C.gates (List.ofFn x)).getD C.output false =
        (PEqualNP.Outside.L_meta_239_aux.run C.gates (List.ofFn y)).getD C.output false
      by_cases ho : C.output < n + C.gates.length
      · exact PEqualNP.Outside.L_meta_239_aux.pullFrontier_agree n C.gates A hA_lt
          (List.ofFn x) (List.ofFn y) (List.length_ofFn) (List.length_ofFn) hagree
          C.output (by simp [A, ho])
      · have hlen1 : (PEqualNP.Outside.L_meta_239_aux.run C.gates (List.ofFn x)).length =
            n + C.gates.length := by
          rw [PEqualNP.Outside.L_meta_239_aux.length_run, List.length_ofFn]
        have hlen2 : (PEqualNP.Outside.L_meta_239_aux.run C.gates (List.ofFn y)).length =
            n + C.gates.length := by
          rw [PEqualNP.Outside.L_meta_239_aux.length_run, List.length_ofFn]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [heval x, heval y] at heq_eval
    exact hx heq_eval.symm
  have hcard_le : (Finset.range n).card ≤ F.card := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard_le
  omega
