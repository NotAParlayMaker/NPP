import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rd (g : Gate) : List ℕ :=
  if g.op.eval [false] = true then g.inputs.take 1 else g.inputs

def supStep (W : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  W ++ [(rd g).toFinset.biUnion (fun i => W.getD i ∅)]

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def start (n : ℕ) : List (Finset ℕ) :=
  (List.range n).map fun i => ({i} : Finset ℕ)

def Bnd (W : List (Finset ℕ)) (k : ℕ) : Prop :=
  ∀ T : Finset ℕ, (T.biUnion fun i => W.getD i ∅).card ≤ T.card + k

def Agree (xs ys : List Bool) (A : Finset ℕ) : Prop :=
  ∀ j ∈ A, xs.getD j false = ys.getD j false

def Inv (xs ys : List Bool) (W : List (Finset ℕ)) (a b : List Bool) : Prop :=
  a.length = W.length ∧ b.length = W.length ∧
    ∀ i, Agree xs ys (W.getD i ∅) → a.getD i false = b.getD i false

lemma getD_snoc {α : Type} (W : List α) (s d : α) (i : ℕ) :
    (W ++ [s]).getD i d = if i = W.length then s else W.getD i d := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma rd_card (g : Gate) (hg : g.inputs.length ≤ 2) :
    (rd g).toFinset.card ≤ 1 + (if g.op.eval [false] = true then 0 else 1) := by
  unfold rd
  split_ifs with h1
  · have h2 := List.toFinset_card_le (g.inputs.take 1)
    have h3 : (g.inputs.take 1).length ≤ 1 := by simp
    omega
  · have h2 := List.toFinset_card_le g.inputs
    omega

lemma bnd_step (W : List (Finset ℕ)) (k : ℕ) (g : Gate) (h : Bnd W k)
    (hg : g.inputs.length ≤ 2) :
    Bnd (supStep W g) (k + if g.op.eval [false] = true then 0 else 1) := by
  intro T
  have hR := rd_card g hg
  by_cases hT : W.length ∈ T
  · have hsub : (T.biUnion fun i => (supStep W g).getD i ∅) ⊆
        ((T.erase W.length) ∪ (rd g).toFinset).biUnion fun i => W.getD i ∅ := by
      intro a ha
      simp only [Finset.mem_biUnion] at ha ⊢
      obtain ⟨i, hi, ha⟩ := ha
      rw [supStep, getD_snoc] at ha
      split_ifs at ha with hi'
      · simp only [Finset.mem_biUnion] at ha
        obtain ⟨j, hj, ha⟩ := ha
        exact ⟨j, Finset.mem_union_right _ hj, ha⟩
      · exact ⟨i, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hi', hi⟩), ha⟩
    have hc : ((T.erase W.length) ∪ (rd g).toFinset).card ≤
        (T.erase W.length).card + (rd g).toFinset.card := Finset.card_union_le _ _
    have he : (T.erase W.length).card = T.card - 1 := Finset.card_erase_of_mem hT
    have hpos : 1 ≤ T.card := Finset.card_pos.2 ⟨_, hT⟩
    have h1 := Finset.card_le_card hsub
    have h2 := h ((T.erase W.length) ∪ (rd g).toFinset)
    omega
  · have heq : (T.biUnion fun i => (supStep W g).getD i ∅) = T.biUnion fun i => W.getD i ∅ := by
      apply Finset.biUnion_congr rfl
      intro i hi
      rw [supStep, getD_snoc]
      split_ifs with hiW
      · exact absurd (hiW ▸ hi) hT
      · rfl
    rw [heq]
    have := h T
    omega

lemma bnd_fold (gs : List Gate) (hgs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ (W : List (Finset ℕ)) (k : ℕ), Bnd W k →
      Bnd (gs.foldl supStep W) (k + gs.countP (fun g => !g.op.eval [false])) := by
  induction gs with
  | nil => intro W k h; simpa using h
  | cons g gs ih =>
    intro W k h
    rw [List.foldl_cons, List.countP_cons]
    have := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (bnd_step W k g h (hgs g List.mem_cons_self))
    intro T
    have hT := this T
    cases hb : g.op.eval [false] <;> simp only [hb] at hT ⊢ <;> simp at hT ⊢ <;> omega

lemma bnd_init (n : ℕ) : Bnd (start n) 0 := by
  intro T
  calc (T.biUnion fun i => (start n).getD i ∅).card
      ≤ ∑ i ∈ T, ((start n).getD i ∅).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa [start] using h)]
          simp [start]
        · rw [List.getD_eq_default _ _ (by simp [start]; omega)]
          simp
    _ = T.card + 0 := by simp

lemma inv_step (xs ys : List Bool) (W : List (Finset ℕ)) (a b : List Bool) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (h : Inv xs ys W a b) : Inv xs ys (supStep W g) (wstep a g) (wstep b g) := by
  obtain ⟨ha, hb, hab⟩ := h
  refine ⟨by simp [wstep, supStep, ha], by simp [wstep, supStep, hb], ?_⟩
  intro i hi
  simp only [wstep, supStep] at hi ⊢
  rw [getD_snoc] at hi
  rw [getD_snoc, getD_snoc, ha, hb]
  split_ifs at hi ⊢ with hiW
  · have key : ∀ j ∈ rd g, a.getD j false = b.getD j false := by
      intro j hj
      apply hab j
      intro t ht
      apply hi t
      exact Finset.mem_biUnion.2 ⟨j, List.mem_toFinset.2 hj, ht⟩
    rcases hg with hg | hg | hg
    · have hr : rd g = g.inputs := by simp [rd, hg, GateOp.eval]
      rw [hr] at key
      rw [List.map_congr_left key]
    · have hr : rd g = g.inputs := by simp [rd, hg, GateOp.eval]
      rw [hr] at key
      rw [List.map_congr_left key]
    · have hr : rd g = g.inputs.take 1 := by simp [rd, hg, GateOp.eval]
      rw [hr] at key
      rw [hg]
      simp only [GateOp.eval]
      cases hin : g.inputs with
      | nil => rfl
      | cons j rest =>
        rw [hin] at key
        have hj := key j (by simp)
        simp only [List.map_cons, List.headD_cons, hj]
  · exact hab i hi

lemma inv_fold (xs ys : List Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (W : List (Finset ℕ)) (a b : List Bool), Inv xs ys W a b →
      Inv xs ys (gs.foldl supStep W) (gs.foldl wstep a) (gs.foldl wstep b) := by
  induction gs with
  | nil => intro W a b h; exact h
  | cons g gs ih =>
    intro W a b h
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ _
      (inv_step xs ys W a b g (hgs g List.mem_cons_self) h)

lemma inv_init (n : ℕ) (xs ys : List Bool) (hx : xs.length = n) (hy : ys.length = n) :
    Inv xs ys (start n) xs ys := by
  refine ⟨by simp [start, hx], by simp [start, hy], ?_⟩
  intro i hi
  by_cases h : i < n
  · apply hi i
    rw [List.getD_eq_getElem _ _ (by simpa [start] using h)]
    simp [start]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hC
  refine ⟨(C.gates.foldl PEqualNP.Outside.L_meta_3266.supStep
    (PEqualNP.Outside.L_meta_3266.start n)).getD C.output ∅, ?_, ?_⟩
  · have h := PEqualNP.Outside.L_meta_3266.bnd_fold C.gates (fun g hg => (hC g hg).2) _ 0
      (PEqualNP.Outside.L_meta_3266.bnd_init n) {C.output}
    simp only [Finset.singleton_biUnion, Finset.card_singleton] at h
    omega
  · intro xs ys hx hy hag
    have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg
      simpa using (hC g hg).1
    have hinv := PEqualNP.Outside.L_meta_3266.inv_fold xs ys C.gates hops _ xs ys
      (PEqualNP.Outside.L_meta_3266.inv_init n xs ys hx hy)
    exact hinv.2.2 C.output hag
