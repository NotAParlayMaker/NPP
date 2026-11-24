import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2982

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.GenericRejection

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun i => L.getD i ∅).foldr (· ∪ ·) ∅

def suppStep {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  L ++ [gateSupp L g]

def initSupp (n : ℕ) : List (Finset (Fin n)) :=
  List.ofFn fun i : Fin n => ({i} : Finset (Fin n))

def supps (n : ℕ) (gs : List Gate) : List (Finset (Fin n)) :=
  gs.foldl suppStep (initSupp n)

lemma mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (x : Fin n) :
    x ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, x ∈ L.getD a ∅ := by
  unfold gateSupp
  induction g.inputs with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp, ih]

lemma length_supps (n : ℕ) (gs : List Gate) :
    (supps n gs).length = n + gs.length := by
  unfold supps
  have h : ∀ (L : List (Finset (Fin n))) (gs : List Gate),
      (gs.foldl suppStep L).length = L.length + gs.length := by
    intro L gs
    induction gs generalizing L with
    | nil => simp
    | cons g rest ih =>
      rw [List.foldl_cons, ih]
      simp [suppStep]
      omega
  rw [h]
  simp [initSupp]

def Agree {n : ℕ} (w1 w2 : List Bool) (L : List (Finset (Fin n))) (u1 u2 : List Bool) : Prop :=
  L.length = u1.length ∧ u1.length = u2.length ∧
    ∀ k : ℕ, (∀ i ∈ L.getD k ∅, w1.getD i.val false = w2.getD i.val false) →
      u1.getD k false = u2.getD k false

lemma agree_foldl {n : ℕ} (w1 w2 : List Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (u1 u2 : List Bool),
      Agree w1 w2 L u1 u2 →
      Agree w1 w2 (gs.foldl suppStep L) (gs.foldl step u1) (gs.foldl step u2) := by
  induction gs with
  | nil => intro L u1 u2 h; exact h
  | cons g rest ih =>
    intro L u1 u2 ⟨h1, h2, h3⟩
    apply ih
    refine ⟨by simp [suppStep, step, h1], by simp [step, h2], ?_⟩
    intro k hk
    rcases lt_trichotomy k L.length with hlt | heq | hgt
    · have hL : (suppStep L g).getD k ∅ = L.getD k ∅ := List.getD_append _ _ _ _ hlt
      rw [hL] at hk
      unfold step
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact h3 k hk
    · subst heq
      have hL : (suppStep L g).getD L.length ∅ = gateSupp L g := by
        unfold suppStep; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
      rw [hL] at hk
      unfold step
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [h1, h2, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hk i ((mem_gateSupp L g i).mpr ⟨a, ha, hi⟩))
    · unfold step
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma agree_init {n : ℕ} (w1 w2 : List Bool) (hw1 : w1.length = n) (hw2 : w2.length = n) :
    Agree w1 w2 (initSupp n) w1 w2 := by
  refine ⟨by simp [initSupp, hw1], by omega, ?_⟩
  intro k hk
  by_cases hkn : k < n
  · have hL : (initSupp n).getD k ∅ = ({⟨k, hkn⟩} : Finset (Fin n)) := by
      unfold initSupp
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hkn]
    rw [hL] at hk
    exact hk ⟨k, hkn⟩ (by simp)
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma eval_eq_of_not_mem_supp {n : ℕ} (C : Circuit) (w1 w2 : List Bool)
    (hw1 : w1.length = n) (hw2 : w2.length = n) (i : Fin n)
    (hdiff : ∀ j : Fin n, j ≠ i → w1.getD j.val false = w2.getD j.val false)
    (hnot : i ∉ (supps n C.gates).getD C.output ∅) :
    C.eval w1 = C.eval w2 := by
  have hag := agree_foldl w1 w2 C.gates (initSupp n) w1 w2 (agree_init w1 w2 hw1 hw2)
  exact hag.2.2 C.output (fun j hj => hdiff j (fun heq => hnot (heq ▸ hj)))

lemma cover_card_le (n : ℕ) (gs : List Gate) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ S : Finset ℕ, (S.biUnion fun w => (supps n gs).getD w ∅).card ≤ S.card + gs.length := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro S
    calc
      (S.biUnion fun w => (supps n []).getD w ∅).card
          ≤ ∑ w ∈ S, ((supps n []).getD w ∅).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ S, 1 := by
        apply Finset.sum_le_sum
        intro w _
        by_cases hwn : w < n
        · have hL : (supps n []).getD w ∅ = ({⟨w, hwn⟩} : Finset (Fin n)) := by
            unfold supps initSupp
            simp only [List.foldl_nil]
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp [hwn]
          rw [hL]; simp
        · have hL : (supps n []).getD w ∅ = ∅ := by
            unfold supps initSupp
            simp only [List.foldl_nil]
            exact List.getD_eq_default _ _ (by simp; omega)
          rw [hL]; simp
      _ = S.card + ([] : List Gate).length := by simp
  | append_singleton gs g ih =>
    intro S
    have hfan_gs : ∀ g0 ∈ gs, g0.inputs.length ≤ 2 := fun g0 hg0 => hfan g0 (by simp [hg0])
    have hg_len : g.inputs.length ≤ 2 := hfan g (by simp)
    have hstep : supps n (gs ++ [g]) = suppStep (supps n gs) g := by
      simp [supps, List.foldl_append]
    set m := n + gs.length
    have hmlen : (supps n gs).length = m := length_supps n gs
    have hget_ne : ∀ w, w ≠ m → (supps n (gs ++ [g])).getD w ∅ = (supps n gs).getD w ∅ := by
      intro w hw
      rw [hstep]
      unfold suppStep
      by_cases hlt : w < (supps n gs).length
      · exact List.getD_append _ _ _ _ hlt
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    have hget_m : (supps n (gs ++ [g])).getD m ∅ = gateSupp (supps n gs) g := by
      rw [hstep]
      unfold suppStep
      rw [← hmlen, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    by_cases hmS : m ∈ S
    · let S' : Finset ℕ := S.erase m ∪ g.inputs.toFinset
      have hsub : (S.biUnion fun w => (supps n (gs ++ [g])).getD w ∅) ⊆
          (S'.biUnion fun w => (supps n gs).getD w ∅) := by
        intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨w, hwS, hxw⟩ := hx
        by_cases hwm : w = m
        · subst hwm
          rw [hget_m, mem_gateSupp] at hxw
          obtain ⟨a, ha, hxa⟩ := hxw
          exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hxa⟩
        · rw [hget_ne w hwm] at hxw
          exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hwS⟩), hxw⟩
      have hcardS' : S'.card ≤ S.card + 1 := by
        have h1 : S'.card ≤ (S.erase m).card + g.inputs.toFinset.card := Finset.card_union_le _ _
        have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
        have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le g.inputs
        have h4 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
        omega
      have hih := ih hfan_gs S'
      have hle := Finset.card_le_card hsub
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · have hsub : (S.biUnion fun w => (supps n (gs ++ [g])).getD w ∅) ⊆
          (S.biUnion fun w => (supps n gs).getD w ∅) := by
        intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨w, hwS, hxw⟩ := hx
        have hwm : w ≠ m := fun h => hmS (h ▸ hwS)
        rw [hget_ne w hwm] at hxw
        exact ⟨w, hwS, hxw⟩
      have hih := ih hfan_gs S
      have hle := Finset.card_le_card hsub
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

lemma incidenceInput_len {n : ℕ} (X Y : Finset (Fin n)) :
    (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

lemma incidenceInput_getD {n : ℕ} (X Y : Finset (Fin n)) (j : Fin (n + n)) :
    (incidenceInput X Y).getD j.val false =
      if h : j.val < n then decide ((⟨j.val, h⟩ : Fin n) ∈ X)
      else decide ((⟨j.val - n, by omega⟩ : Fin n) ∈ Y) := by
  unfold incidenceInput
  by_cases h : j.val < n
  · simp only [h, ↓reduceDIte]
    rw [List.getD_append _ _ _ _ (by simp [h]), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [h]
  · simp only [h, ↓reduceDIte]
    rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
      List.length_ofFn, List.getElem?_ofFn]
    have hlt : j.val - n < n := by omega
    simp [hlt]

lemma core (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : Circuit)
    (h1 : ∀ l : Fin x1, (x2 l).Nonempty)
    (h2 : ∀ p : Fin x1, ∃ l : Fin x1, p ∈ x2 l)
    (hao : IsAO2 (x1 + x1) x3)
    (hright : RightOnIncidentPairs x2 x3)
    (hsingle : ∀ X Y : Finset (Fin x1), X.card + Y.card = 1 → x3.eval (incidenceInput X Y) = false) :
    x1 + x1 ≤ x3.size + 1 := by
  have hfan : ∀ g ∈ x3.gates, g.inputs.length ≤ 2 := fun g hg => by
    have := hao.2.2 g hg; omega
  have hall : ∀ i : Fin (x1 + x1), i ∈ (supps (x1 + x1) x3.gates).getD x3.output ∅ := by
    intro i
    by_contra hnot
    by_cases hi : i.val < x1
    · let p : Fin x1 := ⟨i.val, hi⟩
      obtain ⟨l, hpl⟩ := h2 p
      have htrue : x3.eval (incidenceInput {p} {l}) = true := hright l p hpl
      have hfalse : x3.eval (incidenceInput ∅ {l}) = false := hsingle ∅ {l} (by simp)
      have heq := eval_eq_of_not_mem_supp x3 (incidenceInput {p} {l}) (incidenceInput ∅ {l})
        (incidenceInput_len _ _) (incidenceInput_len _ _) i (fun j hji => by
          rw [incidenceInput_getD, incidenceInput_getD]
          by_cases hj : j.val < x1
          · simp only [hj, ↓reduceDIte, Finset.notMem_empty, decide_false, Finset.mem_singleton]
            have hne : (⟨j.val, hj⟩ : Fin x1) ≠ p := by
              intro h; apply hji; ext; simpa [p] using congrArg Fin.val h
            simp [hne]
          · simp only [hj, ↓reduceDIte]) hnot
      rw [htrue, hfalse] at heq
      exact Bool.noConfusion heq
    · let l : Fin x1 := ⟨i.val - x1, by omega⟩
      obtain ⟨p, hpl⟩ := h1 l
      have htrue : x3.eval (incidenceInput {p} {l}) = true := hright l p hpl
      have hfalse : x3.eval (incidenceInput {p} ∅) = false := hsingle {p} ∅ (by simp)
      have heq := eval_eq_of_not_mem_supp x3 (incidenceInput {p} {l}) (incidenceInput {p} ∅)
        (incidenceInput_len _ _) (incidenceInput_len _ _) i (fun j hji => by
          rw [incidenceInput_getD, incidenceInput_getD]
          by_cases hj : j.val < x1
          · simp only [hj, ↓reduceDIte]
          · simp only [hj, ↓reduceDIte, Finset.notMem_empty, decide_false, Finset.mem_singleton]
            have hne : (⟨j.val - x1, by omega⟩ : Fin x1) ≠ l := by
              intro h; apply hji; ext
              have hv : j.val - x1 = i.val - x1 := congrArg Fin.val h
              omega
            simp [hne]) hnot
      rw [htrue, hfalse] at heq
      exact Bool.noConfusion heq
  have hsub : (Finset.univ : Finset (Fin (x1 + x1))) ⊆
      ({x3.output} : Finset ℕ).biUnion fun w => (supps (x1 + x1) x3.gates).getD w ∅ := by
    intro i _
    rw [Finset.mem_biUnion]
    exact ⟨x3.output, by simp, hall i⟩
  have hcard1 : x1 + x1 ≤ (({x3.output} : Finset ℕ).biUnion fun w => (supps (x1 + x1) x3.gates).getD w ∅).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  have hcard2 := cover_card_le (x1 + x1) x3.gates hfan {x3.output}
  simp only [Finset.card_singleton] at hcard2
  change x1 + x1 ≤ x3.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_2982

theorem PEqualNP.Outside.L_meta_2982 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), (x2 x4).Nonempty) → (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x5 ∈ x2 x6) → PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 x9 : Finset (Fin x1)), x8.card + x9.card = (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 x9) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_2982.core
