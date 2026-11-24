import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2982_aux

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons]
    simp
    omega

lemma foldl_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.gates.foldl stepW x).getD w false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

def Rd (C : Circuit) (N : ℕ) (w u : ℕ) : Prop :=
  ∃ j g, w = N + j ∧ C.gates[j]? = some g ∧ u ∈ g.inputs

lemma val_split (N : ℕ) (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = N)
    (j : ℕ) (hpre : pre.length = j) (hrb : ∀ i ∈ g.inputs, i < N + j) :
    ((pre ++ g :: post).foldl stepW x).getD (N + j) false =
      g.op.eval (g.inputs.map fun i => ((pre ++ g :: post).foldl stepW x).getD i false) := by
  simp only [List.foldl_append, List.foldl_cons]
  have hW : (pre.foldl stepW x).length = N + j := by rw [foldl_len, hx, hpre]
  generalize hWdef : pre.foldl stepW x = W at hW ⊢
  have hl : (stepW W g).length = N + j + 1 := by simp [stepW, hW]
  rw [foldl_keep _ _ _ (by omega)]
  have hk : ∀ i, i < N + j → (post.foldl stepW (stepW W g)).getD i false = W.getD i false :=
    fun i hi => by
      rw [foldl_keep _ _ _ (by omega)]
      exact List.getD_append _ _ _ _ (by omega)
  have : g.inputs.map (fun i => (post.foldl stepW (stepW W g)).getD i false) =
      g.inputs.map (fun i => W.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hk i (hrb i hi)
  rw [this]
  simp [stepW, List.getD_eq_getElem?_getD, hW]

lemma val_gate (C : Circuit) (N : ℕ) (x : List Bool) (hx : x.length = N)
    (hrb : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < N + j)
    (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
    val C x (N + j) = g.op.eval (g.inputs.map fun i => val C x i) := by
  obtain ⟨hjl, hgj⟩ := List.getElem?_eq_some_iff.mp hj
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    rw [← hgj, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
  have h := val_split N (C.gates.take j) (C.gates.drop (j + 1)) g x hx j
    (by simp; omega) (hrb j g hj)
  rw [← hsplit] at h
  exact h

lemma indep (C : Circuit) (N : ℕ)
    (hrb : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < N + j)
    (x x' : List Bool) (hx : x.length = N) (hx' : x'.length = N) (i : ℕ)
    (hdiff : ∀ k, k ≠ i → x.getD k false = x'.getD k false) :
    ∀ w, ¬ Relation.ReflTransGen (Rd C N) w i → val C x w = val C x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnr
    by_cases hwN : w < N
    · have hwi : w ≠ i := fun h => hnr (h ▸ Relation.ReflTransGen.refl)
      unfold val
      rw [foldl_keep _ _ _ (by omega), foldl_keep _ _ _ (by omega)]
      exact hdiff w hwi
    · by_cases hwg : w < N + C.gates.length
      · obtain ⟨j, hj⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        subst hj
        have hjl : j < C.gates.length := by omega
        have hgj : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hjl
        rw [val_gate C N x hx hrb j _ hgj, val_gate C N x' hx' hrb j _ hgj]
        congr 1
        apply List.map_congr_left
        intro u hu
        apply ih u (by have := hrb j _ hgj u hu; omega)
        intro hreach
        exact hnr (Relation.ReflTransGen.head ⟨j, _, rfl, hgj, hu⟩ hreach)
      · unfold val
        rw [List.getD_eq_default _ _ (by rw [foldl_len, hx]; omega),
          List.getD_eq_default _ _ (by rw [foldl_len, hx']; omega)]


open Classical in
lemma cone_count (C : Circuit) (N out : ℕ) (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hout : out < N + C.gates.length) :
    ((Finset.range (N + C.gates.length)).filter
        (fun w => Relation.ReflTransGen (Rd C N) out w)).card ≤
      2 * (((Finset.range (N + C.gates.length)).filter
        (fun w => Relation.ReflTransGen (Rd C N) out w)).filter (fun w => N ≤ w)).card + 1 := by
  set R := (Finset.range (N + C.gates.length)).filter
    (fun w => Relation.ReflTransGen (Rd C N) out w) with hR
  set Gs := R.filter (fun w => N ≤ w) with hGs
  have houtR : out ∈ R :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hout, Relation.ReflTransGen.refl⟩
  let rd : ℕ → Finset ℕ := fun w => (C.gates.getD (w - N) ⟨GateOp.or, []⟩).inputs.toFinset
  have hget : ∀ j g, C.gates[j]? = some g → C.gates.getD (N + j - N) ⟨GateOp.or, []⟩ = g := by
    intro j g hj
    obtain ⟨hjl, hgj⟩ := List.getElem?_eq_some_iff.mp hj
    rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hjl, hgj]
  have hsub : R.erase out ⊆ Gs.biUnion rd := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨hne, huR⟩ := hu
    have huR' := (Finset.mem_filter.mp huR).2
    rcases Relation.ReflTransGen.cases_tail huR' with h | ⟨w, hw, hwu⟩
    · exact absurd h hne
    · obtain ⟨j, g, rfl, hj, hu'⟩ := hwu
      have hjl : j < C.gates.length := (List.getElem?_eq_some_iff.mp hj).1
      rw [Finset.mem_biUnion]
      refine ⟨N + j, ?_, ?_⟩
      · simp only [hGs, hR, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, hw⟩, by omega⟩
      · simp only [rd]
        rw [hget j g hj]
        simpa using hu'
  have hcard : (Gs.biUnion rd).card ≤ 2 * Gs.card := by
    calc (Gs.biUnion rd).card ≤ ∑ w ∈ Gs, (rd w).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ Gs, 2 := by
        apply Finset.sum_le_sum
        intro w hw
        simp only [hGs, hR, Finset.mem_filter, Finset.mem_range] at hw
        have hjl : w - N < C.gates.length := by omega
        have hmem : C.gates.getD (w - N) ⟨GateOp.or, []⟩ ∈ C.gates := by
          rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
        simp only [rd]
        exact (List.toFinset_card_le _).trans (hlen2 _ hmem).le
      _ = 2 * Gs.card := by simp [mul_comm]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem houtR] at h1
  have h2 : 1 ≤ R.card := Finset.card_pos.mpr ⟨out, houtR⟩
  omega

lemma ofFn_getD_true' (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = true ↔ ∃ h : i < n, x ⟨i, h⟩ = true := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma inc_getD (n : ℕ) (X Y : Finset (Fin n)) (k : ℕ) :
    (PEqualNP.GenericRejection.incidenceInput X Y).getD k false = true ↔
      ((∃ h : k < n, (⟨k, h⟩ : Fin n) ∈ X) ∨ (∃ h : n ≤ k ∧ k - n < n, (⟨k - n, h.2⟩ : Fin n) ∈ Y)) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  by_cases hk : k < n
  · rw [List.getD_append _ _ _ _ (by simpa using hk), ofFn_getD_true']
    constructor
    · rintro ⟨h, h2⟩
      exact Or.inl ⟨h, by simpa using h2⟩
    · rintro (⟨h, h2⟩ | ⟨h, _⟩)
      · exact ⟨h, by simpa using h2⟩
      · omega
  · rw [List.getD_append_right _ _ _ _ (by simpa using hk)]
    simp only [List.length_ofFn]
    rw [ofFn_getD_true']
    constructor
    · rintro ⟨h, h2⟩
      exact Or.inr ⟨⟨by omega, h⟩, by simpa using h2⟩
    · rintro (⟨h, _⟩ | ⟨h, h2⟩)
      · omega
      · exact ⟨h.2, by simpa using h2⟩


lemma gateAt_eq' (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C g = C.gates[g] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hg]

open Classical in
theorem main (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hne : ∀ l, (S l).Nonempty) (hcov : ∀ p, ∃ l, p ∈ S l)
    (hao : PEqualNP.TopForm.IsAO2 (n + n) C)
    (hright : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hsingle : ∀ (X Y : Finset (Fin n)), X.card + Y.card = 1 →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false) :
    n + n ≤ C.size + 1 := by
  obtain ⟨hand, hrb, hlen2⟩ := hao
  have hrb' : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + n + j := by
    intro j g hj i hi
    obtain ⟨hjl, hgj⟩ := List.getElem?_eq_some_iff.mp hj
    apply hrb j hjl i
    rw [gateAt_eq' C j hjl, hgj]
    exact hi
  by_cases hn : n = 0
  · subst hn; simp
  have hlenInp : ∀ X Y : Finset (Fin n),
      (PEqualNP.GenericRejection.incidenceInput X Y).length = n + n := by
    intro X Y; simp [PEqualNP.GenericRejection.incidenceInput]
  have hout : C.output < n + n + C.gates.length := by
    by_contra hge
    push_neg at hge
    obtain ⟨p, hp⟩ := hne ⟨0, by omega⟩
    have h := hright ⟨0, by omega⟩ p hp
    rw [eval_eq_val] at h
    unfold val at h
    rw [List.getD_eq_default _ _ (by rw [foldl_len, hlenInp]; omega)] at h
    exact absurd h (by simp)
  have hall : ∀ i, i < n + n → Relation.ReflTransGen (Rd C (n + n)) C.output i := by
    intro i hi
    by_contra hnr
    by_cases hip : i < n
    · obtain ⟨l, hl⟩ := hcov ⟨i, hip⟩
      have ht := hright l ⟨i, hip⟩ hl
      have hf := hsingle ∅ {l} (by simp)
      have heq := indep C (n + n) hrb'
        (PEqualNP.GenericRejection.incidenceInput ∅ {l})
        (PEqualNP.GenericRejection.incidenceInput {⟨i, hip⟩} {l})
        (hlenInp _ _) (hlenInp _ _) i (by
          intro k hk
          rw [Bool.eq_iff_iff, inc_getD, inc_getD]
          simp [Fin.ext_iff, hk]) C.output hnr
      rw [← eval_eq_val, ← eval_eq_val, hf, ht] at heq
      exact absurd heq (by simp)
    · obtain ⟨p, hp⟩ := hne ⟨i - n, by omega⟩
      have ht := hright ⟨i - n, by omega⟩ p hp
      have hf := hsingle {p} ∅ (by simp)
      have heq := indep C (n + n) hrb'
        (PEqualNP.GenericRejection.incidenceInput {p} ∅)
        (PEqualNP.GenericRejection.incidenceInput {p} {⟨i - n, by omega⟩})
        (hlenInp _ _) (hlenInp _ _) i (by
          intro k hk
          rw [Bool.eq_iff_iff, inc_getD, inc_getD]
          simp only [Finset.notMem_empty, Finset.mem_singleton, Fin.ext_iff, exists_false, or_false]
          constructor
          · intro h; exact Or.inl h
          · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
            · exact h
            · exfalso; apply hk; omega) C.output hnr
      rw [← eval_eq_val, ← eval_eq_val, hf, ht] at heq
      exact absurd heq (by simp)
  have hcount := cone_count C (n + n) C.output hlen2 hout
  set R := (Finset.range (n + n + C.gates.length)).filter
    (fun w => Relation.ReflTransGen (Rd C (n + n)) C.output w) with hR
  have hI : (R.filter (fun w => ¬ (n + n ≤ w))).card = n + n := by
    have : R.filter (fun w => ¬ (n + n ≤ w)) = Finset.range (n + n) := by
      ext w
      simp only [hR, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; omega
      · intro h; exact ⟨⟨by omega, hall w h⟩, by omega⟩
    rw [this]; simp
  have hpart := Finset.card_filter_add_card_filter_not (s := R) (fun w => n + n ≤ w)
  have hG : (R.filter (fun w => n + n ≤ w)).card ≤ C.gates.length := by
    have hsub : R.filter (fun w => n + n ≤ w) ⊆ Finset.Ico (n + n) (n + n + C.gates.length) := by
      intro w hw
      simp only [hR, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hw ⊢
      omega
    have := Finset.card_le_card hsub
    simpa using this
  have hsz : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_2982_aux

theorem PEqualNP.Outside.L_meta_2982 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), (x2 x4).Nonempty) → (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x5 ∈ x2 x6) → PEqualNP.TopForm.IsAO2 (x1 + x1) x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 x9 : Finset (Fin x1)), x8.card + x9.card = (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 x9) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) := by
  intro n S C hne hcov hao hright hsingle
  exact PEqualNP.Outside.L_meta_2982_aux.main n S C hne hcov hao hright hsingle
