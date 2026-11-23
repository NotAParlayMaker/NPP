import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.BoolSum529

theorem wires_snoc (L : List Gate) (g : Gate) (o : ℕ) (y : List Bool) :
    Circuit.wires ⟨L ++ [g], o⟩ y = Circuit.wires ⟨L, o⟩ y ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨L, o⟩ y).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (L : List Gate) (o : ℕ) (y : List Bool) :
    (Circuit.wires ⟨L, o⟩ y).length = y.length + L.length := by
  induction L using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton L g ih => rw [wires_snoc]; simp [ih]; omega

def wf (n : ℕ) (L : List Gate) (i : ℕ) (x : Fin n → Bool) : Bool :=
  (Circuit.wires ⟨L, 0⟩ (List.ofFn x)).getD i false

theorem wf_snoc (n : ℕ) (L : List Gate) (g : Gate) (i : ℕ) (x : Fin n → Bool) :
    wf n (L ++ [g]) i x = if i = n + L.length then
      g.op.eval (g.inputs.map fun j => wf n L j x) else wf n L i x := by
  have hlen := wires_length L 0 (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  unfold wf
  rw [wires_snoc]
  split_ifs with h
  · subst h
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem wf_input (n : ℕ) (L : List Gate) (v : Fin n) (x : Fin n → Bool) :
    wf n L v.val x = x v := by
  induction L using List.reverseRecOn with
  | nil => simp [wf, Circuit.wires, List.getD_eq_getElem?_getD]
  | append_singleton L g ih =>
    simp [wf_snoc, ih, show v.val ≠ n + L.length by omega]

theorem wf_nil_ge (n : ℕ) (i : ℕ) (h : n ≤ i) (x : Fin n → Bool) : wf n [] i x = false := by
  simp [wf, Circuit.wires, List.getD_eq_getElem?_getD, show ¬ i < n by omega]

theorem eval_or (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ j ∈ l, f j = true := by
  simp [GateOp.eval]

theorem eval_and (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ j ∈ l, f j = true := by
  simp [GateOp.eval]

def Good (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Mono {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) → f x = true → f y = true

theorem mono_wf (n : ℕ) (L : List Gate) (hL : ∀ g ∈ L, Good g) (i : ℕ) : Mono (wf n L i) := by
  induction L using List.reverseRecOn generalizing i with
  | nil =>
    intro x y hxy hx
    by_cases h : i < n
    · have := wf_input n [] ⟨i, h⟩
      simp only at this
      rw [this] at hx ⊢
      exact hxy _ hx
    · rw [wf_nil_ge n i (by omega)] at hx
      exact absurd hx (by simp)
  | append_singleton L g ih =>
    have hL' : ∀ g ∈ L, Good g := fun g hg => hL g (by simp [hg])
    have hg : Good g := hL g (by simp)
    intro x y hxy hx
    rw [wf_snoc] at hx ⊢
    split_ifs at hx ⊢ with h
    · rcases hg.1 with hop | hop
      · rw [hop, eval_and] at hx ⊢
        exact fun j hj => ih hL' j x y hxy (hx j hj)
      · rw [hop, eval_or] at hx ⊢
        obtain ⟨j, hj, hj'⟩ := hx
        exact ⟨j, hj, ih hL' j x y hxy hj'⟩
    · exact ih hL' i x y hxy hx

def eS {n : ℕ} (v : Fin n) : Fin n → Bool := fun u => decide (u = v)

def Vs {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => f (eS v) = true)

def Clean {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, (∀ v ∈ S, x v = false) → f x = false

def Fam (n : ℕ) (S : Finset (Fin n)) (L : List Gate) : Set (Finset (Fin n)) :=
  {B | ∃ i, Clean S (wf n L i) ∧ B = Vs (wf n L i)}

theorem vs_subset {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool} (h : Clean S f) :
    Vs f ⊆ S := by
  intro v hv
  by_contra hvS
  have := h (eS v) (fun u hu => by
    simp only [eS, decide_eq_false_iff_not]
    rintro rfl
    exact hvS hu)
  simp [Vs, this] at hv

theorem singleton_mem_fam (n : ℕ) (S : Finset (Fin n)) (L : List Gate) (v : Fin n)
    (hv : v ∈ S) : ({v} : Finset (Fin n)) ∈ Fam n S L := by
  refine ⟨v.val, ?_, ?_⟩
  · intro x hx
    rw [wf_input]
    exact hx v hv
  · ext u
    simp [Vs, wf_input, eS, eq_comm]

theorem fam_nil_card (n : ℕ) (S : Finset (Fin n)) (B : Finset (Fin n)) (hB : B ∈ Fam n S []) :
    B.card ≤ 1 := by
  obtain ⟨i, -, rfl⟩ := hB
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Vs, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases h : i < n
  · have e := wf_input n [] ⟨i, h⟩
    simp only at e
    rw [e] at ha hb
    simp only [eS, decide_eq_true_eq] at ha hb
    rw [← ha, ← hb]
  · rw [wf_nil_ge n i (by omega)] at ha
    exact absurd ha (by simp)

theorem fam_snoc (n : ℕ) (S : Finset (Fin n)) (L : List Gate) (g : Gate) (B : Finset (Fin n))
    (hB : B ∈ Fam n S (L ++ [g])) :
    B ∈ Fam n S L ∨ (Clean S (wf n (L ++ [g]) (n + L.length)) ∧
      B = Vs (wf n (L ++ [g]) (n + L.length))) := by
  obtain ⟨i, hc, rfl⟩ := hB
  by_cases h : i = n + L.length
  · subst h
    exact Or.inr ⟨hc, rfl⟩
  · have e : wf n (L ++ [g]) i = wf n L i := by
      funext x
      simp [wf_snoc, h]
    rw [e] at hc ⊢
    exact Or.inl ⟨i, hc, rfl⟩

theorem new_eval (n : ℕ) (L : List Gate) (g : Gate) (x : Fin n → Bool) :
    wf n (L ++ [g]) (n + L.length) x = g.op.eval (g.inputs.map fun j => wf n L j x) := by
  simp [wf_snoc]

theorem cover_for_new (n : ℕ) (S : Finset (Fin n)) (L : List Gate) (g : Gate)
    (hL : ∀ g ∈ L, Good g) (hg : Good g) (hc : Clean S (wf n (L ++ [g]) (n + L.length))) :
    ∃ D : Finset (Finset (Fin n)), (↑D : Set (Finset (Fin n))) ⊆ Fam n S L ∧
      Vs (wf n (L ++ [g]) (n + L.length)) ⊆ D.sup id ∧
      (D.card ≤ 1 ∨ (D.card ≤ 2 ∧ 2 ≤ (Vs (wf n (L ++ [g]) (n + L.length))).card)) := by
  set B := Vs (wf n (L ++ [g]) (n + L.length)) with hBdef
  by_cases hcard : 2 ≤ B.card
  · rcases hg.1 with hop | hop
    · -- an AND gate: one of its inputs is already clean
      have hex : ∃ j ∈ g.inputs, Clean S (wf n L j) := by
        by_contra hno
        push Not at hno
        have hw : ∀ j, j ∈ g.inputs → ∃ y : Fin n → Bool,
            (∀ v ∈ S, y v = false) ∧ wf n L j y = true := by
          intro j hj
          obtain ⟨y, hy1, hy2⟩ : ∃ y : Fin n → Bool, (∀ v ∈ S, y v = false) ∧
              ¬ wf n L j y = false := by
            have := hno j hj
            simp only [Clean, not_forall, exists_prop] at this
            exact this
          exact ⟨y, hy1, by simpa using hy2⟩
        choose y hy using hw
        let z : Fin n → Bool := fun v =>
          @decide (∃ j, ∃ hj : j ∈ g.inputs, y j hj v = true) (Classical.propDecidable _)
        have hz : ∀ v ∈ S, z v = false := by
          intro v hv
          simp only [z, decide_eq_false_iff_not, not_exists]
          intro j hj
          simp [(hy j hj).1 v hv]
        have := hc z hz
        rw [new_eval, hop] at this
        have htrue : GateOp.and.eval (g.inputs.map fun j => wf n L j z) = true := by
          rw [eval_and]
          intro j hj
          refine mono_wf n L hL j (y j hj) z ?_ (hy j hj).2
          intro v hv
          simp only [z, decide_eq_true_eq]
          exact ⟨j, hj, hv⟩
        rw [this] at htrue
        exact absurd htrue (by simp)
      obtain ⟨j, hj, hjc⟩ := hex
      refine ⟨{Vs (wf n L j)}, ?_, ?_, Or.inl (by simp)⟩
      · intro B' hB'
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hB'
        exact ⟨j, hjc, hB'⟩
      · intro v hv
        simp only [hBdef, Vs, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [new_eval, hop, eval_and] at hv
        simp only [Finset.sup_singleton, id, Vs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hv j hj
    · -- an OR gate: every input is clean
      refine ⟨g.inputs.toFinset.image (fun j => Vs (wf n L j)), ?_, ?_, ?_⟩
      · intro B' hB'
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, List.mem_toFinset] at hB'
        obtain ⟨j, hj, rfl⟩ := hB'
        refine ⟨j, ?_, rfl⟩
        intro x hx
        have := hc x hx
        rw [new_eval, hop] at this
        by_contra hne
        have htrue : GateOp.or.eval (g.inputs.map fun j => wf n L j x) = true :=
          (eval_or _ _).2 ⟨j, hj, by simpa using hne⟩
        rw [this] at htrue
        exact absurd htrue (by simp)
      · intro v hv
        simp only [hBdef, Vs, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [new_eval, hop, eval_or] at hv
        obtain ⟨j, hj, hjv⟩ := hv
        rw [Finset.mem_sup]
        refine ⟨Vs (wf n L j), ?_, ?_⟩
        · simp only [Finset.mem_image, List.mem_toFinset]
          exact ⟨j, hj, rfl⟩
        · simp [Vs, hjv]
      · right
        refine ⟨?_, hcard⟩
        calc _ ≤ g.inputs.toFinset.card := Finset.card_image_le
          _ ≤ g.inputs.length := List.toFinset_card_le _
          _ ≤ 2 := hg.2
  · -- at most one element: use the input wires
    refine ⟨B.image (fun v => ({v} : Finset (Fin n))), ?_, ?_, ?_⟩
    · intro B' hB'
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hB'
      obtain ⟨v, hv, rfl⟩ := hB'
      exact singleton_mem_fam n S L v (vs_subset hc hv)
    · intro v hv
      rw [Finset.mem_sup]
      exact ⟨{v}, Finset.mem_image_of_mem _ hv, by simp⟩
    · left
      calc _ ≤ B.card := Finset.card_image_le
        _ ≤ 1 := by omega

theorem step_cover (n : ℕ) (S : Finset (Fin n)) (L : List Gate) (g : Gate)
    (hL : ∀ g ∈ L, Good g) (hg : Good g) (C : Finset (Finset (Fin n)))
    (hC : (↑C : Set (Finset (Fin n))) ⊆ Fam n S (L ++ [g])) (hS : S ⊆ C.sup id) :
    ∃ C' : Finset (Finset (Fin n)), (↑C' : Set (Finset (Fin n))) ⊆ Fam n S L ∧
      S ⊆ C'.sup id ∧ (C'.card ≤ C.card ∨ (C'.card ≤ C.card + 1 ∧
        Clean S (wf n (L ++ [g]) (n + L.length)) ∧
        2 ≤ (Vs (wf n (L ++ [g]) (n + L.length))).card)) := by
  set B := Vs (wf n (L ++ [g]) (n + L.length)) with hBdef
  by_cases hB : Clean S (wf n (L ++ [g]) (n + L.length)) ∧ B ∈ C
  · obtain ⟨D, hD1, hD2, hD3⟩ := cover_for_new n S L g hL hg hB.1
    refine ⟨C.erase B ∪ D, ?_, ?_, ?_⟩
    · intro B' hB'
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hB'
      rcases hB' with hB' | hB'
      · rcases fam_snoc n S L g B' (hC (Finset.mem_of_mem_erase hB')) with h | h
        · exact h
        · exact absurd h.2 (Finset.ne_of_mem_erase hB')
      · exact hD1 hB'
    · intro v hv
      obtain ⟨c, hc, hvc⟩ := Finset.mem_sup.1 (hS hv)
      by_cases hcB : c = B
      · subst hcB
        obtain ⟨d, hd, hvd⟩ := Finset.mem_sup.1 (hD2 hvc)
        exact Finset.mem_sup.2 ⟨d, Finset.mem_union_right _ hd, hvd⟩
      · exact Finset.mem_sup.2 ⟨c, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hcB, hc⟩), hvc⟩
    · have h1 := Finset.card_union_le (C.erase B) D
      have h2 := Finset.card_erase_of_mem hB.2
      have h3 : 1 ≤ C.card := Finset.card_pos.2 ⟨B, hB.2⟩
      rcases hD3 with hD3 | hD3
      · left; omega
      · right; exact ⟨by omega, hB.1, hD3.2⟩
  · refine ⟨C, ?_, hS, Or.inl le_rfl⟩
    intro B' hB'
    rcases fam_snoc n S L g B' (hC hB') with h | h
    · exact h
    · exact absurd ⟨h.1, by rw [hBdef, ← h.2]; exact hB'⟩ hB

theorem sum_step {m : ℕ} (a b : Fin m → ℕ) (P : Fin m → Prop)
    (huniq : ∀ w w', P w → P w' → w = w')
    (h : ∀ w, b w ≤ a w ∨ (b w ≤ a w + 1 ∧ P w)) :
    ∑ w, b w ≤ ∑ w, a w + 1 := by
  by_cases hex : ∃ w0, P w0
  · obtain ⟨w0, hw0⟩ := hex
    calc ∑ w, b w ≤ ∑ w, (a w + if w = w0 then 1 else 0) := by
          apply Finset.sum_le_sum
          intro w _
          rcases h w with h | h
          · split_ifs <;> omega
          · have := huniq w w0 h.2 hw0
            simp [this] at h ⊢
            omega
      _ = ∑ w, a w + 1 := by
          rw [Finset.sum_add_distrib]
          simp
  · push Not at hex
    calc ∑ w, b w ≤ ∑ w, a w := by
          apply Finset.sum_le_sum
          intro w _
          rcases h w with h | h
          · exact h
          · exact absurd h.2 (hex w)
      _ ≤ ∑ w, a w + 1 := Nat.le_succ _

theorem main (n m : ℕ) (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (L : List Gate)
    (hL : ∀ g ∈ L, Good g) (C : Fin m → Finset (Finset (Fin n)))
    (hC : ∀ w, (↑(C w) : Set (Finset (Fin n))) ⊆ Fam n (S w) L)
    (hcov : ∀ w, S w ⊆ (C w).sup id) :
    ∑ w, (S w).card ≤ ∑ w, (C w).card + L.length := by
  induction L using List.reverseRecOn generalizing C with
  | nil =>
    simp only [List.length_nil, add_zero]
    apply Finset.sum_le_sum
    intro w _
    calc (S w).card ≤ ((C w).sup id).card := Finset.card_le_card (hcov w)
      _ ≤ ∑ c ∈ C w, c.card := by
          rw [Finset.sup_eq_biUnion]
          exact Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C w, 1 := Finset.sum_le_sum (fun c hc => fam_nil_card n (S w) c (hC w hc))
      _ = (C w).card := by simp
  | append_singleton L g ih =>
    have hL' : ∀ g ∈ L, Good g := fun g hg => hL g (by simp [hg])
    have hg : Good g := hL g (by simp)
    have hstep := fun w => step_cover n (S w) L g hL' hg (C w) (hC w) (hcov w)
    choose C' hC'1 hC'2 hC'3 using hstep
    have hih := ih hL' C' hC'1 hC'2
    have hsum := sum_step (fun w => (C w).card) (fun w => (C' w).card)
      (fun w => Clean (S w) (wf n (L ++ [g]) (n + L.length)) ∧
        2 ≤ (Vs (wf n (L ++ [g]) (n + L.length))).card)
      (by
        intro w w' hw hw'
        by_contra hne
        have h1 := vs_subset hw.1
        have h2 := vs_subset hw'.1
        have := Finset.card_le_card (Finset.subset_inter h1 h2)
        have := hS w w' hne
        omega)
      (fun w => hC'3 w)
    simp only [List.length_append, List.length_singleton]
    omega

end PEqualNP.Outside.BoolSum529

open PEqualNP.Outside.BoolSum529 in
theorem PEqualNP.Outside.L_meta_529 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  intro n m S hS gates out hgates heval
  have hval : ∀ w x, wf n gates (out w) x = decide (∃ v ∈ S w, x v = true) := by
    intro w x
    exact heval w x
  have hmem : ∀ w, S w ∈ Fam n (S w) gates := by
    intro w
    refine ⟨out w, ?_, ?_⟩
    · intro x hx
      rw [hval]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv
      simp [hx v hv]
    · ext v
      simp [Vs, hval, eS]
  let C : Fin m → Finset (Finset (Fin n)) := fun w => if (S w).Nonempty then {S w} else ∅
  have hmain := main n m S hS gates hgates C
    (by
      intro w B hB
      simp only [C] at hB
      split_ifs at hB with h
      · simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hB
        rw [hB]
        exact hmem w
      · simp at hB)
    (by
      intro w
      simp only [C]
      split_ifs with h
      · simp
      · rw [Finset.not_nonempty_iff_eq_empty.1 h]
        exact Finset.empty_subset _)
  have hper : ∀ w, ((S w).card - 1) + (C w).card ≤ (S w).card := by
    intro w
    simp only [C]
    split_ifs with h
    · have := Finset.card_pos.2 h
      simp
      omega
    · simp
  have := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hper w)
  rw [Finset.sum_add_distrib] at this
  omega
