import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_925

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ?_, ?_, ?_⟩
  · exact g.inputs.toFinset_card_le.trans hlen
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have transfer (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true] at hx ⊢
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact transfer r hr (hx _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true] at hx ⊢
      obtain ⟨b, hb, hv⟩ := hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, transfer r hr hv⟩

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
private lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

private def input {n : ℕ} (U : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∈ U)

private lemma weight_input {n : ℕ} (U : Finset (Fin n)) :
    Finset.univ.filter (fun p => input U p = true) = U := by
  ext p
  simp [input]

private def piece {n m : ℕ} (S : Fin m → Finset (Fin n)) : Fin n ⊕ Fin m → Finset (Fin n)
  | .inl p => {p}
  | .inr j => S j

private lemma pieces_card {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 1 ≤ q) (hsize : ∀ j, (S j).card = q + 1)
    (hmeet : ∀ i j, (S i ∩ S j).Nonempty) (D : Finset (Fin n ⊕ Fin m)) :
    (D.biUnion (piece S)).card ≤ D.card * q + 1 := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert t D ht ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ht]
    cases t with
    | inl p =>
      have hu := Finset.card_union_le ({p} : Finset (Fin n)) (D.biUnion (piece S))
      simp only [Finset.card_singleton] at hu
      change ({p} ∪ D.biUnion (piece S)).card ≤ (D.card + 1) * q + 1
      nlinarith
    | inr j =>
      change (S j ∪ D.biUnion (piece S)).card ≤ (D.card + 1) * q + 1
      by_cases hex : ∃ k, Sum.inr k ∈ D
      · obtain ⟨k, hk⟩ := hex
        obtain ⟨p, hp⟩ := hmeet j k
        have hn : (S j ∩ D.biUnion (piece S)).Nonempty := by
          refine ⟨p, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1, ?_⟩⟩
          exact Finset.mem_biUnion.mpr ⟨Sum.inr k, hk, (Finset.mem_inter.mp hp).2⟩
        have hpos := Finset.card_pos.mpr hn
        have heq := Finset.card_union_add_card_inter (S j) (D.biUnion (piece S))
        rw [hsize j] at heq
        nlinarith
      · have hone : ∀ t ∈ D, (piece S t).card ≤ 1 := by
          intro t ht
          cases t with
          | inl p => simp [piece]
          | inr k => exact False.elim (hex ⟨k, ht⟩)
        have hd := Finset.card_biUnion_le_card_mul D (piece S) 1 hone
        simp only [mul_one] at hd
        have hu := Finset.card_union_le (S j) (D.biUnion (piece S))
        rw [hsize j] at hu
        nlinarith

private lemma pieces_inter_card {n m : ℕ} (S : Fin m → Finset (Fin n))
    (D : Finset (Fin n ⊕ Fin m)) (T : Finset (Fin n))
    (h : ∀ t ∈ D, (piece S t ∩ T).card ≤ 1) :
    ((D.biUnion (piece S)) ∩ T).card ≤ D.card := by
  classical
  have he : ((D.biUnion (piece S)) ∩ T) = D.biUnion (fun t => piece S t ∩ T) := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [he]
  simpa only [mul_one] using Finset.card_biUnion_le_card_mul D (fun t => piece S t ∩ T) 1 h

private def assigned {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (i : Fin m) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    value C (input (S i)) w = true ∧ ∀ j, i ≠ j → value C (input (S j)) w = false

private lemma row_bound {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 1 ≤ q) (hsize : ∀ j, (S j).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hmeet : ∀ i j, (S i ∩ S j).Nonempty) (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ)
    (hcorrect : ∀ i x, (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ K →
      value C x (out i) = decide (∀ p ∈ S i, x p = true))
    (i : Fin m) (c : ℕ) (hcq : c ≤ q) (hcK : c * q < K) :
    c ≤ (assigned S C i).card := by
  classical
  by_contra! hsmall
  have hcpos : 0 < c := by omega
  have hK : q + 1 ≤ K := by nlinarith
  have hroot : value C (input (S i)) (out i) = true := by
    rw [hcorrect i (input (S i)) (by rw [weight_input, hsize]; exact hK)]
    simp [input]
  let G := assigned S C i
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {out i}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let A := B.filter (fun w => value C (input (S i)) w = true)
  have supporting (a : {w // w ∈ A}) : ∃ t : Fin n ⊕ Fin m,
      value C (input (piece S t)) a.val = true ∧ (piece S t ∩ S i).card ≤ 1 := by
    have ha := Finset.mem_filter.mp a.property
    by_cases hn : a.val < n
    · let p : Fin n := ⟨a.val, hn⟩
      refine ⟨Sum.inl p, ?_, ?_⟩
      · change value C (input {p}) p = true
        simp [input_value, input]
      · exact (Finset.card_le_card (Finset.inter_subset_left : ({p} : Finset (Fin n)) ∩ S i ⊆ {p})).trans (by simp)
    · have hw : a.val < n + C.size := by
        by_contra! hw
        have hf := missing_value C (input (S i)) a.val hw
        rw [hf] at ha
        simp at ha
      have hj : ∃ j : Fin m, i ≠ j ∧ value C (input (S j)) a.val = true := by
        by_contra! hj
        apply Finset.disjoint_left.mp hd ha.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hw⟩, ha.2, ?_⟩
        intro j hij
        cases hv : value C (input (S j)) a.val with
        | false => rfl
        | true => exact False.elim (hj j hij hv)
      obtain ⟨j, hij, hv⟩ := hj
      exact ⟨Sum.inr j, hv, hinter j i hij.symm⟩
  choose t ht using supporting
  let D := A.attach.image t
  let U := D.biUnion (piece S)
  have hD : D.card ≤ B.card := calc
    D.card ≤ A.attach.card := Finset.card_image_le
    _ = A.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
  have hU : U.card ≤ K := by
    have hs := pieces_card S hq hsize hmeet D
    change U.card ≤ D.card * q + 1 at hs
    nlinarith
  have hinterU : (U ∩ S i).card ≤ D.card := by
    apply pieces_inter_card S D (S i)
    intro z hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hz
    exact (ht a).2
  have hlt : (U ∩ S i).card < (S i).card := by
    rw [hsize]
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hpU : p ∉ U := fun h => hpnot (Finset.mem_inter.mpr ⟨h, hp⟩)
  have hyfalse : value C (input U) (out i) = false := by
    rw [hcorrect i (input U) (by rwa [weight_input])]
    simp only [decide_eq_false_iff_not]
    intro hall
    exact hpU (of_decide_eq_true (hall p hp))
  have hytrue : value C (input U) (out i) = true := by
    apply hcut (input (S i)) (input U) _ (out i) (Finset.mem_singleton_self _) hroot
    intro w hw hv
    let a : {w // w ∈ A} := ⟨w, Finset.mem_filter.mpr ⟨hw, hv⟩⟩
    apply value_mono C hG (input (piece S (t a))) (input U) _ w (ht a).1
    intro r hr
    have hrmem : r ∈ piece S (t a) := of_decide_eq_true hr
    have htag : t a ∈ D := Finset.mem_image_of_mem t (Finset.mem_attach A a)
    exact decide_eq_true (Finset.mem_biUnion.mpr ⟨t a, htag, hrmem⟩)
  simp [hyfalse] at hytrue

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hinter gates out hG hcorrect c hcq hcK
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  have hmeet : ∀ i j, (S i ∩ S j).Nonempty := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hp : 0 < (S i).card := by rw [hsize]; omega
      simpa using Finset.card_pos.mp hp
    · exact Finset.card_pos.mp (by rw [hinter i j hij]; omega)
  have hcorr : ∀ i x, (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ K →
      value C x (out i) = decide (∀ p ∈ S i, x p = true) := by
    intro i x hx
    exact hcorrect i x hx
  let G (i : Fin m) := assigned S C i
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hf := hi.2 j hij
    rw [hf] at hj
    simp at hj
  have hsum : m * c = ∑ _i : Fin m, c := by simp
  rw [hsum]
  calc
    ∑ _i : Fin m, c ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      row_bound S (by omega) hsize (fun i j h => (hinter i j h).le) hmeet C hG out hcorr i c hcq hcK
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = gates.length := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
