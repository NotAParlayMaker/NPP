import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- The evaluation and cut lemmas adapt L-meta-270 and AdrienDeliege's PR 1359.

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
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
        and_imp] at hx ⊢
      rintro _ r hm rfl
      exact hr r hm (hx _ r hm rfl)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨_, ⟨r, hm, rfl⟩, hv⟩ := hx
      exact ⟨_, ⟨r, hm, rfl⟩, hr r hm hv⟩

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

private abbrev monotoneGates (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private def bits {n : ℕ} (T : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ T)

private def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    value C (bits (S i)) w = true ∧ ∀ j : Fin m, j ≠ i → value C (bits (S j)) w = false

-- One full witness set costs q plus one. Every further witness costs at most q.
private lemma unionBound {ι α : Type} [DecidableEq ι] [DecidableEq α] {m q : ℕ}
    (S : Fin m → Finset α) (sizes : ∀ i, (S i).card = q + 1)
    (meets : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (hq : 1 ≤ q)
    (B : Finset ι) (T : ι → Finset α)
    (kind : ∀ b ∈ B, (T b).card ≤ 1 ∨ ∃ j, T b = S j) :
    (B.biUnion T).card ≤ B.card * q + 1 := by
  classical
  by_cases large : ∃ a ∈ B, ∃ j, T a = S j
  · obtain ⟨a, ha, j, hj⟩ := large
    let diff := fun b => T b \ T a
    have diffSmall : ∀ b ∈ B.erase a, (diff b).card ≤ q := by
      intro b hb
      rcases kind b (Finset.mem_of_mem_erase hb) with small | ⟨i, hi⟩
      · exact ((Finset.card_le_card Finset.sdiff_subset).trans small).trans hq
      · change (T b \ T a).card ≤ q
        rw [hi, hj]
        by_cases he : i = j
        · subst i
          simp
        · have hh := Finset.card_sdiff_add_card_inter (S i) (S j)
          rw [meets i j he, sizes i] at hh
          omega
    have cover : B.biUnion T ⊆ T a ∪ (B.erase a).biUnion diff := by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
      by_cases hxa : x ∈ T a
      · exact Finset.mem_union_left _ hxa
      · have hba : b ≠ a := fun he => hxa (he ▸ hxb)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, Finset.mem_sdiff.mpr ⟨hxb, hxa⟩⟩)
    have hunion := Finset.card_union_le (T a) ((B.erase a).biUnion diff)
    have hd := Finset.card_biUnion_le_card_mul (B.erase a) diff q diffSmall
    have hx := Finset.card_le_card cover
    have hm := congrArg (fun v : ℕ => v * q) (Finset.card_erase_add_one ha)
    simp only [Nat.add_mul, Nat.one_mul] at hm
    have haSize : (T a).card = q + 1 := by rw [hj, sizes]
    rw [haSize] at hunion
    omega
  · have small : ∀ b ∈ B, (T b).card ≤ 1 := by
      intro b hb
      exact (kind b hb).resolve_right (fun h => large ⟨b, hb, h⟩)
    have h := Finset.card_biUnion_le_card_mul B T 1 small
    simp only [Nat.mul_one] at h
    exact h.trans ((by simpa using Nat.mul_le_mul_left B.card hq : B.card ≤ B.card * q).trans
      (Nat.le_add_right ..))

private lemma intersectionBound {ι α : Type} [DecidableEq α] (B : Finset ι)
    (T : ι → Finset α) (S : Finset α) (h : ∀ b ∈ B, (T b ∩ S).card ≤ 1) :
    ((B.biUnion T) ∩ S).card ≤ B.card := by
  have he : (B.biUnion T) ∩ S = B.biUnion (fun b => T b ∩ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨b, hb, hxb⟩, hx⟩
      exact ⟨b, hb, hxb, hx⟩
    · rintro ⟨b, hb, hxb, hx⟩
      exact ⟨⟨b, hb, hxb⟩, hx⟩
  rw [he]
  simpa using Finset.card_biUnion_le_card_mul B (fun b => T b ∩ S) 1 h

private lemma witnesses {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m)
    (w : ℕ) (hw : w ∉ specific C S i) (hv : value C (bits (S i)) w = true) :
    ∃ T : Finset (Fin n), ((T.card ≤ 1) ∨ ∃ j ≠ i, T = S j) ∧ value C (bits T) w = true := by
  classical
  by_cases hinput : w < n
  · let p : Fin n := ⟨w, hinput⟩
    refine ⟨{p}, Or.inl (by simp), ?_⟩
    change value C (bits {p}) p = true
    simp [input_value, bits]
  · have hvalid : w < n + C.size := by
      by_contra! bad
      rw [missing_value C _ _ bad] at hv
      contradiction
    have h : ∃ j ≠ i, value C (bits (S j)) w = true := by
      by_contra! hno
      exact hw (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hvalid⟩, hv,
        fun j hj => Bool.eq_false_iff.mpr (hno j hj)⟩)
    obtain ⟨j, hj, ht⟩ := h
    exact ⟨S j, Or.inr ⟨j, hj, rfl⟩, ht⟩

private lemma perOutput {n m q K c : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (out : Fin m → ℕ) (hG : monotoneGates C) (i : Fin m)
    (sizes : ∀ j, (S j).card = q + 1) (meets : ∀ j k, j ≠ k → (S j ∩ S k).card = 1)
    (hq : 2 ≤ q) (hc : c ≤ q) (hK : c * q < K)
    (correct : ∀ T : Finset (Fin n), T.card ≤ K →
      value C (bits T) (out i) = decide (S i ⊆ T)) : c ≤ (specific C S i).card := by
  classical
  by_cases hc0 : c = 0
  · simp [hc0]
  by_contra! hsmall
  let G := specific C S i
  have hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw =>
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hB, transfer⟩ := cut C hG G hGates (n + C.size) {out i}
    (fun w _ hw => (hGates w hw).2)
  have hb : B.card ≤ c := by
    have hf := Finset.card_filter_le G (· < n + C.size)
    simp only [Finset.card_singleton] at hB
    change G.card < c at hsmall
    omega
  have baseBudget : (S i).card ≤ K := by
    have hl : 1 ≤ c := by omega
    have hqle : q ≤ c * q := by simpa using Nat.mul_le_mul_right q hl
    rw [sizes]
    omega
  have baseTrue : value C (bits (S i)) (out i) = true := by
    rw [correct (S i) baseBudget]
    simp
  let A := B.filter fun w => value C (bits (S i)) w = true
  have sources (w : ℕ) (hw : w ∈ A) : ∃ T : Finset (Fin n),
      (T.card ≤ 1 ∨ ∃ j ≠ i, T = S j) ∧ value C (bits T) w = true :=
    witnesses C S i w (fun h => Finset.disjoint_left.mp hd (Finset.mem_filter.mp hw).1 h)
      (Finset.mem_filter.mp hw).2
  let T (w : ℕ) : Finset (Fin n) := if h : w ∈ A then Classical.choose (sources w h) else ∅
  have source (w : ℕ) (hw : w ∈ A) :
      ((T w).card ≤ 1 ∨ ∃ j ≠ i, T w = S j) ∧ value C (bits (T w)) w = true := by
    simpa only [T, dite_eq_left hw] using Classical.choose_spec (sources w hw)
  let U := A.biUnion T
  have hA : A.card ≤ c := (Finset.card_filter_le _ _).trans hb
  have budget : U.card ≤ K := by
    have h := unionBound S sizes meets (by omega) A T (fun w hw =>
      (source w hw).1.imp id (fun ⟨j, _, he⟩ => ⟨j, he⟩))
    have hd' := Nat.mul_le_mul_right q hA
    change U.card ≤ _ at h
    omega
  have miss : ¬ S i ⊆ U := by
    intro sub
    have bound : (U ∩ S i).card ≤ A.card := by
      apply intersectionBound
      intro w hw
      rcases (source w hw).1 with small | ⟨j, hj, he⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans small
      · rw [he, meets j i hj]
    rw [Finset.inter_eq_right.mpr sub, sizes] at bound
    omega
  have htrue : value C (bits U) (out i) = true := by
    apply transfer (bits (S i)) (bits U) _ (out i) (Finset.mem_singleton_self _) baseTrue
    intro w hw ht
    have hwa : w ∈ A := Finset.mem_filter.mpr ⟨hw, ht⟩
    apply value_mono C hG (bits (T w)) (bits U) _ w (source w hwa).2
    intro j hj
    exact decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hwa, of_decide_eq_true hj⟩)
  rw [correct U budget] at htrue
  exact miss (of_decide_eq_true htrue)

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∀ v ∈ S w, x v = true)) →
    ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq sizes meets gates out hG correct c hc hK
  let C : Circuit := ⟨gates, 0⟩
  let G := specific C S
  have agree (i : Fin m) (T : Finset (Fin n)) (ht : T.card ≤ K) :
      value C (bits T) (out i) = decide (S i ⊆ T) := by
    have eq : Finset.univ.filter (fun j => bits T j = true) = T := by ext j; simp [bits]
    have h := correct i (bits T) (by rwa [eq])
    change value C (bits T) (out i) = _ at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simp only [bits, decide_eq_true_eq]
    exact ⟨fun h _ hv => h _ hv, fun h _ hv => h hv⟩
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rw [hj'.2 i hne] at hi'
    exact Bool.false_ne_true hi'.1
  calc
    m * c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      perOutput C S out hG i sizes meets hq hc hK (agree i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = gates.length := by simp [C, Circuit.size]
