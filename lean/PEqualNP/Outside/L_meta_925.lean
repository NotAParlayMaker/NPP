import Mathlib
import PEqualNP.Defs

-- Original proof by k-sandhu in PR 149.
-- Adapted here to the current proof-file namespace rules.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_925_aux

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
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with h | h
    · simp only [h, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro z hz
      obtain ⟨r, hm, rfl⟩ := hz
      exact hr r hm (hx _ ⟨r, hm, rfl⟩)
    · simp only [h, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨_, ⟨r, hm, rfl⟩, ht⟩ := hx
      exact ⟨_, ⟨r, hm, rfl⟩, hr r hm ht⟩

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


private def charSet {n : ℕ} (T : Finset (Fin n)) (v : Fin n) := decide (v ∈ T)

private def owned {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun r =>
    value C (charSet (S i)) r = true ∧
      ∀ j, j ≠ i → value C (charSet (S j)) r = false

private lemma boundary_witness {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (i : Fin m) (r : ℕ) (hr : r ∉ owned C S i)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) :
    ∃ T : Finset (Fin n), (T.card ≤ 1 ∨ ∃ j, T = S j) ∧
      (T ∩ S i).card ≤ 1 ∧
      (value C (charSet (S i)) r = true → value C (charSet T) r = true) := by
  classical
  by_cases ht : value C (charSet (S i)) r = true
  · by_cases hn : r < n
    · let v : Fin n := ⟨r, hn⟩
      refine ⟨{v}, Or.inl (by simp), (Finset.card_le_card Finset.inter_subset_left).trans
        (by simp), ?_⟩
      intro _
      change value C (charSet {v}) v = true
      simp [input_value, charSet]
    · have hw : r < n + C.size := by
        by_contra! h
        simp [missing_value C _ _ h] at ht
      obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ value C (charSet (S j)) r = true := by
        by_contra! h
        apply hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hw⟩, ht,
          fun j hj => by simpa using h j hj⟩
      exact ⟨S j, Or.inr ⟨j, rfl⟩, (hinter j i hji).le, fun _ => hj⟩
  · exact ⟨∅, Or.inl (by simp), by simp, fun h => False.elim (ht h)⟩

private lemma owned_lower {q n m K c : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (bounds : ∀ (B : Finset ℕ) (Q : ℕ → Finset (Fin n)),
      (∀ r ∈ B, (Q r).card ≤ 1 ∨ ∃ j, Q r = S j) → (B.biUnion Q).card ≤ B.card * q + 1)
    (i : Fin m) (o : ℕ)
    (correct : ∀ T : Finset (Fin n), T.card ≤ K →
      (value C (charSet T) o = true ↔ S i ⊆ T))
    (hc : c ≤ q) (hk : c * q < K) : c ≤ (owned C S i).card := by
  classical
  by_contra! small
  have positive : 1 ≤ c := by omega
  have hsi : (S i).card ≤ K := by
    have := Nat.mul_le_mul_right q positive
    rw [hs]
    simp only [Nat.one_mul] at this
    omega
  let G := owned C S i
  have gateRange (r : ℕ) (hr : r ∈ G) : n ≤ r ∧ r < n + C.size :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1
  obtain ⟨B, hdis, hcard, hcut⟩ := cut C hg G gateRange (n + C.size) {o}
    (fun r _ hr => (gateRange r hr).2)
  have hb : B.card ≤ c := by
    have := Finset.card_filter_le G (fun r => r < n + C.size)
    simp only [Finset.card_singleton] at hcard
    change G.card < c at small
    omega
  have piece (r : ℕ) : ∃ T : Finset (Fin n), (r ∈ B →
      (T.card ≤ 1 ∨ ∃ j, T = S j) ∧ (T ∩ S i).card ≤ 1 ∧
      (value C (charSet (S i)) r = true → value C (charSet T) r = true)) := by
    by_cases hr : r ∈ B
    · obtain ⟨T, hT⟩ := boundary_witness C S i r (Finset.disjoint_left.mp hdis hr) hinter
      exact ⟨T, fun _ => hT⟩
    · exact ⟨∅, fun h => False.elim (hr h)⟩
  choose Q hQ using piece
  let U := B.biUnion Q
  have light : U.card ≤ K := by
    have h := bounds B Q (fun r hr => (hQ r hr).1)
    have hle := Nat.mul_le_mul_right q hb
    change (B.biUnion Q).card ≤ K
    omega
  have outputU : value C (charSet U) o = true := by
    refine hcut (charSet (S i)) (charSet U) ?_ o (by simp) ((correct (S i) hsi).mpr (by rfl))
    intro r hr hx
    apply value_mono C hg (charSet (Q r)) (charSet U) _ r ((hQ r hr).2.2 hx)
    intro v hv
    simp only [charSet, decide_eq_true_eq] at hv ⊢
    exact Finset.mem_biUnion.mpr ⟨r, hr, hv⟩
  have inc : S i ⊆ B.biUnion (fun r => Q r ∩ S i) := by
    intro v hv
    obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp ((correct U light).mp outputU hv)
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_inter.mpr ⟨hvr, hv⟩⟩
  have count := Finset.card_biUnion_le_card_mul B (fun r => Q r ∩ S i) 1
    (fun r hr => (hQ r hr).2.1)
  have hsle := Finset.card_le_card inc
  rw [hs] at hsle
  simp only [Nat.mul_one] at count
  omega

private lemma union_card {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1) (hq : 2 ≤ q)
    (B : Finset ℕ) (Q : ℕ → Finset (Fin n))
    (hQ : ∀ r ∈ B, (Q r).card ≤ 1 ∨ ∃ j, Q r = S j) :
    (B.biUnion Q).card ≤ B.card * q + 1 := by
  classical
  by_cases hb : ∃ r ∈ B, ∃ j, Q r = S j
  · obtain ⟨r, hr, j, hbase⟩ := hb
    let T := B.erase r
    let R := fun k => Q k \ S j
    have bound : ∀ k ∈ T, (R k).card ≤ q := by
      intro k hk
      rcases hQ k (Finset.mem_erase.mp hk).2 with small | ⟨i, hi⟩
      · have le : (R k).card ≤ (Q k).card := Finset.card_le_card Finset.sdiff_subset
        omega
      · change (Q k \ S j).card ≤ q
        rw [hi]
        by_cases h : i = j
        · simp [h]
        · have eq := Finset.card_sdiff_add_card_inter (S i) (S j)
          rw [hinter i j h, hs i] at eq
          omega
    have cover : B.biUnion Q ⊆ S j ∪ T.biUnion R := by
      intro x hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
      by_cases h : x ∈ S j
      · exact Finset.mem_union_left _ h
      · have hne : k ≠ r := by rintro rfl; exact h (hbase ▸ hxk)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_erase.mpr ⟨hne, hk⟩, Finset.mem_sdiff.mpr ⟨hxk, h⟩⟩)
    have sz : T.card + 1 = B.card := Finset.card_erase_add_one hr
    calc
      (B.biUnion Q).card ≤ (S j ∪ T.biUnion R).card := Finset.card_le_card cover
      _ ≤ (S j).card + (T.biUnion R).card := Finset.card_union_le _ _
      _ ≤ (q + 1) + T.card * q := by
        rw [hs]
        exact Nat.add_le_add_left (Finset.card_biUnion_le_card_mul T R q bound) _
      _ = B.card * q + 1 := by rw [← sz, Nat.add_mul]; omega
  · have small : ∀ k ∈ B, (Q k).card ≤ q := by
      intro k hk
      rcases hQ k hk with h | ⟨j, h⟩
      · omega
      · exact False.elim (hb ⟨k, hk, j, h⟩)
    exact (Finset.card_biUnion_le_card_mul B Q q small).trans (Nat.le_succ _)

end PEqualNP.Outside.L_meta_925_aux
open PEqualNP.Outside.L_meta_925_aux
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hs hinter gs out hg hcorrect c hc hk
  let C : Circuit := ⟨gs, 0⟩
  let G (i : Fin m) := owned C S i
  have bound (i : Fin m) : c ≤ (G i).card := by
    apply owned_lower S C hg hs hinter (union_card S hs hinter hq) i (out i) _ hc hk
    intro T hT
    have h := hcorrect i (charSet T) (by simpa [charSet] using hT)
    change value C (charSet T) (out i) = _ at h
    simp only [h, decide_eq_true_eq, charSet]
    rfl 
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun r hi hj => ?_
    have x := (Finset.mem_filter.mp hi).2
    have y := (Finset.mem_filter.mp hj).2
    have bad := x.2 j hij.symm
    simp [y.1] at bad
  calc
    m * c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => bound i
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun r hr => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hr
      exact (Finset.mem_filter.mp hi).1
    _ = gs.length := by simp [C, Circuit.size]
