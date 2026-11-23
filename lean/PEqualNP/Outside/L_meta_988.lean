import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- The circuit evaluation and cut argument are adapted from L-meta-270,
-- originally proved by k-sandhu in PR 149.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_988

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
  refine ⟨P, (Finset.card_filter_le _ _).trans (List.toFinset_card_le _ |>.trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hin : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hin, h⟩)
      · simp [h]
    have gx := gate_value C x w hn hw
    have gy := gate_value C y w hn hw
    change value C x w = g.op.eval _ at gx
    change value C y w = g.op.eval _ at gy
    rw [gx] at hx
    rw [gy]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hx ⊢
      exact fun z hz => hr z hz (hx z hz)
    · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hx ⊢
      obtain ⟨z, hz, hzx⟩ := hx
      exact ⟨z, hz, hr z hz hzx⟩

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

private def shift {n : ℕ} (D : Finset (Fin n)) (x : Fin n → Bool) (p : Fin n) : Bool :=
  decide (p ∈ D) || x p

private def singletonInput {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

private def outside {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

private def shiftedSupport {n : ℕ} (C : Circuit) (D : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (shift D (singletonInput p)) w = true)

private lemma mem_shiftedSupport {n : ℕ} (C : Circuit) (D : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ shiftedSupport C D w ↔ value C (shift D (singletonInput p)) w = true := by simp [shiftedSupport]

private lemma isGate {n : ℕ} (C : Circuit) (D : Finset (Fin n)) (w : ℕ)
    (T : Finset (Fin n)) (hzero : value C (shift D (outside T)) w = false)
    (h : 2 ≤ (shiftedSupport C D w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : shiftedSupport C D w ⊆ {p} := by
      intro q hq
      have hv := (mem_shiftedSupport C D w q).mp hq
      change value C (shift D (singletonInput q)) p = true at hv
      rw [input_value] at hv
      by_cases hp : p ∈ D
      · change value C (shift D (outside T)) p = false at hzero
        simp [input_value, shift, hp] at hzero
      · simpa [shift, hp, singletonInput, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : shiftedSupport C D w = ∅ := by
      ext q
      simp [mem_shiftedSupport, missing_value C _ w hw]
    simp [hs] at h

private abbrev monotoneGates (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

-- A gate assigned to a target is false when every outside point is active,
-- and fires for at least two single-point extensions of the base.
private def assigned {n : ℕ} (C : Circuit) (D T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    value C (shift D (outside T)) w = false ∧ 2 ≤ (shiftedSupport C D w).card

private lemma support_subset {n : ℕ} (C : Circuit) (hG : monotoneGates C)
    (D T : Finset (Fin n)) (w : ℕ) (h : value C (shift D (outside T)) w = false) :
    shiftedSupport C D w ⊆ T := by
  intro p hp
  by_contra hn
  have hxy (q : Fin n) : shift D (singletonInput p) q = true → shift D (outside T) q = true := by
    by_cases hq : q ∈ D
    · simp [shift, hq]
    · simp only [shift, hq, decide_false, Bool.false_or, singletonInput, outside, decide_eq_true_eq]
      rintro rfl
      exact hn
  have hc := value_mono C hG _ _ hxy w ((mem_shiftedSupport _ _ _ _).mp hp)
  simp [h] at hc

-- Each boundary wire left by the cut accounts for at most one target point.
private lemma card_assigned {n : ℕ} (C : Circuit) (hG : monotoneGates C) (D T : Finset (Fin n)) (o : ℕ)
    (hneg : value C (shift D (outside T)) o = false) (hpos : T ⊆ shiftedSupport C D o) :
    T.card - 1 ≤ (assigned C D T).card := by
  classical
  let G := assigned C D T
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw =>
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  let parts (w : ℕ) := if value C (shift D (outside T)) w = false then shiftedSupport C D w else ∅
  have small (w : ℕ) (hw : w ∈ B) : (parts w).card ≤ 1 := by
    by_cases hn : value C (shift D (outside T)) w = false
    · simp only [parts, ite_eq_left hn]
      by_contra! big
      have hg : w ∈ G := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr (isGate C D w T hn (by omega)), hn, by omega⟩
      exact Finset.disjoint_left.mp hd hw hg
    · simp [parts, hn]
  have cover : T ⊆ B.biUnion parts := by
    intro p hp
    by_contra hn
    have chain (w : ℕ) (hw : w ∈ B) (ha : value C (shift D (singletonInput p)) w = true) :
        value C (shift D (outside T)) w = true := by
      cases hv : value C (shift D (outside T)) w with
      | true => rfl
      | false =>
        exfalso
        apply hn
        exact Finset.mem_biUnion.mpr ⟨w, hw, by simpa [parts, hv, mem_shiftedSupport] using ha⟩
    have h := hcut (shift D (singletonInput p)) (shift D (outside T)) chain o
      (Finset.mem_singleton_self o) ((mem_shiftedSupport _ _ _ _).mp (hpos hp))
    simp [hneg] at h
  have hcover := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B parts 1 small)
  have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
  simp only [mul_one] at hcover
  simp only [Finset.card_singleton] at hBcard
  change T.card - 1 ≤ G.card
  omega

end PEqualNP.Outside.L_meta_988

open PEqualNP.Outside.L_meta_988

theorem PEqualNP.Outside.L_meta_988 :
    ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i : Fin m, Disjoint (y i) (S i)) →
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) →
    (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) →
    (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) →
    ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m K S Y C o pair sep hm safe fire clique
  let G (i : Fin m) := assigned C (Y i) (S i)
  let allGates := Finset.Ico n (n + C.size)
  have inc (i : Fin m) : G i ⊆ allGates := fun _ h => (Finset.mem_filter.mp h).1
  have need (i : Fin m) : (S i).card - 1 ≤ (G i).card := by
    apply card_assigned C hm (Y i) (S i) (o i)
    · cases hv : value C (shift (Y i) (outside (S i))) (o i) with
      | false => rfl
      | true =>
        obtain ⟨p, hp, h⟩ := safe i _ hv
        simp only [shift, outside, decide_eq_true_eq, Bool.or_eq_true] at h
        exact False.elim (h.elim (fun hy => Finset.disjoint_left.mp (sep i) hy hp) (fun hn => hn hp))
    · intro p hp
      apply (mem_shiftedSupport _ _ _ _).mpr
      have eq : shift (Y i) (singletonInput p) = (fun q => decide (q ∈ Y i ∨ q = p)) := by
        funext q
        simp [shift, singletonInput]
      rw [eq]
      exact fire i p hp
  let labels (w : ℕ) := Finset.univ.filter (fun i => w ∈ G i)
  -- Two labels of the same gate must meet each other's bases.
  have covers (w : ℕ) : (labels w).card ≤ K := by
    apply clique
    intro i hi j hj neq dis
    have hi' := (Finset.mem_filter.mp ((Finset.mem_filter.mp hi).2)).2
    have hj' := (Finset.mem_filter.mp ((Finset.mem_filter.mp hj).2)).2
    have clean := support_subset C hm (Y i) (S i) w hi'.1
    have who : ∃ p ∈ shiftedSupport C (Y i) w, p ∉ S j := by
      by_contra! h
      have sub : shiftedSupport C (Y i) w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨clean hp, h p hp⟩
      have bound := (Finset.card_le_card sub).trans (pair i j neq)
      omega
    obtain ⟨p, hp, hnj⟩ := who
    have le (q : Fin n) : shift (Y i) (singletonInput p) q = true → shift (Y j) (outside (S j)) q = true := by
      simp only [shift, singletonInput, outside, Bool.or_eq_true, decide_eq_true_eq]
      rintro (hi | rfl)
      · exact Or.inr (Finset.disjoint_left.mp dis hi)
      · exact Or.inr hnj
    have yes := value_mono C hm _ _ le w ((mem_shiftedSupport _ _ _ _).mp hp)
    exact Bool.noConfusion (hj'.1.symm.trans yes)
  -- Count incidences first by targets, then by gates.
  have row (i : Fin m) :
      (G i).card = ∑ w ∈ allGates, (if w ∈ G i then 1 else 0 : ℕ) := by
    simp only [Finset.sum_boole]
    congr 1
    ext w
    simp only [Finset.mem_filter]
    exact ⟨fun hw => ⟨inc i hw, hw⟩, And.right⟩
  have total : ∑ i, ((S i).card - 1) ≤ K * C.size := calc
    _ ≤ ∑ i, (G i).card := Finset.sum_le_sum fun i _ => need i
    _ = ∑ i, ∑ w ∈ allGates, (if w ∈ G i then 1 else 0 : ℕ) := Finset.sum_congr rfl fun i _ => row i
    _ = ∑ w ∈ allGates, (labels w).card := by rw [Finset.sum_comm]; simp [labels]
    _ ≤ ∑ _w ∈ allGates, K := Finset.sum_le_sum fun w _ => covers w
    _ = _ := by simp [allGates, Nat.mul_comm]
  have each : ∑ i, (S i).card ≤ ∑ i, ((S i).card - 1 + 1) := Finset.sum_le_sum fun i _ => by omega
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at each
  change ∑ i, ((S i).card - 1) ≤ K * C.gates.length at total
  omega
