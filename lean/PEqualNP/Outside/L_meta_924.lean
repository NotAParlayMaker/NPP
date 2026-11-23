import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- The bound for ANDs of the sets on light inputs (andBound below) is the proof of L_meta_925,
-- original proof by k-sandhu in PR 149, copied here as a helper. The OR form on heavy inputs
-- follows by the mirror argument after it: flip every input and swap AND with OR.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_924

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
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

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

-- Expand the selected gates once each, from the last wire back to the first.
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


private def onSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ T)

private lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => onSet T p = true)).card = T.card := by
  congr 1
  ext p
  simp [onSet]

private lemma union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (B : Finset ℕ) (A : ℕ → Finset (Fin n))
    (hA : ∀ w ∈ B, (A w).card ≤ q ∨ ∃ i, A w = S i) :
    (B.biUnion A).card ≤ B.card * q + 1 := by
  classical
  by_cases hbig : ∃ w ∈ B, ∃ i, A w = S i
  · obtain ⟨w,hw,i,hi⟩ := hbig
    let R := B.erase w
    have hdiff : ∀ v ∈ R, (A v \ S i).card ≤ q := by
      intro v hv
      rcases hA v (Finset.mem_erase.mp hv).2 with hs | ⟨j,hj⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans hs
      · rw [hj]
        by_cases h : j = i
        · simp [h]
        · have he := Finset.card_sdiff_add_card_inter (S j) (S i)
          rw [hinter j i h, hsize] at he
          omega
    have hsub : B.biUnion A ⊆ S i ∪ R.biUnion (fun v => A v \ S i) := by
      intro p hp
      obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases h : p ∈ S i
      · exact Finset.mem_union_left _ h
      · have hne : v ≠ w := by rintro rfl; exact h (hi ▸ hp)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v,Finset.mem_erase.mpr ⟨hne,hv⟩,Finset.mem_sdiff.mpr ⟨hp,h⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S i) (R.biUnion (fun v => A v \ S i))
    have h3 := Finset.card_biUnion_le_card_mul R (fun v => A v \ S i) q hdiff
    have he : R.card + 1 = B.card := Finset.card_erase_add_one hw
    rw [← he, Nat.add_mul, Nat.one_mul]
    rw [hsize] at h2
    omega
  · have hsmall (v) (hv : v ∈ B) : (A v).card ≤ q :=
      (hA v hv).resolve_right (fun h => hbig ⟨v,hv,h⟩)
    exact (Finset.card_biUnion_le_card_mul B A q hsmall).trans (by omega)

private def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Finset ℕ := (Finset.Ico n (n+C.size)).filter fun w =>
      value C (onSet (S i)) w = true ∧ ∀ j, j ≠ i → value C (onSet (S j)) w = false

private lemma private_count {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (i : Fin m) (o c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ T : Finset (Fin n), T.card ≤ K →
      (value C (onSet T) o = true ↔ S i ⊆ T))
    (hc : c ≤ q) (hK : c*q < K) : c ≤ (specific C S i).card := by
  classical
  by_contra! hsmall
  let G := specific C S i
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBC, hcut⟩ := cut C hg G hgate (n+C.size) {o} (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hf := Finset.card_filter_le G (fun w => w < n+C.size)
    simp only [Finset.card_singleton] at hBC
    change G.card < c at hsmall
    omega
  have hpositive : 1 ≤ c := by omega
  have hsK : (S i).card ≤ K := by
    have hp := Nat.mul_le_mul_right q hpositive
    rw [Nat.one_mul] at hp
    rw [hsize]
    omega
  have witness (w : ℕ) (hw : w ∈ B) : ∃ T : Finset (Fin n),
      (T.card ≤ q ∨ ∃ j, T = S j) ∧ (T ∩ S i).card ≤ 1 ∧
      (value C (onSet (S i)) w = true → value C (onSet T) w = true) := by
    by_cases hv : value C (onSet (S i)) w = true
    · by_cases hin : w < n
      · let p : Fin n := ⟨w,hin⟩
        refine ⟨{p},Or.inl (by simp; omega),?_,?_⟩
        · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ S i ⊆ {p})).trans (by simp)
        · intro _
          change value C (onSet {p}) p = true
          simp [input_value,onSet]
      · have bound : w < n+C.size := by
          by_contra! he
          simp [missing_value C _ w he] at hv
        have hn : w ∉ specific C S i := Finset.disjoint_left.mp hd hw
        have hex : ∃ j, j ≠ i ∧ value C (onSet (S j)) w = true := by
          by_contra! neg
          apply hn
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,bound⟩,hv,?_⟩
          intro j hj
          simpa using neg j hj
        obtain ⟨j,hji,hj⟩ := hex
        exact ⟨S j,Or.inr ⟨j,rfl⟩,(hinter j i hji).le,fun _ => hj⟩
    · exact ⟨∅,Or.inl (by simp),by simp,fun ht => False.elim (hv ht)⟩
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      ((A w).card ≤ q ∨ ∃ j, A w = S j) ∧ (A w ∩ S i).card ≤ 1 ∧
      (value C (onSet (S i)) w = true → value C (onSet (A w)) w = true) := by
    simpa [A,hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hu : U.card ≤ K := by
    have h := union_bound S hsize hinter B A (fun w hw => (ha w hw).1)
    have h' := Nat.mul_le_mul_right q hb
    change (B.biUnion A).card ≤ K
    omega
  have hot : value C (onSet U) o = true := by
    apply hcut (onSet (S i)) (onSet U) _ o (Finset.mem_singleton_self o)
      ((heval (S i) hsK).mpr (by rfl))
    intro w hw hp
    apply value_mono C hg (onSet (A w)) (onSet U) _ w ((ha w hw).2.2 hp)
    intro p hp
    exact decide_eq_true (Finset.mem_biUnion.mpr ⟨w,hw,of_decide_eq_true hp⟩)
  have hSub := (heval U hu).mp hot
  have hcover : S i ⊆ B.biUnion (fun w => A w ∩ S i) := by
    intro p hp
    obtain ⟨w,hw,hm⟩ := Finset.mem_biUnion.mp (hSub hp)
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hm,hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => A w ∩ S i) 1 (fun w hw => (ha w hw).2.1)
  rw [hsize] at h1
  simp only [Nat.mul_one] at h2
  omega

theorem andBound : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hinter gates out hg heval c hc hK
  let C : Circuit := ⟨gates,0⟩
  let G (i : Fin m) := specific C S i
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hi hj => ?_
    have hfalse := (Finset.mem_filter.mp hi).2.2 j (Ne.symm hij)
    have htrue := (Finset.mem_filter.mp hj).2.1
    simp [htrue] at hfalse
  have hi (i : Fin m) : c ≤ (G i).card := by
    apply private_count S hq hsize hinter C i (out i) c hg _ hc hK
    intro T hT
    have h := heval i (onSet T) ((weight T).symm ▸ hT)
    change value C (onSet T) (out i) = _ at h
    rw [h]
    simp [onSet,Finset.subset_iff]
  have hs : Finset.univ.biUnion G ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).1
  calc
    m*c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card hs
    _ = gates.length := by simp [C,Circuit.size]

-- The mirror circuit: swap AND with OR. A gate at wire b may read a wire that does not exist
-- yet, and that read is false in both circuits, so the mirror drops such reads: an AND gate with
-- one becomes the constant true (an AND gate reading no wire), an OR gate keeps only its other
-- reads. The mirror has exactly as many gates as the original.
private def dualGate (b : ℕ) (g : Gate) : Gate :=
  match g with
  | ⟨GateOp.and, l⟩ =>
    if l.all (fun r => decide (r < b)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | ⟨_, l⟩ => ⟨GateOp.and, l.filter (fun r => decide (r < b))⟩

private def dualList (n : ℕ) (gates : List Gate) : List Gate :=
  gates.mapIdx (fun j g => dualGate (n + j) g)

private lemma dual_shape (b : ℕ) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((dualGate b g).op = GateOp.and ∨ (dualGate b g).op = GateOp.or) ∧
      (dualGate b g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := h
  dsimp only at hop hlen
  rcases hop with rfl | rfl
  · by_cases hall : (l.all fun r => decide (r < b)) = true
    · have hd : dualGate b ⟨GateOp.and, l⟩ = ⟨GateOp.or, l⟩ := ite_eq_left hall
      rw [hd]
      exact ⟨Or.inr rfl, hlen⟩
    · have hd : dualGate b ⟨GateOp.and, l⟩ = ⟨GateOp.and, []⟩ := ite_eq_right hall
      rw [hd]
      exact ⟨Or.inl rfl, by simp⟩
  · exact ⟨Or.inl rfl, (List.length_filter_le _ _).trans hlen⟩

private lemma dual_gates (n : ℕ) (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ dualList n gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi' : i < gates.length := by simpa [dualList] using hi
  simp only [dualList, List.getElem_mapIdx]
  exact dual_shape _ _ (hG _ (List.getElem_mem hi'))

private lemma dm_any (w : ℕ) (f : ℕ → Bool) (l : List ℕ) (h : ∀ r ∈ l, r < w) :
    (l.map fun r => if r < w then !(f r) else false).any id =
      !((l.map fun r => if r < w then f r else false).all id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a < w := h a List.mem_cons_self
    have ih' := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    rw [List.map_cons, List.map_cons, List.any_cons, List.all_cons, ih', ite_eq_left ha, ite_eq_left ha]
    simp only [id_eq, Bool.not_and]

private lemma all_bad (w : ℕ) (f : ℕ → Bool) (l : List ℕ) (h : ¬ ∀ r ∈ l, r < w) :
    (l.map fun r => if r < w then f r else false).all id = false := by
  rw [Bool.eq_false_iff]
  intro hall
  apply h
  intro r hr
  rw [List.all_eq_true] at hall
  have hv := hall _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  by_contra hlt
  simp [hlt] at hv

private lemma dm_all (w : ℕ) (f : ℕ → Bool) (l : List ℕ) :
    ((l.filter fun r => decide (r < w)).map fun r => if r < w then !(f r) else false).all id =
      !((l.map fun r => if r < w then f r else false).any id) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a < w
    · rw [List.filter_cons_of_pos (by simpa using ha), List.map_cons, List.map_cons,
        List.all_cons, List.any_cons, ih, ite_eq_left ha, ite_eq_left ha]
      simp only [id_eq, Bool.not_or]
    · rw [List.filter_cons_of_neg (by simpa using ha), List.map_cons, List.any_cons, ih,
        ite_eq_right ha]
      simp only [id_eq, Bool.false_or]

-- One gate: given that the mirror reads agree with the negated original reads below wire w,
-- the mirror gate at wire w is the negation of the original gate.
private lemma dual_eval (w : ℕ) (f f' : ℕ → Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hf : ∀ r, r < w → f' r = !(f r)) :
    (dualGate w g).op.eval ((dualGate w g).inputs.map fun r => if r < w then f' r else false) =
      !(g.op.eval (g.inputs.map fun r => if r < w then f r else false)) := by
  have hfun : (fun r => if r < w then f' r else false) =
      (fun r => if r < w then !(f r) else false) := by
    funext r
    by_cases h : r < w
    · rw [ite_eq_left h, ite_eq_left h, hf r h]
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hfun]
  obtain ⟨op, l⟩ := g
  dsimp only at hop
  rcases hop with rfl | rfl
  · by_cases hall : (l.all fun r => decide (r < w)) = true
    · have hd : dualGate w ⟨GateOp.and, l⟩ = ⟨GateOp.or, l⟩ := ite_eq_left hall
      rw [hd]
      simp only [GateOp.eval]
      exact dm_any w f l (by simpa using hall)
    · have hd : dualGate w ⟨GateOp.and, l⟩ = ⟨GateOp.and, []⟩ := ite_eq_right hall
      rw [hd]
      simp only [GateOp.eval]
      rw [all_bad w f l (by simpa using hall)]
      rfl
  · show GateOp.eval GateOp.and ((l.filter fun r => decide (r < w)).map
        fun r => if r < w then !(f r) else false) =
      !(GateOp.eval GateOp.or (l.map fun r => if r < w then f r else false))
    simp only [GateOp.eval]
    exact dm_all w f l

-- Every existing wire of the mirror on the flipped input is the negation of the original wire.
private lemma dual_value {n : ℕ} (gates : List Gate)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, y p = !(x p)) :
    ∀ w, w < n + gates.length →
      value (⟨dualList n gates, 0⟩ : Circuit) y w = !(value (⟨gates, 0⟩ : Circuit) x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · have h1 : value (⟨dualList n gates, 0⟩ : Circuit) y w = y ⟨w, hn⟩ :=
        input_value _ y ⟨w, hn⟩
      have h2 : value (⟨gates, 0⟩ : Circuit) x w = x ⟨w, hn⟩ := input_value _ x ⟨w, hn⟩
      rw [h1, h2, hxy]
    · have hnw : n ≤ w := by omega
      have hj : w - n < gates.length := by omega
      have hlenD : (dualList n gates).length = gates.length := by simp [dualList]
      have hC := gate_value (⟨gates, 0⟩ : Circuit) x w hnw (by simpa [Circuit.size] using hw)
      have hD := gate_value (⟨dualList n gates, 0⟩ : Circuit) y w hnw
        (by simpa [Circuit.size, hlenD] using hw)
      have hget : (dualList n gates)[w - n]'(by omega) = dualGate w (gates[w - n]'hj) := by
        simp only [dualList, List.getElem_mapIdx]
        congr 1
        omega
      dsimp only at hC hD
      rw [hget] at hD
      rw [hD, hC]
      exact dual_eval w _ _ _ (hG _ (List.getElem_mem hj)).1 (fun r hr => ih r hr (by omega))

end PEqualNP.Outside.L_meta_924

open PEqualNP.Outside.L_meta_924 in
theorem PEqualNP.Outside.L_meta_924 : ∀ (q n m K T : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → K + T = n → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), T ≤ (Finset.univ.filter (fun i : Fin n => x i = true)).card → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K T S hq hKT hsize hinter gates out hg heval c hc hK
  have key : ∀ (w : Fin m) (y : Fin n → Bool),
      (Finset.univ.filter (fun i : Fin n => y i = true)).card ≤ K →
      Circuit.eval ⟨dualList n gates, out w⟩ (List.ofFn y) = decide (∀ v ∈ S w, y v = true) := by
    intro w y hy
    let x : Fin n → Bool := fun p => !(y p)
    have hxy : ∀ p, y p = !(x p) := fun p => by simp [x]
    have hcard : T ≤ (Finset.univ.filter (fun i : Fin n => x i = true)).card := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (fun i => y i = true)
      have h2 : Finset.univ.filter (fun i : Fin n => x i = true) =
          Finset.univ.filter (fun i : Fin n => ¬ y i = true) := by
        ext i
        simp [x]
      rw [h2]
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hx := heval w x hcard
    by_cases hout : out w < n + gates.length
    · have hv := dual_value gates hg x y hxy (out w) hout
      change value (⟨dualList n gates, 0⟩ : Circuit) y (out w) = _
      change value (⟨gates, 0⟩ : Circuit) x (out w) = _ at hx
      rw [hv, hx, Bool.eq_iff_iff]
      simp [x]
    · exfalso
      have hall := heval w (fun _ => true) (by simp; omega)
      change value (⟨gates, 0⟩ : Circuit) (fun _ => true) (out w) = _ at hall
      rw [missing_value (⟨gates, 0⟩ : Circuit) (fun _ => true) (out w)
        (by simp only [Circuit.size]; omega)] at hall
      have hne : (S w).Nonempty := by
        rw [← Finset.card_pos, hsize]
        omega
      obtain ⟨v, hv⟩ := hne
      exact Bool.false_ne_true (hall.trans (decide_eq_true ⟨v, hv, rfl⟩))
  have h := andBound q n m K S hq hsize hinter (dualList n gates) out
    (dual_gates n gates hg) key c hc hK
  simpa [dualList] using h
