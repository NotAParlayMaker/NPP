import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

-- The wire semantics and cut induction are adapted from the L-meta-270 proof by k-sandhu.
-- Filtering the actual list of earlier operands also handles nullary and unary gates.

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P,(Finset.card_filter_le _ _).trans (g.inputs.toFinset_card_le.trans hlen),
    fun r hr => (Finset.mem_filter.mp hr).2,?_⟩
  intro x y hxy hx
  let opnd (z : Fin n → Bool) (r : ℕ) := if r < w then value C z r else false
  have formula (z : Fin n → Bool) : value C z w = g.op.eval (g.inputs.map (opnd z)) :=
    gate_value C z w hn hw
  have rise (r : ℕ) (hr : r ∈ g.inputs) : opnd x r=true → opnd y r=true := by
    by_cases h : r < w
    · simpa [opnd,h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
    · simp [opnd,h]
  rw [formula x] at hx
  rw [formula y]
  rcases hop with h|h
  · have hxa : ∀ r ∈ g.inputs, opnd x r = true := by simpa [h,GateOp.eval] using hx
    simpa [h,GateOp.eval] using (show ∀ r ∈ g.inputs, opnd y r = true from
      fun r hr => rise r hr (hxa r hr))
  · obtain ⟨r,hr,hx'⟩ : ∃ r ∈ g.inputs, opnd x r = true := by simpa [h,GateOp.eval] using hx
    simpa [h,GateOp.eval] using (show ∃ r ∈ g.inputs, opnd y r = true from ⟨r,hr,rise r hr hx'⟩)

lemma value_mono {n : ℕ} (C : Circuit)
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
lemma cut {n : ℕ} (C : Circuit)
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

lemma cut_one {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n+C.size) (o : ℕ) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ G.card+1 ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w=true → value C y w=true) →
        value C x o=true → value C y o=true := by
  obtain ⟨B,dis,sz,h⟩ := cut C hG G hGates (n+C.size) {o} (fun w _ hw => (hGates w hw).2)
  refine ⟨B, dis, ?_, fun x y hxy => h x y hxy o (Finset.mem_singleton_self o)⟩
  have le := Finset.card_filter_le (s:=G) (· < n+C.size)
  simp only [Finset.card_singleton] at sz
  omega

def mask {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ A)

noncomputable def privateWires {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun j => value C (mask (S w)) j = true ∧
    ∀ i, i ≠ w → value C (mask (S i)) j ≠ true)

lemma fragment {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) (b : ℕ) (hb : b ∉ privateWires C S w) :
    ∃ A : Finset (Fin n), (A.card ≤ 1 ∨ ∃ i, i ≠ w ∧ A = S i) ∧
      (value C (mask (S w)) b = true → value C (mask A) b = true) := by
  classical
  by_cases ht : value C (mask (S w)) b = true
  · by_cases hraw : b < n
    · let p : Fin n := ⟨b, hraw⟩
      refine ⟨{p}, Or.inl (by simp), fun _ => ?_⟩
      change value C (mask {p}) p = true
      simp [input_value, mask]
    · have hvalid : b < n + C.size := by
        by_contra! hbad
        rw [missing_value C _ _ hbad] at ht
        contradiction
      have hforeign : ∃ i, i ≠ w ∧ value C (mask (S i)) b = true := by
        by_contra! hnone
        apply hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hvalid⟩, ht, hnone⟩
      obtain ⟨i, hi, hbtrue⟩ := hforeign
      exact ⟨S i, Or.inr ⟨i, hi, rfl⟩, fun _ => hbtrue⟩
  · exact ⟨∅, Or.inl (by simp), fun h => (ht h).elim⟩

end PEqualNP.Outside.L_meta_925_aux

namespace PEqualNP.Outside.L_meta_925_aux

-- A union of frontier sets covers at most as many target points as there are frontier
-- wires. For its total size, charge one full set first. Each other full set meets that set,
-- so contributes at most `q` additional points.
theorem frontier_union_bounds {q n m : ℕ} (S : Fin m → Finset (Fin n)) (w : Fin m)
    (B : Finset ℕ) (F : ℕ → Finset (Fin n)) (hq : 2 ≤ q)
    (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hF : ∀ b ∈ B, (F b).card ≤ 1 ∨ ∃ i, i ≠ w ∧ F b = S i) :
    (B.biUnion F).card ≤ q * B.card + 1 ∧ ((B.biUnion F) ∩ S w).card ≤ B.card := by
  classical
  have capped (T : Finset ℕ) (G : ℕ → Finset (Fin n)) (d : ℕ)
      (h : ∀ a ∈ T, (G a).card ≤ d) : (T.biUnion G).card ≤ d * T.card := by
    calc
      _ ≤ ∑ a ∈ T, (G a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ T, d := Finset.sum_le_sum h
      _ = _ := by simp [Nat.mul_comm]
  constructor
  · by_cases hex : ∃ b ∈ B, ∃ i, i ≠ w ∧ F b = S i
    · obtain ⟨b,hb,i,_,hi⟩ := hex
      let T := B.erase b
      have hdiff : ∀ a ∈ T, (F a \ F b).card ≤ q := by
        intro a ha
        rcases hF a (Finset.mem_of_mem_erase ha) with h | ⟨j,_,hj⟩
        · exact (Finset.card_le_card Finset.sdiff_subset).trans (by omega)
        · rw [hj,hi]
          by_cases hji : j = i
          · simp [hji]
          · have hsum := Finset.card_sdiff_add_card_inter (S j) (S i)
            rw [hsize,hinter j i hji] at hsum
            omega
      have hcover : B.biUnion F ⊆ F b ∪ T.biUnion (fun a => F a \ F b) := by
        intro p hp
        obtain ⟨a,ha,hpa⟩ := Finset.mem_biUnion.mp hp
        by_cases hpb : p ∈ F b
        · exact Finset.mem_union_left _ hpb
        · have hab : a ≠ b := by rintro rfl; exact hpb hpa
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨a,Finset.mem_erase.mpr ⟨hab,ha⟩,Finset.mem_sdiff.mpr ⟨hpa,hpb⟩⟩)
      have hc : B.card = T.card + 1 := by
        dsimp only [T]
        rw [Finset.card_erase_of_mem hb]
        have hp := Finset.card_pos.mpr ⟨b,hb⟩
        omega
      calc
        _ ≤ (F b ∪ T.biUnion (fun a => F a \ F b)).card := Finset.card_le_card hcover
        _ ≤ (F b).card + (T.biUnion (fun a => F a \ F b)).card := Finset.card_union_le _ _
        _ ≤ (q+1) + q*T.card := Nat.add_le_add (by rw [hi,hsize]) (capped _ _ _ hdiff)
        _ = _ := by rw [hc,Nat.mul_add]; omega
    · have small : ∀ b ∈ B, (F b).card ≤ 1 := by
        intro b hb
        exact (hF b hb).resolve_right (fun h => hex ⟨b,hb,h⟩)
      have hcard := capped B F q (fun b hb => (small b hb).trans (by omega))
      omega
  · rw [Finset.biUnion_inter]
    have hcap (b : ℕ) (hb : b ∈ B) : (F b ∩ S w).card ≤ 1 := by
      rcases hF b hb with h | ⟨i,hi,he⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans h
      · rw [he,hinter i w hi]
    simpa using capped _ _ 1 hcap

end PEqualNP.Outside.L_meta_925_aux

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

lemma mask_weight {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter fun p => mask A p = true) = A := by
  ext p
  simp [mask]

lemma per_output {q n m K c : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (out : Fin m → ℕ) (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ w (x : Fin n → Bool), (Finset.univ.filter fun p => x p = true).card ≤ K →
      value C x (out w) = decide (∀ p ∈ S w, x p = true))
    (hc : c ≤ q) (hK : c*q < K) (w : Fin m) : c ≤ (privateWires C S w).card := by
  classical
  by_contra! few
  have hqK : q+1 ≤ K := by
    have h := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [Nat.one_mul] at h
    omega
  let G := privateWires C S w
  have hGates : ∀ j ∈ G, n ≤ j ∧ j < n+C.size := by
    intro j hj
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
  obtain ⟨B, hd, hB, hcut⟩ := cut_one C hG G hGates (out w)
  have hb : B.card ≤ c := by change B.card ≤ (privateWires C S w).card+1 at hB; omega
  have fr (b : ℕ) : ∃ A : Finset (Fin n),
      (A.card ≤ 1 ∨ ∃ i, i ≠ w ∧ A = S i) ∧
      (b ∈ B → value C (mask (S w)) b = true → value C (mask A) b = true) := by
    by_cases h : b ∈ B
    · obtain ⟨A,ha,hs⟩ := fragment C S w b (Finset.disjoint_left.mp hd h)
      exact ⟨A,ha,fun _ => hs⟩
    · exact ⟨∅, Or.inl (by simp), fun hm => (h hm).elim⟩
  choose F hF hkeep using fr
  let U := B.biUnion F
  obtain ⟨hu, hmeet⟩ := frontier_union_bounds S w B F hq hsize hinter (fun b _ => hF b)
  have hprod : q*B.card ≤ c*q := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hb
  have hweight : U.card ≤ K := by change (B.biUnion F).card ≤ K; omega
  have hroot : value C (mask (S w)) (out w) = true := by
    rw [he w _ (by rw [mask_weight, hsize]; exact hqK)]
    simp [mask]
  have hout : value C (mask U) (out w) = true := by
    apply hcut (mask (S w)) (mask U) _ hroot
    intro b hmem hon
    apply value_mono C hG (mask (F b)) (mask U) _ b (hkeep b hmem hon)
    intro p hp
    exact decide_eq_true (Finset.mem_biUnion.mpr ⟨b,hmem,of_decide_eq_true hp⟩)
  rw [he w _ (by simpa only [mask_weight] using hweight)] at hout
  have hsub : S w ⊆ U := fun p hp => of_decide_eq_true (of_decide_eq_true hout p hp)
  have hint : (U ∩ S w) = S w := Finset.inter_eq_right.mpr hsub
  change (U ∩ S w).card ≤ B.card at hmeet
  rw [hint, hsize] at hmeet
  omega

end PEqualNP.Outside.L_meta_925_aux

open PEqualNP.Outside.L_meta_925_aux in
theorem PEqualNP.Outside.L_meta_925 :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q →
    (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) →
    ∀ c : ℕ, c ≤ q → c * q < K →
    m * c ≤ gates.length := by
  intro q n m K S hq hsize hinter gates out hG he c hc hK
  classical
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,0⟩
  let G (w : Fin m) := privateWires C S w
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro b hi hj
    exact (Finset.mem_filter.mp hi).2.2 j hij.symm (Finset.mem_filter.mp hj).2.1
  calc
    m*c = ∑ _ : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (G w).card :=
      Finset.sum_le_sum fun w _ => per_output S C out hq hsize hinter hG he hc hK w
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card fun b hb => by
      obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hb
      exact (Finset.mem_filter.mp hw).1
    _ = gates.length := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
