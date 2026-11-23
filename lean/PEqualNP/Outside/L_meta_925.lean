import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- Proof developed by Astra (OpenAI Codex) for project participant Stibnit3.
-- The cut and wire evaluation helpers adapt the proof of L-meta-270 by k-sandhu.

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
  refine ⟨P, (Finset.card_filter_le ..).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr; exact (Finset.mem_filter.mp hr).2
  · intro x y hh hx
    have tr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hh r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    obtain ha|ha := hop
    · simp only [ha, GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,
        and_imp,forall_apply_eq_imp_iff₂,id_eq] at hx ⊢
      exact fun r hr => tr r hr (hx r hr)
    · simp only [ha, GateOp.eval,List.any_eq_true,List.mem_map,exists_exists_and_eq_and,
        id_eq] at hx ⊢
      obtain ⟨r,hr,ht⟩ := hx
      exact ⟨r,hr,tr r hr ht⟩

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

private def bits {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ T)

private lemma union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q+1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (B : Finset ℕ) (T : ℕ → Finset (Fin n))
    (ht : ∀ b ∈ B, (T b).card ≤ 1 ∨ ∃ j, T b = S j) :
    (B.biUnion T).card ≤ B.card*q+1 := by
  classical
  by_cases ex : ∃ b ∈ B, ∃ j, T b = S j
  · obtain ⟨b,hb,j,hj⟩ := ex
    let D := B.erase b
    let R (v : ℕ) := T v \ S j
    have hc : ∀ v ∈ D, (R v).card ≤ q := by
      intro v hv
      rcases ht v (Finset.mem_of_mem_erase hv) with h|⟨k,hk⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans (by omega)
      · by_cases hkj : k = j
        · simp [R,hk,hkj]
        · have H := Finset.card_union_add_card_inter (S k) (S j)
          have E : (S k \ S j) ∪ S j = S k ∪ S j := by ext x; simp
          have I : (S k \ S j) ∩ S j = ∅ := by ext x; simp
          have A := Finset.card_union_add_card_inter (S k \ S j) (S j)
          rw [E,I,Finset.card_empty] at A
          rw [hi _ _ hkj,hs k] at H
          simpa [R,hk] using (show (S k \ S j).card ≤ q by omega)
    have sub : B.biUnion T ⊆ S j ∪ D.biUnion R := by
      intro x hx; rcases Finset.mem_biUnion.mp hx with ⟨v,hv,hm⟩
      by_cases h : x ∈ S j
      · exact Finset.mem_union_left _ h
      · have ne : v ≠ b := by rintro rfl; exact h (hj ▸ hm)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,Finset.mem_erase.mpr ⟨ne,hv⟩,Finset.mem_sdiff.mpr ⟨hm,h⟩⟩)
    have hh := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
    have hh' := Finset.card_biUnion_le_card_mul D R q hc
    have hd : D.card + 1 = B.card := Finset.card_erase_add_one hb
    rw [← hd,Nat.add_mul,Nat.one_mul]
    rw [hs] at hh
    omega
  · have small : ∀ v ∈ B, (T v).card ≤ 1 := by
      intro v hv; exact (ht v hv).resolve_right (fun h => ex ⟨v,hv,h⟩)
    have h := Finset.card_biUnion_le_card_mul B T 1 small
    have h' : B.card * 1 ≤ B.card*q := Nat.mul_le_mul_left _ (by omega)
    omega

private noncomputable def owned {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) :=
  (Finset.Ico n (n + C.size)).filter (fun w =>
    value C (bits (S i)) w = true ∧ ∀ j, j ≠ i → value C (bits (S j)) w = false)

private lemma enough {n m q K c : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) (o : ℕ)
    (hq : 2 ≤ q) (hs : ∀ j, (S j).card = q+1)
    (hi : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ok : ∀ T : Finset (Fin n), T.card ≤ K → value C (bits T) o = decide (S i ⊆ T))
    (hc : c ≤ q) (hk : c*q < K) : c ≤ (owned C S i).card := by
  classical
  by_contra! small
  let G := owned C S i
  have hg : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hB, hcut⟩ := cut C hG G hg (n+C.size) {o} (fun w _ hw => (hg w hw).2)
  have hb : B.card ≤ c := by
    have hh := Finset.card_filter_le G (· < n + C.size)
    change G.card < c at small
    simp only [Finset.card_singleton] at hB
    omega
  have localW (w : ℕ) : ∃ T : Finset (Fin n),
      ((T.card ≤ 1) ∨ ∃ j, j ≠ i ∧ T = S j) ∧
      (w ∈ B → value C (bits (S i)) w = true → value C (bits T) w = true) := by
    by_cases a : w ∈ B ∧ value C (bits (S i)) w = true
    · by_cases low : w < n
      · let p : Fin n := ⟨w,low⟩
        refine ⟨{p},Or.inl (by simp),fun _ _ => ?_⟩
        change value C (bits {p}) p = true
        simp [input_value,bits]
      · have high : w < n+C.size := by
          by_contra! hh; have := missing_value C (bits (S i)) w hh; simp_all
        have nex : ¬ ∀ j, j ≠ i → value C (bits (S j)) w = false := by
          intro H; exact Finset.disjoint_left.mp hd a.1 (Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨by omega,high⟩,a.2,H⟩)
        push Not at nex
        obtain ⟨j,hn,hv⟩ := nex
        exact ⟨S j,Or.inr ⟨j,hn,rfl⟩,fun _ _ => by simpa using hv⟩
    · exact ⟨∅,Or.inl (by simp),fun h t => False.elim (a ⟨h,t⟩)⟩
  choose T shape test using localW
  let U := B.biUnion T
  have hu : U.card ≤ K := by
    have H := union_bound S hq hs hi B T (fun w _ => (shape w).imp_right (fun ⟨j,_,h⟩ => ⟨j,h⟩))
    change (B.biUnion T).card ≤ K
    have := Nat.mul_le_mul_right q hb
    omega
  have notSub : ¬ S i ⊆ U := by
    intro sub
    let A (w : ℕ) := T w ∩ S i
    have H : S i ⊆ B.biUnion A := by
      intro v hv; obtain ⟨w,hw,hv'⟩ := Finset.mem_biUnion.mp (sub hv)
      exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hv',hv⟩⟩
    have hcA : ∀ w ∈ B, (A w).card ≤ 1 := by
      intro w _; rcases shape w with h|⟨j,hn,h⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans h
      · simp [A,h,hi j i hn]
    have ha := Finset.card_biUnion_le_card_mul B A 1 hcA
    have hh := Finset.card_le_card H
    rw [hs] at hh
    omega
  have pos : 1 ≤ c := by omega
  have le : (S i).card ≤ K := by
    have := Nat.mul_le_mul_right q pos
    rw [Nat.one_mul] at this
    rw [hs]; omega
  have ht : value C (bits (S i)) o = true := by simp [ok _ le]
  have now := hcut (bits (S i)) (bits U) (fun w hw h => value_mono C hG (bits (T w)) (bits U)
    (fun p hp => by exact decide_eq_true (Finset.mem_biUnion.mpr ⟨w,hw,of_decide_eq_true hp⟩ : p ∈ U))
    w (test w hw h)) o (Finset.mem_singleton_self _) ht
  simp [ok _ hu,notSub] at now

end PEqualNP.Outside.L_meta_925

open PEqualNP.Outside.L_meta_925 in
theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hs hi gs o hg hok c hc hk
  let C : Circuit := ⟨gs,0⟩
  let G := owned C S
  have cost (i : Fin m) : c ≤ (G i).card := by
    apply enough C S i (o i) hq hs hi hg _ hc hk
    intro T ht
    have eq : Finset.univ.filter (fun p => bits T p = true) = T := by ext; simp [bits]
    have H := hok i (bits T) (by rw [eq]; exact ht)
    change value C (bits T) (o i) = _ at H
    rw [H]
    congr 1
    apply propext
    simp only [bits, decide_eq_true_eq]
    rfl
  have dis : ((Finset.univ : Finset (Fin m)) : Set _).PairwiseDisjoint G := by
    intro i _ j _ hn
    apply Finset.disjoint_left.mpr
    intro w wi wj
    have a := (Finset.mem_filter.mp wi).2.2 j (Ne.symm hn)
    have b := (Finset.mem_filter.mp wj).2.1
    exact Bool.noConfusion (a.symm.trans b)
  calc
    m*c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => cost i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion dis).symm
    _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card (fun w hw => by
      obtain ⟨i,_,h⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp h).1)
    _ = gs.length := by simp [C,Circuit.size]
