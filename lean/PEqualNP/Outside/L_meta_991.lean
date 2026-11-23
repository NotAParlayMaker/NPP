import Mathlib
import PEqualNP.Defs

-- Circuit evaluation and the binary-gate cut are adapted from PR 149 by k-sandhu.
-- Adapted here to the current proof-file namespace rules.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.Cross991

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


private def test {n : ℕ} (y : Finset (Fin n)) (p v : Fin n) := decide (v ∈ y ∨ v=p)
private def avoid {n : ℕ} (s : Finset (Fin n)) (v : Fin n) := decide (v ∉ s)
private def points {n : ℕ} (C : Circuit) (s y : Finset (Fin n)) (w : ℕ) :=
  s.filter fun p => value C (test y p) w = true
private def charged {n : ℕ} (C : Circuit) (s y : Finset (Fin n)) :=
  (Finset.Ico n (n+C.size)).filter fun w => value C (avoid s) w = false ∧ 2 ≤ (points C s y w).card

private theorem actual {n : ℕ} (C : Circuit) (s y : Finset (Fin n)) (hd : Disjoint y s)
    (w : ℕ) (hz : value C (avoid s) w = false) (hm : 2 ≤ (points C s y w).card) :
    w ∈ Finset.Ico n (n+C.size) := by
  apply Finset.mem_Ico.mpr
  constructor
  · by_contra! h
    let a : Fin n := ⟨w,h⟩
    change value C (avoid s) a = false at hz
    have ha : a ∈ s := by simpa [input_value,avoid] using hz
    have hy : a ∉ y := fun hh => Finset.disjoint_left.mp hd hh ha
    have sub : points C s y w ⊆ {a} := by
      intro p hp
      have h := (Finset.mem_filter.mp hp).2
      change value C (test y p) a = true at h
      simpa [input_value,test,hy,eq_comm] using h
    have le := Finset.card_le_card sub
    simp at le
    omega
  · by_contra! h
    have eq : points C s y w = ∅ := by ext p; simp [points,missing_value C _ w h]
    simp [eq] at hm

private theorem row_bound {n : ℕ} (C : Circuit) (s y : Finset (Fin n)) (o : ℕ)
    (hg : ∀ g ∈ C.gates,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (hd : Disjoint y s) (hout : value C (avoid s) o = false)
    (hit : ∀ p ∈ s, value C (test y p) o = true) :
    s.card ≤ (charged C s y).card + 1 := by
  classical
  let G := charged C s y
  have wires (w : ℕ) (hw : w ∈ G) := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,dis,card,transfer⟩ := cut C hg G wires (n+C.size) {o} (fun w _ hw => (wires w hw).2)
  let cover (w : ℕ) := if value C (avoid s) w = false then points C s y w else ∅
  have small (w : ℕ) (hw : w∈B) : (cover w).card ≤ 1 := by
    by_cases hz : value C (avoid s) w = false
    · simp only [cover,hz,ite_true]
      by_contra! h
      have hm : 2 ≤ (points C s y w).card := by omega
      exact Finset.disjoint_left.mp dis hw (Finset.mem_filter.mpr ⟨actual C s y hd w hz hm,hz,hm⟩)
    · simp [cover,hz]
  have sub : s ⊆ B.biUnion cover := by
    intro p hp
    by_contra h
    have ht := transfer (test y p) (avoid s) (by
      intro w hw hon
      cases hz : value C (avoid s) w with
      | true => rfl
      | false =>
        exact False.elim (h (Finset.mem_biUnion.mpr ⟨w,hw,by
          simp only [cover,hz,ite_true]
          exact Finset.mem_filter.mpr ⟨hp,hon⟩⟩))) o (Finset.mem_singleton_self o) (hit p hp)
    simp [hout] at ht
  have hs := Finset.card_le_card sub
  have hb := Finset.card_biUnion_le_card_mul B cover 1 small
  have hf := Finset.card_filter_le G (fun v => v<n+C.size)
  simp only [Finset.card_singleton] at card
  simp only [Nat.mul_one] at hb
  change s.card ≤ G.card+1
  omega
private theorem shared {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (a b u v : Finset (Fin n)) (hc : (a ∩ b).card ≤ 1) (w : ℕ)
    (ha : w ∈ charged C a u) (hb : w ∈ charged C b v) : ¬ Disjoint u b := by
  intro hd
  have hm := (Finset.mem_filter.mp ha).2.2
  have hsub : ¬ points C a u w ⊆ a ∩ b := by
    intro h
    have le := (Finset.card_le_card h).trans hc
    omega
  obtain ⟨p,hp,hnot⟩ := Finset.not_subset.mp hsub
  obtain ⟨hpa,hval⟩ := Finset.mem_filter.mp hp
  have hpb : p ∉ b := fun h => hnot (Finset.mem_inter.mpr ⟨hpa,h⟩)
  have ht : value C (avoid b) w = true := by
    apply value_mono C hg (test u p) (avoid b) _ w hval
    intro x hx
    rcases of_decide_eq_true hx with hu|rfl
    · exact decide_eq_true (Finset.disjoint_left.mp hd hu)
    · exact decide_eq_true hpb
  rw [(Finset.mem_filter.mp hb).2.1] at ht
  contradiction

private theorem lower {n m D : ℕ} (S y : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (cross : ∀ i j, i≠j → (S i ∩ S j).card ≤ 1) (hd : ∀ i, Disjoint (y i) (S i))
    (hg : ∀ g ∈ C.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
    (out : ∀ i (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true →
        ∃ p ∈ S i, x p=true)
    (hit : ∀ i, ∀ p ∈ S i, value C (test (y i) p) (o i) = true)
    (cap : ∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i≠j → ¬Disjoint (y i) (S j)) → J.card ≤ D) :
    (∑ i, (S i).card) ≤ D*C.size+m := by
  classical
  let G (i : Fin m) := charged C (S i) (y i)
  let W := Finset.Ico n (n+C.size)
  have cost (i : Fin m) : (S i).card ≤ (G i).card+1 := by
    apply row_bound C (S i) (y i) (o i) hg (hd i) _ (hit i)
    cases h : value C (avoid (S i)) (o i) with
    | false => rfl
    | true =>
      obtain ⟨p,hp,hno⟩ := out i _ h
      simp [avoid,hp] at hno
  let rel (i : Fin m) (w : ℕ) := w ∈ G i
  have above (i : Fin m) : W.bipartiteAbove rel i = G i := by
    ext w
    rw [Finset.mem_bipartiteAbove]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  have below (w : ℕ) : ((Finset.univ : Finset (Fin m)).bipartiteBelow rel w).card ≤ D := by
    apply cap
    intro i hi j hj hne
    exact shared C hg (S i) (S j) (y i) (y j) (cross i j hne) w
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have sum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=Finset.univ) (t:=W) rel
  simp_rw [above] at sum
  calc
    (∑ i, (S i).card) ≤ ∑ i, ((G i).card+1) := Finset.sum_le_sum (fun i _ => cost i)
    _ = (∑ w ∈ W, ((Finset.univ : Finset (Fin m)).bipartiteBelow rel w).card)+m := by simp [Finset.sum_add_distrib,sum]
    _ ≤ (∑ _w ∈ W,D)+m := Nat.add_le_add_right (Finset.sum_le_sum (fun w _ => below w)) _
    _ = D*C.size+m := by simp [W,Nat.mul_comm]
end PEqualNP.Outside.Cross991
theorem PEqualNP.Outside.L_meta_991 : ¬ (∃ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧ (∀ i : Fin m, Disjoint (y i) (S i)) ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) ∧ (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) ∧ (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) ∧ D * C.gates.length + m < ∑ i : Fin m, (S i).card) := by
  rintro ⟨n,m,D,S,y,C,o,cross,hd,hg,out,hit,cap,hlt⟩
  exact (not_lt_of_ge (PEqualNP.Outside.Cross991.lower S y C o cross hd hg out hit cap)) hlt
