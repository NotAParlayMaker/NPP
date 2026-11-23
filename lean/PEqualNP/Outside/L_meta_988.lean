import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988

open PEqualNP.CircuitLowerBounds

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
    (hw : n + C.gates.length ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j; omega
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
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.gates.length) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hr, rfl⟩ := hb
      exact step r hr (hx _ ⟨r, hr, rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r, hr, rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r, hr, rfl⟩, step r hr hv⟩

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
    by_cases hw : w < n + C.gates.length
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expanding one selected wire adds at most two earlier wires to the frontier.
private lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.gates.length)
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

private def avoids {n : ℕ} (S : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ S)

private def addsPoint {n : ℕ} (y : Finset (Fin n)) (p v : Fin n) : Bool :=
  decide (v ∈ y ∨ v = p)

private def support {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter (fun p => value C (addsPoint y p) w = true)

private lemma mem_support {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ support C S y w ↔ p ∈ S ∧ value C (addsPoint y p) w = true :=
  Finset.mem_filter

private abbrev charge {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ) : Prop :=
  value C (avoids S) w = false ∧ 2 ≤ (support C S y w).card

private def assigned {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.gates.length)).filter (charge C S y)

private lemma charge_is_gate {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (w : ℕ)
    (hy : Disjoint y S) (hcharge : charge C S y w) :
    n ≤ w ∧ w < n + C.gates.length := by
  constructor
  · by_contra! hw
    let v : Fin n := ⟨w, hw⟩
    have hfalse : avoids S v = false := (input_value C (avoids S) v).symm.trans hcharge.1
    have hvS : v ∈ S := by simpa [avoids] using hfalse
    have hvy : v ∉ y := fun hv => Finset.disjoint_left.mp hy hv hvS
    have hsub : support C S y w ⊆ {v} := by
      intro p hp
      have htrue := (mem_support C S y w p).mp hp |>.2
      change value C (addsPoint y p) (v : ℕ) = true at htrue
      simpa [input_value, addsPoint, hvy, eq_comm] using htrue
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    have hl := hcharge.2
    omega
  · by_contra! hw
    have hempty : support C S y w = ∅ := by
      ext p
      simp [mem_support, missing_value C _ w hw]
    have hl := hcharge.2
    simp [hempty] at hl

-- Each frontier wire that is false on the avoiding assignment covers at most one point.
private lemma count_assigned {n : ℕ} (C : Circuit) (S y : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hy : Disjoint y S) (hneg : value C (avoids S) o = false)
    (hpos : ∀ p ∈ S, value C (addsPoint y p) o = true) :
    S.card ≤ (assigned C S y).card + 1 := by
  let G := assigned C S y
  have hgate (w : ℕ) (hw : w ∈ G) : n ≤ w ∧ w < n + C.gates.length :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hcard, hcut⟩ := cut C hG G hgate (n + C.gates.length) {o}
    (fun w _ hw => (hgate w hw).2)
  let F := B.filter (fun w => value C (avoids S) w = false)
  have hsmall (w : ℕ) (hw : w ∈ F) : (support C S y w).card ≤ 1 := by
    obtain ⟨hb, hfalse⟩ := Finset.mem_filter.mp hw
    by_contra! hlarge
    have hcharge : charge C S y w := ⟨hfalse, hlarge⟩
    exact Finset.disjoint_left.mp hd hb
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (charge_is_gate C S y w hy hcharge), hcharge⟩)
  have hcovered : S ⊆ F.biUnion (support C S y) := by
    intro p hp
    by_contra hmiss
    have htrue : value C (avoids S) o = true := by
      apply hcut (addsPoint y p) (avoids S) _ o (Finset.mem_singleton_self o) (hpos p hp)
      intro w hw ht
      by_contra hfalse
      have hz : value C (avoids S) w = false := Bool.eq_false_iff.mpr hfalse
      exact hmiss (Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_filter.mpr ⟨hw, hz⟩, (mem_support C S y w p).mpr ⟨hp, ht⟩⟩)
    rw [hneg] at htrue
    cases htrue
  calc
    S.card ≤ (F.biUnion (support C S y)).card := Finset.card_le_card hcovered
    _ ≤ F.card * 1 := Finset.card_biUnion_le_card_mul F (support C S y) 1 hsmall
    _ ≤ B.card := by simpa only [mul_one] using Finset.card_filter_le B _
    _ ≤ 1 + (G.filter (· < n + C.gates.length)).card := by simpa using hcard
    _ ≤ (assigned C S y).card + 1 := by
      rw [Nat.add_comm 1]
      exact Nat.add_le_add_right (Finset.card_filter_le G (· < n + C.gates.length)) 1

private lemma shared_charge {n : ℕ} (C : Circuit) (S T y z : Finset (Fin n)) (w : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hST : (S ∩ T).card ≤ 1) (hs : charge C S y w) (ht : charge C T z w) :
    ¬ Disjoint y T := by
  intro hd
  have hsub : support C S y w ⊆ S ∩ T := by
    intro p hp
    obtain ⟨hpS, hptrue⟩ := (mem_support C S y w p).mp hp
    refine Finset.mem_inter.mpr ⟨hpS, ?_⟩
    by_contra hpT
    have hinput (v : Fin n) (hv : addsPoint y p v = true) : avoids T v = true := by
      have hmem : v ∈ y ∨ v = p := of_decide_eq_true hv
      have hvT : v ∉ T := hmem.elim (fun hvy hvT => Finset.disjoint_left.mp hd hvy hvT)
        (fun h => h ▸ hpT)
      simp [avoids, hvT]
    have htrue := value_mono C hG (addsPoint y p) (avoids T) hinput w hptrue
    rw [ht.1] at htrue
    cases htrue
  have hcard := (Finset.card_le_card hsub).trans hST
  have hl := hs.2
  omega

end PEqualNP.Outside.L_meta_988

open PEqualNP.Outside.L_meta_988 in
theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  intro n m D S y C o hinter hy hG hbelow hpos hsharing
  let W := Finset.Ico n (n + C.gates.length)
  let G (i : Fin m) := assigned C (S i) (y i)
  let J (w : ℕ) := Finset.univ.filter (fun i : Fin m => charge C (S i) (y i) w)
  have hn (i : Fin m) : value C (avoids (S i)) (o i) = false := by
    by_contra h
    obtain ⟨p, hp, ht⟩ := hbelow i (avoids (S i)) (Bool.eq_true_of_not_eq_false h)
    simp [avoids, hp] at ht
  have htotal : (∑ i : Fin m, (G i).card) = ∑ w ∈ W, (J w).card := by
    simp only [G, assigned, ← show W = Finset.Ico n (n + C.gates.length) from rfl, J,
      Finset.card_filter]
    exact Finset.sum_comm
  have hcap (w : ℕ) : (J w).card ≤ D := by
    apply hsharing
    intro i hi j hj hij
    exact shared_charge C (S i) (S j) (y i) (y j) w hG (hinter i j hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  calc
    ∑ i : Fin m, (S i).card ≤ ∑ i : Fin m, ((G i).card + 1) :=
      Finset.sum_le_sum (fun i _ => count_assigned C (S i) (y i) (o i) hG (hy i) (hn i) (hpos i))
    _ = (∑ w ∈ W, (J w).card) + m := by
      rw [Finset.sum_add_distrib, htotal]
      simp
    _ ≤ (∑ _w ∈ W, D) + m :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun w _ => hcap w)) m
    _ = D * C.gates.length + m := by simp [W, Nat.mul_comm]
