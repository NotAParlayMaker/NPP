import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1522

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

def support {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter (fun a => value C (fun v => decide (v=a)) w = true)

lemma crossing {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (y : Fin n → Bool)
    (hgate : ∀ g ∈ C.gates, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (k w : ℕ) (hk : 2 ≤ k) (hy : value C y w = false) (hs : k ≤ (support C S w).card) :
    ∃ B : Fin C.gates.length, (C.gates.get B).op = GateOp.or ∧
      value C y (n+B.val)=false ∧ k ≤ (support C S (n+B.val)).card ∧
      (support C S (n+B.val)).card ≤ 2*(k-1) := by
  classical
  let P (r : ℕ) := value C y r=false ∧ k ≤ (support C S r).card
  have hex : ∃ r, P r := ⟨w,hy,hs⟩
  let v := Nat.find hex
  obtain ⟨hvy,hvs⟩ := (Nat.find_spec hex : P v)
  change value C y v=false at hvy
  change k ≤ (support C S v).card at hvs
  have hmin (r : ℕ) (hr : r<v) (hyr : value C y r=false) : (support C S r).card < k := by
    have hh := Nat.find_min hex hr
    change ¬ (value C y r=false ∧ k ≤ (support C S r).card) at hh
    exact lt_of_not_ge (fun hge => hh ⟨hyr,hge⟩)
  have hn : n ≤ v := by
    by_contra h
    have hvn : v<n := by omega
    have hsub : support C S v ⊆ {⟨v,hvn⟩} := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      have hin := input_value C (fun u => decide (u=a)) ⟨v,hvn⟩
      change value C (fun u => decide (u=a)) v = _ at hin
      rw [hin] at ha'
      have he : (⟨v,hvn⟩ : Fin n)=a := of_decide_eq_true ha'
      simpa [he]
    have hh := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hh
    omega
  have hvbound : v < n+C.size := by
    by_contra h
    have hmiss : n+C.size ≤ v := by omega
    have hzero : support C S v=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha
      rw [missing_value C _ v hmiss]
      decide
    rw [hzero, Finset.card_empty] at hvs
    omega
  let j := v-n
  have hj : j<C.gates.length := by dsimp [j]; unfold Circuit.size at hvbound; omega
  have he : n+j=v := by dsimp [j]; omega
  obtain ⟨hop,hlen⟩ := hgate C.gates[j] (List.getElem_mem hj)
  have hsupport : (support C S v).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha⟩ := hsupport
  have hat : value C (fun u => decide (u=a)) v=true := (Finset.mem_filter.mp ha).2
  have hor : C.gates[j].op=GateOp.or := by
    rcases hop with hand | hor
    · have hall (r : ℕ) (hr : r∈C.gates[j].inputs) : r<v := by
        have hh := (and_value C j hj hand (fun u => decide (u=a))).mp (by simpa [he] using hat)
        simpa only [he] using (hh r hr).1
      have hchild : ∃ r∈C.gates[j].inputs, value C y r=false := by
        by_contra hh
        push_neg at hh
        have htrue : value C y (n+j)=true := (and_value C j hj hand y).mpr (by
          intro r hr
          exact ⟨by simpa only [he] using hall r hr, Bool.eq_true_of_not_eq_false (hh r hr)⟩)
        rw [he,hvy] at htrue
        contradiction
      obtain ⟨r,hr,hry⟩ := hchild
      have hsub : support C S v ⊆ support C S r := by
        intro b hb
        obtain ⟨hbS,hbt⟩ := Finset.mem_filter.mp hb
        apply Finset.mem_filter.mpr
        refine ⟨hbS,?_⟩
        have hh := (and_value C j hj hand (fun u => decide (u=b))).mp (by simpa [he] using hbt)
        exact (hh r hr).2
      have hh := Finset.card_le_card hsub
      have hsmall := hmin r (hall r hr) hry
      omega
    · exact hor
  have hchild (r : ℕ) (hr : r∈C.gates[j].inputs) (hrv : r<v) : value C y r=false := by
    cases hval : value C y r with
    | false => rfl
    | true =>
      have hh := (or_value C j hj hor y).mpr ⟨r,hr,by simpa only [he] using hrv,hval⟩
      rw [he,hvy] at hh
      contradiction
  let A (r : ℕ) := if r<v then support C S r else ∅
  have hbound (r : ℕ) (hr : r∈C.gates[j].inputs.toFinset) : (A r).card ≤ k-1 := by
    have hr' := List.mem_toFinset.mp hr
    by_cases hrv : r<v
    · have hh := hmin r hrv (hchild r hr' hrv)
      simp only [A,if_pos hrv]
      omega
    · simp [A,hrv]
  have hsub : support C S v ⊆ C.gates[j].inputs.toFinset.biUnion A := by
    intro b hb
    obtain ⟨hbS,hbt⟩ := Finset.mem_filter.mp hb
    obtain ⟨r,hr,hrv,hrt⟩ := (or_value C j hj hor (fun u => decide (u=b))).mp (by simpa [he] using hbt)
    apply Finset.mem_biUnion.mpr
    refine ⟨r,List.mem_toFinset.mpr hr,?_⟩
    have hr' : r<v := by simpa only [he] using hrv
    simp only [A,if_pos hr']
    exact Finset.mem_filter.mpr ⟨hbS,hrt⟩
  have hcard : (support C S v).card ≤ 2*(k-1) := by
    calc
      _ ≤ (C.gates[j].inputs.toFinset.biUnion A).card := Finset.card_le_card hsub
      _ ≤ C.gates[j].inputs.toFinset.card*(k-1) := Finset.card_biUnion_le_card_mul _ _ _ hbound
      _ ≤ 2*(k-1) := Nat.mul_le_mul_right _ ((List.toFinset_card_le _).trans hlen)
  refine ⟨⟨j,hj⟩,hor,?_,?_,?_⟩
  · simpa only [he] using hvy
  · simpa only [he] using hvs
  · simpa only [he] using hcard

end PEqualNP.Outside.L_meta_1522
theorem PEqualNP.Outside.L_meta_1522 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false →
    (∀ a ∈ ({0, 1, 3} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) →
    ∃ B1 B2 : Fin gates.length, B1 ≠ B2 ∧
      (gates.get B1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get B2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B1 : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B2 : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧
      (({0, 1, 3} : Finset (Fin 13)).filter (fun a => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B1 : ℕ)⟩
        (List.ofFn (fun v : Fin 13 => decide (v = a))) = true)).card = 2 ∧
      (∀ a ∈ ({0, 1, 3} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (B2 : ℕ)⟩
        (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) := by
  classical
  intro L hL gates out hgate hy hs
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,out⟩
  let S : Finset (Fin 13) := {0,1,3}
  let y : Fin 13 → Bool := fun v => decide (v∉L 0)
  have hScard : S.card=3 := by decide
  have hfull : PEqualNP.Outside.L_meta_1522.support C S out=S := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    exact hs a ha
  have hfalse : PEqualNP.Outside.L_meta_1522.value C y out=false := hy
  obtain ⟨B1,hB1,hf1,hlo1,hhi1⟩ := PEqualNP.Outside.L_meta_1522.crossing C S y hgate 2 out (by omega) hfalse (by simp only [hfull,hScard] <;> omega)
  obtain ⟨B2,hB2,hf2,hlo2,hhi2⟩ := PEqualNP.Outside.L_meta_1522.crossing C S y hgate 3 out (by omega) hfalse (by simp only [hfull,hScard] <;> omega)
  have htwo : (PEqualNP.Outside.L_meta_1522.support C S (13+B1.val)).card=2 := by omega
  have heq : PEqualNP.Outside.L_meta_1522.support C S (13+B2.val)=S := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    change S.card ≤ (PEqualNP.Outside.L_meta_1522.support C S (13+B2.val)).card
    omega
  have hne : B1≠B2 := by
    intro h
    subst B2
    omega
  refine ⟨B1,B2,hne,hB1,hB2,hf1,hf2,htwo,?_⟩
  intro a ha
  have hm : a∈PEqualNP.Outside.L_meta_1522.support C S (13+B2.val) := by rw [heq]; exact ha
  exact (Finset.mem_filter.mp hm).2