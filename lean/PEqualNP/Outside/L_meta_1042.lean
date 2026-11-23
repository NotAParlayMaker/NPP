import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1042

open PEqualNP.CircuitLowerBounds

def pasch : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]

lemma pasch_card (i : Fin 4) : (pasch i).card = 3 := by
  fin_cases i <;> decide

lemma pasch_inter_le (i j : Fin 4) (hij : i ≠ j) : (pasch i ∩ pasch j).card ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [pasch]

lemma pasch_inter_nonempty (i j : Fin 4) : (pasch i ∩ pasch j).Nonempty := by
  fin_cases i <;> fin_cases j <;> decide

lemma pasch_deg (v : Fin 6) : (Finset.univ.filter (fun i : Fin 4 => v ∈ pasch i)).card = 2 := by
  fin_cases v <;> decide

lemma pasch_not_deg (v : Fin 6) : (Finset.univ.filter (fun i : Fin 4 => v ∉ pasch i)).card = 2 := by
  fin_cases v <;> decide

lemma pasch_sum : ∑ i : Fin 4, ((pasch i).card - 1) = 8 := by
  decide

lemma pasch_ne {i j : Fin 4} (hij : i ≠ j) : pasch i ≠ pasch j := by
  fin_cases i <;> fin_cases j <;> simp_all [pasch] <;> decide

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

lemma value_eval {n : ℕ} (gl : List Gate) (o : ℕ) (x : Fin n → Bool) :
    value ⟨gl, o⟩ x o = Circuit.eval ⟨gl, o⟩ (List.ofFn x) :=
  rfl

lemma value_irrel {n : ℕ} (gl : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (w : ℕ) :
    value ⟨gl, o1⟩ x w = value ⟨gl, o2⟩ x w :=
  rfl

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

abbrev good (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gate_inputs {n : ℕ} (C : Circuit) (hG : good C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
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
      obtain ⟨b, ⟨r, hr, rfl⟩, hv⟩ := hx
      exact ⟨_, ⟨r, hr, rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit) (hG : good C)
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

lemma cut {n : ℕ} (C : Circuit) (hG : good C)
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
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

def bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

def owned {n : ℕ} (C : Circuit) (z : ℕ) (P S : Finset (Fin n)) : Finset ℕ :=
  ((Finset.Ico n (n + C.size)).erase z).filter fun w =>
    support C w ∩ P ⊆ S ∧ 2 ≤ (support C w ∩ P).card

theorem countOne {n : ℕ} (C : Circuit) (z o : ℕ) (P S : Finset (Fin n)) (hg : good C)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hpos : ∀ p ∈ S ∩ P, value C (fun v => decide (v = p)) o = true)
    (hneg : value C (bit (P \ S)) o = false) :
    (S ∩ P).card - 1 ≤ (owned C z P S).card := by
  classical
  let G := owned C z P S
  have hgate (w) (hw : w ∈ G) : n ≤ w ∧ w < n + C.size :=
    Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  obtain ⟨B, hd, hc, hcut⟩ := cut C hg G hgate (n + C.size) {o} (fun w _ hw => (hgate w hw).2)
  let y := bit (P \ S)
  let F := B.filter fun w => value C y w = false
  have small (w) (hw : w ∈ F) : (support C w ∩ P).card ≤ 1 := by
    have hb := (Finset.mem_filter.mp hw).1
    have hv := (Finset.mem_filter.mp hw).2
    have hs : support C w ∩ P ⊆ S := by
      intro p hp
      by_contra h
      have hpt := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
      have hmono := value_mono C hg (fun q => decide (q = p)) y (by
        intro q he
        have eq : q = p := of_decide_eq_true he
        subst q
        simp [y, bit, (Finset.mem_inter.mp hp).2, h]) w hpt
      simp [hv] at hmono
    by_contra! hlarge
    have hlt := Finset.card_le_card (Finset.inter_subset_left (s₂ := P) (s₁ := support C w))
    have hne : w ≠ z := by rintro rfl; simp [hz y] at hv
    exact Finset.disjoint_left.mp hd hb (Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr (support_gate C w (by omega))⟩, hs, by omega⟩)
  have covered : S ∩ P ⊆ F.biUnion (fun w => support C w ∩ P) := by
    intro p hp
    by_contra hn
    have hbad : value C y o = true := by
      apply hcut _ y _ o (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hv
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, Bool.eq_false_iff.mpr he⟩,
        Finset.mem_inter.mpr ⟨(mem_support C w p).mpr hv, (Finset.mem_inter.mp hp).2⟩⟩)
    rw [hneg] at hbad
    contradiction
  have h1 := Finset.card_le_card covered
  have h2 := Finset.card_biUnion_le_card_mul F (fun w => support C w ∩ P) 1 small
  have h3 := Finset.card_filter_le B (fun w => value C y w = false)
  change F.card ≤ B.card at h3
  have h4 := Finset.card_filter_le G (fun w => w < n + C.size)
  simp only [Finset.card_singleton] at hc
  change _ ≤ G.card
  omega

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) (b : Bool) : Circuit :=
  ⟨gates.set i0 (if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩), 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) (b : Bool) :
    (replC gates i0 b).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_good (gates : List Gate) (i0 : Fin gates.length) (b : Bool)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    good (replC gates i0.val b) := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · cases b <;> simp [replC, hki]
  · have e : (replC gates i0.val b).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_at {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (b : Bool) (x : Fin n → Bool) :
    value (replC gates i0.val b) x (n + i0.val) = b := by
  have h := gate_value (replC gates i0.val b) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  cases b <;> simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (b : Bool) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0 b) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0 b) x r else false) := by
  have h := gate_value (replC gates i0 b) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0 b).gates[w - n]'(by simp [replC]; omega) =
      gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq_before {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (b : Bool)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + i0.val) :
    value (replC gates i0.val b) x w = value ⟨gates, 0⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, 0⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val b) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    · have hlt : w < n + gates.length := by omega
      rw [orig_value gates 0 x w (by omega) hlt,
        replC_other gates i0.val b x w (by omega) hlt (by omega)]
      apply repl_eval_congr
      intro r _
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]

lemma replC_true_ge {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (x : Fin n → Bool) (w : ℕ) :
    value ⟨gates, o⟩ x w = true → value (replC gates i0.val true) x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val true) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact id
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · intro _
        rw [hne]
        exact replC_at gates i0 true x
      · rw [orig_value gates o x w (by omega) hw,
          replC_other gates i0.val true x w (by omega) hw hne]
        have hop : (gates[w - n]'(by omega)).op = GateOp.and ∨
            (gates[w - n]'(by omega)).op = GateOp.or := by
          rcases (hgate (gates[w - n]'(by omega)) (List.getElem_mem _)).1 with hop | hop | hop
          · exact Or.inl hop
          · exact Or.inr hop
          · have := congrArg Fin.val (hnot ⟨w - n, by omega⟩ hop)
            simp only at this
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · intro h
      rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega)] at h
      exact absurd h (by simp)

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (b : Bool) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = b) (w : ℕ) :
    value (replC gates i0.val b) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val b) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_at gates i0 b x
      · rw [orig_value gates o x w (by omega) hw,
          replC_other gates i0.val b x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val b) x w (by rw [replC_size]; omega)]

lemma orig_not_eval {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o hw : ℕ)
    (hop : (gates.get i0).op = GateOp.not) (hhead : (gates.get i0).inputs.head? = some hw)
    (hlt : hw < n + i0.val) (x : Fin n → Bool) :
    value ⟨gates, o⟩ x (n + i0.val) = !(value ⟨gates, o⟩ x hw) := by
  rw [orig_value gates o x (n + i0.val) (by omega) (by omega)]
  have e : gates[n + i0.val - n]'(by omega) = gates.get i0 := by simp
  rw [e, hop]
  obtain ⟨rest, hin⟩ : ∃ rest, (gates.get i0).inputs = hw :: rest := by
    cases h : (gates.get i0).inputs with
    | nil => rw [h] at hhead; simp at hhead
    | cons a rest => rw [h] at hhead; exact ⟨rest, by simpa using hhead⟩
  rw [hin]
  simp [GateOp.eval, hlt]

lemma orig_not_const_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (hop : (gates.get i0).op = GateOp.not)
    (hbad : (gates.get i0).inputs.head? = none ∨
      ∃ hw, (gates.get i0).inputs.head? = some hw ∧ n + i0.val ≤ hw)
    (x : Fin n → Bool) :
    value ⟨gates, o⟩ x (n + i0.val) = true := by
  rw [orig_value gates o x (n + i0.val) (by omega) (by omega)]
  have e : gates[n + i0.val - n]'(by omega) = gates.get i0 := by simp
  rw [e, hop]
  rcases hbad with hnone | ⟨hw, hsome, hge⟩
  · cases h : (gates.get i0).inputs with
    | nil => simp [GateOp.eval]
    | cons a rest => rw [h] at hnone; simp at hnone
  · cases h : (gates.get i0).inputs with
    | nil => rw [h] at hsome; simp at hsome
    | cons a rest =>
      rw [h] at hsome
      have ha : a = hw := by simpa using hsome
      subst ha
      have hnotlt : ¬ a < n + i0.val := by omega
      simp [GateOp.eval, hnotlt]

lemma before_mono {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (w : ℕ) (hw : w < n + i0.val)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  intro hx
  rw [← replC_eq_before gates i0 true x w hw] at hx
  rw [← replC_eq_before gates i0 true y w hw]
  exact value_mono (replC gates i0.val true) (replC_good gates i0 true hgate hnot) x y hxy w hx

lemma sum_card_disjoint_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (A : ι → Finset ℕ)
    (c : ι → ℕ) (B : Finset ℕ)
    (hd : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i ∈ R, A i ⊆ B)
    (hc : ∀ i ∈ R, c i ≤ (A i).card) :
    ∑ i ∈ R, c i ≤ B.card := by
  have hpd : (R : Set ι).PairwiseDisjoint A := fun i hi j hj hij => hd i hi j hj hij
  calc
    ∑ i ∈ R, c i ≤ ∑ i ∈ R, (A i).card := Finset.sum_le_sum hc
    _ = (R.biUnion A).card := (Finset.card_biUnion hpd).symm
    _ ≤ B.card := Finset.card_le_card fun w hw => by
      obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
      exact hsub i hi hwi

lemma sum_card_inter_eq {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, (S s ∩ U).card
      = ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  have h1 : ∀ s : Fin m, (S s ∩ U).card = ∑ u ∈ U, if u ∈ S s then 1 else 0 := by
    intro s
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  have h2 : ∀ u : Fin n, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
      = ∑ s : Fin m, if u ∈ S s then 1 else 0 := by
    intro u
    rw [Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

lemma sum_pred_le_sdiff {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, ((S s).card - 1)
      ≤ ∑ s : Fin m, ((S s \ U).card - 1)
        + ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  rw [← sum_card_inter_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h := Finset.card_sdiff_add_card_inter (S s) U
  omega

def keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) : Finset (Fin n) :=
  if t0 ∈ S then Finset.univ \ (T.erase t0) else Finset.univ \ T

lemma inter_keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) :
    S ∩ keep S T t0 = S \ T.erase t0 := by
  unfold keep
  split_ifs with h
  · ext a; simp
  · ext a
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hT => hn hT.2⟩
    · rintro ⟨ha, hn⟩
      exact ⟨ha, fun hT => hn ⟨fun e => h (e ▸ ha), hT⟩⟩

lemma case_hit_le_two (gl : List Gate) (ol : Fin 4 → ℕ) (i0 : Fin gl.length) (hw : ℕ)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (hop : (gl.get i0).op = GateOp.not)
    (hhead : (gl.get i0).inputs.head? = some hw)
    (hlt : hw < 6 + i0.val)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true))
    (T : Finset (Fin 6)) (t0 : Fin 6) (ht0 : t0 ∈ T) (hTcard : T.card ≤ 2)
    (hT : ∀ y : Fin 6 → Bool, (∀ t ∈ T, y t = false) → value ⟨gl, 0⟩ y hw = false) :
    8 ≤ gl.length := by
  classical
  let C := replC gl i0.val true
  have hlen : C.size = gl.length := replC_size gl i0.val true
  have hgood : good C := replC_good gl i0 true hgate hnot
  let z := 6 + i0.val
  have hz : ∀ x : Fin 6 → Bool, value C x z = true := replC_at gl i0 true
  let P : Fin 4 → Finset (Fin 6) := fun i => keep (pasch i) T t0
  let G : Fin 4 → Finset ℕ := fun i => owned C z (P i) (pasch i)
  have hok : ∀ i x, (∀ u ∈ T.erase t0, x u = false) → (t0 ∈ pasch i ∨ x t0 = false) →
      value C x (ol i) = decide (∃ v ∈ pasch i, x v = true) := by
    intro i x hx hcase
    have hval : value ⟨gl, ol i⟩ x (ol i) = decide (∃ v ∈ pasch i, x v = true) := hout i x
    by_cases h0 : x t0 = false
    · have hzero : ∀ t ∈ T, x t = false := by
        intro t ht
        by_cases htt : t = t0
        · rw [htt]; exact h0
        · exact hx t (Finset.mem_erase.mpr ⟨htt, ht⟩)
      have hztrue : value ⟨gl, ol i⟩ x z = true := by
        rw [orig_not_eval gl i0 (ol i) hw hop hhead hlt x]
        have hf : value ⟨gl, ol i⟩ x hw = false := hT x hzero
        simp [hf]
      rw [replC_eq gl i0 true (ol i) x hztrue (ol i), hval]
    · have hmem : t0 ∈ pasch i := hcase.resolve_right h0
      have htrue : decide (∃ v ∈ pasch i, x v = true) = true :=
        decide_eq_true ⟨t0, hmem, by simpa using h0⟩
      rw [htrue]
      exact replC_true_ge gl i0 (ol i) hgate hnot x (ol i) (hval.trans htrue)
  have hmask (i : Fin 4) (x : Fin 6 → Bool) (h : ∀ v, x v = true → v ∈ P i) :
      value C x (ol i) = decide (∃ v ∈ pasch i, x v = true) := by
    apply hok i x
    · intro u hdel
      apply Bool.eq_false_iff.mpr
      intro hv
      have hin := h u hv
      by_cases hi : t0 ∈ pasch i
      · have hf : u ∈ (Finset.univ : Finset (Fin 6)) \ T.erase t0 := by
          simpa only [P, keep, if_pos hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 hdel
      · have hf : u ∈ (Finset.univ : Finset (Fin 6)) \ T := by
          simpa only [P, keep, if_neg hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_erase.mp hdel).2
    · by_cases hi : t0 ∈ pasch i
      · exact Or.inl hi
      · refine Or.inr (Bool.eq_false_iff.mpr ?_)
        intro hv
        have hin := h t0 hv
        have hf : t0 ∈ (Finset.univ : Finset (Fin 6)) \ T := by
          simpa only [P, keep, if_neg hi] using hin
        exact (Finset.mem_sdiff.mp hf).2 ht0
  have hcount (i : Fin 4) : (pasch i \ T.erase t0).card - 1 ≤ (G i).card := by
    rw [← inter_keep (pasch i) T t0]
    apply countOne C z (ol i) (P i) (pasch i) hgood hz
    · intro p hp
      rw [hmask i _ (fun v hv => (of_decide_eq_true hv : v = p) ▸ (Finset.mem_inter.mp hp).2)]
      exact decide_eq_true ⟨p, (Finset.mem_inter.mp hp).1, by simp⟩
    · have supp (v : Fin 6) (hv : bit (P i \ pasch i) v = true) : v ∈ P i :=
        (Finset.mem_sdiff.mp (show v ∈ P i \ pasch i from of_decide_eq_true hv)).1
      rw [hmask i (bit (P i \ pasch i)) supp]
      apply decide_eq_false
      rintro ⟨p, hp, hb⟩
      exact (Finset.mem_sdiff.mp (show p ∈ P i \ pasch i from of_decide_eq_true hb)).2 hp
  have smallP (i : Fin 4) : (Finset.univ \ T) ⊆ P i := by
    intro p hp
    have hnt := (Finset.mem_sdiff.mp hp).2
    simp only [P, keep]
    split_ifs <;> simp_all
  have comp (i j : Fin 4) : P i ⊆ P j ∨ P j ⊆ P i := by
    by_cases hi : t0 ∈ pasch i
    · by_cases hj : t0 ∈ pasch j
      · exact Or.inl (by simp [P, keep, hi, hj])
      · exact Or.inr (by simpa [P, keep, hj] using smallP i)
    · exact Or.inl (by simpa [P, keep, hi] using smallP j)
  have noCommon (i j : Fin 4) (hij : i ≠ j) (hp : P i ⊆ P j) (w : ℕ)
      (hi : w ∈ G i) (hj : w ∈ G j) : False := by
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    have inc : support C w ∩ P i ⊆ pasch i ∩ pasch j := by
      intro p hp'
      exact Finset.mem_inter.mpr ⟨ai.1 hp', aj.1 (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hp').1, hp (Finset.mem_inter.mp hp').2⟩)⟩
    have hle := pasch_inter_le i j hij
    have hcard := Finset.card_le_card inc
    omega
  have dis (i j : Fin 4) (hij : i ≠ j) : Disjoint (G i) (G j) := by
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases comp i j with h | h
    · exact noCommon i j hij h w hi hj
    · exact noCommon j i hij.symm h w hj hi
  have hsum_sdiff := sum_pred_le_sdiff pasch (T.erase t0)
  rw [pasch_sum] at hsum_sdiff
  have hdeg_sum : ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin 4 => u ∈ pasch c)).card =
      2 * (T.erase t0).card := by
    simp [pasch_deg, mul_comm]
  rw [hdeg_sum] at hsum_sdiff
  have herase_card : (T.erase t0).card = T.card - 1 := Finset.card_erase_of_mem ht0
  by_cases hT1 : T.card = 1
  · have hbound := sum_card_disjoint_le Finset.univ G
      (fun i => (pasch i \ T.erase t0).card - 1) ((Finset.Ico 6 (6 + C.size)).erase z)
      (fun i _ j _ hij => dis i j hij)
      (fun i _ => Finset.filter_subset _ _)
      (fun i _ => hcount i)
    have hzmem : z ∈ Finset.Ico 6 (6 + C.size) := by
      rw [hlen]; exact Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
    rw [Finset.card_erase_of_mem hzmem, Nat.card_Ico, hlen] at hbound
    omega
  · have hT2 : T.card = 2 := by
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨t0, ht0⟩
      omega
    by_cases hwin : hw < 6
    · have hsingle : ∀ y : Fin 6 → Bool, y ⟨hw, hwin⟩ = false → value ⟨gl, 0⟩ y hw = false := by
        intro y hy
        have h1 := input_value ⟨gl, 0⟩ y ⟨hw, hwin⟩
        simp only at h1
        rw [h1, hy]
      have hbound := sum_card_disjoint_le Finset.univ G
        (fun i => (pasch i \ T.erase t0).card - 1) ((Finset.Ico 6 (6 + C.size)).erase z)
        (fun i _ j _ hij => dis i j hij)
        (fun i _ => Finset.filter_subset _ _)
        (fun i _ => hcount i)
      -- Use singleton T' = {⟨hw, hwin⟩} directly by recursing on T' = {⟨hw, hwin⟩}
      have hT' : ∀ y : Fin 6 → Bool,
          (∀ t ∈ ({⟨hw, hwin⟩} : Finset (Fin 6)), y t = false) → value ⟨gl, 0⟩ y hw = false := by
        intro y hy
        exact hsingle y (hy ⟨hw, hwin⟩ (Finset.mem_singleton_self _))
      -- Direct 1-element bound
      let T' : Finset (Fin 6) := {⟨hw, hwin⟩}
      let t0' : Fin 6 := ⟨hw, hwin⟩
      have hok' : ∀ i x, (t0' ∈ pasch i ∨ x t0' = false) →
          value C x (ol i) = decide (∃ v ∈ pasch i, x v = true) := by
        intro i x hcase
        have hval : value ⟨gl, ol i⟩ x (ol i) = decide (∃ v ∈ pasch i, x v = true) := hout i x
        by_cases h0 : x t0' = false
        · have hztrue : value ⟨gl, ol i⟩ x z = true := by
            rw [orig_not_eval gl i0 (ol i) hw hop hhead hlt x]
            have hf : value ⟨gl, ol i⟩ x hw = false := hsingle x h0
            simp [hf]
          rw [replC_eq gl i0 true (ol i) x hztrue (ol i), hval]
        · have hmem : t0' ∈ pasch i := hcase.resolve_right h0
          have htrue : decide (∃ v ∈ pasch i, x v = true) = true :=
            decide_eq_true ⟨t0', hmem, by simpa using h0⟩
          rw [htrue]
          exact replC_true_ge gl i0 (ol i) hgate hnot x (ol i) (hval.trans htrue)
      let P' : Fin 4 → Finset (Fin 6) := fun i => keep (pasch i) T' t0'
      let G' : Fin 4 → Finset ℕ := fun i => owned C z (P' i) (pasch i)
      have hmask' (i : Fin 4) (x : Fin 6 → Bool) (h : ∀ v, x v = true → v ∈ P' i) :
          value C x (ol i) = decide (∃ v ∈ pasch i, x v = true) := by
        apply hok' i x
        by_cases hi : t0' ∈ pasch i
        · exact Or.inl hi
        · refine Or.inr (Bool.eq_false_iff.mpr ?_)
          intro hv
          have hin := h t0' hv
          have hf : t0' ∈ (Finset.univ : Finset (Fin 6)) \ T' := by
            simpa only [P', keep, if_neg hi] using hin
          exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_singleton_self _)
      have hcount' (i : Fin 4) : (pasch i).card - 1 ≤ (G' i).card := by
        have heq : pasch i ∩ P' i = pasch i := by
          rw [inter_keep]
          simp [T', t0']
        rw [← heq]
        apply countOne C z (ol i) (P' i) (pasch i) hgood hz
        · intro p hp
          rw [hmask' i _ (fun v hv => (of_decide_eq_true hv : v = p) ▸ (Finset.mem_inter.mp hp).2)]
          exact decide_eq_true ⟨p, (Finset.mem_inter.mp hp).1, by simp⟩
        · have supp (v : Fin 6) (hv : bit (P' i \ pasch i) v = true) : v ∈ P' i :=
            (Finset.mem_sdiff.mp (show v ∈ P' i \ pasch i from of_decide_eq_true hv)).1
          rw [hmask' i (bit (P' i \ pasch i)) supp]
          apply decide_eq_false
          rintro ⟨p, hp, hb⟩
          exact (Finset.mem_sdiff.mp (show p ∈ P' i \ pasch i from of_decide_eq_true hb)).2 hp
      have comp' (i j : Fin 4) : P' i ⊆ P' j ∨ P' j ⊆ P' i := by
        by_cases hi : t0' ∈ pasch i
        · by_cases hj : t0' ∈ pasch j
          · exact Or.inl (by simp [P', keep, hi, hj])
          · exact Or.inr (by intro p hp; simp [P', keep, hi, hj, T', t0'] at hp ⊢)
        · exact Or.inl (by intro p hp; simp [P', keep, hi] at hp ⊢; split_ifs <;> simp_all [T', t0'])
      have dis' (i j : Fin 4) (hij : i ≠ j) : Disjoint (G' i) (G' j) := by
        apply Finset.disjoint_left.mpr
        intro w hi hj
        have aux (a b : Fin 4) (hab : a ≠ b) (hp : P' a ⊆ P' b)
            (ha : w ∈ G' a) (hb : w ∈ G' b) : False := by
          have ai := (Finset.mem_filter.mp ha).2
          have aj := (Finset.mem_filter.mp hb).2
          have inc : support C w ∩ P' a ⊆ pasch a ∩ pasch b := fun p hp' =>
            Finset.mem_inter.mpr ⟨ai.1 hp', aj.1 (Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hp').1, hp (Finset.mem_inter.mp hp').2⟩)⟩
          have hle := pasch_inter_le a b hab
          have hcard := Finset.card_le_card inc
          omega
        rcases comp' i j with h | h
        · exact aux i j hij h hi hj
        · exact aux j i hij.symm h hj hi
      have hbound' := sum_card_disjoint_le Finset.univ G'
        (fun i => (pasch i).card - 1) ((Finset.Ico 6 (6 + C.size)).erase z)
        (fun i _ j _ hij => dis' i j hij)
        (fun i _ => Finset.filter_subset _ _)
        (fun i _ => hcount' i)
      have hzmem : z ∈ Finset.Ico 6 (6 + C.size) := by
        rw [hlen]; exact Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
      rw [Finset.card_erase_of_mem hzmem, Nat.card_Ico, hlen, pasch_sum] at hbound'
      omega
    · have hhw_not_mem (i : Fin 4) : hw ∉ G i := by
        intro hmem
        have h2 := (Finset.mem_filter.mp hmem).2.2
        have hsub : support C hw ∩ P i ⊆ {t0} := by
          intro p hp
          have hsupp : value C (fun q => decide (q = p)) hw = true :=
            (mem_support C hw p).mp (Finset.mem_inter.mp hp).1
          rw [replC_eq_before gl i0 true _ hw hlt] at hsupp
          have hpT : p ∈ T := by
            by_contra hpnot
            have hfalse := hT (fun q => decide (q = p)) (fun t ht => by
              simp only [decide_eq_false_iff_not]
              intro heq
              exact hpnot (heq ▸ ht))
            rw [hfalse] at hsupp
            exact Bool.false_ne_true hsupp
          have hpP := (Finset.mem_inter.mp hp).2
          simp only [P, keep] at hpP
          split_ifs at hpP with hi
          · have hne := (Finset.mem_sdiff.mp hpP).2
            by_contra hpt0
            exact hne (Finset.mem_erase.mpr ⟨Finset.mem_singleton.not.mp hpt0, hpT⟩)
          · exact absurd hpT (Finset.mem_sdiff.mp hpP).2
        have hcard := Finset.card_le_card hsub
        simp at hcard
        omega
      have hbound := sum_card_disjoint_le Finset.univ G
        (fun i => (pasch i \ T.erase t0).card - 1) (((Finset.Ico 6 (6 + C.size)).erase z).erase hw)
        (fun i _ j _ hij => dis i j hij)
        (fun i _ w hwg => Finset.mem_erase.mpr ⟨fun e => hhw_not_mem i (e ▸ hwg),
          Finset.filter_subset _ _ hwg⟩)
        (fun i _ => hcount i)
      have hzmem : z ∈ Finset.Ico 6 (6 + C.size) := by
        rw [hlen]; exact Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
      have hhwmem : hw ∈ (Finset.Ico 6 (6 + C.size)).erase z := by
        refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
        rw [hlen]; exact Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
      rw [Finset.card_erase_of_mem hhwmem, Finset.card_erase_of_mem hzmem, Nat.card_Ico, hlen] at hbound
      omega

def valV (C : Circuit) (v : Fin 6) (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  value C (fun q => if q = v then true else x q) w

def supportV (C : Circuit) (v : Fin 6) (w : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter (fun p => valV C v (fun q => decide (q = p)) w = true)

lemma mem_supportV (C : Circuit) (v : Fin 6) (w : ℕ) (p : Fin 6) :
    p ∈ supportV C v w ↔ valV C v (fun q => decide (q = p)) w = true := by
  simp [supportV]

def ownedV (C : Circuit) (v : Fin 6) (S : Finset (Fin 6)) : Finset ℕ :=
  (Finset.Ico 6 (6 + C.size)).filter fun w =>
    supportV C v w ⊆ S ∧ 2 ≤ (supportV C v w).card

lemma countOneV (C : Circuit) (v : Fin 6) (o : ℕ) (S : Finset (Fin 6)) (hg : good C)
    (hvS : v ∉ S)
    (hpos : ∀ p ∈ S, valV C v (fun q => decide (q = p)) o = true)
    (hneg : valV C v (bit (Finset.univ \ S)) o = false) :
    S.card - 1 ≤ (ownedV C v S).card := by
  classical
  let G := ownedV C v S
  have hgate (w) (hw : w ∈ G) : 6 ≤ w ∧ w < 6 + C.size :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hc, hcut⟩ := cut C hg G hgate (6 + C.size) {o} (fun w _ hw => (hgate w hw).2)
  let y := bit (Finset.univ \ S)
  let yv : Fin 6 → Bool := fun q => if q = v then true else y q
  let F := B.filter fun w => valV C v y w = false
  have small (w) (hw : w ∈ F) : (supportV C v w).card ≤ 1 := by
    have hb := (Finset.mem_filter.mp hw).1
    have hv := (Finset.mem_filter.mp hw).2
    have hs : supportV C v w ⊆ S := by
      intro p hp
      by_contra h
      have hpt := (mem_supportV C v w p).mp hp
      have hmono := value_mono C hg (fun q => if q = v then true else decide (q = p)) yv (by
        intro q he
        by_cases hqv : q = v
        · simp [yv, hqv]
        · simp only [hqv, ↓reduceIte, decide_eq_true_eq] at he
          subst q
          simp [yv, y, bit, hqv, h]) w hpt
      change value C yv w = false at hv
      simp [hv] at hmono
    by_contra! hlarge
    have hgatew : 6 ≤ w ∧ w < 6 + C.size := by
      constructor
      · by_contra! hlt6
        let p0 : Fin 6 := ⟨w, hlt6⟩
        by_cases hpv : p0 = v
        · have : valV C v y w = true := by
            change value C yv p0 = true
            rw [input_value]; simp [yv, hpv]
          rw [this] at hv; exact Bool.false_ne_true hv.symm
        · have hsub : supportV C v w ⊆ {p0} := by
            intro q hq
            have hqv := (mem_supportV C v w q).mp hq
            change value C (fun r => if r = v then true else decide (r = q)) p0 = true at hqv
            rw [input_value] at hqv
            simp only [hpv, ↓reduceIte, decide_eq_true_eq] at hqv
            exact Finset.mem_singleton.mpr hqv.symm
          have hcard := Finset.card_le_card hsub
          simp at hcard; omega
      · by_contra! hge
        have hemp : supportV C v w = ∅ := by
          ext q
          simp [mem_supportV, valV, missing_value C _ w hge]
        simp [hemp] at hlarge
    exact Finset.disjoint_left.mp hd hb
      (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hgatew, hs, by omega⟩)
  have covered : S ⊆ F.biUnion (fun w => supportV C v w) := by
    intro p hp
    by_contra hn
    have hbad : value C yv o = true := by
      apply hcut (fun q => if q = v then true else decide (q = p)) yv _ o
        (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hvw
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, Bool.eq_false_iff.mpr he⟩,
        (mem_supportV C v w p).mpr hvw⟩)
    change value C yv o = false at hneg
    rw [hneg] at hbad
    exact Bool.false_ne_true hbad
  have h1 := Finset.card_le_card covered
  have h2 := Finset.card_biUnion_le_card_mul F (fun w => supportV C v w) 1 small
  have h3 := Finset.card_filter_le B (fun w => valV C v y w = false)
  change F.card ≤ B.card at h3
  have h4 := Finset.card_filter_le G (fun w => w < 6 + C.size)
  simp only [Finset.card_singleton] at hc
  change _ ≤ G.card
  omega

lemma ownedV_not_const (C : Circuit) (v : Fin 6) (S : Finset (Fin 6)) (hS : S.card < 6)
    (w : ℕ) (hw : w ∈ ownedV C v S) (b : Bool)
    (hc : ∀ x : Fin 6 → Bool, valV C v x w = b) : False := by
  have hsub := (Finset.mem_filter.mp hw).2.1
  have h2 := (Finset.mem_filter.mp hw).2.2
  cases b
  · have hemp : supportV C v w = ∅ := by
      ext p; simp [mem_supportV, hc]
    simp [hemp] at h2
  · have huniv : supportV C v w = Finset.univ := by
      ext p; simp [mem_supportV, hc]
    rw [huniv] at hsub
    have hcard := Finset.card_le_card hsub
    simp at hcard
    omega

lemma four_const_gives_eight (gl : List Gate) (ol : Fin 4 → ℕ) (i0 : Fin gl.length) (hw : ℕ)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (hop : (gl.get i0).op = GateOp.not)
    (hhead : (gl.get i0).inputs.head? = some hw)
    (hlt : hw < 6 + i0.val)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true))
    (v : Fin 6) (hfv : value ⟨gl, 0⟩ (fun q => decide (q = v)) hw = true)
    (K : Finset ℕ) (hKcard : 4 ≤ K.card)
    (hKsub : K ⊆ Finset.Ico 6 (6 + gl.length))
    (hKconst : ∀ w ∈ K, ∃ b : Bool, ∀ x : Fin 6 → Bool,
      valV (replC gl i0.val false) v x w = b) :
    8 ≤ gl.length := by
  classical
  let C0 := replC gl i0.val false
  have hlen : C0.size = gl.length := replC_size gl i0.val false
  have hgood : good C0 := replC_good gl i0 false hgate hnot
  have hagree : ∀ (x : Fin 6 → Bool) (w : ℕ),
      valV C0 v x w = value ⟨gl, 0⟩ (fun q => if q = v then true else x q) w := by
    intro x w
    have hfx : value ⟨gl, 0⟩ (fun q => if q = v then true else x q) hw = true :=
      before_mono gl i0 hgate hnot hw hlt (fun q => decide (q = v))
        (fun q => if q = v then true else x q) (fun q hq => by
          have : q = v := of_decide_eq_true hq
          simp [this]) hfv
    have hzx : value ⟨gl, 0⟩ (fun q => if q = v then true else x q) (6 + i0.val) = false := by
      rw [orig_not_eval gl i0 0 hw hop hhead hlt, hfx]; rfl
    exact replC_eq gl i0 false 0 _ hzx w
  let Av := Finset.univ.filter (fun i : Fin 4 => v ∉ pasch i)
  let G : Fin 4 → Finset ℕ := fun i => ownedV C0 v (pasch i)
  have hcount : ∀ i ∈ Av, 2 ≤ (G i).card := by
    intro i hi
    have hvnot : v ∉ pasch i := (Finset.mem_filter.mp hi).2
    have h := countOneV C0 v (ol i) (pasch i) hgood hvnot
      (fun p hp => by
        rw [hagree, value_irrel gl 0 (ol i), value_eval, hout]
        apply decide_eq_true
        refine ⟨p, hp, ?_⟩
        by_cases hpv : p = v <;> simp [hpv])
      (by
        rw [hagree, value_irrel gl 0 (ol i), value_eval, hout]
        apply decide_eq_false
        rintro ⟨p, hp, hval⟩
        by_cases hpv : p = v
        · exact hvnot (hpv ▸ hp)
        · simp only [hpv, ↓reduceIte, bit, decide_eq_true_eq, Finset.mem_sdiff,
            Finset.mem_univ, true_and] at hval
          exact hval hp)
    rw [pasch_card] at h
    exact h
  have hdis : ∀ i ∈ Av, ∀ j ∈ Av, i ≠ j → Disjoint (G i) (G j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : supportV C0 v w ⊆ pasch i ∩ pasch j :=
      Finset.subset_inter hi.1 hj.1
    have hle := pasch_inter_le i j hij
    have hcard := Finset.card_le_card hsub
    omega
  have hGsub : ∀ i ∈ Av, G i ⊆ (Finset.Ico 6 (6 + gl.length)) \ K := by
    intro i _ w hwg
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · have hm := (Finset.mem_filter.mp hwg).1
      rw [hlen] at hm; exact hm
    · intro hwK
      obtain ⟨b, hb⟩ := hKconst w hwK
      exact ownedV_not_const C0 v (pasch i) (by rw [pasch_card]; omega) w hwg b hb
  have hsum := sum_card_disjoint_le Av G (fun _ => 2) ((Finset.Ico 6 (6 + gl.length)) \ K)
    hdis hGsub hcount
  rw [Finset.sum_const, smul_eq_mul, pasch_not_deg] at hsum
  have hcard_sdiff : ((Finset.Ico 6 (6 + gl.length)) \ K).card = gl.length - K.card := by
    rw [Finset.card_sdiff_of_subset hKsub, Nat.card_Ico]
    omega
  rw [hcard_sdiff] at hsum
  omega

lemma ol_is_gate (gl : List Gate) (ol : Fin 4 → ℕ)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true))
    (i : Fin 4) : 6 ≤ ol i ∧ ol i < 6 + gl.length := by
  have hsupp : support ⟨gl, 0⟩ (ol i) = pasch i := by
    ext p
    rw [mem_support, value_irrel gl 0 (ol i), value_eval, hout]
    simp [eq_comm]
  have hcard : 2 ≤ (support (n := 6) ⟨gl, 0⟩ (ol i)).card := by
    rw [hsupp, pasch_card]; omega
  simpa [Circuit.size] using support_gate ⟨gl, 0⟩ (ol i) hcard

lemma ol_injective (gl : List Gate) (ol : Fin 4 → ℕ)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true)) :
    Function.Injective ol := by
  intro i j hij
  by_contra hne
  have hsupp (k : Fin 4) : support ⟨gl, 0⟩ (ol k) = pasch k := by
    ext p
    rw [mem_support, value_irrel gl 0 (ol k), value_eval, hout]
    simp [eq_comm]
  have heq : pasch i = pasch j := by rw [← hsupp i, ← hsupp j, hij]
  exact pasch_ne hne heq

lemma case_singleton_true (gl : List Gate) (ol : Fin 4 → ℕ) (i0 : Fin gl.length) (hw : ℕ)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (hop : (gl.get i0).op = GateOp.not)
    (hhead : (gl.get i0).inputs.head? = some hw)
    (hlt : hw < 6 + i0.val)
    (hge6 : 6 ≤ hw)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true))
    (v0 : Fin 6) (hfv0 : value ⟨gl, 0⟩ (fun q => decide (q = v0)) hw = true) :
    8 ≤ gl.length := by
  classical
  let z := 6 + i0.val
  have hz_mem : z ∈ Finset.Ico 6 (6 + gl.length) :=
    Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
  have hhw_mem : hw ∈ Finset.Ico 6 (6 + gl.length) :=
    Finset.mem_Ico.mpr ⟨hge6, by have := i0.isLt; omega⟩
  have hagree_of (v : Fin 6) (hfv : value ⟨gl, 0⟩ (fun q => decide (q = v)) hw = true)
      (x : Fin 6 → Bool) (w : ℕ) :
      valV (replC gl i0.val false) v x w =
        value ⟨gl, 0⟩ (fun q => if q = v then true else x q) w := by
    have hfx : value ⟨gl, 0⟩ (fun q => if q = v then true else x q) hw = true :=
      before_mono gl i0 hgate hnot hw hlt (fun q => decide (q = v))
        (fun q => if q = v then true else x q) (fun q hq => by
          have : q = v := of_decide_eq_true hq; simp [this]) hfv
    have hzx : value ⟨gl, 0⟩ (fun q => if q = v then true else x q) z = false := by
      rw [orig_not_eval gl i0 0 hw hop hhead hlt, hfx]; rfl
    exact replC_eq gl i0 false 0 _ hzx w
  have two_lines (v : Fin 6) : ∃ c d : Fin 4, c ≠ d ∧ v ∈ pasch c ∧ v ∈ pasch d := by
    have hcard : (Finset.univ.filter (fun i : Fin 4 => v ∈ pasch i)).card = 2 := pasch_deg v
    obtain ⟨c, d, hcd, hset⟩ := Finset.card_eq_two.mp hcard
    have hc : c ∈ Finset.univ.filter (fun i : Fin 4 => v ∈ pasch i) := by
      rw [hset]; simp
    have hd : d ∈ Finset.univ.filter (fun i : Fin 4 => v ∈ pasch i) := by
      rw [hset]; simp
    exact ⟨c, d, hcd, (Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hd).2⟩
  have make_four (v : Fin 6) (hfv : value ⟨gl, 0⟩ (fun q => decide (q = v)) hw = true)
      (c d : Fin 4) (hcd : c ≠ d) (hvc : v ∈ pasch c) (hvd : v ∈ pasch d)
      (extra : ℕ) (he_mem : extra ∈ Finset.Ico 6 (6 + gl.length))
      (he_nez : extra ≠ z) (he_nec : extra ≠ ol c) (he_ned : extra ≠ ol d)
      (he_const : ∀ x : Fin 6 → Bool, valV (replC gl i0.val false) v x extra = true) :
      8 ≤ gl.length := by
    have hzc : z ≠ ol c := by
      intro heq
      have h1 : valV (replC gl i0.val false) v (fun _ => false) z = false :=
        replC_at gl i0 false _
      have h2 : valV (replC gl i0.val false) v (fun _ => false) (ol c) = true := by
        rw [hagree_of v hfv, value_irrel gl 0 (ol c), value_eval, hout]
        exact decide_eq_true ⟨v, hvc, by simp⟩
      rw [heq] at h1; rw [h1] at h2; exact Bool.false_ne_true h2
    have hzd : z ≠ ol d := by
      intro heq
      have h1 : valV (replC gl i0.val false) v (fun _ => false) z = false :=
        replC_at gl i0 false _
      have h2 : valV (replC gl i0.val false) v (fun _ => false) (ol d) = true := by
        rw [hagree_of v hfv, value_irrel gl 0 (ol d), value_eval, hout]
        exact decide_eq_true ⟨v, hvd, by simp⟩
      rw [heq] at h1; rw [h1] at h2; exact Bool.false_ne_true h2
    have hcd_ol : ol c ≠ ol d := fun e => hcd (ol_injective gl ol hout e)
    let K : Finset ℕ := {z, ol c, ol d, extra}
    have hKcard : K.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [he_ned.symm]
      · simp [hcd_ol, he_nec.symm]
      · simp [hzc, hzd, he_nez.symm]
    refine four_const_gives_eight gl ol i0 hw hgate hnot hop hhead hlt hout v hfv K
      (by omega) ?_ ?_
    · intro w hwK
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hwK
      rcases hwK with rfl | rfl | rfl | rfl
      · exact hz_mem
      · exact Finset.mem_Ico.mpr (ol_is_gate gl ol hout c)
      · exact Finset.mem_Ico.mpr (ol_is_gate gl ol hout d)
      · exact he_mem
    · intro w hwK
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hwK
      rcases hwK with rfl | rfl | rfl | rfl
      · exact ⟨false, fun x => replC_at gl i0 false _⟩
      · exact ⟨true, fun x => by
          rw [hagree_of v hfv, value_irrel gl 0 (ol c), value_eval, hout]
          exact decide_eq_true ⟨v, hvc, by simp⟩⟩
      · exact ⟨true, fun x => by
          rw [hagree_of v hfv, value_irrel gl 0 (ol d), value_eval, hout]
          exact decide_eq_true ⟨v, hvd, by simp⟩⟩
      · exact ⟨true, he_const⟩
  obtain ⟨c, d, hcd, hvc, hvd⟩ := two_lines v0
  by_cases hhw_ol : hw = ol c ∨ hw = ol d
  · have hcase_eq : ∀ c0 : Fin 4, v0 ∈ pasch c0 → hw = ol c0 → 8 ≤ gl.length := by
      intro c0 _ hweq
      have hf_eq : ∀ x : Fin 6 → Bool,
          value ⟨gl, 0⟩ x hw = decide (∃ p ∈ pasch c0, x p = true) := by
        intro x
        rw [hweq, value_irrel gl 0 (ol c0), value_eval, hout]
      let g := gl[hw - 6]'(by have := i0.isLt; omega)
      have hg_spec := hgate g (List.getElem_mem _)
      have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hg_spec.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have := congrArg Fin.val (hnot ⟨hw - 6, by have := i0.isLt; omega⟩ h)
          simp only at this; omega
      have hgv (x : Fin 6 → Bool) :
          value ⟨gl, 0⟩ x hw =
            g.op.eval (g.inputs.map fun r => if r < hw then value ⟨gl, 0⟩ x r else false) :=
        orig_value gl 0 x hw hge6 (by have := i0.isLt; omega)
      rcases hg_op with hand | hor
      · have h0false : value ⟨gl, 0⟩ (fun _ : Fin 6 => false) hw = false := by
          rw [hf_eq]; simp
        rw [hgv, hand] at h0false
        simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq] at h0false
        obtain ⟨b, ⟨r, hr_in, rfl⟩, hr_f⟩ := h0false
        have hr_lt : r < hw := by
          by_contra hge
          have htrue : value ⟨gl, 0⟩ (fun _ : Fin 6 => true) hw = true := by
            rw [hf_eq]
            obtain ⟨p, hp⟩ := pasch_inter_nonempty c0 c0
            exact decide_eq_true ⟨p, (Finset.mem_inter.mp hp).1, rfl⟩
          rw [hgv, hand] at htrue
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at htrue
          have := htrue _ ⟨r, hr_in, rfl⟩
          simp [hge] at this
        have hr_pos : ∀ p ∈ pasch c0, value ⟨gl, 0⟩ (fun q => decide (q = p)) r = true := by
          intro p hp
          have htp : value ⟨gl, 0⟩ (fun q => decide (q = p)) hw = true := by
            rw [hf_eq]; exact decide_eq_true ⟨p, hp, by simp⟩
          rw [hgv, hand] at htp
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at htp
          have := htp _ ⟨r, hr_in, rfl⟩
          simpa [hr_lt] using this
        have hr_ge6 : 6 ≤ r := by
          have hsub : pasch c0 ⊆ support ⟨gl, 0⟩ r := fun p hp =>
            (mem_support ⟨gl, 0⟩ r p).mpr (hr_pos p hp)
          have hcard := Finset.card_le_card hsub
          rw [pasch_card] at hcard
          exact (support_gate ⟨gl, 0⟩ r (by omega)).1
        obtain ⟨p1, hp1⟩ := pasch_inter_nonempty c0 c0
        have hp1c : p1 ∈ pasch c0 := (Finset.mem_inter.mp hp1).1
        obtain ⟨c1, d1, hcd1, hvc1, hvd1⟩ := two_lines p1
        have hpick : ∃ d2 : Fin 4, c0 ≠ d2 ∧ p1 ∈ pasch d2 := by
          by_cases hcc : c0 = c1
          · exact ⟨d1, hcc ▸ hcd1, hvd1⟩
          · exact ⟨c1, hcc, hvc1⟩
        obtain ⟨d2, hcd2, hpd2⟩ := hpick
        have hr_ned2 : r ≠ ol d2 := by
          intro heq
          have hne : (pasch c0 \ pasch d2).Nonempty := by
            have h1 := Finset.card_sdiff_add_card_inter (pasch c0) (pasch d2)
            have h2 := pasch_inter_le c0 d2 hcd2
            rw [pasch_card] at h1
            exact Finset.card_pos.mp (by omega)
          obtain ⟨q, hq⟩ := hne
          have hqc := (Finset.mem_sdiff.mp hq).1
          have hqd := (Finset.mem_sdiff.mp hq).2
          have h1 := hr_pos q hqc
          rw [heq, value_irrel gl 0 (ol d2), value_eval, hout] at h1
          have h2 : decide (∃ v ∈ pasch d2, decide (v = q) = true) = false := by
            apply decide_eq_false
            rintro ⟨u, hu, heu⟩
            exact hqd ((of_decide_eq_true heu) ▸ hu)
          rw [h2] at h1; exact Bool.false_ne_true h1
        have hfp1 : value ⟨gl, 0⟩ (fun q => decide (q = p1)) hw = true := by
          rw [hf_eq]; exact decide_eq_true ⟨p1, hp1c, by simp⟩
        exact make_four p1 hfp1 c0 d2 hcd2 hp1c hpd2 r
          (Finset.mem_Ico.mpr ⟨hr_ge6, by have := i0.isLt; omega⟩)
          (by omega) (by omega) hr_ned2 (fun x => by
            rw [hagree_of p1 hfp1]
            exact before_mono gl i0 hgate hnot r (by omega) (fun q => decide (q = p1))
              (fun q => if q = p1 then true else x q) (fun q hq => by
                have : q = p1 := of_decide_eq_true hq; simp [this]) (hr_pos p1 hp1c))
      · have hcover : ∀ p ∈ pasch c0, ∃ r ∈ g.inputs.toFinset,
            r < hw ∧ value ⟨gl, 0⟩ (fun q => decide (q = p)) r = true := by
          intro p hp
          have htp : value ⟨gl, 0⟩ (fun q => decide (q = p)) hw = true := by
            rw [hf_eq]; exact decide_eq_true ⟨p, hp, by simp⟩
          rw [hgv, hor] at htp
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htp
          obtain ⟨b, ⟨r, hr_in, rfl⟩, hrb⟩ := htp
          by_cases hrlt : r < hw
          · exact ⟨r, List.mem_toFinset.mpr hr_in, hrlt, by simpa [hrlt] using hrb⟩
          · simp [hrlt] at hrb
        have hmap : pasch c0 ⊆ (g.inputs.toFinset.filter (· < hw)).biUnion
            (fun r => support ⟨gl, 0⟩ r) := by
          intro p hp
          obtain ⟨r, hrin, hrlt, hrv⟩ := hcover p hp
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hrin, hrlt⟩,
            (mem_support ⟨gl, 0⟩ r p).mpr hrv⟩
        have hbig : ∃ r ∈ g.inputs.toFinset.filter (· < hw),
            2 ≤ (pasch c0 ∩ support ⟨gl, 0⟩ r).card := by
          by_contra hall
          push_neg at hall
          have hsub : pasch c0 ⊆ (g.inputs.toFinset.filter (· < hw)).biUnion
              (fun r => pasch c0 ∩ support ⟨gl, 0⟩ r) := by
            intro p hp
            obtain ⟨r, hrin, hrlt, hrv⟩ := hcover p hp
            exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hrin, hrlt⟩,
              Finset.mem_inter.mpr ⟨hp, (mem_support ⟨gl, 0⟩ r p).mpr hrv⟩⟩
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_biUnion_le_card_mul (g.inputs.toFinset.filter (· < hw))
            (fun r => pasch c0 ∩ support ⟨gl, 0⟩ r) 1 (fun r hr => by have := hall r hr; omega)
          have h3 : (g.inputs.toFinset.filter (· < hw)).card ≤ 2 :=
            (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hg_spec.2)
          rw [pasch_card] at h1
          omega
        obtain ⟨r, hr_f, hr_card⟩ := hbig
        have hr_lt : r < hw := (Finset.mem_filter.mp hr_f).2
        have hr_ge6 : 6 ≤ r := by
          have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := pasch c0)
            (s₂ := support ⟨gl, 0⟩ r))
          exact (support_gate ⟨gl, 0⟩ r (by omega)).1
        obtain ⟨p1, hp1, p2, hp2, hp12⟩ := Finset.one_lt_card.mp (by omega : 1 < (pasch c0 ∩ support ⟨gl, 0⟩ r).card)
        have hp1c : p1 ∈ pasch c0 := (Finset.mem_inter.mp hp1).1
        have hp2c : p2 ∈ pasch c0 := (Finset.mem_inter.mp hp2).1
        have hp1r : value ⟨gl, 0⟩ (fun q => decide (q = p1)) r = true :=
          (mem_support ⟨gl, 0⟩ r p1).mp (Finset.mem_inter.mp hp1).2
        have hp2r : value ⟨gl, 0⟩ (fun q => decide (q = p2)) r = true :=
          (mem_support ⟨gl, 0⟩ r p2).mp (Finset.mem_inter.mp hp2).2
        obtain ⟨c1, d1, hcd1, hvc1, hvd1⟩ := two_lines p1
        have hpick : ∃ d2 : Fin 4, c0 ≠ d2 ∧ p1 ∈ pasch d2 := by
          by_cases hcc : c0 = c1
          · exact ⟨d1, hcc ▸ hcd1, hvd1⟩
          · exact ⟨c1, hcc, hvc1⟩
        obtain ⟨d2, hcd2, hpd2⟩ := hpick
        have hp2_not_d2 : p2 ∉ pasch d2 := by
          intro hmem
          have hsub : ({p1, p2} : Finset (Fin 6)) ⊆ pasch c0 ∩ pasch d2 := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hp1c, hpd2⟩
            · exact Finset.mem_inter.mpr ⟨hp2c, hmem⟩
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_pair hp12] at h1
          have h2 := pasch_inter_le c0 d2 hcd2
          omega
        have hr_ned2 : r ≠ ol d2 := by
          intro heq
          have h1 := hp2r
          rw [heq, value_irrel gl 0 (ol d2), value_eval, hout] at h1
          have h2 : decide (∃ v ∈ pasch d2, decide (v = p2) = true) = false := by
            apply decide_eq_false
            rintro ⟨u, hu, heu⟩
            exact hp2_not_d2 ((of_decide_eq_true heu) ▸ hu)
          rw [h2] at h1; exact Bool.false_ne_true h1
        have hfp1 : value ⟨gl, 0⟩ (fun q => decide (q = p1)) hw = true := by
          rw [hf_eq]; exact decide_eq_true ⟨p1, hp1c, by simp⟩
        exact make_four p1 hfp1 c0 d2 hcd2 hp1c hpd2 r
          (Finset.mem_Ico.mpr ⟨hr_ge6, by have := i0.isLt; omega⟩)
          (by omega) (by omega) hr_ned2 (fun x => by
            rw [hagree_of p1 hfp1]
            exact before_mono gl i0 hgate hnot r (by omega) (fun q => decide (q = p1))
              (fun q => if q = p1 then true else x q) (fun q hq => by
                have : q = p1 := of_decide_eq_true hq; simp [this]) hp1r)
    rcases hhw_ol with h | h
    · exact hcase_eq c hvc h
    · exact hcase_eq d hvd h
  · push_neg at hhw_ol
    exact make_four v0 hfv0 c d hcd hvc hvd hw hhw_mem (by omega) hhw_ol.1 hhw_ol.2 (fun x => by
      rw [hagree_of v0 hfv0]
      exact before_mono gl i0 hgate hnot hw hlt (fun q => decide (q = v0))
        (fun q => if q = v0 then true else x q) (fun q hq => by
          have : q = v0 := of_decide_eq_true hq; simp [this]) hfv0)

def hasHit (gl : List Gate) (k w : ℕ) : Prop :=
  ∃ T : Finset (Fin 6), T.card ≤ k ∧ ∀ y : Fin 6 → Bool, (∀ t ∈ T, y t = false) →
    value ⟨gl, 0⟩ y w = false

lemma hasHit_input (gl : List Gate) (w : ℕ) (hw : w < 6) : hasHit gl 1 w := by
  refine ⟨{⟨w, hw⟩}, by simp, fun y hy => ?_⟩
  have h := input_value ⟨gl, 0⟩ y ⟨w, hw⟩
  simp only at h
  rw [h]
  exact hy ⟨w, hw⟩ (Finset.mem_singleton_self _)

lemma gate_support_or_hit (gl : List Gate) (i0 : Fin gl.length)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (w : ℕ) (hw6 : 6 ≤ w) (hwz : w < 6 + i0.val)
    (hpre_hit : ∀ r, r < w → hasHit gl 1 r) :
    (∀ x : Fin 6 → Bool, value ⟨gl, 0⟩ x w = true) ∨ hasHit gl 2 w := by
  classical
  let g := gl[w - 6]'(by have := i0.isLt; omega)
  have hg_spec := hgate g (List.getElem_mem _)
  have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases hg_spec.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := congrArg Fin.val (hnot ⟨w - 6, by have := i0.isLt; omega⟩ h)
      simp only at this; omega
  have hgv (x : Fin 6 → Bool) :
      value ⟨gl, 0⟩ x w =
        g.op.eval (g.inputs.map fun r => if r < w then value ⟨gl, 0⟩ x r else false) :=
    orig_value gl 0 x w hw6 (by have := i0.isLt; omega)
  rcases hg_op with hand | hor
  · cases hlist : g.inputs with
    | nil =>
      left
      intro x
      rw [hgv, hand, hlist]; rfl
    | cons r rest =>
      right
      by_cases hrw : r < w
      · obtain ⟨T, hTc, hT⟩ := hpre_hit r hrw
        refine ⟨T, by omega, fun y hy => ?_⟩
        rw [hgv, hand, hlist]
        simp [GateOp.eval, hrw, hT y hy]
      · refine ⟨∅, by simp, fun y _ => ?_⟩
        rw [hgv, hand, hlist]
        simp [GateOp.eval, hrw]
  · right
    cases hlist : g.inputs with
    | nil =>
      refine ⟨∅, by simp, fun y _ => ?_⟩
      rw [hgv, hor, hlist]; rfl
    | cons r1 rest =>
      cases rest with
      | nil =>
        by_cases h1 : r1 < w
        · obtain ⟨T1, hT1c, hT1⟩ := hpre_hit r1 h1
          refine ⟨T1, by omega, fun y hy => ?_⟩
          rw [hgv, hor, hlist]
          simp [GateOp.eval, h1, hT1 y hy]
        · refine ⟨∅, by simp, fun y _ => ?_⟩
          rw [hgv, hor, hlist]
          simp [GateOp.eval, h1]
      | cons r2 rest2 =>
        have hnil : rest2 = [] := by
          have := hg_spec.2
          rw [hlist] at this
          cases rest2 with
          | nil => rfl
          | cons _ _ => simp at this
        subst hnil
        by_cases h1 : r1 < w
        · by_cases h2 : r2 < w
          · obtain ⟨T1, hT1c, hT1⟩ := hpre_hit r1 h1
            obtain ⟨T2, hT2c, hT2⟩ := hpre_hit r2 h2
            refine ⟨T1 ∪ T2, (Finset.card_union_le T1 T2).trans (by omega), fun y hy => ?_⟩
            rw [hgv, hor, hlist]
            have hy1 := hT1 y (fun t ht => hy t (Finset.mem_union_left _ ht))
            have hy2 := hT2 y (fun t ht => hy t (Finset.mem_union_right _ ht))
            simp [GateOp.eval, h1, h2, hy1, hy2]
          · obtain ⟨T1, hT1c, hT1⟩ := hpre_hit r1 h1
            refine ⟨T1, by omega, fun y hy => ?_⟩
            rw [hgv, hor, hlist]
            simp [GateOp.eval, h1, h2, hT1 y hy]
        · by_cases h2 : r2 < w
          · obtain ⟨T2, hT2c, hT2⟩ := hpre_hit r2 h2
            refine ⟨T2, by omega, fun y hy => ?_⟩
            rw [hgv, hor, hlist]
            simp [GateOp.eval, h1, h2, hT2 y hy]
          · refine ⟨∅, by simp, fun y _ => ?_⟩
            rw [hgv, hor, hlist]
            simp [GateOp.eval, h1, h2]

lemma gate_support_card_le_two (gl : List Gate) (i0 : Fin gl.length)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (w : ℕ) (hw6 : 6 ≤ w) (hwz : w < 6 + i0.val)
    (hpre_supp : ∀ r, r < w → (support (n := 6) ⟨gl, 0⟩ r).card ≤ 1) :
    (∀ x : Fin 6 → Bool, value ⟨gl, 0⟩ x w = true) ∨ (support (n := 6) ⟨gl, 0⟩ w).card ≤ 2 := by
  classical
  let g := gl[w - 6]'(by have := i0.isLt; omega)
  have hg_spec := hgate g (List.getElem_mem _)
  have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases hg_spec.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := congrArg Fin.val (hnot ⟨w - 6, by have := i0.isLt; omega⟩ h)
      simp only at this; omega
  have hgv (x : Fin 6 → Bool) :
      value ⟨gl, 0⟩ x w =
        g.op.eval (g.inputs.map fun r => if r < w then value ⟨gl, 0⟩ x r else false) :=
    orig_value gl 0 x w hw6 (by have := i0.isLt; omega)
  rcases hg_op with hand | hor
  · cases hlist : g.inputs with
    | nil =>
      left; intro x; rw [hgv, hand, hlist]; rfl
    | cons r rest =>
      right
      by_cases hrw : r < w
      · have hsub : support (n := 6) ⟨gl, 0⟩ w ⊆ support (n := 6) ⟨gl, 0⟩ r := by
          intro p hp
          have h1 := (mem_support ⟨gl, 0⟩ w p).mp hp
          rw [hgv, hand, hlist] at h1
          simp only [GateOp.eval, List.map_cons, List.all_cons, Bool.and_eq_true, id_eq] at h1
          exact (mem_support ⟨gl, 0⟩ r p).mpr (by simpa [hrw] using h1.1)
        exact (Finset.card_le_card hsub).trans ((hpre_supp r hrw).trans (by omega))
      · have hemp : support (n := 6) ⟨gl, 0⟩ w = ∅ := by
          ext p
          rw [mem_support, hgv, hand, hlist]
          simp [GateOp.eval, hrw]
        simp [hemp]
  · right
    have hsub : support (n := 6) ⟨gl, 0⟩ w ⊆
        (g.inputs.toFinset.filter (· < w)).biUnion (fun r => support (n := 6) ⟨gl, 0⟩ r) := by
      intro p hp
      have h1 := (mem_support ⟨gl, 0⟩ w p).mp hp
      rw [hgv, hor] at h1
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1
      obtain ⟨b, ⟨r, hrin, rfl⟩, hrb⟩ := h1
      by_cases hrw : r < w
      · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrin, hrw⟩,
          (mem_support ⟨gl, 0⟩ r p).mpr (by simpa [hrw] using hrb)⟩
      · simp [hrw] at hrb
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le_card_mul (g.inputs.toFinset.filter (· < w))
      (fun r => support ⟨gl, 0⟩ r) 1 (fun r hr => hpre_supp r (Finset.mem_filter.mp hr).2)
    have h3 : (g.inputs.toFinset.filter (· < w)).card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hg_spec.2)
    omega

lemma case_all_singletons_false (gl : List Gate) (ol : Fin 4 → ℕ) (i0 : Fin gl.length) (hw : ℕ)
    (hgate : ∀ g ∈ gl, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gl.length, (gl.get q).op = GateOp.not → q = i0)
    (hop : (gl.get i0).op = GateOp.not)
    (hhead : (gl.get i0).inputs.head? = some hw)
    (hlt : hw < 6 + i0.val)
    (hge6 : 6 ≤ hw)
    (hout : ∀ (o : Fin 4) (x : Fin 6 → Bool),
      Circuit.eval ⟨gl, ol o⟩ (List.ofFn x) = decide (∃ v ∈ pasch o, x v = true))
    (hnohit : ¬ hasHit gl 2 hw)
    (hzero : ∀ v : Fin 6, value ⟨gl, 0⟩ (fun q => decide (q = v)) hw = false) :
    8 ≤ gl.length := by
  classical
  by_contra! hle7
  let z := 6 + i0.val
  let Z0 : Finset ℕ := (Finset.Ico 6 z).filter (fun w => support (n := 6) ⟨gl, 0⟩ w = ∅)
  let O : Finset ℕ := Finset.univ.image ol
  have hOcard : O.card = 4 := by
    rw [Finset.card_image_of_injective _ (ol_injective gl ol hout)]
    simp
  have hOsub : O ⊆ Finset.Ico 6 (6 + gl.length) := by
    intro w hwO
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwO
    exact Finset.mem_Ico.mpr (ol_is_gate gl ol hout i)
  have hOsupp : ∀ w ∈ O, (support (n := 6) ⟨gl, 0⟩ w).card = 3 := by
    intro w hwO
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwO
    have hs : support ⟨gl, 0⟩ (ol i) = pasch i := by
      ext p
      rw [mem_support, value_irrel gl 0 (ol i), value_eval, hout]
      simp [eq_comm]
    rw [hs, pasch_card]
  have hhwZ0 : hw ∈ Z0 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hge6, hlt⟩, ?_⟩
    ext p; simp [mem_support, hzero]
  have hZ0pos : 1 ≤ Z0.card := Finset.card_pos.mpr ⟨hw, hhwZ0⟩
  have hZ0sub : Z0 ⊆ Finset.Ico 6 (6 + gl.length) := fun w hwZ => by
    have hm := Finset.mem_Ico.mp (Finset.mem_filter.mp hwZ).1
    exact Finset.mem_Ico.mpr ⟨hm.1, by have := i0.isLt; omega⟩
  have hzmem : z ∈ Finset.Ico 6 (6 + gl.length) :=
    Finset.mem_Ico.mpr ⟨by omega, by have := i0.isLt; omega⟩
  have hz_notO : z ∉ O := by
    intro hzO
    obtain ⟨i, _, hzi⟩ := Finset.mem_image.mp hzO
    have h0_ol : value ⟨gl, 0⟩ (fun _ : Fin 6 => false) (ol i) = false := by
      rw [value_irrel gl 0 (ol i), value_eval, hout]; simp
    have h0_hw : value ⟨gl, 0⟩ (fun _ : Fin 6 => false) hw = false := by
      by_contra htrue
      have ht : value ⟨gl, 0⟩ (fun _ : Fin 6 => false) hw = true := by simpa using htrue
      have h1 := before_mono gl i0 hgate hnot hw hlt (fun _ : Fin 6 => false) (fun q => decide (q = 0))
        (fun _ h => by simp at h) ht
      rw [hzero 0] at h1; exact Bool.false_ne_true h1
    have h0_z : value ⟨gl, 0⟩ (fun _ : Fin 6 => false) z = true := by
      rw [orig_not_eval gl i0 0 hw hop hhead hlt, h0_hw]; rfl
    rw [hzi] at h0_ol; rw [h0_z] at h0_ol; exact Bool.false_ne_true h0_ol.symm
  have hz_notZ0 : z ∉ Z0 := fun h => by
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp h).1).2; omega
  have hdis_OZ0 : Disjoint O Z0 := by
    apply Finset.disjoint_left.mpr
    intro w hwO hwZ
    have h1 := hOsupp w hwO
    have h2 := (Finset.mem_filter.mp hwZ).2
    simp [h2] at h1
  have hUcard : (insert z (O ∪ Z0)).card = 1 + 4 + Z0.card := by
    rw [Finset.card_insert_of_notMem (by simp [hz_notO, hz_notZ0]),
      Finset.card_union_of_disjoint hdis_OZ0, hOcard]
    omega
  have hUsub : insert z (O ∪ Z0) ⊆ Finset.Ico 6 (6 + gl.length) := by
    intro w hwU
    simp only [Finset.mem_insert, Finset.mem_union] at hwU
    rcases hwU with rfl | h | h
    · exact hzmem
    · exact hOsub h
    · exact hZ0sub h
  have hUle : (insert z (O ∪ Z0)).card ≤ gl.length := by
    have := Finset.card_le_card hUsub
    simpa [Nat.card_Ico] using this
  have hZ0le2 : Z0.card ≤ 2 := by omega
  let Pre : Finset ℕ := (Finset.Ico 6 z) \ Z0
  have hinput_supp (r : ℕ) (hr : r < 6) : (support (n := 6) ⟨gl, 0⟩ r).card ≤ 1 := by
    have hsub : support (n := 6) ⟨gl, 0⟩ r ⊆ {⟨r, hr⟩} := by
      intro q hq
      have h1 := (mem_support ⟨gl, 0⟩ r q).mp hq
      have h2 := input_value ⟨gl, 0⟩ (fun s => decide (s = q)) ⟨r, hr⟩
      simp only at h2
      rw [h2] at h1
      exact Finset.mem_singleton.mpr (Fin.ext (by
        have : (⟨r, hr⟩ : Fin 6) = q := of_decide_eq_true h1
        exact congrArg Fin.val this.symm))
    exact (Finset.card_le_card hsub).trans (by simp)
  by_cases hZ2 : Z0.card = 2
  · have hPre_sub_O : Pre ⊆ O := by
      intro w hwP
      by_contra hwNotO
      have hw_notZ : w ∉ Z0 := (Finset.mem_sdiff.mp hwP).2
      have hw_Ico : w ∈ Finset.Ico 6 z := (Finset.mem_sdiff.mp hwP).1
      have hw_nez : w ≠ z := by have := (Finset.mem_Ico.mp hw_Ico).2; omega
      have hsub : insert w (insert z (O ∪ Z0)) ⊆ Finset.Ico 6 (6 + gl.length) := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hw_Ico).1,
            by have := (Finset.mem_Ico.mp hw_Ico).2; have := i0.isLt; omega⟩
        · exact hUsub hu
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hw_nez, hwNotO, hw_notZ]), hUcard, Nat.card_Ico] at hcard
      omega
    have hPre_empty : Pre = ∅ := by
      by_contra hne
      have hnon : Pre.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      let w0 := Pre.min' hnon
      have hw0P : w0 ∈ Pre := Finset.min'_mem Pre hnon
      have hw0O : w0 ∈ O := hPre_sub_O hw0P
      have hw0_Ico : w0 ∈ Finset.Ico 6 z := (Finset.mem_sdiff.mp hw0P).1
      have hpre_supp : ∀ r, r < w0 → (support (n := 6) ⟨gl, 0⟩ r).card ≤ 1 := by
        intro r hr
        by_cases hr6 : r < 6
        · exact hinput_supp r hr6
        · have hrZ0 : r ∈ Z0 := by
            by_contra hrnot
            have hrP : r ∈ Pre := Finset.mem_sdiff.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by have := (Finset.mem_Ico.mp hw0_Ico).2; omega⟩, hrnot⟩
            have := Finset.min'_le Pre r hrP
            omega
          simp [(Finset.mem_filter.mp hrZ0).2]
      have hcase := gate_support_card_le_two gl i0 hgate hnot w0
        (Finset.mem_Ico.mp hw0_Ico).1 (Finset.mem_Ico.mp hw0_Ico).2 hpre_supp
      have h3 := hOsupp w0 hw0O
      rcases hcase with htrue | hle2
      · have huniv : support (n := 6) ⟨gl, 0⟩ w0 = Finset.univ := by
          ext p; simp [mem_support, htrue]
        rw [huniv] at h3; simp at h3
      · omega
    have hIco_sub_Z0 : Finset.Ico 6 z ⊆ Z0 := by
      intro w hwI
      by_contra hnotZ
      have : w ∈ Pre := Finset.mem_sdiff.mpr ⟨hwI, hnotZ⟩
      rw [hPre_empty] at this; exact Finset.notMem_empty _ this
    obtain ⟨w1, w2, hw12, hZ0eq⟩ := Finset.card_eq_two.mp hZ2
    have hmin_hit : ∀ w ∈ Z0, (∀ r, 6 ≤ r → r < w → False) → hasHit gl 1 w := by
      intro w hwZ hfirst
      have hwI := Finset.mem_Ico.mp (Finset.mem_filter.mp hwZ).1
      have hwS := (Finset.mem_filter.mp hwZ).2
      let g := gl[w - 6]'(by have := i0.isLt; omega)
      have hg_spec := hgate g (List.getElem_mem _)
      have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hg_spec.1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have := congrArg Fin.val (hnot ⟨w - 6, by have := i0.isLt; omega⟩ h)
          simp only at this; omega
      have hgv (x : Fin 6 → Bool) :
          value ⟨gl, 0⟩ x w =
            g.op.eval (g.inputs.map fun r => if r < w then value ⟨gl, 0⟩ x r else false) :=
        orig_value gl 0 x w hwI.1 (by have := i0.isLt; omega)
      rcases hg_op with hand | hor
      · cases hlist : g.inputs with
        | nil =>
          have h0 : (0 : Fin 6) ∈ support ⟨gl, 0⟩ w := by
            rw [mem_support, hgv, hand, hlist]; rfl
          rw [hwS] at h0; exact absurd h0 (Finset.notMem_empty _)
        | cons r rest =>
          by_cases hrw : r < w
          · have hr6 : r < 6 := by by_contra hge; exact hfirst r (by omega) hrw
            obtain ⟨T, hTc, hT⟩ := hasHit_input gl r hr6
            refine ⟨T, hTc, fun y hy => ?_⟩
            rw [hgv, hand, hlist]; simp [GateOp.eval, hrw, hT y hy]
          · refine ⟨∅, by simp, fun y _ => ?_⟩
            rw [hgv, hand, hlist]; simp [GateOp.eval, hrw]
      · refine ⟨∅, by simp, fun y _ => ?_⟩
        rw [hgv, hor]
        simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq]
        rintro b ⟨r, hrin, rfl⟩
        by_cases hrw : r < w
        · have hr6 : r < 6 := by by_contra hge; exact hfirst r (by omega) hrw
          have hmem : (⟨r, hr6⟩ : Fin 6) ∈ support ⟨gl, 0⟩ w := by
            rw [mem_support, hgv, hor]
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
            refine ⟨true, ⟨r, hrin, ?_⟩, rfl⟩
            have hin := input_value ⟨gl, 0⟩ (fun q => decide (q = ⟨r, hr6⟩)) ⟨r, hr6⟩
            simp only at hin
            simp [hrw, hin]
          rw [hwS] at hmem; exact absurd hmem (Finset.notMem_empty _)
        · simp [hrw]
    have hpre_hit : ∀ r, r < hw → hasHit gl 1 r := by
      intro r hr
      by_cases hr6 : r < 6
      · exact hasHit_input gl r hr6
      · have hrZ0 : r ∈ Z0 := hIco_sub_Z0 (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        refine hmin_hit r hrZ0 (fun s hs6 hsr => ?_)
        have hsZ0 : s ∈ Z0 := hIco_sub_Z0 (Finset.mem_Ico.mpr ⟨hs6, by omega⟩)
        have h3 : ({s, r, hw} : Finset ℕ) ⊆ Z0 := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> assumption
        have hcard := Finset.card_le_card h3
        rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at hcard
        omega
    rcases gate_support_or_hit gl i0 hgate hnot hw hge6 hlt hpre_hit with htrue | hhit
    · have := hzero 0; rw [htrue] at this; exact Bool.false_ne_true this.symm
    · exact hnohit hhit
  · have hZ1 : Z0.card = 1 := by omega
    have hZ0eq : Z0 = {hw} := Finset.card_eq_one.mp hZ1 |>.elim fun a ha => by
      have : hw ∈ ({a} : Finset ℕ) := ha ▸ hhwZ0
      rw [(Finset.mem_singleton.mp this).symm] at ha
      exact ha
    have hPre_nonempty_supp : ∀ r, r < hw → (support (n := 6) ⟨gl, 0⟩ r).Nonempty := by
      intro r hr
      by_cases hr6 : r < 6
      · refine ⟨⟨r, hr6⟩, ?_⟩
        rw [mem_support]
        have := input_value ⟨gl, 0⟩ (fun q => decide (q = ⟨r, hr6⟩)) ⟨r, hr6⟩
        simpa using this
      · by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hrZ0 : r ∈ Z0 := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hemp⟩
        rw [hZ0eq, Finset.mem_singleton] at hrZ0
        omega
    let g := gl[hw - 6]'(by have := i0.isLt; omega)
    have hg_spec := hgate g (List.getElem_mem _)
    have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
      rcases hg_spec.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have := congrArg Fin.val (hnot ⟨hw - 6, by have := i0.isLt; omega⟩ h)
        simp only at this; omega
    have hgv (x : Fin 6 → Bool) :
        value ⟨gl, 0⟩ x hw =
          g.op.eval (g.inputs.map fun r => if r < hw then value ⟨gl, 0⟩ x r else false) :=
      orig_value gl 0 x hw hge6 (by have := i0.isLt; omega)
    rcases hg_op with hand | hor
    · have htwo : ∃ r1 r2 : ℕ, r1 < hw ∧ r2 < hw ∧ ¬ hasHit gl 2 r1 ∧ ¬ hasHit gl 2 r2 ∧
          Disjoint (support (n := 6) ⟨gl, 0⟩ r1) (support (n := 6) ⟨gl, 0⟩ r2) := by
        cases hlist : g.inputs with
        | nil =>
          have := hzero 0
          rw [hgv, hand, hlist] at this
          simp [GateOp.eval] at this
        | cons r1 rest =>
          have h1lt : r1 < hw := by
            by_contra hge
            exact hnohit ⟨∅, by simp, fun y _ => by rw [hgv, hand, hlist]; simp [GateOp.eval, hge]⟩
          have h1nohit : ¬ hasHit gl 2 r1 := by
            intro ⟨T, hTc, hT⟩
            exact hnohit ⟨T, hTc, fun y hy => by
              rw [hgv, hand, hlist]; simp [GateOp.eval, h1lt, hT y hy]⟩
          cases rest with
          | nil =>
            obtain ⟨p, hp⟩ := hPre_nonempty_supp r1 h1lt
            have hp_hw : value ⟨gl, 0⟩ (fun q => decide (q = p)) hw = true := by
              rw [hgv, hand, hlist]
              simp [GateOp.eval, h1lt, (mem_support ⟨gl, 0⟩ r1 p).mp hp]
            rw [hzero p] at hp_hw; exact absurd hp_hw Bool.false_ne_true
          | cons r2 rest2 =>
            have hnil : rest2 = [] := by
              have := hg_spec.2
              rw [hlist] at this
              cases rest2 with
              | nil => rfl
              | cons _ _ => simp at this
            subst hnil
            have h2lt : r2 < hw := by
              by_contra hge
              exact hnohit ⟨∅, by simp, fun y _ => by rw [hgv, hand, hlist]; simp [GateOp.eval, hge]⟩
            have h2nohit : ¬ hasHit gl 2 r2 := by
              intro ⟨T, hTc, hT⟩
              exact hnohit ⟨T, hTc, fun y hy => by
                rw [hgv, hand, hlist]; simp [GateOp.eval, h2lt, hT y hy]⟩
            refine ⟨r1, r2, h1lt, h2lt, h1nohit, h2nohit, ?_⟩
            apply Finset.disjoint_left.mpr
            intro p hp1 hp2
            have hphw : value ⟨gl, 0⟩ (fun q => decide (q = p)) hw = true := by
              rw [hgv, hand, hlist]
              simp [GateOp.eval, h1lt, h2lt, (mem_support ⟨gl, 0⟩ r1 p).mp hp1,
                (mem_support ⟨gl, 0⟩ r2 p).mp hp2]
            rw [hzero p] at hphw; exact Bool.false_ne_true hphw
      obtain ⟨r1, r2, hr1lt, hr2lt, hr1nh, hr2nh, hdis12⟩ := htwo
      have hr1ge6 : 6 ≤ r1 := by
        by_contra hlt6
        obtain ⟨T, hTc, hT⟩ := hasHit_input gl r1 (by omega)
        exact hr1nh ⟨T, by omega, hT⟩
      have hr2ge6 : 6 ≤ r2 := by
        by_contra hlt6
        obtain ⟨T, hTc, hT⟩ := hasHit_input gl r2 (by omega)
        exact hr2nh ⟨T, by omega, hT⟩
      have hPre_ne : Pre.Nonempty := ⟨r1, Finset.mem_sdiff.mpr
        ⟨Finset.mem_Ico.mpr ⟨hr1ge6, by omega⟩, by rw [hZ0eq]; simp; omega⟩⟩
      let w0 := Pre.min' hPre_ne
      have hw0P : w0 ∈ Pre := Finset.min'_mem Pre hPre_ne
      have hw0_Ico : w0 ∈ Finset.Ico 6 z := (Finset.mem_sdiff.mp hw0P).1
      have hw0_lt_hw : w0 < hw := by
        have hr1P : r1 ∈ Pre := Finset.mem_sdiff.mpr
          ⟨Finset.mem_Ico.mpr ⟨hr1ge6, by omega⟩, by rw [hZ0eq]; simp; omega⟩
        have := Finset.min'_le Pre r1 hr1P
        omega
      have hw0_pre_input : ∀ r, r < w0 → r < 6 := by
        intro r hr
        by_contra hr6
        have hrnotZ0 : r ∉ Z0 := by rw [hZ0eq]; simp; omega
        have hrP : r ∈ Pre := Finset.mem_sdiff.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hrnotZ0⟩
        have := Finset.min'_le Pre r hrP
        omega
      have hw0_notO : w0 ∉ O := by
        intro hw0O
        have h3 := hOsupp w0 hw0O
        rcases gate_support_card_le_two gl i0 hgate hnot w0 (Finset.mem_Ico.mp hw0_Ico).1
          (Finset.mem_Ico.mp hw0_Ico).2 (fun r hr => hinput_supp r (hw0_pre_input r hr)) with htrue | hle2
        · have huniv : support (n := 6) ⟨gl, 0⟩ w0 = Finset.univ := by
            ext p; simp [mem_support, htrue]
          rw [huniv] at h3; simp at h3
        · omega
      have hw0_not_r : ∀ r, r < hw → ¬ hasHit gl 2 r →
          (∃ s, s < hw ∧ Disjoint (support (n := 6) ⟨gl, 0⟩ r) (support (n := 6) ⟨gl, 0⟩ s)) →
          w0 ≠ r := by
        intro r _ hrnh ⟨s, hslt, hdis_rs⟩ heq
        subst heq
        rcases gate_support_or_hit gl i0 hgate hnot w0 (Finset.mem_Ico.mp hw0_Ico).1
          (Finset.mem_Ico.mp hw0_Ico).2 (fun t ht => hasHit_input gl t (hw0_pre_input t ht)) with htrue | hhit
        · obtain ⟨p, hp⟩ := hPre_nonempty_supp s hslt
          have hpw0 : p ∈ support ⟨gl, 0⟩ w0 := (mem_support ⟨gl, 0⟩ w0 p).mpr (htrue _)
          exact Finset.disjoint_left.mp hdis_rs hpw0 hp
        · exact hrnh hhit
      have hw0_ner1 : w0 ≠ r1 := hw0_not_r r1 hr1lt hr1nh ⟨r2, hr2lt, hdis12⟩
      have hw0_ner2 : w0 ≠ r2 := hw0_not_r r2 hr2lt hr2nh ⟨r1, hr1lt, hdis12.symm⟩
      have hother_in_O : ∀ r, 6 ≤ r → r < hw → r ≠ w0 → r ∈ O := by
        intro r hr6 hrhw hrnew0
        by_contra hrnotO
        have hrnotZ0 : r ∉ Z0 := by rw [hZ0eq]; simp; omega
        have hw0notZ0 : w0 ∉ Z0 := (Finset.mem_sdiff.mp hw0P).2
        have hsub : insert r (insert w0 (insert z (O ∪ Z0))) ⊆ Finset.Ico 6 (6 + gl.length) := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact Finset.mem_Ico.mpr ⟨hr6, by have := i0.isLt; omega⟩
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hw0_Ico).1, by have := i0.isLt; omega⟩
          · exact hUsub hu
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hrnew0, hrnotO, hrnotZ0]; omega),
          Finset.card_insert_of_notMem (by simp [hw0_notO, hw0notZ0]; omega),
          hUcard, Nat.card_Ico] at hcard
        omega
      have hr1O : r1 ∈ O := hother_in_O r1 hr1ge6 hr1lt hw0_ner1.symm
      have hr2O : r2 ∈ O := hother_in_O r2 hr2ge6 hr2lt hw0_ner2.symm
      obtain ⟨i1, _, hi1⟩ := Finset.mem_image.mp hr1O
      obtain ⟨i2, _, hi2⟩ := Finset.mem_image.mp hr2O
      have hsupp_eq (k : Fin 4) : support ⟨gl, 0⟩ (ol k) = pasch k := by
        ext p
        rw [mem_support, value_irrel gl 0 (ol k), value_eval, hout]
        simp [eq_comm]
      rw [← hi1, ← hi2, hsupp_eq i1, hsupp_eq i2] at hdis12
      obtain ⟨p, hp⟩ := pasch_inter_nonempty i1 i2
      exact Finset.disjoint_left.mp hdis12 (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
    · have hex : ∃ r ∈ g.inputs, r < hw := by
        by_contra hall
        push_neg at hall
        exact hnohit ⟨∅, by simp, fun y _ => by
          rw [hgv, hor]
          simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq]
          rintro b ⟨r, hrin, rfl⟩
          have := hall r hrin
          simp [show ¬ r < hw by omega]⟩
      obtain ⟨r, hrin, hrlt⟩ := hex
      obtain ⟨p, hp⟩ := hPre_nonempty_supp r hrlt
      have hphw : value ⟨gl, 0⟩ (fun q => decide (q = p)) hw = true := by
        rw [hgv, hor]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨true, ⟨r, hrin, by simp [hrlt, (mem_support ⟨gl, 0⟩ r p).mp hp]⟩, rfl⟩
      rw [hzero p] at hphw; exact Bool.false_ne_true hphw

end PEqualNP.Outside.L_meta_1042

theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  intro hNoNot gl ol hgate hnotEx hout
  classical
  obtain ⟨ι, hι⟩ := hnotEx
  let i0 : Fin gl.length := ι 0
  have hnot : ∀ q : Fin gl.length, (gl.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0 := by
    intro q hq
    obtain ⟨k, hk⟩ := hι q hq
    have hk0 : k = 0 := Subsingleton.elim k 0
    rw [← hk, hk0]
  by_cases hop : (gl.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not
  · cases hhead : (gl.get i0).inputs.head? with
    | none =>
      let C := PEqualNP.Outside.L_meta_1042.replC gl i0.val true
      have hlen : C.gates.length = gl.length := PEqualNP.Outside.L_meta_1042.replC_size gl i0.val true
      rw [← hlen, ← PEqualNP.Outside.L_meta_1042.pasch_sum]
      refine hNoNot 6 4 PEqualNP.Outside.L_meta_1042.pasch
        PEqualNP.Outside.L_meta_1042.pasch_inter_le C.gates ol
        (PEqualNP.Outside.L_meta_1042.replC_good gl i0 true hgate hnot) ?_
      intro w x
      have hz := PEqualNP.Outside.L_meta_1042.orig_not_const_true gl i0 (ol w) hop (Or.inl hhead) x
      have heq := PEqualNP.Outside.L_meta_1042.replC_eq gl i0 true (ol w) x hz (ol w)
      exact heq.trans (hout w x)
    | some hw =>
      by_cases hlt : hw < 6 + i0.val
      · by_cases hhit : PEqualNP.Outside.L_meta_1042.hasHit gl 2 hw
        · obtain ⟨T, hTcard, hT⟩ := hhit
          by_cases hTe : T = ∅
          · let C := PEqualNP.Outside.L_meta_1042.replC gl i0.val true
            have hlen : C.gates.length = gl.length :=
              PEqualNP.Outside.L_meta_1042.replC_size gl i0.val true
            rw [← hlen, ← PEqualNP.Outside.L_meta_1042.pasch_sum]
            refine hNoNot 6 4 PEqualNP.Outside.L_meta_1042.pasch
              PEqualNP.Outside.L_meta_1042.pasch_inter_le C.gates ol
              (PEqualNP.Outside.L_meta_1042.replC_good gl i0 true hgate hnot) ?_
            intro w x
            have hf : PEqualNP.Outside.L_meta_1042.value ⟨gl, 0⟩ x hw = false :=
              hT x (by simp [hTe])
            have hz : PEqualNP.Outside.L_meta_1042.value ⟨gl, ol w⟩ x (6 + i0.val) = true := by
              rw [PEqualNP.Outside.L_meta_1042.orig_not_eval gl i0 (ol w) hw hop hhead hlt x]
              change !(PEqualNP.Outside.L_meta_1042.value ⟨gl, 0⟩ x hw) = true
              simp [hf]
            have heq := PEqualNP.Outside.L_meta_1042.replC_eq gl i0 true (ol w) x hz (ol w)
            exact heq.trans (hout w x)
          · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr hTe
            exact PEqualNP.Outside.L_meta_1042.case_hit_le_two gl ol i0 hw hgate hnot hop hhead
              hlt hout T t0 ht0 hTcard hT
        · have hge6 : 6 ≤ hw := by
            by_contra hlt6
            obtain ⟨T, hTc, hT⟩ := PEqualNP.Outside.L_meta_1042.hasHit_input gl hw (by omega)
            exact hhit ⟨T, by omega, hT⟩
          by_cases hex : ∃ v0 : Fin 6,
              PEqualNP.Outside.L_meta_1042.value ⟨gl, 0⟩ (fun q => decide (q = v0)) hw = true
          · obtain ⟨v0, hfv0⟩ := hex
            exact PEqualNP.Outside.L_meta_1042.case_singleton_true gl ol i0 hw hgate hnot hop
              hhead hlt hge6 hout v0 hfv0
          · push_neg at hex
            exact PEqualNP.Outside.L_meta_1042.case_all_singletons_false gl ol i0 hw hgate hnot
              hop hhead hlt hge6 hout hhit (fun v => Bool.eq_false_iff.mpr (hex v))
      · let C := PEqualNP.Outside.L_meta_1042.replC gl i0.val true
        have hlen : C.gates.length = gl.length := PEqualNP.Outside.L_meta_1042.replC_size gl i0.val true
        rw [← hlen, ← PEqualNP.Outside.L_meta_1042.pasch_sum]
        refine hNoNot 6 4 PEqualNP.Outside.L_meta_1042.pasch
          PEqualNP.Outside.L_meta_1042.pasch_inter_le C.gates ol
          (PEqualNP.Outside.L_meta_1042.replC_good gl i0 true hgate hnot) ?_
        intro w x
        have hz := PEqualNP.Outside.L_meta_1042.orig_not_const_true gl i0 (ol w) hop
          (Or.inr ⟨hw, hhead, by omega⟩) x
        have heq := PEqualNP.Outside.L_meta_1042.replC_eq gl i0 true (ol w) x hz (ol w)
        exact heq.trans (hout w x)
  · rw [← PEqualNP.Outside.L_meta_1042.pasch_sum]
    refine hNoNot 6 4 PEqualNP.Outside.L_meta_1042.pasch
      PEqualNP.Outside.L_meta_1042.pasch_inter_le gl ol ?_ hout
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1, h2⟩ := hgate gl[k] hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hk0 := hnot ⟨k, hk⟩ h
      have hi0not : (gl.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not := by
        rw [← hk0]; exact h
      exact absurd hi0not hop
