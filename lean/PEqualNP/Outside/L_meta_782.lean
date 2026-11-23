import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun p => w.getD p false)]

private abbrev run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

private lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma run_read (gs : List Gate) (w : List Bool) {p : ℕ} (hp : p < w.length) :
    (run gs w).getD p false = w.getD p false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD p false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hp

private abbrev wire (C : Circuit) {n : ℕ} (x : Fin n → Bool) (p : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD p false

private lemma wires_length (C : Circuit) {n : ℕ} (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  change (run C.gates (List.ofFn x)).length = _
  rw [run_length, List.length_ofFn, Circuit.size]

private lemma wire_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    wire C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = _
  rw [run_read _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private lemma wire_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wire C x (n + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun p =>
        if p < n + j then wire C x p else false) := by
  let w := run (C.gates.take j) (List.ofFn x)
  let g := C.gates[j]
  let tail := C.gates.drop (j + 1)
  have hw : w.length = n + j := by
    simp [w, run_length, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hgs : C.gates.take j ++ g :: tail = C.gates := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hall : C.wires (List.ofFn x) = run tail (step w g) := by
    change run C.gates (List.ofFn x) = _
    rw [← hgs]
    exact List.foldl_append
  change (C.wires (List.ofFn x)).getD (n + j) false =
    g.op.eval (g.inputs.map fun p => if p < n + j then wire C x p else false)
  rw [hall, run_read _ _ (by simp [step, hw]), step,
    List.getD_append_right _ _ _ _ (by rw [hw]), hw, Nat.sub_self]
  change g.op.eval (g.inputs.map fun p => w.getD p false) = _
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases hp : p < n + j
  · rw [ite_eq_left hp]
    change w.getD p false = (C.wires (List.ofFn x)).getD p false
    rw [hall]
    have hpw : p < w.length := by rwa [hw]
    calc
      w.getD p false = (step w g).getD p false := (List.getD_append _ _ _ _ hpw).symm
      _ = (run tail (step w g)).getD p false :=
        (run_read tail (step w g) (by simp [step, hw]; omega)).symm
  · rw [ite_eq_right hp, List.getD_eq_default _ _ (by rw [hw]; omega)]

private def predecessors (C : Circuit) (n p : ℕ) : Finset ℕ :=
  if h : n ≤ p ∧ p - n < C.gates.length then
    (C.gates[p - n]'(h.2)).inputs.toFinset.filter (· < p)
  else ∅

private lemma predecessors_lt (C : Circuit) (n p : ℕ) {q : ℕ}
    (hq : q ∈ predecessors C n p) : q < p := by
  unfold predecessors at hq
  split at hq
  · exact (Finset.mem_filter.mp hq).2
  · simp at hq

private lemma predecessors_card (C : Circuit) (n p : ℕ)
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2) :
    (predecessors C n p).card ≤ 2 := by
  unfold predecessors
  split
  · rename_i h
    exact (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (basis _ (List.getElem_mem h.2)).2.le)
  · simp

private lemma gate_imp (C : Circuit) {n p : ℕ} {x y : Fin n → Bool}
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2)
    (hn : n ≤ p) (hc : p < n + C.size)
    (hp : ∀ q ∈ predecessors C n p, wire C x q = true → wire C y q = true)
    (hx : wire C x p = true) : wire C y p = true := by
  have hj : p - n < C.gates.length := by
    change p < n + C.gates.length at hc
    omega
  have hidx : n + (p - n) = p := by omega
  have hgate (z : Fin n → Bool) :
      wire C z p = C.gates[p - n].op.eval
        (C.gates[p - n].inputs.map fun q => if q < p then wire C z q else false) := by
    simpa only [hidx] using wire_gate C z hj
  have hread (q : ℕ) (hq : q ∈ C.gates[p - n].inputs) :
      (if q < p then wire C x q else false) = true →
        (if q < p then wire C y q else false) = true := by
    by_cases h : q < p
    · simp only [ite_eq_left h]
      apply hp
      rw [predecessors, dite_eq_left ⟨hn, hj⟩]
      exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hq, h⟩
    · simp [ite_eq_right h]
  rw [hgate x] at hx
  rw [hgate y]
  rcases (basis _ (List.getElem_mem hj)).1 with h | h
  · simp only [h, GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true] at hx ⊢
    exact fun q hq => hread q hq (hx q hq)
  · simp only [h, GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true] at hx ⊢
    obtain ⟨q, hq, ht⟩ := hx
    exact ⟨q, hq, hread q hq ht⟩

private lemma wire_monotone (C : Circuit) {n : ℕ} {x y : Fin n → Bool}
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2)
    (hxy : ∀ a, x a = true → y a = true) (p : ℕ)
    (hx : wire C x p = true) : wire C y p = true := by
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    by_cases hn : p < n
    · let a : Fin n := ⟨p, hn⟩
      change wire C x a = true at hx
      change wire C y a = true
      rw [wire_input] at hx ⊢
      exact hxy a hx
    · by_cases hc : p < n + C.size
      · exact gate_imp C basis (by omega) hc
          (fun q hq => ih q (predecessors_lt C n p hq)) hx
      · have hf : wire C x p = false :=
          List.getD_eq_default _ _ (by rw [wires_length]; omega)
        cases hf.symm.trans hx

private lemma frontier (P : Finset ℕ) (dep : ℕ → Finset ℕ)
    (lower : ∀ p q, q ∈ dep p → q < p) (fan : ∀ p, (dep p).card ≤ 2)
    (b : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, p ∈ P → p < b) :
    ∃ D E : Finset ℕ, D ⊆ P ∧ (∀ p ∈ D, p < b) ∧
      Disjoint E P ∧ F ⊆ D ∪ E ∧ (∀ p ∈ D, dep p ⊆ D ∪ E) ∧
      E.card ≤ D.card + F.card := by
  induction b using Nat.strong_induction_on generalizing F with
  | ind b ih =>
    by_cases h : (F ∩ P).Nonempty
    · let p := (F ∩ P).max' h
      have hp := Finset.mem_inter.mp (Finset.max'_mem (F ∩ P) h)
      have hpb : p < b := hF p hp.1 hp.2
      let G := F.erase p ∪ dep p
      have hG : ∀ q ∈ G, q ∈ P → q < p := by
        intro q hq hqp
        rcases Finset.mem_union.mp hq with he | hd
        · obtain ⟨hne, hqF⟩ := Finset.mem_erase.mp he
          have hle : q ≤ p := (F ∩ P).le_max' q (Finset.mem_inter.mpr ⟨hqF, hqp⟩)
          exact lt_of_le_of_ne hle hne
        · exact lower _ _ hd
      obtain ⟨D, E, hDP, hDlt, hEP, hGE, hDE, hcard⟩ := ih p hpb G hG
      have hnew : p ∉ D := fun hm => (Nat.lt_irrefl p) (hDlt p hm)
      have hFG : ∀ q ∈ G, q ∈ insert p D ∪ E := by
        intro q hq
        rcases Finset.mem_union.mp (hGE hq) with hd | he
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hd)
        · exact Finset.mem_union_right _ he
      refine ⟨insert p D, E, ?_, ?_, hEP, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hp.2 hDP
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hd
        · exact hpb
        · exact (hDlt q hd).trans hpb
      · intro q hq
        by_cases he : q = p
        · subst q
          exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · exact hFG q (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hq⟩))
      · intro q hq r hr
        rcases Finset.mem_insert.mp hq with rfl | hd
        · exact hFG r (Finset.mem_union_right _ hr)
        · rcases Finset.mem_union.mp (hDE q hd hr) with hm | hm
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hm)
          · exact Finset.mem_union_right _ hm
      · have hGcard := Finset.card_union_le (F.erase p) (dep p)
        have hErase : (F.erase p).card = F.card - 1 := Finset.card_erase_of_mem hp.1
        have hPos := Finset.card_pos.mpr ⟨p, hp.1⟩
        rw [Finset.card_insert_of_notMem hnew]
        have hfan := fan p
        change E.card ≤ D.card + G.card at hcard
        change G.card ≤ (F.erase p).card + (dep p).card at hGcard
        omega
    · refine ⟨∅, F, by simp, by simp, ?_, by simp, by simp, by simp⟩
      exact Finset.disjoint_left.mpr fun p hp hpp => h ⟨p, Finset.mem_inter.mpr ⟨hp, hpp⟩⟩

private abbrev single {n : ℕ} (a : Fin n) (b : Fin n) : Bool :=
  decide (b = a)

private def accepted (C : Circuit) (n p : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => wire C (single a) p = true)

private lemma mem_accepted (C : Circuit) {n p : ℕ} {a : Fin n} :
    a ∈ accepted C n p ↔ wire C (single a) p = true := by
  simp [accepted]

private def privateGates (C : Circuit) {n : ℕ} (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter (fun p =>
    accepted C n p ⊆ S ∧ 2 ≤ (accepted C n p).card)

private lemma mem_privateGates (C : Circuit) {n p : ℕ} {S : Finset (Fin n)} :
    p ∈ privateGates C S ↔
      (n ≤ p ∧ p < n + C.size) ∧ accepted C n p ⊆ S ∧
        2 ≤ (accepted C n p).card := by
  simp only [privateGates, Finset.mem_filter, Finset.mem_Ico]

private lemma private_of_accepted (C : Circuit) {n p : ℕ} {S : Finset (Fin n)}
    (hS : accepted C n p ⊆ S) (hcard : 2 ≤ (accepted C n p).card) :
    p ∈ privateGates C S := by
  refine (mem_privateGates C).mpr ⟨⟨?_, ?_⟩, hS, hcard⟩
  · by_contra! hn
    let a : Fin n := ⟨p, hn⟩
    have hsub : accepted C n p ⊆ {a} := by
      intro b hb
      have ht := (mem_accepted C).mp hb
      change wire C (single b) a = true at ht
      rw [wire_input] at ht
      exact Finset.mem_singleton.mpr (of_decide_eq_true ht).symm
    have hle := Finset.card_le_card hsub
    simp at hle
    omega
  · by_contra! hc
    have hempty : accepted C n p = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ht := (mem_accepted C).mp ha
      have hf : wire C (single a) p = false :=
        List.getD_eq_default _ _ (by rwa [wires_length])
      cases hf.symm.trans ht
    simp [hempty] at hcard

private lemma private_disjoint (C : Circuit) {n : ℕ} {S T : Finset (Fin n)}
    (hST : (S ∩ T).card ≤ 1) :
    Disjoint (privateGates C S) (privateGates C T) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hpS hpT
  obtain ⟨_, hS, hcard⟩ := (mem_privateGates C).mp hpS
  obtain ⟨_, hT, _⟩ := (mem_privateGates C).mp hpT
  have hle := Finset.card_le_card (Finset.subset_inter hS hT)
  omega

private lemma closure_imp (C : Circuit) {n : ℕ} {x y : Fin n → Bool}
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2)
    (S : Finset (Fin n)) (D E : Finset ℕ) (hD : D ⊆ privateGates C S)
    (hdep : ∀ p ∈ D, predecessors C n p ⊆ D ∪ E)
    (hE : ∀ p ∈ E, wire C x p = true → wire C y p = true)
    (p : ℕ) (hp : p ∈ D ∪ E) (hx : wire C x p = true) : wire C y p = true := by
  induction p using Nat.strong_induction_on with
  | ind p ih =>
    rcases Finset.mem_union.mp hp with hd | he
    · obtain ⟨⟨hn, hc⟩, _⟩ := (mem_privateGates C).mp (hD hd)
      exact gate_imp C basis hn hc
        (fun q hq => ih q (predecessors_lt C n p hq) (hdep p hd hq)) hx
    · exact hE p he hx

private lemma private_lower_bound (C : Circuit) {n k c o : ℕ} (S : Finset (Fin n))
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2)
    (hS : accepted C n o ⊆ S) (h2 : 2 ≤ (accepted C n o).card)
    (promise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun a => x a = true)).card ≤ k →
      (∀ a ∈ S, x a = false) → wire C x o = false)
    (hck : c ≤ k) (hlarge : c + 1 ≤ (accepted C n o).card) :
    c ≤ (privateGates C S).card := by
  classical
  by_contra! hsmall
  let P := privateGates C S
  have hoP : o ∈ P := private_of_accepted C hS h2
  obtain ⟨D, E, hD, _, hE, hroot, hdep, hcard⟩ :=
    frontier P (predecessors C n) (fun p q => predecessors_lt C n p (q := q))
      (fun p => predecessors_card C n p basis) (o + 1) {o}
      (by simp)
  have ho : o ∈ D := by
    rcases Finset.mem_union.mp (hroot (Finset.mem_singleton_self o)) with hd | he
    · exact hd
    · exact (Finset.disjoint_left.mp hE he hoP).elim
  have hEc : E.card ≤ c := by
    have hDc := Finset.card_le_card hD
    simp only [Finset.card_singleton] at hcard
    change D.card ≤ (privateGates C S).card at hDc
    omega
  let small := E.filter (fun p => accepted C n p ⊆ S)
  let bad := E.filter (fun p => ¬ accepted C n p ⊆ S)
  have pick_exists (p : {p // p ∈ bad}) : ∃ a ∈ accepted C n p.val, a ∉ S :=
    Finset.not_subset.mp (Finset.mem_filter.mp p.property).2
  let pick (p : {p // p ∈ bad}) := Classical.choose (pick_exists p)
  let test := bad.attach.image pick
  let x (a : Fin n) := decide (a ∈ test)
  have htest : (Finset.univ.filter (fun a => x a = true)).card ≤ k := by
    have hx : Finset.univ.filter (fun a => x a = true) = test := by
      ext a
      simp [x]
    rw [hx]
    calc
      test.card ≤ bad.attach.card := Finset.card_image_le
      _ = bad.card := Finset.card_attach
      _ ≤ E.card := Finset.card_filter_le _ _
      _ ≤ k := hEc.trans hck
  have hout : ∀ a ∈ S, x a = false := by
    intro a ha
    suffices a ∉ test by simp [x, this]
    intro ht
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ht
    apply (Classical.choose_spec (pick_exists p)).2
    change pick p ∈ S
    rwa [hp]
  have hbad (p : ℕ) (hp : p ∈ bad) : wire C x p = true := by
    let w : {p // p ∈ bad} := ⟨p, hp⟩
    have ht : pick w ∈ test :=
      Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩
    apply wire_monotone C basis _ p
      ((mem_accepted C).mp (Classical.choose_spec (pick_exists w)).1)
    intro a ha
    have he : a = pick w := of_decide_eq_true ha
    simp [he, x, ht]
  have hcover : accepted C n o ⊆ small.biUnion (accepted C n) := by
    intro a ha
    by_contra hnot
    have hfront (p : ℕ) (hp : p ∈ E) (hw : wire C (single a) p = true) :
        wire C x p = true := by
      by_cases hsub : accepted C n p ⊆ S
      · exact (hnot (Finset.mem_biUnion.mpr
          ⟨p, Finset.mem_filter.mpr ⟨hp, hsub⟩, (mem_accepted C).mpr hw⟩)).elim
      · exact hbad p (Finset.mem_filter.mpr ⟨hp, hsub⟩)
    have hx := closure_imp C basis S D E hD hdep hfront o
      (Finset.mem_union_left _ ho) ((mem_accepted C).mp ha)
    cases (promise x htest hout).symm.trans hx
  have hexit (p : ℕ) (hp : p ∈ small) : (accepted C n p).card ≤ 1 := by
    obtain ⟨hpE, hpS⟩ := Finset.mem_filter.mp hp
    by_contra! hp2
    exact Finset.disjoint_left.mp hE hpE
      (private_of_accepted C hpS (by omega))
  have hcount : (accepted C n o).card ≤ E.card := by
    calc
      (accepted C n o).card ≤ (small.biUnion (accepted C n)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ p ∈ small, (accepted C n p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ small, 1 := Finset.sum_le_sum hexit
      _ = small.card := by simp
      _ ≤ E.card := Finset.card_filter_le _ _
  omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 :
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
  (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n =>
    (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
  (∀ (i : Fin m) (p : Fin n),
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) →
  (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
    (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
  (∀ i : Fin m, c i ≤ k) →
  (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n =>
    (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) →
  ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hST h2 basis hS promise hck hlarge
  let P (i : Fin m) := L_meta_782.privateGates C (S i)
  have hlocal (i : Fin m) : c i ≤ (P i).card :=
    L_meta_782.private_lower_bound C (S i) basis
      (fun _ ha => hS i _ ((L_meta_782.mem_accepted C).mp ha))
      (h2 i) (promise i) (hck i) (hlarge i)
  have hdisj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact L_meta_782.private_disjoint C (hST i j hij)
  have hsub : Finset.univ.biUnion P ⊆ Finset.Ico n (n + C.size) := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_Ico.mpr ((L_meta_782.mem_privateGates C).mp hi).1
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (P i).card := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card hsub
    _ = C.size := by simp
