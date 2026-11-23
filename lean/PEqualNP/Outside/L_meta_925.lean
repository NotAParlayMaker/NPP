import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

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

private lemma gate_branch (C : Circuit) {n p : ℕ} {x : Fin n → Bool}
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hn : n ≤ p) (hc : p < n + C.size) (hx : wire C x p = true) :
    ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ r ∈ D, r < p ∧ wire C x r = true) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ D, wire C y r = true) → wire C y p = true := by
  have hj : p - n < C.gates.length := by
    change p < n + C.gates.length at hc
    omega
  have hidx : n + (p - n) = p := by omega
  have hgate (z : Fin n → Bool) :
      wire C z p = C.gates[p - n].op.eval
        (C.gates[p - n].inputs.map fun r => if r < p then wire C z r else false) := by
    simpa only [hidx] using wire_gate C z hj
  have hbasis := basis _ (List.getElem_mem hj)
  rw [hgate x] at hx
  rcases hbasis.1 with h | h
  · simp only [h, GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true] at hx
    have hchild (r : ℕ) (hr : r ∈ C.gates[p - n].inputs) :
        r < p ∧ wire C x r = true := by
      have ht := hx r hr
      split at ht <;> simp_all
    refine ⟨C.gates[p - n].inputs.toFinset,
      (List.toFinset_card_le _).trans hbasis.2, ?_, ?_⟩
    · exact fun r hr => hchild r (List.mem_toFinset.mp hr)
    · intro y hy
      rw [hgate y]
      simp only [h, GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true]
      intro r hr
      rw [ite_eq_left (hchild r hr).1]
      exact hy r (List.mem_toFinset.mpr hr)
  · simp only [h, GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true] at hx
    obtain ⟨r, hr, ht⟩ := hx
    have hchild : r < p ∧ wire C x r = true := by
      split at ht <;> simp_all
    refine ⟨{r}, by simp, by simpa, ?_⟩
    intro y hy
    rw [hgate y]
    simp only [h, GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true]
    exact ⟨r, hr, by simpa [hchild.1] using hy r (Finset.mem_singleton_self r)⟩

private lemma wire_monotone (C : Circuit) {n : ℕ} {x y : Fin n → Bool}
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
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
      · obtain ⟨D, _, hD, hall⟩ := gate_branch C basis (by omega) hc hx
        exact hall y (fun r hr => ih r (hD r hr).1 (hD r hr).2)
      · have hf : wire C x p = false :=
          List.getD_eq_default _ _ (by rw [wires_length]; omega)
        cases hf.symm.trans hx

private lemma frontier (P : Finset ℕ) (dep : ℕ → Finset ℕ) (live : ℕ → Prop)
    (lower : ∀ p r, r ∈ dep p → r < p) (fan : ∀ p, (dep p).card ≤ 2)
    (child : ∀ p r, r ∈ dep p → live r)
    (b : ℕ) (F : Finset ℕ) (hF : ∀ p ∈ F, p ∈ P → p < b)
    (hLive : ∀ p ∈ F, live p) :
    ∃ D E : Finset ℕ, D ⊆ P ∧ (∀ p ∈ D, p < b) ∧
      Disjoint E P ∧ F ⊆ D ∪ E ∧ (∀ p ∈ D, dep p ⊆ D ∪ E) ∧
      E.card ≤ D.card + F.card ∧ (∀ p ∈ E, live p) := by
  induction b using Nat.strong_induction_on generalizing F with
  | ind b ih =>
    by_cases h : (F ∩ P).Nonempty
    · let p := (F ∩ P).max' h
      have hp := Finset.mem_inter.mp (Finset.max'_mem (F ∩ P) h)
      have hpb : p < b := hF p hp.1 hp.2
      let G := F.erase p ∪ dep p
      have hG : ∀ r ∈ G, r ∈ P → r < p := by
        intro r hr hrp
        rcases Finset.mem_union.mp hr with he | hd
        · obtain ⟨hne, hrF⟩ := Finset.mem_erase.mp he
          have hle : r ≤ p := (F ∩ P).le_max' r (Finset.mem_inter.mpr ⟨hrF, hrp⟩)
          exact lt_of_le_of_ne hle hne
        · exact lower _ _ hd
      have hGLive : ∀ r ∈ G, live r := by
        intro r hr
        rcases Finset.mem_union.mp hr with he | hd
        · exact hLive r (Finset.mem_of_mem_erase he)
        · exact child p r hd
      obtain ⟨D, E, hDP, hDlt, hEP, hGE, hDE, hcard, hELive⟩ := ih p hpb G hG hGLive
      have hnew : p ∉ D := fun hm => (Nat.lt_irrefl p) (hDlt p hm)
      have hsub : D ∪ E ⊆ insert p D ∪ E :=
        Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
      refine ⟨insert p D, E, Finset.insert_subset hp.2 hDP, ?_, hEP, ?_, ?_, ?_, hELive⟩
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hd
        · exact hpb
        · exact (hDlt r hd).trans hpb
      · intro r hr
        by_cases he : r = p
        · subst r
          exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · exact hsub (hGE (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hr⟩)))
      · intro r hr s hs
        rcases Finset.mem_insert.mp hr with rfl | hd
        · exact hsub (hGE (Finset.mem_union_right _ hs))
        · exact hsub (hDE r hd hs)
      · have hGcard := Finset.card_union_le (F.erase p) (dep p)
        have hErase : (F.erase p).card + 1 = F.card := Finset.card_erase_add_one hp.1
        rw [Finset.card_insert_of_notMem hnew]
        have hfan := fan p
        change E.card ≤ D.card + G.card at hcard
        change G.card ≤ (F.erase p).card + (dep p).card at hGcard
        omega
    · refine ⟨∅, F, by simp, by simp, ?_, by simp, by simp, by simp, hLive⟩
      exact Finset.disjoint_left.mpr fun p hp hpp => h ⟨p, Finset.mem_inter.mpr ⟨hp, hpp⟩⟩

private abbrev bits {n : ℕ} (T : Finset (Fin n)) (a : Fin n) : Bool :=
  decide (a ∈ T)

private lemma true_support {n : ℕ} (T : Finset (Fin n)) :
    Finset.univ.filter (fun a => bits T a = true) = T := by
  ext a
  simp

private def specific {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) (p : ℕ) : Prop :=
  wire C (bits (S w)) p = true ∧ ∀ v, v ≠ w → wire C (bits (S v)) p = false

private noncomputable def specificGates {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (w : Fin m) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (specific C S w)

private lemma mem_specificGates {n m p : ℕ} {C : Circuit} {S : Fin m → Finset (Fin n)}
    {w : Fin m} :
    p ∈ specificGates C S w ↔ (n ≤ p ∧ p < n + C.size) ∧ specific C S w p := by
  classical
  simp only [specificGates, Finset.mem_filter, Finset.mem_Ico]

private lemma drop_witness {n m p : ℕ} {C : Circuit} {S : Fin m → Finset (Fin n)}
    {w : Fin m} (hlive : wire C (bits (S w)) p = true)
    (hout : p ∉ specificGates C S w) :
    ∃ T : Finset (Fin n), wire C (bits T) p = true ∧
      (T.card ≤ 1 ∨ ∃ v, v ≠ w ∧ T = S v) := by
  by_cases hn : p < n
  · let a : Fin n := ⟨p, hn⟩
    refine ⟨{a}, ?_, Or.inl (by simp)⟩
    change wire C (bits {a}) a = true
    rw [wire_input]
    simp
  have hc : p < n + C.size := by
    by_contra! h
    have hf : wire C (bits (S w)) p = false :=
      List.getD_eq_default _ _ (by rwa [wires_length])
    cases hf.symm.trans hlive
  have hnot : ¬ ∀ v, v ≠ w → wire C (bits (S v)) p = false := by
    intro h
    exact hout (mem_specificGates.mpr ⟨⟨by omega, hc⟩, hlive, h⟩)
  push Not at hnot
  obtain ⟨v, hv, ht⟩ := hnot
  exact ⟨S v, by simpa using ht, Or.inr ⟨v, hv, rfl⟩⟩

private lemma union_budget {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ v, (S v).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hq : 2 ≤ q) (w : Fin m) (E : Finset ℕ) (T : ℕ → Finset (Fin n))
    (hT : ∀ p ∈ E, (T p).card ≤ 1 ∨ ∃ v, v ≠ w ∧ T p = S v) :
    (E.biUnion T).card ≤ E.card * q + 1 ∧
      (S w ∩ E.biUnion T).card ≤ E.card := by
  constructor
  · by_cases h : ∃ p ∈ E, ∃ v, T p = S v
    · obtain ⟨p, hp, v, hv⟩ := h
      have hdiff (r : ℕ) (hr : r ∈ E.erase p) : (T r \ S v).card ≤ q := by
        rcases hT r (Finset.mem_of_mem_erase hr) with hsmall | ⟨u, _, hu⟩
        · exact (Finset.card_le_card Finset.sdiff_subset).trans (hsmall.trans (by omega))
        · rw [hu]
          by_cases he : u = v
          · simp [he]
          · have hs := hsize u
            have hm := hmeet u v he
            have hd := Finset.card_inter_add_card_sdiff (S u) (S v)
            omega
      have hsub : E.biUnion T ⊆ S v ∪ (E.erase p).biUnion (fun r => T r \ S v) := by
        intro a ha
        by_cases hav : a ∈ S v
        · exact Finset.mem_union_left _ hav
        · obtain ⟨r, hr, hat⟩ := Finset.mem_biUnion.mp ha
          have hne : r ≠ p := by
            rintro rfl
            exact hav (hv ▸ hat)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨r, Finset.mem_erase.mpr ⟨hne, hr⟩, Finset.mem_sdiff.mpr ⟨hat, hav⟩⟩)
      calc
        (E.biUnion T).card ≤ (S v ∪ (E.erase p).biUnion (fun r => T r \ S v)).card :=
          Finset.card_le_card hsub
        _ ≤ (S v).card + ((E.erase p).biUnion (fun r => T r \ S v)).card :=
          Finset.card_union_le _ _
        _ ≤ (S v).card + ∑ r ∈ E.erase p, (T r \ S v).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ (S v).card + ∑ _r ∈ E.erase p, q :=
          Nat.add_le_add_left (Finset.sum_le_sum hdiff) _
        _ = E.card * q + 1 := by
          rw [hsize, Finset.sum_const, Nat.nsmul_eq_mul,
            ← Finset.card_erase_add_one hp, Nat.add_mul]
          omega
    · calc
        (E.biUnion T).card ≤ ∑ p ∈ E, (T p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ E, q := by
          apply Finset.sum_le_sum
          intro p hp
          rcases hT p hp with hsmall | ⟨v, _, hv⟩
          · omega
          · exact (h ⟨p, hp, v, hv⟩).elim
        _ ≤ E.card * q + 1 := by simp
  · have hsub : S w ∩ E.biUnion T ⊆ E.biUnion (fun p => S w ∩ T p) := by
      intro a ha
      obtain ⟨haw, haE⟩ := Finset.mem_inter.mp ha
      obtain ⟨p, hp, hpa⟩ := Finset.mem_biUnion.mp haE
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_inter.mpr ⟨haw, hpa⟩⟩
    calc
      (S w ∩ E.biUnion T).card ≤ (E.biUnion (fun p => S w ∩ T p)).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ p ∈ E, (S w ∩ T p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ E, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        rcases hT p hp with hsmall | ⟨v, hv, he⟩
        · exact (Finset.card_le_card Finset.inter_subset_right).trans hsmall
        · rw [he, hmeet w v (Ne.symm hv)]
      _ = E.card := by simp

private lemma local_bound {q n m K c : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (w : Fin m) (o : ℕ)
    (hq : 2 ≤ q) (hsize : ∀ v, (S v).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (basis : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (promise : ∀ T : Finset (Fin n), T.card ≤ K →
      (wire C (bits T) o = true ↔ S w ⊆ T))
    (hc : c ≤ q) (hck : c * q < K) : c ≤ (specificGates C S w).card := by
  classical
  by_contra! hsmall
  have hqK : q + 1 ≤ K := by
    have hqc := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [Nat.one_mul] at hqc
    omega
  have ho : wire C (bits (S w)) o = true :=
    (promise _ (by rw [hsize]; exact hqK)).mpr (Finset.Subset.refl _)
  let P := specificGates C S w
  let live (p : ℕ) := wire C (bits (S w)) p = true
  have branch (p : ℕ) (hp : p ∈ P) :
      ∃ D : Finset ℕ, D.card ≤ 2 ∧ (∀ r ∈ D, r < p ∧ live r) ∧
        ∀ T : Finset (Fin n), (∀ r ∈ D, wire C (bits T) r = true) →
          wire C (bits T) p = true := by
    obtain ⟨⟨hn, hl⟩, hx, _⟩ := mem_specificGates.mp hp
    obtain ⟨D, hcard, hchild, hvalid⟩ := gate_branch C basis hn hl hx
    exact ⟨D, hcard, hchild, fun T => hvalid (bits T)⟩
  let dep (p : ℕ) := if hp : p ∈ P then Classical.choose (branch p hp) else ∅
  have dep_spec (p : ℕ) (hp : p ∈ P) :
      (dep p).card ≤ 2 ∧ (∀ r ∈ dep p, r < p ∧ live r) ∧
        ∀ T : Finset (Fin n), (∀ r ∈ dep p, wire C (bits T) r = true) →
          wire C (bits T) p = true := by
    simpa only [dep, dite_eq_left hp] using Classical.choose_spec (branch p hp)
  have dep_card (p : ℕ) : (dep p).card ≤ 2 := by
    by_cases hp : p ∈ P
    · exact (dep_spec p hp).1
    · simp [dep, hp]
  have dep_live (p r : ℕ) (hr : r ∈ dep p) : r < p ∧ live r := by
    by_cases hp : p ∈ P
    · exact (dep_spec p hp).2.1 r hr
    · simp [dep, hp] at hr
  obtain ⟨D, E, hD, _, hE, hroot, hdep, hcard, hLive⟩ :=
    frontier P dep live (fun p r h => (dep_live p r h).1) dep_card
      (fun p r h => (dep_live p r h).2) (o + 1) {o} (by simp)
      (fun p hp => (Finset.mem_singleton.mp hp).symm ▸ ho)
  have hEc : E.card ≤ c := by
    have hDP : D.card ≤ (specificGates C S w).card := Finset.card_le_card hD
    simp only [Finset.card_singleton] at hcard
    omega
  have pick_exists (p : ℕ) (hp : p ∈ E) :
      ∃ T : Finset (Fin n), wire C (bits T) p = true ∧
        (T.card ≤ 1 ∨ ∃ v, v ≠ w ∧ T = S v) :=
    drop_witness (hLive p hp) (fun h => Finset.disjoint_left.mp hE hp h)
  let pick (p : ℕ) := if hp : p ∈ E then Classical.choose (pick_exists p hp) else ∅
  have pick_spec (p : ℕ) (hp : p ∈ E) :
      wire C (bits (pick p)) p = true ∧
        ((pick p).card ≤ 1 ∨ ∃ v, v ≠ w ∧ pick p = S v) := by
    simpa only [pick, dite_eq_left hp] using Classical.choose_spec (pick_exists p hp)
  let T := E.biUnion pick
  have hbudget := union_budget S hsize hmeet hq w E pick (fun p hp => (pick_spec p hp).2)
  have hTK : T.card ≤ K :=
    hbudget.1.trans (Nat.succ_le_of_lt ((Nat.mul_le_mul_right q hEc).trans_lt hck))
  have hwire (p : ℕ) (hp : p ∈ D ∪ E) : wire C (bits T) p = true := by
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      rcases Finset.mem_union.mp hp with hd | he
      · have hpP := hD hd
        apply (dep_spec p hpP).2.2 T
        exact fun r hr => ih r ((dep_live p r hr).1) (hdep p hd hr)
      · apply wire_monotone C basis _ p (pick_spec p he).1
        intro a ha
        exact decide_eq_true (Finset.mem_biUnion.mpr ⟨p, he, of_decide_eq_true ha⟩)
  have hsub := (promise T hTK).mp (hwire o (hroot (Finset.mem_singleton_self o)))
  have hle : (S w).card ≤ E.card :=
    (Finset.card_le_card (Finset.subset_inter (Finset.Subset.refl _) hsub)).trans hbudget.2
  rw [hsize] at hle
  omega

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q →
      (∀ i : Fin m, (S i).card = q + 1) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ (w : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
          decide (∀ v ∈ S w, x v = true)) →
      ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hmeet gates out basis promise c hc hck
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  let P (w : Fin m) := L_meta_925.specificGates C S w
  have hlocal (w : Fin m) : c ≤ (P w).card := by
    apply L_meta_925.local_bound C S w (out w) hq hsize hmeet basis _ hc hck
    intro T hT
    have h := promise w (L_meta_925.bits T) (by rwa [L_meta_925.true_support])
    change L_meta_925.wire C (L_meta_925.bits T) (out w) = _ at h
    rw [h, decide_eq_true_eq]
    simp only [L_meta_925.bits, decide_eq_true_eq]
    rfl
  have hdisj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro p hi hj
    have hf := (L_meta_925.mem_specificGates.mp hi).2.2 j (Ne.symm hij)
    have ht := (L_meta_925.mem_specificGates.mp hj).2.1
    cases hf.symm.trans ht
  have hsub : Finset.univ.biUnion P ⊆ Finset.Ico n (n + C.size) := by
    intro p hp
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_Ico.mpr (L_meta_925.mem_specificGates.mp hw).1
  calc
    m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (P w).card := Finset.sum_le_sum (fun w _ => hlocal w)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card hsub
    _ = gates.length := by simp [C, PEqualNP.CircuitLowerBounds.Circuit.size]
