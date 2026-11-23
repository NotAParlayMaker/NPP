import Mathlib
import PEqualNP.Defs

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

-- Monotone fan-in-two gates.
private def Mono (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

-- At a gate wire: the AND or OR of its earlier inputs.
private lemma gate_cases {n : ℕ} (C : Circuit) (hG : Mono C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ l : List ℕ, l.length ≤ 2 ∧
      ((∀ x : Fin n → Bool, value C x w = true ↔ ∀ r ∈ l, r < w ∧ value C x r = true) ∨
       (∀ x : Fin n → Bool, value C x w = true ↔ ∃ r ∈ l, r < w ∧ value C x r = true)) := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  obtain ⟨hop, hlen⟩ := hG _ (List.getElem_mem hj)
  refine ⟨(C.gates[w - n]).inputs, hlen, ?_⟩
  rcases hop with hop | hop
  · left
    intro x
    have hv := gate_value C x w hn hw
    simp only at hv
    rw [hv, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    refine forall_congr' fun r => imp_congr_right fun _ => ?_
    by_cases h : r < w <;> simp [h]
  · right
    intro x
    have hv := gate_value C x w hn hw
    simp only at hv
    rw [hv, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    refine exists_congr fun r => and_congr_right fun _ => ?_
    by_cases h : r < w <;> simp [h]

private lemma value_mono {n : ℕ} (C : Circuit) (hG : Mono C)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨l, _, hl | hl⟩ := gate_cases C hG w (by omega) hw
      · rw [hl x, hl y]
        exact fun h r hr => ⟨(h r hr).1, ih r (h r hr).1 (h r hr).2⟩
      · rw [hl x, hl y]
        rintro ⟨r, hr, hlt, hv⟩
        exact ⟨r, hr, hlt, ih r hlt hv⟩
    · simp [missing_value C x w (by omega)]


private def ind {n m : ℕ} (y : Fin m → Finset (Fin n)) (i : Fin m) (p : Fin n) :
    Fin n → Bool := fun v => decide (v ∈ y i ∨ v = p)

-- The wire implies the OR of the set.
private def Q {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) (w : ℕ) :
    Prop :=
  ∀ x : Fin n → Bool, value C x w = true → ∃ p ∈ S i, x p = true

-- Set points on which the wire fires above the base.
private def P {n m : ℕ} (C : Circuit) (S y : Fin m → Finset (Fin n)) (i : Fin m) (w : ℕ) :
    Finset (Fin n) :=
  (S i).filter (fun p => value C (ind y i p) w = true)

open Classical in
private noncomputable def M {n m : ℕ} (C : Circuit) (S y : Fin m → Finset (Fin n))
    (i : Fin m) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun g => Q C S i g ∧ 2 ≤ (P C S y i g).card)

private lemma witness {n m : ℕ} (C : Circuit) (hG : Mono C) (S : Fin m → Finset (Fin n))
    (i : Fin m) : ∀ l : List ℕ, (∀ c ∈ l, ¬ Q C S i c) →
      ∃ z : Fin n → Bool, (∀ p ∈ S i, z p = false) ∧ ∀ c ∈ l, value C z c = true
  | [], _ => ⟨fun _ => false, by simp, by simp⟩
  | c :: l, h => by
    obtain ⟨z, hz, hzl⟩ := witness C hG S i l (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hc := h c List.mem_cons_self
    simp only [Q, not_forall, not_exists, not_and] at hc
    obtain ⟨x, hx, hxS⟩ := hc
    refine ⟨fun v => x v || z v, ?_, ?_⟩
    · intro p hp
      simp only [hz p hp, Bool.or_false]
      simpa using hxS p hp
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact value_mono C hG x _ (fun p hp => by simp [hp]) d hx
      · exact value_mono C hG z _ (fun p hp => by simp [hp]) d (hzl d hd)

private lemma big_is_gate {n m : ℕ} (C : Circuit) (S y : Fin m → Finset (Fin n))
    (hdis : ∀ i, Disjoint (y i) (S i)) (i : Fin m) (t : ℕ) (hQ : Q C S i t)
    (h2 : 2 ≤ (P C S y i t).card) : n ≤ t ∧ t < n + C.size := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
  have vp : value C (ind y i p) t = true := (Finset.mem_filter.mp hp).2
  have vq : value C (ind y i q) t = true := (Finset.mem_filter.mp hq).2
  refine ⟨?_, ?_⟩
  · by_contra hn
    push Not at hn
    let a : Fin n := ⟨t, hn⟩
    have e1 : ind y i p a = true := by rw [← input_value C (ind y i p) a]; exact vp
    have e2 : ind y i q a = true := by rw [← input_value C (ind y i q) a]; exact vq
    simp only [ind, decide_eq_true_eq] at e1 e2
    have ha : a ∈ y i := by
      rcases e1 with h | h
      · exact h
      rcases e2 with h' | h'
      · exact h'
      exact absurd (h.symm.trans h') hpq
    obtain ⟨r, hr, hxr⟩ := hQ (fun v => decide (v ∈ y i)) (by
      change value C _ (a : ℕ) = true
      rw [input_value]
      simpa using ha)
    exact Finset.disjoint_left.mp (hdis i) (by simpa using hxr) hr
  · by_contra hw
    push Not at hw
    rw [missing_value C _ t hw] at vp
    exact absurd vp (by simp)

private lemma expand {n m : ℕ} (C : Circuit) (hG : Mono C) (S y : Fin m → Finset (Fin n))
    (hdis : ∀ i, Disjoint (y i) (S i)) (i : Fin m) (t : ℕ) (hQ : Q C S i t)
    (h2 : 2 ≤ (P C S y i t).card) :
    ∃ K : Finset ℕ, K.card ≤ 2 ∧ (∀ c ∈ K, c < t ∧ Q C S i c) ∧
      P C S y i t ⊆ K.biUnion (P C S y i) := by
  obtain ⟨hn, hw⟩ := big_is_gate C S y hdis i t hQ h2
  obtain ⟨p, hp, -⟩ := Finset.one_lt_card.mp h2
  have vp : value C (ind y i p) t = true := (Finset.mem_filter.mp hp).2
  obtain ⟨l, hl2, hl | hl⟩ := gate_cases C hG t hn hw
  · have hall := (hl _).mp vp
    by_cases hex : ∃ c ∈ l, Q C S i c
    · obtain ⟨c, hcl, hcQ⟩ := hex
      refine ⟨{c}, by simp, by simpa using ⟨(hall c hcl).1, hcQ⟩, ?_⟩
      intro p' hp'
      obtain ⟨hpS, hv⟩ := Finset.mem_filter.mp hp'
      simp only [Finset.singleton_biUnion]
      exact Finset.mem_filter.mpr ⟨hpS, ((hl _).mp hv c hcl).2⟩
    · push Not at hex
      obtain ⟨z, hz, hzl⟩ := witness C hG S i l hex
      obtain ⟨r, hr, hzr⟩ := hQ z ((hl z).mpr fun c hc => ⟨(hall c hc).1, hzl c hc⟩)
      rw [hz r hr] at hzr
      exact absurd hzr (by simp)
  · refine ⟨(l.filter (· < t)).toFinset, ?_, ?_, ?_⟩
    · exact (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans hl2)
    · intro c hc
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hc
      exact ⟨hc.2, fun x hx => hQ x ((hl x).mpr ⟨c, hc.1, hc.2, hx⟩)⟩
    · intro p' hp'
      obtain ⟨hpS, hv⟩ := Finset.mem_filter.mp hp'
      obtain ⟨r, hr, hrt, hvr⟩ := (hl _).mp hv
      refine Finset.mem_biUnion.mpr ⟨r, ?_, Finset.mem_filter.mpr ⟨hpS, hvr⟩⟩
      simp [hr, hrt]

private lemma frontier {n m : ℕ} (C : Circuit) (hG : Mono C) (S y : Fin m → Finset (Fin n))
    (hdis : ∀ i, Disjoint (y i) (S i)) (i : Fin m) (t : ℕ) :
    ∀ F : Finset ℕ, (∀ w ∈ F, w < t ∧ Q C S i w) →
      (F.biUnion (P C S y i)).card ≤ F.card + (M C S y i t).card := by
  induction t with
  | zero =>
    intro F hF
    have : F = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
      have := (hF w hw).1; omega
    subst this
    simp
  | succ t ih =>
    intro F hF
    have hMsub : M C S y i t ⊆ M C S y i (t + 1) := by
      intro g hg
      simp only [M, Finset.mem_filter, Finset.mem_range] at hg ⊢
      exact ⟨by omega, hg.2⟩
    have hMle := Finset.card_le_card hMsub
    by_cases htF : t ∈ F
    · have hQt := (hF t htF).2
      have hF0 : ∀ w ∈ F.erase t, w < t ∧ Q C S i w := fun w hw => by
        obtain ⟨hne, hw⟩ := Finset.mem_erase.mp hw
        exact ⟨by have := (hF w hw).1; omega, (hF w hw).2⟩
      have hcardF := Finset.card_erase_add_one htF
      have hsplit : F.biUnion (P C S y i) ⊆
          (F.erase t).biUnion (P C S y i) ∪ P C S y i t := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases h : w = t
        · subst h; exact Finset.mem_union_right _ hpw
        · exact Finset.mem_union_left _
            (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨h, hw⟩, hpw⟩)
      by_cases h2 : 2 ≤ (P C S y i t).card
      · obtain ⟨K, hK2, hK, hPK⟩ := expand C hG S y hdis i t hQt h2
        have hF' : ∀ w ∈ F.erase t ∪ K, w < t ∧ Q C S i w := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hF0 w hw
          · exact hK w hw
        have hih := ih _ hF'
        have hsub : F.biUnion (P C S y i) ⊆ (F.erase t ∪ K).biUnion (P C S y i) := by
          refine hsplit.trans ?_
          rw [Finset.union_biUnion]
          exact Finset.union_subset_union (le_refl _) hPK
        have hM : (M C S y i (t + 1)).card = (M C S y i t).card + 1 := by
          have he : M C S y i (t + 1) = insert t (M C S y i t) := by
            ext g
            simp only [M, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
            constructor
            · rintro ⟨hg, hq⟩
              by_cases h : g = t
              · exact Or.inl h
              · exact Or.inr ⟨by omega, hq⟩
            · rintro (rfl | ⟨hg, hq⟩)
              · exact ⟨by omega, hQt, h2⟩
              · exact ⟨by omega, hq⟩
          rw [he, Finset.card_insert_of_notMem]
          simp [M]
        have hu := Finset.card_union_le (F.erase t) K
        have hs := Finset.card_le_card hsub
        omega
      · have hih := ih _ hF0
        have h1 := Finset.card_le_card hsplit
        have h2' := Finset.card_union_le ((F.erase t).biUnion (P C S y i)) (P C S y i t)
        omega
    · have hih := ih F fun w hw => ⟨by
        have := (hF w hw).1
        have : w ≠ t := fun h => htF (h ▸ hw)
        omega, (hF w hw).2⟩
      omega

private lemma share {n m : ℕ} (C : Circuit) (S y : Fin m → Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (i j : Fin m) (hij : i ≠ j)
    (g : ℕ) (hQj : Q C S j g) (h2 : 2 ≤ (P C S y i g).card) : ¬ Disjoint (y i) (S j) := by
  intro hd
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h2
  have key : ∀ r ∈ P C S y i g, r ∈ S i ∩ S j := by
    intro r hr
    obtain ⟨hrS, hv⟩ := Finset.mem_filter.mp hr
    obtain ⟨s, hs, hxs⟩ := hQj _ hv
    simp only [ind, decide_eq_true_eq] at hxs
    rcases hxs with hy | rfl
    · exact absurd hs (Finset.disjoint_left.mp hd hy)
    · exact Finset.mem_inter.mpr ⟨hrS, hs⟩
  have h1 : 1 < (S i ∩ S j).card := Finset.one_lt_card.mpr ⟨p, key p hp, q, key q hq, hpq⟩
  have := hinter i j hij
  omega

end PEqualNP.Outside.L_meta_988

open PEqualNP.Outside.L_meta_988 in
theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  classical
  intro n m D S y C o hinter hdis hG hA hB hJ
  have hG' : Mono C := hG
  let G := Finset.Ico n (n + C.size)
  let Mf : Fin m → Finset ℕ := fun i => G.filter (fun g => Q C S i g ∧ 2 ≤ (P C S y i g).card)
  have hper : ∀ i, (S i).card ≤ 1 + (Mf i).card := by
    intro i
    have hQo : Q C S i (o i) := fun x hx => hA i x hx
    have hSP : S i ⊆ P C S y i (o i) := fun p hp => Finset.mem_filter.mpr ⟨hp, hB i p hp⟩
    have hf := frontier C hG' S y hdis i (o i + 1) {o i} (by simpa using hQo)
    simp only [Finset.singleton_biUnion, Finset.card_singleton] at hf
    have hMM : M C S y i (o i + 1) ⊆ Mf i := by
      intro g hg
      simp only [M, Finset.mem_filter, Finset.mem_range] at hg
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr (big_is_gate C S y hdis i g hg.2.1 hg.2.2), hg.2⟩
    have h1 := Finset.card_le_card hSP
    have h2 := Finset.card_le_card hMM
    omega
  have hsum : ∑ i, (Mf i).card ≤ D * C.gates.length := by
    have he : ∑ i, (Mf i).card = ∑ g ∈ G,
        (Finset.univ.filter (fun i => Q C S i g ∧ 2 ≤ (P C S y i g).card)).card := by
      simp only [Mf, Finset.card_filter]
      exact Finset.sum_comm
    rw [he]
    calc _ ≤ ∑ _g ∈ G, D := Finset.sum_le_sum fun g _ => hJ _ fun i hi j hj hij =>
            share C S y hinter i j hij g (Finset.mem_filter.mp hj).2.1
              (Finset.mem_filter.mp hi).2.2
      _ = D * C.gates.length := by simp [G, Circuit.size, mul_comm]
  calc ∑ i, (S i).card ≤ ∑ i, (1 + (Mf i).card) := Finset.sum_le_sum fun i _ => hper i
    _ = m + ∑ i, (Mf i).card := by simp [Finset.sum_add_distrib]
    _ ≤ D * C.gates.length + m := by omega
