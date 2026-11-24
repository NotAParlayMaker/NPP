import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4659

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

lemma run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp [run, Circuit.wires]

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, Circuit.wires]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run, Circuit.wires]
  | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

lemma getD_outside {α : Type*} (xs : List α) (k : ℕ) (val : α) (hk : xs.length ≤ k) :
    xs.getD k val = val := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
  rfl

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [run_length, List.length_append]; omega),
      ← List.getD_eq_getElem?_getD, ih]

lemma input_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  have h := run_prefix [] C.gates (List.ofFn x) i.val (by simp)
  change (C.wires (List.ofFn x)).getD i.val false = (List.ofFn x).getD i.val false at h
  rw [h, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma wire_gate (C : Circuit) (x : List Bool) (j : Fin C.size) :
    (C.wires x).getD (x.length + j.val) false =
      (C.gates[j.val]'j.isLt).op.eval
        ((C.gates[j.val]'j.isLt).inputs.map fun i =>
          if i < x.length + j.val then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j.val ++ [C.gates[j.val]'j.isLt] ++
      C.gates.drop (j.val + 1) := by
    have hj : j.val < C.gates.length := j.isLt
    change C.gates = C.gates.take j.val ++ [C.gates[j.val]'hj] ++ C.gates.drop (j.val + 1)
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
  have hlen : (C.gates.take j.val).length = j.val := List.length_take_of_le j.isLt.le
  change (run C.gates x).getD (x.length + j.val) false = _
  conv_lhs => rw [hsplit]
  rw [run_prefix _ _ _ _ (by simp [hlen]), run_snoc]
  have hwirelen : (run (C.gates.take j.val) x).length = x.length + j.val := by
    rw [run_length, hlen]
  rw [← hwirelen, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
  simp only [Option.getD_some, hwirelen]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j.val
  · rw [ite_eq_left hi]
    have h := run_prefix (C.gates.take j.val) (C.gates.drop j.val) x i (by rwa [hlen])
    rw [List.take_append_drop] at h
    exact h.symm
  · rw [ite_eq_right hi, getD_outside _ _ _ (by omega)]

lemma wire_gate_fn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : Fin C.size) :
    (C.wires (List.ofFn x)).getD (n + j.val) false =
      (C.gates[j.val]'j.isLt).op.eval
        ((C.gates[j.val]'j.isLt).inputs.map fun i =>
          if i < n + j.val then (C.wires (List.ofFn x)).getD i false else false) := by
  simpa only [List.length_ofFn] using wire_gate C (List.ofFn x) j

lemma gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : ℕ → Bool) (huv : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  rcases hg with h | h
  · rw [h]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro hu _ ⟨i, hi, rfl⟩
    exact huv i hi (hu _ ⟨i, hi, rfl⟩)
  · have hop : g.op = GateOp.or := h
    rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, hui⟩
    exact ⟨v i, ⟨i, hi, rfl⟩, huv i hi hui⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [input_wire C x ⟨w, hi⟩, input_wire C y ⟨w, hi⟩]
      exact hxy _
    by_cases hj : w < n + C.size
    · let j : Fin C.size := ⟨w - n, by omega⟩
      have hw : n + j.val = w := by simp [j]; omega
      rw [← hw, wire_gate_fn C x j, wire_gate_fn C y j]
      apply gate_mono _ (hm _ (List.getElem_mem j.isLt)).1
      intro i _
      by_cases hlt : i < n + j.val
      · simp only [hlt, ite_true]; exact ih i (by omega)
      · simp [hlt]
    · have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
        simpa [run, Circuit.size, Circuit.wires] using run_length C.gates (List.ofFn x)
      rw [getD_outside _ _ _ (by omega)]
      simp

def readsActive {n : ℕ} (C : Circuit) (A : Finset (Fin C.size)) (i w : ℕ) : Prop :=
  ∃ j ∈ A, w = n + j.val ∧ i < w ∧ i ∈ (C.gates[j.val]'j.isLt).inputs

lemma trace_difference {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A : Finset (Fin C.size)) (x y : Fin n → Bool) (s : Fin n)
    (hyx : ∀ i, y i = true → x i = true) (hs : ∀ i, x i ≠ y i → i = s)
    (hA : ∀ j : Fin C.size, (C.wires (List.ofFn x)).getD (n + j.val) false = true →
      (C.wires (List.ofFn y)).getD (n + j.val) false = false → j ∈ A) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = false →
      Relation.ReflTransGen (readsActive (n := n) C A) s.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx hy
    by_cases hi : w < n
    · rw [input_wire C x ⟨w, hi⟩] at hx
      rw [input_wire C y ⟨w, hi⟩] at hy
      have he := hs ⟨w, hi⟩ (by simp [hx, hy])
      rw [← congrArg Fin.val he]
    by_cases hj : w < n + C.size
    · let j : Fin C.size := ⟨w - n, by omega⟩
      have hw : n + j.val = w := by simp [j]; omega
      have hjA : j ∈ A := hA j (hw.symm ▸ hx) (hw.symm ▸ hy)
      rw [← hw, wire_gate_fn C x j] at hx
      rw [← hw, wire_gate_fn C y j] at hy
      have hread : ∃ i ∈ (C.gates[j.val]'j.isLt).inputs, i < w ∧
          (C.wires (List.ofFn x)).getD i false = true ∧
          (C.wires (List.ofFn y)).getD i false = false := by
        by_contra! hnone
        have hmaps : ((C.gates[j.val]'j.isLt).inputs.map fun i =>
              if i < n + j.val then (C.wires (List.ofFn x)).getD i false else false) =
            ((C.gates[j.val]'j.isLt).inputs.map fun i =>
              if i < n + j.val then (C.wires (List.ofFn y)).getD i false else false) := by
          apply List.map_congr_left
          intro i hi
          by_cases hlt : i < w
          · rw [hw, ite_eq_left hlt, ite_eq_left hlt]
            apply Bool.eq_iff_iff.mpr
            exact ⟨fun h => by simpa using hnone i hi hlt h, wires_mono C hm y x hyx i⟩
          · simp [hw, hlt]
        rw [hmaps, hy] at hx
        cases hx
      obtain ⟨i, hi, hiw, hxi, hyi⟩ := hread
      exact (ih i hiw hxi hyi).tail ⟨j, hjA, hw.symm, hiw, hi⟩
    · have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
        simpa [run, Circuit.size, Circuit.wires] using run_length C.gates (List.ofFn x)
      rw [getD_outside _ _ _ (by omega)] at hx
      cases hx

lemma count_reached {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A : Finset (Fin C.size)) (S : Finset (Fin n))
    (hS : ∀ s ∈ S, Relation.ReflTransGen (readsActive (n := n) C A) s.val C.output) :
    S.card ≤ A.card + 1 := by
  classical
  let reach := fun w => Relation.ReflTransGen (readsActive (n := n) C A) w C.output
  let R := A.filter fun j => reach (n + j.val)
  let W := R.biUnion fun j => (C.gates[j.val]'j.isLt).inputs.toFinset
  have hW : W.card ≤ 2 * R.card := by
    calc
      W.card ≤ ∑ j ∈ R, (C.gates[j.val]'j.isLt).inputs.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ R, 2 := Finset.sum_le_sum fun j _ =>
        (List.toFinset_card_le _).trans (hm _ (List.getElem_mem j.isLt)).2
      _ = 2 * R.card := by simp [Nat.mul_comm]
  have hreach (w : ℕ) (hw : reach w) : w ∈ insert C.output W := by
    rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨u, ⟨j, hj, hu, _, hju⟩, hru⟩
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hu ▸ hru⟩,
        List.mem_toFinset.mpr hju⟩
  let S' := S.image Fin.val
  let R' := R.image fun j => n + j.val
  have hsub : S' ∪ R' ⊆ insert C.output W := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
      exact hreach _ (hS s hs)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact hreach _ (Finset.mem_filter.mp hj).2
  have hdisj : Disjoint S' R' := by
    rw [Finset.disjoint_left]
    intro i hs hr
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hs
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hr
    have := s.isLt
    omega
  have hScard : S'.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
  have hRcard : R'.card = R.card :=
    Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
  have hsum := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [Finset.card_union_of_disjoint hdisj, hScard, hRcard] at hsum
  have hR : R.card ≤ A.card := Finset.card_filter_le _ _
  omega

-- The sparse incidence estimate is adapted from L_meta_3487.
open Finset

theorem per_deg (d k : ℕ) (hk : k + d = d * d) : 174 * d ≤ k + 7656 := by
  rcases le_or_gt d 87 with h | h
  · nlinarith
  · nlinarith

theorem key {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (h : ∀ (p p' : α) (l l' : β), p ≠ p' → l ≠ l' →
      ¬((p, l) ∈ E ∧ (p', l) ∈ E ∧ (p, l') ∈ E ∧ (p', l') ∈ E)) :
    174 * E.card + (E.image Prod.fst).card ≤
      (E.image Prod.fst).card * (E.image Prod.fst).card + 7656 * (E.image Prod.snd).card := by
  set P := E.image Prod.fst with hPdef
  set L := E.image Prod.snd with hLdef
  set F : β → Finset (α × β) := fun l => E.filter (fun x => x.2 = l) with hF
  have hE : E.card = ∑ l ∈ L, (F l).card := card_eq_sum_card_image Prod.snd E
  have hinj : ∑ l ∈ L, ((F l).offDiag).card ≤ P.offDiag.card := by
    rw [← card_sigma]
    apply card_le_card_of_injOn (fun z => (z.2.1.1, z.2.2.1))
    · rintro ⟨l, ⟨p, m⟩, ⟨q, n⟩⟩ hz
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_offDiag, hF, mem_filter] at hz
      obtain ⟨_, ⟨h1, hm⟩, ⟨h2, hn⟩, hne⟩ := hz
      subst hm
      subst hn
      simp only [mem_coe, mem_offDiag, hPdef, mem_image]
      refine ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩, ?_⟩
      intro he
      apply hne
      rw [he]
    · rintro ⟨l, ⟨p, m⟩, ⟨q, n⟩⟩ hz ⟨l', ⟨p', m'⟩, ⟨q', n'⟩⟩ hz' heq
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_offDiag, hF, mem_filter] at hz hz'
      obtain ⟨_, ⟨h1, hm⟩, ⟨h2, hn⟩, hne⟩ := hz
      obtain ⟨_, ⟨h1', hm'⟩, ⟨h2', hn'⟩, hne'⟩ := hz'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hp, hq⟩ := heq
      subst hp
      subst hq
      rw [hm] at h1
      rw [hn] at h2
      rw [hm'] at h1'
      rw [hn'] at h2'
      have hpq : p ≠ q := by
        intro he
        apply hne
        rw [he, hm, hn]
      by_cases hll : l = l'
      · subst hll
        rw [hm, hn, hm', hn']
      · exact absurd ⟨h1, h2, h1', h2'⟩ (h p q l l' hpq hll)
  have hdeg : ∀ l ∈ L, 174 * (F l).card ≤ ((F l).offDiag).card + 7656 := by
    intro l _
    apply per_deg
    rw [offDiag_card]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  have hsum : 174 * E.card ≤ P.offDiag.card + 7656 * L.card := by
    rw [hE, mul_sum]
    calc ∑ l ∈ L, 174 * (F l).card ≤ ∑ l ∈ L, (((F l).offDiag).card + 7656) := sum_le_sum hdeg
      _ = ∑ l ∈ L, ((F l).offDiag).card + 7656 * L.card := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm]
      _ ≤ P.offDiag.card + 7656 * L.card := by omega
  have hP : P.offDiag.card + P.card = P.card * P.card := by
    rw [offDiag_card]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  omega

theorem fin_bound (e a b : ℕ) (ha : a ≤ 7656) (h1 : 1 ≤ a)
    (hk : 174 * e + a ≤ a * a + 7656 * b) : e ≤ 44 * (a + b - 1) := by
  have h2 : 174 * e + 7656 ≤ 7656 * a + 7656 * b := by nlinarith
  omega

lemma sparse_bound : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E h hmin
  rcases E.eq_empty_or_nonempty with hE | hE
  · subst hE
    simp
  have ha1 : 1 ≤ (E.image Prod.fst).card := Finset.card_pos.2 (hE.image _)
  have hb1 : 1 ≤ (E.image Prod.snd).card := Finset.card_pos.2 (hE.image _)
  rcases min_le_iff.1 hmin with ha | hb
  · exact fin_bound _ _ _ ha ha1 (key E h)
  · set E' := E.image Prod.swap with hE'
    have hmem : ∀ x y : Fin n, (x, y) ∈ E' ↔ (y, x) ∈ E := by
      intro x y
      simp [hE']
    have hc : E'.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
    have hf : E'.image Prod.fst = E.image Prod.snd := by
      ext x
      simp [hE']
    have hs : E'.image Prod.snd = E.image Prod.fst := by
      ext x
      simp [hE']
    have h' : ∀ (p p' : Fin n) (l l' : Fin n), p ≠ p' → l ≠ l' →
        ¬((p, l) ∈ E' ∧ (p', l) ∈ E' ∧ (p, l') ∈ E' ∧ (p', l') ∈ E') := by
      intro p p' l l' hp hl hh
      rw [hmem, hmem, hmem, hmem] at hh
      obtain ⟨h1, h2, h3, h4⟩ := hh
      exact h l l' p p' hl hp ⟨h1, h3, h2, h4⟩
    have hk := key E' h'
    rw [hc, hf, hs] at hk
    have := fin_bound _ _ _ hb hb1 hk
    rw [Nat.add_comm (E.image Prod.fst).card]
    exact this

end PEqualNP.Outside.L_meta_4659

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4659

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_4659 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x2 → Finset (Fin x2)),   have x7 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x7 : Finset (Fin x2)) (x8 : Fin (x2 + x2)) => Fin.addCases (fun (x9 : Fin x2) => Decidable.decide ¬∃ x10 ∈ x7, x3 x9 x10) (fun (x9 : Fin x2) => Decidable.decide (x9 ∈ x7)) x8;   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => if x8.op.eval [] = Bool.true ∧ x8.inputs.length = (2 : ℕ) ∧ (x8.inputs.all fun (x9 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x9 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x8) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };   have x9 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x9 x10 : Fin x2) (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x9 ∨ x11 = Fin.natAdd x2 x10);   (Finset.univ.biUnion x6).card ≤ (1893 : ℕ) ∨ Fintype.card { x10 : Fin x2 // (x6 x10).Nonempty } ≤ (1893 : ℕ) → (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x13 : Fin x2), Fintype.card { x14 : Fin x2 // x3 x14 x13 } = x1 + (1 : ℕ)) → (∀ (x14 x15 : Fin x2), x14 ≠ x15 → ∃! x17 : Fin x2, x3 x14 x17 ∧ x3 x15 x17) → PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → x5.eval (List.ofFn (x7 x16)) = Bool.false) → (∀ (x17 x18 : Fin x2), x18 ∈ x6 x17 → x3 x18 x17 ∧ x5.eval (List.ofFn (x9 x18 x17)) = Bool.true ∧ x8.eval (List.ofFn (x9 x18 x17)) = Bool.false) → ∑ x18 : Fin x2, (x6 x18).card ≤ (44 : ℕ) * Fintype.card { x18 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x18) Bool.false = Bool.false ∧ ∃ (x19 : Fin x2), ∃ x20 ∈ x6 x19, (x5.wires (List.ofFn (x9 x20 x19))).getD (x2 + x2 + ↑x18) Bool.false = Bool.true } := by
  intro q N I inst C T avoid D pair hsmall hq hN hlines huniq hminimal hreject hT
  classical
  let toEdge : (Σ _ : Fin N, Fin N) → Fin N × Fin N := fun e => (e.2, e.1)
  let E := ((Finset.univ : Finset (Fin N)).sigma T).image toEdge
  have hmem (p l : Fin N) : (p, l) ∈ E ↔ p ∈ T l := by
    constructor
    · intro he
      obtain ⟨⟨l', p'⟩, hm, heq⟩ := Finset.mem_image.mp he
      change (p', l') = (p, l) at heq
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp heq
      exact (Finset.mem_sigma.mp hm).2
    · intro hp
      exact Finset.mem_image.mpr ⟨⟨l, p⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
  have hEcard : E.card = ∑ l : Fin N, (T l).card := by
    change (((Finset.univ : Finset (Fin N)).sigma T).image toEdge).card = _
    rw [Finset.card_image_of_injective, Finset.card_sigma]
    rintro ⟨l₁, p₁⟩ ⟨l₂, p₂⟩ h
    change (p₁, l₁) = (p₂, l₂) at h
    cases h
    rfl
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  have hP : P = Finset.univ.biUnion T := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨p', l⟩, he, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, (hmem p' l).mp he⟩
    · intro hp
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hp
      exact Finset.mem_image.mpr ⟨(p, l), (hmem p l).mpr hl, rfl⟩
  have hL : Fintype.card {l : Fin N // (T l).Nonempty} = L.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, L, Finset.mem_image]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨(p, l), (hmem p l).mpr hp, rfl⟩
    · rintro ⟨⟨p, l'⟩, he, hl⟩
      change l' = l at hl
      subst l'
      exact ⟨p, (hmem p l).mp he⟩
  have hnorect (p r l m : Fin N) (hpr : p ≠ r) (hlm : l ≠ m) :
      ¬ ((p, l) ∈ E ∧ (r, l) ∈ E ∧ (p, m) ∈ E ∧ (r, m) ∈ E) := by
    rintro ⟨hpl, hrl, hpm, hrm⟩
    obtain ⟨l₀, _, hu⟩ := huniq p r hpr
    exact hlm ((hu l ⟨(hT l p ((hmem p l).mp hpl)).1, (hT l r ((hmem r l).mp hrl)).1⟩).trans
      (hu m ⟨(hT m p ((hmem p m).mp hpm)).1, (hT m r ((hmem r m).mp hrm)).1⟩).symm)
  have hmin : min P.card L.card ≤ 7656 := by
    rcases hsmall with hs | hs
    · exact (min_le_left P.card L.card).trans (by rw [hP]; omega)
    · exact (min_le_right P.card L.card).trans (by rw [← hL]; omega)
  have hsparse : E.card ≤ 44 * (P.card + L.card - 1) := sparse_bound N E hnorect hmin
  let A : Finset (Fin C.size) := Finset.univ.filter fun j =>
    (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
      ∃ l : Fin N, ∃ p ∈ T l, (C.wires (List.ofFn (pair p l))).getD (N + N + j.val) false = true
  have hAcard : Fintype.card {j : Fin C.size //
      (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
      ∃ l : Fin N, ∃ p ∈ T l, (C.wires (List.ofFn (pair p l))).getD (N + N + j.val) false = true} =
        A.card := by
    rw [Fintype.card_subtype]
  let single (i : Fin (N + N)) : Fin (N + N) → Bool := fun j => decide (j = i)
  have reject_single (i : Fin (N + N)) (Z : Finset (Fin N)) (hZ : Z.card ≤ q)
      (hi : avoid Z i = true) : C.eval (List.ofFn (single i)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hle (j : Fin (N + N)) (hj : single i j = true) : avoid Z j = true := by
      have hji : j = i := by simpa [single] using hj
      simpa [hji] using hi
    have htrue := wires_mono C hminimal.1 (single i) (avoid Z) hle C.output h
    change C.eval (List.ofFn (avoid Z)) = true at htrue
    rw [hreject Z hZ] at htrue
    cases htrue
  have reject_point (p : Fin N) : C.eval (List.ofFn (single (Fin.castAdd N p))) = false := by
    apply reject_single _ ∅ (by simp)
    simp [avoid]
  have reject_line (l : Fin N) : C.eval (List.ofFn (single (Fin.natAdd N l))) = false := by
    apply reject_single _ {l} (by simpa using (show 1 ≤ q by omega))
    simp only [avoid, Fin.addCases_right, Finset.mem_singleton, decide_true]
  have hreach (i j : Fin (N + N)) (p l : Fin N) (hp : p ∈ T l)
      (hpair : pairInput i j = pair p l) (hfalse : C.eval (List.ofFn (single j)) = false) :
      Relation.ReflTransGen (readsActive (n := N + N) C A) i.val C.output := by
    refine trace_difference C hminimal.1 A (pairInput i j) (single j) i ?_ ?_ ?_ C.output ?_ ?_
    · intro k
      simp only [single, pairInput, decide_eq_true_eq]
      exact Or.inr
    · intro k h
      by_contra hki
      exact h (by simp [pairInput, single, hki])
    · intro a htrue hzero
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, l, p, hp, ?_⟩
      · apply Bool.eq_false_iff.mpr
        intro hz
        have hmono := wires_mono C hminimal.1 (fun _ => false) (single j)
          (by simp) (N + N + a.val)
        rw [List.ofFn_const] at hmono
        rw [hzero] at hmono
        exact Bool.noConfusion (hmono hz)
      · simpa only [hpair] using htrue
    · rw [hpair]
      exact (hT l p hp).2.1
    · exact hfalse
  let SP := P.image (Fin.castAdd N)
  let SL := L.image (Fin.natAdd N)
  have hd : Disjoint SP SL := by
    rw [Finset.disjoint_left]
    intro i hip hil
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hip
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hil
    have h := congrArg Fin.val (hp.trans hl.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    have := p.isLt
    omega
  have hSP : SP.card = P.card := by
    apply Finset.card_image_of_injective
    intro a b h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  have hSL : SL.card = L.card := by
    apply Finset.card_image_of_injective
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (Nat.add_left_cancel hv)
  have hcount : (SP ∪ SL).card ≤ A.card + 1 := by
    apply count_reached C hminimal.1 A
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨⟨p', l⟩, he, hpp⟩ := Finset.mem_image.mp hp
      change p' = p at hpp
      subst p'
      exact hreach _ _ p l ((hmem p l).mp he) rfl (reject_line l)
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨⟨p, l'⟩, he, hll⟩ := Finset.mem_image.mp hl
      change l' = l at hll
      subst l'
      apply hreach _ _ p l ((hmem p l).mp he) _ (reject_point p)
      funext k
      simp [pairInput, pair, or_comm]
  rw [Finset.card_union_of_disjoint hd, hSP, hSL] at hcount
  rw [hAcard, ← hEcard]
  exact hsparse.trans (Nat.mul_le_mul_left 44 (by omega))
