import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1603

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CarriedProduct

def rn (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma rn_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    rn (g :: gs) x = rn gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma rn_length (gs : List Gate) (x : List Bool) :
    (rn gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [rn]
  | cons g gs ih => rw [rn_cons, ih]; simp; omega

lemma rn_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (rn gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [rn_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma rn_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    rn gs x = rn (gs.drop j) (rn (gs.take j) x) := by
  simpa only [rn, List.foldl_append] using
    congrArg (fun l : List Gate => rn l x) (List.take_append_drop j gs).symm

def vl {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma vl_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : vl C x w = false := by
  change (rn C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [rn_length] using hw)

lemma vl_gate0 {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.gates.length) :
    let g := C.gates[w - n]'(by omega)
    vl C x w = g.op.eval (g.inputs.map fun r => if r < w then vl C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j; omega
  let g := C.gates[j]
  let earlier := rn (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, rn_length, Nat.min_eq_left hj.le, j]; omega
  have split : rn C.gates (List.ofFn x) = rn (g :: C.gates.drop (j + 1)) earlier := by
    rw [rn_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then vl C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (rn C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (rn_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (rn C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then vl C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [rn_cons]
  rw [rn_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma vl_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    vl C x w = x ⟨w, hw⟩ := by
  change (rn C.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
  have hp : w < (List.ofFn x).length := by simpa using hw
  rw [rn_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma vl_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    vl C x (n + j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun r => if r < n + j then vl C x r else false) := by
  have h := vl_gate0 C x (n + j) (by omega) (by omega)
  rw [gateAt_eq C j hj]
  simpa only [Nat.add_sub_cancel_left] using h

lemma vl_and {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    vl C x (n + j) = true ↔ ∀ r ∈ (gateAt C j).inputs, r < n + j ∧ vl C x r = true := by
  rw [vl_gate C x j hj, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq]
  constructor
  · intro h r hr
    have h1 := h _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    by_cases hlt : r < n + j
    · rw [if_pos hlt] at h1
      exact ⟨hlt, h1⟩
    · rw [if_neg hlt] at h1
      exact Bool.noConfusion h1
  · intro h b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    obtain ⟨h1, h2⟩ := h r hr
    rw [if_pos h1]
    exact h2

lemma vl_or {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    vl C x (n + j) = true ↔ ∃ r ∈ (gateAt C j).inputs, r < n + j ∧ vl C x r = true := by
  rw [vl_gate C x j hj, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  constructor
  · rintro ⟨b, hb, hv⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    by_cases hlt : r < n + j
    · rw [if_pos hlt] at hv
      exact ⟨r, hr, hlt, hv⟩
    · rw [if_neg hlt] at hv
      exact Bool.noConfusion hv
  · rintro ⟨r, hr, h1, h2⟩
    refine ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    rw [if_pos h1]
    exact h2

def lvF (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) : List ℕ :=
  ((List.range m).reverse).foldl (liveStep n C vals) L

lemma lvF_succ (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) :
    lvF n C vals (m + 1) L = lvF n C vals m (liveStep n C vals L m) := by
  simp [lvF, List.range_succ]

lemma step_sub (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (h : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append.mpr (Or.inl h)
  · exact h

lemma step_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (h : w ∈ liveStep n C vals L j) :
    w ∈ L ∨ (n + j ∈ L ∧ w ∈ (gateAt C j).inputs ∧ w < n + j ∧ vals.getD w false = true) := by
  unfold liveStep at h
  split_ifs at h with hc
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
      have h3 : (decide (w < n + j) && vals.getD w false) = true := h2
      rw [Bool.and_eq_true, decide_eq_true_eq] at h3
      exact Or.inr ⟨hc, h1, h3.1, h3.2⟩
  · exact Or.inl h

lemma step_add (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (hc : n + j ∈ L) (hw : w ∈ (gateAt C j).inputs) (hlt : w < n + j)
    (hv : vals.getD w false = true) : w ∈ liveStep n C vals L j := by
  unfold liveStep
  rw [if_pos hc]
  refine List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨hw, ?_⟩))
  show (decide (w < n + j) && vals.getD w false) = true
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hlt, hv⟩

lemma lvF_sub (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ L → w ∈ lvF n C vals m L := by
  intro m
  induction m with
  | zero => intro L w h; simpa [lvF] using h
  | succ m ih =>
    intro L w h
    rw [lvF_succ]
    exact ih _ _ (step_sub n C vals L m w h)

lemma lvF_inv (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ lvF n C vals m L →
      w ∈ L ∨ (w < n + m ∧ vals.getD w false = true) := by
  intro m
  induction m with
  | zero => intro L w h; left; simpa [lvF] using h
  | succ m ih =>
    intro L w h
    rw [lvF_succ] at h
    rcases ih _ _ h with h | ⟨h1, h2⟩
    · rcases step_mem n C vals L m w h with h | ⟨_, _, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, h4⟩
    · exact Or.inr ⟨by omega, h2⟩

lemma lvF_read (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (j : ℕ), j < m → n + j ∈ lvF n C vals m L →
      ∀ w ∈ (gateAt C j).inputs, w < n + j → vals.getD w false = true →
        w ∈ lvF n C vals m L := by
  intro m
  induction m with
  | zero => intro L j hj; omega
  | succ m ih =>
    intro L j hj hmem w hw hlt hv
    rw [lvF_succ] at hmem ⊢
    by_cases hjm : j < m
    · exact ih _ j hjm hmem w hw hlt hv
    · have hjm' : j = m := by omega
      subst hjm'
      rcases lvF_inv n C vals j _ _ hmem with h | ⟨h, _⟩
      · rcases step_mem n C vals L j _ h with h' | ⟨h', _⟩
        · exact lvF_sub n C vals j _ w (step_add n C vals L j w h' hw hlt hv)
        · exact lvF_sub n C vals j _ w (step_add n C vals L j w h' hw hlt hv)
      · omega

lemma live_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    liveWires n C x = lvF n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := rfl

lemma live_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    vl C x w = true := by
  unfold IsLive at h
  rw [live_eq] at h
  rcases lvF_inv _ _ _ _ _ _ h with h | ⟨_, h⟩
  · split_ifs at h with hc
    · have hw : w = C.output := by simpa using h
      rw [hw]
      exact hc
    · simp at h
  · exact h

lemma live_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) (h : vl C x C.output = true) :
    IsLive n C x C.output := by
  unfold IsLive
  rw [live_eq]
  apply lvF_sub
  rw [if_pos (show (C.wires (List.ofFn x)).getD C.output false = true from h)]
  simp

lemma live_read {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ)
    (hl : IsLive n C x (n + j)) (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hlt : w < n + j) (hv : vl C x w = true) : IsLive n C x w := by
  unfold IsLive at hl ⊢
  rw [live_eq] at hl ⊢
  exact lvF_read n C _ _ _ j hj hl w hw hlt hv

lemma gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]
  exact List.getElem_mem hj

lemma key_side {n : ℕ} (C : Circuit) (hM : Monotone2 C) (u v : Fin n) (B : ℕ)
    (hB : ∀ j, n + j < B → j < C.gates.length → (gateAt C j).op = GateOp.and →
      ¬ IsLive n C (pairInput u v) (n + j)) :
    ∀ w, w < B → IsLive n C (pairInput u v) w →
      vl C (pairInput u u) w = true ∨ vl C (pairInput v v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hl
    have ht := live_true C _ w hl
    by_cases hn : w < n
    · rw [vl_input C _ w hn] at ht
      rw [vl_input C _ w hn, vl_input C _ w hn]
      simp only [pairInput, decide_eq_true_eq] at ht ⊢
      rcases ht with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    by_cases hw : n + C.gates.length ≤ w
    · rw [vl_missing C _ w hw] at ht
      exact Bool.noConfusion ht
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hops := (hM _ (gate_mem C k hk)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
    rcases hops with hop | hop
    · exact absurd hl (hB k hwB hk hop)
    · rw [vl_or C _ k hk hop] at ht
      obtain ⟨r, hr, hlt, hv⟩ := ht
      have hlr := live_read C _ k r hl hk hr hlt hv
      rcases ih r hlt (by omega) hlr with h | h
      · left
        rw [vl_or C _ k hk hop]
        exact ⟨r, hr, hlt, h⟩
      · right
        rw [vl_or C _ k hk hop]
        exact ⟨r, hr, hlt, h⟩

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hM : Monotone2 C)
    (hfun : ∀ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin n => x k = true)).card ≤ 2 →
      circuitFun n C x = graphFun G ∅ x)
    (hand : ∀ j : ℕ, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ i : Fin n, gateVal n C j (pairInput i i) = false)
    (u v : Fin n) (huv : G.Adj u v) :
    (∃ t : ℕ, IsCarrier n C u v t) ∧ ∀ s : ℕ, IsCarrier n C u v s →
      ∃ a b : ℕ, (gateAt C s).inputs = [a, b] ∧
        ((PEqualNP.CleanedNonEdge.wireVal n C a (pairInput u u) = true ∧
            PEqualNP.CleanedNonEdge.wireVal n C b (pairInput v v) = true) ∨
          (PEqualNP.CleanedNonEdge.wireVal n C a (pairInput v v) = true ∧
            PEqualNP.CleanedNonEdge.wireVal n C b (pairInput u u) = true)) := by
  have hcard : ∀ a b : Fin n,
      (Finset.univ.filter (fun k : Fin n => pairInput a b k = true)).card ≤ 2 := by
    intro a b
    refine le_trans (Finset.card_le_card (t := {a, b}) ?_) Finset.card_le_two
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairInput, decide_eq_true_eq] at hk
    simpa using hk
  have houv : vl C (pairInput u v) C.output = true := by
    have h := hfun _ (hcard u v)
    have h2 : graphFun G ∅ (pairInput u v) = true := by
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    rw [h2] at h
    exact h
  have hsing : ∀ i : Fin n, vl C (pairInput i i) C.output = false := by
    intro i
    have h := hfun _ (hcard i i)
    have h2 : graphFun G ∅ (pairInput i i) = false := by
      simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨by simp, ?_⟩
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [pairInput, or_self, decide_eq_true_eq] at ha hb
      subst ha
      subst hb
      exact G.irrefl hab
    rw [h2] at h
    exact h
  have hex : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      IsLive n C (pairInput u v) (n + j) := by
    by_contra hno
    have hB : ∀ j, n + j < C.output + 1 → j < C.gates.length →
        (gateAt C j).op = GateOp.and → ¬ IsLive n C (pairInput u v) (n + j) := by
      intro j _ hj hop hl
      exact hno ⟨j, hj, hop, hl⟩
    rcases key_side C hM u v _ hB C.output (by omega) (live_out C _ houv) with h | h
    · rw [hsing u] at h
      exact Bool.noConfusion h
    · rw [hsing v] at h
      exact Bool.noConfusion h
  refine ⟨?_, ?_⟩
  · classical
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1,
      (Nat.find_spec hex).2.2, ?_⟩
    intro i hi hop hl
    have hs := (Nat.find_spec hex).1
    exact Nat.find_min hex hi ⟨by omega, hop, hl⟩
  · rintro s ⟨hs, hop, hlive, hmin⟩
    have hB : ∀ j, n + j < n + s → j < C.gates.length →
        (gateAt C j).op = GateOp.and → ¬ IsLive n C (pairInput u v) (n + j) := by
      intro j hj _ hopj
      exact hmin j (by omega) hopj
    have hK := key_side C hM u v _ hB
    have ht := live_true C _ _ hlive
    rw [vl_and C _ s hs hop] at ht
    have hu : vl C (pairInput u u) (n + s) = false := hand s hs hop u
    have hv : vl C (pairInput v v) (n + s) = false := hand s hs hop v
    have hlen := (hM _ (gate_mem C s hs)).2
    have hside : ∀ r ∈ (gateAt C s).inputs,
        vl C (pairInput u u) r = true ∨ vl C (pairInput v v) r = true := by
      intro r hr
      obtain ⟨hlt, hval⟩ := ht r hr
      exact hK r hlt (live_read C _ s r hlive hs hr hlt hval)
    have hnu : ¬ ∀ r ∈ (gateAt C s).inputs, r < n + s ∧ vl C (pairInput u u) r = true := by
      intro h
      rw [(vl_and C _ s hs hop).mpr h] at hu
      exact Bool.noConfusion hu
    have hnv : ¬ ∀ r ∈ (gateAt C s).inputs, r < n + s ∧ vl C (pairInput v v) r = true := by
      intro h
      rw [(vl_and C _ s hs hop).mpr h] at hv
      exact Bool.noConfusion hv
    rcases hin : (gateAt C s).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · rw [hin] at hnu
      exact absurd (by simp) hnu
    · rw [hin] at hnu hnv ht hside
      have hlt := (ht a (by simp)).1
      rcases hside a (by simp) with h | h
      · exfalso
        apply hnu
        intro r hr
        have hra : r = a := by simpa using hr
        subst hra
        exact ⟨hlt, h⟩
      · exfalso
        apply hnv
        intro r hr
        have hra : r = a := by simpa using hr
        subst hra
        exact ⟨hlt, h⟩
    · rw [hin] at hnu hnv ht hside
      have hlta := (ht a (by simp)).1
      have hltb := (ht b (by simp)).1
      refine ⟨a, b, rfl, ?_⟩
      rcases hside a (by simp) with ha | ha <;> rcases hside b (by simp) with hb | hb
      · exfalso
        apply hnu
        intro r hr
        have hr' : r = a ∨ r = b := by simpa using hr
        rcases hr' with rfl | rfl
        · exact ⟨hlta, ha⟩
        · exact ⟨hltb, hb⟩
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
      · exfalso
        apply hnv
        intro r hr
        have hr' : r = a ∨ r = b := by simpa using hr
        rcases hr' with rfl | rfl
        · exact ⟨hlta, ha⟩
        · exact ⟨hltb, hb⟩
    · rw [hin] at hlen
      simp at hlen

end PEqualNP.Outside.L_meta_1603

theorem PEqualNP.Outside.L_meta_1603 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (Finset.univ.filter (fun k : Fin n => x k = true)).card ≤ 2 → PEqualNP.MetaComplexity.circuitFun n C x = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) → (∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ i : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput i i) = false) → ∀ u v : Fin n, G.Adj u v → (∃ t : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v t) ∧ ∀ s : ℕ, PEqualNP.CarriedProduct.IsCarrier n C u v s → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C s).inputs = [a, b] ∧ ((PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput u u) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput v v) = true) ∨ (PEqualNP.CleanedNonEdge.wireVal n C a (PEqualNP.EdgeOwnership.pairInput v v) = true ∧ PEqualNP.CleanedNonEdge.wireVal n C b (PEqualNP.EdgeOwnership.pairInput u u) = true)) := by
  intro n G _ C hM hfun hand u v huv
  exact PEqualNP.Outside.L_meta_1603.main n G C hM hfun hand u v huv
