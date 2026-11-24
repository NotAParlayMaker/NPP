import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_append_left_g {α : Type} {l1 l2 : List α} {i : Nat} (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  induction l1 generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih (by simpa using h)

lemma getD_append_left {l1 l2 : List Bool} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false :=
  getD_append_left_g false h

lemma getD_append_self_g {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil => rfl
  | cons x t ih => simpa using ih

lemma getD_concat_two {α : Type} (l : List α) (a b d : α) : (l ++ [a, b]).getD l.length d = a := by
  induction l with
  | nil => rfl
  | cons x t ih => simpa using ih

lemma getD_concat_two_succ {α : Type} (l : List α) (a b d : α) :
    (l ++ [a, b]).getD (l.length + 1) d = b := by
  induction l with
  | nil => rfl
  | cons x t ih => simpa using ih

lemma getD_map_gate (l : List Gate) (f : Gate → Gate) (j : Nat) (d : Gate) (h : j < l.length) :
    (l.map f).getD j d = f (l.getD j d) := by
  induction l generalizing j with
  | nil => simp at h
  | cons g t ih =>
    cases j with
    | zero => rfl
    | succ j => simpa using ih j (by simpa using h)

lemma wires_cons (g : Gate) (t : List Gate) (out : Nat) (L : List Bool) :
    (⟨g :: t, out⟩ : Circuit).wires L
      = (⟨t, out⟩ : Circuit).wires (L ++ [g.op.eval (g.inputs.map fun i => L.getD i false)]) := by
  simp [Circuit.wires]

lemma wires_append (gs hs : List Gate) (out : Nat) (L : List Bool) :
    (⟨gs ++ hs, out⟩ : Circuit).wires L
      = (⟨hs, out⟩ : Circuit).wires ((⟨gs, out⟩ : Circuit).wires L) := by
  simp [Circuit.wires, List.foldl_append]

lemma wires_single (g : Gate) (out : Nat) (W : List Bool) :
    (⟨[g], out⟩ : Circuit).wires W
      = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := by
  simp [Circuit.wires]

lemma wires_two (g1 g2 : Gate) (out : Nat) (W : List Bool) :
    (⟨[g1, g2], out⟩ : Circuit).wires W
      = W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false),
              g2.op.eval (g2.inputs.map fun i =>
                (W ++ [g1.op.eval (g1.inputs.map fun j => W.getD j false)]).getD i false)] := by
  simp [Circuit.wires]

lemma and_eval_pair (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

lemma or_eval_pair (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

lemma wires_getD_input (gs : List Gate) (out : Nat) (L : List Bool) {i : Nat} (h : i < L.length) :
    ((⟨gs, out⟩ : Circuit).wires L).getD i false = L.getD i false := by
  induction gs generalizing L with
  | nil => rfl
  | cons g t ih =>
    rw [wires_cons]
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact getD_append_left (by simpa using h)

lemma wires_length (gs : List Gate) (out : Nat) (L : List Bool) :
    ((⟨gs, out⟩ : Circuit).wires L).length = L.length + gs.length := by
  induction gs generalizing L with
  | nil => simp [Circuit.wires]
  | cons g t ih =>
    rw [wires_cons, ih]
    simp
    omega

def sig (n m : Nat) (w : Nat → Nat) (v : Nat) : Nat := if v < n then w v else m + (v - n)

lemma sig_lt {n m : Nat} {w : Nat → Nat} (hw : ∀ k, k < n → w k < m) {d v : Nat} (hv : v < n + d) :
    sig n m w v < m + d := by
  by_cases h : v < n
  · have h1 : sig n m w v = w v := by simp [sig, h]
    have h2 := hw v h
    omega
  · have h1 : sig n m w v = m + (v - n) := by simp [sig, h]
    omega

lemma sig_of_lt {n m : Nat} {w : Nat → Nat} {v : Nat} (h : v < n) : sig n m w v = w v := by
  simp [sig, h]

lemma sig_of_le {n m : Nat} {w : Nat → Nat} {v : Nat} (h : n <= v) : sig n m w v = m + (v - n) := by
  have h' : ¬ v < n := by omega
  simp [sig, h']

lemma sub_aux {n m : Nat} (w : Nat → Nat) (hw : ∀ k, k < n → w k < m)
    (gs : List Gate) (off : Nat) (L M : List Bool) (out : Nat)
    (hL : L.length = m + off) (hM : M.length = n + off)
    (hinv : ∀ v, v < n + off → M.getD v false = L.getD (sig n m w v) false)
    (hback : ∀ j, j < gs.length → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + off + j) :
    ∀ v, v < n + off + gs.length →
      ((⟨gs, out⟩ : Circuit).wires M).getD v false
        = ((⟨gs.map (fun g => ⟨g.op, g.inputs.map (sig n m w)⟩), out⟩ : Circuit).wires L).getD (sig n m w v) false := by
  induction gs generalizing off L M with
  | nil =>
    intro v hv
    exact hinv v (by simpa using hv)
  | cons g t ih =>
    intro v hv
    simp only [List.map_cons]
    conv_lhs => rw [wires_cons g t out M]
    conv_rhs => rw [wires_cons ⟨g.op, g.inputs.map (sig n m w)⟩
      (List.map (fun g => ⟨g.op, g.inputs.map (sig n m w)⟩) t) out L]
    set vM : Bool := g.op.eval (g.inputs.map fun i => M.getD i false) with hvM
    set vL : Bool := g.op.eval ((g.inputs.map (sig n m w)).map fun i => L.getD i false) with hvL
    have hveq : vM = vL := by
      rw [hvM, hvL]
      simp only [List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro i hi
      have hb : i < n + off := by
        have h0 := hback 0 (by simp) i (by simpa using hi)
        simpa using h0
      exact hinv i hb
    rw [hveq]
    have hL' : (L ++ [vL]).length = m + (off + 1) := by
      rw [List.length_append, List.length_singleton, hL]; omega
    have hM' : (M ++ [vL]).length = n + (off + 1) := by
      rw [List.length_append, List.length_singleton, hM]; omega
    have hinv' : ∀ u, u < n + (off + 1) → (M ++ [vL]).getD u false = (L ++ [vL]).getD (sig n m w u) false := by
      intro u hu
      by_cases hu' : u < n + off
      · have e1 : (M ++ [vL]).getD u false = M.getD u false :=
          getD_append_left (l1 := M) (l2 := [vL]) (i := u) (by simp [hM]; omega)
        have e2 : (L ++ [vL]).getD (sig n m w u) false = L.getD (sig n m w u) false :=
          getD_append_left (l1 := L) (l2 := [vL]) (i := sig n m w u) (by simp [hL]; exact sig_lt hw (by omega))
        rw [e1, e2]
        exact hinv u hu'
      · have hu2 : u = n + off := by omega
        subst hu2
        have e1 : (M ++ [vL]).getD (n + off) false = vL := by
          rw [← hM]; exact getD_append_self_g M vL false
        have e2 : (L ++ [vL]).getD (sig n m w (n + off)) false = vL := by
          have hs : sig n m w (n + off) = m + off := by
            rw [sig_of_le (n := n) (m := m) (w := w) (by omega)]; omega
          rw [hs, ← hL]
          exact getD_append_self_g L vL false
        rw [e1, e2]
    have hback' : ∀ j, j < t.length → ∀ i ∈ (t.getD j ⟨GateOp.or, []⟩).inputs, i < n + (off + 1) + j := by
      intro j hj i hi
      have h0 := hback (j + 1) (by simp; omega) i (by simpa using hi)
      omega
    have hv' : v < n + (off + 1) + t.length := by
      simp only [List.length_cons] at hv; omega
    exact ih (off + 1) (L ++ [vL]) (M ++ [vL]) hL' hM' hinv' hback' v hv'

lemma mapGate_isAO2' {n m : Nat} (w : Nat → Nat) (hw : ∀ k, k < n → w k < m)
    {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 m
      (⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (sig n m w)⟩), sig n m w C.output⟩ : Circuit) := by
  obtain ⟨ha, hb, hc⟩ := hC
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact ha g' hg'
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa using hj
    change i ∈ ((C.gates.map (fun g => ⟨g.op, g.inputs.map (sig n m w)⟩)).getD j
      (⟨GateOp.or, []⟩ : Gate)).inputs at hi
    rw [getD_map_gate C.gates _ j _ hj'] at hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hi
    exact sig_lt hw (hb j hj' i' hi')
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa using hc g' hg'

lemma sub_circuit {n m : Nat} (w : Nat → Nat) (hw : ∀ k, k < n → w k < m)
    {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.size) :
    ∃ C' : Circuit, C'.size = C.size ∧ PEqualNP.TopForm.IsAO2 m C' ∧ C'.output < m + C'.size ∧
      ∀ (L : List Bool) (z : Fin n → Bool), L.length = m →
        (∀ k : Fin n, z k = L.getD (w k.val) false) → C'.eval L = circuitFun n C z := by
  refine ⟨⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (sig n m w)⟩), sig n m w C.output⟩, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · exact mapGate_isAO2' w hw hC
  · have h1 : sig n m w C.output < m + C.size := sig_lt hw (by simpa using hout)
    simpa [Circuit.size] using h1
  · intro L z hL hz
    have hM : (List.ofFn z).length = n + 0 := by simp
    have hL0 : L.length = m + 0 := by simpa using hL
    have hinv : ∀ v, v < n + 0 → (List.ofFn z).getD v false = L.getD (sig n m w v) false := by
      intro v hv
      have hv' : v < n := by simpa using hv
      have h1 : (List.ofFn z).getD v false = z ⟨v, hv'⟩ := by simp [List.getD, hv']
      rw [h1, sig_of_lt (n := n) (m := m) (w := w) hv']
      exact hz ⟨v, hv'⟩
    have hback : ∀ j, j < C.gates.length →
        ∀ i ∈ (C.gates.getD j (⟨GateOp.or, []⟩ : Gate)).inputs, i < n + 0 + j := by
      intro j hj i hi
      exact hC.2.1 j hj i hi
    have key := sub_aux w hw C.gates 0 L (List.ofFn z) C.output hL0 hM hinv hback C.output
      (by simpa [Circuit.size] using hout)
    simp only [Circuit.eval]
    exact key.symm

lemma getD_eq_false_of_le {l : List Bool} {i : Nat} (h : l.length <= i) : l.getD i false = false := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons x t ih =>
    cases i with
    | zero => simp at h
    | succ i => simpa using ih (by simpa using h)

lemma phi_lt {x1 : Nat} (x2 k : Nat) (hk : k < x1 + x2) :
    (if k < x1 then k else (x1 + x2) + k) < (x1 + x2) + (x1 + x2) := by
  by_cases h : k < x1
  · simp [h]; omega
  · simp [h]; omega

lemma append_pair {n : Nat} (D : Circuit) (hD : PEqualNP.TopForm.IsAO2 (n + n) D)
    (hout : D.output < n + n + D.size) (a b : Nat) (ha : a < n + n) (hb : b < n + n) :
    ∃ E : Circuit, E.size = D.size + 2 ∧ PEqualNP.TopForm.IsAO2 (n + n) E ∧
      E.output = n + n + D.size + 1 ∧
      ∀ L : List Bool, L.length = n + n →
        E.eval L = (D.eval L || (L.getD a false && L.getD b false)) := by
  have hsz : D.size = D.gates.length := rfl
  refine ⟨⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + n + D.size]⟩],
    n + n + D.size + 1⟩, ?_, ?_, rfl, ?_⟩
  · simp [Circuit.size]
  · obtain ⟨hAO, hRB, h2⟩ := hD
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact hAO g hg
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro j hj i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
      by_cases hjd : j < D.gates.length
      · rw [getD_append_left_g (l1 := D.gates) (d := (⟨GateOp.or, []⟩ : Gate)) (i := j) (by omega)] at hi
        have := hRB j hjd i hi
        omega
      · rcases (by omega : j = D.gates.length ∨ j = D.gates.length + 1) with rfl | rfl
        · rw [getD_concat_two] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
        · rw [getD_concat_two_succ] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact h2 g hg
      · rfl
      · rfl
  · intro L hL
    have hlen : (D.wires L).length = n + n + D.size := by rw [wires_length]; omega
    have e1 : (D.wires L).getD a false = L.getD a false :=
      wires_getD_input D.gates D.output L (by omega)
    have e2 : (D.wires L).getD b false = L.getD b false :=
      wires_getD_input D.gates D.output L (by omega)
    have hcomp : (⟨D.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [D.output, n + n + D.size]⟩],
        n + n + D.size + 1⟩ : Circuit).wires L
        = (D.wires L ++ [L.getD a false && L.getD b false]) ++
            [(D.eval L || (L.getD a false && L.getD b false))] := by
      rw [wires_append, wires_two]
      rw [show (⟨D.gates, n + n + D.size + 1⟩ : Circuit).wires L = D.wires L from rfl]
      simp only [List.map_cons, List.map_nil, and_eval_pair, or_eval_pair]
      rw [e1, e2]
      rw [List.append_assoc, List.singleton_append]
      rw [getD_append_left (l1 := D.wires L) (i := D.output) (by omega)]
      rw [← hlen]
      rw [getD_append_self_g (l := D.wires L) (a := (L.getD a false && L.getD b false)) (d := false)]
      rw [show (D.wires L).getD D.output false = D.eval L from rfl]
    have hidx : (D.wires L ++ [L.getD a false && L.getD b false]).length
        = n + n + D.size + 1 := by
      rw [List.length_append, hlen]; simp
    rw [Circuit.eval, hcomp, ← hidx, getD_append_self_g]

lemma ofFn_getD {m : Nat} (y : Fin m → Bool) {i : Nat} (hi : i < m) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp [List.getD, hi]

lemma ofFn_castAdd {n : Nat} (y : Fin (n + n) → Bool) (a : Fin n) :
    y (Fin.castAdd n a) = (List.ofFn y).getD a.val false := by
  have h2 : a.val < n + n := by have := a.isLt; omega
  have h1 : (Fin.castAdd n a) = (⟨a.val, h2⟩ : Fin (n + n)) := Fin.ext rfl
  rw [h1]
  exact (ofFn_getD y h2).symm

lemma ofFn_natAdd {n : Nat} (y : Fin (n + n) → Bool) (a : Fin n) :
    y (Fin.natAdd n a) = (List.ofFn y).getD (n + a.val) false := by
  have h2 : n + a.val < n + n := by have := a.isLt; omega
  have h1 : (Fin.natAdd n a) = (⟨n + a.val, h2⟩ : Fin (n + n)) := Fin.ext rfl
  rw [h1]
  exact (ofFn_getD y h2).symm

lemma chain {n : Nat} (D : Circuit) (hD : PEqualNP.TopForm.IsAO2 (n + n) D)
    (hout : D.output < (n + n) + D.size) (S : Finset (Fin n × Fin n)) :
    ∃ E : Circuit, PEqualNP.TopForm.IsAO2 (n + n) E ∧ E.size = D.size + 2 * S.card ∧
      E.output < (n + n) + E.size ∧
      ∀ L : List Bool, L.length = n + n →
        E.eval L = (D.eval L ||
          decide (∃ p ∈ S, L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true)) := by
  classical
  induction S using Finset.induction with
  | empty =>
      refine ⟨D, hD, by simp, hout, ?_⟩
      intro L hL
      simp
  | insert a S ha ih =>
      obtain ⟨E, hE, hsz, houtE, hev⟩ := ih
      have ha1 : a.1.val < n + n := by have := a.1.isLt; omega
      have ha2 : n + a.2.val < n + n := by have := a.2.isLt; omega
      obtain ⟨E', hE'sz, hE', hE'out, hE'ev⟩ :=
        append_pair E hE houtE a.1.val (n + a.2.val) ha1 ha2
      refine ⟨E', hE', ?_, ?_, ?_⟩
      · rw [hE'sz, hsz, Finset.card_insert_of_notMem ha]
        ring
      · rw [hE'out, hE'sz]
        omega
      · intro L hL
        rw [hE'ev L hL, hev L hL]
        have hiff : (∃ p ∈ insert a S,
              (L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true))
            ↔ ((L.getD a.1.val false = true ∧ L.getD (n + a.2.val) false = true) ∨
                ∃ p ∈ S, (L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true)) := by
          constructor
          · rintro ⟨p, hp, h1, h2⟩
            rcases Finset.mem_insert.1 hp with rfl | hpS
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨p, hpS, h1, h2⟩
          · rintro (⟨h1, h2⟩ | ⟨p, hp, h1, h2⟩)
            · exact ⟨a, Finset.mem_insert_self a S, h1, h2⟩
            · exact ⟨p, Finset.mem_insert_of_mem hp, h1, h2⟩
        have hdec : decide (∃ p ∈ insert a S,
              (L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true))
            = ((L.getD a.1.val false && L.getD (n + a.2.val) false) ||
                decide (∃ p ∈ S,
                  (L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true))) := by
          simp only [hiff]
          simp [Bool.decide_eq_true]
        rw [hdec, Bool.or_assoc,
          Bool.or_comm (decide (∃ p ∈ S,
            (L.getD p.1.val false = true ∧ L.getD (n + p.2.val) false = true)))]


end PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 :
∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by

  intro x1 x2 x3 x4 hne hAO hfun
  classical
  dsimp only
  intro x10
  have hout : x4.output < (x1 + x2) + x4.size := by
    by_contra hcon
    push Not at hcon
    have hT : circuitFun (x1 + x2) x4 (fun _ => true) = true := by
      rw [hfun]
      obtain ⟨⟨i0, j0⟩, hi0⟩ := hne
      exact decide_eq_true_eq.mpr ⟨i0, j0, hi0, rfl, rfl⟩
    have hlen : (x4.wires (List.ofFn fun _ : Fin (x1 + x2) => true)).length
        = (x1 + x2) + x4.size := by
      rw [wires_length]
      simp [Circuit.size]
    have hF : circuitFun (x1 + x2) x4 (fun _ => true) = false := by
      simp only [circuitFun, Circuit.eval]
      exact getD_eq_false_of_le (by omega)
    rw [hF] at hT
    exact Bool.noConfusion hT
  obtain ⟨D, hDsz, hDAO, hDout, hDev⟩ := sub_circuit (n := x1 + x2) (m := (x1 + x2) + (x1 + x2))
    (fun k => if k < x1 then k else (x1 + x2) + k) (fun k hk => phi_lt x2 k hk) hAO hout
  obtain ⟨E, hEAO, hEsz, hEout, hEev⟩ := chain (n := x1 + x2) D hDAO hDout x10
  refine ⟨E, hEAO, ?_, ?_⟩
  · rw [hEsz, hDsz]
  · intro y
    have hL : (List.ofFn y).length = (x1 + x2) + (x1 + x2) := by simp
    have hD9 : D.eval (List.ofFn y) = decide (∃ p ∈ x3.image (fun p : Fin x1 × Fin x2 =>
          (Fin.castAdd x2 p.1, Fin.natAdd x1 p.2)),
        (List.ofFn y).getD p.1.val false = true ∧
          (List.ofFn y).getD ((x1 + x2) + p.2.val) false = true) := by
      rw [hDev (List.ofFn y) _ hL (fun k => rfl), hfun]
      congr 1
      apply propext
      constructor
      · rintro ⟨i, j, hij, h1, h2⟩
        refine ⟨(Fin.castAdd x2 i, Fin.natAdd x1 j), ?_, ?_, ?_⟩
        · exact Finset.mem_image_of_mem _ hij
        · simpa [Fin.val_castAdd, i.isLt] using h1
        · simpa [Fin.val_natAdd, Nat.add_assoc, show ¬ (x1 + j.val < x1) from by omega] using h2
      · rintro ⟨p, hp, h1, h2⟩
        obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.1 hp
        refine ⟨i, j, hij, ?_, ?_⟩
        · simpa [Fin.val_castAdd, i.isLt] using h1
        · simpa [Fin.val_natAdd, Nat.add_assoc, show ¬ (x1 + j.val < x1) from by omega] using h2
    have hun : (∃ x13 : Fin (x1 + x2), ∃ x14 : Fin (x1 + x2),
          (x13, x14) ∈ x3.image (fun p : Fin x1 × Fin x2 => (Fin.castAdd x2 p.1, Fin.natAdd x1 p.2)) ∪ x10 ∧
            y (Fin.castAdd (x1 + x2) x13) = true ∧ y (Fin.natAdd (x1 + x2) x14) = true)
        ↔ ((∃ p ∈ x3.image (fun p : Fin x1 × Fin x2 => (Fin.castAdd x2 p.1, Fin.natAdd x1 p.2)),
              (List.ofFn y).getD p.1.val false = true ∧
                (List.ofFn y).getD ((x1 + x2) + p.2.val) false = true)
            ∨ (∃ p ∈ x10, (List.ofFn y).getD p.1.val false = true ∧
                (List.ofFn y).getD ((x1 + x2) + p.2.val) false = true)) := by
      constructor
      · rintro ⟨a, b, hab, h1, h2⟩
        rw [ofFn_castAdd (n := x1 + x2) (y := y)] at h1
        rw [ofFn_natAdd (n := x1 + x2) (y := y)] at h2
        rcases Finset.mem_union.1 hab with hab | hab
        · exact Or.inl ⟨(a, b), hab, h1, h2⟩
        · exact Or.inr ⟨(a, b), hab, h1, h2⟩
      · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
        · refine ⟨p.1, p.2, Finset.mem_union_left _ hp, ?_, ?_⟩
          · rw [ofFn_castAdd (n := x1 + x2) (y := y)]; exact h1
          · rw [ofFn_natAdd (n := x1 + x2) (y := y)]; exact h2
        · refine ⟨p.1, p.2, Finset.mem_union_right _ hp, ?_, ?_⟩
          · rw [ofFn_castAdd (n := x1 + x2) (y := y)]; exact h1
          · rw [ofFn_natAdd (n := x1 + x2) (y := y)]; exact h2
    rw [show circuitFun ((x1 + x2) + (x1 + x2)) E y = E.eval (List.ofFn y) from rfl]
    rw [hEev (List.ofFn y) hL, hD9]
    simp only [hun]
    simp
