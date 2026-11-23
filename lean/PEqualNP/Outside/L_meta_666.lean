import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Fano666

open PEqualNP.CircuitLowerBounds

-- The wire evaluation lemmas are adapted from the project's L-meta-616 proof.
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

private lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

private lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

private lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

private lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

private lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

private lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

private lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])


private def line (w : Fin 7) : Finset (Fin 7) :=
  ({0, 1, 3} : Finset (Fin 7)).image fun u => u + w

private lemma line_card : ∀ w, (line w).card = 3 := by decide

private lemma line_injective : Function.Injective line := by
  unfold Function.Injective
  decide

private def charge (S : Finset (Fin 7)) (w : Fin 7) : ℕ :=
  if (S.card = 2 ∧ S ⊆ line w) ∨ (S.card = 4 ∧ line w ⊆ S) then 2
  else if S.card = 5 ∧ line w ⊆ S then 1 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
private lemma column_bound : ∀ S : Finset (Fin 7), (∑ w, charge S w) ≤ 2 := by
  decide

private lemma line_charge_zero (S : Finset (Fin 7)) (h : S.card = 3) (w : Fin 7) :
    charge S w = 0 := by
  simp [charge, h]

private lemma charge_pair {S : Finset (Fin 7)} {w : Fin 7}
    (h : S.card = 2) (hs : S ⊆ line w) : charge S w = 2 := by simp [charge, h, hs]

private lemma charge_four {S : Finset (Fin 7)} {w : Fin 7}
    (h : S.card = 4) (hs : line w ⊆ S) : charge S w = 2 := by simp [charge, h, hs]

private lemma charge_five {S : Finset (Fin 7)} {w : Fin 7}
    (h : S.card = 5) (hs : line w ⊆ S) : charge S w = 1 := by simp [charge, h, hs]

private def hot (v : Fin 7) : Fin 7 → Bool := fun i => decide (i = v)

private def wire (gs : List Gate) (k : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter fun v =>
    ((⟨gs, 0⟩ : Circuit).wires (List.ofFn (hot v))).getD k false = true

private lemma mem_wire (gs : List Gate) (k : ℕ) (v : Fin 7) :
    v ∈ wire gs k ↔ ((⟨gs, 0⟩ : Circuit).wires (List.ofFn (hot v))).getD k false = true := by
  simp [wire]

private lemma wire_initial (gs : List Gate) (i : ℕ) (hi : i < 7) :
    wire gs i = {⟨i, hi⟩} := by
  ext v
  rw [mem_wire, wires_input _ _ _ hi]
  simp [hot, eq_comm]

private lemma wire_missing (gs : List Gate) (i : ℕ) (hi : 7 + gs.length ≤ i) :
    wire gs i = ∅ := by
  ext v
  rw [mem_wire, wires_oob _ _ _ hi]
  simp

private def read (gs : List Gate) (j i : ℕ) : Finset (Fin 7) :=
  if i < 7 + j then wire gs i else ∅

private lemma mem_read (gs : List Gate) (j i : ℕ) (v : Fin 7) :
    v ∈ read gs j i ↔
      (if i < 7 + j then ((⟨gs, 0⟩ : Circuit).wires (List.ofFn (hot v))).getD i false
        else false) = true := by
  by_cases h : i < 7 + j <;> simp [read, h, mem_wire]

private lemma binary_union (gs : List Gate) {j : ℕ} {g : Gate} (hg : gs[j]? = some g)
    (hop : g.op = GateOp.or) {a b : ℕ} (hi : g.inputs = [a,b]) :
    wire gs (7 + j) = read gs j a ∪ read gs j b := by
  ext v
  rw [mem_wire, wires_gate_ofFn _ _ _ _ hg, hop, hi, Finset.mem_union, mem_read, mem_read]
  simp [GateOp.eval]

private lemma binary_inter (gs : List Gate) {j : ℕ} {g : Gate} (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and) {a b : ℕ} (hi : g.inputs = [a,b]) :
    wire gs (7 + j) = read gs j a ∩ read gs j b := by
  ext v
  rw [mem_wire, wires_gate_ofFn _ _ _ _ hg, hop, hi, Finset.mem_inter, mem_read, mem_read]
  simp [GateOp.eval]

private lemma unary (gs : List Gate) {j : ℕ} {g : Gate} (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a : ℕ} (hi : g.inputs = [a]) :
    wire gs (7 + j) = read gs j a := by
  ext v
  rw [mem_wire, wires_gate_ofFn _ _ _ _ hg, hi, mem_read]
  rcases hop with h | h <;> simp [h, GateOp.eval]

private lemma nullary (gs : List Gate) {j : ℕ} {g : Gate} (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hi : g.inputs = []) :
    wire gs (7 + j) = Finset.univ ∨ wire gs (7 + j) = ∅ := by
  rcases hop with h | h
  · left
    ext v
    rw [mem_wire, wires_gate_ofFn _ _ _ _ hg, hi]
    simp [h, GateOp.eval]
  · right
    ext v
    rw [mem_wire, wires_gate_ofFn _ _ _ _ hg, hi]
    simp [h, GateOp.eval]

private lemma read_gate (gs : List Gate) {j i : ℕ} (h : 2 ≤ (read gs j i).card) :
    ∃ k : ℕ, k < j ∧ i = 7 + k ∧ read gs j i = wire gs (7 + k) := by
  have hi : i < 7 + j := by
    by_contra hn
    simp [read, hn] at h
  have hstart : 7 ≤ i := by
    by_contra hn
    have hh : i < 7 := by omega
    simp [read, hi, wire_initial gs i hh] at h
  have he : i = 7 + (i - 7) := by omega
  refine ⟨i - 7, by omega, he, ?_⟩
  simp only [read, ite_eq_left hi]
  rw [← he]

private lemma read_ne_line (gs : List Gate) (w : Fin 7) {j i : ℕ}
    (hprev : ∀ k < j, wire gs (7 + k) ≠ line w) :
    read gs j i ≠ line w := by
  intro h
  have hc : 2 ≤ (read gs j i).card := by rw [h, line_card]; decide
  obtain ⟨k, hk, _, he⟩ := read_gate gs hc
  exact hprev k hk (he.symm.trans h)

private lemma line_union (w : Fin 7) (P Q : Finset (Fin 7))
    (h : P ∪ Q = line w) (hp : P ≠ line w) (hq : Q ≠ line w) :
    (P.card = 2 ∧ charge P w = 2) ∨ (Q.card = 2 ∧ charge Q w = 2) := by
  have hps : P ⊆ line w := h ▸ Finset.subset_union_left
  have hqs : Q ⊆ line w := h ▸ Finset.subset_union_right
  have hcP : P.card < 3 := by
    simpa only [line_card] using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hps,hp⟩)
  have hcQ : Q.card < 3 := by
    simpa only [line_card] using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hqs,hq⟩)
  have hsum : 3 ≤ P.card + Q.card := by
    simpa only [h, line_card] using Finset.card_union_le (s := P) (t := Q)
  by_cases hP : P.card = 2
  · exact Or.inl ⟨hP, charge_pair hP hps⟩
  · have hQ : Q.card = 2 := by omega
    exact Or.inr ⟨hQ, charge_pair hQ hqs⟩

private lemma line_inter (w : Fin 7) (P Q : Finset (Fin 7))
    (h : P ∩ Q = line w) (hp : P ≠ line w) (hq : Q ≠ line w) :
    (P.card = 4 ∧ charge P w = 2) ∨ (Q.card = 4 ∧ charge Q w = 2) ∨
      (P.card = 5 ∧ Q.card = 5 ∧ charge P w = 1 ∧ charge Q w = 1 ∧ P ≠ Q) := by
  have hps : line w ⊆ P := h ▸ Finset.inter_subset_left
  have hqs : line w ⊆ Q := h ▸ Finset.inter_subset_right
  have hcP : 3 < P.card := by
    simpa only [line_card] using
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hps, Ne.symm hp⟩)
  have hcQ : 3 < Q.card := by
    simpa only [line_card] using
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hqs, Ne.symm hq⟩)
  by_cases hP : P.card = 4
  · exact Or.inl ⟨hP, charge_four hP hps⟩
  by_cases hQ : Q.card = 4
  · exact Or.inr (Or.inl ⟨hQ, charge_four hQ hqs⟩)
  have hsize : (P ∪ Q).card ≤ 7 := by simpa using Finset.card_le_univ (P ∪ Q)
  have hc := Finset.card_union_add_card_inter P Q
  rw [h, line_card] at hc
  have hp5 : P.card = 5 := by omega
  have hq5 : Q.card = 5 := by omega
  refine Or.inr (Or.inr ⟨hp5, hq5, charge_five hp5 hps, charge_five hq5 hqs, ?_⟩)
  intro he
  exact hp (by simpa [← he] using h)

private def gateSet (gs : List Gate) (i : Fin gs.length) : Finset (Fin 7) :=
  wire gs (7 + i.val)

private lemma charge_two_of_read (gs : List Gate) (w : Fin 7) {j i : ℕ}
    (hj : j < gs.length) (hc : 2 ≤ (read gs j i).card) (h : charge (read gs j i) w = 2) :
    ∃ k : Fin gs.length, charge (gateSet gs k) w = 2 := by
  obtain ⟨k, hk, _, he⟩ := read_gate gs hc
  refine ⟨⟨k, lt_trans hk hj⟩, ?_⟩
  simpa only [gateSet, ← he] using h

private lemma charge_two_reads (gs : List Gate) (w : Fin 7) {j i k : ℕ}
    (hj : j < gs.length) (hi : 2 ≤ (read gs j i).card) (hk : 2 ≤ (read gs j k).card)
    (ci : charge (read gs j i) w = 1) (ck : charge (read gs j k) w = 1)
    (hne : read gs j i ≠ read gs j k) :
    ∃ a b : Fin gs.length, a ≠ b ∧ charge (gateSet gs a) w = 1 ∧ charge (gateSet gs b) w = 1 := by
  obtain ⟨a, ha, _, ea⟩ := read_gate gs hi
  obtain ⟨b, hb, _, eb⟩ := read_gate gs hk
  refine ⟨⟨a, lt_trans ha hj⟩, ⟨b, lt_trans hb hj⟩, ?_, ?_, ?_⟩
  · intro he
    apply hne
    have hval := congrArg Fin.val he
    exact ea.trans ((congrArg (fun v => wire gs (7 + v)) hval).trans eb.symm)
  · simpa only [gateSet, ← ea] using ci
  · simpa only [gateSet, ← eb] using ck

private lemma first_charge (gs : List Gate) (w : Fin 7) (j : Fin gs.length)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw : gateSet gs j = line w)
    (hprev : ∀ k < j.val, wire gs (7 + k) ≠ line w) :
    (∃ k : Fin gs.length, charge (gateSet gs k) w = 2) ∨
      (∃ a b : Fin gs.length, a ≠ b ∧ charge (gateSet gs a) w = 1 ∧ charge (gateSet gs b) w = 1) := by
  let g := gs[j.val]
  have hg : gs[j.val]? = some g := List.getElem?_eq_getElem j.isLt
  have hm : g ∈ gs := List.getElem_mem j.isLt
  obtain ⟨hop, hlen⟩ := hops g hm
  have hw' : wire gs (7 + j.val) = line w := hw
  cases hinputs : g.inputs with
  | nil =>
    have hc := nullary gs hg hop hinputs
    rw [hw'] at hc
    rcases hc with he | he
    · have he' := congrArg Finset.card he
      simp [line_card] at he'
    · have he' := congrArg Finset.card he
      simp [line_card] at he'
  | cons a tail =>
    cases tail with
    | nil =>
      have he := unary gs hg hop hinputs
      exact (read_ne_line gs w hprev (he.symm.trans hw')).elim
    | cons b tail =>
      cases tail with
      | nil =>
        have ha := read_ne_line gs w (i := a) hprev
        have hb := read_ne_line gs w (i := b) hprev
        rcases hop with hop | hop
        · have he := (binary_inter gs hg hop hinputs).symm.trans hw'
          rcases line_inter w _ _ he ha hb with ⟨hs, hc⟩ | ⟨hs, hc⟩ | ⟨hs, ht, hc, hd, hne⟩
          · exact Or.inl (charge_two_of_read gs w j.isLt (by omega) hc)
          · exact Or.inl (charge_two_of_read gs w j.isLt (by omega) hc)
          · exact Or.inr (charge_two_reads gs w j.isLt (by omega) (by omega) hc hd hne)
        · have he := (binary_union gs hg hop hinputs).symm.trans hw'
          rcases line_union w _ _ he ha hb with ⟨hs, hc⟩ | ⟨hs, hc⟩
          · exact Or.inl (charge_two_of_read gs w j.isLt (by omega) hc)
          · exact Or.inl (charge_two_of_read gs w j.isLt (by omega) hc)
      | cons c tail =>
        simp only [hinputs, List.length_cons] at hlen
        omega

private lemma row_bound (gs : List Gate) (w : Fin 7)
    (h : (∃ k : Fin gs.length, charge (gateSet gs k) w = 2) ∨
      (∃ a b : Fin gs.length, a ≠ b ∧ charge (gateSet gs a) w = 1 ∧ charge (gateSet gs b) w = 1)) :
    2 ≤ ∑ i : Fin gs.length, charge (gateSet gs i) w := by
  rcases h with ⟨k, hk⟩ | ⟨a, b, hn, ha, hb⟩
  · rw [← hk]
    exact Finset.single_le_sum (f := fun i => charge (gateSet gs i) w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  · have hsum : (∑ i ∈ ({a,b} : Finset (Fin gs.length)), charge (gateSet gs i) w) = 2 := by
      rw [Finset.sum_pair hn, ha, hb]
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

private lemma output_line (gs : List Gate) (out : Fin 7 → ℕ)
    (hm : ∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j, x i = true → x j = true → i = j) →
      (⟨gs, out w⟩ : Circuit).eval (List.ofFn x) = decide (∃ v ∈ line w, x v = true))
    (w : Fin 7) : ∃ j : ℕ, j < gs.length ∧ wire gs (7 + j) = line w := by
  have hwire : wire gs (out w) = line w := by
    ext v
    have hv : ∀ i j, hot v i = true → hot v j = true → i = j := by
      intro i j hi hj
      simp only [hot, decide_eq_true_eq] at hi hj
      exact hi.trans hj.symm
    have he := hm w (hot v) hv
    change ((⟨gs, 0⟩ : Circuit).wires (List.ofFn (hot v))).getD (out w) false = _ at he
    rw [mem_wire, he, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, hv'⟩
      have hi' : i = v := by simpa [hot] using hv'
      rwa [hi'] at hi
    · intro hv'
      exact ⟨v, hv', by simp [hot]⟩
  have hge : 7 ≤ out w := by
    by_contra hh
    have hs : out w < 7 := by omega
    have hc := congrArg Finset.card ((wire_initial gs (out w) hs).symm.trans hwire)
    simp [line_card] at hc
  have hlt : out w < 7 + gs.length := by
    by_contra hh
    have hs : 7 + gs.length ≤ out w := by omega
    have hc := congrArg Finset.card ((wire_missing gs (out w) hs).symm.trans hwire)
    simp [line_card] at hc
  refine ⟨out w - 7, by omega, ?_⟩
  have he : 7 + (out w - 7) = out w := by omega
  rwa [he]

private lemma count_gates (gs : List Gate)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (exists_line : ∀ w : Fin 7, ∃ j : ℕ, j < gs.length ∧ wire gs (7 + j) = line w) :
    14 ≤ gs.length := by
  classical
  let target (w : Fin 7) : Fin gs.length :=
    ⟨Nat.find (exists_line w), (Nat.find_spec (exists_line w)).1⟩
  have ht (w : Fin 7) : gateSet gs (target w) = line w := (Nat.find_spec (exists_line w)).2
  have hprev (w : Fin 7) : ∀ k < (target w).val, wire gs (7 + k) ≠ line w := by
    intro k hk he
    have hk' : k < gs.length := lt_trans hk (target w).isLt
    exact Nat.not_le_of_lt hk (Nat.find_min' (exists_line w) ⟨hk', he⟩)
  have hinj : Function.Injective target := by
    intro a b h
    exact line_injective ((ht a).symm.trans ((congrArg (gateSet gs) h).trans (ht b)))
  let vertices : Finset (Fin gs.length) := Finset.univ
  let aux := vertices.filter fun j => (gateSet gs j).card ≠ 3
  let declared := vertices.filter fun j => (gateSet gs j).card = 3
  have hlines : 7 ≤ declared.card := by
    calc
      7 = (Finset.univ.image target).card := by
        rw [Finset.card_image_of_injective _ hinj]
        simp
      _ ≤ declared.card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hi
        simp [declared, vertices, ht, line_card]
  have hcharge :
      14 ≤ 2 * aux.card := by
    calc
      14 = ∑ _ : Fin 7, (2 : ℕ) := by simp
      _ ≤ ∑ w : Fin 7, ∑ i : Fin gs.length, charge (gateSet gs i) w :=
        Finset.sum_le_sum fun w _ => row_bound gs w (first_charge gs w (target w) hops (ht w) (hprev w))
      _ = ∑ i : Fin gs.length, ∑ w : Fin 7, charge (gateSet gs i) w := Finset.sum_comm
      _ = ∑ i ∈ aux, ∑ w : Fin 7, charge (gateSet gs i) w := by
        rw [show aux = Finset.univ.filter (fun j => (gateSet gs j).card ≠ 3) from rfl, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : (gateSet gs i).card = 3
        · simp [h, line_charge_zero _ h]
        · simp [h]
      _ ≤ ∑ _ ∈ aux, (2 : ℕ) := Finset.sum_le_sum fun i _ => column_bound (gateSet gs i)
      _ = 2 * aux.card := by simp [Nat.mul_comm]
  have hsplit : declared.card + aux.card = gs.length := by
    unfold declared aux
    rw [Finset.card_filter_add_card_filter_not]
    simp [vertices]
  omega

end PEqualNP.Outside.Fano666

namespace PEqualNP.Outside

theorem L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  intro gates out hops correctness
  exact Fano666.count_gates gates hops (Fano666.output_line gates out correctness)

end PEqualNP.Outside
