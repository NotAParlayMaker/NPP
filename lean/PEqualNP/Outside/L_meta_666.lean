import Mathlib
import PEqualNP.Defs

namespace Gap666

open PEqualNP.CircuitLowerBounds

def wv (gates : List Gate) (x : List Bool) (k : ℕ) : Bool :=
  (Circuit.wires ⟨gates, 0⟩ x).getD k false

theorem eval_eq_wv (gates : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gates, o⟩ x = wv gates x o := rfl

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq_foldl (gates : List Gate) (x : List Bool) :
    Circuit.wires ⟨gates, 0⟩ x = gates.foldl stepF x := rfl

theorem foldl_stepF_append (hs : List Gate) :
    ∀ w : List Bool, ∃ t : List Bool, hs.foldl stepF w = w ++ t := by
  induction hs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons h hs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepF w h)
    refine ⟨[h.op.eval (h.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [stepF]

theorem foldl_stepF_length (hs : List Gate) :
    ∀ w : List Bool, (hs.foldl stepF w).length = w.length + hs.length := by
  induction hs with
  | nil => intro w; simp
  | cons h hs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepF]
    omega

theorem wv_ge (gates : List Gate) (x : List Bool) (k : ℕ)
    (hk : x.length + gates.length ≤ k) : wv gates x k = false := by
  unfold wv
  rw [wires_eq_foldl]
  apply List.getD_eq_default
  rw [foldl_stepF_length]
  exact hk

theorem wv_input (gates : List Gate) (x : List Bool) (k : ℕ) (hk : k < x.length) :
    wv gates x k = x.getD k false := by
  unfold wv
  rw [wires_eq_foldl]
  obtain ⟨t, ht⟩ := foldl_stepF_append gates x
  rw [ht, List.getD_append _ _ _ _ hk]

theorem wv_gate (gates : List Gate) (x : List Bool) (j : ℕ) (hj : j < gates.length) :
    wv gates x (x.length + j) = (gates[j]).op.eval
      ((gates[j]).inputs.map fun i => if i < x.length + j then wv gates x i else false) := by
  have hsplit : gates = gates.take j ++ gates[j] :: gates.drop (j + 1) := by
    simp
  have hlen : ((gates.take j).foldl stepF x).length = x.length + j := by
    rw [foldl_stepF_length, List.length_take, Nat.min_eq_left hj.le]
  obtain ⟨t, ht⟩ := foldl_stepF_append (gates.drop (j + 1))
    (stepF ((gates.take j).foldl stepF x) gates[j])
  have hw : gates.foldl stepF x = (gates.take j).foldl stepF x ++
      ([(gates[j]).op.eval ((gates[j]).inputs.map
        fun i => ((gates.take j).foldl stepF x).getD i false)] ++ t) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, ht]
    simp [stepF]
  have hpre : ∀ i : ℕ, ((gates.take j).foldl stepF x).getD i false =
      if i < x.length + j then wv gates x i else false := by
    intro i
    by_cases hi : i < x.length + j
    · rw [if_pos hi]
      unfold wv
      rw [wires_eq_foldl, hw, List.getD_append _ _ _ _ (by rw [hlen]; exact hi)]
    · rw [if_neg hi]
      apply List.getD_eq_default
      rw [hlen]
      omega
  unfold wv
  rw [wires_eq_foldl]
  conv_lhs => rw [hw]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self]
  simp only [List.singleton_append, List.getD_cons_zero]
  congr 2
  funext i
  exact hpre i

def e0 : Fin 7 → Bool := fun _ => false

def e1 (i : Fin 7) : Fin 7 → Bool := fun j => decide (j = i)

def zt (gates : List Gate) (k : ℕ) : Bool := wv gates (List.ofFn e0) k

def St (gates : List Gate) (k : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter fun i => wv gates (List.ofFn (e1 i)) k = true

def zr (gates : List Gate) (j a : ℕ) : Bool := if a < 7 + j then zt gates a else false

def Sr (gates : List Gate) (j a : ℕ) : Finset (Fin 7) := if a < 7 + j then St gates a else ∅

theorem mem_St (gates : List Gate) (k : ℕ) (i : Fin 7) :
    i ∈ St gates k ↔ wv gates (List.ofFn (e1 i)) k = true := by
  simp [St]

theorem mem_Sr (gates : List Gate) (j a : ℕ) (i : Fin 7) :
    i ∈ Sr gates j a ↔ (if a < 7 + j then wv gates (List.ofFn (e1 i)) a else false) = true := by
  unfold Sr
  split_ifs with h
  · exact mem_St gates a i
  · simp

theorem zt_input (gates : List Gate) (i : Fin 7) : zt gates i = false := by
  unfold zt
  rw [wv_input _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rfl

theorem St_input (gates : List Gate) (i : Fin 7) : St gates i = {i} := by
  ext m
  rw [mem_St, wv_input _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  simp [e1, eq_comm]

theorem zt_ge (gates : List Gate) (k : ℕ) (hk : 7 + gates.length ≤ k) : zt gates k = false := by
  unfold zt
  exact wv_ge _ _ _ (by simpa using hk)

theorem St_ge (gates : List Gate) (k : ℕ) (hk : 7 + gates.length ≤ k) : St gates k = ∅ := by
  ext m
  rw [mem_St, wv_ge _ _ _ (by simpa using hk)]
  simp

theorem zt_gate (gates : List Gate) (j : ℕ) (hj : j < gates.length) :
    zt gates (7 + j) = (gates[j]).op.eval ((gates[j]).inputs.map fun a => zr gates j a) := by
  have h := wv_gate gates (List.ofFn e0) j hj
  simp only [List.length_ofFn] at h
  exact h

theorem mem_St_gate (gates : List Gate) (j : ℕ) (hj : j < gates.length) (i : Fin 7) :
    i ∈ St gates (7 + j) ↔ (gates[j]).op.eval ((gates[j]).inputs.map
      fun a => decide (i ∈ Sr gates j a)) = true := by
  rw [mem_St]
  have h := wv_gate gates (List.ofFn (e1 i)) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  have : (fun a => if a < 7 + j then wv gates (List.ofFn (e1 i)) a else false) =
      fun a => decide (i ∈ Sr gates j a) := by
    funext a
    rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_Sr]
  rw [this]

theorem zt_and_nil (gates : List Gate) (j : ℕ) (hj : j < gates.length)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = []) :
    zt gates (7 + j) = true := by
  rw [zt_gate gates j hj, hop, hin]; rfl

theorem St_and_nil (gates : List Gate) (j : ℕ) (hj : j < gates.length)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = []) :
    St gates (7 + j) = Finset.univ := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem zt_or_nil (gates : List Gate) (j : ℕ) (hj : j < gates.length)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = []) :
    zt gates (7 + j) = false := by
  rw [zt_gate gates j hj, hop, hin]; rfl

theorem St_or_nil (gates : List Gate) (j : ℕ) (hj : j < gates.length)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = []) :
    St gates (7 + j) = ∅ := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem zt_and_one (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a : ℕ)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = [a]) :
    zt gates (7 + j) = zr gates j a := by
  rw [zt_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem St_and_one (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a : ℕ)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = [a]) :
    St gates (7 + j) = Sr gates j a := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem zt_or_one (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a : ℕ)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = [a]) :
    zt gates (7 + j) = zr gates j a := by
  rw [zt_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem St_or_one (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a : ℕ)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = [a]) :
    St gates (7 + j) = Sr gates j a := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem zt_and_two (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a b : ℕ)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = [a, b]) :
    zt gates (7 + j) = (zr gates j a && zr gates j b) := by
  rw [zt_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem St_and_two (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a b : ℕ)
    (hop : (gates[j]).op = GateOp.and) (hin : (gates[j]).inputs = [a, b]) :
    St gates (7 + j) = Sr gates j a ∩ Sr gates j b := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem zt_or_two (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a b : ℕ)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = [a, b]) :
    zt gates (7 + j) = (zr gates j a || zr gates j b) := by
  rw [zt_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem St_or_two (gates : List Gate) (j : ℕ) (hj : j < gates.length) (a b : ℕ)
    (hop : (gates[j]).op = GateOp.or) (hin : (gates[j]).inputs = [a, b]) :
    St gates (7 + j) = Sr gates j a ∪ Sr gates j b := by
  ext i
  rw [mem_St_gate gates j hj, hop, hin]
  simp [GateOp.eval]

theorem trace_of_hyp (gates : List Gate) (out : Fin 7 → ℕ)
    (hyp : ∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true))
    (w : Fin 7) :
    zt gates (out w) = false ∧
      St gates (out w) = ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w) := by
  constructor
  · have h := hyp w e0 (by intro i j hi; simp [e0] at hi)
    rw [eval_eq_wv] at h
    unfold zt
    rw [h]
    simp [e0]
  · ext i
    have h := hyp w (e1 i) (by
      intro a b ha hb
      simp only [e1, decide_eq_true_eq] at ha hb
      rw [ha, hb])
    rw [eval_eq_wv] at h
    rw [mem_St, h]
    simp only [e1, decide_eq_true_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hi
      exact ⟨i, hi, rfl⟩

theorem Sr_avail (gates : List Gate) (j a : ℕ) :
    Sr gates j a = ∅ ∨ ∃ c, c < 7 + j ∧ Sr gates j a = St gates c := by
  unfold Sr
  split_ifs with h
  · exact Or.inr ⟨a, h, rfl⟩
  · exact Or.inl rfl

theorem line_ne_singleton : ∀ w i : Fin 7,
    ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w) ≠ {i} := by
  decide

theorem line_ne_empty : ∀ w : Fin 7,
    ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w) ≠ ∅ := by
  decide

theorem model_of_hyp (gates : List Gate) (out : Fin 7 → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hyp : ∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) :
    ∃ S : ℕ → Finset (Fin 7), (∀ i : Fin 7, S i = {i}) ∧
      (∀ j, j < gates.length → S (7 + j) = Finset.univ ∨ ∃ P Q : Finset (Fin 7),
        (P = ∅ ∨ ∃ a, a < 7 + j ∧ P = S a) ∧ (Q = ∅ ∨ ∃ b, b < 7 + j ∧ Q = S b) ∧
        (S (7 + j) = P ∪ Q ∨ S (7 + j) = P ∩ Q)) ∧
      ∀ w : Fin 7, ∃ j, j < gates.length ∧
        S (7 + j) = ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w) := by
  refine ⟨St gates, St_input gates, ?_, ?_⟩
  · intro j hj
    obtain ⟨hop, hlen⟩ := hg gates[j] (List.getElem_mem hj)
    rcases hin : (gates[j]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · rcases hop with hop | hop
      · exact Or.inl (St_and_nil gates j hj hop hin)
      · exact Or.inr ⟨∅, ∅, Or.inl rfl, Or.inl rfl,
          Or.inl (by rw [St_or_nil gates j hj hop hin]; simp)⟩
    · refine Or.inr ⟨Sr gates j a, Sr gates j a, Sr_avail gates j a, Sr_avail gates j a,
        Or.inl ?_⟩
      rcases hop with hop | hop
      · rw [St_and_one gates j hj a hop hin]; simp
      · rw [St_or_one gates j hj a hop hin]; simp
    · refine Or.inr ⟨Sr gates j a, Sr gates j b, Sr_avail gates j a, Sr_avail gates j b, ?_⟩
      rcases hop with hop | hop
      · exact Or.inr (St_and_two gates j hj a b hop hin)
      · exact Or.inl (St_or_two gates j hj a b hop hin)
    · rw [hin] at hlen
      simp at hlen
  · intro w
    obtain ⟨-, hS⟩ := trace_of_hyp gates out hyp w
    have h7 : 7 ≤ out w := by
      by_contra hlt
      have hlt' : out w < 7 := by omega
      have h := St_input gates ⟨out w, hlt'⟩
      simp only at h
      rw [hS] at h
      exact line_ne_singleton w _ h
    have hup : out w < 7 + gates.length := by
      by_contra hge
      have h := St_ge gates (out w) (by omega)
      rw [hS] at h
      exact line_ne_empty w h
    refine ⟨out w - 7, by omega, ?_⟩
    have : 7 + (out w - 7) = out w := by omega
    rw [this]
    exact hS

def line666 (w : Fin 7) : Finset (Fin 7) :=
  ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)

def wt666 (P : Finset (Fin 7)) (w : Fin 7) : ℕ :=
  if P = line666 w then 2
  else if P.card = 2 ∧ P ⊆ line666 w then 2
  else if P.card = 4 ∧ line666 w ⊆ P then 2
  else if P.card = 5 ∧ line666 w ⊆ P then 1
  else 0

theorem cardline666 (w : Fin 7) : (line666 w).card = 3 := by
  fin_cases w <;> decide

private theorem line666_inj : ∀ w1 w2 : Fin 7, line666 w1 = line666 w2 → w1 = w2 := by
  decide

private theorem line666_inter_card :
    ∀ w1 w2 : Fin 7, w1 ≠ w2 → (line666 w1 ∩ line666 w2).card = 1 := by
  decide

private theorem line666_avoid_pair_card :
    ∀ a b : Fin 7, a ≠ b →
      (Finset.univ.filter (fun w : Fin 7 => a ∉ line666 w ∧ b ∉ line666 w)).card ≤ 2 := by
  decide

private theorem sum_ite_two_le (p : Fin 7 → Prop) [DecidablePred p]
    (h : ∀ w1 w2 : Fin 7, p w1 → p w2 → w1 = w2) :
    (∑ w : Fin 7, if p w then (2 : ℕ) else 0) ≤ 2 := by
  have hcard : (Finset.univ.filter p).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    exact h w1 w2 (Finset.mem_filter.mp hw1).2 (Finset.mem_filter.mp hw2).2
  have hsum : (∑ w : Fin 7, if p w then (2 : ℕ) else 0) = (Finset.univ.filter p).card * 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  omega

theorem cap666 (P : Finset (Fin 7)) : ∑ w : Fin 7, wt666 P w ≤ 2 := by
  by_cases h3 : P.card = 3
  · have hwt : ∀ w : Fin 7, wt666 P w = if P = line666 w then 2 else 0 := by
      intro w
      unfold wt666
      split_ifs <;> omega
    simp_rw [hwt]
    apply sum_ite_two_le
    intro w1 w2 h1 h2
    exact line666_inj w1 w2 (h1.symm.trans h2)
  · have hne : ∀ w : Fin 7, P ≠ line666 w := by
      intro w hw
      exact h3 (hw ▸ cardline666 w)
    by_cases h2 : P.card = 2
    · have hwt : ∀ w : Fin 7, wt666 P w = if P ⊆ line666 w then 2 else 0 := by
        intro w
        unfold wt666
        have := hne w
        split_ifs <;> simp_all
      simp_rw [hwt]
      apply sum_ite_two_le
      intro w1 w2 h1 h2'
      by_contra hne12
      have hsub : P ⊆ line666 w1 ∩ line666 w2 := Finset.subset_inter h1 h2'
      have hle := Finset.card_le_card hsub
      have hinter := line666_inter_card w1 w2 hne12
      omega
    · by_cases h4 : P.card = 4
      · have hwt : ∀ w : Fin 7, wt666 P w = if line666 w ⊆ P then 2 else 0 := by
          intro w
          unfold wt666
          have := hne w
          split_ifs <;> simp_all
        simp_rw [hwt]
        apply sum_ite_two_le
        intro w1 w2 h1 h2'
        by_contra hne12
        have hsub : line666 w1 ∪ line666 w2 ⊆ P := Finset.union_subset h1 h2'
        have hle := Finset.card_le_card hsub
        have hunion := Finset.card_union_add_card_inter (line666 w1) (line666 w2)
        have hinter := line666_inter_card w1 w2 hne12
        have hc1 := cardline666 w1
        have hc2 := cardline666 w2
        omega
      · by_cases h5 : P.card = 5
        · have hwt : ∀ w : Fin 7, wt666 P w = if line666 w ⊆ P then 1 else 0 := by
            intro w
            unfold wt666
            have := hne w
            split_ifs <;> simp_all
          simp_rw [hwt]
          have hcomp : Pᶜ.card = 2 := by
            have := Finset.card_compl P
            simp [Fintype.card_fin] at this
            omega
          have h1lt : 1 < Pᶜ.card := by omega
          rcases Finset.one_lt_card.mp h1lt with ⟨a, ha, b, hb, hab⟩
          have haP : a ∉ P := Finset.mem_compl.mp ha
          have hbP : b ∉ P := Finset.mem_compl.mp hb
          have hsum : (∑ w : Fin 7, if line666 w ⊆ P then (1 : ℕ) else 0) =
              (Finset.univ.filter (fun w : Fin 7 => line666 w ⊆ P)).card := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
          rw [hsum]
          have hsub : Finset.univ.filter (fun w : Fin 7 => line666 w ⊆ P) ⊆
              Finset.univ.filter (fun w : Fin 7 => a ∉ line666 w ∧ b ∉ line666 w) := by
            intro w hw
            have hLw : line666 w ⊆ P := (Finset.mem_filter.mp hw).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, fun h => haP (hLw h), fun h => hbP (hLw h)⟩
          exact le_trans (Finset.card_le_card hsub) (line666_avoid_pair_card a b hab)
        · have hwt : ∀ w : Fin 7, wt666 P w = 0 := by
            intro w
            unfold wt666
            have := hne w
            split_ifs <;> simp_all
          simp [hwt]

theorem wt666_pair (P : Finset (Fin 7)) (w : Fin 7) (hc : P.card = 2) (hs : P ⊆ line666 w) :
    wt666 P w = 2 := by
  unfold wt666
  split_ifs <;> first | rfl | tauto

theorem wt666_four (P : Finset (Fin 7)) (w : Fin 7) (hc : P.card = 4) (hs : line666 w ⊆ P) :
    wt666 P w = 2 := by
  unfold wt666
  split_ifs <;> first | rfl | tauto

theorem wt666_five (P : Finset (Fin 7)) (w : Fin 7) (hc : P.card = 5) (hs : line666 w ⊆ P) :
    1 ≤ wt666 P w := by
  unfold wt666
  split_ifs <;> first | omega | tauto

theorem local666 (P Q : Finset (Fin 7)) (w : Fin 7) (hp : P ≠ line666 w) (hq : Q ≠ line666 w)
    (h : line666 w = P ∪ Q ∨ line666 w = P ∩ Q) :
    2 ≤ wt666 P w ∨ 2 ≤ wt666 Q w ∨ (1 ≤ wt666 P w ∧ 1 ≤ wt666 Q w ∧ P ≠ Q) := by
  have hL := cardline666 w
  rcases h with h | h
  · have hPs : P ⊆ line666 w := by rw [h]; exact Finset.subset_union_left
    have hQs : Q ⊆ line666 w := by rw [h]; exact Finset.subset_union_right
    have hPc : P.card < 3 := by
      rw [← hL]
      exact Finset.card_lt_card (lt_of_le_of_ne hPs hp)
    have hQc : Q.card < 3 := by
      rw [← hL]
      exact Finset.card_lt_card (lt_of_le_of_ne hQs hq)
    have hu : 3 ≤ P.card + Q.card := by
      have := Finset.card_union_le P Q
      rw [← h, hL] at this
      exact this
    by_cases h2 : P.card = 2
    · exact Or.inl (wt666_pair P w h2 hPs).ge
    · exact Or.inr (Or.inl (wt666_pair Q w (by omega) hQs).ge)
  · have hPs : line666 w ⊆ P := by rw [h]; exact Finset.inter_subset_left
    have hQs : line666 w ⊆ Q := by rw [h]; exact Finset.inter_subset_right
    have hPc : 3 < P.card := by
      rw [← hL]
      exact Finset.card_lt_card (lt_of_le_of_ne hPs (Ne.symm hp))
    have hQc : 3 < Q.card := by
      rw [← hL]
      exact Finset.card_lt_card (lt_of_le_of_ne hQs (Ne.symm hq))
    have hsum := Finset.card_union_add_card_inter P Q
    rw [← h, hL] at hsum
    have h7 : (P ∪ Q).card ≤ 7 := by
      have := Finset.card_le_univ (P ∪ Q)
      simpa using this
    by_cases h4 : P.card = 4
    · exact Or.inl (wt666_four P w h4 hPs).ge
    by_cases h4' : Q.card = 4
    · exact Or.inr (Or.inl (wt666_four Q w h4' hQs).ge)
    refine Or.inr (Or.inr ⟨wt666_five P w (by omega) hPs, wt666_five Q w (by omega) hQs, ?_⟩)
    intro hPQ
    rw [← hPQ, Finset.inter_self] at h
    rw [h] at hL
    omega

theorem zeroSmall666 (R : Finset (Fin 7)) (w : Fin 7) (hr : R.card ≤ 1) :
    wt666 R w = 0 := by
  have hl := cardline666 w
  have hne : R ≠ line666 w := by
    intro h
    rw [h] at hr
    omega
  have h2 : R.card ≠ 2 := by omega
  have h4 : R.card ≠ 4 := by omega
  have h5 : R.card ≠ 5 := by omega
  simp [wt666, hne, h2, h4, h5]

theorem posSource666 {S : ℕ → Finset (Fin 7)} (hin : ∀ i : Fin 7, S i = {i})
    {j : ℕ} {R : Finset (Fin 7)} (hr : R = ∅ ∨ ∃ a, a < 7+j ∧ R = S a)
    (w : Fin 7) (hw : 0 < wt666 R w) : ∃ i, i < j ∧ R = S (7+i) := by
  rcases hr with rfl | ⟨a, ha, rfl⟩
  · rw [zeroSmall666 _ _ (by simp)] at hw
    omega
  · by_cases h : a < 7
    · have he := hin ⟨a,h⟩
      change S a = _ at he
      rw [zeroSmall666 _ _ (by rw [he]; simp)] at hw
      omega
    · refine ⟨a-7, by omega, ?_⟩
      congr 1
      omega

theorem four666 (S : ℕ → Finset (Fin 7)) (n : ℕ) (hin : ∀ i : Fin 7, S i = {i})
    (hop : ∀ j, j < n → S (7+j) = Finset.univ ∨ ∃ P Q : Finset (Fin 7),
      (P = ∅ ∨ ∃ a, a < 7+j ∧ P = S a) ∧ (Q = ∅ ∨ ∃ b, b < 7+j ∧ Q = S b) ∧
      (S (7+j) = P ∪ Q ∨ S (7+j) = P ∩ Q))
    (w : Fin 7) (hw : ∃ j, j < n ∧ S (7+j) = line666 w) :
    4 ≤ ∑ i ∈ Finset.range n, wt666 (S (7+i)) w := by
  let j := Nat.find hw
  obtain ⟨hj, he⟩ : j < n ∧ S (7+j) = line666 w := Nat.find_spec hw
  have hown : wt666 (S (7+j)) w = 2 := by simp [he, wt666]
  have strict : ∀ R : Finset (Fin 7), (R = ∅ ∨ ∃ a, a < 7+j ∧ R = S a) → R ≠ line666 w := by
    intro R hr e
    have ht : 0 < wt666 R w := by simp [e, wt666]
    obtain ⟨i, hi, hR⟩ := posSource666 hin hr w ht
    exact Nat.find_min hw hi ⟨by omega, hR.symm.trans e⟩
  obtain hU | ⟨P, Q, hP, hQ, hbit⟩ := hop j hj
  · have hb := cardline666 w
    rw [← he, hU] at hb
    simp at hb
  rw [he] at hbit
  let f := fun i : ℕ => wt666 (S (7+i)) w
  have one : ∀ R : Finset (Fin 7), (R = ∅ ∨ ∃ a, a < 7+j ∧ R = S a) →
      2 ≤ wt666 R w → 2 ≤ ∑ i ∈ Finset.range j, f i := by
    intro R hr ht
    obtain ⟨i, hi, rfl⟩ := posSource666 hin hr w (by omega)
    exact ht.trans (Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi))
  have htwo : 2 ≤ ∑ i ∈ Finset.range j, f i := by
    rcases local666 P Q w (strict P hP) (strict Q hQ) hbit with h | h | ⟨ht, hu, hne⟩
    · exact one P hP h
    · exact one Q hQ h
    · obtain ⟨a, ha, rfl⟩ := posSource666 hin hP w ht
      obtain ⟨b, hb, rfl⟩ := posSource666 hin hQ w hu
      have hab : a ≠ b := by rintro rfl; exact hne rfl
      have hsub : ({a,b} : Finset ℕ) ⊆ Finset.range j := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp [*]
      have hbnd := Finset.sum_le_sum_of_subset (f := f) hsub
      rw [Finset.sum_pair hab] at hbnd
      change 1 ≤ f a at ht
      change 1 ≤ f b at hu
      omega
  have hbnd := Finset.sum_le_sum_of_subset (f := f) (Finset.range_mono (show j+1 ≤ n by omega))
  rw [Finset.sum_range_succ] at hbnd
  change f j = 2 at hown
  change 4 ≤ ∑ i ∈ Finset.range n, f i
  omega

theorem count666 (S : ℕ → Finset (Fin 7)) (n : ℕ) (hin : ∀ i : Fin 7, S i = {i})
    (hop : ∀ j, j < n → S (7+j) = Finset.univ ∨ ∃ P Q : Finset (Fin 7),
      (P = ∅ ∨ ∃ a, a < 7+j ∧ P = S a) ∧ (Q = ∅ ∨ ∃ b, b < 7+j ∧ Q = S b) ∧
      (S (7+j) = P ∪ Q ∨ S (7+j) = P ∩ Q))
    (hw : ∀ w : Fin 7, ∃ j, j < n ∧ S (7+j) = line666 w) : 14 ≤ n := by
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun (w : Fin 7) _ => four666 S n hin hop w (hw w))
  have hu := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => cap666 (S (7+i)))
  rw [Finset.sum_comm] at hl
  simp at hl hu
  omega

end Gap666

theorem PEqualNP.Outside.L_meta_666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) → 14 ≤ gates.length := by
  intro gates out hg hyp
  obtain ⟨S, hin, hop, hw⟩ := Gap666.model_of_hyp gates out hg hyp
  exact Gap666.count666 S gates.length hin hop hw
