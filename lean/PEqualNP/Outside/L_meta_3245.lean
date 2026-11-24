import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The side of a wire. An input is on the point side when it is below p. A chain gate, an OR
-- whose second input is an input, is on the side of that input. Other wires have no side.
def sig (n p : ℕ) (G : List Gate) (w : ℕ) : Option Bool :=
  if w < n then some (decide (w < p)) else
    match G[w - n]? with
    | some ⟨GateOp.or, [_, leaf]⟩ => if leaf < n then some (decide (leaf < p)) else none
    | _ => none

theorem sig_input {n p : ℕ} {G : List Gate} {w : ℕ} (h : w < n) :
    sig n p G w = some (decide (w < p)) := by
  simp [sig, h]

theorem sig_chain {n p : ℕ} {G : List Gate} {w acc leaf : ℕ} (hw : n ≤ w)
    (hg : G[w - n]? = some ⟨GateOp.or, [acc, leaf]⟩) (hl : leaf < n) :
    sig n p G w = some (decide (leaf < p)) := by
  have : ¬ w < n := by omega
  simp [sig, this, hg, hl]

theorem sig_some {n p : ℕ} {G : List Gate} {w : ℕ} {b : Bool} (hw : n ≤ w)
    (h : sig n p G w = some b) :
    ∃ acc leaf, G[w - n]? = some ⟨GateOp.or, [acc, leaf]⟩ ∧ leaf < n ∧ decide (leaf < p) = b := by
  have hn : ¬ w < n := by omega
  unfold sig at h
  rw [if_neg hn] at h
  split at h
  · rename_i acc leaf heq
    by_cases hl : leaf < n
    · rw [if_pos hl] at h
      exact ⟨acc, leaf, heq, hl, Option.some.inj h⟩
    · rw [if_neg hl] at h
      exact absurd h (by simp)
  · exact absurd h (by simp)

-- What every gate of the cover circuit satisfies, gate j being wire n + j.
def GateOK (n p : ℕ) (G : List Gate) (j : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ (∀ i ∈ g.inputs, i < n + j) ∧
  (∀ acc leaf, g = ⟨GateOp.or, [acc, leaf]⟩ → leaf < n →
    sig n p G acc = some (decide (leaf < p))) ∧
  (g.op = GateOp.and → ∃ t acc, g.inputs = [t, acc] ∧ t < n ∧
    sig n p G acc = some (!decide (t < p)))

def accL (B v1 m : ℕ) : List ℕ := v1 :: (List.range m).map (fun j => B + j)

theorem accL_zero (B v1 m : ℕ) : (accL B v1 m).getD 0 0 = v1 := by
  simp [accL]

theorem accL_succ (B v1 m i : ℕ) (hi : i < m) : (accL B v1 m).getD (i + 1) 0 = B + i := by
  simp [accL, List.getD_eq_getElem?_getD, hi]

theorem blockGates_eq (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    blockGates B a t v1 rest lead =
      (List.range rest.length).map (fun i =>
        (⟨GateOp.or, [(accL B v1 rest.length).getD i 0, rest.getD i 0]⟩ : Gate)) ++
      ((⟨GateOp.and, [t, (accL B v1 rest.length).getD rest.length 0]⟩ : Gate) ::
        (if lead then [] else [⟨GateOp.or, [a, B + rest.length]⟩])) := by
  rfl

theorem blockGates_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  rw [blockGates_eq]
  cases lead <;> simp

theorem get_mid (pre blk post : List Gate) (k : ℕ) (hk : k < blk.length) :
    (pre ++ blk ++ post)[pre.length + k]? = some blk[k] := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

theorem block_ok (n p B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) (pre post G : List Gate)
    (hG : G = pre ++ blockGates B a t v1 rest lead ++ post) (hB : B = n + pre.length)
    (hside : ∀ v ∈ v1 :: rest, v < n ∧ decide (v < p) = !decide (t < p)) (ht : t < n)
    (ha : lead = false → a < B) (k : ℕ) (hk : k < (blockGates B a t v1 rest lead).length) :
    GateOK n p G (pre.length + k) ((blockGates B a t v1 rest lead)[k]) := by
  set m := rest.length with hm
  have hlen := blockGates_length B a t v1 rest lead
  have hv1 := hside v1 List.mem_cons_self
  have hrest (i : ℕ) (hi : i < m) : rest.getD i 0 < n ∧
      decide (rest.getD i 0 < p) = !decide (t < p) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hside _ (List.mem_cons_of_mem _ (List.getElem_mem hi))
  -- the gate at block position k, read in the global list
  have hGk (k' : ℕ) (hk' : k' < (blockGates B a t v1 rest lead).length) :
      G[B + k' - n]? = some ((blockGates B a t v1 rest lead)[k']) := by
    rw [hG, show B + k' - n = pre.length + k' by omega]
    exact get_mid _ _ _ _ hk'
  -- the side of the chain value before position i (i ≤ m)
  have hacc (i : ℕ) (hi : i ≤ m) : (accL B v1 m).getD i 0 < B + i ∧
      sig n p G ((accL B v1 m).getD i 0) = some (!decide (t < p)) := by
    cases i with
    | zero =>
      rw [accL_zero]
      refine ⟨by omega, ?_⟩
      rw [sig_input hv1.1, hv1.2]
    | succ i =>
      rw [accL_succ _ _ _ _ (by omega)]
      refine ⟨by omega, ?_⟩
      have hi' : i < (blockGates B a t v1 rest lead).length := by rw [hlen]; omega
      have hg := hGk i hi'
      have he : (blockGates B a t v1 rest lead)[i] =
          ⟨GateOp.or, [(accL B v1 m).getD i 0, rest.getD i 0]⟩ := by
        simp only [blockGates_eq]
        rw [List.getElem_append_left (by simp; omega)]
        simp [hm]
      rw [he] at hg
      rw [sig_chain (by omega) hg (hrest i (by omega)).1, (hrest i (by omega)).2]
  rcases Nat.lt_or_ge k m with hkm | hkm
  · -- a chain OR
    have he : (blockGates B a t v1 rest lead)[k] =
        ⟨GateOp.or, [(accL B v1 m).getD k 0, rest.getD k 0]⟩ := by
      simp only [blockGates_eq]
      rw [List.getElem_append_left (by simp; omega)]
      simp [hm]
    rw [he]
    obtain ⟨h1, h2⟩ := hacc k (by omega)
    obtain ⟨h3, h4⟩ := hrest k hkm
    refine ⟨Or.inr rfl, rfl, ?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro acc leaf heq _
      simp only [Gate.mk.injEq, List.cons.injEq, and_true, true_and] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [h2, h4]
    · intro hop
      exact absurd hop (by simp)
  · rcases Nat.lt_or_ge k (m + 1) with hkm' | hkm'
    · -- the AND of the owner with the chain
      have hk_eq : k = m := by omega
      subst hk_eq
      have he : (blockGates B a t v1 rest lead)[m] =
          ⟨GateOp.and, [t, (accL B v1 m).getD m 0]⟩ := by
        simp only [blockGates_eq]
        rw [List.getElem_append_right (by simp [hm])]
        simp [hm]
      rw [he]
      obtain ⟨h1, h2⟩ := hacc m le_rfl
      refine ⟨Or.inl rfl, rfl, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro acc leaf heq
        simp at heq
      · intro _
        exact ⟨t, _, rfl, ht, h2⟩
    · -- the OR joining this block to the blocks before
      have hk_eq : k = m + 1 := by
        cases lead <;> simp at hlen <;> omega
      subst hk_eq
      have hlead : lead = false := by
        cases lead
        · rfl
        · simp at hlen; omega
      subst hlead
      have he : (blockGates B a t v1 rest false)[m + 1] =
          ⟨GateOp.or, [a, B + m]⟩ := by
        simp only [blockGates_eq]
        rw [List.getElem_append_right (by simp [hm])]
        simp [hm]
      rw [he]
      have ha' := ha rfl
      refine ⟨Or.inr rfl, rfl, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · intro acc leaf heq hl
        simp only [Gate.mk.injEq, List.cons.injEq, and_true, true_and] at heq
        omega
      · intro hop
        exact absurd hop (by simp)

-- An owner list is valid: a nonempty list, the owner on one side and its list on the other.
def Valid (p n : ℕ) (own : List (ℕ × List ℕ)) : Prop :=
  ∀ o ∈ own, o.2 ≠ [] ∧ ((o.1 < p ∧ ∀ v ∈ o.2, p ≤ v ∧ v < n) ∨
    (p ≤ o.1 ∧ o.1 < n ∧ ∀ v ∈ o.2, v < p))

theorem cover_ok (n p : ℕ) (hpn : p ≤ n) (G : List Gate) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (pre : List Gate),
      G = pre ++ coverGatesB B lead a own → B = n + pre.length → (lead = false → a < B) →
      Valid p n own →
      ∀ j (hj : j < G.length), pre.length ≤ j → GateOK n p G j G[j] := by
  intro own
  induction own with
  | nil =>
    intro B lead a pre hG _ _ _ j hj hpre
    simp [coverGatesB] at hG
    subst hG
    omega
  | cons o os ih =>
    intro B lead a pre hG hB ha hv j hj hpre
    obtain ⟨t, leaves⟩ := o
    have hvo := hv (t, leaves) List.mem_cons_self
    have hvos : Valid p n os := fun o ho => hv o (List.mem_cons_of_mem _ ho)
    cases leaves with
    | nil => exact absurd rfl hvo.1
    | cons v1 rest =>
      set blk := blockGates B a t v1 rest lead with hblk
      have hcov : coverGatesB B lead a ((t, v1 :: rest) :: os) =
          blk ++ coverGatesB (B + blk.length) false (B + blk.length - 1) os := rfl
      rw [hcov] at hG
      have hblen := blockGates_length B a t v1 rest lead
      rcases Nat.lt_or_ge j (pre.length + blk.length) with hjb | hjb
      · -- inside this block
        have hside : ∀ v ∈ v1 :: rest, v < n ∧ decide (v < p) = !decide (t < p) := by
          intro v hvm
          rcases hvo.2 with ⟨htp, hl⟩ | ⟨htp, htn, hl⟩
          · have := hl v hvm
            refine ⟨this.2, ?_⟩
            simp [htp]; omega
          · have := hl v hvm
            refine ⟨by omega, ?_⟩
            simp [this]; omega
        have ht : t < n := by
          rcases hvo.2 with ⟨htp, _⟩ | ⟨_, htn, _⟩ <;> omega
        have hG' : G = pre ++ blk ++ coverGatesB (B + blk.length) false (B + blk.length - 1) os := by
          rw [hG, List.append_assoc]
        obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + k := ⟨j - pre.length, by omega⟩
        have hk : k < blk.length := by omega
        have key := block_ok n p B a t v1 rest lead pre _ G hG' hB hside ht ha k hk
        have h1 : G[pre.length + k]? = some (blk[k]) := by
          rw [hG']
          exact get_mid pre blk _ k hk
        rw [List.getElem?_eq_getElem hj] at h1
        rw [Option.some.inj h1]
        exact key
      · -- in a later block
        apply ih (B + blk.length) false (B + blk.length - 1) (pre ++ blk)
          (by rw [hG, List.append_assoc]) (by simp [hB]; omega)
          (fun _ => by rw [hblen]; omega) hvos j hj (by simp; omega)

end PEqualNP.Outside.L_meta_3245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3245

theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro p m own
  dsimp only
  intro hv
  classical
  set n := p + m with hn
  have hpn : p ≤ n := by omega
  have hval : Valid p n own := by
    intro o ho
    obtain ⟨hne, h⟩ := hv o ho
    refine ⟨hne, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, fun v hv' => h2 v hv'⟩
    · exact Or.inr ⟨h1, h2, h3⟩
  set G := coverGatesB n true 0 own with hGdef
  have hok : ∀ j (hj : j < G.length), GateOK n p G j G[j] := fun j hj =>
    cover_ok n p hpn G own n true 0 [] (by simp [hGdef]) (by simp) (by simp) hval j hj (by simp)
  by_cases hempty : G = []
  · have hc : coverCircuitB n own = ⟨[], n⟩ := by
      simp only [coverCircuitB, ← hGdef, hempty, if_true]
    rw [hc]
    refine ⟨∅, ∅, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · intro j hj; simp at hj
      · intro g hg; simp at hg
    · intro w hw; simp at hw
    · intro w hw; simp at hw
    · intro j hj; simp at hj
  · have hc : coverCircuitB n own = ⟨G, n + G.length - 1⟩ := by
      simp only [coverCircuitB, ← hGdef, hempty, if_false]
    rw [hc]
    have hgate (j : ℕ) (hj : j < G.length) :
        NestedCover.gateAt ⟨G, n + G.length - 1⟩ j = G[j] := by
      simp [NestedCover.gateAt, List.getElem?_eq_getElem hj]
    let P : Finset ℕ := (Finset.range (n + G.length)).filter (fun w => sig n p G w = some true)
    let L : Finset ℕ := (Finset.range (n + G.length)).filter (fun w => sig n p G w = some false)
    have memP (w : ℕ) : w ∈ P ↔ w < n + G.length ∧ sig n p G w = some true := by
      simp [P]
    have memL (w : ℕ) : w ∈ L ↔ w < n + G.length ∧ sig n p G w = some false := by
      simp [L]
    -- the inputs of a gate are wires of the circuit
    have inRange (j : ℕ) (hj : j < G.length) (i : ℕ) (hi : i ∈ G[j].inputs) : i < n + G.length := by
      have := (hok j hj).2.2.1 i hi
      omega
    -- a wire with a side is an input on that side or a chain OR whose inputs are on that side
    have sided (b : Bool) (w : ℕ) (hw : w < n + G.length) (hs : sig n p G w = some b) :
        (w < n ∧ decide (w < p) = b) ∨ ∃ j, ∃ hj : j < G.length, w = n + j ∧
          (G[j]'hj).op = GateOp.or ∧
          ∀ i ∈ (G[j]'hj).inputs, i < n + G.length ∧ sig n p G i = some b := by
      by_cases hwn : w < n
      · left
        rw [sig_input hwn] at hs
        exact ⟨hwn, Option.some.inj hs⟩
      · right
        obtain ⟨acc, leaf, hg, hl, hb⟩ := sig_some (by omega) hs
        have hj : w - n < G.length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega)] at hg
          exact absurd hg (by simp)
        have hgj : G[w - n] = ⟨GateOp.or, [acc, leaf]⟩ := by
          rw [List.getElem?_eq_getElem hj] at hg
          exact Option.some.inj hg
        refine ⟨w - n, hj, by omega, by rw [hgj], ?_⟩
        intro i hi
        refine ⟨inRange _ hj i hi, ?_⟩
        rw [hgj] at hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        have hchain := (hok (w - n) hj).2.2.2.1 acc leaf hgj hl
        rcases hi with rfl | rfl
        · rw [hchain, hb]
        · rw [sig_input hl, hb]
    refine ⟨P, L, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact (hok j hj).1
      · intro j hj i hi
        change j < G.length at hj
        rw [hgate j hj] at hi
        exact (hok j hj).2.2.1 i hi
      · intro g hg
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact (hok j hj).2.1
    · intro w hw
      obtain ⟨hwr, hs⟩ := (memP w).1 hw
      rcases sided true w hwr hs with ⟨_, hb⟩ | ⟨j, hj, rfl, hop, hin⟩
      · left; simpa using hb
      · right
        refine ⟨j, hj, rfl, by rw [hgate j hj]; exact hop, ?_⟩
        intro i hi
        rw [hgate j hj] at hi
        exact (memP i).2 (hin i hi)
    · intro w hw
      obtain ⟨hwr, hs⟩ := (memL w).1 hw
      rcases sided false w hwr hs with ⟨hwn, hb⟩ | ⟨j, hj, rfl, hop, hin⟩
      · left
        simp at hb
        exact ⟨hb, hwn⟩
      · right
        refine ⟨j, hj, rfl, by rw [hgate j hj]; exact hop, ?_⟩
        intro i hi
        rw [hgate j hj] at hi
        exact (memL i).2 (hin i hi)
    · intro j hj hop
      change j < G.length at hj
      rw [hgate j hj] at hop ⊢
      obtain ⟨t, acc, hin, ht, hs⟩ := (hok j hj).2.2.2.2 hop
      refine ⟨t, acc, hin, ?_⟩
      have htr : t < n + G.length := by omega
      have hacr : acc < n + G.length := inRange j hj acc (by rw [hin]; simp)
      by_cases htp : t < p
      · left
        refine ⟨(memP t).2 ⟨htr, ?_⟩, (memL acc).2 ⟨hacr, ?_⟩⟩
        · rw [sig_input ht]; simp [htp]
        · rw [hs]; simp [htp]
      · right
        refine ⟨(memL t).2 ⟨htr, ?_⟩, (memP acc).2 ⟨hacr, ?_⟩⟩
        · rw [sig_input ht]; simp [htp]
        · rw [hs]; simp [htp]
