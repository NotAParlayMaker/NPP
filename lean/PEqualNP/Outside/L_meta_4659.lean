import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith.Frontend
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_4659.Count

open scoped BigOperators

lemma degree_secant (d : ℕ) : 86 * d ≤ d * (d - 1) + 1892 := by
  by_cases hd : d = 0
  · simp [hd]
  have hd1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hsplit : d ≤ 43 ∨ 44 ≤ d := by omega
  rcases hsplit with hsmall | hlarge
  · have h43 : 43 - d + d = 43 := Nat.sub_add_cancel hsmall
    have h44 : 44 - d + d = 44 := Nat.sub_add_cancel (by omega)
    have hprod : 0 ≤ (43 - d) * (44 - d) := Nat.zero_le _
    nlinarith
  · have h43 : d - 43 + 43 = d := Nat.sub_add_cancel (by omega)
    have h44 : d - 44 + 44 = d := Nat.sub_add_cancel hlarge
    have hprod : 0 ≤ (d - 43) * (d - 44) := Nat.zero_le _
    nlinarith

lemma left_support_edges (N : ℕ) (K : Fin N → Finset (Fin N))
    (hlinear : ∀ p p' l l' : Fin N, p ≠ p' →
      p ∈ K l → p' ∈ K l → p ∈ K l' → p' ∈ K l' → l = l')
    (hsmall : (Finset.univ.biUnion K).card ≤ 1893) :
    (∑ l : Fin N, (K l).card) ≤
      22 * ((Finset.univ.biUnion K).card +
        (Finset.univ.filter fun l => (K l).Nonempty).card) := by
  classical
  let A := Finset.univ.biUnion K
  let B := Finset.univ.filter fun l => (K l).Nonempty
  have hdisj : (B : Set (Fin N)).PairwiseDisjoint (fun l => (K l).offDiag) := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_offDiag.mp he with ⟨hp, hp', hpp'⟩
    rcases Finset.mem_offDiag.mp he' with ⟨hpl, hp'l, _⟩
    exact hne (hlinear e.1 e.2 l l' hpp' hp hp' hpl hp'l)
  have hsub : B.biUnion (fun l => (K l).offDiag) ⊆ A.offDiag := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨l, _, he⟩
    rcases Finset.mem_offDiag.mp he with ⟨hp, hp', hpp'⟩
    apply Finset.mem_offDiag.mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hp⟩,
      Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hp'⟩, hpp'⟩
  have hpairs : (∑ l ∈ B, (K l).card * ((K l).card - 1)) ≤
      A.card * (A.card - 1) := by
    calc
      _ = (B.biUnion fun l => (K l).offDiag).card := by
        rw [Finset.card_biUnion hdisj]
        simp only [Finset.offDiag_card, Nat.mul_sub_one]
      _ ≤ A.offDiag.card := Finset.card_le_card hsub
      _ = A.card * (A.card - 1) := by
        simp only [Finset.offDiag_card, Nat.mul_sub_one]
  have hbound : A.card * (A.card - 1) ≤ 1892 * A.card := by
    have hA : A.card ≤ 1893 := hsmall
    have hA' : A.card - 1 ≤ 1892 := by omega
    calc
      _ ≤ A.card * 1892 := Nat.mul_le_mul_left A.card hA'
      _ = 1892 * A.card := Nat.mul_comm _ _
  have hsum : (∑ l ∈ B, (K l).card) = ∑ l : Fin N, (K l).card := by
    apply Finset.sum_subset (Finset.subset_univ B)
    intro l hl hlB
    have hnot : ¬ (K l).Nonempty := by
      intro hnonempty
      exact hlB (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hnonempty⟩)
    have hK : K l = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    simp [hK]
  have hsecant : 86 * (∑ l ∈ B, (K l).card) ≤
      (∑ l ∈ B, (K l).card * ((K l).card - 1)) + 1892 * B.card := by
    calc
      _ = ∑ l ∈ B, 86 * (K l).card := by rw [Finset.mul_sum]
      _ ≤ ∑ l ∈ B, ((K l).card * ((K l).card - 1) + 1892) :=
        Finset.sum_le_sum fun l _ => degree_secant (K l).card
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Nat.mul_comm]
  rw [hsum] at hsecant
  change (∑ l : Fin N, (K l).card) ≤ 22 * (A.card + B.card)
  omega

lemma small_support_edges (N : ℕ) (K : Fin N → Finset (Fin N))
    (hlinear : ∀ p p' l l' : Fin N, p ≠ p' →
      p ∈ K l → p' ∈ K l → p ∈ K l' → p' ∈ K l' → l = l')
    (hsmall : (Finset.univ.biUnion K).card ≤ 1893 ∨
      (Finset.univ.filter fun l => (K l).Nonempty).card ≤ 1893) :
    (∑ l : Fin N, (K l).card) ≤
      22 * ((Finset.univ.biUnion K).card +
        (Finset.univ.filter fun l => (K l).Nonempty).card) := by
  classical
  rcases hsmall with hleft | hright
  · exact left_support_edges N K hlinear hleft
  · let L : Fin N → Finset (Fin N) :=
      fun p => Finset.univ.filter fun l => p ∈ K l
    have htranspose : ∀ l l' p p' : Fin N, l ≠ l' →
        l ∈ L p → l' ∈ L p → l ∈ L p' → l' ∈ L p' → p = p' := by
      intro l l' p p' hll hl hl' hpl hpl'
      have hp : p ∈ K l := (Finset.mem_filter.mp hl).2
      have hp' : p ∈ K l' := (Finset.mem_filter.mp hl').2
      have hpp : p' ∈ K l := (Finset.mem_filter.mp hpl).2
      have hpp' : p' ∈ K l' := (Finset.mem_filter.mp hpl').2
      by_contra hne
      exact hll (hlinear p p' l l' hne hp hpp hp' hpp')
    have hA : Finset.univ.biUnion L =
        Finset.univ.filter fun l => (K l).Nonempty := by
      ext l
      constructor
      · intro hl
        rcases Finset.mem_biUnion.mp hl with ⟨p, _, hp⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ l, ⟨p, (Finset.mem_filter.mp hp).2⟩⟩
      · intro hl
        rcases (Finset.mem_filter.mp hl).2 with ⟨p, hp⟩
        exact Finset.mem_biUnion.mpr
          ⟨p, Finset.mem_univ p, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hp⟩⟩
    have hB : (Finset.univ.filter fun p => (L p).Nonempty) =
        Finset.univ.biUnion K := by
      ext p
      constructor
      · intro hp
        rcases (Finset.mem_filter.mp hp).2 with ⟨l, hl⟩
        exact Finset.mem_biUnion.mpr
          ⟨l, Finset.mem_univ l, (Finset.mem_filter.mp hl).2⟩
      · intro hp
        rcases Finset.mem_biUnion.mp hp with ⟨l, _, hl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ p, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩⟩
    have hsum : (∑ p : Fin N, (L p).card) = ∑ l : Fin N, (K l).card := by
      calc
        _ = ∑ p : Fin N, ∑ l : Fin N, if p ∈ K l then 1 else 0 := by
          simp [L]
        _ = ∑ l : Fin N, ∑ p : Fin N, if p ∈ K l then 1 else 0 :=
          Finset.sum_comm
        _ = _ := by simp [← Finset.sum_filter]
    have hleft : (Finset.univ.biUnion L).card ≤ 1893 := by
      rw [hA]
      exact hright
    have hresult := left_support_edges N L htranspose hleft
    rw [hA, hB, hsum, Nat.add_comm] at hresult
    exact hresult

end PEqualNP.Outside.L_meta_4659.Count

namespace PEqualNP.Outside.L_meta_4659.Circuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incPair {N : ℕ} (p l : Fin N) (i : Fin (N + N)) : Bool :=
  decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Below (x y : List Bool) : Prop :=
  ∀ i, x.getD i false = true → y.getD i false = true

lemma getD_append_lt (x z : List Bool) {i : ℕ} (hi : i < x.length) :
    (x ++ z).getD i false = x.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ite_eq_left hi]

lemma getD_append_last (x : List Bool) (b : Bool) :
    (x ++ [b]).getD x.length false = b := by
  simp

lemma run_preserve (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [show run (g :: gs) x = run gs (x ++
      [g.op.eval (g.inputs.map fun i => x.getD i false)]) from rfl]
    rw [ih _ (by simpa using Nat.lt_succ_of_lt hi), getD_append_lt _ _ hi]

lemma gate_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {x y : List Bool} (hxy : Below x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    exact fun h i hi => hxy i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and]
    rintro ⟨i, hi, h⟩
    exact ⟨i, hi, hxy i h⟩

lemma below_append {x y : List Bool} (hlen : x.length = y.length)
    (hxy : Below x y) {a b : Bool} (hab : a = true → b = true) :
    Below (x ++ [a]) (y ++ [b]) := by
  intro i hi
  by_cases hix : i < x.length
  · rw [getD_append_lt x _ hix] at hi
    rw [getD_append_lt y _ (by omega)]
    exact hxy i hi
  · by_cases hie : i = x.length
    · subst i
      simpa [hlen] using hab (by simpa using hi)
    · have hx : x.length + 1 ≤ i := by omega
      have hy : y.length + 1 ≤ i := by omega
      have hxi : (x ++ [a]).length ≤ i := by simpa using hx
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hxi] at hi

lemma run_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {x y : List Bool} (hlen : x.length = y.length) (hxy : Below x y) :
    Below (run gs x) (run gs y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    apply ih (fun g hg => hm g (by simp [hg])) (by simpa using hlen)
    exact below_append hlen hxy (gate_mono g (hm g (by simp)) hxy)

lemma ofFn_below {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : Below (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using hxy ⟨i, hin⟩
      (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · simp [List.getD_eq_getElem?_getD, hin] at hi

lemma monotone_eval {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hmono : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true)
    (hx : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  exact run_mono C.gates (fun g hg => (hmono g hg).1)
    (by simp) (ofFn_below x y hxy) C.output hx

lemma run_avoids (gs : List Gate) (n e : ℕ)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y z : List Bool) (hx : x.length = n) (hy : y.length = n) (hz : z.length = n)
    (hzy : Below z y) (hyx : Below y x)
    (heq : ∀ i, i ≠ e → x.getD i false = y.getD i false)
    (havoid : ∀ pre g post, gs = pre ++ g :: post →
      (run gs z).getD (n + pre.length) false = false →
      (run gs x).getD (n + pre.length) false = true → e ∉ g.inputs) :
    ∀ i, i ≠ e → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs generalizing n x y z with
  | nil => exact heq
  | cons g gs ih =>
    let a := g.op.eval (g.inputs.map fun i => x.getD i false)
    let b := g.op.eval (g.inputs.map fun i => y.getD i false)
    let c := g.op.eval (g.inputs.map fun i => z.getD i false)
    have hba : b = true → a = true := gate_mono g (hm g (by simp)) hyx
    have hcb : c = true → b = true := gate_mono g (hm g (by simp)) hzy
    have hab : a = b := by
      by_contra hne
      have hat : a = true := by
        cases ha : a with
        | true => rfl
        | false =>
          have hbf : b = false := by
            cases hb : b with
            | false => rfl
            | true => have h := hba hb; simp [ha] at h
          exact False.elim (hne (ha.trans hbf.symm))
      have hbf : b = false := by
        cases hb : b with
        | false => rfl
        | true => exact False.elim (hne (hat.trans hb.symm))
      have hcf : c = false := by
        cases hc : c with
        | false => rfl
        | true => have h := hcb hc; simp [hbf] at h
      have hea : e ∉ g.inputs := by
        apply havoid [] g gs rfl
        · change (run gs (z ++ [c])).getD n false = false
          rw [run_preserve gs _ (by simp [hz]), ← hz, getD_append_last]
          exact hcf
        · change (run gs (x ++ [a])).getD n false = true
          rw [run_preserve gs _ (by simp [hx]), ← hx, getD_append_last]
          exact hat
      have hmap : g.inputs.map (fun i => x.getD i false) =
          g.inputs.map (fun i => y.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact heq i (fun hie => hea (hie ▸ hi))
      exact hne (congrArg (fun bs => g.op.eval bs) hmap)
    apply ih (n + 1) (fun g hg => hm g (by simp [hg]))
      (x ++ [a]) (y ++ [b]) (z ++ [c])
      (by simp [hx]) (by simp [hy]) (by simp [hz])
      (below_append (by omega) hzy hcb) (below_append (by omega) hyx hba)
    · intro i hie
      by_cases hi : i < n
      · rw [getD_append_lt _ _ (by omega), getD_append_lt _ _ (by omega)]
        exact heq i hie
      · by_cases hin : i = n
        · subst i
          simpa [hx, hy] using hab
        · have hix : (x ++ [a]).length ≤ i := by simp [hx]; omega
          have hiy : (y ++ [b]).length ≤ i := by simp [hy]; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hix,
            List.getElem?_eq_none hiy]
    · intro pre g' post hs hzero htrue
      apply havoid (g :: pre) g' post (by simp [hs])
      · simpa [run, c, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero
      · simpa [run, a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htrue

abbrev Active {N : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (K : Fin N → Finset (Fin N)) :=
  {j : Fin C.size //
    (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
    ∃ l : Fin N, ∃ p ∈ K l,
      (C.wires (List.ofFn (incPair p l))).getD (N + N + j.val) false = true}

lemma active_reader {N : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (K : Fin N → Finset (Fin N)) (hmono : Monotone2 C)
    (hsingle : ∀ i : Fin (N + N),
      C.eval (List.ofFn (fun j => decide (j = i))) = false)
    (l p : Fin N) (hp : p ∈ K l)
    (hpair : C.eval (List.ofFn (incPair p l)) = true)
    (e f : Fin (N + N))
    (hef : ∀ i, incPair p l i = decide (i = e ∨ i = f)) :
    ∃ j : Active C K, e.val ∈ (C.gates.get j.val).inputs := by
  classical
  by_contra hn
  have hout : C.output ≠ e.val := by
    intro ho
    have ht : C.eval (List.ofFn (fun j : Fin (N + N) => decide (j = e))) = true := by
      change (run C.gates (List.ofFn (fun j : Fin (N + N) => decide (j = e)))).getD
        C.output false = true
      rw [ho, run_preserve C.gates _ (by simpa using e.isLt)]
      simp [List.getD_eq_getElem?_getD, e.isLt]
    rw [hsingle e] at ht
    cases ht
  have hxy : Below (List.ofFn (fun j : Fin (N + N) => decide (j = f)))
      (List.ofFn (incPair p l)) := by
    apply ofFn_below
    intro i hi
    have hi' : i = f := of_decide_eq_true hi
    rw [hef i]
    simp [hi']
  have hzy : Below (List.ofFn (fun _ : Fin (N + N) => false))
      (List.ofFn (fun j : Fin (N + N) => decide (j = f))) := by
    apply ofFn_below
    simp
  have heq : ∀ i, i ≠ e.val →
      (List.ofFn (incPair p l)).getD i false =
      (List.ofFn (fun j : Fin (N + N) => decide (j = f))).getD i false := by
    intro i hie
    by_cases hi : i < N + N
    · have hif : (⟨i, hi⟩ : Fin (N + N)) ≠ e := by
        intro h
        exact hie (congrArg Fin.val h)
      simp [List.getD_eq_getElem?_getD, hi, hef, hif]
    · simp [List.getD_eq_getElem?_getD, hi]
  have hsame := run_avoids C.gates (N + N) e.val
    (fun g hg => (hmono g hg).1)
    (List.ofFn (incPair p l))
    (List.ofFn (fun j : Fin (N + N) => decide (j = f)))
    (List.ofFn (fun _ : Fin (N + N) => false))
    (by simp) (by simp) (by simp) hzy hxy heq
  have havoid : ∀ pre g post, C.gates = pre ++ g :: post →
      (run C.gates (List.ofFn (fun _ : Fin (N + N) => false))).getD
        (N + N + pre.length) false = false →
      (run C.gates (List.ofFn (incPair p l))).getD
        (N + N + pre.length) false = true → e.val ∉ g.inputs := by
    intro pre g post hs hz hx he
    let j : Fin C.size := ⟨pre.length, by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hs]⟩
    have hget : C.gates.get j = g := by
      have hj : pre.length < C.gates.length := by
        simpa only [j, PEqualNP.CircuitLowerBounds.Circuit.size] using j.isLt
      change C.gates[pre.length]'hj = g
      simp [hs]
    have hact : (C.wires (List.replicate (N + N) false)).getD
        (N + N + j.val) false = false ∧
        ∃ l : Fin N, ∃ p ∈ K l,
          (C.wires (List.ofFn (incPair p l))).getD (N + N + j.val) false = true := by
      constructor
      · simpa [j, PEqualNP.CircuitLowerBounds.Circuit.wires, run] using hz
      · exact ⟨l, p, hp, hx⟩
    apply hn
    exact ⟨⟨j, hact⟩, by simpa [hget] using he⟩
  have hfinal := hsame havoid C.output hout
  change C.eval (List.ofFn (incPair p l)) =
    C.eval (List.ofFn (fun j : Fin (N + N) => decide (j = f))) at hfinal
  rw [hpair, hsingle f] at hfinal
  cases hfinal

lemma active_support_bound {N : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (K : Fin N → Finset (Fin N)) (hmono : Monotone2 C)
    (hsingle : ∀ i : Fin (N + N),
      C.eval (List.ofFn (fun j => decide (j = i))) = false)
    (hpair : ∀ l p, p ∈ K l → C.eval (List.ofFn (incPair p l)) = true) :
    (Finset.univ.biUnion K).card +
        (Finset.univ.filter (fun l => (K l).Nonempty)).card ≤
      2 * Fintype.card (Active C K) := by
  classical
  let A := Finset.univ.biUnion K
  let B := Finset.univ.filter (fun l => (K l).Nonempty)
  let R : Finset ℕ := Finset.univ.biUnion
    (fun j : Active C K => (C.gates.get j.val).inputs.toFinset)
  let E : Finset ℕ := A.image Fin.val ∪ B.image (fun l : Fin N => N + l.val)
  have hAR : ∀ p ∈ A, p.val ∈ R := by
    intro p hp
    obtain ⟨l, _, hpl⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, hj⟩ := active_reader C K hmono hsingle l p hpl (hpair l p hpl)
      (Fin.castAdd N p) (Fin.natAdd N l) (fun _ => rfl)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa using hj⟩
  have hBR : ∀ l ∈ B, N + l.val ∈ R := by
    intro l hl
    obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨j, hj⟩ := active_reader C K hmono hsingle l p hp (hpair l p hp)
      (Fin.natAdd N l) (Fin.castAdd N p) (fun i => by simp [incPair, or_comm])
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simpa [Nat.add_comm] using hj⟩
  have hER : E ⊆ R := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      exact hAR p hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      exact hBR l hl
  have hdisj : Disjoint (A.image Fin.val) (B.image (fun l : Fin N => N + l.val)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hj
    have hp := p.isLt
    omega
  have hE : E.card = A.card + B.card := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (by
        intro a b h
        apply Fin.ext
        change N + a.val = N + b.val at h
        omega)]
  have hR : R.card ≤ 2 * Fintype.card (Active C K) := by
    calc
      R.card ≤ ∑ j : Active C K, ((C.gates.get j.val).inputs.toFinset).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ j : Active C K, 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact le_trans (List.toFinset_card_le _) (hmono _ (List.get_mem _ _)).2
      _ = 2 * Fintype.card (Active C K) := by simp [Nat.mul_comm]
  calc
    A.card + B.card = E.card := hE.symm
    _ ≤ R.card := Finset.card_le_card hER
    _ ≤ 2 * Fintype.card (Active C K) := hR

end PEqualNP.Outside.L_meta_4659.Circuit

open PEqualNP.Outside.L_meta_4659

theorem PEqualNP.Outside.L_meta_4659 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x2 → Finset (Fin x2)),   have x7 : Finset (Fin x2) → Fin (x2 + x2) → Bool := fun (x7 : Finset (Fin x2)) (x8 : Fin (x2 + x2)) => Fin.addCases (fun (x9 : Fin x2) => Decidable.decide ¬∃ x10 ∈ x7, x3 x9 x10) (fun (x9 : Fin x2) => Decidable.decide (x9 ∈ x7)) x8;   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => if x8.op.eval [] = Bool.true ∧ x8.inputs.length = (2 : ℕ) ∧ (x8.inputs.all fun (x9 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x9 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x8) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };   have x9 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x9 x10 : Fin x2) (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x9 ∨ x11 = Fin.natAdd x2 x10);   (Finset.univ.biUnion x6).card ≤ (1893 : ℕ) ∨ Fintype.card { x10 : Fin x2 // (x6 x10).Nonempty } ≤ (1893 : ℕ) → (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x13 : Fin x2), Fintype.card { x14 : Fin x2 // x3 x14 x13 } = x1 + (1 : ℕ)) → (∀ (x14 x15 : Fin x2), x14 ≠ x15 → ∃! x17 : Fin x2, x3 x14 x17 ∧ x3 x15 x17) → PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → x5.eval (List.ofFn (x7 x16)) = Bool.false) → (∀ (x17 x18 : Fin x2), x18 ∈ x6 x17 → x3 x18 x17 ∧ x5.eval (List.ofFn (x9 x18 x17)) = Bool.true ∧ x8.eval (List.ofFn (x9 x18 x17)) = Bool.false) → ∑ x18 : Fin x2, (x6 x18).card ≤ (44 : ℕ) * Fintype.card { x18 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x18) Bool.false = Bool.false ∧ ∃ (x19 : Fin x2), ∃ x20 ∈ x6 x19, (x5.wires (List.ofFn (x9 x20 x19))).getD (x2 + x2 + ↑x18) Bool.false = Bool.true } := by
  classical
  intro q N R inst C K
  dsimp only
  intro hsmall hq _hN _hcol huniq hmin hsound hselected
  have hmono : PEqualNP.MetaComplexity.Monotone2 C := hmin.1
  let A : Finset (Fin N) := Finset.univ.biUnion K
  let B : Finset (Fin N) := Finset.univ.filter fun l => (K l).Nonempty
  have hlinear : ∀ p p' l l' : Fin N, p ≠ p' → p ∈ K l → p' ∈ K l →
      p ∈ K l' → p' ∈ K l' → l = l' := by
    intro p p' l l' hne hp hp' hpl hpl'
    obtain ⟨w, _hw, huw⟩ := huniq p p' hne
    exact (huw l ⟨(hselected l p hp).1, (hselected l p' hp').1⟩).trans
      (huw l' ⟨(hselected l' p hpl).1, (hselected l' p' hpl').1⟩).symm
  have hsmall' : A.card ≤ 1893 ∨ B.card ≤ 1893 := by
    simpa only [A, B, Fintype.card_subtype] using hsmall
  have hpoint (p : Fin N) :
      C.eval (List.ofFn fun j : Fin (N + N) => decide (j = Fin.castAdd N p)) = false := by
    cases hc : C.eval (List.ofFn fun j : Fin (N + N) => decide (j = Fin.castAdd N p)) with
    | false => rfl
    | true =>
      have hup := Circuit.monotone_eval (C := C) hmono
        (x := fun j : Fin (N + N) => decide (j = Fin.castAdd N p))
        (y := fun j : Fin (N + N) => Fin.addCases
          (fun r : Fin N => decide (¬ ∃ l ∈ (∅ : Finset (Fin N)), R r l))
          (fun l : Fin N => decide (l ∈ (∅ : Finset (Fin N)))) j)
        (by
          intro j hj
          have he : j = Fin.castAdd N p := of_decide_eq_true hj
          subst j
          simp)
        hc
      have hz := hsound (∅ : Finset (Fin N)) (by simp)
      rw [hz] at hup
      contradiction
  have hline (l : Fin N) :
      C.eval (List.ofFn fun j : Fin (N + N) => decide (j = Fin.natAdd N l)) = false := by
    cases hc : C.eval (List.ofFn fun j : Fin (N + N) => decide (j = Fin.natAdd N l)) with
    | false => rfl
    | true =>
      have hup := Circuit.monotone_eval (C := C) hmono
        (x := fun j : Fin (N + N) => decide (j = Fin.natAdd N l))
        (y := fun j : Fin (N + N) => Fin.addCases
          (fun r : Fin N => decide (¬ ∃ t ∈ ({l} : Finset (Fin N)), R r t))
          (fun t : Fin N => decide (t ∈ ({l} : Finset (Fin N)))) j)
        (by
          intro j hj
          have he : j = Fin.natAdd N l := of_decide_eq_true hj
          subst j
          rw [Fin.addCases_right]
          simp)
        hc
      have hz := hsound ({l} : Finset (Fin N)) (by simp; omega)
      rw [hz] at hup
      contradiction
  have hsingle (i : Fin (N + N)) :
      C.eval (List.ofFn fun j : Fin (N + N) => decide (j = i)) = false := by
    by_cases hi : i.val < N
    · let p : Fin N := ⟨i.val, hi⟩
      have he : i = Fin.castAdd N p := Fin.ext rfl
      simpa only [he] using hpoint p
    · let l : Fin N := ⟨i.val - N, by omega⟩
      have he : i = Fin.natAdd N l := by
        apply Fin.ext
        dsimp [l]
        omega
      simpa only [he] using hline l
  have hpair : ∀ l p : Fin N, p ∈ K l →
      C.eval (List.ofFn (Circuit.incPair p l)) = true := by
    intro l p hp
    exact (hselected l p hp).2.1
  have hcount := Count.small_support_edges (N := N) (K := K) hlinear hsmall'
  have hreaders := Circuit.active_support_bound (C := C) (K := K) hmono hsingle hpair
  change (∑ l : Fin N, (K l).card) ≤ 44 * Fintype.card (Circuit.Active C K)
  omega
