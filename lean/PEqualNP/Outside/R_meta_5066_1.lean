import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

-- When all rows have degree two, the extra edges are a permutation after matching relabeling.
-- The two child statements isolate cycle unions and the case with a larger row.
theorem PEqualNP.Outside.R_meta_5066_1
    (cycles : ∀ (n : ℕ) (next : Equiv.Perm (Fin n)) (C : Circuit), 3 ≤ n →
      (∀ i, next i ≠ i) → (∀ i, next (next i) ≠ i) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x = decide
        (∃ i, x (Fin.castAdd n i) = true ∧
          (x (Fin.natAdd n i) = true ∨ x (Fin.natAdd n (next i)) = true))) →
      3*n ≤ C.size+1)
    (wider : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (matching : Equiv.Perm (Fin n))
      (C : Circuit), 4 ≤ n → n < E.card → 2*n ≤ C.size+1 →
      (∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
      (∀ i, (i,matching i) ∈ E) → IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x = decide
        (∃ i j, (i,j) ∈ E ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n j) = true)) →
      ((∀ i, ∃ j, j ≠ matching i ∧ (i,j) ∈ E) ∧
        (∀ j, ∃ i, matching i ≠ j ∧ (i,j) ∈ E)) →
      (∃ i a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ (i,a) ∈ E ∧ (i,b) ∈ E ∧ (i,c) ∈ E) →
      E.card+n ≤ C.size+1) :
∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x12 ≠ x3 x11 ∧ (x11, x12) ∈ x2) ∧ ∀ (x11 : Fin x1), ∃ (x12 : Fin x1), x3 x12 ≠ x11 ∧ (x12, x11) ∈ x2) → x2.card + x1 ≤ x4.size + (1 : ℕ)
 := by
  let rename {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (p ⟨i, h⟩).val else i

  have rename_small {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : rename p i < n ↔ i < n := by
    by_cases hi : i < n
    · simp [rename, hi, (p ⟨i, hi⟩).isLt]
    · simp [rename, hi]

  have rename_internal {n : ℕ} (p : Fin n → Fin n) {i : ℕ} (hi : n ≤ i) : rename p i = i := by
    simp [rename, Nat.not_lt.mpr hi]

  let mapGate {n : ℕ} (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename p)⟩

  let mapCircuit {n : ℕ} (p : Fin n → Fin n) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate p), rename p C.output⟩

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have same_after_append {n : ℕ} (p : Fin n → Fin n) (old new : List Bool)
      (hlen : old.length = new.length) (hraw : n ≤ old.length)
      (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) (b : Bool) :
      ∀ i, (new ++ [b]).getD (rename p i) false = (old ++ [b]).getD i false := by
    intro i
    by_cases hi : i < old.length
    · have hnew : rename p i < new.length := by
        by_cases h : i < n
        · have hp := (rename_small p i).mpr h
          omega
        · rw [rename_internal p (Nat.le_of_not_gt h)]
          omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hnew,
        List.getElem?_append_left hi]
      simpa only [List.getD_eq_getElem?_getD] using hbit i
    · have hri := rename_internal p (by omega : n ≤ i)
      have hnew : new.length ≤ i := by omega
      rw [hri]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt hi),
        List.getElem?_append_right hnew, hlen]

  have propagate {n : ℕ} (p : Fin n → Fin n) (gs : List Gate) (old new : List Bool)
      (hlen : old.length = new.length) (hraw : n ≤ old.length)
      (hbit : ∀ i, new.getD (rename p i) false = old.getD i false) :
      ∀ i, ((gs.map (mapGate p)).foldl step new).getD (rename p i) false =
        (gs.foldl step old).getD i false := by
    induction gs generalizing old new with
    | nil => exact hbit
    | cons g gs ih =>
      change ∀ i, ((gs.map (mapGate p)).foldl step (step new (mapGate p g))).getD (rename p i) false =
        (gs.foldl step (step old g)).getD i false
      have eqb : (g.inputs.map (rename p)).map (fun i => new.getD i false) =
          g.inputs.map (fun i => old.getD i false) := by
        rw [List.map_map]
        exact List.map_congr_left fun i _ => hbit i
      have hn : step new (mapGate p g) = new ++ [g.op.eval (g.inputs.map fun i => old.getD i false)] := by
        simp only [step, mapGate, eqb]
      rw [hn]
      exact ih _ _ (by simp [step, hlen]) (by simp [step]; omega)
        (same_after_append p old new hlen hraw hbit _)

  have input_read {n : ℕ} (p : Fin n → Fin n) (x : Fin n → Bool) :
      ∀ i : ℕ, (List.ofFn x).getD (rename p i) false = (List.ofFn (x ∘ p)).getD i false := by
    intro i
    by_cases hi : i < n
    · simp [rename, hi, List.getD_eq_getElem?_getD, (p ⟨i, hi⟩).isLt]
    · simp [rename, hi, List.getD_eq_getElem?_getD]

  have row_degree_lower {n : ℕ} (E : Finset (Fin n × Fin n)) (matched : Equiv.Perm (Fin n))
      (diag : ∀ i, (i, matched i) ∈ E)
      (extra : ∀ i, ∃ j, j ≠ matched i ∧ (i,j) ∈ E) :
      ∀ i : Fin n, 2 ≤ (Finset.univ.filter fun j => (i,j) ∈ E).card := by
    intro i
    obtain ⟨j, neq, mem⟩ := extra i
    have sub : ({matched i, j} : Finset (Fin n)) ⊆ (Finset.univ.filter fun k => (i,k) ∈ E) := by
      intro k hk
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hk : k = matched i ∨ k = j) with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, diag i⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem⟩
    simpa [Ne.symm neq] using Finset.card_le_card sub

  have two_regular_permutation {n : ℕ} (E : Finset (Fin n × Fin n)) (matched : Equiv.Perm (Fin n))
      (c4 : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E))
      (diag : ∀ i, (i, matched i) ∈ E)
      (extraRow : ∀ i, ∃ j, j ≠ matched i ∧ (i,j) ∈ E)
      (extraCol : ∀ j, ∃ i, matched i ≠ j ∧ (i,j) ∈ E)
      (row2 : ∀ i : Fin n, (Finset.univ.filter fun j => (i,j) ∈ E).card = 2) :
      ∃ next : Equiv.Perm (Fin n),
        (∀ i, next i ≠ i) ∧ (∀ i, next (next i) ≠ i) ∧
        (∀ i j, (i,j) ∈ E ↔ j = matched i ∨ j = matched (next i)) ∧ E.card = 2*n := by
    classical
    choose follower follower_ne follower_mem using extraRow
    have row (i : Fin n) : (Finset.univ.filter fun j => (i,j) ∈ E) = {matched i, follower i} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro k hk
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hk :
          k = matched i ∨ k = follower i) with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, diag i⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, follower_mem i⟩
      · rw [row2]
        simp [Ne.symm (follower_ne i)]
    have cols (i j : Fin n) : (i,j) ∈ E ↔ j = matched i ∨ j = follower i := by
      have h := Finset.ext_iff.mp (row i) j
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton] using h
    have onto : Function.Surjective follower := by
      intro j
      obtain ⟨i, forbidden, he⟩ := extraCol j
      rcases (cols i j).mp he with hm | he
      · exact (forbidden hm.symm).elim
      · exact ⟨i, he.symm⟩
    let followEquiv := Equiv.ofBijective follower ⟨Finite.injective_iff_surjective.mpr onto, onto⟩
    let next := followEquiv.trans matched.symm
    have matchNext (i : Fin n) : matched (next i) = follower i := by
      change matched (matched.symm (follower i)) = follower i
      exact matched.apply_symm_apply _
    have nf (i : Fin n) : next i ≠ i := by
      intro e
      exact follower_ne i ((matchNext i).symm.trans (congrArg matched e))
    have nc (i : Fin n) : next (next i) ≠ i := by
      intro e
      have ne : i ≠ next i := (nf i).symm
      have matchNe : matched i ≠ matched (next i) := fun q => ne (matched.injective q)
      have cross₁ : (i, matched (next i)) ∈ E := by rw [matchNext]; exact follower_mem i
      have cross₂ : (next i, matched i) ∈ E := by
        have he := follower_mem (next i)
        rwa [← matchNext, e] at he
      exact c4 i (next i) (matched i) (matched (next i)) ne matchNe
        ⟨diag i, cross₁, cross₂, diag (next i)⟩
    have hrow (i j : Fin n) : (i,j) ∈ E ↔ j = matched i ∨ j = matched (next i) := by
      rw [matchNext]; exact cols i j
    refine ⟨next, nf, nc, hrow, ?_⟩
    let toEdge (p : Fin n × Fin 2) : E :=
      ⟨(p.1, if p.2.val = 0 then matched p.1 else follower p.1), by
        by_cases h : p.2.val = 0
        · simpa [h] using diag p.1
        · simpa [h] using follower_mem p.1⟩
    have injective : Function.Injective toEdge := by
      rintro ⟨i,p⟩ ⟨j,q⟩ eq
      have h := congrArg Subtype.val eq
      have e : i = j := congrArg Prod.fst h
      subst j
      have hcol := congrArg Prod.snd h
      have neq := follower_ne i
      have neq' := neq.symm
      fin_cases p <;> fin_cases q
      · rfl
      · exact (neq' (by simpa [toEdge] using hcol)).elim
      · exact (neq (by simpa [toEdge] using hcol)).elim
      · rfl
    have surjective : Function.Surjective toEdge := by
      rintro ⟨⟨i,j⟩, h⟩
      rcases (cols i j).mp h with rfl | rfl
      · exact ⟨(i,0), Subtype.ext rfl⟩
      · exact ⟨(i,1), Subtype.ext rfl⟩
    have hc := Fintype.card_congr (Equiv.ofBijective toEdge ⟨injective,surjective⟩)
    simpa [Nat.mul_comm] using hc.symm

  have cycle_length_lower {n : ℕ} (perm : Equiv.Perm (Fin n)) (pos : 0 < n)
      (one : ∀ i, perm i ≠ i) (two : ∀ i, perm (perm i) ≠ i) : 3 ≤ n := by
    let i : Fin n := ⟨0,pos⟩
    let a : Fin n := perm i
    let b : Fin n := perm a
    have ha : a ≠ i := one i
    have hb : b ≠ i := two i
    have hab : b ≠ a := one a
    have card : ({i,a,b} : Finset (Fin n)).card = 3 := by
      simp [ha.symm, hb.symm, hab.symm]
    have bound := Finset.card_le_univ ({i,a,b} : Finset (Fin n))
    rw [card, Fintype.card_fin] at bound
    exact bound

  have dense_size_lower {n : ℕ} (E : Finset (Fin n × Fin n)) (matched : Equiv.Perm (Fin n))
      (c4 : ∀ a b c d : Fin n, a ≠ b → c ≠ d →
        ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E))
      (diag : ∀ i, (i, matched i) ∈ E)
      (extra : ∀ i, ∃ j, j ≠ matched i ∧ (i,j) ∈ E)
      (wide : ∃ i : Fin n, 3 ≤ (Finset.univ.filter fun j => (i,j) ∈ E).card) : 4 ≤ n := by
    obtain ⟨i,hi⟩ := wide
    have cn := Finset.card_le_univ (Finset.univ.filter fun j => (i,j) ∈ E)
    rw [Fintype.card_fin] at cn
    by_contra small
    have all : (Finset.univ.filter fun j => (i,j) ∈ E) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    have allMem (j : Fin n) : (i,j) ∈ E := by
      have h : j ∈ (Finset.univ.filter fun j => (i,j) ∈ E) := by rw [all]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp h).2
    let z : Fin n := ⟨0,by omega⟩
    let o : Fin n := ⟨1,by omega⟩
    obtain ⟨j,ij⟩ : ∃ j : Fin n, i ≠ j := by
      by_cases h : i = z
      · refine ⟨o, fun h' => ?_⟩
        have e : z = o := h.symm.trans h'
        exact (show (0 : ℕ) ≠ 1 by decide) (congrArg Fin.val e)
      · exact ⟨z,h⟩
    obtain ⟨k,km,ke⟩ := extra j
    exact c4 i j (matched j) k ij km.symm ⟨allMem _, allMem _,diag j,ke⟩

  have map_ao {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (H : IsAO2 n C) :
      IsAO2 n (mapCircuit p C) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
      exact H.1 old ho
    · intro j hj i hi
      have hc : j < C.gates.length := by simpa [mapCircuit] using hj
      have eqGate : gateAt (mapCircuit p C) j = mapGate p (gateAt C j) := by
        change (C.gates.map (mapGate p)).getD j ⟨.or, []⟩ =
          mapGate p (C.gates.getD j ⟨.or, []⟩)
        rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getD_eq_getElem _ _ hc]
        simp only [List.getElem_map]
      rw [eqGate] at hi
      obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hi
      have back := H.2.1 j hc raw hraw
      by_cases hn : raw < n
      · have := (rename_small p raw).mpr hn
        omega
      · rw [rename_internal p (Nat.le_of_not_gt hn)]
        exact back
    · intro g hg
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
      simpa [mapGate] using H.2.2 _ ho

  have map_eval {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
      circuitFun n (mapCircuit p C) x = circuitFun n C (x ∘ p) :=
    propagate p C.gates (List.ofFn (x ∘ p)) (List.ofFn x) (by simp) (by simp) (input_read p x) C.output

  let renumberRight {n : ℕ} (matched : Equiv.Perm (Fin n)) : Fin (n+n) → Fin (n+n) :=
    Fin.addCases (Fin.castAdd n) (fun j => Fin.natAdd n (matched.symm j))

  have diagonal_semantics {n : ℕ} (E : Finset (Fin n × Fin n))
      (matched next : Equiv.Perm (Fin n)) (C : Circuit)
      (row : ∀ i j, (i,j) ∈ E ↔ j = matched i ∨ j = matched (next i))
      (agree : ∀ x : Fin (n+n) → Bool, circuitFun (n+n) C x = decide
        (∃ i j, (i,j) ∈ E ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n j) = true)) :
      ∀ x : Fin (n+n) → Bool, circuitFun (n+n) (mapCircuit (renumberRight matched) C) x = decide
        (∃ i, x (Fin.castAdd n i) = true ∧
          (x (Fin.natAdd n i) = true ∨ x (Fin.natAdd n (next i)) = true)) := by
    intro x
    rw [map_eval, agree]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Function.comp_apply]
    have leftCast (j : Fin n) : renumberRight matched (Fin.castAdd n j) = Fin.castAdd n j := by
      change Fin.addCases (motive := fun _ : Fin (n+n) => Fin (n+n))
        (Fin.castAdd n) (fun k => Fin.natAdd n (matched.symm k))
        (Fin.castAdd n j) = _
      rw [Fin.addCases_left]
    have rightCast (j : Fin n) : renumberRight matched (Fin.natAdd n (matched j)) = Fin.natAdd n j := by
      change Fin.addCases (motive := fun _ : Fin (n+n) => Fin (n+n))
        (Fin.castAdd n) (fun k => Fin.natAdd n (matched.symm k))
        (Fin.natAdd n (matched j)) = _
      rw [Fin.addCases_right, matched.symm_apply_apply]
    constructor
    · rintro ⟨i,j,he,hl,hr⟩
      have hl' : x (Fin.castAdd n i) = true := by simpa only [leftCast] using hl
      rcases (row i j).mp he with rfl | rfl
      · exact ⟨i, hl', Or.inl (by simpa only [rightCast] using hr)⟩
      · exact ⟨i, hl', Or.inr (by simpa only [rightCast] using hr)⟩
    · rintro ⟨i,hl,hr | hr⟩
      · exact ⟨i, matched i, (row _ _).mpr (Or.inl rfl),
          by simpa only [leftCast] using hl, by simpa only [rightCast] using hr⟩
      · exact ⟨i, matched (next i), (row _ _).mpr (Or.inr rfl),
          by simpa only [leftCast] using hl, by simpa only [rightCast] using hr⟩

  intro n E matching C many basic c4 diag AO agree extra
  by_cases regular : ∀ i : Fin n, (Finset.univ.filter fun j => (i,j) ∈ E).card = 2
  · obtain ⟨next, nf, nc, row, card⟩ :=
      two_regular_permutation E matching c4 diag extra.1 extra.2 regular
    have pos : 0 < n := by rw [card] at many; omega
    have enough := cycle_length_lower next pos nf nc
    let D := mapCircuit (renumberRight matching) C
    have same : D.size = C.size := by
      change (C.gates.map (mapGate (renumberRight matching))).length = C.gates.length
      simp
    have alt : IsAO2 (n+n) D := map_ao _ _ AO
    have evaluates := diagonal_semantics E matching next C row agree
    have hbound := cycles n next D enough nf nc alt evaluates
    rw [same] at hbound
    rw [card]
    omega
  · push Not at regular
    obtain ⟨i, neq⟩ := regular
    have bound := row_degree_lower E matching diag extra.1 i
    have large : ∃ i : Fin n, 3 ≤ (Finset.univ.filter fun j => (i,j) ∈ E).card :=
      ⟨i, by omega⟩
    have hthree : 2 < (Finset.univ.filter fun j => (i,j) ∈ E).card := by omega
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp hthree
    exact wider n E matching C (dense_size_lower E matching c4 diag extra.1 large)
      many basic c4 diag AO agree extra
      ⟨i,a,b,c,ab,ac,bc,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2,(Finset.mem_filter.mp hc).2⟩
