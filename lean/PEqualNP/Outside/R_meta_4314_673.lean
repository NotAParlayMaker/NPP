import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- This reduction for L-meta-4314 removes the two final gate slots. The two
-- children forbid a circuit on the first 12 slots whose final expression matches the
-- 24 target rows, using either A ∨ (B ∧ C) or A ∨ (B ∨ C). In the second
-- case all three operands are internal gate outputs.
--
-- To retain the constraints on these slots, decode each literal into a variable block
-- of width 1049 and keep clauses entirely in the first 12 slots, omitting the
-- output selector. There are 15 slots per variable kind in this encoding.

open PEqualNP.Defs.LratEncoding

set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.R_meta_4314_673
    (hAnd :
      let y : List ℕ := [515, 518, 12, 529, 24, 545, 578, 132, 160, 264, 288, 320]
      let n : List ℕ := [554, 562, 581, 104, 116, 650, 713, 208, 773, 276, 897, 914]
      let rs := y ++ n
      let earlyClauses := (enc 10 14 y.contains rs).filter fun c => c.all fun l =>
        let blk := (l / 2 - 1) / 1049
        decide (blk % 15 < 12 ∧ blk / 15 ≠ 6)
      ¬ ∃ (a : ℕ → Bool) (i j k : ℕ),
        let w := fun (q r : ℕ) => if q < 10 then r.testBit q else a (ix 10 14 3 (q - 10) r + 1)
        i < 12 ∧ j < k ∧ k < 22 ∧
        (∀ c ∈ earlyClauses, ClauseSat a c) ∧
        (∀ r ∈ rs, (a (ix 10 14 3 i r + 1) || (w j r && w k r)) = y.contains r))
    (hOr :
      let y : List ℕ := [515, 518, 12, 529, 24, 545, 578, 132, 160, 264, 288, 320]
      let n : List ℕ := [554, 562, 581, 104, 116, 650, 713, 208, 773, 276, 897, 914]
      let rs := y ++ n
      let earlyClauses := (enc 10 14 y.contains rs).filter fun c => c.all fun l =>
        let blk := (l / 2 - 1) / 1049
        decide (blk % 15 < 12 ∧ blk / 15 ≠ 6)
      ¬ ∃ (a : ℕ → Bool) (i j k : ℕ),
        let w := fun (q r : ℕ) => if q < 10 then r.testBit q else a (ix 10 14 3 (q - 10) r + 1)
        i < 12 ∧ 10 ≤ j ∧ j < k ∧ k < 22 ∧
        (∀ c ∈ earlyClauses, ClauseSat a c) ∧
        (∀ r ∈ rs, (a (ix 10 14 3 i r + 1) || (w j r || w k r)) = y.contains r))
    : have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2) ++ [[PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (0 : ℕ) (13 : ℕ) (1 : ℕ))], [PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (2 : ℕ) (13 : ℕ) (22 : ℕ))], List.map (fun (x3 : ℕ) => PEqualNP.Defs.LratEncoding.P (PEqualNP.Defs.LratEncoding.ix (10 : ℕ) (14 : ℕ) (1 : ℕ) (13 : ℕ) ((10 : ℕ) + x3))) (List.range (12 : ℕ))]) := by
  let yes : List ℕ := [515, 518, 12, 529, 24, 545, 578, 132, 160, 264, 288, 320]
  let no : List ℕ := [554, 562, 581, 104, 116, 650, 713, 208, 773, 276, 897, 914]
  let rows := yes ++ no
  let base := enc 10 14 yes.contains rows
  let extra : List (List ℕ) :=
    [[P (ix 10 14 0 13 1)], [P (ix 10 14 2 13 22)],
     (List.range 12).map fun i => P (ix 10 14 1 13 (10 + i))]
  change ¬ FormulaSat (base ++ extra)
  rintro ⟨a, ha⟩
  let on := fun e j k => a (ix 10 14 e j k + 1)
  let wire := fun (q r : ℕ) => if q < 10 then r.testBit q else on 3 (q - 10) r
  have baseSat (c : List ℕ) (hc : c ∈ base) := ha c (List.mem_append_left _ hc)
  have extraSat (c : List ℕ) (hc : c ∈ extra) := ha c (List.mem_append_right _ hc)
  have pos (e j k : ℕ) : litVal a (P (ix 10 14 e j k)) = on e j k := by
    let t := ix 10 14 e j k
    change (a ((2 * t + 2) / 2) == ((2 * t + 2) % 2 == 0)) = a (t + 1)
    have h : (2*t+2)/2 = t+1 := by omega
    have q : (2*t+2)%2 = 0 := by omega
    simp [h,q]
  have neg (e j k : ℕ) : litVal a (Q (ix 10 14 e j k)) = !(on e j k) := by
    let t := ix 10 14 e j k
    change (a ((2 * t + 3) / 2) == ((2 * t + 3) % 2 == 0)) = !(a (t + 1))
    have h : (2*t+3)/2 = t+1 := by omega
    have q : (2*t+3)%2 = 1 := by omega
    simp [h,q]
  have clause_rule (c : List ℕ) : ClauseSat a c ↔ ∃ l ∈ c, litVal a l = true := Iff.rfl
  have lit_rule (t : ℕ) (b : Bool) : L t b = (if b then P t else Q t) := by
    cases b <;> rfl
  have lastOr : on 0 13 1 = true := by
    have h := extraSat [P (ix 10 14 0 13 1)] (by simp [extra])
    simpa [clause_rule,pos] using h
  have lastR : on 2 13 22 = true := by
    have h := extraSat [P (ix 10 14 2 13 22)] (by simp [extra])
    simpa [clause_rule,pos] using h
  have lc := extraSat ((List.range 12).map fun i => P (ix 10 14 1 13 (10+i))) (by simp [extra])
  obtain ⟨literal, hm, hyes⟩ := lc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  have hi' : i < 12 := List.mem_range.mp hi
  have lastL : on 1 13 (10+i) = true := by simpa only [pos] using hyes
  -- Extract the clause families used to recover the two final gates.
  have take_gate (c : List ℕ) (hc : c ∈ fGate 10 14 rows) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))))
  have take_src (c : List ℕ) (hc : c ∈ fSrcEq 10 14 rows) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))))))
  have take_alo (c : List ℕ) (hc : c ∈ fSrcAlo 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))))))
  have take_op (c : List ℕ) (hc : c ∈ fOp 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hc)))))))))))
  have take_out (c : List ℕ) (hc : c ∈ fOut 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc)))))
  have take_outEq (c : List ℕ) (hc : c ∈ fOutEq 10 14 yes.contains rows) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))))
  have take_pad (c : List ℕ) (hc : c ∈ fPad 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hc))))
  have take_pre (c : List ℕ) (hc : c ∈ fPre 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hc)))
  have take_rd (c : List ℕ) (hc : c ∈ fPadRd 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr hc))
  have take_ord (c : List ℕ) (hc : c ∈ fOrd 10 14) : ClauseSat a c := by
    apply baseSat c
    change c ∈ enc 10 14 yes.contains rows
    delta enc
    simp only [List.mem_append]
    exact Or.inl (Or.inr hc)
  -- Reading gate 12 forces both tail gates to be active and fixes the output.
  have nonpad12 : on 7 12 0 = false := by
    have h := take_rd [Q (ix 10 14 7 12 0), Q (ix 10 14 2 13 22)] (by
      refine List.mem_flatMap.mpr ⟨13, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      decide)
    simpa [clause_rule,neg,lastR] using h
  have nonpad13 : on 7 13 0 = false := by
    have h := take_pre [Q (ix 10 14 7 13 0), P (ix 10 14 7 12 0)] (by
      exact List.mem_map.mpr ⟨12, by decide, rfl⟩)
    simpa [clause_rule,pos,neg,nonpad12] using h
  have lastOut : on 6 0 23 = true := by
    have h := take_out [P (ix 10 14 6 0 23), P (ix 10 14 7 13 0)] (by decide)
    simpa [clause_rule,pos,nonpad13] using h
  have padAt (c : List ℕ)
      (h : c ∈ [[Q (ix 10 14 7 12 0), P (ix 10 14 0 12 2)],
        [Q (ix 10 14 7 12 0), P (ix 10 14 1 12 22)],
        [Q (ix 10 14 7 12 0), P (ix 10 14 2 12 22)],
        [P (ix 10 14 7 12 0), Q (ix 10 14 0 12 2)],
        [P (ix 10 14 7 12 0), Q (ix 10 14 1 12 22)],
        [P (ix 10 14 7 12 0), Q (ix 10 14 2 12 22)]]) : ClauseSat a c :=
    take_pad c (List.mem_flatMap.mpr ⟨12, by decide, h⟩)
  have noConst : on 0 12 2 = false := by
    have h := padAt [P (ix 10 14 7 12 0), Q (ix 10 14 0 12 2)] (by decide)
    simpa [clause_rule,pos,neg,nonpad12] using h
  have mode : on 0 12 0 = true ∨ on 0 12 1 = true := by
    have h := take_op [P (ix 10 14 0 12 0), P (ix 10 14 0 12 1), P (ix 10 14 0 12 2)]
      (List.mem_map.mpr ⟨12, by decide, rfl⟩)
    simpa [clause_rule,pos,noConst] using h
  have pick (e : ℕ) (he : e = 1 ∨ e = 2) : ∃ k < 22, on e 12 k = true := by
    have hc := take_alo ((List.range 23).map fun k => P (ix 10 14 e 12 k)) (by
      refine List.mem_flatMap.mpr ⟨e, by simpa using he, ?_⟩
      exact List.mem_map.mpr ⟨12, by decide, rfl⟩)
    obtain ⟨t, h, ht⟩ := hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    have hs : on e 12 k = true := by simpa only [pos] using ht
    have bound := List.mem_range.mp hk
    have hn : on e 12 22 = false := by
      have H := padAt [P (ix 10 14 7 12 0), Q (ix 10 14 e 12 22)] (by
        rcases he with rfl | rfl <;> decide)
      simpa [clause_rule,pos,neg,nonpad12] using H
    have ne : k ≠ 22 := by
      intro eq
      simp [eq,hn] at hs
    exact ⟨k, by omega, hs⟩
  obtain ⟨j, hj, hjOn⟩ := pick 1 (Or.inl rfl)
  obtain ⟨k, hk, hkOn⟩ := pick 2 (Or.inr rfl)
  have ordered : j < k := by
    by_contra! h
    have hc := take_ord [Q (ix 10 14 1 12 j), Q (ix 10 14 2 12 k), P (ix 10 14 7 12 0)] (by
      refine List.mem_flatMap.mpr ⟨12, by decide, ?_⟩
      refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by omega), ?_⟩
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    simp [clause_rule,pos,neg,hjOn,hkOn,nonpad12] at hc
  -- Read the selected gate operations and incoming wires on each target row.
  have gateAt (g r : ℕ) (hg : g < 14) (hr : r ∈ rows) (c : List ℕ)
      (hc : c ∈ gateCl 10 14 g r) : ClauseSat a c :=
    take_gate c (List.mem_flatMap.mpr ⟨g,List.mem_range.mpr hg,List.mem_flatMap.mpr ⟨r,hr,hc⟩⟩)
  have andAt (j r : ℕ) (hj : j < 14) (hr : r ∈ rows) (hm : on 0 j 0 = true) :
      on 3 j r = (on 4 j r && on 5 j r) := by
    have c0 := gateAt j r hj hr [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 4 j r)] (by delta gateCl; simp)
    have c1 := gateAt j r hj hr [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 5 j r)] (by delta gateCl; simp)
    have c2 := gateAt j r hj hr [Q (ix 10 14 0 j 0), P (ix 10 14 3 j r), Q (ix 10 14 4 j r), Q (ix 10 14 5 j r)] (by delta gateCl; simp)
    cases u : on 3 j r <;> cases x : on 4 j r <;> cases z : on 5 j r <;>
      simp [clause_rule, pos, neg, hm, u, x, z] at c0 c1 c2 ⊢
  have orAt (j r : ℕ) (hj : j < 14) (hr : r ∈ rows) (hm : on 0 j 1 = true) :
      on 3 j r = (on 4 j r || on 5 j r) := by
    have c0 := gateAt j r hj hr [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 4 j r)] (by delta gateCl; simp)
    have c1 := gateAt j r hj hr [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 5 j r)] (by delta gateCl; simp)
    have c2 := gateAt j r hj hr [Q (ix 10 14 0 j 1), Q (ix 10 14 3 j r), P (ix 10 14 4 j r), P (ix 10 14 5 j r)] (by delta gateCl; simp)
    cases u : on 3 j r <;> cases x : on 4 j r <;> cases z : on 5 j r <;>
      simp [clause_rule, pos, neg, hm, u, x, z] at c0 c1 c2 ⊢
  have sourceAt (e g q r : ℕ) (he : e = 1 ∨ e = 2) (hg : g < 14)
      (hq : q < 10+g) (hr : r ∈ rows) (hs : on e g q = true) :
      on (e+3) g r = wire q r := by
    have fromSrc (c : List ℕ) (hc : c ∈ srcEq 10 14 e g q r) : ClauseSat a c := take_src c (by
      refine List.mem_flatMap.mpr ⟨e, by simpa using he, ?_⟩
      refine List.mem_flatMap.mpr ⟨g, List.mem_range.mpr hg, ?_⟩
      refine List.mem_flatMap.mpr ⟨r, hr, ?_⟩
      exact List.mem_flatMap.mpr ⟨q,List.mem_range.mpr (by omega), hc⟩)
    by_cases primary : q < 10
    · have h := fromSrc [Q (ix 10 14 e g q), L (ix 10 14 (e+3) g r) (r.testBit q)] (by delta srcEq; simp [primary])
      cases u : r.testBit q <;> simpa [wire,primary,u,clause_rule,lit_rule,pos,neg,hs] using h
    · have h1 := fromSrc [Q (ix 10 14 e g q), Q (ix 10 14 (e+3) g r), P (ix 10 14 3 (q-10) r)]
        (by delta srcEq; simp [primary,hq])
      have h2 := fromSrc [Q (ix 10 14 e g q), P (ix 10 14 (e+3) g r), Q (ix 10 14 3 (q-10) r)]
        (by delta srcEq; simp [primary,hq])
      cases u : on (e+3) g r <;> cases t : on 3 (q-10) r <;>
        simp [wire,primary,clause_rule,pos,neg,hs,u,t] at h1 h2 ⊢
  have targetAt (r : ℕ) (hr : r ∈ rows) : on 3 13 r = yes.contains r := by
    have h := take_outEq [Q (ix 10 14 6 0 23), L (ix 10 14 3 13 r) (yes.contains r)] (by
      refine List.mem_flatMap.mpr ⟨r,hr,?_⟩
      refine List.mem_flatMap.mpr ⟨23,by decide,?_⟩
      delta outEq
      simp)
    cases u : yes.contains r <;> rw [u] at h <;> simpa [clause_rule,lit_rule,pos,neg,lastOut] using h
  have covered (r : ℕ) (hr : r ∈ rows) : (on 3 i r || on 3 12 r) = yes.contains r := by
    have hl := sourceAt 1 13 (10+i) r (Or.inl rfl) (by decide) (by omega) hr lastL
    have hh := sourceAt 2 13 22 r (Or.inr rfl) (by decide) (by decide) hr lastR
    have g := orAt 13 r (by decide) hr lastOr
    change on 4 13 r = wire (10+i) r at hl
    change on 5 13 r = wire 22 r at hh
    have hil : ¬10+i < 10 := by omega
    simp [wire,hil] at hl hh
    rw [hl,hh] at g
    exact g.symm.trans (targetAt r hr)
  have lr (r : ℕ) (hr : r ∈ rows) : on 4 12 r = wire j r ∧ on 5 12 r = wire k r :=
    ⟨sourceAt 1 12 j r (Or.inl rfl) (by decide) hj hr hjOn,
     sourceAt 2 12 k r (Or.inr rfl) (by decide) hk hr hkOn⟩
  rcases mode with h | h
  · apply hAnd
    refine ⟨a,i,j,k,hi',ordered,hk,fun c hc => baseSat c (List.mem_filter.mp hc).1,?_⟩
    intro r hr
    change (on 3 i r || (wire j r && wire k r)) = yes.contains r
    have hg := andAt 12 r (by decide) hr h
    rw [(lr r hr).1,(lr r hr).2] at hg
    rw [← hg]
    exact covered r hr
  · have posRows (r : ℕ) (hr : r ∈ rows) :
        (on 3 i r || (wire j r || wire k r)) = yes.contains r := by
      have hg := orAt 12 r (by decide) hr h
      rw [(lr r hr).1,(lr r hr).2] at hg
      rw [← hg]
      exact covered r hr
    have internal : 10 ≤ j := by
      by_contra! primary
      -- Each primary input is true on at least one required negative row.
      let witness := fun (b : Fin 10) => ([581,554,581,554,562,554,581,650,773,554] : List ℕ).getD b.val 0
      have checked : ∀ b : Fin 10, witness b ∈ no ∧ (witness b).testBit b.val = true ∧ yes.contains (witness b) = false := by decide
      obtain ⟨hn, hb, hy⟩ := checked ⟨j,primary⟩
      have eqn := posRows (witness ⟨j,primary⟩) (List.mem_append_right _ hn)
      have wj : wire j (witness ⟨j,primary⟩) = true := by
        change (if j < 10 then _ else _) = true
        simp [primary, hb]
      rw [hy] at eqn
      simp [wj] at eqn
    apply hOr
    exact ⟨a,i,j,k,hi',internal,ordered,hk,fun c hc => baseSat c (List.mem_filter.mp hc).1,posRows⟩
