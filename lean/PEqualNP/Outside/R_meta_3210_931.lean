import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3210_931
    (andCase :
      let pos : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let negs : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      let sources := fun e => (List.range 13).map fun i => P (ix 10 14 e 13 (10+i))
      ¬FormulaSat ((enc 10 14 pos.contains (pos ++ negs)) ++
        [[P (ix 10 14 0 13 0)], [P (ix 10 14 6 0 23)], sources 1, sources 2]))
    (orCase :
      let pos : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
      let negs : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
      let sources := fun e => (List.range 13).map fun i => P (ix 10 14 e 13 (10+i))
      ¬FormulaSat ((enc 10 14 pos.contains (pos ++ negs)) ++
        [[P (ix 10 14 0 13 1)], [P (ix 10 14 6 0 23)], sources 1, sources 2])) :
    have x1 : List ℕ := [(515 : ℕ), (518 : ℕ), (12 : ℕ), (529 : ℕ), (24 : ℕ), (545 : ℕ), (578 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]; have x2 : List ℕ := [(554 : ℕ), (562 : ℕ), (581 : ℕ), (104 : ℕ), (116 : ℕ), (650 : ℕ), (713 : ℕ), (208 : ℕ), (773 : ℕ), (276 : ℕ), (897 : ℕ), (914 : ℕ)]; ¬PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) (fun (x3 : ℕ) => x1.contains x3) (x1 ++ x2)) := by
  let pos : List Nat := [515,518,12,529,24,545,578,132,160,264,288,320]
  let negs : List Nat := [554,562,581,104,116,650,713,208,773,276,897,914]
  let rows : List Nat := pos ++ negs

  let Satisfies (a : Nat → Bool) : Prop :=
    ∀ c ∈ enc 10 14 pos.contains rows, ClauseSat a c

  let read (a : Nat → Bool) (e j k : Nat) : Bool := a (ix 10 14 e j k + 1)

  have read_eq (a : Nat → Bool) (e j k : Nat) : read a e j k = a (ix 10 14 e j k + 1) := rfl

  let rd (a : Nat → Bool) (j k r : Nat) : Bool :=
    if k < 10 then r.testBit k else if k < 10 + j then read a 3 (k-10) r else false

  have clause_pos (a : Nat → Bool) (v : Nat) : litVal a (P v) = a (v+1) := by
    unfold litVal P
    have h₁ : (2 * v + 2) / 2 = v+1 := by omega
    have h₂ : (2 * v + 2) % 2 = 0 := by omega
    simp [h₁,h₂]

  have clause_neg (a : Nat → Bool) (v : Nat) : litVal a (Q v) = !(a (v+1)) := by
    unfold litVal Q
    have h₁ : (2 * v + 3) / 2 = v+1 := by omega
    have h₂ : (2 * v + 3) % 2 = 1 := by omega
    simp [h₁,h₂]

  have clause_lit (a : Nat → Bool) (v : Nat) (b : Bool) :
      litVal a (L v b) = (a (v+1) == b) := by
    delta L
    cases b <;> simp [clause_pos,clause_neg]

  have clause_cons (a : Nat → Bool) (l : Nat) (ls : List Nat) :
      ClauseSat a (l :: ls) ↔ litVal a l = true ∨ ClauseSat a ls := by
    delta ClauseSat
    simp only [List.mem_cons]
    constructor
    · rintro ⟨w, h | h, hw⟩
      · exact Or.inl (h ▸ hw)
      · exact Or.inr ⟨w,h,hw⟩
    · rintro (h | ⟨w,hw₁,hw₂⟩)
      · exact ⟨l,Or.inl rfl,h⟩
      · exact ⟨w,Or.inr hw₁,hw₂⟩

  have clause_nil (a : Nat → Bool) : ClauseSat a [] ↔ False := by
    delta ClauseSat
    simp

  have op_available {a : Nat → Bool} (h : Satisfies a) {j : Nat} (hj : j < 14) :
      ∃ t : Nat, t < 3 ∧ read a 0 j t = true := by
    have hc : ClauseSat a [P (ix 10 14 0 j 0), P (ix 10 14 0 j 1), P (ix 10 14 0 j 2)] := by
      apply h
      have hm : [P (ix 10 14 0 j 0), P (ix 10 14 0 j 1), P (ix 10 14 0 j 2)] ∈ fOp 10 14 :=
        List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hm)))))))))))
    simp only [clause_cons, clause_pos, clause_nil, or_false, ← read_eq] at hc
    rcases hc with h₀ | h₁ | h₂
    · exact ⟨0,by decide,h₀⟩
    · exact ⟨1,by decide,h₁⟩
    · exact ⟨2,by decide,h₂⟩

  have src_available {a : Nat → Bool} (h : Satisfies a) {e j : Nat}
      (he : e ∈ [1,2]) (hj : j < 14) :
      ∃ k : Nat, k ≤ 10+j ∧ read a e j k = true := by
    let c := (List.range (10+j+1)).map (fun k => P (ix 10 14 e j k))
    have hc : ClauseSat a c := by
      apply h
      have hm : c ∈ fSrcAlo 10 14 :=
        List.mem_flatMap.mpr ⟨e,he,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))))))))
    obtain ⟨l,hl,ht⟩ := hc
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    exact ⟨k, by have hx := List.mem_range.mp hk; omega, by simpa [clause_pos,read] using ht⟩

  have source_reads {a : Nat → Bool} (h : Satisfies a) {e j k r : Nat}
      (he : e ∈ [1,2]) (hj : j < 14) (hk : k ≤ 10+j) (hr : r ∈ rows)
      (on : read a e j k = true) : read a (e+3) j r = rd a j k r := by
    have hs : ∀ c ∈ srcEq 10 14 e j k r, ClauseSat a c := by
      intro c hc
      apply h
      have hm : c ∈ fSrcEq 10 14 rows :=
        List.mem_flatMap.mpr ⟨e,he,List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,
        List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),hc⟩⟩⟩⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))))))
    by_cases hi : k < 10
    · have hh := hs [Q (ix 10 14 e j k), L (ix 10 14 (e+3) j r) (r.testBit k)] (by delta srcEq; simp [hi])
      simpa [clause_cons,clause_neg,clause_lit,clause_nil, ← read_eq,on,rd,hi] using hh
    · by_cases hg : k < 10+j
      · have h₁ := hs [Q (ix 10 14 e j k), Q (ix 10 14 (e+3) j r), P (ix 10 14 3 (k-10) r)]
          (by delta srcEq; simp [hi,hg])
        have h₂ := hs [Q (ix 10 14 e j k), P (ix 10 14 (e+3) j r), Q (ix 10 14 3 (k-10) r)]
          (by delta srcEq; simp [hi,hg])
        simp only [clause_cons,clause_neg,clause_pos,clause_nil, ← read_eq,on, Bool.not_true,
          Bool.false_eq_true, false_or, or_false, rd, hi, hg, ite_false, ite_true] at h₁ h₂ ⊢
        cases ha : read a (e+3) j r <;> cases hb : read a 3 (k-10) r <;> simp_all
      · have hh := hs [Q (ix 10 14 e j k),Q (ix 10 14 (e+3) j r)] (by delta srcEq; simp [hi,hg])
        simpa [clause_cons,clause_neg,clause_nil, ← read_eq,on,rd,hi,hg] using hh

  have gate_reads {a : Nat → Bool} (h : Satisfies a) {j r : Nat}
      (hj : j < 14) (hr : r ∈ rows) :
      (read a 0 j 0 = true → read a 3 j r = (read a 4 j r && read a 5 j r)) ∧
      (read a 0 j 1 = true → read a 3 j r = (read a 4 j r || read a 5 j r)) ∧
      (read a 0 j 2 = true → read a 3 j r = true) := by
    have hs : ∀ c ∈ gateCl 10 14 j r, ClauseSat a c := by
      intro c hc
      apply h
      have hm : c ∈ fGate 10 14 rows := List.mem_flatMap.mpr
        ⟨j,List.mem_range.mpr hj,List.mem_flatMap.mpr ⟨r,hr,hc⟩⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))))))
    have h₀ := hs [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 4 j r)]
      (by delta gateCl; simp)
    have h₁ := hs [Q (ix 10 14 0 j 0), Q (ix 10 14 3 j r), P (ix 10 14 5 j r)]
      (by delta gateCl; simp)
    have h₂ := hs [Q (ix 10 14 0 j 0), P (ix 10 14 3 j r), Q (ix 10 14 4 j r), Q (ix 10 14 5 j r)]
      (by delta gateCl; simp)
    have h₃ := hs [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 4 j r)]
      (by delta gateCl; simp)
    have h₄ := hs [Q (ix 10 14 0 j 1), P (ix 10 14 3 j r), Q (ix 10 14 5 j r)]
      (by delta gateCl; simp)
    have h₅ := hs [Q (ix 10 14 0 j 1), Q (ix 10 14 3 j r), P (ix 10 14 4 j r), P (ix 10 14 5 j r)]
      (by delta gateCl; simp)
    have h₆ := hs [Q (ix 10 14 0 j 2), P (ix 10 14 3 j r)] (by delta gateCl; simp)
    simp only [clause_cons,clause_pos,clause_neg,clause_nil,or_false, ← read_eq] at h₀ h₁ h₂ h₃ h₄ h₅ h₆
    cases hv : read a 3 j r <;> cases hL : read a 4 j r <;> cases hR : read a 5 j r <;> simp_all

  have out_available {a : Nat → Bool} (h : Satisfies a) :
      ∃ k : Nat, k ≤ 24 ∧ read a 6 0 k = true := by
    let c := (List.range 25).map (fun k => P (ix 10 14 6 0 k))
    have hc : ClauseSat a c := by
      apply h
      have hm : c ∈ fOutAlo 10 14 := by delta fOutAlo; simp [c]
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))))
    obtain ⟨l,hl,ht⟩ := hc
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    exact ⟨k, by have hx := List.mem_range.mp hk; omega, by simpa [clause_pos,read] using ht⟩

  have out_reads {a : Nat → Bool} (h : Satisfies a) {k r : Nat}
      (hk : k ≤ 24) (hr : r ∈ rows) (on : read a 6 0 k = true) : rd a 14 k r = pos.contains r := by
    have hs : ∀ c ∈ outEq 10 14 pos.contains k r, ClauseSat a c := by
      intro c hc
      apply h
      have hm : c ∈ fOutEq 10 14 pos.contains rows :=
        List.mem_flatMap.mpr ⟨r,hr,List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),hc⟩⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))))
    by_cases hi : k < 10
    · simp only [rd,hi,ite_true]
      by_contra hm
      have hc := hs [Q (ix 10 14 6 0 k)] (by delta outEq; simp only [hi,hm,ite_true,ite_false,List.mem_singleton])
      simp [clause_cons,clause_neg,clause_nil, ← read_eq,on] at hc
    · by_cases hg : k < 24
      · have hc := hs [Q (ix 10 14 6 0 k),L (ix 10 14 3 (k-10) r) (pos.contains r)]
          (by delta outEq; simp [hi,hg])
        simpa [clause_cons,clause_neg,clause_lit,clause_nil, ← read_eq,on,rd,hi,hg] using hc
      · simp only [rd,hi,hg,ite_false]
        by_cases ht : pos.contains r = true
        · have hc := hs [Q (ix 10 14 6 0 k)] (by delta outEq; simp only [hi,hg,ht,ite_true,ite_false,List.mem_singleton])
          simp [clause_cons,clause_neg,clause_nil, ← read_eq,on] at hc
        · exact (Bool.eq_false_iff.mpr ht).symm



  change ¬FormulaSat (enc 10 14 pos.contains rows)
  intro sat
  obtain ⟨a, ha⟩ := sat
  have h : Satisfies a := ha
  have zeros : ∀ r ∈ negs, pos.contains r = false := by decide +kernel
  have negRow : (554 : Nat) ∈ rows := by decide +kernel
  have posRow : (515 : Nat) ∈ rows := by decide +kernel
  have allPos (k : Fin 10) : (pos.any fun r => !r.testBit k.val) = true := by
    revert k
    decide +kernel
  have allNeg (k : Fin 10) : (negs.any fun r => r.testBit k.val) = true := by
    revert k
    decide +kernel
  have rawHasFalse (k : Nat) (hk : k < 10) :
      ∃ r ∈ rows, pos.contains r = true ∧ r.testBit k = false := by
    obtain ⟨r,hr,hoff⟩ := List.any_eq_true.mp (allPos ⟨k,hk⟩)
    exact ⟨r,List.mem_append_left _ hr,List.contains_iff_mem.mpr hr,by simpa using hoff⟩
  have rawHasTrue (k : Nat) (hk : k < 10) :
      ∃ r ∈ rows, pos.contains r = false ∧ r.testBit k = true := by
    obtain ⟨r,hr,hon⟩ := List.any_eq_true.mp (allNeg ⟨k,hk⟩)
    exact ⟨r,List.mem_append_right _ hr,zeros r hr,hon⟩
  have earlierPad (j : Nat) (hj : j < 13) :
      read a 7 (j+1) 0 = true → read a 7 j 0 = true := by
    have c : ClauseSat a [Q (ix 10 14 7 (j+1) 0),P (ix 10 14 7 j 0)] := by
      apply h
      have hm : [Q (ix 10 14 7 (j+1) 0),P (ix 10 14 7 j 0)] ∈ fPre 10 14 :=
        List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
    intro hp
    simpa [clause_cons,clause_neg,clause_pos,clause_nil,← read_eq,hp] using c
  have padOperation (j : Nat) (hj : j < 14) :
      read a 7 j 0 = true → read a 0 j 2 = true := by
    have c : ClauseSat a [Q (ix 10 14 7 j 0), P (ix 10 14 0 j 2)] := by
      apply h
      have hm : [Q (ix 10 14 7 j 0), P (ix 10 14 0 j 2)] ∈ fPad 10 14 :=
        List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,by simp⟩
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))
    intro hp
    simpa [clause_cons,clause_neg,clause_pos,clause_nil,← read_eq,hp] using c
  have lastNotPad : read a 7 13 0 = false := by
    apply Bool.eq_false_iff.mpr
    intro hp
    have allPad (j : Nat) (hj : j ≤ 13) : read a 7 j 0 = true := by
      have aux (i j : Nat) (e : j+i=13) : read a 7 j 0 = true := by
        induction i generalizing j with
        | zero =>
          have ej : j=13 := by omega
          simpa [ej] using hp
        | succ i ih => exact earlierPad j (by omega) (ih (j+1) (by omega))
      exact aux (13-j) j (by omega)
    obtain ⟨k,hk,ho⟩ := out_available h
    by_cases hraw : k < 10
    · obtain ⟨r,hr,hn,on⟩ := rawHasTrue k hraw
      have he := out_reads h hk hr ho
      simp only [rd,hraw,ite_true,on,hn,Bool.true_eq_false] at he
    · by_cases hg : k < 24
      · have hj : k-10 < 14 := by omega
        have ht := (gate_reads h hj negRow).2.2 (padOperation _ hj (allPad _ (by omega)))
        have he := out_reads h hk negRow ho
        have hn : pos.contains 554 = false := by decide +kernel
        simp only [rd,hraw,hg,ite_false,ite_true,ht,hn,Bool.true_eq_false] at he
      · have he := out_reads h hk posRow ho
        have hn : pos.contains 515 = true := by decide +kernel
        simp only [rd,hraw,hg,ite_false,hn,Bool.false_eq_true] at he
  have lastOutput : read a 6 0 23 = true := by
    have c : ClauseSat a [P (ix 10 14 6 0 23),P (ix 10 14 7 13 0)] := by
      apply h
      have hm : [P (ix 10 14 6 0 23),P (ix 10 14 7 13 0)] ∈ fOut 10 14 := by decide +kernel
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm)))))
    simpa [clause_cons,clause_pos,clause_nil,← read_eq,lastNotPad] using c
  have lastValue (r : Nat) (hr : r ∈ rows) : read a 3 13 r = pos.contains r := by
    have he := out_reads h (k := 23) (by decide) hr lastOutput
    exact he
  have lastNoTrue : read a 0 13 2 ≠ true := by
    intro ht
    have he := (gate_reads h (j := 13) (by decide) negRow).2.2 ht
    rw [lastValue 554 negRow,show pos.contains 554 = false by decide +kernel] at he
    contradiction
  have noConst (e : Nat) (he : e ∈ [1,2]) : read a e 13 23 = false := by
    have c : ClauseSat a [P (ix 10 14 7 13 0),Q (ix 10 14 e 13 23)] := by
      apply h
      have hm : [P (ix 10 14 7 13 0),Q (ix 10 14 e 13 23)] ∈ fPad 10 14 := by
        apply List.mem_flatMap.mpr
        refine ⟨13,by decide,?_⟩
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl <;> decide +kernel
      delta enc
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))
    simpa [clause_cons,clause_pos,clause_neg,clause_nil,← read_eq,lastNotPad] using c
  have innerSource (d : Bool) (hop : read a 0 13 (if d then 1 else 0) = true)
      (e : Nat) (he : e ∈ [1,2]) :
      ClauseSat a ((List.range 13).map fun i => P (ix 10 14 e 13 (10+i))) := by
    obtain ⟨k,hk,hsrc⟩ := src_available h he (j := 13) (by decide)
    have hnotPad : k < 23 := by
      by_contra hn
      have heq : k = 23 := by omega
      rw [heq,noConst e he] at hsrc
      contradiction
    have hnotRaw : 10 ≤ k := by
      by_contra! hraw
      cases d
      · obtain ⟨r,hr,hy,hoff⟩ := rawHasFalse k hraw
        have hsource := source_reads h he (by decide) hk hr hsrc
        have hval := (gate_reads h (j := 13) (by decide) hr).1 hop
        rw [lastValue r hr,hy] at hval
        simp only [rd,hraw,ite_true,hoff] at hsource
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl
        · change read a 4 13 r = false at hsource
          simp [hsource] at hval
        · change read a 5 13 r = false at hsource
          simp [hsource] at hval
      · obtain ⟨r,hr,hy,hon⟩ := rawHasTrue k hraw
        have hsource := source_reads h he (by decide) hk hr hsrc
        have hval := (gate_reads h (j := 13) (by decide) hr).2.1 hop
        rw [lastValue r hr,hy] at hval
        simp only [rd,hraw,ite_true,hon] at hsource
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl | rfl
        · change read a 4 13 r = true at hsource
          simp [hsource] at hval
        · change read a 5 13 r = true at hsource
          simp [hsource] at hval
    refine ⟨P (ix 10 14 e 13 k),List.mem_map.mpr ?_,by simpa [clause_pos,← read_eq] using hsrc⟩
    exact ⟨k-10,List.mem_range.mpr (by omega),by rw [show 10+(k-10)=k by omega]⟩
  have selected (d : Bool) (hop : read a 0 13 (if d then 1 else 0) = true) :
      FormulaSat ((enc 10 14 pos.contains rows) ++
        [[P (ix 10 14 0 13 (if d then 1 else 0))], [P (ix 10 14 6 0 23)],
         (List.range 13).map (fun i => P (ix 10 14 1 13 (10+i))),
         (List.range 13).map (fun i => P (ix 10 14 2 13 (10+i)))]) := by
    refine ⟨a,?_⟩
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h c hc
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · simp [clause_cons,clause_pos,clause_nil,← read_eq,hop]
      · simp [clause_cons,clause_pos,clause_nil,← read_eq,lastOutput]
      · exact innerSource d hop 1 (by decide)
      · exact innerSource d hop 2 (by decide)
  obtain ⟨t,ht,htrue⟩ := op_available h (j := 13) (by decide)
  interval_cases t
  · exact andCase (selected false htrue)
  · exact orCase (selected true htrue)
  · exact lastNoTrue htrue
