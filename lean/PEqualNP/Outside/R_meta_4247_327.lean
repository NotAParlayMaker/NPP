import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4247_327
    (small : let idx := fun j : Fin 14 => Fin.ofNat 16 (if j.val = 0 then 0 else if j.val < 9 then j.val+1 else j.val+2)
      let has := fun (y : Fin 14 → Bool) (m : ℕ) => ∀ i : Fin 14, m.testBit (idx i).val = true → y i = true
      let low : List ℕ := [33, 40, 68, 80, 132, 136, 264, 272, 513, 528, 2052, 4104, 8208, 16385, 32769, 32772]
      let high := fun s : Fin 6 => ([34,66] : List ℕ) ++ (if s.val=5 then [6291,25102] else ([6291,12551,25102,51226] : List ℕ).take s.val)
      ∃ (D : Circuit) (j : ℕ) (s : Fin 6), Monotone2 D ∧ NestedCover.ReadsBack 14 D ∧
        D.size ≤ 19 ∧ D.output < 14+D.size ∧ j < 14+D.size ∧ ∀ y : Fin 14 → Bool,
          let w := D.wires (List.ofFn y)
          (w.getD D.output false = decide (∃ m ∈ low, has y m)) ∧
          (w.getD D.output false = false → w.getD j false = decide (∃ m ∈ high s, has y m)))
    (attach : ∀ (D : Circuit) (j : ℕ), Monotone2 D → NestedCover.ReadsBack 14 D →
      D.output < 14+D.size → j < 14+D.size → ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack 16 C ∧
        C.size ≤ D.size+3 ∧ ∀ x : Fin 16 → Bool,
          let y := x ∘ (fun j : Fin 14 => Fin.ofNat 16 (if j.val = 0 then 0 else if j.val < 9 then j.val+1 else j.val+2))
          let w := D.wires (List.ofFn y)
          circuitFun 16 C x = (w.getD D.output false || (x 1 && (x 10 || w.getD j false)))) :
    have x1 : List ℕ := [(33 : ℕ), (34 : ℕ), (40 : ℕ), (66 : ℕ), (68 : ℕ), (80 : ℕ), (132 : ℕ), (136 : ℕ), (264 : ℕ), (272 : ℕ), (513 : ℕ), (528 : ℕ), (1026 : ℕ), (2052 : ℕ), (4104 : ℕ), (8208 : ℕ), (16385 : ℕ), (32769 : ℕ), (32772 : ℕ)]; have x2 : List ℕ := [(6291 : ℕ), (12551 : ℕ), (25102 : ℕ), (51226 : ℕ)]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (6 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x3 ∧ x3.size ≤ (22 : ℕ) ∧ ∀ (x5 : Fin (16 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x3 x5 = Decidable.decide (∃ x6 ∈ x1 ++ if ↑x4 = (5 : ℕ) then [(6291 : ℕ), (25102 : ℕ)] else List.take (↑x4) x2, ∀ (x7 : Fin (16 : ℕ)), x6.testBit ↑x7 = Bool.true → x5 x7 = Bool.true) := by
  let low : List ℕ := [33, 40, 68, 80, 132, 136, 264, 272, 513, 528, 2052, 4104, 8208, 16385, 32769, 32772]
  let high := fun s : Fin 6 => ([34,66] : List ℕ) ++ (if s.val=5 then [6291,25102] else ([6291,12551,25102,51226] : List ℕ).take s.val)
  let full := fun s : Fin 6 => ([33, 34, 40, 66, 68, 80, 132, 136, 264, 272, 513, 528, 1026, 2052, 4104, 8208, 16385, 32769, 32772] : List ℕ) ++
    (if s.val=5 then [6291,25102] else ([6291,12551,25102,51226] : List ℕ).take s.val)
  let idx := fun j : Fin 14 => Fin.ofNat 16 (if j.val = 0 then 0 else if j.val < 9 then j.val+1 else j.val+2)
  let has := fun (y : Fin 14 → Bool) (m : ℕ) => ∀ i : Fin 14, m.testBit (idx i).val = true → y i = true
  have sets : ∀ s : Fin 6, (full s).Perm (low ++ [1026] ++ high s) := by decide +kernel
  have flagsL : ∀ m ∈ low, m.testBit 1 = false ∧ m.testBit 10 = false := by decide
  have flagsH : ∀ s : Fin 6, ∀ m ∈ high s, m.testBit 1 = true ∧ m.testBit 10 = false := by decide
  have none : ∀ j : Fin 14, (1026 : ℕ).testBit (idx j).val = false := by decide
  obtain ⟨D,j,s,md,rd,bd,od,jd,sem⟩ := small
  obtain ⟨C,mc,rc,cost,ev⟩ := attach D j md rd od jd
  refine ⟨C,s,mc,rc,by omega,?_⟩
  intro x
  let y := x ∘ idx
  let w := D.wires (List.ofFn y)
  let H := fun m : ℕ => ∀ k : Fin 16, m.testBit k.val = true → x k = true
  have slice (m : ℕ) : H m ↔ has y m ∧ (m.testBit 1=true → x 1=true) ∧
      (m.testBit 10=true → x 10=true)  := by
    have covers : ∀ i : Fin 16, i = 1 ∨ i = 10 ∨ ∃ j : Fin 14, idx j = i := by decide
    constructor
    · intro h
      exact ⟨fun j => h (idx j),h 1,h 10⟩
    · rintro ⟨part,h1,h10⟩ i
      rcases covers i with rfl|rfl|⟨j,rfl⟩
      · exact h1
      · exact h10
      · exact part j
  have lowH (m) (hm : m ∈ low) : H m ↔ has y m := by
    rw [slice]; simp [(flagsL m hm).1,(flagsL m hm).2]
  have highH (m) (hm : m ∈ high s) : H m ↔ has y m ∧ x 1=true := by
    rw [slice]; simp [(flagsH s m hm).1,(flagsH s m hm).2]
  have mid : H 1026 ↔ x 1=true ∧ x 10=true := by
    have hx : has y 1026 := by intro k h; rw [none k] at h; contradiction
    rw [slice]
    simp [hx,show (1026 : ℕ).testBit 1 = true from rfl,show (1026 : ℕ).testBit 10 = true from rfl]
  obtain ⟨hlo,hhi⟩ := sem y
  change w.getD D.output false = decide (∃ m ∈ low, has y m) at hlo
  change w.getD D.output false = false → w.getD j false = decide (∃ m ∈ high s, has y m) at hhi
  have factor : (∃ m ∈ full s, H m) ↔ (∃ m ∈ low, has y m) ∨
      (x 1=true ∧ (x 10=true ∨ ∃ m ∈ high s, has y m)) := by
    constructor
    · rintro ⟨m,hm,v⟩
      have hh := (sets s).mem_iff.mp hm
      simp only [List.mem_append,List.mem_singleton] at hh
      rcases hh with (a|rfl)|b
      · exact Or.inl ⟨m,a,(lowH m a).mp v⟩
      · exact Or.inr ⟨(mid.mp v).1,Or.inl (mid.mp v).2⟩
      · obtain ⟨hm',b1⟩ := (highH m b).mp v
        exact Or.inr ⟨b1,Or.inr ⟨m,b,hm'⟩⟩
    · rintro (⟨m,hm,v⟩|⟨on,b10|⟨m,hm,v⟩⟩)
      · exact ⟨m,(sets s).mem_iff.mpr (by simp [hm]),(lowH m hm).mpr v⟩
      · exact ⟨1026,(sets s).mem_iff.mpr (by simp),mid.mpr ⟨on,b10⟩⟩
      · exact ⟨m,(sets s).mem_iff.mpr (by simp [hm]),(highH m hm).mpr ⟨v,on⟩⟩
  change circuitFun 16 C x = decide (∃ m ∈ full s, H m)
  rw [ev]
  change (w.getD D.output false || (x 1 && (x 10 || w.getD j false))) = _
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,factor]
  cases h : w.getD D.output false with
  | false =>
    have hh := hhi h
    rw [hlo] at h
    have hn := of_decide_eq_false h
    rw [hh]
    simp [hn]
  | true =>
    rw [hlo] at h
    simp [of_decide_eq_true h]
