import Mathlib

set_option maxRecDepth 10000 in
set_option maxHeartbeats 9000000 in
theorem PEqualNP.Outside.R_meta_4649_487
  (loss : ∀ (m s : ℕ) (e v d : ℕ → Bool) (a b : ℕ → ℕ) (o : ℕ → Bool),
    (∀ i < m, e i = true → v i = true ∨ d i = true) →
    (∀ i < s, a i < m+i ∧ b i < m+i ∧
      (o i = true → e (m+i) = (e (a i) || e (b i)) ∧ v (m+i) = (v (a i) || v (b i)) ∧
        d (m+i) = (d (a i) || d (b i))) ∧
      (o i = false → e (m+i) = (e (a i) && e (b i)) ∧ v (m+i) = (v (a i) && v (b i)) ∧
        d (m+i) = ((v (a i) && d (b i)) || (d (a i) && v (b i))))) →
    ∀ w < m+s, e w = true → v w = false → d w = false →
      ∃ i < s, o i = false ∧ e (a i) = true ∧ e (b i) = true ∧
        v (a i) = false ∧ v (b i) = false ∧
        Relation.ReflTransGen (fun x y => m ≤ y ∧ (x = a (y-m) ∨ x = b (y-m)) ∧
          e x = true ∧ v x = false ∧ d x = false) (m+i) w)
  (obstruction :
    let inputs : List ℕ := [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]
    ¬∃ (k : ℕ) (W : ℕ → Fin 62 → Bool) (a b : ℕ → ℕ) (o : ℕ → Bool),
      k ≤ 27 ∧ W (13+k) = (fun t => decide (t.val < 21)) ∧
      (∀ i < 14, W i = (fun t => (inputs.getD i 0).testBit t.val)) ∧ o 0 = true ∧
      (∀ i < k, a i < b i ∧ b i < 14+i ∧ ∀ t, W (14+i) t =
        if o i = true then (W (a i) t || W (b i) t)
        else if t = 60 then (W (a i) 58 && W (b i) 60 || W (a i) 60 && W (b i) 58)
        else if t = 61 then (W (a i) 59 && W (b i) 61 || W (a i) 61 && W (b i) 59)
        else (W (a i) t && W (b i) t)) ∧
      ∀ t : Bool,
        let v : ℕ → Bool := fun j => W j (if t = true then 58 else 59)
        let d : ℕ → Bool := fun j => W j (if t = true then 60 else 61)
        ∃ i < k, o i = false ∧ W (a i) 0 = true ∧ W (b i) 0 = true ∧
          v (a i) = false ∧ v (b i) = false ∧
          Relation.ReflTransGen (fun x y => 14 ≤ y ∧ (x = a (y-14) ∨ x = b (y-14)) ∧
            W x 0 = true ∧ v x = false ∧ d x = false) (14+i) (13+k)) :
  have x1 : List (Fin (62 : ℕ) → Bool) := List.map (fun (x1 : ℕ) (x2 : Fin (62 : ℕ)) => x1.testBit ↑x2) [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]; ¬∃ (x2 : List (Fin (62 : ℕ) → Bool)),     x2.length ≤ (27 : ℕ) ∧       (fun (x3 : Fin (62 : ℕ)) => Decidable.decide (↑x3 < (21 : ℕ))) ∈ x2 ∧         ∀ x3 < x2.length,           ∃ (x5 : ℕ) (x6 : ℕ),             x5 ≠ x6 ∧               x5 < (14 : ℕ) + x3 ∧                 x6 < (14 : ℕ) + x3 ∧                   have x7 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x5 fun (x7 : Fin (62 : ℕ)) => Bool.false;                   have x8 : Fin (62 : ℕ) → Bool := (x1 ++ x2).getD x6 fun (x8 : Fin (62 : ℕ)) => Bool.false;                   ((x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => x7 x9 || x8 x9) ∨ (0 : ℕ) < x3 ∧ (x2.getD x3 fun (x9 : Fin (62 : ℕ)) => Bool.false) = fun (x9 : Fin (62 : ℕ)) => if x9 = (60 : Fin (62 : ℕ)) then x7 (58 : Fin (62 : ℕ)) && x8 (60 : Fin (62 : ℕ)) || x7 (60 : Fin (62 : ℕ)) && x8 (58 : Fin (62 : ℕ)) else if x9 = (61 : Fin (62 : ℕ)) then x7 (59 : Fin (62 : ℕ)) && x8 (61 : Fin (62 : ℕ)) || x7 (61 : Fin (62 : ℕ)) && x8 (59 : Fin (62 : ℕ)) else x7 x9 && x8 x9 := by
  intro seed witness
  obtain ⟨s,cap,found,gates⟩ := witness
  obtain ⟨w,hw,out⟩ := List.mem_iff_getElem.mp found
  let empty : Fin 62 → Bool := fun _ => false
  let W (i : ℕ) := (seed ++ s).getD i empty
  let input : List ℕ := [(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)]
  have seedEq : seed = input.map (fun v t => Nat.testBit v (t : Fin 62).val) := rfl
  have seedLen : seed.length = 14 := rfl
  have primary i (hi : i < 14) : W i = (fun t => (input.getD i 0).testBit t.val) := by
    dsimp only [W]
    rw [List.getD_append _ _ _ _ (by rw [seedLen]; exact hi),seedEq]
    have eq : empty = (fun t : Fin 62 => (0 : ℕ).testBit t.val) :=
      funext (fun t => (Nat.zero_testBit t.val).symm)
    rw [eq]
    rw [List.getD_map]
  have indexed i : W (14+i) = s.getD i empty := by
    dsimp [W]
    rw [List.getD_append_right _ _ _ _ (by rw [seedLen]; omega),seedLen]
    congr 1
    omega
  have target : W (14+w) = (fun t => decide (t.val < 21)) := by
    rw [indexed,List.getD_eq_getElem _ _ hw]
    exact out
  let combine (o : Bool) (A B : Fin 62 → Bool) (t : Fin 62) :=
    if o = true then (A t || B t)
    else if t = 60 then (A 58 && B 60 || A 60 && B 58)
    else if t = 61 then (A 59 && B 61 || A 61 && B 59)
    else (A t && B t)
  have commutes (o : Bool) (A B : Fin 62 → Bool) : combine o A B = combine o B A := by
    funext t
    dsimp [combine]
    split
    · exact Bool.or_comm _ _
    · split
      · ac_rfl
      · split
        · ac_rfl
        · exact Bool.and_comm _ _
  have normalized (j : Fin (w+1)) : ∃ (a b : ℕ) (o : Bool), a < b ∧ b < 14+j.val ∧
      (j.val = 0 → o = true) ∧ W (14+j.val) = combine o (W a) (W b) := by
    have hj : j.val < s.length := by have := j.isLt; omega
    obtain ⟨a,b,diff,ha,hb,op⟩ := gates j.val hj
    have permits : ∃ o : Bool,
        (j.val = 0 → o = true) ∧ W (14+j.val) = combine o (W a) (W b) := by
      rw [indexed]
      rcases op with hor | ⟨pos,hand⟩
      · exact ⟨true,fun _ => rfl,hor⟩
      · exact ⟨false,fun hz => False.elim (by omega),hand⟩
    obtain ⟨o,first,eval⟩ := permits
    rcases lt_or_gt_of_ne diff with ab | ba
    · exact ⟨a,b,o,ab,hb,first,eval⟩
    · exact ⟨b,a,o,ba,ha,first,eval.trans (commutes _ _ _)⟩
  choose A B O strict earlier first eval using normalized
  let a (i : ℕ) := if h : i < w+1 then A ⟨i,h⟩ else 0
  let b (i : ℕ) := if h : i < w+1 then B ⟨i,h⟩ else 0
  let o (i : ℕ) := if h : i < w+1 then O ⟨i,h⟩ else false
  have limits i (hi : i < w+1) : a i < b i ∧ b i < 14+i := by
    simpa only [a,b,dif_pos hi] using And.intro (strict ⟨i,hi⟩) (earlier ⟨i,hi⟩)
  have run i (hi : i < w+1) : W (14+i) = combine (o i) (W (a i)) (W (b i)) := by
    simpa only [a,b,o,dif_pos hi] using eval ⟨i,hi⟩
  have atZero : o 0 = true := by
    have hi : 0 < w+1 := by omega
    simpa [o,hi] using first ⟨0,hi⟩ rfl
  apply obstruction
  refine ⟨w+1,W,a,b,o,by omega,?_,primary,atZero,?_,?_⟩
  · rwa [show 13+(w+1) = 14+w by omega]
  · intro i hi
    refine ⟨(limits i hi).1,(limits i hi).2,fun t => congrFun (run i hi) t⟩
  · intro side
    let base : Fin 62 := if side = true then 58 else 59
    let slope : Fin 62 := if side = true then 60 else 61
    have inputsOK : ∀ i < 14, W i 0 = true → W i base = true ∨ W i slope = true := by
      have bits : ∀ (i : Fin 14) (side : Bool),
          let value : Fin 62 → Bool := fun t => (input.getD i.val 0).testBit t.val
          value 0 = true → value (if side = true then 58 else 59) = true ∨
            value (if side = true then 60 else 61) = true := by
        decide +kernel
      intro i hi
      rw [primary i hi]
      exact bits ⟨i,hi⟩ side
    have ready : W (14+w) 0 = true ∧ W (14+w) base = false ∧ W (14+w) slope = false := by
      rw [target]
      cases side <;> decide
    have square := loss 14 (w+1) (fun j => W j 0) (fun j => W j base) (fun j => W j slope)
      a b o inputsOK (by
        intro i hi
        obtain ⟨sorted,previous⟩ := limits i hi
        refine ⟨sorted.trans previous,previous,?_,?_⟩
        · intro hor
          rw [run i hi]
          simp [combine,hor]
        · intro hand
          rw [run i hi]
          cases side <;> simp [combine,hand,base,slope])
      (14+w) (by omega) ready.1 ready.2.1 ready.2.2
    simpa only [show 13+(w+1) = 14+w by omega] using square
