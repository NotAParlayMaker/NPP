import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2567_713
    (assemble : ∀ (n : ℕ) (C : Circuit) (ws : List ℕ) (b : Bool),
      Monotone2 C → ws ≠ [] → (∀ i ∈ ws, i < n+C.size) →
      ∃ D : Circuit, Monotone2 D ∧ D.size+1 = C.size+ws.length ∧ ∀ x : List Bool, x.length=n →
        D.eval x = if b then ws.all (fun i => (C.wires x).getD i false)
          else ws.any (fun i => (C.wires x).getD i false))
    (frontier : ∃ (op : GateOp) (j : Fin 26) (C : Circuit) (ws : List ℕ) (b : Bool),
      (op = GateOp.and ∨ op = GateOp.or) ∧ j ∈ ([1,13,15] : List (Fin 26)) ∧
      Monotone2 C ∧ 2 ≤ ws.length ∧ C.size+ws.length ≤ 63 ∧ ws.Nodup ∧
      (∀ i ∈ ws, i < 27+C.size) ∧
      let read := fun (x : Fin 26 → Bool) (i : ℕ) =>
        (C.wires (List.ofFn x ++ [op.eval [x 0,x j]])).getD i false
      (∀ i ∈ ws, ∃ x : Fin 26 → Bool, ∀ k ∈ ws, read x k = (decide (i=k) != b)) ∧
      ∀ x : Fin 26 → Bool, (if b then ws.all (read x) else ws.any (read x)) =
        decide (∃ p l : Fin 13, (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  obtain ⟨op,j,C,ws,b,allowed,pair,mono,two,cost,_unique,valid,_private,table⟩ := frontier
  have nonempty : ws ≠ [] := by rintro rfl; simp at two
  obtain ⟨D,legal,sz,joined⟩ := assemble 27 C ws b mono nonempty valid
  have budget : D.size ≤ 62 := by omega
  have endpoints : ((0 : Fin 26),j) ∈ [((0 : Fin 26),1),(0,13),(0,15)] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pair ⊢
    rcases pair with rfl|rfl|rfl <;> simp
  refine ⟨op,0,j,D,allowed,endpoints,legal,budget,?_⟩
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let row := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => (Finset.univ : Finset (Fin 13)).filter fun l => ∀ p ∈ s, ¬ near p l
  let answer := fun (s t : Finset (Fin 13)) => D.eval
    (List.ofFn (row s t) ++ [op.eval [row s t 0,row s t j]])
  change (∀ p l, near p l → answer {p} {l} = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → answer s (off s) = false ∧ answer (off s) s = false
  have bits (s t : Finset (Fin 13)) (p l : Fin 13) :
      (row s t (Fin.castAdd 13 p) = true ↔ p∈s) ∧
      (row s t (Fin.natAdd 13 l) = true ↔ l∈t) := by
    have ep : Fin.ofNat 13 (Fin.castAdd 13 p).val = p := by fin_cases p <;> rfl
    have el : Fin.ofNat 13 (Fin.natAdd 13 l).val = l := by fin_cases l <;> rfl
    have hlow : (Fin.castAdd 13 p).val < 13 := p.isLt
    have hhigh : ¬ (Fin.natAdd 13 l).val < 13 := by change ¬ 13+l.val < 13; omega
    simp only [row,hlow,hhigh,↓reduceIte,ep,el,decide_eq_true_eq,and_self]
  have spec (s t : Finset (Fin 13)) :
      answer s t = true ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
    have eval := joined (List.ofFn (row s t) ++ [op.eval [row s t 0,row s t j]]) (by simp)
    change answer s t = _ at eval
    rw [eval,table (row s t),decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,inc,hp,hl⟩
      exact ⟨p,(bits s t p l).1.mp hp,l,(bits s t p l).2.mp hl,inc⟩
    · rintro ⟨p,hp,l,hl,inc⟩
      exact ⟨p,l,inc,(bits s t p l).1.mpr hp,(bits s t p l).2.mpr hl⟩
  constructor
  · intro p l h
    exact (spec _ _).mpr ⟨p,by simp,l,by simp,h⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,hp,l,hl,inc⟩ := (spec _ _).mp h
      exact (Finset.mem_filter.mp hl).2 p hp inc
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,hp,l,hl,inc⟩ := (spec _ _).mp h
      have sym : near l p := by simpa only [near,Nat.add_comm] using inc
      exact (Finset.mem_filter.mp hp).2 l hl sym
