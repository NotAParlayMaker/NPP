import PEqualNP.Defs

-- Project the full plane after taking each labeled image. The same negative row
-- covers the main output and, with the four pencil bits cleared, the auxiliary wire.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2215_73
    (cover :
      let basis : List ℕ := [67100672,62816257,27131907,11436037,9306119,1441803,2523149,18481171,2785301,3309593,2261021,34897961,17432659,42205345]
      let row := fun (z m : ℕ) (t : Fin 13) (d : Bool) (i : Fin 25) =>
        let p := decide (i.val < 12)
        (if p == d then z / 8192 else z % 8192).testBit ((m*(i.val+1)+(if p then t.val else 13-t.val))%13)
      ∀ P : Fin 12 → Bool, ∃ z ∈ basis, ∃ m ∈ ([1,3,9] : List ℕ), ∃ (t : Fin 13) (d : Bool), ∀ i : Fin 25,
        (if hi : i.val < 12 then P ⟨i.val,hi⟩ = true else ∀ j : Fin 12, P j = true → (j.val+i.val+2)%13 ∉ ([0,1,3,9] : List ℕ)) → row z m t d i = true)
    (search :
      let basis : List ℕ := [67100672,62816257,27131907,11436037,9306119,1441803,2523149,18481171,2785301,3309593,2261021,34897961,17432659,42205345]
      let row := fun (z m : ℕ) (t : Fin 13) (d : Bool) (i : Fin 25) =>
        let p := decide (i.val < 12)
        (if p == d then z / 8192 else z % 8192).testBit ((m*(i.val+1)+(if p then t.val else 13-t.val))%13)
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (q : ℕ), PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 61 ∧ C.output < 25+C.size ∧ q < 25+C.size ∧
        let read := fun (j : ℕ) (x : Fin 25 → Bool) => (C.wires (List.ofFn x)).getD j false
        let S : List ℕ := [12,13,15,21]
        (∀ i j : Fin 25, i.val < 12 → 12 ≤ j.val → (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ) → read C.output (fun k => decide (k=i ∨ k=j)) = true) ∧
        (∀ i : Fin 25, i.val ∈ S → read q (fun k => decide (k=i)) = true) ∧
        ∀ z ∈ basis, ∀ m ∈ ([1,3,9] : List ℕ), ∀ (t : Fin 13) (d : Bool),
          read C.output (row z m t d) = false ∧ read q (fun i => row z m t d i && decide (i.val ∉ S)) = false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let basis : List ℕ := [67100672,62816257,27131907,11436037,9306119,1441803,2523149,18481171,2785301,3309593,2261021,34897961,17432659,42205345]
  let row := fun (z m : ℕ) (t : Fin 13) (d : Bool) (i : Fin 25) =>
    let p := decide (i.val < 12)
    (if p == d then z / 8192 else z % 8192).testBit ((m*(i.val+1)+(if p then t.val else 13-t.val))%13)
  obtain ⟨C,q,hm,hs,ho,hq,pos,flag,neg⟩ := search
  let S : List ℕ := [12,13,15,21]
  let read := fun (w : ℕ) (x : Fin 25 → Bool) => (C.wires (List.ofFn x)).getD w false
  let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le := fun (w z : List Bool) => ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have fold (gs : List PEqualNP.CircuitLowerBounds.Gate) (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (w z : List Bool) (len : w.length = z.length) (le : Le w z) : Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun r hr => ok _ (by simp [hr])) _ _ (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true → g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with op|op
        · rw [op]
          change (g.inputs.map fun i => w.getD i false).all id = true → (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          exact fun h i hi => le i (h i hi)
        · rw [op]
          change (g.inputs.map fun i => w.getD i false).any id = true → (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨i,hi,h⟩; exact ⟨i,hi,le i h⟩
      intro i
      by_cases hi : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi)] using le i
      by_cases he : i = w.length
      · subst i; simpa [step,←len] using gate
      · rw [List.getD_eq_default _ _ (by simp [step]; omega)]; simp
  have mono {x y : Fin 25 → Bool} (h : ∀ i, x i = true → y i = true) (w : ℕ) : read w x = true → read w y = true := by
    apply fold C.gates (fun g hg => (hm g hg).1) _ _ (by simp) _ w
    intro i hi
    by_cases hl : i < 25
    · rw [List.getD_eq_getElem _ _ (by simpa using hl),List.getElem_ofFn] at hi ⊢
      exact h _ hi
    · have hi' : (List.ofFn x).length ≤ i := by simpa only [List.length_ofFn] using Nat.le_of_not_gt hl
      exact Bool.false_ne_true ((List.getD_eq_default (List.ofFn x) false hi').symm.trans hi) |>.elim
  have bad {x : Fin 25 → Bool} (hn : ¬∃ i j : Fin 25, (i.val < 12 ∧ 12 ≤ j.val ∧ (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ)) ∧ x i = true ∧ x j = true) :
      ∃ z ∈ basis, ∃ m ∈ ([1,3,9] : List ℕ), ∃ (t : Fin 13) (d : Bool), ∀ i, x i = true → row z m t d i = true := by
    let pt (j : Fin 12) : Fin 25 := ⟨j.val,by omega⟩
    obtain ⟨z,hz,m,hM,t,d,hcov⟩ := cover (fun j => x (pt j))
    refine ⟨z,hz,m,hM,t,d,?_⟩
    intro i hi
    apply hcov i
    split_ifs with hlo
    · exact hi
    · intro j hj hinc
      exact hn ⟨pt j,i,⟨j.isLt,by omega,hinc⟩,hj,hi⟩
  have main (x : Fin 25 → Bool) : read C.output x = true ↔ ∃ i j : Fin 25, (i.val < 12 ∧ 12 ≤ j.val ∧ (i.val+j.val+2)%13 ∈ ([0,1,3,9] : List ℕ)) ∧ x i = true ∧ x j = true := by
    constructor
    · intro hx
      by_contra hn
      obtain ⟨z,hz,m,hM,t,d,hcov⟩ := bad hn
      have he := mono hcov C.output hx
      exact Bool.false_ne_true ((neg z hz m hM t d).1.symm.trans he)
    · rintro ⟨i,j,⟨hi,hj,he⟩,hp,hl⟩
      apply mono (x := fun k => decide (k=i ∨ k=j)) _ _ (pos i j hi hj he)
      intro k hk; rcases of_decide_eq_true hk with rfl|rfl <;> assumption
  refine ⟨C,q,hm,hs,ho,hq,?_⟩
  intro x
  refine ⟨main x,?_⟩
  intro hx
  change read q x = (x 12 || x 13 || x 15 || x 21)
  have pencil : (x 12 || x 13 || x 15 || x 21) = true ↔ ∃ i : Fin 25, i.val ∈ S ∧ x i = true := by
    simp only [Bool.or_eq_true]
    constructor
    · rintro (((h|h)|h)|h)
      · exact ⟨12,by decide,h⟩
      · exact ⟨13,by decide,h⟩
      · exact ⟨15,by decide,h⟩
      · exact ⟨21,by decide,h⟩
    · rintro ⟨i,hi,hx⟩
      simp only [S,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with h|h|h|h
      · exact Or.inl (Or.inl (Or.inl (Fin.ext (b := 12) h ▸ hx)))
      · exact Or.inl (Or.inl (Or.inr (Fin.ext (b := 13) h ▸ hx)))
      · exact Or.inl (Or.inr (Fin.ext (b := 15) h ▸ hx))
      · exact Or.inr (Fin.ext (b := 21) h ▸ hx)
  apply Bool.eq_iff_iff.mpr
  rw [pencil]
  constructor
  · intro yes
    by_contra hn
    change read C.output x = false at hx
    have absent := fun h => Bool.false_ne_true (hx.symm.trans ((main x).2 h))
    obtain ⟨z,hz,m,hM,t,d,hcov⟩ := bad absent
    have sub (i : Fin 25) (hi : x i = true) : (row z m t d i && decide (i.val ∉ S)) = true := by
      simp only [hcov i hi,Bool.true_and,decide_eq_true_eq]
      exact fun h => hn ⟨i,h,hi⟩
    have inc := mono sub q yes
    exact Bool.false_ne_true ((neg z hz m hM t d).2.symm.trans inc)
  · rintro ⟨i,hS,hx⟩
    apply mono (x := fun k => decide (k=i)) _ _ (flag i hS)
    intro k hk; obtain rfl : k=i := of_decide_eq_true hk; exact hx
