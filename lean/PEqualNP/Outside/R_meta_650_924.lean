import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two outputs share their gates. One rejects generic maximal negatives.
-- The other rejects the exceptional maximal negatives.
-- Uses the input representation of R_meta_650_713.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 32768 in
theorem PEqualNP.Outside.R_meta_650_924
    (search : ∃ (D : Circuit) (a b : ℕ), Monotone2 D ∧ D.size ≤ 62 ∧
      a < 26 + D.size ∧ b < 26 + D.size ∧
      (let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ s) else decide ((Fin.ofNat 13 i.val) ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let exceptional := fun (s t : Finset (Fin 13)) =>
    (∃ l : Fin 13, ∀ p ∈ s, near p l) ∨ (∃ p : Fin 13, ∀ l ∈ t, near p l)
       let view := fun j s t => (D.wires (List.ofFn (vec s t))).getD j false
       (∀ p l, near p l → view a {p} {l} = true ∧ view b {p} {l} = true) ∧
       (∀ s, s = off (off s) → view (if exceptional s (off s) then b else a) s (off s) = false)))
    (join : ∀ (D : Circuit) (a b : ℕ), Monotone2 D →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 1 ∧ ∀ x : Fin 26 → Bool,
        C.eval (List.ofFn x) = (((D.wires (List.ofFn x)).getD a false) &&
          ((D.wires (List.ofFn x)).getD b false))) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨D,a,b,hD,dSize,_,_,tests⟩ := search
  obtain ⟨C,hm,size,eval⟩ := join D a b hD
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ s) else decide ((Fin.ofNat 13 i.val) ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let exceptional := fun (s t : Finset (Fin 13)) =>
    (∃ l : Fin 13, ∀ p ∈ s, near p l) ∨ (∃ p : Fin 13, ∀ l ∈ t, near p l)
  let view := fun j s t => (D.wires (List.ofFn (vec s t))).getD j false
  let read := fun s t => C.eval (List.ofFn (vec s t))
  change (∀ p l, near p l → view a {p} {l} = true ∧ view b {p} {l} = true) ∧
       (∀ s, s = off (off s) → view (if exceptional s (off s) then b else a) s (off s) = false) at tests
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le := fun (w z : List Bool) => ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
      (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g) (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).all id = true → (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact le i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).any id = true → (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,le i ha⟩
      intro i
      by_cases small : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)] using le i
      · have big : w.length ≤ i := by omega
        simp only [step,List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : i-w.length with
        | zero => exact gate
        | succ j => simp
  have mono {s t u v : Finset (Fin 13)} (a : s ⊆ u) (b : t ⊆ v) :
      read s t = true → read u v = true := by
    have init : Le (List.ofFn (vec s t)) (List.ofFn (vec u v)) := by
      intro j
      by_cases hj : j < 26
      · rw [List.getD_eq_getElem (List.ofFn (vec s t)) false (by simpa only [List.length_ofFn] using hj),
            List.getD_eq_getElem (List.ofFn (vec u v)) false (by simpa only [List.length_ofFn] using hj)]
        simp only [List.getElem_ofFn]
        by_cases hp : j < 13
        · simpa [vec,hp] using a (x := Fin.ofNat 13 j)
        · simpa [vec,hp] using b (x := Fin.ofNat 13 j)
      · rw [List.getD_eq_default (List.ofFn (vec s t)) false (by simp only [List.length_ofFn]; omega)]
        intro h
        exact Bool.noConfusion h
    exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp) init C.output
  let pt (p : Fin 13) : Fin 26 := ⟨p.val,by omega⟩
  let ln (l : Fin 13) : Fin 26 := ⟨13+l.val,by omega⟩
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ u v : Fin 26, (u.val,v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ near (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val) := by
    dsimp only [edges,near]
    decide +kernel
  have points : ∀ p : Fin 13, (Fin.ofNat 13 (pt p).val) = p := by
    intro p
    apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  have lines : ∀ l : Fin 13, (Fin.ofNat 13 (ln l).val) = l := by
    intro l
    apply Fin.ext
    change (13+l.val) % 13 = l.val
    omega
  have pointInv : ∀ i : Fin 26, i.val < 13 → pt (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  have lineInv : ∀ i : Fin 26, 13 ≤ i.val → ln (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    change 13+i.val % 13 = i.val
    omega
  refine ⟨C,hm,by omega,?_⟩
  intro x
  let s := Finset.univ.filter fun p : Fin 13 => x (pt p) = true
  let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
  have repr : vec s t = x := by
    funext i
    by_cases hi : i.val < 13
    · simp only [vec,ite_eq_left hi,s,Finset.mem_filter,Finset.mem_univ,true_and,pointInv i hi]
      simp
    · simp only [vec,ite_eq_right hi,t,Finset.mem_filter,Finset.mem_univ,true_and,lineInv i (by omega)]
      simp
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true
  have arr : (∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true) ↔
      ∃ p ∈ s, ∃ l ∈ t, near p l := by
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      obtain ⟨ha,hb,hc⟩ := (table u v).mp he
      exact ⟨Fin.ofNat 13 u.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [pointInv u ha]; exact hu⟩,Fin.ofNat 13 v.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [lineInv v hb]; exact hv⟩,hc⟩
    · rintro ⟨p,hp,l,hl,hpl⟩
      refine ⟨pt p,ln l,(table _ _).mpr ⟨by dsimp [pt]; omega,by dsimp [ln]; omega,?_⟩,?_,?_⟩
      · simpa only [points,lines] using hpl
      · simpa [s] using hp
      · simpa [t] using hl
  rw [arr,← repr]
  change read s t = true ↔ _
  constructor
  · intro accepted
    by_contra no
    have leOff : t ⊆ off s := by
      intro l hl
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun p hp e => no ⟨p,hp,l,hl,e⟩⟩
    have antitone {u v : Finset (Fin 13)} (sub : u ⊆ v) : off v ⊆ off u := by
      intro j hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun i hi => (Finset.mem_filter.mp hj).2 i (sub hi)⟩
    have extensive (u : Finset (Fin 13)) : u ⊆ off (off u) := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j hj
      simpa only [near, Nat.add_comm] using (Finset.mem_filter.mp hj).2 i hi
    let s' := off (off s)
    have same : off s' = off s :=
      Finset.Subset.antisymm (antitone (extensive s)) (extensive (off s))
    have closed : s' = off (off s') := by
      rw [same]
    have rejects := tests.2 s' closed
    have bad : read s' (off s') = true := mono (extensive s) (same.symm ▸ leOff) accepted
    have combination : read s' (off s') = (view a s' (off s') && view b s' (off s')) :=
      eval _
    rw [combination, Bool.and_eq_true] at bad
    by_cases h : exceptional s' (off s')
    · rw [ite_eq_left h] at rejects
      rw [rejects] at bad
      exact Bool.noConfusion bad.2
    · rw [ite_eq_right h] at rejects
      rw [rejects] at bad
      exact Bool.noConfusion bad.1
  · rintro ⟨p,hp,l,hl,hpl⟩
    obtain ⟨aTrue,bTrue⟩ := tests.1 p l hpl
    apply mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)
    change C.eval (List.ofFn (vec {p} {l})) = true
    rw [eval]
    change (view a {p} {l} && view b {p} {l}) = true
    simp [aTrue,bTrue]
