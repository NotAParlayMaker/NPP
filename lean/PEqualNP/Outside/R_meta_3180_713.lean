import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3180_713
    (simulate : ∀ (α : Type) (C : Circuit) (_hc : FanInTwo C) (s v : List (α → Bool)),
      (∀ b : Bool, (fun _ : α => b) ∈ s) →
      (∀ u ∈ v, u ∈ s ∧ (fun x => !(u x)) ∈ s) →
      ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ C.size ∧ ∀ x : α,
        (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
          w ++ [z,!z]) (s.map fun u => u x)).getD o false = C.eval (v.map fun u => u x))
    (cut : ∀ (j : Fin 9) (f : (Fin 9 → Bool) → Bool) (m : ℕ),
      let raw := fun x : Fin 9 → Bool => [false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not
      let can := fun (s : (Fin 9 → Bool) → List Bool) (n : ℕ) (h : (Fin 9 → Bool) → Bool) =>
        ∃ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ n ∧ ∀ x : Fin 9 → Bool,
          (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
            w ++ [z,!z]) (s x)).getD o false = h x
      (∃ x : Fin 9 → Bool, j ≠ 0 ∧ x j = true ∧ f (Function.update x 0 false) ≠ f (Function.update x 0 true)) →
      can (fun x => raw x ++ [x 0 && !(x j),!(x 0 && !(x j))]) m f →
      can raw m f ∨ can raw (m-2) (fun x => f (Function.update x 0 false)))
    (rawLower : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 13 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (deletedLower : ∀ (p : List (ℕ × ℕ)) (o : ℕ), p.length ≤ 11 → ∃ x : Fin 9 → Bool,
      (p.foldl (fun w ij => let z := w.getD ij.1 false && w.getD ij.2 false
        w ++ [z,!z]) ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not)).getD o false ≠
      ([(1,2),(2,3),(3,4),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (9 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  let graph := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  intro l len bound _ witnesses C hc size
  have selector (l : List ℕ) (len : l.length = 2) (range : ∀ k ∈ l, k < 10)
      (nontrivial : ¬∀ k ∈ l, k = 0 ∨ k = 9) (holds : 9 ∈ l) :
      ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      GateOp.or.eval (l.map fun k => (List.ofFn x ++ [!x 0]).getD k false) = (!x 0 || x j) := by
    obtain ⟨a,b,rfl⟩ : ∃ a b, l = [a,b] := by
      cases l with
      | nil => simp at len
      | cons a tail =>
        cases tail with
        | nil => simp at len
        | cons b rest =>
          have h : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
          exact ⟨a,b,by rw [h]⟩
    have read (x : Fin 9 → Bool) (j : Fin 9) : (List.ofFn x ++ [!x 0]).getD j.val false = x j := by
      rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; exact j.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa using j.isLt),List.getElem_ofFn]
    have neg (x : Fin 9 → Bool) : (List.ofFn x ++ [!x 0]).getD 9 false = !x 0 := rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at holds
    rcases holds with h | h
    · subst a
      have small : b < 10 := range b (by simp)
      have other : b ≠ 0 ∧ b ≠ 9 := by
        constructor <;> intro e <;> subst b <;> apply nontrivial <;> simp
      let j : Fin 9 := ⟨b,by omega⟩
      refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
      intro x
      have rb : (List.ofFn x ++ [!x 0]).getD b false = x j := read x j
      change ([(List.ofFn x ++ [!x 0]).getD 9 false,(List.ofFn x ++ [!x 0]).getD b false] : List Bool).any id = _
      rw [neg,rb]
      simp
    · subst b
      have small : a < 10 := range a (by simp)
      have other : a ≠ 0 ∧ a ≠ 9 := by
        constructor <;> intro e <;> subst a <;> apply nontrivial <;> simp
      let j : Fin 9 := ⟨a,by omega⟩
      refine ⟨j,fun e => other.1 (congrArg Fin.val e),?_⟩
      intro x
      have ra : (List.ofFn x ++ [!x 0]).getD a false = x j := read x j
      change ([(List.ofFn x ++ [!x 0]).getD a false,(List.ofFn x ++ [!x 0]).getD 9 false] : List Bool).any id = _
      rw [neg,ra]
      simp [Bool.or_comm]

  obtain ⟨j,nz,signal⟩ := selector l len bound witnesses.1 witnesses.2
  by_contra! correct
  let raws := List.ofFn (fun k : Fin 9 => fun x : Fin 9 → Bool => x k)
  let base := [(fun _ : Fin 9 → Bool => false),(fun _ : Fin 9 → Bool => true)] ++ raws ++ raws.map (fun u x => !(u x))
  let seed := fun x : Fin 9 → Bool => x 0 && !(x j)
  let s := base ++ [seed,fun x => !(seed x)]
  let v := raws ++ [(fun x => !(x 0)),fun x => !(seed x)]
  have constants (b : Bool) : (fun _ : Fin 9 → Bool => b) ∈ s := by
    cases b <;> simp [s,base]
  have pos (i : Fin 9) : (fun x : Fin 9 → Bool => x i) ∈ s := by
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have neg (i : Fin 9) : (fun x : Fin 9 → Bool => !(x i)) ∈ s := by
    apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
  have pins : ∀ u ∈ v, u ∈ s ∧ (fun x => !(u x)) ∈ s := by
    intro u hu
    rcases List.mem_append.mp hu with hr | he
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      exact ⟨pos i,neg i⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl
      · simpa only [Bool.not_not] using And.intro (neg 0) (pos 0)
      · simp [s]
  have value (x : Fin 9 → Bool) : C.eval (v.map fun u => u x) = graph x := by
    have h := correct x
    dsimp only at h
    rw [signal] at h
    have eq := not_not.mp h
    simpa [v,raws,seed,graph,List.map_ofFn,Function.comp_def,Bool.or_assoc] using eq
  have pool (x : Fin 9 → Bool) : s.map (fun u => u x) =
      ([false,true] ++ List.ofFn x ++ (List.ofFn x).map Bool.not) ++ [x 0 && !(x j),!(x 0 && !(x j))] := by
    simp only [s,base,raws,seed,List.map_append,List.map_cons,List.map_nil,List.map_ofFn]
    rfl
  obtain ⟨p,o,lim,hit⟩ := simulate (Fin 9 → Bool) C hc s v constants pins
  let witness : Fin 9 → ℕ := ![0,2,20,10,16,32,80,130,258]
  have facts : ∀ k : Fin 9, k ≠ 0 → (witness k).testBit k.val = true ∧
      graph (Function.update (fun i : Fin 9 => (witness k).testBit i.val) 0 false) ≠
      graph (Function.update (fun i : Fin 9 => (witness k).testBit i.val) 0 true) := by decide
  have disj := cut j graph C.size
    ⟨fun i => (witness j).testBit i.val,nz,(facts j nz).1,(facts j nz).2⟩
    ⟨p,o,lim,fun x => by simpa only [pool] using (hit x).trans (value x)⟩
  rcases disj with ⟨q,k,cap,ok⟩ | ⟨q,k,cap,ok⟩
  · obtain ⟨x,bad⟩ := rawLower q k (by omega)
    exact bad (ok x)
  · obtain ⟨x,bad⟩ := deletedLower q k (by omega)
    apply bad
    apply (ok x).trans
    simp [graph,Function.update]
