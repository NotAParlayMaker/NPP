import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Relabel the original inputs by an automorphism, preserving every suffix wire.
-- A pair of distinct vertices has two representatives, adjacent and nonadjacent.
-- Index ten on the first gate denotes any out-of-range read.
-- The wire replay argument follows R_meta_2736_91.
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.R_meta_2373_42
    (degenerate : ∀ (g : Gate) (C : Circuit) (a b : Nat),
      g.inputs ∈ ([[],[0],[10],[0,0],[0,10],[10,0],[10,10]] : List (List Nat)) → FanInTwo ⟨[g],0⟩ → FanInTwo C → C.size ≤ 17 →
      let w := fun (x : Fin 10 → Bool) (i : Nat) =>
        (C.wires ((Circuit.mk [g] 0).wires (List.ofFn x))).getD i false
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      ∃ x, (w x a || w x b) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (distinct : ∀ (g : Gate) (C : Circuit) (a b : Nat),
      g.inputs ∈ ([[0,1],[0,2]] : List (List Nat)) → FanInTwo ⟨[g],0⟩ → FanInTwo C → C.size ≤ 17 →
      let w := fun (x : Fin 10 → Bool) (i : Nat) =>
        (C.wires ((Circuit.mk [g] 0).wires (List.ofFn x))).getD i false
      (∃ x, w x a = true ∧ w x b = false) → (∃ x, w x a = false ∧ w x b = true) →
      ∃ x, (w x a || w x b) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro g C a b hg hc budget
  let F := fun x : Fin 10 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let W := fun (x : Fin 10 → Bool) i => (C.wires ((Circuit.mk [g] 0).wires (List.ofFn x))).getD i false
  change (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
    (∀ x, F x = false → W x a = false ∧ W x b = false) →
    ∃ x, F x = true ∧ W x a = false ∧ W x b = false
  intro ha hb off
  by_contra miss
  have correct (x) : (W x a || W x b) = F x := by
    cases h : F x with
    | false => obtain ⟨u,v⟩ := off x h; simp [u,v]
    | true =>
      cases u : W x a <;> cases v : W x b
      · exact (miss ⟨x,h,u,v⟩).elim
      all_goals rfl
  let clip (n : Nat) : Fin 11 := if h : n < 10 then ⟨n,by omega⟩ else 10
  let reps : Fin 11 → Fin 11 → Fin 60 := ![![0,0,0,1,1,2,3,4,2,5,0],![6,6,7,7,6,8,9,10,11,9,6],![12,12,12,13,14,15,16,15,13,17,12],![18,19,19,20,18,20,21,22,20,23,20],![24,25,26,26,24,24,27,28,29,27,24],![30,30,31,32,33,30,34,31,32,35,30],![36,37,37,38,39,40,38,41,38,39,38],![42,43,44,44,45,42,46,45,47,45,45],![48,49,50,50,51,48,49,52,50,53,50],![54,55,56,57,54,58,59,56,59,54,54],![0,6,12,20,24,30,38,45,50,54,0]]
  let perms : Fin 60 → Fin 10 → Fin 10 := ![![0,1,2,3,4,5,6,7,8,9],![0,4,3,2,1,5,9,8,7,6],![0,5,8,3,4,1,7,6,2,9],![0,1,6,8,5,4,2,9,3,7],![0,4,3,8,5,1,9,2,6,7],![0,4,9,6,1,5,3,7,8,2],![1,0,4,3,2,6,5,9,8,7],![4,0,1,2,3,9,5,6,7,8],![1,0,4,9,6,2,5,3,7,8],![4,0,5,8,3,9,1,7,6,2],![4,0,1,6,9,3,5,2,8,7],![5,0,4,3,8,7,1,9,2,6],![2,1,0,4,3,7,6,5,9,8],![8,5,0,1,6,3,7,4,2,9],![3,4,0,1,2,8,9,5,6,7],![3,4,0,5,8,2,9,1,7,6],![6,1,0,4,9,8,2,5,3,7],![8,5,0,4,3,6,7,1,9,2],![2,3,4,0,1,7,8,9,5,6],![3,2,1,0,4,8,7,6,5,9],![3,8,5,0,4,2,6,7,1,9],![8,3,4,0,5,6,2,9,1,7],![8,6,1,0,5,3,9,2,4,7],![6,8,5,0,1,9,3,7,4,2],![1,6,8,5,0,2,9,3,7,4],![1,2,3,4,0,6,7,8,9,5],![4,3,2,1,0,9,8,7,6,5],![4,3,8,5,0,9,2,6,7,1],![5,8,3,4,0,7,6,2,9,1],![4,9,6,1,0,3,7,8,2,5],![1,2,3,8,6,0,7,4,5,9],![4,3,2,7,9,0,8,1,5,6],![5,8,3,2,7,0,6,4,1,9],![1,6,8,3,2,0,9,5,4,7],![4,3,8,6,9,0,2,5,1,7],![4,9,6,8,3,0,7,1,5,2],![2,1,6,8,3,7,0,9,5,4],![6,1,2,3,8,9,0,7,4,5],![9,4,3,2,7,6,0,8,1,5],![3,4,9,7,2,8,0,6,5,1],![3,4,9,6,8,2,0,7,1,5],![9,4,3,8,6,7,0,2,5,1],![2,3,4,9,7,1,8,0,6,5],![3,2,1,6,8,4,7,0,9,5],![8,6,1,2,3,5,9,0,7,4],![3,8,5,7,2,4,6,0,9,1],![8,3,4,9,6,5,2,0,7,1],![6,9,4,3,8,1,7,0,2,5],![2,3,8,5,7,1,4,6,0,9],![3,2,7,5,8,4,1,9,0,6],![8,3,2,1,6,5,4,7,0,9],![3,8,6,1,2,4,5,9,0,7],![6,8,3,4,9,1,5,2,0,7],![8,6,9,4,3,5,1,7,0,2],![2,3,8,6,1,7,4,5,9,0],![3,2,7,9,4,8,1,5,6,0],![8,3,2,7,5,6,4,1,9,0],![6,8,3,2,1,9,5,4,7,0],![3,8,6,9,4,2,5,1,7,0],![9,6,8,3,4,7,1,5,2,0]]
  let adj (i j : Fin 10) := ([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0 |>.testBit j.val
  have invariant : ∀ k i j, adj (perms k i) (perms k j) = adj i j := by decide
  have onto : ∀ k, Function.Surjective (perms k) := by unfold Function.Surjective; decide
  let es : List (Fin 10 × Fin 10) :=
    [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  have flags : ∀ i j, adj i j = true ↔ (i,j) ∈ es ∨ (j,i) ∈ es := by decide
  have edge (x) : F x = true ↔ ∃ i j, adj i j = true ∧ x i = true ∧ x j = true := by
    have e : F x = es.any (fun ij => x ij.1 && x ij.2) := by
      simp only [F,es,List.any_cons,List.any_nil,Bool.or_false]
      ac_rfl
    rw [e,List.any_eq_true]
    constructor
    · rintro ⟨⟨i,j⟩,hm,h⟩
      exact ⟨i,j,(flags i j).2 (.inl hm),Bool.and_eq_true_iff.mp h⟩
    · rintro ⟨i,j,h,hi,hj⟩
      rcases (flags i j).1 h with h|h
      · exact ⟨(i,j),h,Bool.and_eq_true_iff.mpr ⟨hi,hj⟩⟩
      · exact ⟨(j,i),h,Bool.and_eq_true_iff.mpr ⟨hj,hi⟩⟩
  have symmF (k) (x) : F (x ∘ perms k) = F x := by
    apply Bool.eq_iff_iff.mpr
    rw [edge,edge]
    constructor
    · rintro ⟨i,j,h,hi,hj⟩
      exact ⟨_,_,(invariant k i j).trans h,hi,hj⟩
    · rintro ⟨i,j,h,hi,hj⟩
      obtain ⟨u,rfl⟩ := onto k i
      obtain ⟨v,rfl⟩ := onto k j
      exact ⟨u,v,(invariant k u v).symm.trans h,hi,hj⟩
  let lift (k : Fin 60) (v : Fin 11) : Nat :=
    if h : v.val < 10 then (perms k ⟨v.val,h⟩).val else 10
  have pairTable : ∀ u v, let k := reps u v; [lift k u,lift k v] ∈
      ([[],[0],[10],[0,0],[0,10],[10,0],[10,10]] : List (List Nat)) ∨ [lift k u,lift k v] ∈ ([[0,1],[0,2]] : List (List Nat)) := by decide
  have oneTable : ∀ u, [lift (reps u 10) u] ∈ ([[],[0],[10],[0,0],[0,10],[10,0],[10,10]] : List (List Nat)) := by decide
  let k := reps (clip (g.inputs.getD 0 10)) (clip (g.inputs.getD 1 10))
  let p := perms k
  let σ := fun i : Nat => if h : i < 10 then (p ⟨i,h⟩).val else i
  let ρ := fun i : Nat => lift k (clip i)
  let hgate : Gate := ⟨g.op,g.inputs.map ρ⟩
  have canon : hgate.inputs ∈ ([[],[0],[10],[0,0],[0,10],[10,0],[10,10]] : List (List Nat)) ∨ hgate.inputs ∈ [[0,1],[0,2]] := by
    have len := (hg g (by simp)).2
    change g.inputs.map ρ ∈ _ ∨ _
    cases h : g.inputs with
    | nil => simp
    | cons u tail =>
      cases ht : tail with
      | nil =>
        left
        have ten : clip 10 = 10 := rfl
        simpa only [hgate,ρ,k,h,ht,List.map_cons,List.map_nil,List.getD_cons_zero,
          List.getD_cons_succ,List.getD_nil,ten] using oneTable (clip u)
      | cons v rest =>
        have hnil : rest = [] := by simpa [h,ht] using len
        subst rest
        simpa only [hgate,ρ,k,h,ht,List.map_cons,List.map_nil,List.getD_cons_zero,
          List.getD_cons_succ] using pairTable (clip u) (clip v)
  let mapGate (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let rewired (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate σ),σ C.output⟩

  have fan {C : Circuit} (σ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (rewired σ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h a ha).1,by simpa [mapGate] using (h a ha).2⟩

  have run {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (gs : List Gate) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires y).getD (σ i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map (fun i => x.getD i false))
      have same : (mapGate σ g).op.eval ((mapGate σ g).inputs.map (fun i => y.getD i false)) = b := by
        simp only [b,mapGate,List.map_map,Function.comp_def,agree]
      change ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires (y++[_])).getD (σ i) false =
        ((Circuit.mk gs 0).wires (x++[b])).getD i false
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i<x.length
      · have hsi : σ i<y.length := by
          by_cases hr : i<cut
          · have := raw i hr; omega
          · rw [later i (by omega)]; omega
        rw [List.getD_append _ _ _ _ hsi, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [later i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]


  let B := rewired σ C
  let V := fun (x : Fin 10 → Bool) i => (B.wires ((Circuit.mk [hgate] 0).wires (List.ofFn x))).getD i false
  have smallσ (i : Nat) (h : i < 10) : σ i < 10 := by simp [σ,h]
  have largeσ (i : Nat) (h : 10 ≤ i) : σ i = i := by simp [σ,Nat.not_lt.mpr h]
  have rawEq (x : Fin 10 → Bool) (i : Nat) :
      (List.ofFn x).getD (σ i) false = (List.ofFn (x ∘ p)).getD i false := by
    by_cases h : i < 10
    · rw [List.getD_eq_getElem _ _ (by simpa using smallσ i h),
          List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_ofFn,Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left h
    · rw [largeσ i (by omega),List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have clipped (x : Fin 10 → Bool) (i : Nat) :
      (List.ofFn x).getD (ρ i) false = (List.ofFn (x ∘ p)).getD i false := by
    by_cases h : i < 10
    · simpa [ρ,lift,clip,σ,h,p] using rawEq x i
    · have hi : ¬ (10 : Fin 11).val < 10 := by decide
      simp only [ρ,clip,h,dite_false,lift,hi]
      rw [List.getD_eq_default _ _ (by simp),List.getD_eq_default _ _ (by simp; omega)]
  have replay (x : Fin 10 → Bool) (i : Nat) : V x (σ i) = W (x ∘ p) i := by
    apply run σ smallσ largeσ C.gates _ _ (by change (List.ofFn (x ∘ p) ++ [_]).length = (List.ofFn x ++ [_]).length; simp) (by change 10 ≤ (List.ofFn (x ∘ p) ++ [_]).length; simp)
    let v := g.op.eval (g.inputs.map fun n => (List.ofFn (x ∘ p)).getD n false)
    have val : hgate.op.eval (hgate.inputs.map fun n => (List.ofFn x).getD n false) = v := by
      simp only [hgate,v,List.map_map,Function.comp_def,clipped]
    intro t
    change (List.ofFn x ++ [_]).getD (σ t) false = (List.ofFn (x ∘ p) ++ [v]).getD t false
    rw [val]
    by_cases h : t < 10
    · rw [List.getD_append _ _ _ _ (by simpa using smallσ t h),
          List.getD_append _ _ _ _ (by simpa using h)]
      exact rawEq x t
    · rw [largeσ t (by omega),List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  have inv (x : Fin 10 → Bool) : ∃ y, y ∘ p = x := by
    have inj : Function.Injective p := (Finite.injective_iff_surjective).2 (onto k)
    let e := Equiv.ofBijective p ⟨inj,onto k⟩
    exact ⟨x ∘ e.symm,funext fun i => congrArg x (e.symm_apply_apply i)⟩
  have ah : ∃ y, V y (σ a) = true ∧ V y (σ b) = false := by
    obtain ⟨x,ua,ub⟩ := ha
    obtain ⟨y,hy⟩ := inv x
    exact ⟨y,by rw [replay,hy,ua],by rw [replay,hy,ub]⟩
  have bh : ∃ y, V y (σ a) = false ∧ V y (σ b) = true := by
    obtain ⟨x,ua,ub⟩ := hb
    obtain ⟨y,hy⟩ := inv x
    exact ⟨y,by rw [replay,hy,ua],by rw [replay,hy,ub]⟩
  have gateOk : FanInTwo ⟨[hgate],0⟩ := by
    intro z hz
    obtain rfl : z = hgate := by simpa using hz
    have h := hg g (by simp)
    exact ⟨h.1,by simpa [hgate] using h.2⟩
  have cost : B.size ≤ 17 := by change (C.gates.map (mapGate σ)).length ≤ 17; rw [List.length_map]; exact budget
  have bad : ∃ x, (V x (σ a) || V x (σ b)) ≠ F x := by
    rcases canon with h|h
    · exact degenerate hgate B _ _ h gateOk (fan σ hc) cost ah bh
    · exact distinct hgate B _ _ h gateOk (fan σ hc) cost ah bh
  obtain ⟨x,hx⟩ := bad
  rw [replay,replay,correct,symmF] at hx
  exact hx rfl


