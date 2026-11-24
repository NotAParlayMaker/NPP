import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The extremal rows detect both functional errors and whether any monotone wire
-- can turn on away from the target. The construction is for the shard with at least three junk ANDs.
theorem PEqualNP.Outside.R_meta_1342_406
    (samples :
      let yes : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let no : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let row (r : ℕ) (i : Fin 11) := r.testBit i.val
      let contains (x : Fin 11 → Bool) := ∃ r ∈ yes, ∀ i : Fin 11, row r i ≤ x i
      ∀ f : (Fin 11 → Bool) → Bool, Monotone f →
        ((∀ r ∈ no, f (row r) = false) ↔ (∀ x, f x = true → contains x)) ∧
        ((∀ r ∈ yes, f (row r) = true) ↔ (∀ x, contains x → f x = true)))
    (construction :
      let yes : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
      let no : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
      let row (r : ℕ) (i : Fin 11) := r.testBit i.val
      let edges : List ℕ := [9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97]
      let G := PEqualNP.EdgeOwnership.edgeGraph 11 (edges.map fun e => (e / 11, e % 11))
      ∃ C : Circuit, PEqualNP.TopForm.IsAO2 11 C ∧ PEqualNP.TopForm.TopForm G C ∧
        3 ≤ (PEqualNP.TopForm.junk G C).card ∧ C.size ≤ 21 ∧
        (∀ r ∈ yes, C.eval (List.ofFn (row r)) = true) ∧
        (∀ r ∈ no, C.eval (List.ofFn (row r)) = false)) :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∀ x : Fin 11 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧ C.size ≤ 21 := by
  let Step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have val_mono (g : Gate) (op : g.op = .and ∨ g.op = .or) (u v : List Bool)
      (mono : ∀ i, u.getD i false = true → v.getD i false = true)
      (hu : g.op.eval (g.inputs.map fun i => u.getD i false) = true) :
      g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
    rcases op with op | op
    · rw [op] at hu ⊢
      change (g.inputs.map fun i => u.getD i false).all id = true at hu
      change (g.inputs.map fun i => v.getD i false).all id = true
      apply List.all_eq_true.mpr
      intro bit fromInput
      obtain ⟨i,member,rfl⟩ := List.mem_map.mp fromInput
      exact mono i (List.all_eq_true.mp hu _ (List.mem_map.mpr ⟨i,member,rfl⟩))
    · rw [op] at hu ⊢
      change (g.inputs.map fun i => u.getD i false).any id = true at hu
      change (g.inputs.map fun i => v.getD i false).any id = true
      obtain ⟨bit,fromInput,active⟩ := List.any_eq_true.mp hu
      obtain ⟨i,member,rfl⟩ := List.mem_map.mp fromInput
      exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,member,rfl⟩,mono i active⟩

  have step_mono (g : Gate) (op : g.op = .and ∨ g.op = .or)
      (u v : List Bool) (len : u.length = v.length)
      (mono : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (Step u g).getD i false = true → (Step v g).getD i false = true := by
    unfold Step
    intro i hi
    by_cases early : i < u.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left early] at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < v.length by omega)]
      exact mono i hi
    · rw [List.getD_append_right _ _ _ _ (by omega), ← len]
      rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      by_cases last : i = u.length
      · simp [last] at hi ⊢
        exact val_mono g op u v mono hi
      · have oob : 1 ≤ i-u.length := by omega
        rw [List.getD_eq_default _ _ (by simpa using oob)] at hi
        simp at hi

  have all_mono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (u v : List Bool) (len : u.length = v.length)
      (mono : ∀ i, u.getD i false = true → v.getD i false = true) :
      ∀ i, (gs.foldl Step u).getD i false = true → (gs.foldl Step v).getD i false = true := by
    induction gs generalizing u v with
    | nil => exact mono
    | cons g rest ih =>
      exact ih (fun h used => ops h (List.mem_cons_of_mem _ used)) (Step u g) (Step v g)
        (by simp [Step,len]) (step_mono g (ops g (by simp)) u v len mono)

  have monotone_eval {n : ℕ} (C : Circuit) (hc : Monotone2 C) :
      Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
    intro a b le
    have ab (i : ℕ) : (List.ofFn a).getD i false = true → (List.ofFn b).getD i false = true := by
      by_cases small : i<n
      · have left : (List.ofFn a).getD i false = a ⟨i,small⟩ := by
          simp [List.getD_eq_getElem?_getD,small]
        have right : (List.ofFn b).getD i false = b ⟨i,small⟩ := by
          simp [List.getD_eq_getElem?_getD,small]
        rw [left,right]
        intro h
        have out := le ⟨i,small⟩
        cases hb : b ⟨i,small⟩
        · rw [h,hb] at out
          exact (show ¬(true ≤ false) by decide) out |>.elim
        · rfl
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp
    change (C.gates.foldl Step (List.ofFn a)).getD C.output false ≤
      (C.gates.foldl Step (List.ofFn b)).getD C.output false
    have mono := all_mono C.gates (fun g used => by simpa using (hc g used).1)
      (List.ofFn a) (List.ofFn b) (by simp) ab C.output
    cases p : (C.gates.foldl Step (List.ofFn a)).getD C.output false
    · simp
    · rw [mono p]


  let pairs : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

  let edgeMask (p : Fin 11 × Fin 11) : ℕ := 2 ^ p.1.val + 2 ^ p.2.val

  have mask_bit : ∀ p ∈ pairs, ∀ i : Fin 11,
      (edgeMask p).testBit i.val = (i == p.1 || i == p.2) := by
    unfold pairs
    decide +kernel

  have bit_le_eq (b : Bool) (h : true ≤ b) : b = true := by
    cases b
    · exact ((show ¬ (true ≤ false) by decide) h).elim
    · rfl

  have edge_characterization (x : Fin 11 → Bool) :
      (∃ r ∈ ([513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768] : List ℕ), ∀ i : Fin 11, r.testBit i.val ≤ x i) ↔
        ∃ u v : Fin 11, (u.val,v.val) ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true := by
    change (∃ r ∈ pairs.map edgeMask, ∀ i : Fin 11, r.testBit i.val ≤ x i) ↔
      (∃ u v : Fin 11, (u.val,v.val) ∈ pairs.map (fun p => (p.1.val,p.2.val)) ∧
        x u = true ∧ x v = true)
    constructor
    · rintro ⟨r,hr,bits⟩
      obtain ⟨p,real,rfl⟩ := List.mem_map.mp hr
      refine ⟨p.1,p.2,List.mem_map.mpr ⟨p,real,rfl⟩,?_,?_⟩
      · have hit := bits p.1
        rw [mask_bit p real] at hit
        exact bit_le_eq _ (by simpa using hit)
      · have hit := bits p.2
        rw [mask_bit p real] at hit
        exact bit_le_eq _ (by simpa using hit)
    · rintro ⟨u,v,mem,hu,hv⟩
      obtain ⟨p,real,eq⟩ := List.mem_map.mp mem
      have left : p.1 = u := Fin.ext (congrArg Prod.fst eq)
      have right : p.2 = v := Fin.ext (congrArg Prod.snd eq)
      refine ⟨edgeMask p,List.mem_map.mpr ⟨p,real,rfl⟩,?_⟩
      intro i
      rw [mask_bit p real,left,right]
      by_cases hi : i = u
      · subst i
        simp [hu]
      · by_cases hj : i = v
        · subst i
          simp [hv]
        · rw [beq_eq_false_iff_ne.mpr hi,beq_eq_false_iff_ne.mpr hj]
          cases x i <;> decide
  obtain ⟨C,valid,_,_,size,yes,no⟩ := construction
  have mono : Monotone2 C := by
    intro g used
    have arity := valid.2.2 g used
    exact ⟨by simpa using valid.1 g used,by omega⟩
  obtain ⟨sound,complete⟩ := samples _ (monotone_eval C mono)
  refine ⟨C,mono,fun x => ?_,size⟩
  exact ⟨fun h => (edge_characterization x).mp (sound.mp no x h),
    fun h => complete.mp yes x ((edge_characterization x).mpr h)⟩
