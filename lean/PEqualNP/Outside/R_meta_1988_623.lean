import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1988_623
  (h1 : let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
    let graph := fun x : (Fin 26 → Bool) => ∃ p l : Fin 13, near p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    let vec := fun (P L : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)
    let off := fun P : Finset (Fin 13) => Finset.univ.filter fun l : Fin 13 => ∀ p ∈ P, ¬near p l
    ∀ f : (Fin 26 → Bool) → Bool, Monotone f →
    (∀ p l : Fin 13, near p l → f (vec {p} {l}) = true) →
    (∀ P : Finset (Fin 13), P.card ≤ 3 → f (vec P (off P)) = false ∧ f (vec (off P) P) = false) →
    ∀ x, f x = true ↔ graph x)
  (h2 : let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
    let graph := fun x : (Fin 26 → Bool) => ∃ p l : Fin 13, near p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    let sparse := fun g : (Fin 26 → Bool) → Bool => ∀ a b : Fin 26, g (fun t => decide (t = a)) = true → g (fun t => decide (t = b)) = true → a = b
    ∀ f g : (Fin 26 → Bool) → Bool, Monotone f → Monotone g →
    (∀ x, (f x = true ∧ g x = true) ↔ graph x) → sparse f ∨ sparse g)
  (h3 : let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
    let graph := fun x : (Fin 26 → Bool) => ∃ p l : Fin 13, near p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    let sparse := fun g : (Fin 26 → Bool) → Bool => ∀ a b : Fin 26, g (fun t => decide (t = a)) = true → g (fun t => decide (t = b)) = true → a = b
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ), PEqualNP.MetaComplexity.Monotone2 C →
    let wire := fun (k : ℕ) (x : (Fin 26 → Bool)) => (C.wires (List.ofFn x)).getD k false
    (∀ x, (wire i x = true ∧ wire j x = true) ↔ graph x) → sparse (wire i) → 63 ≤ C.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C pins m lim tested
  dsimp only at tested
  let wire := fun (k : ℕ) (x : Fin 26 → Bool) => (C.wires (List.ofFn x)).getD k false
  let allPins := fun x : Fin 26 → Bool => GateOp.and.eval (pins.map fun k => wire k x)
  have getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
      w.getD i false ≤ w'.getD i false := by
    induction h generalizing i with
    | nil => simp
    | cons hab _ ih =>
      cases i with
      | zero => simpa using hab
      | succ i => simpa using ih i
  have bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
    cases a <;> cases b <;> decide
  have gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
      (h : List.Forall₂ (fun a b => a ≤ b) w w') :
      g.op.eval (g.inputs.map fun i => w.getD i false) ≤
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
    rw [bool_le]
    rcases hg with hg | hg
    · rw [hg]
      change ((g.inputs.map fun i => w.getD i false).all id = true) → ((g.inputs.map fun i => w'.getD i false).all id = true)
      simp only [List.all_eq_true, List.mem_map, id]
      intro hx x hx'
      obtain ⟨i, hi, rfl⟩ := hx'
      exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
    · rw [hg]
      change ((g.inputs.map fun i => w.getD i false).any id = true) → ((g.inputs.map fun i => w'.getD i false).any id = true)
      simp only [List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩
  have fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
      ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
        List.Forall₂ (fun a b => a ≤ b)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
    induction gs with
    | nil => intro w w' h; simpa using h
    | cons g gs ih =>
      intro w w' h
      simp only [List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)
  have wm (k : ℕ) : Monotone (wire k) := by
    intro x y xy
    apply getD_le
    apply fold_le C.gates (fun g hg => (m g hg).1)
    rw [List.forall₂_iff_get]
    exact ⟨by simp,fun i hi hj => by simp only [List.get_eq_getElem,List.getElem_ofFn]; exact xy _⟩
  have am : Monotone allPins := by
    intro x y xy
    apply bool_le.mpr
    change (pins.map fun i => wire i x).all id = true → (pins.map fun i => wire i y).all id = true
    simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    exact fun h k hk => bool_le.mp (wm k xy) (h k hk)
  have cert := h1 allPins am tested.1 tested.2
  have ne : pins ≠ [] := by
    intro eq
    have bad := (tested.2 ∅ (by simp)).1
    rw [eq] at bad
    exact Bool.false_ne_true (show true = false from bad).symm
  obtain ⟨i,j,pair⟩ : ∃ i j : ℕ, ∀ x, (wire i x = true ∧ wire j x = true) ↔ allPins x = true := by
    dsimp only [allPins]
    cases pins with
    | nil => exact (ne rfl).elim
    | cons i t =>
      cases t with
      | nil =>
        refine ⟨i,i,fun x => ?_⟩
        change _ ↔ (wire i x && true) = true
        simp
      | cons j s =>
        cases s with
        | cons a as => simp at lim
        | nil =>
          refine ⟨i,j,fun x => ?_⟩
          change _ ↔ (wire i x && (wire j x && true)) = true
          simp
  have both := fun x => (pair x).trans (cert x)
  rcases h2 (wire i) (wire j) (wm i) (wm j) both with hi | hj
  · exact h3 C i j m both hi
  · exact h3 C j i m (fun x => And.comm.trans (both x)) hj
