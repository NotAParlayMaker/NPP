import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rwire {n : Nat} (p : Fin n → Fin n) (i : Nat) : Nat := if h : i < n then (p ⟨i,h⟩).val else i
def rgate {n : Nat} (p : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (rwire p)⟩
def rcirc {n : Nat} (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (rgate p),rwire p C.output⟩

theorem lookup_rename {n : Nat} (p : Fin n → Fin n) (x : Fin n → Bool) (t : List Bool) (i : Nat) :
  ((List.ofFn x) ++ t).getD (rwire p i) false = ((List.ofFn (fun j => x (p j))) ++ t).getD i false := by
  by_cases h : i < n
  · have h' := (p ⟨i,h⟩).isLt
    simp [rwire,h,List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_ofFn,h']
  · simp [rwire,h,List.getD_eq_getElem?_getD,List.getElem?_append,List.getElem?_ofFn]

def gateStep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem run_rename {n : Nat} (p : Fin n → Fin n) (x : Fin n → Bool) (gs : List Gate) (t : List Bool) :
  ∃ u : List Bool,
   (gs.map (rgate p)).foldl gateStep (List.ofFn x ++ t) = List.ofFn x ++ u ∧
   gs.foldl gateStep (List.ofFn (fun j => x (p j)) ++ t) = List.ofFn (fun j => x (p j)) ++ u := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (List.ofFn (fun j => x (p j)) ++ t).getD i false)
    have eq : (rgate p g).op.eval ((rgate p g).inputs.map fun i => (List.ofFn x ++ t).getD i false) = v := by
      dsimp [v,rgate]; rw [List.map_map]; apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _; exact lookup_rename p x t i
    simp only [List.map_cons,List.foldl_cons]
    change ∃ u, (List.map (rgate p) gs).foldl gateStep ((List.ofFn x ++ t) ++ [_]) = _ ∧
                gs.foldl gateStep ((List.ofFn (fun j => x (p j)) ++ t) ++ [v]) = _
    rw [eq]; simp only [List.append_assoc]
    exact ih (t ++ [v])

theorem circuit_rename {n : Nat} (p : Fin n → Fin n) (x : Fin n → Bool) (C : Circuit) :
  (rcirc p C).eval (List.ofFn x) = C.eval (List.ofFn (fun j => x (p j))) := by
  obtain ⟨u,h1,h2⟩ := run_rename p x C.gates []
  simp only [List.append_nil] at h1 h2
  change (List.foldl gateStep (List.ofFn x) (C.gates.map (rgate p))).getD (rwire p C.output) false =
    (List.foldl gateStep (List.ofFn fun j => x (p j)) C.gates).getD C.output false
  rw [h1,h2]; exact lookup_rename p x u C.output

theorem circuit_size_rename {n : Nat} (p : Fin n → Fin n) (C : Circuit) : (rcirc p C).size = C.size := by
  simp [rcirc,Circuit.size]

-- This form preserves every predicate on the gate operation and every arity cap.
theorem arity_rename {n : Nat} (p : Fin n → Fin n) (C : Circuit) (O : GateOp → Prop) (b : Nat)
  (h : ∀ g ∈ C.gates, O g.op ∧ g.inputs.length ≤ b) :
  ∀ g ∈ (rcirc p C).gates, O g.op ∧ g.inputs.length ≤ b := by
  intro g hg
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
  simpa [rgate] using h j hj
def graph9 : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))
def π6 (i : Fin 8) : Fin 8 := [1, 0, 4, 7, 5, 2, 6, 3][i.val]!
theorem funct6 (x : Fin 8 → Bool) : graph9 ((6 : Fin 9).insertNth false (fun j => x (π6 j))) = graph9 ((4 : Fin 9).insertNth false x) := by
  change ((x 1 && x 0) || ((x 0 && x 4) || ((x 4 && x 7) || ((x 7 && x 5) || ((x 5 && x 1) || ((x 1 && x 2) || ((x 0 && false) || ((x 4 && x 6) || ((x 7 && x 3) || ((x 2 && x 6) || ((false && x 3) || ((x 3 && x 2) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && false) || ((false && x 0) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false))))))))))))
  simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
def π7 (i : Fin 8) : Fin 8 := [2, 1, 0, 4, 6, 3, 5, 7][i.val]!
theorem funct7 (x : Fin 8 → Bool) : graph9 ((7 : Fin 9).insertNth false (fun j => x (π7 j))) = graph9 ((4 : Fin 9).insertNth false x) := by
  change ((x 2 && x 1) || ((x 1 && x 0) || ((x 0 && x 4) || ((x 4 && x 6) || ((x 6 && x 2) || ((x 2 && x 3) || ((x 1 && x 5) || ((x 0 && false) || ((x 4 && x 7) || ((x 3 && false) || ((x 5 && x 7) || ((x 7 && x 3) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && false) || ((false && x 0) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false))))))))))))
  simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
theorem rename_transport (k : Fin 9) (ρ : Fin 8 → Fin 8)
 (hρ : ∀ x : Fin 8 → Bool, graph9 (k.insertNth false (fun j => x (ρ j))) = graph9 ((4 : Fin 9).insertNth false x))
 (C : Circuit) (hC : FanInTwo C) (hf : circuitFun 8 C = fun x => graph9 (k.insertNth false x)) :
 ∃ D : Circuit, FanInTwo D ∧ circuitFun 8 D = (fun x => graph9 ((4 : Fin 9).insertNth false x)) ∧ D.size ≤ C.size := by
 refine ⟨rcirc ρ C,arity_rename ρ C (fun o => o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) 2 hC, ?_, Nat.le_of_eq (circuit_size_rename ρ C)⟩
 funext x
 change (rcirc ρ C).eval (List.ofFn x) = _
 rw [circuit_rename]
 exact (congrFun hf (fun j => x (ρ j))).trans (hρ x)
theorem transport8555 :
 ∀ k ∈ [(6 : Fin 9), 7], ∀ C : Circuit, FanInTwo C → circuitFun 8 C = (fun x => graph9 (k.insertNth false x)) →
 ∃ D : Circuit, FanInTwo D ∧ circuitFun 8 D = (fun x => graph9 ((4 : Fin 9).insertNth false x)) ∧ D.size ≤ C.size := by
 intro k hk C hC hf
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl | rfl
 · exact rename_transport 6 π6 funct6 C hC hf
 · exact rename_transport 7 π7 funct7 C hC hf
theorem wire_rename {n : Nat} (p : Fin n → Fin n) (x : Fin n → Bool) (C : Circuit) (i : Nat) :
 ((rcirc p C).wires (List.ofFn x)).getD (rwire p i) false = (C.wires (List.ofFn (fun j => x (p j)))).getD i false := by
 obtain ⟨u,h₁,h₂⟩ := run_rename p x C.gates []
 simp only [List.append_nil] at h₁ h₂
 change (List.foldl gateStep (List.ofFn x) (C.gates.map (rgate p))).getD (rwire p i) false =
    (List.foldl gateStep (List.ofFn fun j => x (p j)) C.gates).getD i false
 rw [h₁,h₂]; exact lookup_rename p x u i

theorem truefunct6 (x : Fin 8 → Bool) : graph9 ((6 : Fin 9).insertNth true (fun j => x (π6 j))) = graph9 ((4 : Fin 9).insertNth true x) := by
  change ((x 1 && x 0) || ((x 0 && x 4) || ((x 4 && x 7) || ((x 7 && x 5) || ((x 5 && x 1) || ((x 1 && x 2) || ((x 0 && true) || ((x 4 && x 6) || ((x 7 && x 3) || ((x 2 && x 6) || ((true && x 3) || ((x 3 && x 2) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && true) || ((true && x 0) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false))))))))))))
  simp only [Bool.false_and, Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false, Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]

theorem truefunct7 (x : Fin 8 → Bool) : graph9 ((7 : Fin 9).insertNth true (fun j => x (π7 j))) = graph9 ((4 : Fin 9).insertNth true x) := by
  change ((x 2 && x 1) || ((x 1 && x 0) || ((x 0 && x 4) || ((x 4 && x 6) || ((x 6 && x 2) || ((x 2 && x 3) || ((x 1 && x 5) || ((x 0 && true) || ((x 4 && x 7) || ((x 3 && true) || ((x 5 && x 7) || ((x 7 && x 3) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && true) || ((true && x 0) || ((x 0 && x 4) || ((x 1 && x 5) || ((x 2 && x 6) || ((x 3 && x 7) || ((x 4 && x 6) || ((x 5 && x 7) || ((x 7 && x 4) || false))))))))))))
  simp only [Bool.false_and, Bool.true_and, Bool.and_true, Bool.and_false, Bool.false_or, Bool.or_false, Bool.and_comm, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
def sensitive (k : Fin 9) (x : Fin 8 → Bool) : Prop :=
 graph9 (k.insertNth false x) = false ∧ graph9 (k.insertNth true x) = true
theorem buildWireBridge (k : Fin 9) (ρ : Fin 8 → Fin 8)
 (h₀ : ∀ x : Fin 8 → Bool, graph9 (k.insertNth false (fun j => x (ρ j))) = graph9 ((4 : Fin 9).insertNth false x))
 (h₁ : ∀ x : Fin 8 → Bool, graph9 (k.insertNth true (fun j => x (ρ j))) = graph9 ((4 : Fin 9).insertNth true x))
 (C : Circuit) (hC : FanInTwo C) (hsize : C.size = 13)
 (hf : circuitFun 8 C = (fun x => graph9 (k.insertNth false x))) :
 ∃ D : Circuit, FanInTwo D ∧ D.size = 13 ∧ circuitFun 8 D = (fun x => graph9 ((4 : Fin 9).insertNth false x)) ∧
   ∀ i : Nat, ∃ j : Nat, ∀ x : Fin 8 → Bool, sensitive 4 x ∧ (D.wires (List.ofFn x)).getD j false = false →
     ∃ y : Fin 8 → Bool, sensitive k y ∧ (C.wires (List.ofFn y)).getD i false = false := by
 let D := rcirc ρ C
 have hD : FanInTwo D := arity_rename ρ C (fun o => o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) 2 hC
 have hDs : D.size = 13 := (circuit_size_rename ρ C).trans hsize
 have hDf : circuitFun 8 D = (fun x => graph9 ((4 : Fin 9).insertNth false x)) := by
   funext x; change (rcirc ρ C).eval (List.ofFn x) = _; rw [circuit_rename]
   exact (congrFun hf (fun j => x (ρ j))).trans (h₀ x)
 refine ⟨D,hD,hDs,hDf,?_⟩
 intro i
 refine ⟨rwire ρ i, ?_⟩
 intro x hx
 obtain ⟨⟨hminus,hplus⟩,hwire⟩ := hx
 exact ⟨fun j => x (ρ j), ⟨(h₀ x).trans hminus,(h₁ x).trans hplus⟩, (wire_rename ρ x C i).symm.trans hwire⟩
theorem bridge8557 :
 ∀ k ∈ [(6 : Fin 9), 7], ∀ C : Circuit, FanInTwo C → C.size = 13 → circuitFun 8 C = (fun x => graph9 (k.insertNth false x)) →
 ∃ D : Circuit, FanInTwo D ∧ D.size = 13 ∧ circuitFun 8 D = (fun x => graph9 ((4 : Fin 9).insertNth false x)) ∧
   ∀ i : Nat, ∃ j : Nat, ∀ x : Fin 8 → Bool, sensitive 4 x ∧ (D.wires (List.ofFn x)).getD j false = false →
     ∃ y : Fin 8 → Bool, sensitive k y ∧ (C.wires (List.ofFn y)).getD i false = false := by
 intro k hk C hC hs hf
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
 rcases hk with rfl | rfl
 · exact buildWireBridge 6 π6 funct6 truefunct6 C hC hs hf
 · exact buildWireBridge 7 π7 funct7 truefunct7 C hC hs hf

#print axioms bridge8557
