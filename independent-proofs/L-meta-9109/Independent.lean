import PEqualNP.Defs

namespace PNP8133
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

end PNP8133
namespace PNP8133
def masks : List Nat := [34,69,138,260,192,385,274,52,104]
def edges : List Nat := [1,12,23,34,40,5,16,27,38,57,68,85]
def π (i : Fin 9) : Fin 9 := [4,0,1,6,7,3,5,2,8][i.val]!
def tailV (k : Nat) := Fin.ofNat 9 (k/10)
def headV (k : Nat) := Fin.ofNat 9 (k%10)
def adj (i j : Fin 9) : Bool := (masks.getD i.val 0).testBit j.val

theorem edgeForward : ∀ i j : Fin 9, adj i j = true → ∃ k ∈ edges,
    (π i = tailV k ∧ π j = headV k) ∨ (π i = headV k ∧ π j = tailV k) := by decide +kernel
theorem edgeBackward : ∀ k ∈ edges, ∃ i j : Fin 9,
    adj i j = true ∧ π i = tailV k ∧ π j = headV k := by decide +kernel

def maskFun (x : Fin 9 → Bool) := decide (∃ i j : Fin 9, x i = true ∧ x j = true ∧ adj i j = true)
def listFun (y : Fin 9 → Bool) := edges.any fun k => y (tailV k) && y (headV k)

theorem edgeIso (y : Fin 9 → Bool) : maskFun (fun i => y (π i)) = listFun y := by
  apply Bool.eq_iff_iff.mpr
  simp only [maskFun, listFun, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i,j,hi,hj,ha⟩
    obtain ⟨k,hk,hor⟩ := edgeForward i j ha
    rcases hor with ⟨a,b⟩ | ⟨a,b⟩
    · exact ⟨k,hk,a ▸ hi,b ▸ hj⟩
    · exact ⟨k,hk,b ▸ hj,a ▸ hi⟩
  · rintro ⟨k,hk,ht,hh⟩
    obtain ⟨i,j,ha,a,b⟩ := edgeBackward k hk
    exact ⟨i,j,a.symm ▸ ht,b.symm ▸ hh,ha⟩
#print axioms edgeIso
end PNP8133
namespace PNP8133
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def zGate : Gate := ⟨.or,[]⟩
def pad (C : Circuit) (k : Nat) : Circuit := ⟨C.gates ++ List.replicate k zGate,C.output⟩
theorem fold_zGate (w : List Bool) (k : Nat) :
  (List.replicate k zGate).foldl gateStep w = w ++ List.replicate k false := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ',List.foldl_append,ih,List.replicate_succ']
    simp [gateStep,zGate,GateOp.eval,List.append_assoc]
theorem pad_eval (C : Circuit) (k : Nat) (bits : List Bool) :
    (pad C k).eval bits = C.eval bits := by
  change (List.foldl gateStep bits (C.gates ++ List.replicate k zGate)).getD C.output false = _
  rw [List.foldl_append,fold_zGate]
  let l := C.gates.foldl gateStep bits
  change (l ++ List.replicate k false).getD C.output false = l.getD C.output false
  by_cases h : C.output < l.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,h,List.getElem?_eq_none (Nat.le_of_not_gt h),List.getElem?_replicate]
    split <;> rfl
theorem pad_fan (C : Circuit) (k : Nat) (h : FanInTwo C) : FanInTwo (pad C k) := by
  intro g hg
  change g ∈ C.gates ++ List.replicate k zGate at hg
  rcases List.mem_append.mp hg with hor | hz
  · exact h g hor
  · have he := (List.mem_replicate.mp hz).2
    subst g
    exact ⟨Or.inr (Or.inl rfl),by decide⟩
theorem pad_size (C : Circuit) (k : Nat) : (pad C k).size = C.size + k := by simp [pad,Circuit.size]
theorem bridge (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ 15)
    (hf : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = maskFun x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = 15 ∧ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = listFun y := by
  let D := rcirc π C
  have hD : FanInTwo D := arity_rename π C (fun o => o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not) 2 hC
  have hDs : D.size = C.size := circuit_size_rename π C
  refine ⟨pad D (15-C.size),pad_fan D _ hD, ?_, ?_⟩
  · rw [pad_size,hDs]; omega
  · intro y
    rw [pad_eval,circuit_rename,hf,edgeIso]
#print axioms bridge
end PNP8133

theorem PNP8133.checkedChild : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun (x1 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)), x1 x2 = Bool.true ∧ x1 x3 = Bool.true ∧ ([(34 : ℕ), (69 : ℕ), (138 : ℕ), (260 : ℕ), (192 : ℕ), (385 : ℕ), (274 : ℕ), (52 : ℕ), (104 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true)) x) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 15 ∧ ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = (fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))) y := by exact PNP8133.bridge
#print axioms PNP8133.checkedChild
