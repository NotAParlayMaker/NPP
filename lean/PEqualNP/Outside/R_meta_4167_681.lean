import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_4167_681
    (lower : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (normal : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → (∀ x5 ∈ x2.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) → ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → (∀ x9 ∈ x7.inputs, x9 < x1 + x6) ∧ x7.inputs.Nodup ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (1 : ℕ)) ∧ (x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length = (2 : ℕ)))
    (search : ∀ C : Circuit, Monotone2 C → C.size = 15 → C.output = 23 →
      (C.gates[0]? = some ⟨.or,[0,2]⟩ ∨ C.gates[0]? = some ⟨.or,[2,0]⟩) →
      (∀ i g, C.gates[i]? = some g →
        (∀ w ∈ g.inputs, w < 9+i) ∧ g.inputs.Nodup ∧ g.inputs.length=2) →
      (∀ v : Fin 3, C.gates.countP (fun g => g.inputs.contains (![4,6,7] v)) ≤ 2) →
      circuitFun 9 C ≠ (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → x2.size = (15 : ℕ) → (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1 := by
  intro target C hfan hnot hwire hsize hocc heq
  have minimal : IsMinimalCircuit 9 C := by
    refine ⟨hfan, fun D hD same => ?_⟩
    by_contra! hsmall
    apply lower
    exact ⟨D,hD,by omega,fun x => congrFun (same.trans heq) x⟩
  have live : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y := by
    rw [heq]
    exact ⟨fun _ => false,fun _ => true,by decide +kernel⟩
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨hop,hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
    exact ⟨hop.elim Or.inl (fun hp => hp.elim Or.inr (fun hn => (hnot g hg hn).elim)),hlen⟩
  have proper (i : ℕ) (g : Gate) (hg : C.gates[i]? = some g) :
      (∀ w ∈ g.inputs, w < 9+i) ∧ g.inputs.Nodup ∧ g.inputs.length=2 := by
    obtain ⟨hb,hd,_,hl⟩ := normal 9 C minimal live (fun g hg hn => (hnot g hg hn).elim) i g hg
    exact ⟨hb,hd,hl (hnot g (List.mem_of_getElem? hg))⟩
  let run (gs : List Gate) (u : List Bool) :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u
  have append_run (a b : List Gate) (u : List Bool) :
      run (a ++ b) u = run b (run a u) := by simp [run,List.foldl_append]
  have extend (gs : List Gate) (u : List Bool) :
      ∃ r : List Bool, run gs u = u++r ∧ r.length=gs.length := by
    induction gs generalizing u with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map fun i => u.getD i false)
      obtain ⟨r,hr,hlen⟩ := ih (u++[b])
      exact ⟨b::r,by simpa [run,List.append_assoc,b] using hr,by simp [hlen]⟩
  have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (run gs u).getD i false = u.getD i false := by
    obtain ⟨r,hr,_⟩ := extend gs u
    rw [hr,List.getD_append _ _ _ _ hi]
  have run_len (gs : List Gate) (u : List Bool) : (run gs u).length = u.length+gs.length := by
    obtain ⟨r,hr,hL⟩ := extend gs u
    simp [hr,hL]
  have input (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    fin_cases i <;> rfl
  have gates_len : C.gates.length = 15 := hsize
  have out_lt : C.output < 24 := by
    by_contra! h
    have hz := List.getD_eq_default (run C.gates (List.ofFn (fun _ : Fin 9 => true))) false
      (n := C.output) (by rw [run_len,List.length_ofFn,gates_len]; omega)
    change circuitFun 9 C (fun _ => true) = false at hz
    rw [heq] at hz
    have ht : target (fun _ => true) = true := by decide +kernel
    simp [ht] at hz
  have out_last : C.output = 23 := by
    by_contra hn
    let k := C.output + 1 - 9
    have hk : k < C.gates.length := by dsimp [k]; omega
    let D : Circuit := ⟨C.gates.take k,C.output⟩
    have hD : FanInTwo D := fun g hg => hfan g ((List.take_sublist _ _).subset hg)
    have same : circuitFun 9 D = circuitFun 9 C := by
      funext x
      change (run (C.gates.take k) (List.ofFn x)).getD C.output false =
        (run C.gates (List.ofFn x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop k C.gates,append_run]
      symm
      apply keep
      rw [run_len,List.length_ofFn,List.length_take_of_le hk.le]
      dsimp [k]
      omega
    have h := minimal.2 D hD same
    change C.gates.length ≤ (C.gates.take k).length at h
    rw [List.length_take_of_le hk.le] at h
    omega
  obtain ⟨g,rest,first⟩ : ∃ g rest, C.gates = g::rest := by
    cases h : C.gates with
    | nil => rw [h] at gates_len; simp at gates_len
    | cons g rest => exact ⟨g,rest,rfl⟩
  have at_zero : C.gates[0]? = some g := by simp [first]
  have hg := List.mem_of_getElem? at_zero
  obtain ⟨back,distinct,two⟩ := proper 0 g at_zero
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp two
  have alo := back a (by simp [ab])
  have blo := back b (by simp [ab])
  let A : Fin 9 := ⟨a,by omega⟩
  let B : Fin 9 := ⟨b,by omega⟩
  have hab : A ≠ B := by
    intro h
    have he := congrArg Fin.val h
    change a=b at he
    simp [ab,he] at distinct
  have value (x : Fin 9 → Bool) : g.op.eval [x A,x B] = (x 0 || x 2) := by
    have hw := hwire x
    change (run C.gates (List.ofFn x)).getD 9 false = _ at hw
    rw [first] at hw
    let u := List.ofFn x
    let r := g.op.eval (g.inputs.map fun i => u.getD i false)
    change (run rest (u++[r])).getD 9 false = _ at hw
    have hu : u.length=9 := by simp [u]
    rw [keep _ _ _ (by simp [hu]),List.getD_append_right _ _ _ _ (by omega)] at hw
    simp only [hu,Nat.sub_self,List.getD_cons_zero] at hw
    change r = _ at hw
    change g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false)) = _ at hw
    rw [ab] at hw
    change g.op.eval [(List.ofFn x).getD A.val false,(List.ofFn x).getD B.val false] = _ at hw
    rwa [input x A,input x B] at hw
  have identify : ∀ (s t : Fin 9) (isAnd : Bool), s ≠ t →
      (∀ i : Fin 9, (if isAnd then GateOp.and else GateOp.or).eval [decide (s=i),decide (t=i)] =
        (decide ((0 : Fin 9)=i) || decide ((2 : Fin 9)=i))) →
      isAnd = false ∧ ((s=0 ∧ t=2) ∨ (s=2 ∧ t=0)) := by decide +kernel
  have signature (isAnd : Bool) (hop : g.op = if isAnd then .and else .or) :
      ∀ i : Fin 9, (if isAnd then GateOp.and else GateOp.or).eval [decide (A=i),decide (B=i)] =
        (decide ((0 : Fin 9)=i) || decide ((2 : Fin 9)=i)) := by
    intro i
    have hi := value (fun j => decide (j=i))
    rw [hop] at hi
    exact hi
  have gate_or : g.op = .or := by
    have hop := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · have hf := (identify A B true hab (signature true ha)).1
      cases hf
    · exact ho
  have order : (A=0 ∧ B=2) ∨ (A=2 ∧ B=0) :=
    (identify A B false hab (signature false gate_or)).2
  have packed : C.gates[0]? = some ⟨.or,[0,2]⟩ ∨ C.gates[0]? = some ⟨.or,[2,0]⟩ := by
    rw [at_zero]
    rcases order with ⟨hA,hB⟩ | ⟨hA,hB⟩
    · left
      have av : a=0 := congrArg Fin.val hA
      have bv : b=2 := congrArg Fin.val hB
      cases g
      simp_all
    · right
      have av : a=2 := congrArg Fin.val hA
      have bv : b=0 := congrArg Fin.val hB
      cases g
      simp_all
  exact search C mono hsize out_last packed proper hocc heq
