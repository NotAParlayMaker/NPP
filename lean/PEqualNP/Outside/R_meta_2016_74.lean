import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2016_74
    (binary_bound :
      let f := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any
        fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ c : Circuit, FanInTwo c → circuitFun 7 c = f →
        11 ≤ (c.gates.filter fun g => (g.inputs.length == 2) && g.op.eval [true,true]).length)
    (positive_tables :
      let f := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any
        fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      let row := fun x : Fin 7 → Bool => f x = false ∨ (List.ofFn x).count true ≤ 2
      ∀ c : Circuit, c.size = 11 →
        (∀ g ∈ c.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) →
        (∀ x, row x → circuitFun 7 c x = f x) →
        ¬∀ t : Bool, ∃ (a b : ℕ) (d : Circuit),
          List.Forall₂ (fun g h : Gate => g.op = h.op ∧
            List.Forall₂ (fun i j => j = i+1 ∨ j = 0 ∧ (i = a ∨ i = b)) g.inputs h.inputs)
            c.gates d.gates ∧
          ∀ x, row x → (d.wires (true :: List.ofFn x)).getD (c.output+1) false =
            (f x || (if t then (x 0 || x 3) else x 2))) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  intro graph
  rintro ⟨c,fan,size,base,mixed⟩
  let f := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List ℕ).any
    fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  have base_eq : ∀ x : Fin 7 → Bool,
      graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = f x := by decide
  have branch_eq : ∀ (t : Bool) (x : Fin 7 → Bool),
      graph (Fin.insertNth 0 t (Fin.insertNth 3 (!t) x)) =
        (f x || (if t then (x 0 || x 3) else x 2)) := by decide
  have hf : circuitFun 7 c = f := funext fun x => (congrFun base x).trans (base_eq x)
  let bin := fun g : Gate => (g.inputs.length == 2) && g.op.eval [true,true]
  have lower : 11 ≤ (c.gates.filter bin).length := binary_bound c fan hf
  have upper := List.length_filter_le bin c.gates
  change c.gates.length = 11 at size
  have allbin := List.length_filter_eq_length_iff.mp (show (c.gates.filter bin).length = c.gates.length by omega)
  have positive (g : Gate) (hg : g ∈ c.gates) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
    have h : bin g = true := allbin g hg
    change ((g.inputs.length == 2) && g.op.eval [true,true]) = true at h
    have hparts := Bool.and_eq_true_iff.mp h
    have hlen : g.inputs.length = 2 := by simpa only [beq_iff_eq] using hparts.1
    have ok := (fan g hg).1
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at ok
    rcases ok with hA | hO | hN
    · exact ⟨Or.inl hA,hlen⟩
    · exact ⟨Or.inr hO,hlen⟩
    · have impossible := hparts.2
      rw [hN] at impossible
      exact Bool.noConfusion (show false = true from impossible)
  apply positive_tables c size positive (fun x _ => congrFun hf x)
  intro t
  obtain ⟨a,b,d,ho,ports,ev⟩ := mixed t
  refine ⟨a,b,d,ports,fun x _ => ?_⟩
  rw [← ho]
  exact (ev x).trans (branch_eq t x)
