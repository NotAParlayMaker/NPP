import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_4877_836
    (geometry : let inc := fun (p l : Fin 13) => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
    let edge := fun (P L : Fin 13 → Bool) => decide (∃ p l, inc p l ∧ P p=true ∧ L l=true)
    let line := fun (P : Fin 13 → Bool) (l : Fin 13) => !(P l || P (l+1) || P (l+3) || P (l+9))
    let point := fun (L : Fin 13 → Bool) (p : Fin 13) => !(L p || L (p-1) || L (p-3) || L (p-9))
    let one := fun (p x : Fin 13) => decide (x=p)
    (∀ p l, line (one p) l=false → edge (one p) (one l)=true) ∧
    (∀ P, edge P (line P)=false) ∧ ∀ L, edge (point L) L=false)
    (assemble : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
  PEqualNP.TopForm.IsAO2 26 C →
  (∀ g ∈ C.gates, g.inputs.Nodup) →
  u < 26 + C.size → v < 26 + C.size → u ≠ v →
  (∀ b : Bool,
    have w : List Bool := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if b = true then 13 else 0))
    w.getD u false = false ∧ w.getD v false = false) →
  have D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and,[u,v]⟩],26+C.size⟩
  PEqualNP.TopForm.IsAO2 26 D ∧
  (∀ g ∈ D.gates, g.inputs.Nodup) ∧
  (∀ x : List Bool, x.length = 26 → D.eval x = ((C.wires x).getD u false && (C.wires x).getD v false)) ∧
  ∀ b : Bool, ∃ d : ℕ → Bool,
    (∀ i < 26, d i = decide (i = if b = true then 0 else 13)) ∧
    (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (a c : ℕ),
      D.gates[j]? = some g → g.inputs = [a,c] →
      have w : List Bool := D.wires (List.ofFn fun i : Fin 26 => decide (i.val = if b = true then 13 else 0))
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        d (26+j) = (w.getD a false && d c || d a && w.getD c false)) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → d (26+j) = (d a || d c))) ∧
    d D.output = false)
    (factors : let inc := fun (p l : Fin 13) => p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
    let edge := fun (P L : Fin 13 → Bool) => decide (∃ p l, inc p l ∧ P p=true ∧ L l=true)
    ∃ (C : Circuit) (u v : Nat),
      C.size ≤ 63 ∧ TopForm.IsAO2 26 C ∧ (∀ g∈C.gates, g.inputs.Nodup) ∧
      u<26+C.size ∧ v<26+C.size ∧ u≠v ∧
      (∀ b : Bool,
        let w := C.wires (List.ofFn fun i : Fin 26 => decide (i.val = if b=true then 13 else 0))
        w.getD u false=false ∧ w.getD v false=false) ∧
      (∀ P L : Fin 13 → Bool,
        let w := C.wires (List.ofFn fun i : Fin 26 => Fin.addCases P L i)
        (w.getD u false && w.getD v false) = edge P L) ∧
      (∀ i : Fin 26, ∃ x : Fin 26 → Bool,
        (C.wires (List.ofFn x)).getD u false ≠
        (C.wires (List.ofFn fun j => x j || decide (j=i))).getD u false) ∧
      17 ≤ { i : Fin 26 | ∃ x : Fin 26 → Bool,
        (C.wires (List.ofFn x)).getD v false ≠
        (C.wires (List.ofFn fun j => x j || decide (j=i))).getD v false }.ncard) :
  have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧         (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧           (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧             ∀ (x5 : Bool),               ∃ (x6 : ℕ → Bool),                 (∀ x7 < (26 : ℕ), x6 x7 = Decidable.decide (x7 = if x5 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ),                       x4.gates[x7]? = Option.some x8 →                         x8.inputs = [x9, x10] →                           have x13 : List Bool := x4.wires (List.ofFn fun (x13 : Fin (26 : ℕ)) => Decidable.decide (↑x13 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ((26 : ℕ) + x7) = (x13.getD x9 Bool.false && x6 x10 || x6 x9 && x13.getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 ((26 : ℕ) + x7) = (x6 x9 || x6 x10))) ∧                     x6 x4.output = Bool.false := by
  dsimp only at factors geometry ⊢
  obtain ⟨C,u,v,sz,legal,nd,hu,hv,ne,sing,eval,_⟩ := factors
  obtain ⟨law,distinct,he,der⟩ := assemble C u v legal nd hu hv ne sing
  refine ⟨_,by change (C.gates ++ [_]).length ≤ 64; rw [List.length_append]; exact Nat.succ_le_succ sz,law,distinct,?_,?_,der⟩
  · intro p l hit
    rw [he _ (by simp)]
    exact (eval _ _).trans (geometry.1 p l hit)
  · intro P _
    constructor
    · rw [he _ (by simp)]
      exact (eval _ _).trans (geometry.2.1 P)
    · rw [he _ (by simp)]
      exact (eval _ _).trans (geometry.2.2 P)
