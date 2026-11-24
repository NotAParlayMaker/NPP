import PEqualNP.Defs

-- The seven-vertex edge numbering is the one used in the checked reduction R_meta_2016_83.
-- Each test below may choose a fresh copy and may replace any operand by the true input.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2016_64
    (noInverter : let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ c : Circuit, FanInTwo c → c.size = 11 → circuitFun 7 c = f → Monotone2 c)
    (fourTests : let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
      ∀ c : Circuit, Monotone2 c → c.size = 11 → circuitFun 7 c = f →
      ∃ t ∈ ([(4,9),(4,48),(1,96),(8,18)] : List (ℕ × ℕ)),
        ¬ ∃ d : Circuit, List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧
          List.Forall₂ (fun a b : ℕ => b = a+1 ∨ b = 0) g.inputs h.inputs) c.gates d.gates ∧
          (d.wires (true :: List.ofFn (fun i : Fin 7 => t.1.testBit i.val))).getD (c.output+1) false = true ∧
          (d.wires (true :: List.ofFn (fun i : Fin 7 => t.2.testBit i.val))).getD (c.output+1) false = false) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  intro graph
  rintro ⟨c, fan, size, base, variants⟩
  let f := fun (x : Fin 7 → Bool) => ([1,12,4,15,26,35,46,36] : List ℕ).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  have eqLow : ∀ x : Fin 7 → Bool, graph (Fin.insertNth 0 false (Fin.insertNth 3 false x)) = f x := by
    decide +kernel
  have low : circuitFun 7 c = f := funext fun x => (congrFun base x).trans (eqLow x)
  obtain ⟨t, member, impossible⟩ := fourTests c (noInverter c fan size low) size low
  let phase := t.1 != 4
  obtain ⟨a, b, d, out, aligned, eval⟩ := variants phase
  have loosened : List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧
      List.Forall₂ (fun u v : ℕ => v = u+1 ∨ v = 0) g.inputs h.inputs) c.gates d.gates := by
    apply List.Forall₂.imp (R := fun (g h : Gate) => g.op = h.op ∧ List.Forall₂
      (fun u v : ℕ => v = u+1 ∨ v = 0 ∧ (u = a ∨ u = b)) g.inputs h.inputs) _ aligned
    intro g h gh
    refine ⟨gh.1, ?_⟩
    apply List.Forall₂.imp _ gh.2
    intro u v uv
    exact uv.imp id And.left
  have observed (m : ℕ) : (d.wires (true :: List.ofFn (fun i : Fin 7 => m.testBit i.val))).getD (c.output+1) false =
      graph (Fin.insertNth 0 phase (Fin.insertNth 3 (!phase) (fun i : Fin 7 => m.testBit i.val))) := by
    rw [← out]
    exact eval _
  have pairValues : ∀ t ∈ ([(4,9),(4,48),(1,96),(8,18)] : List (ℕ × ℕ)),
      graph (Fin.insertNth 0 (t.1 != 4) (Fin.insertNth 3 (!(t.1 != 4)) (fun i : Fin 7 => t.1.testBit i.val))) = true ∧
      graph (Fin.insertNth 0 (t.1 != 4) (Fin.insertNth 3 (!(t.1 != 4)) (fun i : Fin 7 => t.2.testBit i.val))) = false := by
    decide +kernel
  obtain ⟨positive, negative⟩ := pairValues t member
  exact impossible ⟨d, loosened, (observed t.1).trans positive, (observed t.2).trans negative⟩
