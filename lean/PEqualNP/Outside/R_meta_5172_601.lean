import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Isolate the inverter, if present. Evaluate the monotone suffix just twice
-- per row, independently of which earlier wire supplies that inverter.
theorem PEqualNP.Outside.R_meta_5172_601
    (isolate : ∀ (C : Circuit) (n : ℕ), FanInTwo C → (C.gates.filter (fun g => GateOp.rec false false true (fun _ => false) false g.op)).length ≤ 1 →
      ∃ (p s : List Gate) (e : Bool) (k : ℕ), k ≤ n+p.length ∧ p.length+s.length+e.toNat = C.size ∧ Monotone2 ⟨p++s,0⟩ ∧
      ∀ a : List Bool, a.length = n → let w := (Circuit.mk p 0).wires a
        C.eval a = (Circuit.mk s C.output).eval (w ++ List.replicate e.toNat (!(w.getD k false))))
    (ordered : ∀ (C : Circuit), Monotone2 C → ∀ w : List Bool,
      C.eval (w++[false]) = true → C.eval (w++[true]) = true)
    (separate : ∀ (i j : Fin 9) (p s : List Gate) (o : ℕ) (e : Bool), 9*i.val+j.val ∈ [1,2,3,4,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61] → Monotone2 ⟨p++s,0⟩ → p.length+s.length+e.toNat ≤ 13 →
      let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun v => x (Fin.ofNat 9 (v / 9)) && x (Fin.ofNat 9 (v % 9)))
      let bank := fun x : Fin 9 → Bool => (Circuit.mk p 0).wires (List.ofFn x ++ [!(x 0), x i || x j])
      let out := fun (x : Fin 9 → Bool) (v : Bool) => (Circuit.mk s o).eval (bank x ++ List.replicate e.toNat v)
      (∃ x, (out x false = true ∧ f x = false) ∨ (out x true = false ∧ f x = true)) ∨
        ∀ k ≤ 11+p.length, ∃ x, out x false = false ∧ out x true = true ∧ (!((bank x).getD k false)) ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (9 : ℕ) * ↑x3 + ↑x4 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (21 : ℕ), (22 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (31 : ℕ), (33 : ℕ), (42 : ℕ), (61 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x10 : ℕ) => Bool.false) Bool.false x9.op) x5.gates).length ≤ (1 : ℕ) → ¬x2 x3 x4 x5 := by
  dsimp only
  intro i j C pairs fan small few correct
  obtain ⟨p,s,e,k,hk,cost,mono,cut⟩ := isolate C 11 fan few
  let f := fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun v => x (Fin.ofNat 9 (v / 9)) && x (Fin.ofNat 9 (v % 9)))
  let input := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0), x i || x j]
  let bank := fun x => (Circuit.mk p 0).wires (input x)
  let out := fun (x : Fin 9 → Bool) (v : Bool) => (Circuit.mk s C.output).eval (bank x ++ List.replicate e.toNat v)
  have monoS : Monotone2 ⟨s,C.output⟩ := fun g hg => mono g (List.mem_append_right p hg)
  have co (x : Fin 9 → Bool) : out x false = true → out x true = true := by
    cases e with
    | false => exact id
    | true => exact ordered _ monoS (bank x)
  have fits (x : Fin 9 → Bool) : out x (!((bank x).getD k false)) = f x := by
    exact (cut (input x) (by simp [input])).symm.trans (correct x)
  have h := separate i j p s C.output e pairs mono (by omega)
  change (∃ x, (out x false = true ∧ f x = false) ∨ (out x true = false ∧ f x = true)) ∨
    ∀ a ≤ 11+p.length, ∃ x, out x false = false ∧ out x true = true ∧ (!((bank x).getD a false)) ≠ f x at h
  rcases h with ⟨x,hx⟩ | misses
  · have v := fits x
    rcases hx with ⟨hl,hf⟩ | ⟨hh,hf⟩
    · have hh := co x hl
      cases he : !((bank x).getD k false) <;> simp only [he,hl,hh,hf] at v <;> contradiction
    · have hl : out x false = false := by
        cases he : out x false
        · rfl
        · exact (Bool.noConfusion (hh.symm.trans (co x he)))
      cases he : !((bank x).getD k false) <;> simp only [he,hl,hh,hf] at v <;> contradiction
  · obtain ⟨x,hl,hh,wrong⟩ := misses k hk
    have v := fits x
    cases he : !((bank x).getD k false) <;> simp_all only [Bool.false_eq_true]
