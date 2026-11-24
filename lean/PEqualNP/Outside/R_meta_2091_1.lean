import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2091_1
 (unfolded : let D : Finset (Fin 13) := {0,1,3,9}
  let I := fun p l : Fin 13 => ∃ d∈D,p=l+d
  let A := fun S : Finset (Fin 13) => fun l : Fin 13 => ∀ p∈S, ¬I p l
  let maximal := fun S : Finset (Fin 13) => (∀ p∉S, ∃ l,A S l ∧ I p l) ∧ ((∃ l, ∀ p∈S,I p l) ∨ ∃ p, ∀ l,A S l → I p l)
  let test := fun (S : Finset (Fin 13)) (i : Fin 26) => decide ((∃ p∈S,i=Fin.castAdd 13 p) ∨ ∃ l,i=Fin.natAdd 13 l ∧ A S l)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size≤62 → ∀ (u v : Fin (26+C.size)), u≠v →
  let cost := C.gates.foldl (fun (w : List Nat) g => w ++ [(g.inputs.map (fun i => w.getD i 0)).sum+1]) (List.replicate 26 0)
  let out := fun x : Fin 26 → Bool => let w := C.wires (List.ofFn x); w.getD u.val false || w.getD v.val false
  (∀ p l, I p l → out (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l))=true) → (∀ S, maximal S → out (test S)=false) → 65≤cost.getD u.val 0 + cost.getD v.val 0 + 1)
 (high : let D : Finset (Fin 13) := {0,1,3,9}
  let I := fun p l : Fin 13 => ∃ d∈D,p=l+d
  let A := fun S : Finset (Fin 13) => fun l : Fin 13 => ∀ p∈S, ¬I p l
  let maximal := fun S : Finset (Fin 13) => (∀ p∉S, ∃ l,A S l ∧ I p l) ∧ ((∃ l, ∀ p∈S,I p l) ∨ ∃ p, ∀ l,A S l → I p l)
  let test := fun (S : Finset (Fin 13)) (i : Fin 26) => decide ((∃ p∈S,i=Fin.castAdd 13 p) ∨ ∃ l,i=Fin.natAdd 13 l ∧ A S l)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → C.size≤62 → ∀ (u v : Fin (26+C.size)), u≠v →
  let cost := C.gates.foldl (fun (w : List Nat) g => w ++ [(g.inputs.map (fun i => w.getD i 0)).sum+1]) (List.replicate 26 0)
  let out := fun x : Fin 26 → Bool => let w := C.wires (List.ofFn x); w.getD u.val false || w.getD v.val false
  (∀ p l, I p l → out (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l))=true) → 65≤cost.getD u.val 0 + cost.getD v.val 0 + 1 → ∃ S, maximal S ∧ out (test S)=true) :
 have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  intro D I A pair test wire C hm sz u v ne pos neg
  have borg (a b : Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  simp only [borg] at pos neg
  have z := unfolded C hm sz u v ne pos (fun S h => neg S h.1 h.2)
  obtain ⟨S,h,hits⟩ := high C hm sz u v ne pos z
  have fails := neg S h.1 h.2
  exact Bool.noConfusion (hits.symm.trans fails)
