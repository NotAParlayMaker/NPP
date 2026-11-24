import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4506

def wire (base stop i : Nat) : Nat :=
  if i < base then i else if i = base then stop else i - 1

def gate (base stop : Nat) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire base stop)⟩

lemma read (p t : List Bool) (stop i : Nat) (bound : p.length + t.length ≤ stop) :
    (p ++ false :: t).getD i false = (p ++ t).getD (wire p.length stop i) false := by
  by_cases lt : i < p.length
  · simp only [wire, ite_eq_left lt]
    rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ lt]
  · by_cases eq : i = p.length
    · subst i
      simp only [wire, lt_self_iff_false, ite_false, ite_true]
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
      change false = (p ++ t).getD stop false
      symm
      apply List.getD_eq_default
      simpa using bound
    · simp only [wire, ite_eq_right lt, ite_eq_right eq]
      rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨d,hd⟩ : ∃ d, i - p.length = d+1 := ⟨i-p.length-1, by omega⟩
      rw [hd]
      have h : i-1-p.length = d := by omega
      rw [h]
      rfl

lemma run (p t : List Bool) (stop : Nat) (gs : List Gate)
    (bound : p.length + t.length + gs.length ≤ stop) :
    ∃ tail : List Bool,
      (Circuit.mk gs 0).wires (p ++ false :: t) = p ++ false :: tail ∧
      (Circuit.mk (gs.map (gate p.length stop)) 0).wires (p ++ t) = p ++ tail ∧
      p.length + tail.length ≤ stop := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl,by simpa using bound⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (p ++ false :: t).getD i false)
    have he : (gate p.length stop g).op.eval ((gate p.length stop g).inputs.map
        (fun i => (p ++ t).getD i false)) = b := by
      apply congrArg g.op.eval
      simp only [gate, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun i _ => (read p t stop i (by omega)).symm)
    have nextState :=  ih (t ++ [b]) (by simp at bound ⊢; omega)
    obtain ⟨tail,h1,h2,h3⟩ := nextState
    refine ⟨tail, ?_, ?_, h3⟩
    · change (Circuit.mk gs 0).wires ((p ++ false :: t) ++ [b]) = _
      simpa only [List.append_assoc, List.cons_append] using h1
    · change (Circuit.mk _ 0).wires ((p ++ t) ++ [_]) = _
      rw [he, List.append_assoc]
      exact h2

lemma wiresLen (gs : List Gate) (input : List Bool) :
    ((Circuit.mk gs 0).wires input).length = input.length + gs.length := by
  induction gs generalizing input with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (input ++ [_])).length = _
    rw [ih]
    simp
    omega

end PEqualNP.Outside.L_meta_4506

open PEqualNP.Outside.L_meta_4506

theorem PEqualNP.Outside.L_meta_4506 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x5 : Fin (8 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x5) ++ [Bool.false]) = (x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x6 : Fin (8 : ℕ) → Bool) => x6 (0 : Fin (8 : ℕ)) && x6 (1 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (2 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (3 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (1 : Fin (8 : ℕ)) && x6 (5 : Fin (8 : ℕ)) || x6 (2 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (4 : Fin (8 : ℕ)) && x6 (6 : Fin (8 : ℕ)) || x6 (5 : Fin (8 : ℕ)) && x6 (7 : Fin (8 : ℕ)) || x6 (7 : Fin (8 : ℕ)) && x6 (4 : Fin (8 : ℕ)) || x6 (0 : Fin (8 : ℕ)) || x6 (3 : Fin (8 : ℕ))) (x1.size + x2.size) := by
  intro A B ha hb correct
  let base := 8 + A.gates.length
  let stop := base + B.gates.length
  let C : Circuit := ⟨A.gates ++ B.gates.map (gate base stop),wire base stop B.output⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact ha g h
    · obtain ⟨g',hg',rfl⟩ := List.mem_map.mp h
      obtain ⟨op,arity⟩ := hb g' hg'
      exact ⟨op,by simpa [gate] using arity⟩
  · simp [C, Circuit.size]
  · intro x
    let p := A.wires (List.ofFn x)
    have hp : p.length = base := by
      have h := wiresLen A.gates (List.ofFn x)
      simpa [p, base, Circuit.wires] using h
    obtain ⟨tail,old,new,bnd⟩ := run p [] stop B.gates (by simp [hp,stop])
    simp only [List.append_nil] at new
    rw [hp] at new
    simp only [C, Circuit.eval, Circuit.wires, List.foldl_append]
    change ((Circuit.mk (B.gates.map (gate base stop)) 0).wires p).getD (wire base stop B.output) false = _
    rw [new]
    calc
      _ = (p ++ false :: tail).getD B.output false := by simpa [hp] using (read p tail stop B.output bnd).symm
      _ = B.eval (p ++ [false]) := by rw [← old]; rfl
      _ = _ := correct x
