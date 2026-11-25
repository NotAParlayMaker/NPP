import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The four lines through point 3 partition the other twelve points into triples.
-- The prefix computes their four disjunctions and detects all sixteen pencil edges.
-- The completion gets these four wires and the pencil output for the affine search.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3773_681
  (pencilGates : let rows : List (Fin 13 × List (Fin 13)) := [(0,[0,1,9]),(6,[7,8,10]),(10,[4,6,12]),(11,[2,5,11])]
    ∃ A : Circuit, Monotone2 A ∧ A.size=19 ∧ A.gates.head?=some ⟨.or,[0,1]⟩ ∧
      ∀ x y : Fin 13 → Bool, ∃ z : List Bool, z.length=19 ∧
        A.wires (List.ofFn x ++ List.ofFn y)=List.ofFn x ++ List.ofFn y ++ z ∧
        (∀ i : Fin 4, z.getD (4*i.val+1) false = ((rows.getD i.val (0,[])).2.any x)) ∧
        z.getD 18 false=rows.any (fun r => (x 3 || r.2.any x) && y r.1))
  (affine : let rows : List (Fin 13 × List (Fin 13)) := [(0,[0,1,9]),(6,[7,8,10]),(10,[4,6,12]),(11,[2,5,11])]
    let d : Finset (Fin 13) := {0,1,3,9}
    let pencil : Finset (Fin 13) := {0,6,10,11}
    ∃ D : Circuit, Monotone2 D ∧ D.size≤44 ∧ ∀ (x y : Fin 13 → Bool) (z : List Bool),
      z.length=19 → (∀ i : Fin 4, z.getD (4*i.val+1) false = ((rows.getD i.val (0,[])).2.any x)) →
      D.eval (List.ofFn x ++ List.ofFn y ++ z) = (z.getD 18 false ||
        decide (∃ p l : Fin 13, l∉pencil ∧ p+l∈d ∧ x p=true ∧ y l=true))) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false := by
  classical
  let d : Finset (Fin 13) := {0,1,3,9}
  let P : Finset (Fin 13) := {0,6,10,11}
  let rows : List (Fin 13 × List (Fin 13)) := [(0,[0,1,9]),(6,[7,8,10]),(10,[4,6,12]),(11,[2,5,11])]
  have geom (p l : Fin 13) : (l∈P ∧ p+l∈d) ↔
      ∃ r∈rows, l=r.1 ∧ (p=3 ∨ p∈r.2) := by
    revert p l
    decide +kernel
  obtain ⟨A,ma,sa,headA,hw⟩ := pencilGates
  obtain ⟨D,md,sd,compute⟩ := affine
  let C : Circuit := ⟨A.gates++D.gates,D.output⟩
  have full (x y : Fin 13 → Bool) : C.eval (List.ofFn x ++ List.ofFn y)=
      decide (∃ p l : Fin 13, p+l∈d ∧ x p=true ∧ y l=true) := by
    obtain ⟨z,len,bank,aux,top⟩ := hw x y
    have result := compute x y z len aux
    have app : C.eval (List.ofFn x ++ List.ofFn y)=D.eval (A.wires (List.ofFn x ++ List.ofFn y)) := by
      delta Circuit.eval Circuit.wires
      simp only [C,List.foldl_append]
    rw [app,bank,result,top,Bool.eq_iff_iff]
    change (rows.any (fun r => (x 3 || r.2.any x) && y r.1) ||
      decide (∃ p l : Fin 13, l∉P ∧ p+l∈d ∧ x p=true ∧ y l=true))=true ↔ _
    simp only [Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · rintro (⟨r,hr,hx,hy⟩|⟨p,l,_,edge,px,ly⟩)
      · rcases hx with three|⟨p,hp,px⟩
        · exact ⟨3,r.1,((geom 3 r.1).mpr ⟨r,hr,rfl,Or.inl rfl⟩).2,three,hy⟩
        · exact ⟨p,r.1,((geom p r.1).mpr ⟨r,hr,rfl,Or.inr hp⟩).2,px,hy⟩
      · exact ⟨p,l,edge,px,ly⟩
    · rintro ⟨p,l,edge,px,ly⟩
      by_cases hl : l∈P
      · obtain ⟨r,hr,rfl,hp⟩ := (geom p l).mp ⟨hl,edge⟩
        exact Or.inl ⟨r,hr,hp.elim (fun eq => Or.inl (eq ▸ px)) (fun mem => Or.inr ⟨p,mem,px⟩),ly⟩
      · exact Or.inr ⟨p,l,hl,edge,px,ly⟩
  have whole (v : Fin (13+13) → Bool) : C.eval (List.ofFn v)=
      decide (∃ p l : Fin 13, p+l∈d ∧ v (Fin.castAdd 13 p)=true ∧ v (Fin.natAdd 13 l)=true) := by
    rw [List.ofFn_add]
    exact full _ _
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro g mem
    exact (List.mem_append.mp mem).elim (ma g) (md g)
  · change (A.gates++D.gates).length≤63
    rw [List.length_append]
    change A.gates.length=19 at sa
    change D.gates.length≤44 at sd
    omega
  · refine ⟨⟨.or,[0,1]⟩,?_,Or.inr ⟨rfl,by simp⟩⟩
    change (A.gates++D.gates).head?=some _
    cases eq : A.gates with
    | nil => simp [eq] at headA
    | cons g gs => simpa [eq] using headA
  · intro p l inc
    rw [whole,decide_eq_true_eq]
    exact ⟨p,l,inc,decide_eq_true (Or.inl rfl),decide_eq_true (Or.inr rfl)⟩
  · intro S _
    constructor
    · rw [whole,decide_eq_false_iff_not]
      simp only [Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
      rintro ⟨p,l,edge,sp,free⟩
      exact free p sp edge
    · rw [whole,decide_eq_false_iff_not]
      simp only [Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq]
      rintro ⟨p,l,edge,free,sl⟩
      exact free l sl edge
