import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2056_1
    (witness : let tab : List ℕ := [2863267855, 3435921648, 4042264320, 4278251520, 286326801, 84214018, 858980384, 1431633924, 16715776, 252641792, 3350592, 5586952, 1016832, 50530432, 287278097, 56051848, 1600061956, 1602167364, 1061093920, 1065304616, 87499074, 301928465, 536810001, 1442779140, 1476335748, 2004287524, 2004845604, 926351650, 939462946]
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 18 ∧ ∀ k : Fin 32, circuitFun 29 D (fun i => (tab.getD i.val 0).testBit k.val) = decide (k.val < 16))
    (certify : let tab : List ℕ := [2863267855, 3435921648, 4042264320, 4278251520, 286326801, 84214018, 858980384, 1431633924, 16715776, 252641792, 3350592, 5586952, 1016832, 50530432, 287278097, 56051848, 1600061956, 1602167364, 1061093920, 1065304616, 87499074, 301928465, 536810001, 1442779140, 1476335748, 2004287524, 2004845604, 926351650, 939462946]
    let gm : List ℕ := [1, 2, 4, 32, 8192, 16384, 32768, 65536, 131072, 1048576, 2097152, 4194304, 16777216, 33554432, 16785408, 37748736, 1114112, 3211264, 1081344, 5275648, 2113536, 139264, 1187840, 196608, 33751040, 98304, 16875520, 49152, 180224]
    ∀ D : Circuit, Monotone2 D → (∀ k : Fin 32, circuitFun 29 D (fun i => (tab.getD i.val 0).testBit k.val) = decide (k.val < 16)) → ∀ x : Fin 26 → Bool,
      circuitFun 29 D (fun i : Fin 29 => decide (∃ j : Fin 26, (gm.getD i.val 0).testBit j.val = true ∧ x j = true)) = decide (∃ p l : Fin 13, p ∈ ([0,1,2,5] : List (Fin 13)) ∧ (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true))
    (assemble : let gm : List ℕ := [1, 2, 4, 32, 8192, 16384, 32768, 65536, 131072, 1048576, 2097152, 4194304, 16777216, 33554432, 16785408, 37748736, 1114112, 3211264, 1081344, 5275648, 2113536, 139264, 1187840, 196608, 33751040, 98304, 16875520, 49152, 180224]
    ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size+45 ∧
      ∀ x : Fin 26 → Bool, circuitFun 26 C x = (decide (∃ p l : Fin 13, p ∉ ([0,1,2,5] : List (Fin 13)) ∧ (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) || circuitFun 29 D (fun i : Fin 29 => decide (∃ j : Fin 26, (gm.getD i.val 0).testBit j.val = true ∧ x j = true))))
    : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  obtain ⟨D,md,sz,rows⟩ := witness
  obtain ⟨C,mc,sc,eq⟩ := assemble D md
  have all (x : Fin 26 → Bool) : circuitFun 26 C x = true ↔
      ∃ p l : Fin 13, (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ) ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
    rw [eq,certify D md rows,Bool.or_eq_true]
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨p,l,_,e,a,b⟩|⟨p,l,_,e,a,b⟩) <;> exact ⟨p,l,e,a,b⟩
    · rintro ⟨p,l,e,a,b⟩
      by_cases hp : p ∈ ([0,1,2,5] : List (Fin 13))
      · exact Or.inr ⟨p,l,hp,e,a,b⟩
      · exact Or.inl ⟨p,l,hp,e,a,b⟩
  refine ⟨C,mc,by omega,?_⟩
  let near := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  let inp := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then
    decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter (fun l => ∀ p ∈ s, ¬near p l)
  have pval (s t : Finset (Fin 13)) (p : Fin 13) : inp s t (Fin.castAdd 13 p) = decide (p∈s) := by
    change (if p.val < 13 then decide (Fin.ofNat 13 p.val ∈ s) else _) = _
    rw [if_pos p.isLt,show Fin.ofNat 13 p.val = p from Fin.ext (Nat.mod_eq_of_lt p.isLt)]
  have lval (s t : Finset (Fin 13)) (l : Fin 13) : inp s t (Fin.natAdd 13 l) = decide (l∈t) := by
    have ge : ¬13+l.val<13 := by omega
    change (if 13+l.val < 13 then _ else decide (Fin.ofNat 13 (13+l.val) ∈ t)) = _
    rw [if_neg ge,show Fin.ofNat 13 (13+l.val) = l from Fin.ext (by
      change (13+l.val)%13=l.val; simp [Nat.add_mod,Nat.mod_eq_of_lt l.isLt])]
  have result (s t : Finset (Fin 13)) : C.eval (List.ofFn (inp s t)) = true ↔
      ∃ p l, near p l ∧ p∈s ∧ l∈t := by
    change circuitFun 26 C (inp s t) = true ↔ _
    rw [all]
    simp only [pval,lval,decide_eq_true_eq,near]
  constructor
  · intro p l e
    exact (result _ _).2 ⟨p,l,e,Finset.mem_singleton_self _,Finset.mem_singleton_self _⟩
  · intro s _
    change C.eval (List.ofFn (inp s (off s))) = false ∧ C.eval (List.ofFn (inp (off s) s)) = false
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,e,ps,lt⟩ := (result _ _).1 h
      exact (Finset.mem_filter.mp lt).2 p ps e
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p,l,e,pt,ls⟩ := (result _ _).1 h
      apply (Finset.mem_filter.mp pt).2 l ls
      simpa [near,Nat.add_comm] using e
