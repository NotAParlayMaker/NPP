import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- These three pairs of inputs keep the borrowed OR true while changing the target.
theorem PEqualNP.Outside.R_meta_3969_528
    (pair :
      ∀ (C : Circuit) (left right : List Gate) (g : Gate) (u v : List Bool),
        C.gates = left ++ g :: right →
        (u.length = v.length ∧ ∀ i, i ≠ 6 → u.getD i false = v.getD i false) →
        6 < v.length → v.getD 6 false = true → g.op = .or → 6 ∈ g.inputs →
        (∀ p ∈ left ++ right, 6 ∉ p.inputs) → C.output ≠ 6 →
        (C.wires u).getD (u.length + left.length) false = true →
        C.eval u = C.eval v)
    (recognizedCases :
      let input (b : Bool) (x : Fin 8 → Bool) := (([1,0,4,7,5,2,8,6,3] : List ℕ).map
        (fun k => if k = 8 then b else x (Fin.ofNat 8 k))) ++ [x 1 || b]
      let base (x : Fin 8 → Bool) := ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
      let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
      let recognized (C : Circuit) := ∃ (a b : Fin 9) (h : Gate),
        10 * min a.val b.val + max a.val b.val ∈ labels ∧
        h ∈ C.gates ∧ h.op = .or ∧ (h.inputs = [a.val,b.val] ∨ h.inputs = [b.val,a.val])
      ∀ (C : Circuit), Monotone2 C → C.size = 14 → recognized C →
        (∀ x, C.eval (input false x) = base x) →
        ∃ x, C.eval (input true x) ≠ (base x || x 0 || x 3))
    (remaining :
      let input (b : Bool) (x : Fin 8 → Bool) := (([1,0,4,7,5,2,8,6,3] : List ℕ).map
        (fun k => if k = 8 then b else x (Fin.ofNat 8 k))) ++ [x 1 || b]
      let base (x : Fin 8 → Bool) := ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
      let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
      let recognized (C : Circuit) := ∃ (a b : Fin 9) (h : Gate),
        10 * min a.val b.val + max a.val b.val ∈ labels ∧
        h ∈ C.gates ∧ h.op = .or ∧ (h.inputs = [a.val,b.val] ∨ h.inputs = [b.val,a.val])
      ∀ (C : Circuit) (left right : List Gate) (g : Gate), Monotone2 C → C.size = 14 →
        C.gates = left ++ g :: right → g.op = .or → 6 ∈ g.inputs →
        (∀ p ∈ left ++ right, 6 ∉ p.inputs) → ¬ recognized C →
        (∀ x, C.eval (input false x) = base x) →
        (∀ m ∈ ([10,26,74] : List ℕ), (C.wires (input false (fun i => m.testBit i.val))).getD
          (10 + left.length) false = false) →
        ∃ x, C.eval (input true x) ≠ (base x || x 0 || x 3)) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false]) x4.gates = (0 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∃ x9 ∈ x4.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (6 : ℕ) ∈ x9.inputs) → (∀ (x10 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x10) = x3 x10) → ∃ (x11 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x11) ≠ (x3 x11 || x11 (0 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fan size no count existsReader off
  obtain ⟨g,member,op,reader⟩ := existsReader
  let input (b : Bool) (x : Fin 8 → Bool) := (([1,0,4,7,5,2,8,6,3] : List ℕ).map
        (fun k => if k = 8 then b else x (Fin.ofNat 8 k))) ++ [x 1 || b]
  let base (x : Fin 8 → Bool) := ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))

  let labels : List ℕ := [1,2,4,5,8,12,13,15,16,23,27,28,34,35,38,46,47,57,58,67,68]
  let recognized (C : Circuit) := ∃ (a b : Fin 9) (h : Gate),
    10 * min a.val b.val + max a.val b.val ∈ labels ∧
    h ∈ C.gates ∧ h.op = .or ∧ (h.inputs = [a.val,b.val] ∨ h.inputs = [b.val,a.val])
  have input_eq (b : Bool) (x : Fin 8 → Bool) : input b x = [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b] := rfl
  have base_eq : ∀ x : Fin 8 → Bool, base x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
    x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) := by
    decide +kernel
  have off_eq (x : Fin 8 → Bool) : C.eval (input false x) = base x := by
    rw [input_eq,base_eq]
    exact off x
  have ops (p : Gate) (mem : p ∈ C.gates) : p.op = .and ∨ p.op = .or := by
    have issued := (fan p mem).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at issued
    rcases issued with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have forbid := List.countP_eq_zero.mp no p mem
      rw [h] at forbid
      exact (forbid (show GateOp.not.eval [false] = true from rfl)).elim
  have mono : Monotone2 C := by
    intro p mem
    exact ⟨by simpa using ops p mem,(fan p mem).2⟩
  by_contra! on
  have exactlyOn (x : Fin 8 → Bool) : C.eval (input true x) = (base x || x 0 || x 3) := by
    rw [input_eq,base_eq]
    exact on x
  have unrecognized : ¬ recognized C := by
    intro hit
    obtain ⟨x,hx⟩ := recognizedCases C mono size hit off_eq
    exact hx (exactlyOn x)
  let read6 (p : Gate) : Bool := decide (6 ∈ p.inputs)
  have readEq (p : Gate) : (p.inputs.any fun i => decide (i = 6)) = read6 p := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,decide_eq_true_eq,read6]
    constructor
    · rintro ⟨i,mem,h⟩
      exact h ▸ mem
    · intro mem
      exact ⟨6,mem,rfl⟩
  have actual : C.gates.countP read6 ≤ 1 := by
    refine (List.countP_congr (q := read6) (l := C.gates) ?_).symm.trans_le count
    intro p mem
    have ff : p.op.eval [false,false] = false := by
      rcases ops p mem with h | h <;> rw [h] <;> rfl
    rw [ff,ite_eq_right (by decide)]
    exact Bool.eq_iff_iff.mp (readEq p)
  obtain ⟨left,right,split⟩ := List.append_of_mem member
  have unique : ∀ p ∈ left ++ right, 6 ∉ p.inputs := by
    have read : read6 g = true := decide_eq_true reader
    rw [split,List.countP_append,List.countP_cons_of_pos read] at actual
    have zero : (left ++ right).countP read6 = 0 := by rw [List.countP_append]; omega
    intro p mem uses
    exact (List.countP_eq_zero.mp zero p mem) (decide_eq_true uses)
  let step (w : List Bool) (p : Gate) := w ++ [p.op.eval (p.inputs.map fun i => w.getD i false)]
  have read_initial (s : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (s.foldl step w).getD i false = w.getD i false := by
    induction s generalizing w with
    | nil => rfl
    | cons p rest ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      simp only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
  have out : C.output ≠ 6 := by
    intro e
    let w := input false (fun _ => true)
    have keep : C.eval w = false := by
      change (C.gates.foldl step w).getD C.output false = false
      rw [e,read_initial _ _ _ (by decide)]
      rfl
    have p := off_eq (fun _ => true)
    change C.eval w = true at p
    rw [keep] at p
    contradiction
  have observations : ∀ m ∈ ([10,26,74] : List ℕ),
      let x : Fin 8 → Bool := fun i => m.testBit i.val
      (∀ i : Fin 10, i.val ≠ 6 →
        (input false x).getD i.val false = (input true x).getD i.val false) ∧
      base x = false ∧ (base x || x 0 || x 3) = true := by
    decide +kernel
  have agree (m : ℕ) (mem : m ∈ ([10,26,74] : List ℕ)) :
      (C.wires (input false (fun i => m.testBit i.val))).getD (10 + left.length) false = false := by
    let x : Fin 8 → Bool := fun i => m.testBit i.val
    obtain ⟨agreeRows,offBit,onBit⟩ := observations m mem
    have unchanged (i : ℕ) (different : i ≠ 6) :
        (input false x).getD i false = (input true x).getD i false := by
      by_cases early : i < 10
      · exact agreeRows ⟨i,early⟩ different
      · rw [List.getD_eq_default _ _ (by change 10 ≤ i; omega),
          List.getD_eq_default _ _ (by change 10 ≤ i; omega)]
    cases marked : (C.wires (input false x)).getD (10 + left.length) false
    · rfl
    · have same := pair C left right g (input false x) (input true x) split
        ⟨rfl,unchanged⟩ (by change 6 < 10; decide) rfl op reader unique out marked
      have v0 := (off_eq x).trans offBit
      have v1 := (exactlyOn x).trans onBit
      rw [v0,v1] at same
      contradiction
  obtain ⟨x,fail⟩ := remaining C left right g mono size split op reader unique unrecognized off_eq agree
  exact fail (exactlyOn x)
