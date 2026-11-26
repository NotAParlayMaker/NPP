import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17912
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Input := Fin 26 → Bool
def val (C : Circuit) (x : Input) (i : ℕ) := (C.wires (List.ofFn x)).getD i false

def Builds (f : Input → Bool) (k : ℕ) := ∀ C : Circuit, Monotone2 C →
  ∃ (D : Circuit) (r : ℕ), Monotone2 D ∧ D.size = C.size + k ∧ r < 26 + D.size ∧
    (0 < k → 26 + C.size ≤ r) ∧
    (∀ x j, j < 26 + C.size → val D x j = val C x j) ∧ ∀ x, val D x r = f x

def advance (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl advance w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, advance, Nat.add_comm, Nat.add_left_comm]

lemma input_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl advance w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl advance (advance w g)).getD i false = _
    rw [ih _ (by simp [advance]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma input (i : Fin 26) : Builds (fun x => x i) 0 := by
  intro C h
  refine ⟨C, i.val, h, by simp, by omega, by omega, fun _ _ _ => rfl, ?_⟩
  intro x
  change (C.gates.foldl advance (List.ofFn x)).getD i.val false = _
  rw [input_run _ _ _ (by simp)]
  fin_cases i <;> rfl

lemma combine {f g : Input → Bool} {k l : ℕ} (op : GateOp) (hop : op = .and ∨ op = .or)
    (hf : Builds f k) (hg : Builds g l) :
    Builds (fun x => op.eval [f x, g x]) (k+l+1) := by
  intro C hC
  obtain ⟨A,a,hA,szA,ha,_,oldA,va⟩ := hf C hC
  obtain ⟨B,b,hB,szB,hb,_,oldB,vb⟩ := hg A hA
  let gate : Gate := ⟨op,[a,b]⟩
  let D : Circuit := ⟨B.gates ++ [gate], 26+B.size⟩
  have szD : D.size = B.size+1 := by simp [D,Circuit.size]
  have wires (x : Input) : D.wires (List.ofFn x) =
      B.wires (List.ofFn x) ++ [op.eval [val B x a, val B x b]] := by
    simp [D, Circuit.wires, List.foldl_append, gate, val]
  have len (x : Input) : (B.wires (List.ofFn x)).length = 26 + B.size := by
    change (B.gates.foldl advance _).length = _
    rw [length_run, List.length_ofFn]; rfl
  have oldD (x : Input) (j : ℕ) (hj : j < 26+B.size) : val D x j = val B x j := by
    unfold val
    rw [wires, List.getD_append _ _ _ _ (by rwa [len])]
  refine ⟨D,26+B.size,?_,by omega,by omega,by omega,?_,?_⟩
  · intro t ht
    change t ∈ B.gates ++ [gate] at ht
    rcases List.mem_append.mp ht with h | h
    · exact hB t h
    · obtain rfl := List.mem_singleton.mp h
      rcases hop with rfl | rfl <;> simp [gate]
  · intro x j hj
    rw [oldD _ _ (by omega), oldB _ _ (by omega), oldA _ _ hj]
  · intro x
    change (D.wires (List.ofFn x)).getD (26+B.size) false = _
    rw [wires, ← len x, List.getD_append_right _ _ _ _ (by rfl), Nat.sub_self,
      List.getD_cons_zero, oldB x a ha, va, vb]

lemma andB {f g : Input → Bool} {k l : ℕ} (hf : Builds f k) (hg : Builds g l) :
    Builds (fun x => f x && g x) (k+l+1) := by
  simpa [GateOp.eval] using combine GateOp.and (Or.inl rfl) hf hg

lemma orB {f g : Input → Bool} {k l : ℕ} (hf : Builds f k) (hg : Builds g l) :
    Builds (fun x => f x || g x) (k+l+1) := by
  simpa [GateOp.eval] using combine GateOp.or (Or.inr rfl) hf hg

def rows : List (Fin 13 × List (Fin 13)) := [(4, [5, 9, 10, 12]), (5, [4, 8, 9, 11]), (7, [2, 6, 7, 9]), (8, [1, 5, 6, 8]), (9, [0, 4, 5, 7]), (10, [3, 4, 6, 12]), (11, [2, 3, 5, 11]), (12, [1, 2, 4, 10])]

def outside (x : Input) : Bool := rows.any fun row => x (Fin.castAdd 13 row.1) && row.2.any (fun j => x (Fin.natAdd 13 j))

lemma outside_build : Builds outside 39 := by
  have he : outside = (fun x => ((((x 4 && ((x 18 || x 22) || (x 23 || x 25))) || (x 5 && ((x 17 || x 21) || (x 22 || x 24)))) || ((x 7 && ((x 15 || x 19) || (x 20 || x 22))) || (x 8 && ((x 14 || x 18) || (x 19 || x 21))))) || (((x 9 && ((x 13 || x 17) || (x 18 || x 20))) || (x 10 && ((x 16 || x 17) || (x 19 || x 25)))) || ((x 11 && ((x 15 || x 16) || (x 18 || x 24))) || (x 12 && ((x 14 || x 15) || (x 17 || x 23))))))) := by
    funext x
    simp [outside, rows, Bool.or_assoc, Fin.castAdd, Fin.natAdd]
  rw [he]
  exact (orB (orB (orB (andB (input 4) (orB (orB (input 18) (input 22)) (orB (input 23) (input 25)))) (andB (input 5) (orB (orB (input 17) (input 21)) (orB (input 22) (input 24))))) (orB (andB (input 7) (orB (orB (input 15) (input 19)) (orB (input 20) (input 22)))) (andB (input 8) (orB (orB (input 14) (input 18)) (orB (input 19) (input 21)))))) (orB (orB (andB (input 9) (orB (orB (input 13) (input 17)) (orB (input 18) (input 20)))) (andB (input 10) (orB (orB (input 16) (input 17)) (orB (input 19) (input 25))))) (orB (andB (input 11) (orB (orB (input 15) (input 16)) (orB (input 18) (input 24)))) (andB (input 12) (orB (orB (input 14) (input 15)) (orB (input 17) (input 23)))))))

end PEqualNP.Outside.L_meta_17912
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17912

theorem PEqualNP.Outside.L_meta_17912 : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (23 : ℕ) → x3.output < (26 : ℕ) + x3.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ (62 : ℕ) ∧ x3.output < x8 ∧ ∀ (x9 x10 : Finset (Fin (13 : ℕ))), (x7.wires (x2 x9 x10)).getD x3.output Bool.false = x3.eval (x2 x9 x10) ∧ (x7.wires (x2 x9 x10)).getD x8 Bool.false = Decidable.decide (∃ x11 ∈ x9, ↑x11 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧ ∃ x12 ∈ x10, x1 x11 x12)) := by
  intro inc assignment C hm hsize hout
  obtain ⟨D,r,hD,szD,_,hr,old,value⟩ := outside_build C hm
  refine ⟨D,r,hD,by omega,by have := hr (by decide); omega,?_⟩
  intro X Y
  let x : Input := fun k => if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ X)
                           else decide (Fin.ofNat 13 k.val ∈ Y)
  refine ⟨old x C.output hout, ?_⟩
  change val D x r = _
  rw [value]
  have points (i : Fin 13) : x (Fin.castAdd 13 i) = decide (i ∈ X) := by
    fin_cases i <;> rfl
  have lines (i : Fin 13) : x (Fin.natAdd 13 i) = decide (i ∈ Y) := by
    fin_cases i <;> rfl
  have table : ∀ p l : Fin 13, (∃ row ∈ rows, row.1 = p ∧ l ∈ row.2) ↔
      (p.val ∉ [0,1,2,3,6] ∧ inc p l) := by decide +kernel
  apply Bool.eq_iff_iff.mpr
  simp only [outside, List.any_eq_true, Bool.and_eq_true, points, lines, decide_eq_true_eq]
  constructor
  · rintro ⟨row, hrow, hp, l, hl, hy⟩
    obtain ⟨hskip, hi⟩ := (table row.1 l).mp ⟨row,hrow,rfl,hl⟩
    exact ⟨row.1,hp,hskip,l,hy,hi⟩
  · rintro ⟨p,hp,hskip,l,hy,hi⟩
    obtain ⟨row,hrow,he,hl⟩ := (table p l).mpr ⟨hskip,hi⟩
    exact ⟨row,hrow,he.symm ▸ hp,l,hl,hy⟩
