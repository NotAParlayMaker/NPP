import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4257

open PEqualNP.CircuitLowerBounds

def eI (i : ℕ) : Fin 25 := if h : i < 25 then ⟨i, h⟩ else ⟨24, by norm_num⟩

theorem eI_val (i : ℕ) : (eI i).val = if i < 25 then i else 24 := by
  unfold eI
  split_ifs <;> rfl

theorem eI_getD (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
    w.getD (eI i).val false = w.getD i false := by
  rw [eI_val]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

def enc (g : Gate) : Fin 3 × Fin 25 × Fin 25 :=
  match g.op, g.inputs with
  | GateOp.and, [] => (2, eI 24, eI 24)
  | GateOp.and, [a] => (0, eI a, eI a)
  | GateOp.and, a :: b :: _ => (0, eI a, eI b)
  | GateOp.or, [] => (0, eI 24, eI 24)
  | GateOp.or, [a] => (1, eI a, eI a)
  | GateOp.or, a :: b :: _ => (1, eI a, eI b)
  | GateOp.not, [] => (2, eI 24, eI 24)
  | GateOp.not, a :: _ => (2, eI a, eI a)
  | _, _ => (0, eI 24, eI 24)

def op3 (c : Fin 3) : GateOp :=
  if c = (0 : Fin 3) then GateOp.and else if c = (1 : Fin 3) then GateOp.or else GateOp.not

def step7 (w : List Bool) (t : Fin 3 × Fin 25 × Fin 25) : List Bool :=
  w ++ [(op3 t.1).eval [w.getD t.2.1 false, w.getD t.2.2 false]]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem enc_eval (g : Gate) (hg : Good g) (w : List Bool) (hw : w.length ≤ 24) :
    step7 w (enc g) = stepW w g := by
  obtain ⟨hop, hlen⟩ := hg
  have h24 : w.getD 24 false = false := List.getD_eq_default _ _ (by omega)
  have e24 : (eI 24).val = 24 := by rw [eI_val]; simp
  have hE : ∀ i, w[(eI i).val]?.getD false = w[i]?.getD false := by
    intro i
    have := eI_getD w hw i
    simpa [List.getD_eq_getElem?_getD] using this
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  unfold step7 stepW
  congr 2
  rcases hop with rfl | rfl | rfl <;>
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
  simp_all [enc, op3, GateOp.eval]

def cnt1 (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any
    fun x2 => x2 == 4 || x2 == 9

def cnt2 (t : Fin 3 × Fin 25 × Fin 25) : Bool :=
  [t.2.1, t.2.2].any fun x3 => (x3.val == 4 || x3.val == 9)

theorem eI_49 (a : ℕ) : ((eI a).val == 4 || (eI a).val == 9) = (a == 4 || a == 9) := by
  rw [eI_val]
  split_ifs with h
  · rfl
  · have h4 : (a == 4) = false := by simp; omega
    have h9 : (a == 9) = false := by simp; omega
    rw [h4, h9]; rfl

theorem enc_cnt (g : Gate) (hg : Good g) : cnt2 (enc g) = cnt1 g := by
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl <;>
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
  simp_all [enc, cnt1, cnt2, GateOp.eval, eI_49]

theorem fold_eq (gs : List Gate) (hgs : ∀ g ∈ gs, Good g) :
    ∀ w : List Bool, w.length + gs.length ≤ 24 →
      (gs.map enc).foldl step7 w = gs.foldl stepW w := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hw
    simp only [List.map_cons, List.foldl_cons, List.length_cons] at hw ⊢
    rw [enc_eval g (hgs g (List.mem_cons_self ..)) w (by omega)]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ (by simp [stepW]; omega)

end PEqualNP.Outside.L_meta_4257

theorem PEqualNP.Outside.L_meta_4257 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ) → Bool := fun (x2 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => [x2.2.1, x2.2.2].any fun (x3 : Fin (25 : ℕ)) => ↑x3 == (4 : ℕ) || ↑x3 == (9 : ℕ); have x3 : Fin (3 : ℕ) → PEqualNP.CircuitLowerBounds.GateOp := fun (x3 : Fin (3 : ℕ)) => if x3 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x3 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → ∃ (x7 : List (Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ))) (x8 : Fin (25 : ℕ)), x7.length = x4.size ∧ List.countP x2 x7 = List.countP x1 x4.gates ∧ ∀ (x9 : List Bool), x9.length = (10 : ℕ) → (List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => x11 ++ [(x3 x12.1).eval [x11.getD (↑x12.2.1) Bool.false, x11.getD (↑x12.2.2) Bool.false]]) x9 x7).getD (↑x8) Bool.false = x4.eval x9 := by
  intro x1 x2 x3 C hfan hsize
  have hgood : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_4257.Good g := fun g hg => hfan g hg
  refine ⟨C.gates.map PEqualNP.Outside.L_meta_4257.enc, PEqualNP.Outside.L_meta_4257.eI C.output, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_, ?_⟩
  · rw [List.countP_map]
    apply List.countP_congr
    intro g hg
    have h' : (x2 ∘ PEqualNP.Outside.L_meta_4257.enc) g = x1 g := PEqualNP.Outside.L_meta_4257.enc_cnt g (hgood g hg)
    rw [h']
  · intro x9 hx9
    have hs : C.gates.length ≤ 14 := hsize
    have e1 : (List.foldl (fun (x11 : List Bool) (x12 : Fin 3 × Fin 25 × Fin 25) => x11 ++ [(x3 x12.1).eval [x11.getD (↑x12.2.1) Bool.false, x11.getD (↑x12.2.2) Bool.false]]) x9 (C.gates.map PEqualNP.Outside.L_meta_4257.enc))
        = (C.gates.map PEqualNP.Outside.L_meta_4257.enc).foldl PEqualNP.Outside.L_meta_4257.step7 x9 := rfl
    rw [e1, PEqualNP.Outside.L_meta_4257.fold_eq C.gates hgood x9 (by omega)]
    have hl : (C.gates.foldl PEqualNP.Outside.L_meta_4257.stepW x9).length ≤ 24 := by
      have : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (gs.foldl PEqualNP.Outside.L_meta_4257.stepW w).length = w.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro w; simp
        | cons g gs ih => intro w; simp only [List.foldl_cons, ih, PEqualNP.Outside.L_meta_4257.stepW, List.length_append, List.length_cons, List.length_nil]; omega
      rw [this]; omega
    rw [PEqualNP.Outside.L_meta_4257.eI_getD _ hl]
    rfl
