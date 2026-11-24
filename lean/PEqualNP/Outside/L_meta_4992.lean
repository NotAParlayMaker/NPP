import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4992

open PEqualNP.CircuitLowerBounds

def tr (g : Gate) : Bool × ℕ × ℕ :=
  match g.op, g.inputs with
  | GateOp.or, [] => (true, 0, 0)
  | GateOp.or, [a] => (true, a + 2, a + 2)
  | GateOp.or, a :: b :: _ => (true, a + 2, b + 2)
  | GateOp.and, [] => (false, 1, 1)
  | GateOp.and, [a] => (false, a + 2, a + 2)
  | GateOp.and, a :: b :: _ => (false, a + 2, b + 2)
  | _, _ => (true, 0, 0)

def stepS (x6 : List (BitVec 24)) (x7 : Bool × ℕ × ℕ) : List (BitVec 24) :=
  x6 ++ [if x7.1 = Bool.true then x6.getD x7.2.1 (0 : BitVec 24) ||| x6.getD x7.2.2 (0 : BitVec 24)
    else x6.getD x7.2.1 (0 : BitVec 24) &&& x6.getD x7.2.2 (0 : BitVec 24)]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc {α : Type} (w : List α) (a d : α) (k : ℕ) :
    (w ++ [a]).getD k d = if k < w.length then w.getD k d else if k = w.length then a else d := by
  by_cases h1 : k < w.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : k = w.length
    · rw [if_pos h2, h2]
      simp
    · rw [if_neg h2]
      apply List.getD_eq_default
      rw [List.length_append]
      simp
      omega

lemma ones_bit : ∀ b : Fin 24, (BitVec.allOnes 24)[(b : ℕ)]'b.isLt = true := by decide

def Inv (b : Fin 24) (S : List (BitVec 24)) (W : List Bool) : Prop :=
  S.length = W.length + 2 ∧ S.getD 0 0 = 0 ∧ S.getD 1 0 = BitVec.allOnes 24 ∧
    ∀ i, (S.getD (i + 2) 0).getLsbD b = W.getD i false

lemma val_eq (b : Fin 24) (S : List (BitVec 24)) (W : List Bool) (h : Inv b S W) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (if (tr g).1 = Bool.true then S.getD (tr g).2.1 (0 : BitVec 24) ||| S.getD (tr g).2.2 (0 : BitVec 24)
      else S.getD (tr g).2.1 (0 : BitVec 24) &&& S.getD (tr g).2.2 (0 : BitVec 24)).getLsbD b =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
  obtain ⟨_, h0, h1, hi⟩ := h
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only [List.getD_eq_getElem?_getD] at h0 h1
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨e, t⟩⟩⟩
    · have h1' : S[1]?.getD 0#24 = BitVec.allOnes 24 := h1
      simp [tr, GateOp.eval]
      rw [h1']
      exact ones_bit b
    · have ha := hi a
      simp only [List.getD_eq_getElem?_getD] at ha
      simp [tr, GateOp.eval, ← ha]
    · have ha := hi a
      have hc := hi c
      simp only [List.getD_eq_getElem?_getD] at ha hc
      simp [tr, GateOp.eval, ← ha, ← hc]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨e, t⟩⟩⟩
    · have h0' : S[0]?.getD 0#24 = 0#24 := h0
      simp [tr, GateOp.eval]
      rw [h0']
      simp
    · have ha := hi a
      simp only [List.getD_eq_getElem?_getD] at ha
      simp [tr, GateOp.eval, ← ha]
    · have ha := hi a
      have hc := hi c
      simp only [List.getD_eq_getElem?_getD] at ha hc
      simp [tr, GateOp.eval, ← ha, ← hc]
    · simp at hlen

lemma inv_step (b : Fin 24) (S : List (BitVec 24)) (W : List Bool) (h : Inv b S W) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Inv b (stepS S (tr g)) (stepW W g) := by
  have hv := val_eq b S W h g hg
  obtain ⟨hl, h0, h1, hi⟩ := h
  refine ⟨by simp [stepS, stepW, hl], ?_, ?_, ?_⟩
  · unfold stepS; rw [getD_snoc, if_pos (by omega)]; exact h0
  · unfold stepS; rw [getD_snoc, if_pos (by omega)]; exact h1
  · intro i
    unfold stepS stepW
    rw [getD_snoc, getD_snoc, hl]
    by_cases c1 : i < W.length
    · rw [if_pos (by omega), if_pos c1]; exact hi i
    · rw [if_neg (by omega), if_neg c1]
      by_cases c2 : i = W.length
      · rw [if_pos (by omega), if_pos c2]; exact hv
      · rw [if_neg (by omega), if_neg c2]; simp

lemma inv_fold (b : Fin 24) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ (S : List (BitVec 24)) (W : List Bool), Inv b S W →
      Inv b ((gs.map tr).foldl stepS S) (gs.foldl stepW W) := by
  intro gs
  induction gs with
  | nil => intro _ S W h; simpa using h
  | cons g gs ih =>
    intro hM S W h
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step b S W h g (hM g (List.mem_cons_self)))

lemma inv_init (b : Fin 24) (x2 : List (BitVec 24)) :
    Inv b ((0 : BitVec 24) :: BitVec.allOnes 24 :: x2) (x2.map fun v => v.getLsbD b) := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map]
  cases x2[i]? <;> simp

end PEqualNP.Outside.L_meta_4992

theorem PEqualNP.Outside.L_meta_4992 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (BitVec (24 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : List (Bool × ℕ × ℕ)), x4.length = x1.size ∧ ∀ (x5 : Fin (24 : ℕ)), ((List.foldl (fun (x6 : List (BitVec (24 : ℕ))) (x7 : Bool × ℕ × ℕ) => x6 ++ [if x7.1 = Bool.true then x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) ||| x6.getD x7.2.2 (0 : BitVec (24 : ℕ)) else x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) &&& x6.getD x7.2.2 (0 : BitVec (24 : ℕ))]) ((0 : BitVec (24 : ℕ)) :: BitVec.allOnes (24 : ℕ) :: x2) x4).getD (x1.output + (2 : ℕ)) (0 : BitVec (24 : ℕ))).getLsbD ↑x5 = x1.eval (List.map (fun (x6 : BitVec (24 : ℕ)) => x6.getLsbD ↑x5) x2) := by
  intro C x2 hC
  refine ⟨C.gates.map PEqualNP.Outside.L_meta_4992.tr, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  intro b
  have h := PEqualNP.Outside.L_meta_4992.inv_fold b C.gates hC _ _ (PEqualNP.Outside.L_meta_4992.inv_init b x2)
  exact h.2.2.2 C.output
