import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9308_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gL {V l : List Bool} {i : ℕ} (h : i < V.length) :
    (V ++ l).getD i false = V.getD i false := List.getD_append _ _ _ _ h

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; simp [stp]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl stp w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stp w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      simp only [List.foldl_cons]; rw [ht]; simp [stp]⟩

def chainG : ℕ → ℕ → List (ℕ × ℕ) → List Gate
  | _, _, [] => []
  | c, acc, p :: ps => ⟨GateOp.and, [p.1, p.2]⟩ :: ⟨GateOp.or, [acc, c]⟩ :: chainG (c + 2) (c + 1) ps

def fin : ℕ → ℕ → List (ℕ × ℕ) → ℕ
  | _, acc, [] => acc
  | c, _, _ :: ps => fin (c + 2) (c + 1) ps

theorem chain_len (ps : List (ℕ × ℕ)) : ∀ c acc, (chainG c acc ps).length = 2 * ps.length := by
  induction ps with
  | nil => simp [chainG]
  | cons p ps ih => intro c acc; simp [chainG, ih]; omega

theorem chain_ok (ps : List (ℕ × ℕ)) : ∀ c acc, ∀ g ∈ chainG c acc ps,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ps with
  | nil => simp [chainG]
  | cons p ps ih =>
    intro c acc g hg
    simp only [chainG, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact ih _ _ g hg

theorem chain_val (R : ℕ) (f : ℕ → Bool) (ps : List (ℕ × ℕ)) (hps : ∀ p ∈ ps, p.1 < R ∧ p.2 < R) :
    ∀ c acc (v : Bool) (V : List Bool), V.length = c → R ≤ c → (∀ i < R, V.getD i false = f i) →
      V.getD acc false = v → (∀ b, (V ++ [b]).getD acc false = v) →
      ((chainG c acc ps).foldl stp V).getD (fin c acc ps) false =
        (v || ps.any fun p => f p.1 && f p.2) := by
  induction ps with
  | nil => intro c acc v V _ _ _ h0 _; simp only [chainG, fin, List.foldl_nil, List.any_nil, Bool.or_false]; exact h0
  | cons p ps ih =>
    intro c acc v V hV hR hf h0 h1
    obtain ⟨hp1, hp2⟩ := hps p (by simp)
    simp only [chainG, fin, List.foldl_cons]
    set a := GateOp.and.eval ([p.1, p.2].map fun i => V.getD i false) with ha
    have hs1 : stp V ⟨GateOp.and, [p.1, p.2]⟩ = V ++ [a] := rfl
    rw [hs1]
    set o := GateOp.or.eval ([acc, c].map fun i => (V ++ [a]).getD i false) with ho
    have hs2 : stp (V ++ [a]) ⟨GateOp.or, [acc, c]⟩ = V ++ [a] ++ [o] := rfl
    rw [hs2]
    have hW : (V ++ [a] ++ [o]).length = c + 2 := by simp [hV]
    have hfW : ∀ i < R, (V ++ [a] ++ [o]).getD i false = f i := by
      intro i hi; rw [List.append_assoc, gL (by omega)]; exact hf i hi
    have hoW : (V ++ [a] ++ [o]).getD (c + 1) false = o := by
      simp [List.getD_eq_getElem?_getD, hV, List.getElem?_append_right]
    rw [ih (fun q hq => hps q (by simp [hq])) (c + 2) (c + 1) o _ hW (by omega) hfW hoW
      (fun b => by rw [gL (by omega)]; exact hoW)]
    have hav : a = (f p.1 && f p.2) := by
      rw [ha]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]; rw [hf _ hp1, hf _ hp2]
    have hov : o = (v || a) := by
      have hc : (V ++ [a]).getD c false = a := by
        simp [List.getD_eq_getElem?_getD, hV, List.getElem?_append_right]
      rw [ho]; simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]; rw [h1 a, hc]
    rw [hov, hav]
    simp [Bool.or_assoc]

theorem ev (C : Circuit) (x : List Bool) : C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

end PEqualNP.Outside.L_meta_9308_aux

open PEqualNP.Outside.L_meta_9308_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9308 : ∀ (x1 : ℕ) (x2 : List (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.size + (2 : ℕ) * x2.length ∧ ∀ (x6 x7 : Fin x1 → Bool), x5.eval (List.ofFn x6 ++ List.ofFn x7) = (x3.eval (List.ofFn x6 ++ List.ofFn x7) || x2.any fun (x8 : Fin x1 × Fin x1) => x6 x8.1 && x7 x8.2) := by
  intro x1 x2 x3 hm
  let ps : List (ℕ × ℕ) := x2.map fun p => (p.1.val, x1 + p.2.val)
  let B := 2 * x1 + x3.size
  let a := if x3.output < B then x3.output else B + 2
  refine ⟨⟨x3.gates ++ chainG B a ps, fin B a ps⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hm g hg
    · exact chain_ok ps B a g hg
  · simp [Circuit.size, chain_len, ps]
  · intro x6 x7
    rw [ev, ev]
    simp only [List.foldl_append]
    set x := List.ofFn x6 ++ List.ofFn x7 with hx
    have hxl : x.length = 2 * x1 := by simp [hx]; omega
    have hVl : (x3.gates.foldl stp x).length = B := by rw [fold_len, hxl]; rfl
    obtain ⟨t, ht⟩ := fold_pre x3.gates x
    have hval : ∀ b, ((x3.gates.foldl stp x) ++ [b]).getD a false = (x3.gates.foldl stp x).getD x3.output false := by
      intro b
      simp only [a]
      split_ifs with h
      · exact gL (by omega)
      · rw [List.getD_eq_default _ _ (by simp [hVl]), List.getD_eq_default _ _ (by omega)]
    have hval0 : (x3.gates.foldl stp x).getD a false = (x3.gates.foldl stp x).getD x3.output false := by
      simp only [a]
      split_ifs with h
      · rfl
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [chain_val (2 * x1) (fun i => x.getD i false) ps (by
        intro p hp; simp only [ps, List.mem_map] at hp; obtain ⟨q, _, rfl⟩ := hp; simp; omega)
      B a _ _ hVl (by omega) (by intro i hi; rw [ht, gL (by omega)]) hval0 hval]
    congr 1
    simp only [ps, List.any_map, Function.comp_def]
    congr 1
    funext q
    rw [hx, List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
