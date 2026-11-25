import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5471

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Mask := BitVec 5

def inputs : List Mask := [7, 24, 0, 0, 9, 18, 4, 0]

def base : List Mask := [0, 31, 7, 24, 9, 18, 4]

def row : Fin 5 → Fin 4 := ![0,0,0,1,1]
def col : Fin 5 → Fin 4 := ![0,1,2,0,1]

def bit (i : Fin 5) (a : Mask) := a.getLsbD i.val

theorem samples : ∀ i, inputs.map (bit i) = oneEach (row i) (col i) := by decide

theorem targets : ∀ i, (22 : ℕ).testBit (4 * (row i).val + (col i).val) = bit i 14 := by decide

def moves (s : List Mask) : List Mask :=
  s ++ s.flatMap (fun a => s.flatMap (fun b => [a &&& b, a ||| b]))

def safe : ℕ → List Mask → Bool
  | 0, s => !(s.contains 14)
  | 1, s => !((moves s).contains 14)
  | k+2, s => !(s.contains 14) && (moves s).dedup.all (fun a => safe (k+1) (a :: s))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cert : safe 3 base = true := by decide +kernel

theorem old {s : List Mask} {a : Mask} (h : a ∈ s) : a ∈ moves s :=
  List.mem_append_left _ h

theorem both {s : List Mask} {a b : Mask} (ha : a ∈ s) (hb : b ∈ s) :
    a &&& b ∈ moves s ∧ a ||| b ∈ moves s := by
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatMap.mpr <;>
    refine ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, ?_⟩⟩ <;> simp

theorem absent {n : ℕ} {s : List Mask} (h : safe n s = true) : (14 : Mask) ∉ s := by
  cases n with
  | zero => simpa [safe] using h
  | succ k =>
    cases k with
    | zero =>
      have h' : (14 : Mask) ∉ moves s := by simpa [safe] using h
      exact fun m => h' (old m)
    | succ k =>
      change (!_ && _) = true at h
      simp only [Bool.and_eq_true] at h
      simpa using h.1

theorem proceed {k : ℕ} {s : List Mask} {a : Mask} (h : safe (k+1) s = true)
    (m : a ∈ moves s) : safe k (a :: s) = true := by
  cases k with
  | zero =>
    have hn : (14 : Mask) ∉ moves s := by simpa [safe] using h
    have ha : (14 : Mask) ≠ a := fun e => hn (e ▸ m)
    have hs := absent h
    simpa [safe] using And.intro ha hs
  | succ k =>
    change (!_ && _) = true at h
    simp only [Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.2 a (List.mem_dedup.mpr m)

theorem lookup (w s : List Mask) (hs : w ⊆ s) (hz : 0 ∈ s) (k : ℕ) :
    w.getD k 0 ∈ s := by
  by_cases h : k < w.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hs (List.getElem_mem h)
  · rwa [List.getD_eq_default _ _ (by omega)]

theorem readBit (w : List Mask) (i : Fin 5) (k : ℕ) :
    (w.map (bit i)).getD k false = bit i (w.getD k 0) := by
  have hz : bit i 0 = false := by simp [bit]
  rw [← hz, List.getD_map]

def advance (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]

theorem advance_mask (w s : List Mask) (hw : w ⊆ s) (hz : 0 ∈ s) (ht : 31 ∈ s)
    (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∃ a ∈ moves s, ∀ i, advance (w.map (bit i)) g = (w ++ [a]).map (bit i) := by
  rcases g with ⟨op, ks⟩
  change (op = .and ∨ op = .or) ∧ ks.length ≤ 2 at h
  rcases h with ⟨hop, hl⟩
  have H := lookup w s hw hz
  cases ks with
  | nil =>
    rcases hop with rfl | rfl
    · refine ⟨31, old ht, ?_⟩
      intro i
      have t : ∀ j : Fin 5, bit j 31 = true := by decide
      simp [advance, GateOp.eval]
      exact t i
    · refine ⟨0, old hz, ?_⟩
      intro i
      simp [advance, GateOp.eval, bit]
  | cons x xs =>
    cases xs with
    | nil =>
      refine ⟨w.getD x 0, old (H x), ?_⟩
      intro i
      rcases hop with rfl | rfl <;>
        simp only [advance, List.map_cons, List.map_nil, List.map_append, readBit] <;>
        simp [GateOp.eval]
    | cons y ys =>
      cases ys with
      | nil =>
        have hxy := both (H x) (H y)
        rcases hop with rfl | rfl
        · refine ⟨_, hxy.1, ?_⟩
          intro i
          simp only [advance, List.map_cons, List.map_nil, List.map_append, readBit]
          simp [GateOp.eval, bit]
        · refine ⟨_, hxy.2, ?_⟩
          intro i
          simp only [advance, List.map_cons, List.map_nil, List.map_append, readBit]
          simp [GateOp.eval, bit]
      | cons z zs => simp at hl

theorem run_masks (gs : List Gate) (n : ℕ) (w s : List Mask)
    (hs : safe n s = true) (hw : w ⊆ s) (hz : 0 ∈ s) (ht : 31 ∈ s)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hlen : gs.length ≤ n) (out : ℕ) :
    ∃ a : Mask, a ≠ 14 ∧ ∀ i, (gs.foldl advance (w.map (bit i))).getD out false = bit i a := by
  induction gs generalizing n w s with
  | nil =>
    refine ⟨_, fun e => absent hs (e ▸ lookup w s hw hz out), ?_⟩
    exact fun i => readBit w i out
  | cons g gs ih =>
    cases n with
    | zero => simp at hlen
    | succ k =>
      obtain ⟨a, ha, he⟩ := advance_mask w s hw hz ht g (hm g (by simp))
      have hsub : w ++ [a] ⊆ a :: s := by
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact List.mem_cons_of_mem _ (hw hb)
        · simpa using List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hb) : b = a ∨ b ∈ s)
      obtain ⟨v, hv, heval⟩ := ih k (w ++ [a]) (a :: s) (proceed hs ha) hsub
        (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ht)
        (fun j hj => hm j (by simp [hj])) (by simpa using hlen)
      refine ⟨v, hv, fun i => ?_⟩
      rw [List.foldl_cons, he]
      exact heval i

def witness : Circuit := ⟨[⟨.or,[5,6]⟩, ⟨.and,[0,8]⟩, ⟨.and,[1,4]⟩, ⟨.or,[9,10]⟩],11⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp [witness] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  rintro ⟨C, hm, hl, hr⟩
  have hsub : inputs ⊆ base := by decide
  obtain ⟨a, ha, he⟩ := run_masks C.gates 3 inputs base cert hsub (by decide) (by decide) hm hl C.output
  apply ha
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  let i : Fin 5 := ⟨j,hj⟩
  have h := he i
  rw [samples] at h
  exact h.symm.trans ((hr (row i) (col i)).trans (targets i))

end PEqualNP.Outside.L_meta_5471

theorem PEqualNP.Outside.L_meta_5471 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  exact ⟨PEqualNP.Outside.L_meta_5471.upper, PEqualNP.Outside.L_meta_5471.lower⟩
