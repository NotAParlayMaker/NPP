import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5465

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity

abbrev M := BitVec 6

def base : List M := [7, 24, 32, 0, 41, 18, 4, 0]

def pool : List M := [0, 63, 7, 24, 32, 41, 18, 4]

def moves (p : List M) : List M :=
  p ++ p.flatMap (fun a => p.flatMap (fun b => [a &&& b, a ||| b]))

def clear : ℕ → List M → Bool
  | 0, p => decide (11 ∉ p)
  | n+1, p => decide (11 ∉ p) &&
      ((if n = 0 then moves p else (moves p).dedup).all (fun z => clear n (z :: p)))

set_option maxRecDepth 16000 in
theorem checked : clear 3 pool = true := by decide +kernel

theorem clear_now (n : ℕ) (p : List M) (h : clear n p = true) : (11 : M) ∉ p := by
  cases n with
  | zero => simpa [clear] using h
  | succ n => exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem clear_next {n : ℕ} {p : List M} {z : M} (h : clear (n+1) p = true)
    (hz : z ∈ moves p) : clear n (z :: p) = true := by
  have ht := (Bool.and_eq_true_iff.mp h).2
  apply List.all_eq_true.mp ht z
  split
  · exact hz
  · exact List.mem_dedup.mpr hz

def bits (k : Fin 6) (a : M) : Bool := a.getLsbD k.val

theorem topbits : ∀ k, bits k 63 = true := by decide

theorem read_bits (k : Fin 6) (l : List M) (i : ℕ) :
    (l.map (bits k)).getD i false = bits k (l.getD i 0) := by
  rw [show false = bits k 0 by simp [bits], List.getD_map]

theorem read_mem {l p : List M} (hl : ∀ x ∈ l, x ∈ p) (hz : 0 ∈ p) (i : ℕ) :
    l.getD i 0 ∈ p := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hl _ (List.getElem_mem h)
  · rwa [List.getD_eq_default _ _ (by omega)]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem single_mem {p : List M} {a : M} (h : a ∈ p) : a ∈ moves p :=
  List.mem_append_left _ h

theorem pair_mem {p : List M} {a b : M} (ha : a ∈ p) (hb : b ∈ p) :
    (a &&& b) ∈ moves p ∧ (a ||| b) ∈ moves p := by
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatMap.mpr <;>
    refine ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, ?_⟩⟩ <;> simp

theorem gate_ok (l p : List M) (hl : ∀ x ∈ l, x ∈ p) (hz : 0 ∈ p) (ht : 63 ∈ p)
    (g : Gate) (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ∃ z ∈ moves p, ∀ k : Fin 6, step (l.map (bits k)) g = (l ++ [z]).map (bits k) := by
  obtain ⟨op, js⟩ := g
  change op = .and ∨ op = .or at hop
  change js.length ≤ 2 at hlen
  have hm := read_mem hl hz
  cases js with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨63, single_mem ht, by intro k; simp [step, GateOp.eval]; exact topbits k⟩
    · exact ⟨0, single_mem hz, by intro k; simp [step, GateOp.eval, bits]⟩
  | cons i js =>
    cases js with
    | nil =>
      refine ⟨l.getD i 0, single_mem (hm i), ?_⟩
      rcases hop with rfl | rfl <;> intro k <;> simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.map_append, read_bits] <;> simp
    | cons j js =>
      cases js with
      | nil =>
        obtain ⟨ha, ho⟩ := pair_mem (hm i) (hm j)
        rcases hop with rfl | rfl
        · refine ⟨_, ha, ?_⟩
          intro k
          simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.map_append, read_bits]
          simp [bits]
        · refine ⟨_, ho, ?_⟩
          intro k
          simp only [step, GateOp.eval, List.map_cons, List.map_nil, List.map_append, read_bits]
          simp [bits]
      | cons j' js => simp at hlen

theorem exclude (gs : List Gate) (n : ℕ) (p l : List M) (o : ℕ)
    (hmon : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hlen : gs.length ≤ n) (hc : clear n p = true)
    (hl : ∀ x ∈ l, x ∈ p) (hz : 0 ∈ p) (ht : 63 ∈ p) :
    ∃ z : M, z ≠ 11 ∧ ∀ k : Fin 6,
      (gs.foldl step (l.map (bits k))).getD o false = bits k z := by
  induction gs generalizing n p l with
  | nil =>
    refine ⟨l.getD o 0, ?_, fun k => read_bits k l o⟩
    intro he
    exact clear_now n p hc (he ▸ read_mem hl hz o)
  | cons g gs ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      obtain ⟨hg, hgl⟩ := hmon g List.mem_cons_self
      obtain ⟨z, hzm, hstep⟩ := gate_ok l p hl hz ht g hg hgl
      obtain ⟨y, hy, he⟩ := ih n (z :: p) (l ++ [z])
        (fun j hj => hmon j (List.mem_cons_of_mem _ hj)) (by simpa using hlen)
        (clear_next hc hzm) (by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with h | rfl
          · exact List.mem_cons_of_mem _ (hl x h)
          · exact List.mem_cons_self)
        (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ ht)
      exact ⟨y, hy, fun k => by rw [List.foldl_cons, hstep]; exact he k⟩

def row (k : Fin 6) : Fin 4 := ![0, 0, 0, 1, 1, 2] k
def col (k : Fin 6) : Fin 4 := ![0, 1, 2, 0, 1, 0] k

theorem start_eq : ∀ k : Fin 6, oneEach (row k) (col k) = base.map (bits k) := by decide

theorem unique_mask : ∀ z : M, (∀ k : Fin 6, bits k z =
    (19 : ℕ).testBit (4 * (row k).val + (col k).val)) → z = 11 := by decide +kernel

def witness : Circuit := ⟨[⟨.or, [0,1]⟩, ⟨.and, [8,4]⟩, ⟨.and, [0,5]⟩, ⟨.or, [9,10]⟩], 11⟩

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  rintro ⟨⟨gs, o⟩, hmon, hlen, hrep⟩
  obtain ⟨z, hne, he⟩ := exclude gs 3 pool base o
    (fun g hg => ⟨by simpa using (hmon g hg).1, (hmon g hg).2⟩) hlen checked
    (by decide) (by decide) (by decide)
  apply hne (unique_mask z ?_)
  intro k
  have h := hrep (row k) (col k)
  change (gs.foldl step (oneEach (row k) (col k))).getD o false = _ at h
  rwa [start_eq, he] at h

end PEqualNP.Outside.L_meta_5465

theorem PEqualNP.Outside.L_meta_5465 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  exact ⟨PEqualNP.Outside.L_meta_5465.upper, PEqualNP.Outside.L_meta_5465.lower⟩
