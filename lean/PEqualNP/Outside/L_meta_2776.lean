import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2776

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Profile := BitVec 24

def tests : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276,
    288, 320, 385, 402]

def positives : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def input (mask : ℕ) : List Bool :=
  let x : Fin 9 → Bool := fun i => mask.testBit i.val
  List.ofFn x ++ [x 0 || x 4]

def bit (r : Fin 24) (p : Profile) : Bool := p.getLsbD r.val

def one : Profile := 16777215

def columns : List Profile :=
  [4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]

def base : List Profile := 0 :: one :: columns

def target : Profile := 3428671

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem rowFacts : ∀ r : Fin 24,
    tests.getD r.val 0 ∈ tests ∧
    columns.map (bit r) = input (tests.getD r.val 0) ∧
    bit r target = decide (tests.getD r.val 0 ∈ positives) := by
  decide

theorem bitZero (r : Fin 24) : bit r 0 = false := by
  simp [bit]

theorem bitOne (r : Fin 24) : bit r one = true := by
  have e : one = BitVec.allOnes 24 := by decide
  unfold bit
  rw [e, BitVec.getLsbD_allOnes]
  exact decide_eq_true r.isLt

theorem getDBit (r : Fin 24) (p : List Profile) (i : ℕ) :
    (p.map (bit r)).getD i false = bit r (p.getD i 0) := by
  rw [← bitZero r, List.getD_map]

def gateValue (g : Gate) (p : List Profile) : Profile :=
  match g.op, g.inputs with
  | .and, [] => one
  | .or, [] => 0
  | _, [i] => p.getD i 0
  | .and, i :: j :: _ => p.getD i 0 &&& p.getD j 0
  | .or, i :: j :: _ => p.getD i 0 ||| p.getD j 0
  | _, _ => 0

def Good (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem gateBit (g : Gate) (hg : Good g) (p : List Profile) (r : Fin 24) :
    bit r (gateValue g p) =
      g.op.eval (g.inputs.map fun i => (p.map (bit r)).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, tail⟩⟩⟩
  all_goals
    first
    | (simp only [List.length_cons] at hlen; omega)
    | (simp only [gateValue, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
        Bool.and_true, Bool.or_false, getDBit, bitZero, bitOne]
       <;> simp only [bit, BitVec.getLsbD_and, BitVec.getLsbD_or])

def run (gs : List Gate) (p : List Profile) : List Profile :=
  gs.foldl (fun ws g => ws ++ [gateValue g ws]) p

def runBool (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) w

theorem runBit (gs : List Gate) (hg : ∀ g ∈ gs, Good g) (r : Fin 24) (p : List Profile) :
    (run gs p).map (bit r) = runBool gs (p.map (bit r)) := by
  induction gs generalizing p with
  | nil => rfl
  | cons g gs ih =>
    simp only [run, runBool, List.foldl_cons]
    have e := ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)) (p ++ [gateValue g p])
    simpa only [run, runBool, List.map_append, List.map_cons, List.map_nil,
      gateBit g (hg g (by simp)) p r] using e

def Join (pool : List Profile) (x : Profile) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, x = a &&& b ∨ x = a ||| b

def Steps (p : List Profile) : Prop :=
  ∀ (i : ℕ) (hi : i < p.length), p[i] ∉ base ++ p.take i ∧
    Join (base ++ p.take i) p[i]

theorem stepsSnoc {p : List Profile} {x : Profile}
    (h : Steps p) (hn : x ∉ base ++ p) (hj : Join (base ++ p) x) : Steps (p ++ [x]) := by
  intro i hi
  by_cases hlt : i < p.length
  · rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact h i hlt
  · have ei : i = p.length := by simp at hi; omega
    subst i
    rw [List.take_append_length, List.getElem_append_right (le_refl p.length)]
    simpa using And.intro hn hj

theorem readMem {p s : List Profile} (h : ∀ x ∈ p, x ∈ s) (h0 : (0 : Profile) ∈ s) (i : ℕ) :
    p.getD i 0 ∈ s := by
  by_cases hi : i < p.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact h0

theorem newGate {g : Gate} {p s : List Profile} (hg : Good g)
    (hp : ∀ z ∈ p, z ∈ s) (h0 : (0 : Profile) ∈ s) (h1 : one ∈ s)
    (hn : gateValue g p ∉ s) : Join s (gateValue g p) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, _⟩ := hg
  change op = GateOp.and ∨ op = GateOp.or at hop
  have hread := readMem hp h0
  rcases hop with rfl | rfl <;> rcases ins with _ | ⟨i, _ | ⟨j, tail⟩⟩
  · exact False.elim (hn h1)
  · exact False.elim (hn (hread i))
  · exact ⟨_,hread i,_,hread j,Or.inl rfl⟩
  · exact False.elim (hn h0)
  · exact False.elim (hn (hread i))
  · exact ⟨_,hread i,_,hread j,Or.inr rfl⟩

theorem compress (gs : List Gate) (hg : ∀ g ∈ gs, Good g) (p s : List Profile)
    (hs : Steps s) (hp : ∀ x ∈ p, x ∈ base ++ s) :
    ∃ t : List Profile, t.length ≤ s.length + gs.length ∧ Steps t ∧
      ∀ x ∈ run gs p, x ∈ base ++ t := by
  induction gs generalizing p s with
  | nil =>
    exact ⟨s, by simp, hs, hp⟩
  | cons g gs ih =>
    let x := gateValue g p
    have ht : ∀ h ∈ gs, Good h := fun h hh => hg h (List.mem_cons_of_mem _ hh)
    by_cases hx : x ∈ base ++ s
    · have hall : ∀ z ∈ p ++ [x], z ∈ base ++ s := by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · exact hp z hz
        · rcases List.mem_singleton.1 hz with rfl
          exact hx
      obtain ⟨t, htlen, hsteps, hm⟩ := ih ht (p ++ [x]) s hs hall
      exact ⟨t, by simp only [List.length_cons]; omega, hsteps, hm⟩
    · have hj := newGate (hg g (by simp)) hp (by simp [base]) (by simp [base]) hx
      have hall : ∀ z ∈ p ++ [x], z ∈ base ++ (s ++ [x]) := by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · have hkeep : z ∈ (base ++ s) ++ [x] := List.mem_append_left [x] (hp z hz)
          simpa only [List.append_assoc] using hkeep
        · have hz' : z = x := List.mem_singleton.1 hz
          subst z
          simp
      obtain ⟨t, htlen, hsteps, hm⟩ := ih ht (p ++ [x]) (s ++ [x]) (stepsSnoc hs hx hj) hall
      exact ⟨t, by simp at htlen ⊢; omega, hsteps, hm⟩

theorem main (C : Circuit) (hm : Monotone2 C)
    (he : ∀ m ∈ tests, C.eval (input m) = decide (m ∈ positives)) :
    ∃ p : List Profile, p.length ≤ C.size ∧ Steps p ∧ target ∈ base ++ p := by
  have hg : ∀ g ∈ C.gates, Good g := by
    intro g h
    have ho := hm g h
    simpa [Good] using ho
  obtain ⟨p, hpl, hs, hw⟩ :=
    compress C.gates hg columns [] (by simp [Steps]) (by intro z hz; simp [base, hz])
  refine ⟨p, by simpa [Circuit.size] using hpl, hs, ?_⟩
  have hout : (run C.gates columns).getD C.output 0 ∈ base ++ p :=
    readMem hw (by simp [base]) C.output
  have ht : (run C.gates columns).getD C.output 0 = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 24 := ⟨i, hi⟩
    obtain ⟨hmem, hcol, htarget⟩ := rowFacts r
    change bit r ((run C.gates columns).getD C.output 0) = bit r target
    rw [← getDBit, runBit _ hg, hcol, htarget]
    exact he _ hmem
  rwa [ht] at hout

end PEqualNP.Outside.L_meta_2776



theorem PEqualNP.Outside.L_meta_2776 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       have x4 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];       ∃ (x5 : List (BitVec (24 : ℕ))), x5.length ≤ x1.size ∧ (∀ (x6 : ℕ) (x7 : x6 < x5.length), x5[x6] ∉ x4 ++ List.take x6 x5 ∧ ∃ x8 ∈ x4 ++ List.take x6 x5, ∃ x9 ∈ x4 ++ List.take x6 x5, x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧ (3428671 : BitVec (24 : ℕ)) ∈ x4 ++ x5 :=
  PEqualNP.Outside.L_meta_2776.main
