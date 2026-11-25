import Mathlib
import PEqualNP.Defs

/-!
Lower bound 6 for the edge function of a graph on 6 vertices,
for circuits of AND, OR and NOT gates of fan-in two.

The truth-table kernel search (possible, gate_table, lastTwo, fastTwo, masked and the
reading lemmas) is adapted from the merged L_meta_139 by Lewis Watson, here on BitVec 64
truth tables. The search only follows canonical gate sequences (no constant or repeated
wire, and two adjacent independent gates appear in increasing order). A sequence reaching
the target with the least code is canonical, since otherwise dropping or swapping a gate
gives a smaller code. The top level is split into one kernel check per first gate.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5489

abbrev T := BitVec 64
def ins : List T := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def target : T := (0xaaaaaaaaaaaaaaaa &&& 0xf0f0f0f0f0f0f0f0) |||
  (0xaaaaaaaaaaaaaaaa &&& 0xffff0000ffff0000) |||
  (0xaaaaaaaaaaaaaaaa &&& 0xffffffff00000000) |||
  (0xcccccccccccccccc &&& 0xf0f0f0f0f0f0f0f0) |||
  (0xcccccccccccccccc &&& 0xffff0000ffff0000) |||
  (0xcccccccccccccccc &&& 0xffffffff00000000) |||
  (0xf0f0f0f0f0f0f0f0 &&& 0xff00ff00ff00ff00)

def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bit (k : Fin 64) (z : T) := z[k.val]

theorem read_bit (w : List T) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

theorem pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

theorem absent {n : ℕ} {ws : List T} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

def choices (ws : List T) : List T :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
def lastTwo (ws : List T) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target || ~~~z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

theorem lastTwo_safe {ws : List T} (h : lastTwo ws) : safe 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff ws z).2 hz
  have ht (u : T) (hu : u ∈ choices ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : T) (hu : u ∈ choices ws) : u ≠ target ∧ ~~~u ≠ target ∧
      (∀ x ∈ ws, x &&& u ≠ target) ∧ (∀ x ∈ ws, x ||| u ≠ target) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← BitVec.and_assoc, BitVec.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← BitVec.or_assoc, BitVec.or_self]
  have H := hnot z hz'
  have base (x : T) (hx : x ∈ ws) := hnot x ((choice_iff ws x).2 (atom (.inr hx)).1)
  have unary (x : T) (hx : x ∈ z :: ws) : x ≠ target ∧ ~~~x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : T) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, BitVec.and_comm, BitVec.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
    · simpa [hye] using And.intro (H.2.2.1 x hxm) (H.2.2.2 x hxm)
    · exact ⟨(base y hym).2.2.1 x hxm, (base y hym).2.2.2 x hxm⟩
  have hv' : v ≠ target := by
    simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hv
    rcases hv with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst v
    · decide
    · decide
    · exact (unary x hx).1
    · exact (unary x hx).2
    · exact (binary x y hx hy).1
    · exact (binary x y hx hy).2
  change (v :: z :: ws).contains target = false
  suffices target ∉ v :: z :: ws by simpa using this
  intro hm
  rcases List.mem_cons.mp hm with he | hm
  · exact hv' he.symm
  · exact (unary target hm).1 rfl

def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target || masked ws (-1) (~~~target) ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : T) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr BitVec.allOnes_and)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
    cases x[i] <;> cases m[i] <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply BitVec.eq_of_getElem_eq <;> intro i hi <;> simp only [BitVec.getElem_and, BitVec.getElem_or] <;>
      cases x[i] <;> cases y[i] <;> cases m[i] <;> decide

theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' (-1)
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he] at hh
    simp_all
  · intro he
    have hh := masked_of_possible hz' (-1)
    have he' : z = ~~~target := by rw [← he, BitVec.not_not]
    rw [show z &&& (-1 : T) = z from BitVec.and_allOnes, he'] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' x
    rw [BitVec.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' (~~~x)
    have he' : z &&& ~~~x = target &&& ~~~x := by
      rw [← he]
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp
      cases x[i] <;> cases z[i] <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

/-! Gate sequences. A sequence lists new wires, first gate first; the wire list of a state
lists the newest wire first. -/

def valid : List T → List T → Prop
  | _, [] => True
  | ws, z :: s => possible ws z ∧ valid (z :: ws) s

theorem valid_append (p : List T) : ∀ (ws q : List T),
    valid ws (p ++ q) ↔ valid ws p ∧ valid (p.reverse ++ ws) q := by
  induction p with
  | nil => intro ws q; simp [valid]
  | cons z p ih =>
    intro ws q
    simp only [List.cons_append, valid, ih, List.reverse_cons, List.append_assoc]
    tauto

-- every wire of the first list is a wire of the second or a constant
def Sub (a b : List T) : Prop := ∀ x ∈ a, x = 0 ∨ x = -1 ∨ x ∈ b

theorem rel_atom {ws : List T} {x : T} (hx : x = 0 ∨ x = -1 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with h | h | h
  · exact atom (.inl h)
  · subst h
    have e : (~~~(-1) : T) = 0 := by decide
    rw [e]
    exact ⟨by simp [possible], by simp [possible]⟩
  · exact atom (.inr h)

theorem rel_pair {ws : List T} {x y : T} (hx : x = 0 ∨ x = -1 ∨ x ∈ ws)
    (hy : y = 0 ∨ y = -1 ∨ y ∈ ws) : possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  have k0 : possible ws 0 := by simp [possible]
  have k1 : possible ws (-1) := by simp [possible]
  have a1 (u : T) : (-1 : T) &&& u = u := BitVec.allOnes_and
  have o1 (u : T) : (-1 : T) ||| u = -1 := BitVec.allOnes_or
  have a1' (u : T) : u &&& (-1 : T) = u := BitVec.and_allOnes
  have o1' (u : T) : u ||| (-1 : T) = -1 := BitVec.or_allOnes
  have z0 (u : T) : (0 : T) &&& u = 0 := BitVec.zero_and
  have z1 (u : T) : (0 : T) ||| u = u := BitVec.zero_or
  have z0' (u : T) : u &&& (0 : T) = 0 := BitVec.and_zero
  have z1' (u : T) : u ||| (0 : T) = u := BitVec.or_zero
  rcases hx with rfl | rfl | hx
  · rw [z0, z1]; exact ⟨k0, (rel_atom hy).1⟩
  · rw [a1, o1]; exact ⟨(rel_atom hy).1, k1⟩
  rcases hy with rfl | rfl | hy
  · rw [z0', z1']; exact ⟨k0, (rel_atom (.inr (.inr hx))).1⟩
  · rw [a1', o1']; exact ⟨(rel_atom (.inr (.inr hx))).1, k1⟩
  · exact pair (.inr hx) (.inr hy)

theorem possible_mono {a b : List T} (hs : Sub a b) {z : T} (hz : possible a z) :
    possible b z := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · simp [possible]
  · simp [possible]
  · exact (rel_atom (hs x hx)).1
  · exact (rel_atom (hs x hx)).2
  · exact (rel_pair (hs x hx) (hs y hy)).1
  · exact (rel_pair (hs x hx) (hs y hy)).2

theorem valid_mono (s : List T) : ∀ (a b : List T), Sub a b → valid a s → valid b s := by
  induction s with
  | nil => intro a b _ _; trivial
  | cons z s ih =>
    intro a b hs hv
    refine ⟨possible_mono hs hv.1, ih (z :: a) (z :: b) ?_ hv.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inr (.inr List.mem_cons_self)
    · rcases hs x hx with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (List.mem_cons_of_mem _ h))

theorem target_ne : target ≠ 0 ∧ target ≠ -1 := by decide

theorem target_mono {a b q : List T} (hs : Sub a b) (h : target ∈ q.reverse ++ a) :
    target ∈ q.reverse ++ b := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · rcases hs _ h with h' | h' | h'
    · exact absurd h' target_ne.1
    · exact absurd h' target_ne.2
    · exact List.mem_append_right _ h'

theorem trace (gs : List Gate) (hg : ∀ g ∈ gs, legal g) : ∀ (w ws : List T), w ⊆ ws →
    ∃ s, valid ws s ∧ s.length = gs.length ∧ (w ++ s ⊆ s.reverse ++ ws) ∧
      ∀ k, gs.foldl step (w.map (bit k)) = (w ++ s).map (bit k) := by
  induction gs with
  | nil =>
    intro w ws hw
    exact ⟨[], trivial, rfl, by simpa using hw, fun k => by simp⟩
  | cons g gs ih =>
    intro w ws hw
    obtain ⟨z, hz, hstep⟩ := gate_table w ws hw g (hg g List.mem_cons_self)
    have hw' : w ++ [z] ⊆ z :: ws := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact List.mem_cons_of_mem _ (hw hx)
      · exact List.mem_cons_self
    obtain ⟨s, hv, hl, hsub, hf⟩ := ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (w ++ [z]) (z :: ws) hw'
    refine ⟨z :: s, ⟨hz, hv⟩, by simp [hl], ?_, ?_⟩
    · intro x hx
      have : x ∈ w ++ [z] ++ s := by simpa using hx
      simpa using hsub this
    · intro k
      rw [List.foldl_cons, hstep k, hf k]
      simp

def cd (c : ℕ) (s : List T) : ℕ := s.foldl (fun c z => 2 * c + (z.toNat + 1)) c

theorem cd_lt (s : List T) : ∀ {c c' : ℕ}, c < c' → cd c s < cd c' s := by
  induction s with
  | nil => intro c c' h; exact h
  | cons z s ih =>
    intro c c' h
    show cd (2 * c + (z.toNat + 1)) s < cd (2 * c' + (z.toNat + 1)) s
    exact ih (by omega)

theorem cd_append (c : ℕ) (p q : List T) : cd c (p ++ q) = cd (cd c p) q := by
  simp [cd, List.foldl_append]

theorem cd_cons (c : ℕ) (z : T) (q : List T) :
    cd c (z :: q) = cd (2 * c + (z.toNat + 1)) q := rfl

def ok (ws : List T) (pv : Bool) (z : T) : Bool :=
  z != 0 && z != -1 && !ws.contains z &&
    (!pv || decide ((ws.headD 0).toNat < z.toNat) || !possible ws.tail z)

def canon : List T → Bool → List T → Prop
  | _, _, [] => True
  | ws, pv, z :: s => ok ws pv z = true ∧ canon (z :: ws) true s

theorem bad_aux (s : List T) : ∀ r : List T, ¬ canon (r ++ ins) (!r.isEmpty) s →
    (∃ p z q, r.reverse ++ s = p ++ z :: q ∧ (z = 0 ∨ z = -1 ∨ z ∈ p.reverse ++ ins)) ∨
    (∃ p y z q, r.reverse ++ s = p ++ y :: z :: q ∧ z.toNat < y.toNat ∧
      possible (p.reverse ++ ins) z) := by
  induction s with
  | nil => intro r h; exact absurd trivial h
  | cons z s ih =>
    intro r h
    by_cases hok : ok (r ++ ins) (!r.isEmpty) z = true
    · have hc : ¬ canon ((z :: r) ++ ins) (!(z :: r).isEmpty) s := fun hc => h ⟨hok, hc⟩
      have e : (z :: r).reverse ++ s = r.reverse ++ z :: s := by simp
      rw [← e]
      exact ih (z :: r) hc
    · by_cases h0 : z = 0 ∨ z = -1 ∨ z ∈ r ++ ins
      · exact .inl ⟨r.reverse, z, s, rfl, by simpa using h0⟩
      · push Not at h0
        obtain ⟨h1, h2, h3⟩ := h0
        cases r with
        | nil =>
          exfalso; apply hok
          simp only [ok]
          simp
          exact ⟨⟨fun e => h1 e, fun e => h2 e⟩, by simpa using h3⟩
        | cons y r' =>
          have hne : z ≠ y := fun e => h3 (e ▸ List.mem_cons_self)
          simp [ok] at hok
          obtain ⟨hle, hpos⟩ := hok (fun e => h1 e) (fun e => h2 e) hne
            (fun hm => h3 (by simp [hm])) (fun hm => h3 (by simp [hm]))
          refine .inr ⟨r'.reverse, y, z, s, by simp, ?_, by simpa using hpos⟩
          have : z.toNat ≠ y.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
          omega

theorem improve (s : List T) (hv : valid ins s) (ht : target ∈ s.reverse ++ ins)
    (hc : ¬ canon ins false s) : ∃ s', valid ins s' ∧ s'.length ≤ s.length ∧
      target ∈ s'.reverse ++ ins ∧ cd 0 s' < cd 0 s := by
  have hb := bad_aux s [] (by simpa using hc)
  simp only [List.reverse_nil, List.nil_append] at hb
  rcases hb with ⟨p, z, q, rfl, hz⟩ | ⟨p, y, z, q, rfl, hlt, hpz⟩
  · rw [valid_append] at hv
    obtain ⟨hp, hzq⟩ := hv
    have hsub : Sub (z :: (p.reverse ++ ins)) (p.reverse ++ ins) := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hz
      · exact .inr (.inr hx)
    refine ⟨p ++ q, ?_, by simp, ?_, ?_⟩
    · rw [valid_append]
      exact ⟨hp, valid_mono q _ _ hsub hzq.2⟩
    · have ht' : target ∈ q.reverse ++ (z :: (p.reverse ++ ins)) := by simpa using ht
      simpa using target_mono hsub ht'
    · rw [cd_append, cd_append, cd_cons]
      exact cd_lt q (by omega)
  · rw [valid_append] at hv
    obtain ⟨hp, hy, hz, hq⟩ := hv
    have s1 : Sub (p.reverse ++ ins) (z :: (p.reverse ++ ins)) :=
      fun x hx => .inr (.inr (List.mem_cons_of_mem _ hx))
    have s2 : Sub (z :: y :: (p.reverse ++ ins)) (y :: z :: (p.reverse ++ ins)) := by
      intro x hx
      refine .inr (.inr ?_)
      simp only [List.mem_cons] at hx ⊢
      tauto
    refine ⟨p ++ z :: y :: q, ?_, by simp, ?_, ?_⟩
    · rw [valid_append]
      exact ⟨hp, hpz, possible_mono s1 hy, valid_mono q _ _ s2 hq⟩
    · have ht' : target ∈ q.reverse ++ (z :: y :: (p.reverse ++ ins)) := by simpa using ht
      have := target_mono s2 ht'
      simpa using this
    · rw [cd_append, cd_append, cd_cons, cd_cons, cd_cons, cd_cons]
      exact cd_lt q (by omega)

def search : ℕ → List T → Bool → Bool
  | 0, ws, _ => fastTwo ws
  | n + 1, ws, pv => !ws.contains target &&
      (choices ws).all (fun z => !ok ws pv z || search n (z :: ws) true)

theorem search_sound (n : ℕ) : ∀ ws pv, search n ws pv = true → ∀ s, valid ws s →
    canon ws pv s → s.length ≤ n + 2 → target ∉ s.reverse ++ ws := by
  induction n with
  | zero =>
    intro ws pv h s hv _ hl
    have h2 := lastTwo_safe (fast_implies_last h)
    have k0 (u : List T) : possible u 0 := by simp [possible]
    match s, hv, hl with
    | [], _, _ => simpa using absent h2
    | [z], hv, _ =>
      have := absent (h2 z hv.1 0 (k0 _))
      intro hm; apply this; simp at hm ⊢; tauto
    | [z, v], hv, _ =>
      have := absent (h2 z hv.1 v hv.2.1)
      intro hm; apply this; simp at hm ⊢; tauto
    | _ :: _ :: _ :: _, _, hl => simp at hl
  | succ n ih =>
    intro ws pv h s hv hc hl
    simp only [search, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨h0, hall⟩ := h
    match s, hv, hc, hl with
    | [], _, _, _ => simpa using h0
    | z :: s, hv, hc, hl =>
      have hz := hall z ((choice_iff ws z).2 hv.1)
      simp only [hc.1, Bool.not_true, Bool.false_or] at hz
      have := ih (z :: ws) true hz s hv.2 hc.2 (by simp at hl; omega)
      simpa using this


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br3 : search 2 (0x5555555555555555 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br4 : search 2 (0x8888888888888888 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br5 : search 2 (0xeeeeeeeeeeeeeeee :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br6 : search 2 (0xa0a0a0a0a0a0a0a0 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br7 : search 2 (0xfafafafafafafafa :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br8 : search 2 (0xaa00aa00aa00aa00 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br9 : search 2 (0xffaaffaaffaaffaa :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br10 : search 2 (0xaaaa0000aaaa0000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br11 : search 2 (0xffffaaaaffffaaaa :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br12 : search 2 (0xaaaaaaaa00000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br13 : search 2 (0xffffffffaaaaaaaa :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br15 : search 2 (0x3333333333333333 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br16 : search 2 (0xc0c0c0c0c0c0c0c0 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br17 : search 2 (0xfcfcfcfcfcfcfcfc :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br18 : search 2 (0xcc00cc00cc00cc00 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br19 : search 2 (0xffccffccffccffcc :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br20 : search 2 (0xcccc0000cccc0000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br21 : search 2 (0xffffccccffffcccc :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br22 : search 2 (0xcccccccc00000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br23 : search 2 (0xffffffffcccccccc :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br25 : search 2 (0x0f0f0f0f0f0f0f0f :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br26 : search 2 (0xf000f000f000f000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br27 : search 2 (0xfff0fff0fff0fff0 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br28 : search 2 (0xf0f00000f0f00000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br29 : search 2 (0xfffff0f0fffff0f0 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br30 : search 2 (0xf0f0f0f000000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br31 : search 2 (0xfffffffff0f0f0f0 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br33 : search 2 (0x00ff00ff00ff00ff :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br34 : search 2 (0xff000000ff000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br35 : search 2 (0xffffff00ffffff00 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br36 : search 2 (0xff00ff0000000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br37 : search 2 (0xffffffffff00ff00 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br39 : search 2 (0x0000ffff0000ffff :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br40 : search 2 (0xffff000000000000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br41 : search 2 (0xffffffffffff0000 :: ins) true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem br43 : search 2 (0x00000000ffffffff :: ins) true = true := by decide +kernel

theorem top_of (h : ∀ z ∈ choices ins, ok ins false z = true →
    search 2 (z :: ins) true = true) : search 3 ins false = true := by
  show (!ins.contains target && (choices ins).all
    (fun z => !ok ins false z || search 2 (z :: ins) true)) = true
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨by decide, fun z hz => ?_⟩
  by_cases hk : ok ins false z = true
  · rw [h z hz hk, Bool.or_true]
  · rw [Bool.not_eq_true] at hk
    rw [hk]
    rfl

set_option maxRecDepth 100000 in
theorem starts : choices ins = [
    0x0000000000000000,
    0xffffffffffffffff,
    0xaaaaaaaaaaaaaaaa,
    0x5555555555555555,
    0x8888888888888888,
    0xeeeeeeeeeeeeeeee,
    0xa0a0a0a0a0a0a0a0,
    0xfafafafafafafafa,
    0xaa00aa00aa00aa00,
    0xffaaffaaffaaffaa,
    0xaaaa0000aaaa0000,
    0xffffaaaaffffaaaa,
    0xaaaaaaaa00000000,
    0xffffffffaaaaaaaa,
    0xcccccccccccccccc,
    0x3333333333333333,
    0xc0c0c0c0c0c0c0c0,
    0xfcfcfcfcfcfcfcfc,
    0xcc00cc00cc00cc00,
    0xffccffccffccffcc,
    0xcccc0000cccc0000,
    0xffffccccffffcccc,
    0xcccccccc00000000,
    0xffffffffcccccccc,
    0xf0f0f0f0f0f0f0f0,
    0x0f0f0f0f0f0f0f0f,
    0xf000f000f000f000,
    0xfff0fff0fff0fff0,
    0xf0f00000f0f00000,
    0xfffff0f0fffff0f0,
    0xf0f0f0f000000000,
    0xfffffffff0f0f0f0,
    0xff00ff00ff00ff00,
    0x00ff00ff00ff00ff,
    0xff000000ff000000,
    0xffffff00ffffff00,
    0xff00ff0000000000,
    0xffffffffff00ff00,
    0xffff0000ffff0000,
    0x0000ffff0000ffff,
    0xffff000000000000,
    0xffffffffffff0000,
    0xffffffff00000000,
    0x00000000ffffffff] := by decide +kernel

set_option maxRecDepth 100000 in
theorem top : search 3 ins false = true := by
  apply top_of
  intro z hz hk
  rw [starts] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hk (by decide +kernel)
  · exact absurd hk (by decide +kernel)
  · exact absurd hk (by decide +kernel)
  · exact br3
  · exact br4
  · exact br5
  · exact br6
  · exact br7
  · exact br8
  · exact br9
  · exact br10
  · exact br11
  · exact br12
  · exact br13
  · exact absurd hk (by decide +kernel)
  · exact br15
  · exact br16
  · exact br17
  · exact br18
  · exact br19
  · exact br20
  · exact br21
  · exact br22
  · exact br23
  · exact absurd hk (by decide +kernel)
  · exact br25
  · exact br26
  · exact br27
  · exact br28
  · exact br29
  · exact br30
  · exact br31
  · exact absurd hk (by decide +kernel)
  · exact br33
  · exact br34
  · exact br35
  · exact br36
  · exact br37
  · exact absurd hk (by decide +kernel)
  · exact br39
  · exact br40
  · exact br41
  · exact absurd hk (by decide +kernel)
  · exact br43

theorem no_seq (c : ℕ) : ∀ s : List T, cd 0 s = c → valid ins s → s.length ≤ 5 →
    target ∈ s.reverse ++ ins → False := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hc hv hl ht
    by_cases hcan : canon ins false s
    · exact search_sound 3 ins false top s hv hcan hl ht
    · obtain ⟨s', hv', hl', ht', hlt⟩ := improve s hv ht hcan
      exact ih _ (hc ▸ hlt) s' rfl hv' (le_trans hl' hl) ht'

def graph (x : Fin 6 → Bool) :=
  (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)

def assignment (k : Fin 64) (i : Fin 6) := bit k (ins.getD i.val 0)

theorem lower (t : ℕ) (h : HasCircuitSize 6 graph t) : 6 ≤ t := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 5 := by change C.gates.length ≤ t at hsize; omega
  obtain ⟨s, hv, hl, hsub, hf⟩ := trace C.gates hg ins ins (fun _ h => h)
  have hk : ∀ k, ((ins ++ s).map (bit k)).getD C.output false = bit k target := by
    intro k
    rw [← hf k]
    have hi : ∀ t, List.ofFn (assignment t) = ins.map (bit t) := by decide
    have ht : ∀ t, graph (assignment t) = bit t target := by decide
    unfold step
    simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment k)
  have hval : (ins ++ s).getD C.output 0 = target := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simpa only [read_bit, bit] using hk ⟨i, hi⟩
  have hmem : target ∈ s.reverse ++ ins := by
    rcases read_wire (ins ++ s) C.output with h0 | hm
    · exact absurd (hval ▸ h0) target_ne.1
    · exact hsub (hval ▸ hm)
  exact no_seq _ s rfl hv (by omega) hmem

end PEqualNP.Outside.L_meta_5489

theorem PEqualNP.Outside.L_meta_5489 :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)) t → 6 ≤ t :=
  fun t h => PEqualNP.Outside.L_meta_5489.lower t h
