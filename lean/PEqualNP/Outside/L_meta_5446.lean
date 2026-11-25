import Mathlib
import PEqualNP.Defs

/-!
Lower bound 7 for the edge function of K4 on 4 vertices (threshold two of four),
for circuits of AND, OR and NOT gates of fan-in two.

The truth-table kernel search (possible, gate_table, lastTwo, fastTwo, masked and the
reading lemmas) is adapted from the merged L_meta_139 by Lewis Watson. New here: the
search only follows canonical gate sequences (no constant or repeated wire, and two
adjacent independent gates appear in increasing order). A sequence reaching the target
with the least code is canonical, since otherwise dropping or swapping a gate gives a
smaller code.
-/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5446

def M : ℕ := 0xffff
def nt (x : ℕ) : ℕ := x ^^^ M
def ins : List ℕ := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def target : ℕ := 0xfee8

def possible (w : List ℕ) (z : ℕ) : Bool :=
  z == 0 || z == M || w.any (fun u => z == u || z == nt u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bit (k : Fin 16) (z : ℕ) := z.testBit k.val

theorem hM : ∀ k : Fin 16, M.testBit k.val = true := by decide

theorem read_bit (w : List ℕ) (i : ℕ) (k : Fin 16) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem read_wire (w : List ℕ) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem atom {ws : List ℕ} {x : ℕ} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (nt x) := by
  rcases hx with rfl | hx
  · simp [possible, nt]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

theorem pair {ws : List ℕ} {x y : ℕ} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
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

theorem gate_table (w ws : List ℕ) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨M, by simp [possible], by simp [step, GateOp.eval, bit, hM]⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨M, by simp [possible], by simp [step, GateOp.eval, bit, hM]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit, nt, hM]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit, nt, hM]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit, nt, hM]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit, nt, hM]⟩

def safe : ℕ → List ℕ → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

theorem absent {n : ℕ} {ws : List ℕ} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

def choices (ws : List ℕ) : List ℕ :=
  (0 :: M :: ws.flatMap (fun x => x :: nt x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

theorem choice_iff (ws : List ℕ) (z : ℕ) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
def lastTwo (ws : List ℕ) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target || nt z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

theorem lastTwo_safe {ws : List ℕ} (h : lastTwo ws) : safe 2 ws := by
  intro z hz v hv
  have hz' := (choice_iff ws z).2 hz
  have ht (u : ℕ) (hu : u ∈ choices ws) := (List.all_eq_true.mp h) u hu
  have hnot (u : ℕ) (hu : u ∈ choices ws) : u ≠ target ∧ nt u ≠ target ∧
      (∀ x ∈ ws, x &&& u ≠ target) ∧ (∀ x ∈ ws, x ||| u ≠ target) := by
    have H := ht u hu
    simp at H
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := H
    refine ⟨h1,h2,?_,?_⟩
    · intro x hx he
      apply h3 x hx _ he
      rw [← he, ← Nat.and_assoc, Nat.and_self]
    · intro x hx he
      apply h4 x hx _ he
      rw [← he, ← Nat.or_assoc, Nat.or_self]
  have H := hnot z hz'
  have base (x : ℕ) (hx : x ∈ ws) := hnot x ((choice_iff ws x).2 (atom (.inr hx)).1)
  have unary (x : ℕ) (hx : x ∈ z :: ws) : x ≠ target ∧ nt x ≠ target := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨H.1, H.2.1⟩
    · exact ⟨(base x hx).1, (base x hx).2.1⟩
  have binary (x y : ℕ) (hx : x ∈ z :: ws) (hy : y ∈ z :: ws) :
      x &&& y ≠ target ∧ x ||| y ≠ target := by
    rcases List.mem_cons.mp hx with hxe | hxm <;> rcases List.mem_cons.mp hy with hye | hym
    · simpa [hxe, hye] using H.1
    · simpa [hxe, Nat.and_comm, Nat.or_comm] using And.intro (H.2.2.1 y hym) (H.2.2.2 y hym)
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

def masked (ws : List ℕ) (mask want : ℕ) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == (M &&& mask) || xs.any fun x =>
    x == want || (nt x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

def fastTwo (ws : List ℕ) : Bool :=
  !(masked ws M target || masked ws M (nt target) ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (nt x &&& M) (target &&& (nt x &&& M))))

theorem masked_of_possible {ws : List ℕ} {u : ℕ} (hu : possible ws u) (m : ℕ) :
    masked ws m (u &&& m) := by
  let xs := ws.map (fun x => x &&& m)
  have mem (x : ℕ) (hx : x ∈ ws) : x &&& m ∈ xs := List.mem_map.mpr ⟨x, hx, rfl⟩
  simp only [masked, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hu
  rcases hu with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst u
  · exact .inl (.inl (by simp))
  · exact .inl (.inr rfl)
  · exact .inr ⟨_, mem x hx, .inl (.inl (.inl rfl))⟩
  · refine .inr ⟨_, mem x hx, .inl (.inl (.inr ?_))⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp [nt]
    cases x.testBit i <;> cases m.testBit i <;> cases M.testBit i <;> rfl
  · refine .inr ⟨_, mem x hx, .inl (.inr ⟨?_, _, mem y hy, ?_⟩)⟩ <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_and] <;>
      cases x.testBit i <;> cases y.testBit i <;> cases m.testBit i <;> decide
  · refine .inr ⟨_, mem x hx, .inr ⟨?_, _, mem y hy, ?_⟩⟩ <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_and, Nat.testBit_or] <;>
      cases x.testBit i <;> cases y.testBit i <;> cases m.testBit i <;> decide

theorem fast_implies_last {ws : List ℕ} (hf : fastTwo ws) : lastTwo ws := by
  simp [fastTwo] at hf
  obtain ⟨⟨hn, hc⟩, hp⟩ := hf
  apply List.all_eq_true.mpr
  intro z hz
  have hz' := (choice_iff _ _).1 hz
  simp
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro he
    have hh := masked_of_possible hz' M
    rw [he, show target &&& M = target by decide] at hh
    simp_all
  · intro he
    have hh := masked_of_possible hz' M
    have he' : z = nt target := by rw [← he]; simp [nt, Nat.xor_assoc]
    rw [he', show nt target &&& M = nt target by decide] at hh
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' x
    rw [Nat.and_comm z x, he] at hh
    have hpair := hp x hx
    simp_all
  · intro x hx ha he
    have hh := masked_of_possible hz' (nt x &&& M)
    have he' : z &&& (nt x &&& M) = target &&& (nt x &&& M) := by
      rw [← he]
      apply Nat.eq_of_testBit_eq
      intro i
      simp [nt]
      cases x.testBit i <;> cases z.testBit i <;> cases M.testBit i <;> rfl
    rw [he'] at hh
    have hpair := hp x hx
    simp_all

/-! Gate sequences. A sequence lists new wires, first gate first; the wire list of a state
lists the newest wire first. -/

def valid : List ℕ → List ℕ → Prop
  | _, [] => True
  | ws, z :: s => possible ws z ∧ valid (z :: ws) s

theorem valid_append (p : List ℕ) : ∀ (ws q : List ℕ),
    valid ws (p ++ q) ↔ valid ws p ∧ valid (p.reverse ++ ws) q := by
  induction p with
  | nil => intro ws q; simp [valid]
  | cons z p ih =>
    intro ws q
    simp only [List.cons_append, valid, ih, List.reverse_cons, List.append_assoc]
    tauto

-- every wire of the first list is a wire of the second or a constant
def Sub (a b : List ℕ) : Prop := ∀ x ∈ a, x = 0 ∨ x ∈ b

theorem rel_pair {ws : List ℕ} {x y : ℕ} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := pair hx hy

theorem possible_mono {a b : List ℕ} (hs : Sub a b) {z : ℕ} (hz : possible a z) :
    possible b z := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · simp [possible]
  · simp [possible]
  · exact (atom (hs x hx)).1
  · exact (atom (hs x hx)).2
  · exact (rel_pair (hs x hx) (hs y hy)).1
  · exact (rel_pair (hs x hx) (hs y hy)).2

theorem valid_mono (s : List ℕ) : ∀ (a b : List ℕ), Sub a b → valid a s → valid b s := by
  induction s with
  | nil => intro a b _ _; trivial
  | cons z s ih =>
    intro a b hs hv
    refine ⟨possible_mono hs hv.1, ih (z :: a) (z :: b) ?_ hv.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inr List.mem_cons_self
    · rcases hs x hx with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem target_ne : target ≠ 0 := by decide

theorem target_mono {a b q : List ℕ} (hs : Sub a b) (h : target ∈ q.reverse ++ a) :
    target ∈ q.reverse ++ b := by
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ h
  · rcases hs _ h with h' | h'
    · exact absurd h' target_ne
    · exact List.mem_append_right _ h'

theorem trace (gs : List Gate) (hg : ∀ g ∈ gs, legal g) : ∀ (w ws : List ℕ), w ⊆ ws →
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

theorem possible_lt {ws : List ℕ} (hb : ∀ x ∈ ws, x < 2 ^ 16) {z : ℕ} (hz : possible ws z) :
    z < 2 ^ 16 := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · decide
  · decide
  · exact hb x hx
  · exact Nat.xor_lt_two_pow (hb x hx) (by decide)
  · exact Nat.and_lt_two_pow _ (hb y hy)
  · exact Nat.or_lt_two_pow (hb x hx) (hb y hy)

theorem valid_lt (s : List ℕ) : ∀ ws, valid ws s → (∀ x ∈ ws, x < 2 ^ 16) →
    ∀ x ∈ s.reverse ++ ws, x < 2 ^ 16 := by
  induction s with
  | nil => intro ws _ hb; simpa using hb
  | cons z s ih =>
    intro ws hv hb
    have h1 : ∀ x ∈ z :: ws, x < 2 ^ 16 := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact possible_lt hb hv.1
      · exact hb x hx
    have := ih (z :: ws) hv.2 h1
    simpa using this

def cd (c : ℕ) (s : List ℕ) : ℕ := s.foldl (fun c z => 2 * c + (z + 1)) c

theorem cd_lt (s : List ℕ) : ∀ {c c' : ℕ}, c < c' → cd c s < cd c' s := by
  induction s with
  | nil => intro c c' h; exact h
  | cons z s ih =>
    intro c c' h
    show cd (2 * c + (z + 1)) s < cd (2 * c' + (z + 1)) s
    exact ih (by omega)

theorem cd_append (c : ℕ) (p q : List ℕ) : cd c (p ++ q) = cd (cd c p) q := by
  simp [cd, List.foldl_append]

theorem cd_cons (c : ℕ) (z : ℕ) (q : List ℕ) :
    cd c (z :: q) = cd (2 * c + (z + 1)) q := rfl

def ok (ws : List ℕ) (pv : Bool) (z : ℕ) : Bool :=
  z != 0 && !ws.contains z &&
    (!pv || decide (ws.headD 0 < z) || !possible ws.tail z)

def canon : List ℕ → Bool → List ℕ → Prop
  | _, _, [] => True
  | ws, pv, z :: s => ok ws pv z = true ∧ canon (z :: ws) true s

theorem bad_aux (s : List ℕ) : ∀ r : List ℕ, ¬ canon (r ++ ins) (!r.isEmpty) s →
    (∃ p z q, r.reverse ++ s = p ++ z :: q ∧ (z = 0 ∨ z ∈ p.reverse ++ ins)) ∨
    (∃ p y z q, r.reverse ++ s = p ++ y :: z :: q ∧ z < y ∧
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
    · by_cases h0 : z = 0 ∨ z ∈ r ++ ins
      · exact .inl ⟨r.reverse, z, s, rfl, by simpa using h0⟩
      · push Not at h0
        obtain ⟨h1, h3⟩ := h0
        cases r with
        | nil =>
          exfalso; apply hok
          simp only [ok]
          simp
          exact ⟨fun e => h1 e, by simpa using h3⟩
        | cons y r' =>
          have hne : z ≠ y := fun e => h3 (e ▸ List.mem_cons_self)
          simp [ok] at hok
          obtain ⟨hle, hpos⟩ := hok (fun e => h1 e) hne
            (fun hm => h3 (by simp [hm])) (fun hm => h3 (by simp [hm]))
          refine .inr ⟨r'.reverse, y, z, s, by simp, ?_, by simpa using hpos⟩
          omega

theorem improve (s : List ℕ) (hv : valid ins s) (ht : target ∈ s.reverse ++ ins)
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
      · exact .inr hx
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
      fun x hx => .inr (List.mem_cons_of_mem _ hx)
    have s2 : Sub (z :: y :: (p.reverse ++ ins)) (y :: z :: (p.reverse ++ ins)) := by
      intro x hx
      refine .inr ?_
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

def search : ℕ → List ℕ → Bool → Bool
  | 0, ws, _ => fastTwo ws
  | n + 1, ws, pv => !ws.contains target &&
      (choices ws).all (fun z => !ok ws pv z || search n (z :: ws) true)

theorem search_sound (n : ℕ) : ∀ ws pv, search n ws pv = true → ∀ s, valid ws s →
    canon ws pv s → s.length ≤ n + 2 → target ∉ s.reverse ++ ws := by
  induction n with
  | zero =>
    intro ws pv h s hv _ hl
    have h2 := lastTwo_safe (fast_implies_last h)
    have k0 (u : List ℕ) : possible u 0 := by simp [possible]
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

theorem lift (n : ℕ) (ws : List ℕ) (pv : Bool) (L : List ℕ)
    (h0 : ws.contains target = false)
    (hL : (choices ws).all (fun z => !ok ws pv z || L.contains z) = true)
    (hall : ∀ z ∈ L, search n (z :: ws) true = true) : search (n + 1) ws pv = true := by
  simp only [search, h0, Bool.not_false, Bool.true_and, List.all_eq_true]
  intro z hz
  have hz' := List.all_eq_true.mp hL z hz
  cases hok : ok ws pv z
  · simp
  · simp only [hok, Bool.not_true, Bool.false_or, List.contains_iff_mem] at hz' ⊢
    exact hall z hz'

theorem cons_ok {P : ℕ → Prop} {a : ℕ} {L : List ℕ} (ha : P a) (hL : ∀ z ∈ L, P z) :
    ∀ z ∈ a :: L, P z := List.forall_mem_cons.2 ⟨ha, hL⟩

theorem nil_ok {P : ℕ → Prop} : ∀ z ∈ ([] : List ℕ), P z := fun _ h => absurd h List.not_mem_nil

set_option maxRecDepth 100000 in
theorem p1 : search 3 [0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [] (by decide +kernel) (by decide +kernel)
    nil_ok

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3 : search 2 [0xffff, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4 : search 2 [0x4444, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5 : search 2 [0xdddd, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6 : search 2 [0x5050, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7 : search 2 [0xf5f5, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8 : search 2 [0x5500, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9 : search 2 [0xff55, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10 : search 2 [0x8888, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11 : search 2 [0xeeee, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12 : search 2 [0xa0a0, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13 : search 2 [0xfafa, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14 : search 2 [0xaa00, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15 : search 2 [0xffaa, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16 : search 2 [0xc0c0, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17 : search 2 [0xfcfc, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18 : search 2 [0xcc00, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19 : search 2 [0xffcc, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20 : search 2 [0xf000, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21 : search 2 [0xfff0, 0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p2 : search 3 [0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0x5555, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x4444, 0xdddd, 0x5050, 0xf5f5, 0x5500, 0xff55, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p3 (cons_ok p4 (cons_ok p5 (cons_ok p6 (cons_ok p7 (cons_ok p8 (cons_ok p9 (cons_ok p10 (cons_ok p11 (cons_ok p12 (cons_ok p13 (cons_ok p14 (cons_ok p15 (cons_ok p16 (cons_ok p17 (cons_ok p18 (cons_ok p19 (cons_ok p20 (cons_ok p21 nil_ok)))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p23 : search 2 [0xffff, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p24 : search 2 [0x7777, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25 : search 2 [0x8080, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26 : search 2 [0xf8f8, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27 : search 2 [0x8800, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28 : search 2 [0xff88, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29 : search 2 [0xeeee, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30 : search 2 [0xa0a0, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31 : search 2 [0xfafa, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p32 : search 2 [0xaa00, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p33 : search 2 [0xffaa, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p34 : search 2 [0xc0c0, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p35 : search 2 [0xfcfc, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p36 : search 2 [0xcc00, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p37 : search 2 [0xffcc, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p38 : search 2 [0xf000, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p39 : search 2 [0xfff0, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p22 : search 3 [0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x7777, 0x8080, 0xf8f8, 0x8800, 0xff88, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p23 (cons_ok p24 (cons_ok p25 (cons_ok p26 (cons_ok p27 (cons_ok p28 (cons_ok p29 (cons_ok p30 (cons_ok p31 (cons_ok p32 (cons_ok p33 (cons_ok p34 (cons_ok p35 (cons_ok p36 (cons_ok p37 (cons_ok p38 (cons_ok p39 nil_ok)))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p41 : search 2 [0xffff, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p42 : search 2 [0x1111, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p43 : search 2 [0xe0e0, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p44 : search 2 [0xfefe, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p45 : search 2 [0xee00, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p46 : search 2 [0xffee, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p47 : search 2 [0xfafa, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p48 : search 2 [0xffaa, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p49 : search 2 [0xfcfc, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p50 : search 2 [0xffcc, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p51 : search 2 [0xf000, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p52 : search 2 [0xfff0, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p40 : search 3 [0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x1111, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0xfafa, 0xffaa, 0xfcfc, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p41 (cons_ok p42 (cons_ok p43 (cons_ok p44 (cons_ok p45 (cons_ok p46 (cons_ok p47 (cons_ok p48 (cons_ok p49 (cons_ok p50 (cons_ok p51 (cons_ok p52 nil_ok))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p54 : search 2 [0xffff, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p55 : search 2 [0x5f5f, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p56 : search 2 [0x8080, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p57 : search 2 [0xecec, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p58 : search 2 [0xa000, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p59 : search 2 [0xffa0, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p60 : search 2 [0xeeee, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p61 : search 2 [0xfafa, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p62 : search 2 [0xaa00, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p63 : search 2 [0xffaa, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p64 : search 2 [0xc0c0, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p65 : search 2 [0xfcfc, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p66 : search 2 [0xcc00, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p67 : search 2 [0xffcc, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p68 : search 2 [0xf000, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p69 : search 2 [0xfff0, 0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p53 : search 3 [0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xa0a0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x5f5f, 0x8080, 0xecec, 0xa000, 0xffa0, 0xeeee, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p54 (cons_ok p55 (cons_ok p56 (cons_ok p57 (cons_ok p58 (cons_ok p59 (cons_ok p60 (cons_ok p61 (cons_ok p62 (cons_ok p63 (cons_ok p64 (cons_ok p65 (cons_ok p66 (cons_ok p67 (cons_ok p68 (cons_ok p69 nil_ok))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p71 : search 2 [0xffff, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p72 : search 2 [0x0505, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p73 : search 2 [0xc8c8, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p74 : search 2 [0xfefe, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p75 : search 2 [0xfa00, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p76 : search 2 [0xfffa, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p77 : search 2 [0xffaa, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p78 : search 2 [0xfcfc, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p79 : search 2 [0xffcc, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p80 : search 2 [0xfff0, 0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p70 : search 3 [0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xfafa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0505, 0xc8c8, 0xfefe, 0xfa00, 0xfffa, 0xffaa, 0xfcfc, 0xffcc, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p71 (cons_ok p72 (cons_ok p73 (cons_ok p74 (cons_ok p75 (cons_ok p76 (cons_ok p77 (cons_ok p78 (cons_ok p79 (cons_ok p80 nil_ok))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p82 : search 2 [0xffff, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p83 : search 2 [0x55ff, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p84 : search 2 [0x8800, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p85 : search 2 [0xeecc, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p86 : search 2 [0xa000, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p87 : search 2 [0xfaf0, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p88 : search 2 [0xeeee, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p89 : search 2 [0xfafa, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p90 : search 2 [0xffaa, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p91 : search 2 [0xc0c0, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p92 : search 2 [0xfcfc, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p93 : search 2 [0xcc00, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p94 : search 2 [0xffcc, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p95 : search 2 [0xf000, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p96 : search 2 [0xfff0, 0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p81 : search 3 [0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xaa00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x55ff, 0x8800, 0xeecc, 0xa000, 0xfaf0, 0xeeee, 0xfafa, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p82 (cons_ok p83 (cons_ok p84 (cons_ok p85 (cons_ok p86 (cons_ok p87 (cons_ok p88 (cons_ok p89 (cons_ok p90 (cons_ok p91 (cons_ok p92 (cons_ok p93 (cons_ok p94 (cons_ok p95 (cons_ok p96 nil_ok)))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p98 : search 2 [0xffff, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p99 : search 2 [0x0055, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p100 : search 2 [0xcc88, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p101 : search 2 [0xffee, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p102 : search 2 [0xf0a0, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p103 : search 2 [0xfffa, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p104 : search 2 [0xffcc, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p105 : search 2 [0xfff0, 0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p97 : search 3 [0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xffaa, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0055, 0xcc88, 0xffee, 0xf0a0, 0xfffa, 0xffcc, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p98 (cons_ok p99 (cons_ok p100 (cons_ok p101 (cons_ok p102 (cons_ok p103 (cons_ok p104 (cons_ok p105 nil_ok))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p107 : search 2 [0xffff, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p108 : search 2 [0x2222, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p109 : search 2 [0xbbbb, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p110 : search 2 [0x3030, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p111 : search 2 [0xf3f3, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p112 : search 2 [0x3300, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p113 : search 2 [0xff33, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p114 : search 2 [0x5555, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p115 : search 2 [0x8888, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p116 : search 2 [0xeeee, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p117 : search 2 [0xa0a0, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p118 : search 2 [0xfafa, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p119 : search 2 [0xaa00, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p120 : search 2 [0xffaa, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p121 : search 2 [0xc0c0, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p122 : search 2 [0xfcfc, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p123 : search 2 [0xcc00, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p124 : search 2 [0xffcc, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p125 : search 2 [0xf000, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p126 : search 2 [0xfff0, 0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p106 : search 3 [0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0x3333, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x2222, 0xbbbb, 0x3030, 0xf3f3, 0x3300, 0xff33, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p107 (cons_ok p108 (cons_ok p109 (cons_ok p110 (cons_ok p111 (cons_ok p112 (cons_ok p113 (cons_ok p114 (cons_ok p115 (cons_ok p116 (cons_ok p117 (cons_ok p118 (cons_ok p119 (cons_ok p120 (cons_ok p121 (cons_ok p122 (cons_ok p123 (cons_ok p124 (cons_ok p125 (cons_ok p126 nil_ok))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p128 : search 2 [0xffff, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p129 : search 2 [0x3f3f, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p130 : search 2 [0x8080, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p131 : search 2 [0xeaea, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p132 : search 2 [0xc000, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p133 : search 2 [0xffc0, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p134 : search 2 [0xeeee, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p135 : search 2 [0xfafa, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p136 : search 2 [0xffaa, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p137 : search 2 [0xfcfc, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p138 : search 2 [0xcc00, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p139 : search 2 [0xffcc, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p140 : search 2 [0xf000, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p141 : search 2 [0xfff0, 0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p127 : search 3 [0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xc0c0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x3f3f, 0x8080, 0xeaea, 0xc000, 0xffc0, 0xeeee, 0xfafa, 0xffaa, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p128 (cons_ok p129 (cons_ok p130 (cons_ok p131 (cons_ok p132 (cons_ok p133 (cons_ok p134 (cons_ok p135 (cons_ok p136 (cons_ok p137 (cons_ok p138 (cons_ok p139 (cons_ok p140 (cons_ok p141 nil_ok))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p143 : search 2 [0xffff, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p144 : search 2 [0x0303, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p145 : search 2 [0xa8a8, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p146 : search 2 [0xfefe, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p147 : search 2 [0xfc00, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p148 : search 2 [0xfffc, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p149 : search 2 [0xffaa, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p150 : search 2 [0xffcc, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p151 : search 2 [0xfff0, 0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p142 : search 3 [0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xfcfc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0303, 0xa8a8, 0xfefe, 0xfc00, 0xfffc, 0xffaa, 0xffcc, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p143 (cons_ok p144 (cons_ok p145 (cons_ok p146 (cons_ok p147 (cons_ok p148 (cons_ok p149 (cons_ok p150 (cons_ok p151 nil_ok)))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p153 : search 2 [0xffff, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p154 : search 2 [0x33ff, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p155 : search 2 [0x8800, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p156 : search 2 [0xeeaa, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p157 : search 2 [0xc000, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p158 : search 2 [0xfcf0, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p159 : search 2 [0xeeee, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p160 : search 2 [0xfafa, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p161 : search 2 [0xffaa, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p162 : search 2 [0xfcfc, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p163 : search 2 [0xffcc, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p164 : search 2 [0xf000, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p165 : search 2 [0xfff0, 0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p152 : search 3 [0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xcc00, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x33ff, 0x8800, 0xeeaa, 0xc000, 0xfcf0, 0xeeee, 0xfafa, 0xffaa, 0xfcfc, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p153 (cons_ok p154 (cons_ok p155 (cons_ok p156 (cons_ok p157 (cons_ok p158 (cons_ok p159 (cons_ok p160 (cons_ok p161 (cons_ok p162 (cons_ok p163 (cons_ok p164 (cons_ok p165 nil_ok)))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p167 : search 2 [0xffff, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p168 : search 2 [0x0033, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p169 : search 2 [0xaa88, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p170 : search 2 [0xffee, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p171 : search 2 [0xf0c0, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p172 : search 2 [0xfffc, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p173 : search 2 [0xfff0, 0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p166 : search 3 [0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xffcc, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0033, 0xaa88, 0xffee, 0xf0c0, 0xfffc, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p167 (cons_ok p168 (cons_ok p169 (cons_ok p170 (cons_ok p171 (cons_ok p172 (cons_ok p173 nil_ok)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p175 : search 2 [0xffff, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p176 : search 2 [0x0a0a, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p177 : search 2 [0xafaf, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p178 : search 2 [0x0c0c, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p179 : search 2 [0xcfcf, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p180 : search 2 [0x0f00, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p181 : search 2 [0xff0f, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p182 : search 2 [0x5555, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p183 : search 2 [0x8888, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p184 : search 2 [0xeeee, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p185 : search 2 [0xa0a0, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p186 : search 2 [0xfafa, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p187 : search 2 [0xaa00, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p188 : search 2 [0xffaa, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p189 : search 2 [0x3333, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p190 : search 2 [0xc0c0, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p191 : search 2 [0xfcfc, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p192 : search 2 [0xcc00, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p193 : search 2 [0xffcc, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p194 : search 2 [0xf000, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p195 : search 2 [0xfff0, 0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p174 : search 3 [0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0x0f0f, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0a0a, 0xafaf, 0x0c0c, 0xcfcf, 0x0f00, 0xff0f, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p175 (cons_ok p176 (cons_ok p177 (cons_ok p178 (cons_ok p179 (cons_ok p180 (cons_ok p181 (cons_ok p182 (cons_ok p183 (cons_ok p184 (cons_ok p185 (cons_ok p186 (cons_ok p187 (cons_ok p188 (cons_ok p189 (cons_ok p190 (cons_ok p191 (cons_ok p192 (cons_ok p193 (cons_ok p194 (cons_ok p195 nil_ok)))))))))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p197 : search 2 [0xffff, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p198 : search 2 [0x0fff, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p199 : search 2 [0xa000, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p200 : search 2 [0xfaaa, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p201 : search 2 [0xc000, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p202 : search 2 [0xfccc, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p203 : search 2 [0xfafa, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p204 : search 2 [0xffaa, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p205 : search 2 [0xfcfc, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p206 : search 2 [0xffcc, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p207 : search 2 [0xfff0, 0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p196 : search 3 [0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xf000, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x0fff, 0xa000, 0xfaaa, 0xc000, 0xfccc, 0xfafa, 0xffaa, 0xfcfc, 0xffcc, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p197 (cons_ok p198 (cons_ok p199 (cons_ok p200 (cons_ok p201 (cons_ok p202 (cons_ok p203 (cons_ok p204 (cons_ok p205 (cons_ok p206 (cons_ok p207 nil_ok)))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p209 : search 2 [0xffff, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p210 : search 2 [0x000f, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p211 : search 2 [0xaaa0, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p212 : search 2 [0xfffa, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p213 : search 2 [0xccc0, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p214 : search 2 [0xfffc, 0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p208 : search 3 [0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0xfff0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x000f, 0xaaa0, 0xfffa, 0xccc0, 0xfffc] (by decide +kernel) (by decide +kernel)
    (cons_ok p209 (cons_ok p210 (cons_ok p211 (cons_ok p212 (cons_ok p213 (cons_ok p214 nil_ok))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p216 : search 2 [0xffff, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p217 : search 2 [0x00aa, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p218 : search 2 [0xaaff, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p219 : search 2 [0x00cc, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p220 : search 2 [0xccff, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p221 : search 2 [0x00f0, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p222 : search 2 [0xf0ff, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p223 : search 2 [0x5555, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p224 : search 2 [0x8888, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p225 : search 2 [0xeeee, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p226 : search 2 [0xa0a0, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p227 : search 2 [0xfafa, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p228 : search 2 [0xaa00, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p229 : search 2 [0xffaa, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p230 : search 2 [0x3333, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p231 : search 2 [0xc0c0, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p232 : search 2 [0xfcfc, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p233 : search 2 [0xcc00, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p234 : search 2 [0xffcc, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p235 : search 2 [0x0f0f, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p236 : search 2 [0xf000, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p237 : search 2 [0xfff0, 0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p215 : search 3 [0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true = true :=
  lift 2 [0x00ff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00] true [0xffff, 0x00aa, 0xaaff, 0x00cc, 0xccff, 0x00f0, 0xf0ff, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0] (by decide +kernel) (by decide +kernel)
    (cons_ok p216 (cons_ok p217 (cons_ok p218 (cons_ok p219 (cons_ok p220 (cons_ok p221 (cons_ok p222 (cons_ok p223 (cons_ok p224 (cons_ok p225 (cons_ok p226 (cons_ok p227 (cons_ok p228 (cons_ok p229 (cons_ok p230 (cons_ok p231 (cons_ok p232 (cons_ok p233 (cons_ok p234 (cons_ok p235 (cons_ok p236 (cons_ok p237 nil_ok))))))))))))))))))))))

set_option maxRecDepth 100000 in
theorem p0 : search 4 [0xaaaa, 0xcccc, 0xf0f0, 0xff00] false = true :=
  lift 3 [0xaaaa, 0xcccc, 0xf0f0, 0xff00] false [0xffff, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0, 0x00ff] (by decide +kernel) (by decide +kernel)
    (cons_ok p1 (cons_ok p2 (cons_ok p22 (cons_ok p40 (cons_ok p53 (cons_ok p70 (cons_ok p81 (cons_ok p97 (cons_ok p106 (cons_ok p127 (cons_ok p142 (cons_ok p152 (cons_ok p166 (cons_ok p174 (cons_ok p196 (cons_ok p208 (cons_ok p215 nil_ok)))))))))))))))))

theorem top : search 4 ins false = true := p0

theorem no_seq (c : ℕ) : ∀ s : List ℕ, cd 0 s = c → valid ins s → s.length ≤ 6 →
    target ∈ s.reverse ++ ins → False := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hc hv hl ht
    by_cases hcan : canon ins false s
    · exact search_sound 4 ins false top s hv hcan hl ht
    · obtain ⟨s', hv', hl', ht', hlt⟩ := improve s hv ht hcan
      exact ih _ (hc ▸ hlt) s' rfl hv' (le_trans hl' hl) ht'

def graph (x : Fin 4 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)

def assignment (k : Fin 16) (i : Fin 4) := bit k (ins.getD i.val 0)

theorem lower (t : ℕ) (h : HasCircuitSize 4 graph t) : 7 ≤ t := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hlen : C.gates.length ≤ 6 := by change C.gates.length ≤ t at hsize; omega
  obtain ⟨s, hv, hl, hsub, hf⟩ := trace C.gates hg ins ins (fun _ h => h)
  have hk : ∀ k, ((ins ++ s).map (bit k)).getD C.output false = bit k target := by
    intro k
    rw [← hf k]
    have hi : ∀ t, List.ofFn (assignment t) = ins.map (bit t) := by decide
    have ht : ∀ t, graph (assignment t) = bit t target := by decide
    unfold step
    simpa only [Circuit.eval, Circuit.wires, hi, ht] using he (assignment k)
  have hbd : ∀ x ∈ s.reverse ++ ins, x < 2 ^ 16 := valid_lt s ins hv (by decide)
  have hval : (ins ++ s).getD C.output 0 = target := by
    have hb : (ins ++ s).getD C.output 0 < 2 ^ 16 := by
      rcases read_wire (ins ++ s) C.output with h0 | hm
      · rw [h0]; decide
      · exact hbd _ (hsub hm)
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 16
    · simpa only [read_bit, bit] using hk ⟨i, hi⟩
    · have h2 : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb h2), Nat.testBit_lt_two_pow (lt_of_lt_of_le (show target < 2 ^ 16 by decide) h2)]
  have hmem : target ∈ s.reverse ++ ins := by
    rcases read_wire (ins ++ s) C.output with h0 | hm
    · exact absurd (hval ▸ h0) target_ne
    · exact hsub (hval ▸ hm)
  exact no_seq _ s rfl hv (by omega) hmem

end PEqualNP.Outside.L_meta_5446

theorem PEqualNP.Outside.L_meta_5446 :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)) t → 7 ≤ t :=
  fun t h => PEqualNP.Outside.L_meta_5446.lower t h
