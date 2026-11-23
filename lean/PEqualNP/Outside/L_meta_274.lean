import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Threshold274
private abbrev T := BitVec 16
private def ins : List T := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
private def target : T := 0xe880
private def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 16) (z : T) := z[k.val]

private theorem read_bit (w : List T) (i : ℕ) (k : Fin 16) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List T) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List T} {x : T} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List T} {x y : T} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem gate_table (w ws : List T) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
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

private def safe : ℕ → List T → Prop
  | 0, ws => ws.contains target = false
  | n + 1, ws => ∀ z, possible ws z → safe n (z :: ws)

private theorem absent {n : ℕ} {ws : List T} (h : safe n ws) : target ∉ ws := by
  induction n generalizing ws with
  | zero => simpa [safe] using h
  | succ n ih =>
    have ht := ih (h 0 (by simp [possible]))
    exact fun hm => ht (List.mem_cons_of_mem _ hm)

private theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w ws : List T) (hw : w ⊆ ws) (m : ℕ) (hm : gs.length ≤ m) (hs : safe m ws)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) : False := by
  induction gs generalizing w ws m with
  | nil =>
    have hval : w.getD out 0 = target := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | ht
    · exact (by decide : target ≠ 0) hz
    · exact absent hs (hw ht)
  | cons g gs ih =>
    cases m with
    | zero => simp at hm
    | succ m =>
      obtain ⟨z, hz, hstep⟩ := gate_table w ws hw g (hg g (by simp))
      apply ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) (z :: ws) _ m
        (by simpa using hm) (hs z hz)
      · intro k
        simpa only [List.foldl_cons, hstep] using he k
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact List.mem_cons_of_mem _ (hw hx)
        · simp

private def choices (ws : List T) : List T :=
  (0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))).eraseDups

private theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, possible, List.any_eq_true]
  grind

-- With two gates left, only an existing wire containing every true bit of
-- the target can serve as the other input to an AND. OR has the dual test.
private def lastTwo (ws : List T) : Bool :=
  let above := ws.filter (fun x => (x &&& target) == target)
  let below := ws.filter (fun x => (x ||| target) == target)
  (choices ws).all fun z => !(z == target || ~~~z == target ||
    above.any (fun x => (x &&& z) == target) ||
    below.any (fun x => (x ||| z) == target))

private theorem lastTwo_safe {ws : List T} (h : lastTwo ws) : safe 2 ws := by
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

private def masked (ws : List T) (mask want : T) : Bool :=
  let xs := ws.map (fun x => x &&& mask)
  want == 0 || want == mask || xs.any fun x =>
    x == want || (~~~x &&& mask) == want ||
    ((x &&& want) == want && xs.any (fun y => (x &&& y) == want)) ||
    ((x ||| want) == want && xs.any (fun y => (x ||| y) == want))

private def fastTwo (ws : List T) : Bool :=
  !(masked ws (-1) target || masked ws (-1) (~~~target) ||
    ws.any fun x =>
      ((x &&& target) == target && masked ws x target) ||
      ((x ||| target) == target && masked ws (~~~x) (target &&& ~~~x)))

private theorem masked_of_possible {ws : List T} {u : T} (hu : possible ws u) (m : T) :
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

private theorem fast_implies_last {ws : List T} (hf : fastTwo ws) : lastTwo ws := by
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

private def search : ℕ → List T → Bool
  | 0, ws => fastTwo ws
  | n+1, ws => (choices ws).all (fun z => search n (z :: ws))

private theorem search_safe {n : ℕ} {ws : List T} (h : search n ws) : safe (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe (fast_implies_last h)
  | succ n ih =>
    intro z hz
    exact ih ((List.all_eq_true.mp h) z ((choice_iff _ _).2 hz))

private def move (p : ℕ) (x : T) : T :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 16 => x.getLsbD (p / 16 ^ i.val % 16))).cast (by simp)

private theorem move_bit (p : ℕ) (x : T) (i : ℕ) (hi : i < 16) :
    (move p x).getLsbD i = x.getLsbD (p / 16 ^ i % 16) := by
  simp only [move, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi), List.getElem_ofFn]

private theorem move_zero (p : ℕ) : move p 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [move_bit p 0 i hi]
  simp

private theorem move_not (p : ℕ) (x : T) : move p (~~~x) = ~~~(move p x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [move_bit _ _ _ hi, BitVec.getLsbD_not, decide_eq_true hi,
    decide_eq_true (Nat.mod_lt _ (by decide : 0 < 16)), Bool.true_and]

private theorem move_and (p : ℕ) (x y : T) : move p (x &&& y) = move p x &&& move p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [move_bit _ _ _ hi, BitVec.getLsbD_and]

private theorem move_or (p : ℕ) (x y : T) : move p (x ||| y) = move p x ||| move p y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [move_bit _ _ _ hi, BitVec.getLsbD_or]

private theorem move_possible {p : ℕ} {ws vs : List T} {z : T}
    (hm : ws.map (move p) ⊆ vs) (hz : possible ws z) : possible vs (move p z) := by
  have mem (x : T) (hx : x ∈ ws) : move p x ∈ vs := hm (List.mem_map_of_mem hx)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz ⊢
  rcases hz with ((h | h) | ⟨x, hx, ((h | h) | ⟨y, hy, h | h⟩)⟩) <;> subst z
  · exact .inl (.inl (move_zero p))
  · exact .inl (.inr (by change move p (~~~0) = ~~~0; rw [move_not, move_zero]))
  · exact .inr ⟨_, mem x hx, .inl (.inl rfl)⟩
  · exact .inr ⟨_, mem x hx, .inl (.inr (move_not p x))⟩
  · exact .inr ⟨_, mem x hx, .inr ⟨_, mem y hy, .inl (move_and p x y)⟩⟩
  · exact .inr ⟨_, mem x hx, .inr ⟨_, mem y hy, .inr (move_or p x y)⟩⟩

private theorem pullSafe (p : ℕ) {n : ℕ} {ws vs : List T} (h : safe n vs)
    (hp : move p target = target) (hm : ws.map (move p) ⊆ vs) : safe n ws := by
  induction n generalizing ws vs with
  | zero =>
    have hn : target ∉ vs := by simpa [safe] using h
    suffices target ∉ ws by simpa [safe] using this
    intro ht
    exact hn (hp ▸ hm (List.mem_map_of_mem ht))
  | succ n ih =>
    intro z hz
    exact ih (h (move p z) (move_possible hm hz)) (List.cons_subset_cons _ hm)

private def assignment (k : Fin 16) (i : Fin 4) := bit k (ins.getD i.val 0)

private theorem finish (hs : safe 6 ins) (C : Circuit) (hg : FanInTwo C) (hsize : C.size ≤ 6)
    (he : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true) : False := by
  apply exclude C.gates C.output hg ins ins (fun ⦃_⦄ h => h) 6 hsize hs
  intro k
  have hi : ∀ t, List.ofFn (assignment t) = ins.map (bit t) := by decide
  have ht : ∀ t, (bit t target = true ↔ 3 ≤ (List.ofFn (assignment t)).count true) := by decide
  have hb := (he (assignment k)).trans (ht k).symm
  unfold step
  simpa only [Circuit.eval, Circuit.wires, hi] using (Bool.eq_iff_iff.mpr hb)

set_option maxHeartbeats 0 in
private theorem stage3_0 : safe 3 (ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_1 : safe 3 (0x0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_2 : safe 3 (0x0 :: 0xf :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_3 : safe 3 (0x0 :: 0xaa :: 0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_4 : safe 3 (0x0 :: 0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_5 : safe 3 (0x0 :: 0xff :: 0xf0f :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_6 : safe 3 (0x0 :: 0xff :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_7 : safe 3 (0x0 :: 0xff :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_8 : safe 3 (0x0 :: 0xff :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_9 : safe 3 (0x0 :: 0xff :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_10 : safe 3 (0x0 :: 0xff :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_11 : safe 3 (0x0 :: 0xff :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_12 : safe 3 (0x0 :: 0xfff :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_13 : safe 3 (0x0 :: 0x8080 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_14 : safe 3 (0x0 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_15 : safe 3 (0x0 :: 0x8888 :: 0xa0a0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_16 : safe 3 (0x0 :: 0x8888 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_17 : safe 3 (0x0 :: 0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_18 : safe 3 (0x0 :: 0x8888 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_19 : safe 3 (0x0 :: 0x8888 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_20 : safe 3 (0x0 :: 0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_21 : safe 3 (0x0 :: 0x8888 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_22 : safe 3 (0x0 :: 0xa8a8 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_23 : safe 3 (0x0 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_24 : safe 3 (0x0 :: 0xeeee :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_25 : safe 3 (0x0 :: 0xeeee :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_26 : safe 3 (0x0 :: 0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_27 : safe 3 (0x0 :: 0xeeee :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_28 : safe 3 (0x0 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_29 : safe 3 (0x3 :: 0xfcfc :: 0xfffc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_30 : safe 3 (0xa :: 0xf :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_31 : safe 3 (0xf :: 0xff :: 0xf0f :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_32 : safe 3 (0xf :: 0xff :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_33 : safe 3 (0xf :: 0x3333 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_34 : safe 3 (0xf :: 0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_35 : safe 3 (0xf :: 0xa0a0 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_36 : safe 3 (0xf :: 0xaaa0 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_37 : safe 3 (0xf :: 0xaaaf :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_38 : safe 3 (0xf :: 0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_39 : safe 3 (0xf :: 0xf000 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_40 : safe 3 (0xf :: 0xf0ff :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_41 : safe 3 (0xf :: 0xfafa :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_42 : safe 3 (0xf :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_43 : safe 3 (0xf :: 0xfff0 :: 0xfffa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_44 : safe 3 (0xf :: 0xfff0 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_45 : safe 3 (0x3f :: 0xc0c0 :: 0xffc0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_46 : safe 3 (0x88 :: 0xaa :: 0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_47 : safe 3 (0x88 :: 0xff :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_48 : safe 3 (0xaa :: 0xcc :: 0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_49 : safe 3 (0xaa :: 0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_50 : safe 3 (0xaa :: 0xff :: 0xf0f :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_51 : safe 3 (0xaa :: 0xff :: 0x5555 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_52 : safe 3 (0xaa :: 0xff :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_53 : safe 3 (0xaa :: 0xff :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_54 : safe 3 (0xaa :: 0xff :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_55 : safe 3 (0xaa :: 0xff :: 0xc0c0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_56 : safe 3 (0xaa :: 0xff :: 0xcc00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_57 : safe 3 (0xaa :: 0xff :: 0xccee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_58 : safe 3 (0xaa :: 0xff :: 0xccff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_59 : safe 3 (0xaa :: 0xff :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_60 : safe 3 (0xaa :: 0xff :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_61 : safe 3 (0xaa :: 0xff :: 0xff55 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_62 : safe 3 (0xaa :: 0xff :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_63 : safe 3 (0xaa :: 0xff :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_64 : safe 3 (0xaa :: 0xff :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_65 : safe 3 (0xaa :: 0x5555 :: 0xff55 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_66 : safe 3 (0xaa :: 0x55ff :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_67 : safe 3 (0xee :: 0xff :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_68 : safe 3 (0xff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_69 : safe 3 (0xff :: 0xf0f :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_70 : safe 3 (0xff :: 0xf0f :: 0xfff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_71 : safe 3 (0xff :: 0xf0f :: 0x3333 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_72 : safe 3 (0xff :: 0xf0f :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_73 : safe 3 (0xff :: 0xf0f :: 0xa0a0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_74 : safe 3 (0xff :: 0xf0f :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_75 : safe 3 (0xff :: 0xf0f :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_76 : safe 3 (0xff :: 0xf0f :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_77 : safe 3 (0xff :: 0xf0f :: 0xf0ff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_78 : safe 3 (0xff :: 0xf0f :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_79 : safe 3 (0xff :: 0xf0f :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_80 : safe 3 (0xff :: 0xf0f :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_81 : safe 3 (0xff :: 0xfff :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_82 : safe 3 (0xff :: 0x3f3f :: 0xc0c0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_83 : safe 3 (0xff :: 0x8080 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_84 : safe 3 (0xff :: 0x8800 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_85 : safe 3 (0xff :: 0x8800 :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_86 : safe 3 (0xff :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_87 : safe 3 (0xff :: 0x8888 :: 0x88ff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_88 : safe 3 (0xff :: 0x8888 :: 0xa0a0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_89 : safe 3 (0xff :: 0x8888 :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_90 : safe 3 (0xff :: 0x8888 :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_91 : safe 3 (0xff :: 0x8888 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_92 : safe 3 (0xff :: 0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_93 : safe 3 (0xff :: 0x8888 :: 0xf0ff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_94 : safe 3 (0xff :: 0x8888 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_95 : safe 3 (0xff :: 0x8888 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_96 : safe 3 (0xff :: 0x8888 :: 0xff88 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_97 : safe 3 (0xff :: 0x8888 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_98 : safe 3 (0xff :: 0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_99 : safe 3 (0xff :: 0x8888 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_100 : safe 3 (0xff :: 0x88aa :: 0xccff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_101 : safe 3 (0xff :: 0xa8a8 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_102 : safe 3 (0xff :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_103 : safe 3 (0xff :: 0xaa00 :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_104 : safe 3 (0xff :: 0xaa00 :: 0xcc00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_105 : safe 3 (0xff :: 0xaa00 :: 0xccff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_106 : safe 3 (0xff :: 0xaa00 :: 0xeecc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_107 : safe 3 (0xff :: 0xaa00 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_108 : safe 3 (0xff :: 0xaa00 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_109 : safe 3 (0xff :: 0xaa00 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_110 : safe 3 (0xff :: 0xaa00 :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_111 : safe 3 (0xff :: 0xaa00 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_112 : safe 3 (0xff :: 0xaa88 :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_113 : safe 3 (0xff :: 0xaaff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_114 : safe 3 (0xff :: 0xaaff :: 0xccff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_115 : safe 3 (0xff :: 0xaaff :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_116 : safe 3 (0xff :: 0xaaff :: 0xeeff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_117 : safe 3 (0xff :: 0xaaff :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_118 : safe 3 (0xff :: 0xaaff :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_119 : safe 3 (0xff :: 0xaaff :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_120 : safe 3 (0xff :: 0xaaff :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_121 : safe 3 (0xff :: 0xee00 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_122 : safe 3 (0xff :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_123 : safe 3 (0xff :: 0xeeee :: 0xeeff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_124 : safe 3 (0xff :: 0xeeee :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_125 : safe 3 (0xff :: 0xeeee :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_126 : safe 3 (0xff :: 0xeeee :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_127 : safe 3 (0xff :: 0xeeee :: 0xffee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_128 : safe 3 (0xff :: 0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_129 : safe 3 (0xff :: 0xeeee :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_130 : safe 3 (0xff :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_131 : safe 3 (0xff :: 0xffaa :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_132 : safe 3 (0xff :: 0xffaa :: 0xffee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_133 : safe 3 (0xff :: 0xffaa :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_134 : safe 3 (0xff :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_135 : safe 3 (0x3ff :: 0xfc00 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_136 : safe 3 (0xaaa :: 0xfff :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_137 : safe 3 (0xfff :: 0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_138 : safe 3 (0xfff :: 0xa000 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_139 : safe 3 (0xfff :: 0xa0a0 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_140 : safe 3 (0xfff :: 0xafff :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_141 : safe 3 (0xfff :: 0xeeee :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_142 : safe 3 (0xfff :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_143 : safe 3 (0xfff :: 0xf000 :: 0xfaaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_144 : safe 3 (0xfff :: 0xf000 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_145 : safe 3 (0xfff :: 0xf000 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_146 : safe 3 (0xfff :: 0xf000 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_147 : safe 3 (0x3fff :: 0xc000 :: 0xc0c0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_148 : safe 3 (0x8000 :: 0x8080 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_149 : safe 3 (0x8000 :: 0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_150 : safe 3 (0x8080 :: 0x8800 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_151 : safe 3 (0x8080 :: 0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_152 : safe 3 (0x8080 :: 0x8888 :: 0xa0a0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_153 : safe 3 (0x8080 :: 0x8888 :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_154 : safe 3 (0x8080 :: 0x8888 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_155 : safe 3 (0x8080 :: 0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_156 : safe 3 (0x8080 :: 0x8888 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_157 : safe 3 (0x8080 :: 0x8888 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_158 : safe 3 (0x8080 :: 0x8888 :: 0xff80 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_159 : safe 3 (0x8080 :: 0x8888 :: 0xff88 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_160 : safe 3 (0x8080 :: 0x8888 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_161 : safe 3 (0x8080 :: 0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_162 : safe 3 (0x8080 :: 0x8888 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_163 : safe 3 (0x8880 :: 0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_164 : safe 3 (0x8880 :: 0xaaa0 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_165 : safe 3 (0x8888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_166 : safe 3 (0x8888 :: 0xa0a0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_167 : safe 3 (0x8888 :: 0xa0a0 :: 0xa8a8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_168 : safe 3 (0x8888 :: 0xa0a0 :: 0xaa00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_169 : safe 3 (0x8888 :: 0xa0a0 :: 0xc0c0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_170 : safe 3 (0x8888 :: 0xa0a0 :: 0xcc00 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_171 : safe 3 (0x8888 :: 0xa0a0 :: 0xecec :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_172 : safe 3 (0x8888 :: 0xa0a0 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_173 : safe 3 (0x8888 :: 0xa0a0 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_174 : safe 3 (0x8888 :: 0xa0a0 :: 0xff88 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_175 : safe 3 (0x8888 :: 0xa0a0 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_176 : safe 3 (0x8888 :: 0xa0a0 :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_177 : safe 3 (0x8888 :: 0xa0a0 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_178 : safe 3 (0x8888 :: 0xa8a8 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_179 : safe 3 (0x8888 :: 0xa8a8 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_180 : safe 3 (0x8888 :: 0xaaa0 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_181 : safe 3 (0x8888 :: 0xe0e0 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_182 : safe 3 (0x8888 :: 0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_183 : safe 3 (0x8888 :: 0xeeee :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_184 : safe 3 (0x8888 :: 0xeeee :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_185 : safe 3 (0x8888 :: 0xeeee :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_186 : safe 3 (0x8888 :: 0xeeee :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_187 : safe 3 (0x8888 :: 0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_188 : safe 3 (0x8888 :: 0xeeee :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_189 : safe 3 (0x8888 :: 0xf000 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_190 : safe 3 (0x8888 :: 0xf000 :: 0xf888 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_191 : safe 3 (0x8888 :: 0xf000 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_192 : safe 3 (0x8888 :: 0xf000 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_193 : safe 3 (0x8888 :: 0xf000 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_194 : safe 3 (0x8888 :: 0xf080 :: 0xff88 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_195 : safe 3 (0x8888 :: 0xf0a0 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_196 : safe 3 (0x8888 :: 0xf8f8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_197 : safe 3 (0x8888 :: 0xf8f8 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_198 : safe 3 (0x8888 :: 0xf8f8 :: 0xff88 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_199 : safe 3 (0x8888 :: 0xf8f8 :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_200 : safe 3 (0x8888 :: 0xf8f8 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_201 : safe 3 (0x8888 :: 0xf8f8 :: 0xfff8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_202 : safe 3 (0x8888 :: 0xf8f8 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_203 : safe 3 (0x8888 :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_204 : safe 3 (0x8888 :: 0xfafa :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_205 : safe 3 (0x8888 :: 0xfafa :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_206 : safe 3 (0x8888 :: 0xfafa :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_207 : safe 3 (0x8888 :: 0xfafa :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_208 : safe 3 (0x8888 :: 0xfafa :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_209 : safe 3 (0x8888 :: 0xfafa :: 0xfffa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_210 : safe 3 (0x8888 :: 0xfafa :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_211 : safe 3 (0x8888 :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_212 : safe 3 (0x8888 :: 0xfff0 :: 0xfff8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_213 : safe 3 (0x8888 :: 0xfff0 :: 0xfffa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_214 : safe 3 (0x8888 :: 0xfff0 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_215 : safe 3 (0x8888 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_216 : safe 3 (0xa8a8 :: 0xecec :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_217 : safe 3 (0xa8a8 :: 0xeeee :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_218 : safe 3 (0xa8a8 :: 0xfc00 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_219 : safe 3 (0xa8a8 :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_220 : safe 3 (0xa8a8 :: 0xfcfc :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_221 : safe 3 (0xa8a8 :: 0xfcfc :: 0xffa8 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_222 : safe 3 (0xa8a8 :: 0xfcfc :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_223 : safe 3 (0xa8a8 :: 0xfcfc :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_224 : safe 3 (0xa8a8 :: 0xfcfc :: 0xfffc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_225 : safe 3 (0xa8a8 :: 0xfcfc :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_226 : safe 3 (0xaaa8 :: 0xfcfc :: 0xfffc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_227 : safe 3 (0xeaea :: 0xeeee :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_228 : safe 3 (0xeee0 :: 0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_229 : safe 3 (0xeeee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_230 : safe 3 (0xeeee :: 0xfafa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_231 : safe 3 (0xeeee :: 0xfafa :: 0xfcfc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_232 : safe 3 (0xeeee :: 0xfafa :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_233 : safe 3 (0xeeee :: 0xfafa :: 0xffaa :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_234 : safe 3 (0xeeee :: 0xfafa :: 0xffcc :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_235 : safe 3 (0xeeee :: 0xfafa :: 0xffee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_236 : safe 3 (0xeeee :: 0xfafa :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_237 : safe 3 (0xeeee :: 0xfefe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_238 : safe 3 (0xeeee :: 0xfefe :: 0xffee :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_239 : safe 3 (0xeeee :: 0xfefe :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_240 : safe 3 (0xeeee :: 0xfefe :: 0xfffe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_241 : safe 3 (0xeeee :: 0xfefe :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_242 : safe 3 (0xeeee :: 0xfff0 :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_243 : safe 3 (0xeeee :: 0xfff0 :: 0xfffe :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_244 : safe 3 (0xeeee :: 0xfff0 :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_245 : safe 3 (0xeeee :: 0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage3_246 : safe 3 (0xffff :: ins) := by
  exact search_safe (n := 1) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_0 : safe 4 (ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (ins) = [0x0, 0xffff, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_1 : safe 4 (0x0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: ins) = [0x0, 0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_2 : safe 4 (0x0 :: 0xff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: 0xff :: ins) = [0x0, 0xffff, 0xff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_3 : safe 4 (0x0 :: 0x8888 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: 0x8888 :: ins) = [0x0, 0xffff, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x7777, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_12 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_16 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_17 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_20 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_6 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_4 : safe 4 (0x0 :: 0xeeee :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: 0xeeee :: ins) = [0x0, 0xffff, 0xeeee, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x1111, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_22 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_22 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_16 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_20 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_26 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_9 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_5 : safe 4 (0x0 :: 0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: 0xffff :: ins) = [0x0, 0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_11 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_6 : safe 4 (0xf :: 0xfff0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xf :: 0xfff0 :: ins) = [0x0, 0xffff, 0xf, 0xfff0, 0xa, 0xaaaf, 0xc, 0xcccf, 0xf0ff, 0xff0f, 0xaaa0, 0xfffa, 0xccc0, 0xfffc, 0xf0f0, 0xff00, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_44 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_30 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_37 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_30 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_37 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_40 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_40 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_36 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_43 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_36 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_43 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_33 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_34 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_38 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_35 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_35 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_33 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_35 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_35 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_39 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_32 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_7 : safe 4 (0xaa :: 0xff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xaa :: 0xff :: ins) = [0x0, 0xffff, 0xaa, 0xff55, 0xff, 0xaaaa, 0x88, 0xccee, 0xa0, 0xf0fa, 0xffaa, 0xff00, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_64 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_61 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_46 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_57 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_46 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_57 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_62 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_54 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_48 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_58 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_48 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_58 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_51 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_52 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_59 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_52 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_59 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_53 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_55 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_60 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_56 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_63 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_56 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_63 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_8 : safe 4 (0xff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_49 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_68 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_130 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_9 : safe 4 (0xff :: 0xf0f :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xf0f :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xf, 0xfff, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xf0f, 0xf0f0, 0xa0a, 0xafaf, 0xc0c, 0xcfcf, 0xf00, 0xff0f, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_80 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_70 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_51 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_77 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_50 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_51 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_77 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_71 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_72 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_75 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_69 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_71 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_76 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_79 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_10 : safe 4 (0xff :: 0x8888 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0x8888 :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0x88, 0x88ff, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0x8888, 0x7777, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_99 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_47 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_87 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_52 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_90 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_52 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_90 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_55 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_93 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_82 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_83 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_94 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_84 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_96 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_91 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_88 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_95 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_97 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_88 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_95 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_97 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_72 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_92 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_98 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_11 : safe 4 (0xff :: 0xaa00 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xaa00 :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaaff, 0xaa, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xaa00, 0x55ff, 0xaaaa, 0x8800, 0xeecc, 0xa000, 0xfaf0, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_103 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_53 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_56 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_105 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_56 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_105 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_81 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_85 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_106 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_85 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_106 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_76 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_107 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_107 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_109 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_92 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_108 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_104 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_110 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_73 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_104 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_110 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_12 : safe 4 (0xff :: 0xaaff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xaaff :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaaff, 0xaa, 0xcc, 0xccff, 0xf0, 0xf0ff, 0x5500, 0xaaaa, 0x88cc, 0xeeff, 0xa0f0, 0xfaff, 0xaa00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_120 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_54 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_58 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_114 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_58 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_114 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7d5b391e6c4a280 stage3_65 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_100 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_116 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_100 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_116 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_103 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_77 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_90 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_115 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_90 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_115 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_118 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_93 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_117 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_105 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_119 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_113 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_74 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_105 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_119 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_13 : safe 4 (0xff :: 0xeeee :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xeeee :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xee, 0xeeff, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xeeee, 0x1111, 0xaaaa, 0xcccc, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_129 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_67 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_123 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_59 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_115 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_59 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_115 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_60 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_117 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_33 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_101 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_125 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_121 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_127 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_91 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_95 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_124 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_107 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_95 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_124 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_107 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_75 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_108 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_128 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_14 : safe 4 (0xff :: 0xffaa :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xffaa :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xffaa, 0x55, 0xaaaa, 0xcc88, 0xffee, 0xf0a0, 0xfffa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_133 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_62 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_118 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_63 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_119 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_63 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_119 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_112 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_132 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_112 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_132 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_79 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_97 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_97 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_109 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_98 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_128 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_110 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_131 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_78 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_110 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_131 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_15 : safe 4 (0xff :: 0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: 0xffff :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xaaaa, 0xcccc, 0xf0f0, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_64 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_120 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_64 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_120 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_64 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_120 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_80 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_99 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_129 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_99 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_129 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_133 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_80 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_99 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_129 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_133 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_80 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_133 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_16 : safe 4 (0xfff :: 0xf000 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xfff :: 0xf000 :: ins) = [0x0, 0xffff, 0xfff, 0xf000, 0xaaa, 0xafff, 0xccc, 0xcfff, 0xf0, 0xf00, 0xa000, 0xfaaa, 0xc000, 0xfccc, 0xf0f0, 0xff00, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_12 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_146 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_136 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_140 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_136 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_140 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_66 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_66 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_138 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_143 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_138 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_143 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_82 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_137 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_141 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_144 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_144 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_82 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_144 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_144 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_81 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_145 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_81 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_17 : safe 4 (0x8080 :: 0x8888 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8080 :: 0x8888 :: ins) = [0x0, 0xffff, 0x8080, 0x7f7f, 0x8888, 0xaaaa, 0xcccc, 0xf0f0, 0x8000, 0xff80, 0x7777, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_162 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_147 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_148 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_158 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_138 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_156 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_150 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_159 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_85 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_154 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_152 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_157 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_153 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_160 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_85 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_152 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_157 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_153 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_160 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_84 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_155 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_161 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_83 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_18 : safe 4 (0x8888 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_142 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_151 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_102 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_86 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_165 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_86 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_19 : safe 4 (0x8888 :: 0xa0a0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xa0a0 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0x8080, 0xa8a8, 0xaaaa, 0xcccc, 0xf8f8, 0x8800, 0xff88, 0xa0a0, 0x5f5f, 0xecec, 0xf0f0, 0xa000, 0xffa0, 0x5555, 0xeeee, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_177 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_152 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_167 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_171 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_153 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_174 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_139 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_171 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_153 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_174 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_104 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_168 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_175 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_169 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_173 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_89 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_166 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_88 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_20 : safe 4 (0x8888 :: 0xeeee :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xeeee :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xeeee, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x1111, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_16 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_188 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_145 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_154 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_184 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_154 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_184 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_39 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_181 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_186 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_181 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_186 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_109 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_109 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_91 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_183 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_187 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_91 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_21 : safe 4 (0x8888 :: 0xf000 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xf000 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0x8000, 0xf888, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0xf000, 0xfff, 0xa000, 0xfaaa, 0xc000, 0xfccc, 0xf0f0, 0xff00, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_17 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_193 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_137 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_149 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_190 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_155 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_191 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_155 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_191 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_137 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_155 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_191 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73d951ea62c840 stage3_155 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73d951ea62c840 stage3_191 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_189 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73d951ea62c840 stage3_92 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_183 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_192 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_192 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_92 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_192 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_170 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_192 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_92 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_183 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_92 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_22 : safe 4 (0x8888 :: 0xf8f8 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xf8f8 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xf8f8, 0xaaaa, 0xcccc, 0x8080, 0x8800, 0xff88, 0x707, 0xa8a8, 0xfafa, 0xc8c8, 0xfcfc, 0xf0f0, 0xf800, 0xfff8, 0x5555, 0xeeee, 0xa0a0, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_202 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_143 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_156 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_159 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_198 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_45 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_178 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_197 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_178 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_197 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_194 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_201 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_106 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_184 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_171 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_174 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_199 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_106 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_171 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_174 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_199 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_96 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_191 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_200 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_196 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_94 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_23 : safe 4 (0x8888 :: 0xfafa :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xfafa :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xfafa, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x505, 0xc8c8, 0xfefe, 0xf0f0, 0xfa00, 0xfffa, 0x5555, 0xeeee, 0xa0a0, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_144 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_157 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_197 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_160 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_199 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_35 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_179 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_205 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_195 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_209 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_110 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_172 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_175 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_206 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_107 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_173 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_204 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_207 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_97 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_192 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_95 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_24 : safe 4 (0x8888 :: 0xfff0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xfff0 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0x8880, 0xfff8, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0xfff0, 0xf, 0xaaa0, 0xfffa, 0xccc0, 0xfffc, 0xf0f0, 0xff00, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_20 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_214 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_141 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_163 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_212 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_161 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_200 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_161 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_200 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_34 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_180 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_213 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_180 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_213 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_108 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_187 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_108 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_176 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_98 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_183 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_98 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_25 : safe 4 (0x8888 :: 0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: 0xffff :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0xf0f0, 0xff00, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_146 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_162 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_202 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_162 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_202 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_188 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_177 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_177 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_111 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_177 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_177 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_99 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_193 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_214 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_99 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_26 : safe 4 (0xa8a8 :: 0xfcfc :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xa8a8 :: 0xfcfc :: ins) = [0x0, 0xffff, 0xa8a8, 0x5757, 0xfcfc, 0xaaaa, 0x8888, 0xecec, 0xa0a0, 0xf8f8, 0xa800, 0xffa8, 0x303, 0xfefe, 0xcccc, 0xf0f0, 0xfc00, 0xfffc, 0x5555, 0xeeee, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_22 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_225 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7d5b391e6c4a280 stage3_135 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_179 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_216 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_179 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_216 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_164 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_221 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_36 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_220 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_218 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_224 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_121 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_217 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_217 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_180 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_222 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_112 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_181 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_195 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_223 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_112 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_195 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_223 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_101 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_27 : safe 4 (0xeeee :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xaaaa, 0xcccc, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_42 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_219 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_182 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_130 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_203 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_122 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_211 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_229 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_122 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_28 : safe 4 (0xeeee :: 0xfafa :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: 0xfafa :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xeaea, 0xfefe, 0xaaaa, 0xcccc, 0xe0e0, 0xee00, 0xffee, 0xfafa, 0x505, 0xc8c8, 0xf0f0, 0xfa00, 0xfffa, 0x5555, 0x8888, 0xa0a0, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_236 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_227 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_232 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_217 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_223 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_235 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_41 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_217 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6b3a2d5c49180 stage3_223 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_235 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_131 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_185 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_206 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_233 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_204 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_231 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_126 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_208 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_230 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_124 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_29 : safe 4 (0xeeee :: 0xfefe :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: 0xfefe :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xfefe, 0xaaaa, 0xcccc, 0xe0e0, 0xee00, 0xffee, 0x101, 0xf0f0, 0xfe00, 0xfffe, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_241 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_43 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_220 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_224 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_238 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_29 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_226 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_240 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_132 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_186 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_205 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_232 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_209 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_235 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_132 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_205 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_232 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_209 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_235 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_127 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_213 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_239 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_237 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_125 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_30 : safe 4 (0xeeee :: 0xfff0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: 0xfff0 :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xeee0, 0xfffe, 0xaaaa, 0xcccc, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0xfff0, 0xf, 0xaaa0, 0xfffa, 0xccc0, 0xfffc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_26 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_244 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_38 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_228 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_243 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_222 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_239 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_222 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_239 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_38 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_222 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_239 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_222 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73d951ea62c840 stage3_239 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_242 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73d951ea62c840 stage3_128 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_187 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_207 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_207 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_128 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_207 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_207 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_234 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_128 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_187 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_128 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_31 : safe 4 (0xeeee :: 0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: 0xffff :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xaaaa, 0xcccc, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_44 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage3_225 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_241 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage3_225 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_241 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_133 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_188 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_236 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_236 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_133 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage3_236 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_210 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage3_236 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_129 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_214 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_244 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_129 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage2_32 : safe 4 (0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xffff :: ins) = [0x0, 0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage3_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_246 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage3_134 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_215 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage3_245 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage3_134 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_0 : safe 5 (ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (ins) = [0x0, 0xffff, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_1 : safe 5 (0x0 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x0 :: ins) = [0x0, 0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage2_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage2_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_2 : safe 5 (0xff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xff :: ins) = [0x0, 0xffff, 0xff, 0xff00, 0xaa, 0xaaff, 0xcc, 0xccff, 0xf0, 0xf0ff, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_12 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_12 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage2_7 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage2_12 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_8 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_9 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage2_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage2_14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_3 : safe 5 (0x8888 :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0x8888 :: ins) = [0x0, 0xffff, 0x8888, 0x7777, 0xaaaa, 0xcccc, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_16 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_17 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_22 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_17 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_22 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage2_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_20 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage2_11 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage2_19 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_10 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_21 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_18 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_4 : safe 5 (0xeeee :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xeeee :: ins) = [0x0, 0xffff, 0xeeee, 0x1111, 0xaaaa, 0xcccc, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_6 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfbead9c873625140 stage2_26 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_29 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xf7e6d5c4b3a29180 stage2_26 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_29 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage2_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_20 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage2_14 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdecb9a875643120 stage2_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_23 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdec7564b9a83120 stage2_28 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_13 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_24 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_30 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_27 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_13 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage1_5 : safe 5 (0xffff :: ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (0xffff :: ins) = [0x0, 0xffff, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f, 0xf000, 0xfff0, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage2_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_32 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage2_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage2_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage2_15 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_25 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage2_31 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage2_15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
private theorem stage0_0 : safe 6 (ins) := by
  intro z hz
  have hm := (choice_iff _ _).2 hz
  rw [show choices (ins) = [0x0, 0xffff, 0xaaaa, 0x5555, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xcccc, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0xf0f0, 0xf0f, 0xf000, 0xfff0, 0xff00, 0xff] by decide +kernel] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pullSafe 0xfedcba9876543210 stage1_1 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_5 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb97531eca86420 stage1_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfebadc9876325410 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfe76dc54ba329810 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfeba7632dc985410 stage1_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfdb9eca875316420 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfd75ec64b931a820 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedc7654ba983210 stage1_2 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage1_3 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfb73ea62d951c840 stage1_4 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_0 (by decide +kernel) (by decide +kernel)
  · exact pullSafe 0xfedcba9876543210 stage1_2 (by decide +kernel) (by decide +kernel)

end Threshold274

open Threshold274 in
theorem PEqualNP.Outside.L_meta_274 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro ⟨C, hg, hsize, he⟩
  exact finish stage0_0 C hg hsize he
