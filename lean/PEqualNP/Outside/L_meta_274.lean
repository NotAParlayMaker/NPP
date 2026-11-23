import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_274

abbrev T := BitVec 16

def ins : List T := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def base : List T := [0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0, -1]
def target : T := 0xe880
def canon : List T := [0x5555, 0x8888, 0xeeee]
def perms : List (List T) := [[0xaaaa, 0xcccc, 0xf0f0, 0xff00], [0xaaaa, 0xf0f0, 0xcccc, 0xff00], [0xaaaa, 0xf0f0, 0xff00, 0xcccc], [0xcccc, 0xaaaa, 0xf0f0, 0xff00], [0xf0f0, 0xaaaa, 0xcccc, 0xff00], [0xf0f0, 0xaaaa, 0xff00, 0xcccc], [0xcccc, 0xf0f0, 0xaaaa, 0xff00], [0xf0f0, 0xcccc, 0xaaaa, 0xff00], [0xf0f0, 0xff00, 0xaaaa, 0xcccc], [0xcccc, 0xf0f0, 0xff00, 0xaaaa], [0xf0f0, 0xcccc, 0xff00, 0xaaaa], [0xf0f0, 0xff00, 0xcccc, 0xaaaa]]

def possible (w : List T) (z : T) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

def bit (k : Fin 16) (z : T) := z[k.val]

theorem read_bit (w : List T) (i : ℕ) (k : Fin 16) :
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

theorem exclude (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
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

def raw (ws : List T) : List T :=
  0 :: -1 :: ws.flatMap (fun x => x :: ~~~x :: ws.flatMap (fun y => [x &&& y, x ||| y]))

def choices (ws : List T) : List T := (raw ws).eraseDups

theorem choice_iff (ws : List T) (z : T) : z ∈ choices ws ↔ possible ws z := by
  simp [choices, raw, possible, List.any_eq_true]
  grind

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

theorem possible_mono {ws ws' : List T} (h : ws ⊆ ws') {z : T} (hz : possible ws z) :
    possible ws' z := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz ⊢
  rcases hz with ((h1 | h1) | ⟨x, hx, ((h2 | h2) | ⟨y, hy, h3 | h3⟩)⟩)
  · exact .inl (.inl h1)
  · exact .inl (.inr h1)
  · exact .inr ⟨x, h hx, .inl (.inl h2)⟩
  · exact .inr ⟨x, h hx, .inl (.inr h2)⟩
  · exact .inr ⟨x, h hx, .inr ⟨y, h hy, .inl h3⟩⟩
  · exact .inr ⟨x, h hx, .inr ⟨y, h hy, .inr h3⟩⟩

theorem safe_mono : ∀ (n : ℕ) {ws ws' : List T}, ws ⊆ ws' → safe n ws' → safe n ws
  | 0, ws, ws', h, hs => by
      have h1 : target ∉ ws' := by simpa [safe] using hs
      have h2 : target ∉ ws := fun hm => h1 (h hm)
      simpa [safe] using h2
  | n + 1, ws, ws', h, hs => fun z hz =>
      safe_mono n (List.cons_subset_cons z h) (hs z (possible_mono h hz))

def fresh (ws : List T) : List T := ((raw ws).filter (fun z => !(ws.contains z))).eraseDups

theorem fresh_mem {ws : List T} {z : T} (hz : possible ws z) (hn : z ∉ ws) : z ∈ fresh ws := by
  have h1 : z ∈ choices ws := (choice_iff ws z).2 hz
  simp only [choices, List.mem_eraseDups] at h1
  simp only [fresh, List.mem_eraseDups, List.mem_filter]
  exact ⟨h1, by simpa using hn⟩

def allNe (l : List T) (f : T → Bool) : Bool :=
  match l with
  | [] => false
  | z :: r => (z :: r).all f

theorem allNe_spec {l : List T} {f : T → Bool} (h : allNe l f = true) :
    (∃ z, z ∈ l) ∧ ∀ v ∈ l, f v = true := by
  cases l with
  | nil => simp [allNe] at h
  | cons z r => exact ⟨⟨z, by simp⟩, fun v hv => List.all_eq_true.mp h v hv⟩

def search : ℕ → List T → Bool
  | 0, ws => fastTwo ws
  | n + 1, ws => allNe (fresh ws) (fun v => search n (v :: ws))

theorem search_safe {n : ℕ} {ws : List T} (h : search n ws = true) : safe (n + 2) ws := by
  induction n generalizing ws with
  | zero => exact lastTwo_safe (fast_implies_last h)
  | succ n ih =>
    obtain ⟨⟨z0, hz0⟩, hall⟩ := allNe_spec (show allNe (fresh ws) (fun v => search n (v :: ws)) = true from h)
    intro z hz
    by_cases hm : z ∈ ws
    · have h0 : safe (n + 2) (z0 :: ws) := ih (hall z0 hz0)
      have h1 : safe (n + 2) ws := safe_mono _ (fun x hx => List.mem_cons_of_mem _ hx) h0
      exact safe_mono _ (List.cons_subset.mpr ⟨hm, List.Subset.refl _⟩) h1
    · exact ih (hall z (fresh_mem hz hm))

def good (z : T) : Bool := (canon ++ base).contains z

theorem perms_len : ∀ w ∈ perms, w.length = 4 := by decide

theorem ins_mem : ins ∈ perms := by decide

theorem getD_min (w : List T) (hw : w.length = 4) (i : ℕ) : w.getD i 0 = w.getD (min i 4) 0 := by
  by_cases h : i < 4
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem key_id : ∀ a < 5, good (ins.getD a 0) = true := by decide

theorem key_not : ∀ a < 5, ∃ w ∈ perms, good (~~~(w.getD a 0)) = true := by decide

theorem key_and : ∀ a < 5, ∀ b < 5, ∃ w ∈ perms, good (w.getD a 0 &&& w.getD b 0) = true := by
  decide

theorem key_or : ∀ a < 5, ∀ b < 5, ∃ w ∈ perms, good (w.getD a 0 ||| w.getD b 0) = true := by
  decide

theorem first_gate (g : Gate) (hg : legal g) :
    ∃ w ∈ perms, ∃ z, good z = true ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  have rd (w : List T) (hw : w ∈ perms) (i : ℕ) := getD_min w (perms_len w hw) i
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨ins, ins_mem, -1, by decide, by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨ins, ins_mem, 0, by decide, by simp [step, GateOp.eval, bit]⟩
    · exact ⟨ins, ins_mem, -1, by decide, by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      have hid := key_id (min i 4) (by omega)
      rw [← rd ins ins_mem i] at hid
      obtain ⟨w, hw, hn⟩ := key_not (min i 4) (by omega)
      rw [← rd w hw i] at hn
      rcases hop with rfl | rfl | rfl
      · exact ⟨ins, ins_mem, _, hid, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨ins, ins_mem, _, hid, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨w, hw, _, hn, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · obtain ⟨w, hw, hn⟩ := key_and (min i 4) (by omega) (min j 4) (by omega)
          rw [← rd w hw i, ← rd w hw j] at hn
          exact ⟨w, hw, _, hn, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · obtain ⟨w, hw, hn⟩ := key_or (min i 4) (by omega) (min j 4) (by omega)
          rw [← rd w hw i, ← rd w hw j] at hn
          exact ⟨w, hw, _, hn, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · obtain ⟨w, hw, hn⟩ := key_not (min i 4) (by omega)
          rw [← rd w hw i] at hn
          exact ⟨w, hw, _, hn, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def asg (w : List T) (k : Fin 16) (i : Fin 4) : Bool := bit k (w.getD i.val 0)

theorem asg_ofFn : ∀ w ∈ perms, ∀ k, List.ofFn (asg w k) = w.map (bit k) := by decide

theorem asg_target : ∀ w ∈ perms, ∀ k,
    (decide (3 ≤ (w.map (bit k)).count true)) = bit k target := by decide

theorem perms_sub (w : List T) (hw : w ∈ perms) (x : T) (hx : x ∈ w) : x ∈ base := by
  have h : perms.all (fun w => w.all (fun x => base.contains x)) = true := by decide +kernel
  have := List.all_eq_true.mp (List.all_eq_true.mp h w hw) x hx
  simpa using this

theorem fresh_c0 : fresh (0x5555 :: base) = [0x4444, 0xdddd, 0x5050, 0xf5f5, 0x5500, 0xff55, 0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0, 0x00ff] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem search_c0 : search 3 (0x5555 :: base) = true := by
  show allNe (fresh (0x5555 :: base)) (fun v => search 2 (v :: 0x5555 :: base)) = true
  rw [fresh_c0]
  simp only [allNe, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel
theorem fresh_c1 : fresh (0x8888 :: base) = [0x7777, 0x8080, 0xf8f8, 0x8800, 0xff88, 0x5555, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0, 0x00ff] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem search_c1 : search 3 (0x8888 :: base) = true := by
  show allNe (fresh (0x8888 :: base)) (fun v => search 2 (v :: 0x8888 :: base)) = true
  rw [fresh_c1]
  simp only [allNe, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel
theorem fresh_c2 : fresh (0xeeee :: base) = [0x1111, 0xe0e0, 0xfefe, 0xee00, 0xffee, 0x5555, 0x8888, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0x3333, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc, 0x0f0f, 0xf000, 0xfff0, 0x00ff] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem search_c2 : search 3 (0xeeee :: base) = true := by
  show allNe (fresh (0xeeee :: base)) (fun v => search 2 (v :: 0xeeee :: base)) = true
  rw [fresh_c2]
  simp only [allNe, List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  repeat' apply And.intro
  all_goals decide +kernel

theorem safe_canon : ∀ z ∈ canon, safe 5 (z :: base) := by
  intro z hz
  simp only [canon, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact search_safe search_c0
  · exact search_safe search_c1
  · exact search_safe search_c2

theorem good_safe (z : T) (hz : good z = true) : safe 5 (z :: base) := by
  have hz' : z ∈ canon ∨ z ∈ base := by simpa [good] using hz
  rcases hz' with hc | hb
  · exact safe_canon z hc
  · have h0 := safe_canon 0x8888 (by decide)
    have h1 : safe 5 base := safe_mono _ (fun x hx => List.mem_cons_of_mem _ hx) h0
    exact safe_mono _ (List.cons_subset.mpr ⟨hb, List.Subset.refl _⟩) h1

theorem main (C : Circuit) (hg : FanInTwo C) (hs : C.size ≤ 6)
    (he : ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) :
    False := by
  have hleg : ∀ g ∈ C.gates, legal g := hg
  have hev : ∀ w ∈ perms, ∀ k,
      (C.gates.foldl step (w.map (bit k))).getD C.output false = bit k target := by
    intro w hw k
    have h1 := he (asg w k)
    rw [asg_ofFn w hw k] at h1
    rw [← asg_target w hw k]
    have h2 : C.eval (w.map (bit k)) = (C.gates.foldl step (w.map (bit k))).getD C.output false := rfl
    rw [← h2]
    cases hc : C.eval (w.map (bit k)) <;> simp_all
  have hsz : C.gates.length ≤ 6 := hs
  cases hC : C.gates with
  | nil =>
    apply exclude [] C.output (by simp) ins base (fun x hx => perms_sub ins ins_mem x hx) 0
      (by simp) (show base.contains target = false by decide)
    intro k
    have := hev ins ins_mem k
    rw [hC] at this
    exact this
  | cons g gs =>
    rw [hC] at hleg hsz hev
    obtain ⟨w, hw, z, hz, hstep⟩ := first_gate g (hleg g (by simp))
    apply exclude gs C.output (fun g' hg' => hleg g' (by simp [hg'])) (w ++ [z]) (z :: base) ?_ 5
      (by simp at hsz; omega) (good_safe z hz)
    · intro k
      have := hev w hw k
      rw [List.foldl_cons, hstep k] at this
      exact this
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact List.mem_cons_of_mem _ (perms_sub w hw x hx)
      · simp

end PEqualNP.Outside.L_meta_274

theorem PEqualNP.Outside.L_meta_274 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro ⟨C, hg, hs, he⟩
  exact PEqualNP.Outside.L_meta_274.main C hg hs he
