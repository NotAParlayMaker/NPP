import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12945
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- ============================================================
-- 1. Polymorphic Wire / Reach / Run / Contraction (free NOT)
-- ============================================================

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d = 0 then combine false a b
  else if d = 1 then combine true a b
  else if d = 2 then combine false a (inv b)
  else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ inv v ∈ pool

def supply {R} (pool xs : List (Wire R)) : Prop := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R),
      Reach roots p bank ∧ Available bank a ∧ Available bank b ∧ c = combine op a b :: bank

theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl

theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine op a b :: bank) :=
  ⟨op, bank, a, b, h, ha, hb, rfl⟩

theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p + 1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero => obtain rfl := h; exact start
  | succ p ih => obtain ⟨op, bank, a, b, h, ha, hb, rfl⟩ := h; exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧
      Run goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op, ka, kb, a, b, rest, hd, q, h⟩ := h
    exact ⟨op, ka, kb, a, b, rest, hd, q.trans p, h⟩

theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)}
    (op : Nat) (hd : op < 4) (ka kb : Bool)
    (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))) :
    Run goal (s + 1) (a :: b :: rest) :=
  ⟨op, ka, kb, a, b, rest, hd, List.Perm.refl _, h⟩

theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs),
      motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : op < 4) (ka kb : Bool)
      (h : Run goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s + 1) (a :: b :: rest) (Run.two op hd ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, p, h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_append {R} (a b : List (Wire R)) : mass (a ++ b) = mass a + mass b := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a) = a := by funext r; simp [inv]

theorem cost_inv {R} (a : Wire R) : cost (inv a) = cost a := by
  have hiff : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h, inv_constant⟩
  by_cases h : Constant a
  · simp only [cost, if_pos h, if_pos (hiff.mpr h)]
  · simp only [cost, if_neg h, if_neg (fun x => h (hiff.mp x))]

theorem avail_inv {R} {bank : List (Wire R)} {a} (h : Available bank a) : Available bank (inv a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr ((inv_inv' a).symm ▸ h))
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost, ca, cb, both_constant op ca cb]
    · simp [cost, ca, cb]
    · simp [cost, ca, cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem op_four {d : Nat} (h : d < 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega

theorem comb_prime {R} {bank : List (Wire R)} {d a b} (hd : d < 4)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ op x y, comb d a b = combine op x y ∧ Available bank x ∧ Available bank y ∧
      cost x = cost a ∧ cost y = cost b := by
  rcases op_four hd with rfl | rfl | rfl | rfl
  · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
  · exact ⟨false, a, inv b, rfl, ha, avail_inv hb, rfl, cost_inv b⟩
  · exact ⟨false, inv a, b, rfl, avail_inv ha, hb, cost_inv a, rfl⟩

theorem extend_comb {R} (roots : List (Wire R)) {p bank a b} (d) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (comb d a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  obtain ⟨op, x, y, e, hx, hy, cx, cy⟩ := comb_prime hd ha hb
  rw [e, ← cx, ← cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb; split_ifs <;> rfl

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons, restrict_kept, restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons, List.length_cons, cost, if_pos ha, ih (fun x hx => hc x (by simp [hx]))]
    omega

-- Circuit execution directly to Reach (for any row type R)
def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

def evalWire {R} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map fun i => (w.getD i (fun _ => false)) r)

def execWires {R} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun l g => l ++ [evalWire l g]) w

theorem execWires_at {R} (gs : List Gate) (w : List (Wire R)) (r : R) :
    (execWires gs w).map (fun f => f r) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execWires gs (w ++ [evalWire w g])).map _ = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_singleton]
    congr 2; congr 1; unfold evalWire; congr 1
    apply List.map_congr_left; intro i _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? <;> rfl

theorem avail_getD {R} {bank w : List (Wire R)} (hs : supply bank w) (i : Nat) :
    Available bank (w.getD i (fun _ => false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (Or.inl ⟨false, rfl⟩)
  | some f => exact hs f (List.mem_of_getElem? h)

theorem circuit_reach {R} (roots : List (Wire R)) (gs : List Gate) (w : List (Wire R))
    (p : Nat) (bank : List (Wire R))
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hr : Reach roots p bank) (hs : supply bank w) :
    ∃ q next, q ≤ p + gs.countP (fun g => !isNot g) ∧ Reach roots q next ∧ supply next (execWires gs w) := by
  induction gs generalizing w p bank with
  | nil => exact ⟨p, bank, by simp, hr, hs⟩
  | cons g gs ih =>
    obtain ⟨ho, hl⟩ := legal g (by simp)
    have hstep : ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧
        Reach roots p' bank' ∧ supply bank' (w ++ [evalWire w g]) := by
      have addAvail {v : Wire R} (hv : Available bank v) :
          ∃ p' bank', p' ≤ p + (if isNot g then 0 else 1) ∧ Reach roots p' bank' ∧ supply bank' (w ++ [v]) :=
        ⟨p, bank, by omega, hr, fun a ha => by rcases List.mem_append.mp ha with h | h; exact hs a h; exact List.mem_singleton.mp h ▸ hv⟩
      obtain ⟨op, l⟩ := g
      rcases ho with rfl | rfl | rfl
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.and, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.and, [i, j]⟩ = combine false (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two false hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨false, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          cases l with
          | nil =>
            have eq : evalWire w ⟨.or, [i]⟩ = w.getD i (fun _ => false) := by
              funext r; simp [evalWire, GateOp.eval]
            rw [eq]; exact addAvail (avail_getD hs i)
          | cons j l =>
            cases l with
            | cons _ _ => simp at hl
            | nil =>
              have eq : evalWire w ⟨.or, [i, j]⟩ = combine true (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) := by
                funext r; simp [evalWire, GateOp.eval, combine]
              rw [eq]
              refine ⟨p + 1, _, by simp [isNot], Reach.two true hr (avail_getD hs i) (avail_getD hs j), ?_⟩
              intro a ha; rcases List.mem_append.mp ha with h | h
              · exact available_cons _ (hs a h)
              · rw [List.mem_singleton.mp h]; exact Or.inl (by simp)
      · cases l with
        | nil => exact addAvail (Or.inr (Or.inl ⟨true, by funext r; simp [evalWire, GateOp.eval]⟩))
        | cons i l =>
          have eq : evalWire w ⟨.not, i :: l⟩ = inv (w.getD i (fun _ => false)) := by
            funext r; simp [evalWire, GateOp.eval, inv]
          rw [eq]; exact addAvail (avail_inv (avail_getD hs i))
    obtain ⟨p', bank', hp', hr', hs'⟩ := hstep
    obtain ⟨q, next, hq, hreq, hsup⟩ := ih (w ++ [evalWire w g]) p' bank' (fun a ha => legal a (by simp [ha])) hr' hs'
    refine ⟨q, next, ?_, hreq, hsup⟩
    rw [List.countP_cons]; cases hn : isNot g <;> simp [hn] at hp' ⊢ <;> omega

-- ============================================================
-- 2. BitVec N (polymorphic for N=64 and N=128) Live & Lower
-- ============================================================

section BitVecEngine
variable {N : Nat} [NeZero N]

def zeroBV : BitVec N := 0
def oneBV : BitVec N := BitVec.allOnes N
def negBV (a : BitVec N) : BitVec N := ~~~a
def binBV (d : Nat) (a b : BitVec N) : BitVec N :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else if d = 2 then a &&& ~~~b else ~~~a &&& b
def properBV (a : BitVec N) : Prop := a ≠ zeroBV ∧ a ≠ oneBV
def flipOp (d : Nat) := if d = 2 then 3 else if d = 3 then 2 else d
def bitBV (i : Fin N) (a : BitVec N) : Bool := a.getLsbD i.val

theorem bitBV_zero (i : Fin N) : bitBV i (zeroBV (N := N)) = false := by simp [bitBV, zeroBV]
theorem bitBV_one (i : Fin N) : bitBV i (oneBV (N := N)) = true := by
  unfold bitBV oneBV; rw [BitVec.getLsbD_allOnes]; simp
theorem bitBV_neg (i : Fin N) (a : BitVec N) : bitBV i (negBV a) = !(bitBV i a) := by
  simp [bitBV, negBV, i.isLt]
theorem bitBV_bin (i : Fin N) (d : Nat) (a b : BitVec N) :
    bitBV i (binBV d a b) =
      (if d = 0 then bitBV i a && bitBV i b else if d = 1 then bitBV i a || bitBV i b else
       if d = 2 then bitBV i a && !(bitBV i b) else !(bitBV i a) && bitBV i b) := by
  unfold binBV; split_ifs <;> simp [bitBV, i.isLt]
theorem bitBV_ext {a b : BitVec N} (h : ∀ i : Fin N, bitBV i a = bitBV i b) : a = b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j, hj⟩

theorem binBV_flip {d : Nat} (h : d < 4) (a b : BitVec N) :
    binBV d a b = binBV (flipOp d) b a := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> simp [binBV, flipOp, BitVec.and_comm, BitVec.or_comm]
theorem flipOp_lt {d : Nat} (h : d < 4) : flipOp d < 4 := by
  rcases op_four h with rfl | rfl | rfl | rfl <;> decide

def nrmBV (a : BitVec N) : BitVec N := if a.getLsbD 0 then negBV a else a
theorem nrmBV_bit0 (a : BitVec N) : (nrmBV a).getLsbD 0 = false := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true]
theorem nrmBV_id {a : BitVec N} (h : a.getLsbD 0 = false) : nrmBV a = a := by simp [nrmBV, h]
theorem nrmBV_neg (a : BitVec N) : nrmBV (negBV a) = nrmBV a := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  cases h : a.getLsbD 0 <;>
    simp only [nrmBV, negBV, h, Bool.false_eq_true, ite_true, ite_false, BitVec.getLsbD_not, hpos, decide_true, Bool.true_and, Bool.not_true, Bool.not_false, BitVec.not_not]
theorem properBV_neg {a : BitVec N} (h : properBV (negBV a)) : properBV a := by
  refine ⟨?_, ?_⟩
  · rintro rfl; exact h.2 (by simp [negBV, zeroBV, oneBV])
  · rintro rfl; exact h.1 (by simp [negBV, zeroBV, oneBV])
theorem properBV_nrm {a : BitVec N} (h : properBV (nrmBV a)) : properBV a := by
  unfold nrmBV at h
  split at h
  · exact properBV_neg h
  · exact h
theorem nrmBV_ne_one (a : BitVec N) : nrmBV a ≠ oneBV := by
  intro h; have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 := nrmBV_bit0 a; rw [h] at h1; simp [oneBV, hpos] at h1

def primeBV (d : Bool) (a b : BitVec N) : BitVec N := if d then a ||| b else a &&& b
theorem bitBV_prime (i : Fin N) (d : Bool) (a b : BitVec N) :
    bitBV i (primeBV d a b) = (if d then bitBV i a || bitBV i b else bitBV i a && bitBV i b) := by
  cases d <;> simp [primeBV, bitBV]

theorem nrmBV_prime (d : Bool) (a b : BitVec N) :
    ∃ e, e < 4 ∧ nrmBV (primeBV d a b) = binBV e (nrmBV a) (nrmBV b) := by
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨if d then (if a.getLsbD 0 then (if b.getLsbD 0 then 0 else 2) else (if b.getLsbD 0 then 3 else 1))
    else (if a.getLsbD 0 then (if b.getLsbD 0 then 1 else 3) else (if b.getLsbD 0 then 2 else 0)), ?_, ?_⟩
  · split_ifs <;> omega
  · apply bitBV_ext; intro i
    cases d <;> cases ha : a.getLsbD 0 <;> cases hb : b.getLsbD 0 <;>
      simp only [nrmBV, primeBV, binBV, negBV, bitBV, ha, hb, BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_not, i.isLt, hpos, decide_true, Bool.true_and, Bool.false_and, Bool.and_true,
        Bool.and_false, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_eq_true,
        Bool.not_true, Bool.not_false, ite_true, ite_false, show (3 : Nat) ≠ 2 by decide,
        OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, Nat.one_ne_zero] <;>
      cases a.getLsbD i.val <;> cases b.getLsbD i.val <;> rfl

def LiveBV (target : BitVec N) : Nat → Finset (BitVec N) → Prop
  | 0, S => S = {target} ∧ properBV target
  | k + 1, S => ∃ (U : Finset (BitVec N)) (a b : BitVec N) (d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ properBV a ∧ properBV b ∧ a ≠ b ∧
      binBV d a b ∉ insert a (insert b U) ∧ LiveBV target k (insert (binBV d a b) U)

theorem LiveBV.stop {target : BitVec N} (hp : properBV target) : LiveBV target 0 {target} := ⟨rfl, hp⟩
theorem LiveBV.binary {target : BitVec N} {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat}
    (hd : d < 4) (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
    (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)) :
    LiveBV target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩

theorem LiveBV.ind {target : BitVec N} {motive : ∀ (k : Nat) (S : Finset (BitVec N)), LiveBV target k S → Prop}
    (stop : ∀ (hp : properBV target), motive 0 {target} (LiveBV.stop hp))
    (binary : ∀ {k : Nat} {U : Finset (BitVec N)} {a b : BitVec N} {d : Nat} (hd : d < 4)
      (ha : properBV a) (hb : properBV b) (hab : a ≠ b)
      (hfresh : binBV d a b ∉ insert a (insert b U)) (tail : LiveBV target k (insert (binBV d a b) U)),
      motive k (insert (binBV d a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBV.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset (BitVec N)} (h : LiveBV target k S) : motive k S h := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hp⟩ := h; exact stop hp
  | succ k ih => obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hf, tail⟩ := h; exact binary hd ha hb hab hf tail (ih tail)

theorem liveBV_proper {target : BitVec N} {k S} (h : LiveBV target k S) : ∀ a ∈ S, properBV a := by
  induction h using LiveBV.ind with
  | stop hp => simpa using hp
  | binary _ ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveBV_size {target : BitVec N} {k S} (h : LiveBV target k S) : S.card ≤ k + 1 := by
  induction h using LiveBV.ind with
  | stop _ => simp
  | @binary k U a b d _ _ _ _ hf _ ih =>
    have hu : binBV d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def representedBV (w : List (BitVec N)) (v : BitVec N) : Prop := v ∈ w ∨ ¬properBV v
def ReprBV (w : List (BitVec N)) (v : BitVec N) : Prop := representedBV w (nrmBV v)
def witnessBV (w : List (BitVec N)) (z : BitVec N) : Prop :=
  ∃ d a b, d < 4 ∧ a ∈ w ∧ b ∈ w ∧ properBV a ∧ properBV b ∧ a ≠ b ∧ z = binBV d a b

private lemma binBV_laws (a : BitVec N) :
    binBV 0 a oneBV = a ∧ binBV 1 a zeroBV = a ∧
    binBV 0 a zeroBV = zeroBV ∧ binBV 1 a oneBV = oneBV ∧
    binBV 0 a a = a ∧ binBV 1 a a = a ∧ binBV 2 a a = zeroBV ∧ binBV 3 a a = zeroBV ∧
    binBV 2 a zeroBV = a ∧ binBV 3 zeroBV a = a ∧ binBV 2 zeroBV a = zeroBV ∧ binBV 3 a zeroBV = zeroBV ∧
    binBV 0 zeroBV a = zeroBV ∧ binBV 1 zeroBV a = a ∧
    binBV 0 oneBV a = a ∧ binBV 1 oneBV a = oneBV := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bitBV_ext <;> intro i <;>
    simp [bitBV_bin, bitBV_zero, bitBV_one]

private lemma operandBV_cases {w : List (BitVec N)} {a : BitVec N} (h : representedBV w a) :
    a = zeroBV ∨ a = oneBV ∨ a ∈ w ∧ properBV a := by
  by_cases hz : a = zeroBV; · exact Or.inl hz
  by_cases ho : a = oneBV; · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

private lemma binBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Nat) (hd : d < 4)
    (ha : representedBV w a) (hb : representedBV w b) (no : a ≠ oneBV ∧ b ≠ oneBV) :
    representedBV w (binBV d a b) ∨ witnessBV w (binBV d a b) := by
  have rz : representedBV w zeroBV := Or.inr (fun h => h.1 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := binBV_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := binBV_laws b
  by_cases he : a = b
  · subst b; left
    rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operandBV_cases ha with rfl | rfl | ⟨ham, hap⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · exact absurd rfl no.1
  rcases operandBV_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · left; rcases op_four hd with rfl | rfl | rfl | rfl
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · exact absurd rfl no.2
  exact Or.inr ⟨d, a, b, hd, ham, hbm, hap, hbp, he, rfl⟩

theorem primeBV_rep {w : List (BitVec N)} {a b : BitVec N} (d : Bool)
    (ha : ReprBV w a) (hb : ReprBV w b) :
    ReprBV w (primeBV d a b) ∨ witnessBV w (nrmBV (primeBV d a b)) := by
  obtain ⟨e, he, eq⟩ := nrmBV_prime d a b
  unfold ReprBV; rw [eq]
  exact binBV_rep e he ha hb ⟨nrmBV_ne_one a, nrmBV_ne_one b⟩

theorem reprBV_const {w : List (BitVec N)} {v : BitVec N} (h : v = zeroBV ∨ v = oneBV) : ReprBV w v := by
  refine Or.inr fun hp => ?_
  have := properBV_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

private lemma pullBV_gate {target : BitVec N} {w : List (BitVec N)} {z : BitVec N} {k S c}
    (h : LiveBV target k S) (hz : representedBV w z ∨ (c = 1 ∧ witnessBV w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' S', k' ≤ k + c ∧ LiveBV target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha; rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveBV_proper h z hm
      rcases hz with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binBV d a b)
        have ht : LiveBV target k (insert (binBV d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
          obtain ⟨hne, hmv⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hmv
        have hf : binBV d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, Nat.le_refl _, LiveBV.binary hd pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha

def observeBV (a : BitVec N) : Wire (Fin N) := fun r => bitBV r a
def tableBV (f : Wire (Fin N)) : BitVec N :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem bitBV_table (f : Wire (Fin N)) (r : Fin N) : bitBV r (tableBV f) = f r := by
  simp only [bitBV, tableBV, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [r.isLt]
theorem tableBV_observe (v : BitVec N) : tableBV (observeBV v) = v :=
  bitBV_ext fun r => bitBV_table (observeBV v) r
theorem observeBV_table (f : Wire (Fin N)) : observeBV (tableBV f) = f :=
  funext fun r => bitBV_table f r
theorem obsBV_neg (a : BitVec N) : observeBV (negBV a) = inv (observeBV a) :=
  funext fun r => bitBV_neg r a
theorem obsBV_bin (d : Nat) (a b : BitVec N) : observeBV (binBV d a b) = comb d (observeBV a) (observeBV b) := by
  funext r; simp only [observeBV, bitBV_bin, comb]; split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α) (hn : l.Nodup) (ha : a ∉ l) :
    (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin {α : Type} [DecidableEq α] (k : Bool) (a : α) (l : List α) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by cases k <;> simp [kept]

theorem list_runBV {T : BitVec N} {k S} (h : LiveBV T k S) (v : List (BitVec N))
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observeBV T) k (v.map observeBV) := by
  classical
  induction h using LiveBV.ind generalizing v with
  | stop _ =>
    have eq : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simpa [eqv])
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd _ _ hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : binBV d a b ∉ tail := fun hz =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (binBV d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((binBV d a b :: kept ka a (kept kb b rest)).map observeBV) at progress
    rw [List.map_cons, map_kept, map_kept, obsBV_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j; by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem tableBV_inv (f : Wire (Fin N)) : tableBV (inv f) = negBV (tableBV f) := by
  rw [← tableBV_observe (negBV (tableBV f)), obsBV_neg, observeBV_table]
theorem tableBV_prime (d : Bool) (f g : Wire (Fin N)) :
    tableBV (combine d f g) = primeBV d (tableBV f) (tableBV g) := by
  apply bitBV_ext; intro r; rw [bitBV_table, bitBV_prime, bitBV_table, bitBV_table]; cases d <;> rfl

theorem availableBV_rep {bank : List (Wire (Fin N))} {a} (h : Available bank a) :
    ReprBV ((bank.map tableBV).map nrmBV) (tableBV a) := by
  rcases h with hm | ⟨b, rfl⟩ | hm
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply reprBV_const; cases b
    · exact Or.inl (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_zero i).symm)
    · exact Or.inr (bitBV_ext fun i => (bitBV_table _ i).trans (bitBV_one i).symm)
  · refine Or.inl ?_; rw [← nrmBV_neg, ← tableBV_inv a]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reachBV_live_sub {roots : List (Wire (Fin N))} {p bank}
    (h : Reach roots p bank) {T k S} (run : LiveBV T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map tableBV).map nrmBV) :
    ∃ l V, l ≤ p + k ∧ LiveBV T l V ∧ ∀ a ∈ V, a ∈ (roots.map tableBV).map nrmBV := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k, S, by omega, run, sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons, List.map_cons, tableBV_prime] at sub
    have rep := primeBV_rep d (availableBV_rep ha) (availableBV_rep hb)
    obtain ⟨k', S', hk, run', sub'⟩ := pullBV_gate (c := 1) run (rep.imp id (fun h => ⟨rfl, h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l, V, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, V, by omega, hr, hs⟩

def plainWordBV (a : BitVec N) : Bool := !(a.getLsbD 0)
theorem nrmBV_map {w : List (BitVec N)} (h : w.all plainWordBV = true) : w.map nrmBV = w := by
  have e : w.map nrmBV = w.map id := List.map_congr_left fun a ha =>
    nrmBV_id (by simpa [plainWordBV] using List.all_eq_true.mp h a ha)
  rw [e, List.map_id]

theorem reachBV_live {roots : List (BitVec N)} {p bank T}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (h : Reach (roots.map observeBV) p bank) (hit : Available bank (observeBV T)) :
    ∃ k S, k ≤ p ∧ LiveBV T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := availableBV_rep hit
  rw [tableBV_observe] at hm
  unfold ReprBV at hm
  rw [nrmBV_id (by simpa [plainWordBV] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, V, hl, hr, hs⟩ := reachBV_live_sub h (LiveBV.stop hp) (by simpa using mem)
  refine ⟨l, V, by omega, hr, ?_⟩
  have e : (roots.map observeBV).map tableBV = roots := by
    simp [List.map_map, Function.comp_def, tableBV_observe]
  rw [e, nrmBV_map nR] at hs
  exact hs

theorem liveBV_row_diff {T : BitVec N} {k S} (h : LiveBV T k S) {r s : Fin N}
    (diff : bitBV r T ≠ bitBV s T) : ∃ a ∈ S, bitBV r a ≠ bitBV s a := by
  induction h using LiveBV.ind with
  | stop _ => exact ⟨_, by simp, diff⟩
  | @binary k U a b d _ _ _ _ _ _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bitBV r a = bitBV s a
      · refine ⟨b, by simp, fun beq => hd (by rw [bitBV_bin, bitBV_bin, aeq, beq])⟩
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem rawBV_required {T : BitVec N} {k S} (h : LiveBV T k S) (roots : List (BitVec N)) (a : BitVec N)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Fin N) (diff : bitBV r T ≠ bitBV s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := liveBV_row_diff h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def LowerBV (roots : List (BitVec N)) (T : BitVec N) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observeBV) p bank → Available bank (observeBV T) → L ≤ p

def ImpossibleBV (T : BitVec N) (cap : Nat) (S : Finset (BitVec N)) : Prop :=
  ∀ k, k ≤ cap → ¬LiveBV T k S

def EssentialBV (T : BitVec N) (roots : List (BitVec N)) (a : BitVec N) : Prop :=
  ∃ r s : Fin N, bitBV r T ≠ bitBV s T ∧ ∀ v ∈ roots, v ≠ a → bitBV r v = bitBV s v

theorem lowerBV_impossible {roots : List (BitVec N)} {T : BitVec N} {L : Nat}
    (hp : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true)
    (essential : ∀ a ∈ roots, EssentialBV T roots a)
    (noRun : ImpossibleBV T L roots.toFinset) : LowerBV roots T (L + 1) := by
  intro p bank h ha
  obtain ⟨k, S, hk, run, hs⟩ := reachBV_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a; rw [List.mem_toFinset]
    refine ⟨fun hm => ?_, hs a⟩
    obtain ⟨r, s, hd, iso⟩ := essential _ hm
    exact rawBV_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observeBV_proper {v : BitVec N} (hv : properBV v) : ¬Constant (observeBV v) := by
  rintro ⟨b, h⟩
  have hr : representedBV ([] : List (BitVec N)) v := by
    cases b
    · exact Or.inr fun hp => hp.1 (bitBV_ext fun i => (congrFun h i).trans (bitBV_zero i).symm)
    · exact Or.inr fun hp => hp.2 (bitBV_ext fun i => (congrFun h i).trans (bitBV_one i).symm)
  exact (hr.resolve_left (by simp)) hv

end BitVecEngine

theorem lowerBV_slice {N M : Nat} [NeZero N] [NeZero M]
    {roots : List (BitVec N)} {other : List (BitVec M)} {T : BitVec N} {G : BitVec M}
    (pT : properBV T) (nT : plainWordBV T = true) (nR : roots.all plainWordBV = true) (pG : properBV G)
    (r : Fin M → Fin N) (eq : restrictRows r (observeBV T) = observeBV G)
    (covered : ∀ a ∈ roots, Available (other.map observeBV) (restrictRows r (observeBV a)))
    (singles : Finset (BitVec N)) (necessary : ∀ a ∈ singles, EssentialBV T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictRows r (observeBV a)))
    (L : Nat) (prior : LowerBV other G L) : LowerBV roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs; obtain ⟨i, j, hd, hiso⟩ := necessary a hs
    exact rawBV_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have run' := list_runBV run front nd fe
  have supp : supply (other.map observeBV) ((front.map observeBV).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (eq ▸ observeBV_proper pG) Reach.start supp (L := L) (eq ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observeBV).map (restrictRows r)) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map observeBV).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _; rw [sz]; omega
  omega

-- ============================================================
-- 3. 6-variable (BitVec 64) Engine, Slices, Pools & CutCheck
-- ============================================================

abbrev Sig := BitVec 64
abbrev Row := Fin 64

def x0 : Sig := 0xaaaaaaaaaaaaaaaa#64
def x1 : Sig := 0xcccccccccccccccc#64
def x2 : Sig := 0xf0f0f0f0f0f0f0f0#64
def x3 : Sig := 0xff00ff00ff00ff00#64
def x4 : Sig := 0xffff0000ffff0000#64
def x5 : Sig := 0xffffffff00000000#64
def allVars6 : List Sig := [x0, x1, x2, x3, x4, x5]

def rawOf (vmask : Nat) : List Sig :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD i 0) else none

theorem rawOf_nodup (m : Nat) : (rawOf m).Nodup := by
  unfold rawOf
  have h : ∀ b0 b1 b2 b3 b4 b5 : Bool,
      (([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
        if (match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | _ => b5)
        then some (allVars6.getD i 0) else none).Nodup := by decide +kernel
  exact h (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4) (m.testBit 5)

def rename6 (f : Row → Row) (a : Sig) : Sig := tableBV fun r => bitBV (f r) a
theorem bit6_rename (f : Row → Row) (a : Sig) (r : Row) : bitBV r (rename6 f a) = bitBV (f r) a :=
  bitBV_table _ _
theorem observe6_rename (f : Row → Row) (a : Sig) : observeBV (rename6 f a) = restrictRows f (observeBV a) := by
  funext r; exact bit6_rename f a r
theorem rename6_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename6 f (binBV d a b) = binBV d (rename6 f a) (rename6 f b) := by
  apply bitBV_ext; intro r; simp only [bit6_rename, bitBV_bin]
theorem rename6_const (f : Row → Row) : rename6 f zeroBV = zeroBV ∧ rename6 f oneBV = oneBV := by
  constructor <;> apply bitBV_ext <;> intro r
  · exact (bit6_rename f zeroBV r).trans ((bitBV_zero _).trans (bitBV_zero r).symm)
  · exact (bit6_rename f oneBV r).trans ((bitBV_one _).trans (bitBV_one r).symm)
theorem rename6_inj (f : Row → Row) (onto : Function.Surjective f) : Function.Injective (rename6 f) := by
  intro a b h; apply bitBV_ext; intro j
  obtain ⟨r, hr⟩ := onto j
  have he := congrArg (bitBV r) h
  rw [bit6_rename, bit6_rename, hr] at he; exact he

theorem live6_rename {T : Sig} {k S} (h : LiveBV T k S) (f : Row → Row) (onto : Function.Surjective f) :
    LiveBV (rename6 f T) k (S.image (rename6 f)) := by
  have inj := rename6_inj f onto
  obtain ⟨fz, fo⟩ := rename6_const f
  have pp (v : Sig) (p : properBV v) : properBV (rename6 f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)), fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using LiveBV.ind with
  | stop hp => simpa using LiveBV.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename6 f (binBV d a b) ∉ (insert a (insert b U)).image (rename6 f) := by
      intro hm; obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp hm; exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert, rename6_bin] at fresh ih ⊢
    exact LiveBV.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

def rowPerm (p : List Nat) (r : Row) : Row :=
  let v := ([0, 1, 2, 3, 4, 5] : List Nat).foldl
    (fun acc i => if r.val.testBit (p.getD i 0) then acc ||| (1 <<< i) else acc) 0
  ⟨v % 64, Nat.mod_lt _ (by decide)⟩

def sigPerm (p : List Nat) (a : Sig) : Sig := rename6 (rowPerm p) a

def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (63 ^^^ (z ||| o))) ||| (o &&& 63)) % 64, Nat.mod_lt _ (by decide)⟩

def subcube6 (z o : Nat) : Sig :=
  tableBV fun r => ((r.val &&& z) == 0) && ((r.val &&& o) == (o &&& 63))

def properB (T : Sig) : Bool := T != zeroBV && T != oneBV
theorem proper_of {T : Sig} (h : properB T = true) : properBV T := by
  simpa only [properB, properBV, Bool.and_eq_true, bne_iff_ne] using h

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),
    (∀ r, bitBV (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observeBV) (restrictRows f (observeBV a))) ∧
    ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) L

def masked (d a : Sig) : Sig := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zeroBV || m == d || (pool.map (masked d)).any (fun v => v == m) ||
    (let c := masked d (negBV a); (pool.map (masked d)).any (fun v => v == c))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = masked d b) : restrictRows f (observeBV a) = restrictRows f (observeBV b) := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = bitBV (f r) b
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = zeroBV) : restrictRows f (observeBV a) = fun _ => false := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = false; rw [bitBV_zero] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bitBV (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observeBV a) = fun _ => true := by
  funext r; have h := congrArg (bitBV (f r)) eq
  change bitBV (f r) a = true; rw [dom r] at h
  simpa only [bitBV, masked, BitVec.getLsbD_and, show d.getLsbD (f r).val = true from dom r, Bool.and_true] using h

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) : Prop :=
  ∀ a ∈ pool, Available bank (restrictRows f (observeBV a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bitBV (f r) d = true) (sup : poolSupply f bank pool)
    (h : availableB d pool a = true) : Available bank (restrictRows f (observeBV a)) := by
  simp only [availableB, List.any_map, Function.comp_def, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with ((hz | ho) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one dom ho⟩)
  · exact masked_eq dom he ▸ sup v hv
  · have h := avail_inv (masked_eq dom he ▸ sup v hv)
    rw [obsBV_neg] at h
    have e : inv (restrictRows f (inv (observeBV a))) = restrictRows f (observeBV a) := by
      funext r; simp [inv, restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) : Sig := binBV c.1 c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) : Bool :=
  decide (c.1 < 4) && availableB d pool c.2.1 && availableB d pool c.2.2

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bitBV (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨op, x, y, e, hx, hy, _, _⟩ := comb_prime valid.1.1 (availableB_sound dom hs valid.1.2)
    (availableB_sound dom hs valid.2)
  refine ⟨_, Reach.two op hp hx hy, ?_⟩
  intro a hm; rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal, obsBV_bin, restrict_comb, e]; exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c :: cs => if choiceOK d pool c then makePool d (choiceVal c :: pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok; split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction

def isMaskedConst (d a : Sig) : Bool := masked d a == zeroBV || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bitBV (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConst d) ≤ mass ((ws.map observeBV).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConst d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observeBV a)) := by
        have hh : masked d a = zeroBV ∨ masked d a = d := by
          simpa only [isMaskedConst, Bool.or_eq_true, beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false, masked_zero dom hz⟩
        · exact ⟨true, masked_one dom ho⟩
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

abbrev BoundPool := Sig × Nat × Nat × List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bitBV (f r) c.1 = true) ∧ ¬Constant (restrictRows f (observeBV T)) ∧
    LowerBV roots (rename6 f T) c.2.1 ∧
    Reach (roots.map observeBV) c.2.2.1 bank ∧ poolSupply f bank c.2.2.2

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T (d, lb, cs.length, ws) := by
  obtain ⟨f, roots, dom, sup, nc, prior⟩ := h
  obtain ⟨bank, hr, hs⟩ := makePool_sound dom (Reach.start (roots := roots.map observeBV)) sup cs build
  exact ⟨f, roots, bank, dom, nc, prior, by simpa using hr, hs⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.1 c.2.2.2 a = true)
    (buy : if paid then choiceOK c.1 c.2.2.2 choice = true else availableB c.1 c.2.2.2 (choiceVal choice) = true)
    (bound : k + c.2.2.1 + paid.toNat < c.2.1 + (choiceVal choice :: rest).countP (isMaskedConst c.1))
    (nd : (choiceVal choice :: rest).Nodup) :
    ImpossibleBV T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  let ws := choiceVal choice :: rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observeBV) n out)
      (zs : poolSupply f out ws) (le : n = c.2.2.1 + paid.toNat) : False := by
    have covered : supply out ((ws.map observeBV).map (restrictRows f)) := by
      intro v hv; obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm; exact zs _ ha
    have lo' : ∀ q bs, Reach (roots.map observeBV) q bs → Available bs (restrictRows f (observeBV T)) → c.2.1 ≤ q := by
      simpa only [LowerBV, observe6_rename] using lo
    have b := projected_bound f (list_runBV run ws nd rfl) nc reach covered lo'
    have cm := count_constants dom ws
    change k + c.2.2.1 + paid.toNat < c.2.1 + ws.countP (isMaskedConst c.1) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h; rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · exact availableB_sound dom (fun v hu => hc v (List.mem_cons_of_mem _ hu)) (known _ hm)

-- ============================================================
-- 4. Cut Checking (ess, K3, P4, C5, and lifts) on BitVec 64
-- ============================================================

structure CutSpec where
  z : Nat
  o : Nat
  L : Nat
  kind : Nat
  dropZ : Nat
  perm : List Nat
  dom : Sig

def essentialCheck6 (G : Sig) (roots : List Sig) (a : Sig) : Bool :=
  (List.range 64).any fun r =>
    let r1 : Row := ⟨r % 64, Nat.mod_lt _ (by decide)⟩
    (List.range 64).any fun s =>
      let r2 : Row := ⟨s % 64, Nat.mod_lt _ (by decide)⟩
      (bitBV r1 G != bitBV r2 G) && roots.all (fun w => w == a || bitBV r1 w == bitBV r2 w)

theorem essentialCheck6_sound {G : Sig} {roots : List Sig} {a : Sig}
    (h : essentialCheck6 G roots a = true) : EssentialBV G roots a := by
  simp only [essentialCheck6, List.any_eq_true, Bool.and_eq_true, bne_iff_ne,
    List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨r, _, s, _, hdiff, hiso⟩ := h
  exact ⟨⟨r % 64, _⟩, ⟨s % 64, _⟩, hdiff, fun w hw hne => (hiso w hw).resolve_left hne⟩

def freeWord6 (roots : List Sig) (w : Sig) : Bool :=
  w == zeroBV || w == oneBV || roots.contains w

theorem freeWord6_sound {roots : List Sig} {w : Sig} (h : freeWord6 roots w = true) :
    Available (roots.map observeBV) (observeBV w) := by
  simp only [freeWord6, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h
  rcases h with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false, funext bitBV_zero⟩)
  · exact Or.inr (Or.inl ⟨true, funext bitBV_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

theorem lower6_count {roots : List Sig} {G : Sig} (pG : properBV G)
    (nG : plainWordBV G = true) (nR : roots.all plainWordBV = true)
    (es : List Sig) (nd : es.Nodup) (he : es.all (essentialCheck6 G roots) = true) :
    LowerBV roots G (es.length - 1) := by
  intro p bank hr hit
  obtain ⟨k, S, hk, run, sub⟩ := reachBV_live pG nG nR hr hit
  have le : es.toFinset.card ≤ S.card := by
    apply Finset.card_le_card; intro a ha
    have ha' := List.mem_toFinset.mp ha
    obtain ⟨r, s, hd, iso⟩ := essentialCheck6_sound (List.all_eq_true.mp he a ha')
    exact rawBV_required run roots a sub r s hd iso
  rw [List.toFinset_card_of_nodup nd] at le
  have hsz := liveBV_size run
  omega

def checkCut (vmask : Nat) (T : Sig) (c : CutSpec)
    (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  let raw := rawOf vmask
  let d := subcube6 c.z c.o
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  let domOk := (List.range 64).all fun r => bitBV (f ⟨r % 64, Nat.mod_lt _ (by decide)⟩) d
  let rawOk := raw.all (fun a => freeWord6 freeRaw (rename6 f a))
  (c.dom == d) && domOk && properB G && rawOk && plainWordBV G && freeRaw.all plainWordBV &&
  (if c.kind == 0 then
     let es := freeRaw.filter (essentialCheck6 G freeRaw)
     decide (c.L ≤ es.length - 1)
   else
     let (bRoots, bT, bL) := baseOf c.kind
     let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
     properB bT &&
     (rename6 g G == bT) &&
     freeRaw.all (fun a => freeWord6 bRoots (rename6 g a)) &&
     decide (c.L ≤ bL))

theorem checkCut_sound {vmask : Nat} {T : Sig} {c : CutSpec}
    {baseOf : Nat → List Sig × Sig × Nat}
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (ok : checkCut vmask T c baseOf = true) :
    Slice (rawOf vmask) T c.dom c.L := by
  unfold checkCut at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hdomEq, domOk⟩, pG⟩, rawOk⟩, nG⟩, nFR⟩, hbody⟩ := ok
  rw [beq_iff_eq.mp hdomEq]
  let f := fixRow c.z c.o
  let G := rename6 f T
  let freeMask := vmask &&& (63 ^^^ (c.z ||| c.o))
  let freeRaw := rawOf freeMask
  have hdom : ∀ r : Row, bitBV (f r) (subcube6 c.z c.o) = true := by
    intro r
    have h := List.all_eq_true.mp domOk r.val (List.mem_range.mpr r.isLt)
    have hmod : (⟨r.val % 64, Nat.mod_lt _ (by decide)⟩ : Row) = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
    simpa [hmod] using h
  have hraw : ∀ a ∈ rawOf vmask, Available (freeRaw.map observeBV) (restrictRows f (observeBV a)) := by
    intro a ha; rw [← observe6_rename]
    exact freeWord6_sound (List.all_eq_true.mp rawOk a ha)
  have hnc : ¬Constant (restrictRows f (observeBV T)) := by
    rw [← observe6_rename]; exact observeBV_proper (proper_of pG)
  refine ⟨f, freeRaw, hdom, hraw, hnc, ?_⟩
  by_cases hk : c.kind = 0
  · simp only [hk, beq_self_eq_true, ite_true, decide_eq_true_eq] at hbody
    let es := freeRaw.filter (essentialCheck6 G freeRaw)
    have hnd : es.Nodup := (rawOf_nodup freeMask).filter _
    have hes : es.all (essentialCheck6 G freeRaw) = true := by
      apply List.all_eq_true.mpr; intro a ha; exact (List.mem_filter.mp ha).2
    have hlo := lower6_count (proper_of pG) nG nFR es hnd hes
    intro p bank hr ha; exact le_trans hbody (hlo p bank hr ha)
  · have hkn : (c.kind == 0) = false := beq_false_of_ne hk
    simp only [hkn, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hbody
    obtain ⟨⟨⟨pbT, hEq⟩, hCov⟩, hLe⟩ := hbody
    let b := baseOf c.kind
    let g : Row → Row := fun r => fixRow c.dropZ 0 (rowPerm c.perm r)
    have hlo := lowerBV_slice (proper_of pG) nG nFR (proper_of pbT) g
      ((observe6_rename g G).symm.trans (congrArg observeBV hEq))
      (fun a ha => by rw [← observe6_rename]; exact freeWord6_sound (List.all_eq_true.mp hCov a ha))
      ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (fun _ h => absurd h (Finset.notMem_empty _))
      b.2.2 (hb c.kind hk)
    simp only [Finset.card_empty, Nat.add_zero] at hlo
    intro p bank hr ha; exact le_trans hLe (hlo p bank hr ha)

-- ============================================================
-- 5. BTree, BST, Strict Nat Kernel Checker & Soundness
-- ============================================================

inductive BTree (α : Type) where
  | leaf (a : α)
  | node (l r : BTree α)

def BTree.get {α} : BTree α → Nat → α
  | .leaf a, _ => a
  | .node l r, p => if p &&& 1 == 0 then l.get (p >>> 1) else r.get (p >>> 1)

def BTree.all {α} (f : α → Bool) : BTree α → Bool
  | .leaf a => f a
  | .node l r => l.all f && r.all f

theorem BTree.get_all {α} {f : α → Bool} {t : BTree α} (h : t.all f = true) (p : Nat) :
    f (t.get p) = true := by
  induction t generalizing p with
  | leaf a => exact h
  | node l r ihl ihr =>
    simp only [BTree.all, Bool.and_eq_true] at h
    unfold BTree.get; split
    · exact ihl h.1 _
    · exact ihr h.2 _

inductive BST where
  | e
  | l (k v : Nat)
  | n (k v : Nat) (l r : BST)

abbrev BE := BST.e
abbrev BL := BST.l
abbrev BN := BST.n

def BST.find : BST → Nat → Option (Nat × Nat)
  | .e, _ => none
  | .l k v, x => if Nat.beq x k then some (v >>> 7, v &&& 127) else none
  | .n k v left right, x =>
    if Nat.beq x k then some (v >>> 7, v &&& 127)
    else if Nat.ble x k then left.find x else right.find x

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl

noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x :: xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) :
    forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x :: xs)) = _
    rw [force_eq, ih]; rfl

def zN (op x y : Nat) : Nat :=
  cond (Nat.beq op 0) (Nat.land x y)
    (cond (Nat.beq op 1) (Nat.lor x y)
      (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))

theorem zN_mask (op : Nat) (d a b : Sig) :
    zN op (Nat.land a.toNat d.toNat) (Nat.land b.toNat d.toNat) = Nat.land (binBV op a b).toNat d.toNat := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  rw [tn, tn, tn]; unfold zN
  by_cases h0 : op = 0
  · subst h0; change Nat.land _ _ = _; rw [tn]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, ite_true, BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op = 1
  · subst h1; change Nat.lor _ _ = _; rw [tor]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, Nat.one_ne_zero, ite_true, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
    simp only [binBV, bitBV, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_true, ite_false,
      BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0, e1, e2]; change Nat.xor _ (Nat.land _ _) = _; rw [tn, tx]; congr 1; apply bitBV_ext; intro r
  simp only [binBV, bitBV, h0, h1, h2, ite_false, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, r.isLt, decide_true, Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl

theorem nat_testBit_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) :=
  Nat.testBit_and a b i
theorem nat_testBit_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) :=
  Nat.testBit_or a b i
theorem nat_testBit_xor (a b i : Nat) : (Nat.xor a b).testBit i = Bool.xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (binBV op a b).toNat := by
  have e (v : Sig) : Nat.land v.toNat (oneBV (N := 64)).toNat = v.toNat := by
    change v.toNat &&& (oneBV (N := 64)).toNat = v.toNat
    rw [← BitVec.toNat_and]; congr 1; exact BitVec.and_allOnes
  have := zN_mask op oneBV a b; rwa [e, e, e] at this

theorem zN_testBit (op x y i : Nat) :
    (zN op x y).testBit i =
      (if op = 0 then x.testBit i && y.testBit i
       else if op = 1 then x.testBit i || y.testBit i
       else if op = 2 then x.testBit i && !(y.testBit i)
       else !(x.testBit i) && y.testBit i) := by
  unfold zN
  by_cases h0 : op = 0
  · subst h0; simp [nat_testBit_land]
  by_cases h1 : op = 1
  · subst h1; simp [nat_testBit_lor]
  have e0 : Nat.beq op 0 = false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1 = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op = 2
  · subst h2; simp only [e0, e1, Bool.cond_false, Bool.cond_true, Nat.beq_refl, nat_testBit_xor, nat_testBit_land,
      OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false, ite_true]
    cases x.testBit i <;> cases y.testBit i <;> rfl
  have e2 : Nat.beq op 2 = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  simp only [e0, e1, e2, Bool.cond_false, nat_testBit_xor, nat_testBit_land, h0, h1, h2, ite_false]
  cases x.testBit i <;> cases y.testBit i <;> rfl

abbrev CovN := Nat × Nat × Nat

def addCovN (z : Nat) (c : CovN) : CovN :=
  (Nat.lor z c.1,
   Nat.lor (Nat.xor z (Nat.land z c.1)) (Nat.xor c.2.1 (Nat.land c.2.1 z)),
   Nat.lor (Nat.land z c.2.1) (Nat.xor c.2.2 (Nat.land c.2.2 z)))

def covOfCols : List Nat → CovN
  | [] => (0, 0, 0)
  | z :: zs => addCovN z (covOfCols zs)

def takeOneN (c : CovN) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.1 (Nat.land c.2.1 a))
def takeTwoN (c : CovN) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.land c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b))))
def restCovN (c : CovN) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOneN c b)
  else if kb then takeOneN c a else takeTwoN c a b

theorem addCovN_swap (c : CovN) (a b : Nat) : addCovN a (addCovN b c) = addCovN b (addCovN a c) := by
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  all_goals
    simp only [addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem takeOneN_add (c : CovN) (a : Nat) : takeOneN (addCovN a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOneN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl

theorem takeTwoN_add (c : CovN) (a b : Nat) : takeTwoN (addCovN a (addCovN b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwoN, addCovN, nat_testBit_lor, nat_testBit_land, nat_testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl

theorem covOfCols_perm {l r : List Nat} (h : l.Perm r) : covOfCols l = covOfCols r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCovN a) ih
  | swap a b _ => exact addCovN_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

def orList : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.lor x (orList xs)

theorem covOfCols_fst (l : List Nat) : (covOfCols l).1 = orList l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [covOfCols, addCovN, orList, ih]

theorem orList_testBit (l : List Nat) (i : Nat) :
    (orList l).testBit i = true ↔ ∃ x ∈ l, x.testBit i = true := by
  induction l with
  | nil => simp [orList]
  | cons x xs ih => simp [orList, Nat.testBit_lor, ih]

abbrev DWire := Sig × Nat × Nat
def dcol (w : DWire) : Nat := Nat.xor w.2.1 w.2.2
def dbin (op : Nat) (a b : DWire) : DWire := (binBV op a.1 b.1, zN op a.2.1 b.2.1, zN op a.2.2 b.2.2)

def Faithful (pos neg : List Row) (w : DWire) : Prop :=
  (∀ i : Nat, i < pos.length →
    w.2.1.testBit i = bitBV (pos.getD i ⟨0, by decide⟩) w.1 ∧
    w.2.2.testBit i = bitBV (neg.getD i ⟨0, by decide⟩) w.1) ∧
  w.2.1 < 2 ^ pos.length ∧ w.2.2 < 2 ^ pos.length

theorem zN_lt_pow {W op x y : Nat} (hx : x < 2 ^ W) (hy : y < 2 ^ W) : zN op x y < 2 ^ W := by
  have hi : ∀ i ≥ W, (zN op x y).testBit i = false := by
    intro i hi
    have h1 : x.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))
    have h2 : y.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi))
    rw [zN_testBit, h1, h2]; split_ifs <;> rfl
  by_contra! hge
  have hlt : W ≤ Nat.log2 (zN op x y) := by
    have hp : zN op x y ≠ 0 := by
      have : 0 < 2 ^ W := Nat.pow_pos (by decide)
      omega
    exact (Nat.le_log2 hp).mpr hge
  have htb := Nat.testBit_log2 (show zN op x y ≠ 0 by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega)
  rw [hi _ hlt] at htb; exact Bool.noConfusion htb

theorem faithful_dbin {pos neg : List Row} {a b : DWire} (op : Nat)
    (ha : Faithful pos neg a) (hb : Faithful pos neg b) : Faithful pos neg (dbin op a b) := by
  refine ⟨fun i hi => ?_, zN_lt_pow ha.2.1 hb.2.1, zN_lt_pow ha.2.2 hb.2.2⟩
  obtain ⟨ha1, ha2⟩ := ha.1 i hi
  obtain ⟨hb1, hb2⟩ := hb.1 i hi
  simp only [dbin, zN_testBit, bitBV_bin, ha1, ha2, hb1, hb2, and_self]

theorem faithful_zero (pos neg : List Row) : Faithful pos neg (zeroBV, 0, 0) :=
  ⟨fun i _ => by simp [bitBV_zero], Nat.pow_pos (by decide), Nat.pow_pos (by decide)⟩

def CritOK (T : Sig) (pos neg : List Row) : Prop :=
  ∀ i : Nat, i < pos.length →
    bitBV (pos.getD i ⟨0, by decide⟩) T ≠ bitBV (neg.getD i ⟨0, by decide⟩) T

def allOnesNat (W : Nat) : Nat := (1 <<< W) - 1

theorem dcol_lt {pos neg : List Row} {w : DWire} (h : Faithful pos neg w) : dcol w < 2 ^ pos.length := by
  have hi : ∀ i ≥ pos.length, (dcol w).testBit i = false := by
    intro i hi
    have h1 : w.2.1.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.1 (Nat.pow_le_pow_right (by decide) hi))
    have h2 : w.2.2.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.2.2 (Nat.pow_le_pow_right (by decide) hi))
    simp [dcol, Nat.testBit_xor, h1, h2]
  by_contra! hge
  have hp : dcol w ≠ 0 := by have : 0 < 2 ^ pos.length := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem orList_lt {W : Nat} {l : List Nat} (hl : ∀ x ∈ l, x < 2 ^ W) : orList l < 2 ^ W := by
  have hi : ∀ i ≥ W, (orList l).testBit i = false := by
    intro i hi; apply Bool.eq_false_iff.mpr; intro ht
    obtain ⟨x, hx, hxt⟩ := (orList_testBit l i).mp ht
    have hf := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hl x hx) (Nat.pow_le_pow_right (by decide) hi))
    rw [hf] at hxt; exact Bool.noConfusion hxt
  by_contra! hge
  have hp : orList l ≠ 0 := by have : 0 < 2 ^ W := Nat.pow_pos (by decide); omega
  have htb := Nat.testBit_log2 hp
  rw [hi _ ((Nat.le_log2 hp).mpr hge)] at htb; exact Bool.noConfusion htb

theorem live6_cover_eq {T : Sig} {k} {ws : List DWire} {pos neg : List Row}
    (hcrit : CritOK T pos neg) (hf : ∀ w ∈ ws, Faithful pos neg w)
    (h : LiveBV T k (ws.map Prod.fst).toFinset) :
    orList (ws.map dcol) = allOnesNat pos.length := by
  have hlt : orList (ws.map dcol) < 2 ^ pos.length :=
    orList_lt fun x hx => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact dcol_lt (hf w hw)
  apply Nat.eq_of_testBit_eq; intro i
  simp only [allOnesNat, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · simp only [hi, decide_true]
    obtain ⟨v, hv, hdiff⟩ := liveBV_row_diff h (hcrit i hi)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    apply (orList_testBit _ i).mpr
    refine ⟨dcol w, List.mem_map_of_mem hw, ?_⟩
    obtain ⟨h1, h2⟩ := (hf w hw).1 i hi
    simp only [dcol, Nat.testBit_xor, h1, h2]
    cases hx : bitBV (pos.getD i ⟨0, by decide⟩) w.1 <;>
      cases hy : bitBV (neg.getD i ⟨0, by decide⟩) w.1 <;> simp_all
  · simp only [hi, decide_false]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))

def delOne {α} [BEq α] (ws : List α) (a : α) (keep : Bool) : List α :=
  if keep then ws else ws.erase a
def delTwo {α} [BEq α] (ws : List α) (a b : α) (ka kb : Bool) : List α :=
  delOne (delOne ws a ka) b kb

theorem delOne_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a : α) (k : Bool) :
    (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem delTwo_sub {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)

theorem delTwo_len {α} [BEq α] [LawfulBEq α] (ws : List α) (a b : α) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;>
    simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]

theorem delTwo_cov {ws : List DWire} {a b : DWire} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    orList ((delTwo ws a b ka kb).map dcol) = restCovN (covOfCols (ws.map dcol)) (dcol a) (dcol b) ka kb := by
  rw [← covOfCols_fst]
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb
  · have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hm))
    change (covOfCols (((ws.erase a).erase b).map dcol)).1 = takeTwoN _ _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeTwoN_add _ _ _).symm
  · have hp : ws.Perm (a :: ws.erase a) := List.perm_cons_erase ha
    change (covOfCols ((ws.erase a).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · have hp : ws.Perm (b :: ws.erase b) := List.perm_cons_erase hb
    change (covOfCols ((ws.erase b).map dcol)).1 = takeOneN _ _
    rw [covOfCols_perm (hp.map dcol)]; exact (takeOneN_add _ _).symm
  · rfl

abbrev NodeData := Nat × Nat × List Nat
def lf (p0 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, 0, hs)
def lf2 (p0 p1 : Nat) (hs : List Nat) : BTree NodeData := .leaf (p0, p1, hs)
abbrev nd := @BTree.node NodeData
def mkRows (l : List Nat) : List Row := l.map fun x => ⟨x % 64, Nat.mod_lt _ (by decide)⟩

def unpackH1 (h : Nat) : List (Nat × Nat) :=
  if Nat.beq h 0 then [] else
  let a := ((h &&& 255) - 1, (h >>> 8) &&& 255)
  let h1 := h >>> 16
  if Nat.beq h1 0 then [a] else
  let b := ((h1 &&& 255) - 1, (h1 >>> 8) &&& 255)
  let h2 := h1 >>> 16
  if Nat.beq h2 0 then [a, b] else
  [a, b, ((h2 &&& 255) - 1, (h2 >>> 8) &&& 255)]

def unpackHints (hs : List Nat) : List (Nat × Nat) := hs.flatMap unpackH1

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons _ _ ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons _ _ ih =>
    rw [List.map_cons, selectLive, selectLive]
    split
    · rw [List.map_cons, ih]
    · exact ih _

def decodeDBank : Nat → Nat → List DWire → List DWire
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    let a := ws.getD (ops &&& 15) (zeroBV, 0, 0)
    let b := ws.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)
    decodeDBank n (ops >>> 10) (ws ++ [dbin ((ops >>> 8) &&& 3) a b])

theorem decodeDBank_faithful {pos neg : List Row} (n ops : Nat) (ws : List DWire)
    (hb : ∀ w ∈ ws, Faithful pos neg w) :
    ∀ w ∈ decodeDBank n ops ws, Faithful pos neg w := by
  have getF {l : List DWire} (hl : ∀ w ∈ l, Faithful pos neg w) (i : Nat) :
      Faithful pos neg (l.getD i (zeroBV, 0, 0)) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : l[i]? with
    | none => exact faithful_zero pos neg
    | some v => exact hl v (List.mem_of_getElem? h)
  induction n generalizing ops ws with
  | zero => exact hb
  | succ n ih =>
    apply ih; intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hb w h
    · obtain rfl := List.mem_singleton.mp h
      exact faithful_dbin _ (getF hb _) (getF hb _)

noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0, _, ws => ws
  | n + 1, ops, ws =>
    force (zN ((ops >>> 8) &&& 3) (ws.getD (ops &&& 15) 0) (ws.getD ((ops >>> 4) &&& 15) 0)) fun z =>
      decodeN n (ops >>> 10) (ws ++ [z])

theorem decodeN_eq (F : Sig → Nat) (F0 : F zeroBV = 0) (Fb : ∀ op a b, F (binBV op a b) = zN op (F a) (F b))
    (n ops : Nat) (ds : List DWire) :
    (decodeDBank n ops ds).map (fun w => F w.1) = decodeN n ops (ds.map fun w => F w.1) := by
  have gd (l : List DWire) (i : Nat) :
      (l.map fun w => F w.1).getD i 0 = F (l.getD i (zeroBV, 0, 0)).1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases l[i]? with
    | none => exact F0.symm
    | some _ => rfl
  induction n generalizing ops ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN, force_eq, decodeDBank, ih, gd, gd, ← Fb, List.map_append]; rfl

def chosenSteps (bank : List DWire) : Nat → Nat → Nat → List Choice
  | _, _, 0 => []
  | ops, paid, n + 1 =>
    if Nat.beq paid 0 then [] else
    let rest := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then rest else
      ((ops >>> 8) &&& 3, (bank.getD (ops &&& 15) (zeroBV, 0, 0)).1,
        (bank.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)).1) :: rest

def kwN (v : Nat) : Nat :=
  let n := v % 134217689
  (n * (n + 971)) % 134217689

noncomputable def anyEq (m : Nat) (l : List Nat) : Bool :=
  List.rec false (fun v _ ih => or (Nat.beq m v) ih) l

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l = true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons]

def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (anyEq (Nat.xor d m) pm)
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)

theorem masked_comp (d x : Sig) : masked d (negBV x) = d ^^^ masked d x := by
  apply bitBV_ext; intro r
  simp only [masked, negBV, bitBV, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    r.isLt, decide_true, Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl

theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]; exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConst d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zeroBV) := by
    have z0 : (zeroBV (N := 64)).toNat = 0 := by simp [zeroBV]
    rw [← beq_toNat, z0]
  rw [nconst, e, beq_toNat]; rfl
theorem anyEq_masked (x d : Sig) (pool : List Sig) :
    anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v == x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih, nmask_eq, beq_toNat, List.map_cons, List.any_cons, Bool.beq_comm]
theorem navail_eq (d a : Sig) (pool : List Sig) :
    navail d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (negBV a)).toNat := by
    rw [masked_comp]; exact (BitVec.toNat_xor _ _).symm
  rw [navail, nconst_eq, nmask_eq, x, anyEq_masked, anyEq_masked]
  simp only [availableB, isMaskedConst]

abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat

noncomputable def quickSpec (k : Nat) (ws : List DWire) (p : BoundPool) : QS :=
  let d := p.1.toNat
  let pm := p.2.2.2.map (nmask d)
  let ms := ws.map (fun w : DWire => nmask d w.1)
  (d, ms.countP (nconst d), p.2.1, Nat.add k p.2.2.1,
    (ms.map fun m => cond (navail d pm m) 0 1).sum, ms, pm)

noncomputable def forcePool {β : Type} (k : Nat) (ws : List DWire) (p : BoundPool) (f : QS → β) : β :=
  force p.1.toNat fun d => forceMap (nmask d) p.2.2.2 fun pm =>
  forceMap (fun w : DWire => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.2.1 fun l => force (Nat.add k p.2.2.1) fun t =>
  force (ms.map fun m => cond (navail d pm m) 0 1).sum fun v => f (d, c, l, t, v, ms, pm)

theorem forcePool_eq {β : Type} (k ws p) (f : QS → β) : forcePool k ws p f = f (quickSpec k ws p) := by
  simp only [forcePool, force_eq, forceMap_eq]; rfl

noncomputable def forcePools {β : Type} (k : Nat) (ws : List DWire) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool k ws p fun q => ih fun qs => f (q :: qs)) ps

theorem forcePools_eq {β : Type} (k ws ps) (f : List QS → β) :
    forcePools k ws ps f = f (ps.map (quickSpec k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool k ws p (fun q => forcePools k ws ps fun qs => f (q :: qs)) = _
    rw [forcePool_eq, ih]; rfl

noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.1 s.2.2.2.2.2.2
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))

theorem delTwo_sum {α} [BEq α] [LawfulBEq α] (f : α → Nat) {ws : List α} {a b : α}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List α} {x : α} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons, List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha; have e2 := er hb; have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo, delOne, Bool.false_eq_true, ite_true, ite_false, cond_true, cond_false] <;> omega

theorem keptCount {α} [BEq α] [LawfulBEq α] (p : α → Bool) (ws : List α) (a b : α) (ka kb : Bool) :
    ws.countP p - (if ka then 0 else (p a).toNat) - (if kb then 0 else (p b).toNat) ≤
    (delTwo ws a b ka kb).countP p := by
  have lb (l : List α) (x : α) (k : Bool) : l.countP p ≤ (delOne l x k).countP p + (if k then 0 else (p x).toNat) := by
    cases k
    · simp only [delOne, Bool.false_eq_true, ite_false, List.countP_erase]
      split
      next h => simp [h.2]; omega
      next => omega
    · simp [delOne]
  have h1 := lb ws a ka; have h2 := lb (delOne ws a ka) b kb
  simp only [delTwo]; omega

theorem fastCost_sound {raw T} {p : BoundPool} (vp : ValidPool raw T p)
    {k : Nat} {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
    (nd : (ws.map Prod.fst).Nodup)
    (hfresh : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
    (hfc : fastCost (quickSpec k ws p) i j op ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  have ha : ws[i] ∈ ws := List.getElem_mem hi
  have hb : ws[j] ∈ ws := List.getElem_mem hj
  have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
  let a := ws[i]; let b := ws[j]; let rest := delTwo ws a b ka kb
  have hsub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : (binBV op a.1 b.1 :: rest.map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨fun hm => hfresh ((hsub.map _).subset hm), nd.sublist (hsub.map _)⟩
  have gget (t : Nat) (ht : t < ws.length) :
      (ws.map (fun w : DWire => nmask p.1.toNat w.1)).getD t 0 = nmask p.1.toNat (ws[t]).1 := by
    simp [List.getD_eq_getElem?_getD, ht]
  have su : ((ws.map (fun w : DWire => nmask p.1.toNat w.1)).map
      fun m => cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) m) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum := by
    rw [List.map_map]; refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
    change cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat w.1)) 0 1 = _
    rw [navail_eq]
  have nloss_e (w : DWire) (kp : Bool) :
      nloss p.1.toNat (nmask p.1.toNat w.1) kp = if kp then 0 else (isMaskedConst p.1 w.1).toNat := by
    rw [nloss, nconst_eq]
    cases kp
    · cases isMaskedConst p.1 w.1 <;> rfl
    · rfl
  simp only [fastCost, quickSpec, force_eq, gget i hi, gget j hj, su, List.countP_map, Function.comp_def,
    nconst_eq, nloss_e] at hfc
  change and (Nat.beq (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum
    (Nat.add (cond ka 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat a.1)) 0 1))
      (cond kb 0 (cond (navail p.1.toNat (p.2.2.2.map (nmask p.1.toNat)) (nmask p.1.toNat b.1)) 0 1)))) _ = true at hfc
  have zeq : zN op (nmask p.1.toNat a.1) (nmask p.1.toNat b.1) = nmask p.1.toNat (binBV op a.1 b.1) := zN_mask op p.1 a.1 b.1
  rw [zeq, nconst_eq, navail_eq, navail_eq, navail_eq] at hfc
  simp only [Nat.add_eq, Nat.sub_eq, Nat.succ_eq_add_one, Bool.and_eq_true, Nat.beq_eq] at hfc
  obtain ⟨hu, hcond⟩ := hfc
  have hsum := delTwo_sum (fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1) ha hb hne ka kb
  change (rest.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum =
      (ws.map fun w => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum -
      cond ka 0 (cond (availableB p.1 p.2.2.2 a.1) 0 1) -
      cond kb 0 (cond (availableB p.1 p.2.2.2 b.1) 0 1) at hsum
  rw [hu] at hsum
  have hzero : (rest.map fun w : DWire => cond (availableB p.1 p.2.2.2 w.1) 0 1).sum = 0 := by omega
  have hknown : ∀ v ∈ rest.map Prod.fst, availableB p.1 p.2.2.2 v = true := by
    intro _ hm; obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
    have hv := List.sum_eq_zero_iff.mp hzero _ (List.mem_map_of_mem hw)
    cases e : availableB p.1 p.2.2.2 w.1
    · simp [e] at hv
    · rfl
  have hkc := keptCount (fun w : DWire => isMaskedConst p.1 w.1) ws a b ka kb
  have hcm : (binBV op a.1 b.1 :: rest.map Prod.fst).countP (isMaskedConst p.1) =
      rest.countP (fun w : DWire => isMaskedConst p.1 w.1) + (isMaskedConst p.1 (binBV op a.1 b.1)).toNat := by
    simp only [List.countP_cons, List.countP_map, Function.comp_def]
    cases isMaskedConst p.1 (binBV op a.1 b.1) <;> simp
  have ca : isMaskedConst p.1 (binBV op a.1 b.1) = true → availableB p.1 p.2.2.2 (binBV op a.1 b.1) = true := by
    intro h; simp only [availableB, isMaskedConst, Bool.or_eq_true] at h ⊢; exact Or.inl (Or.inl h)
  let ch : Choice := (op, a.1, b.1)
  have hcv : choiceVal ch = binBV op a.1 b.1 := rfl
  generalize hC : (ws.countP (fun w => isMaskedConst p.1 w.1) - (if ka then 0 else (isMaskedConst p.1 a.1).toNat) -
      (if kb then 0 else (isMaskedConst p.1 b.1).toNat)) = C at hcond hkc
  change C ≤ rest.countP (fun w => isMaskedConst p.1 w.1) at hkc
  cases h1 : Nat.ble (k + p.2.2.1 + 1) (p.2.1 + C)
  · rw [h1] at hcond
    cases h2 : Nat.ble (k + p.2.2.1) (p.2.1 + C)
    · rw [h2] at hcond; simp at hcond
    · rw [h2] at hcond
      have hl2 := Nat.ble_eq.mp h2
      simp only [Bool.cond_true, Bool.cond_false] at hcond
      have haz := ca hcond
      exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm, hcond]; simp; omega) ndc
  · rw [h1] at hcond
    have hl1 := Nat.ble_eq.mp h1
    simp only [Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at hcond
    rcases hcond with haz | ⟨hl2, haa, hbb⟩
    · exact valid_exclude vp k (rest.map Prod.fst) ch false hknown haz (by rw [hcv, hcm]; simp; omega) ndc
    · have hcok : choiceOK p.1 p.2.2.2 ch = true := by simp [choiceOK, ch, hop, haa, hbb]
      exact valid_exclude vp k (rest.map Prod.fst) ch true hknown hcok (by rw [hcv, hcm]; simp; omega) ndc

-- Forest & fastNodeOK
structure Forest where
  vmask : Nat
  target : Sig
  cap : Nat
  pos : List Row
  neg : List Row
  rawCols : List (Nat × Nat)
  autos : List (List Nat)
  cuts : List CutSpec
  levels : Nat → Option (BTree NodeData)
  maps : Nat → BST

def Forest.rawD (g : Forest) : List DWire :=
  (rawOf g.vmask).zipWith (fun s c => (s, c.1, c.2)) g.rawCols

def Forest.nodeWires (g : Forest) (nd : NodeData) : List DWire :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  selectLive liveMask (decodeDBank depth ops g.rawD)

def Forest.nodeVals (g : Forest) (nd : NodeData) : List Sig :=
  (g.nodeWires nd).map Prod.fst

def rawPermN (vmask : Nat) (perm : List Nat) : List Nat :=
  ([0, 1, 2, 3, 4, 5] : List Nat).filterMap fun i =>
    if vmask.testBit i then some (allVars6.getD (perm.getD i 0) 0).toNat else none

noncomputable def fastPermState (g : Forest) (k : Nat) (tag : Nat) : Option (List Nat) :=
  ((g.maps k).find tag).bind fun (path, ai) =>
  (g.levels (k - 1)).bind fun tree =>
  (g.autos[ai]?).map fun perm =>
    let x := tree.get path
    selectLive ((x.1 >>> 4) &&& 65535) (decodeN (x.1 &&& 15) ((x.1 >>> 20) + (x.2.1 <<< 40)) (rawPermN g.vmask perm))

def rowPermSurjB (p : List Nat) : Bool :=
  (List.range 64).all fun y =>
    (List.range 64).any fun x =>
      (rowPerm p ⟨x % 64, Nat.mod_lt _ (by decide)⟩).val == y

theorem rowPermSurjB_sound {p : List Nat} (h : rowPermSurjB p = true) :
    Function.Surjective (rowPerm p) := by
  intro y
  have hy := List.all_eq_true.mp h y.val (List.mem_range.mpr y.isLt)
  obtain ⟨x, _, hx⟩ := List.any_eq_true.mp hy
  exact ⟨⟨x % 64, Nat.mod_lt _ (by decide)⟩, Fin.ext (beq_iff_eq.mp hx)⟩

def autoCheck (T : Sig) (p : List Nat) : Bool :=
  rowPermSurjB p && (sigPerm p T == T) &&
  ([0, 1, 2, 3, 4, 5] : List Nat).all (fun i => sigPerm p (allVars6.getD i 0) == allVars6.getD (p.getD i 0) 0)

theorem autoCheck_rotate {T : Sig} {p : List Nat} (hok : autoCheck T p = true)
    {k : Nat} {ws : List Sig} (himp : ImpossibleBV T k ws.toFinset) :
    ImpossibleBV T k (ws.map (sigPerm p)).toFinset := by
  simp only [autoCheck, Bool.and_eq_true, beq_iff_eq] at hok
  have hsurj := rowPermSurjB_sound hok.1.1
  have hbij : Function.Bijective (rowPerm p) := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  obtain ⟨invF, hinvL, hinvR⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hinvSurj : Function.Surjective invF := fun r => ⟨rowPerm p r, hinvL r⟩
  have hinvSig (a : Sig) : rename6 invF (sigPerm p a) = a := by
    apply bitBV_ext; intro r; rw [bit6_rename, sigPerm, bit6_rename, hinvR]
  have hTinv : rename6 invF T = T := by conv => lhs; rw [← hok.1.2]; exact hinvSig T
  intro t ht hlive
  have hrun := live6_rename hlive invF hinvSurj
  rw [hTinv] at hrun
  have hback : (ws.map (sigPerm p)).toFinset.image (rename6 invF) = ws.toFinset := by
    ext a; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩; simpa only [hinvSig] using hw
    · intro ha; exact ⟨_, ⟨a, ha, rfl⟩, hinvSig a⟩
  rw [hback] at hrun
  exact himp t ht hrun

theorem zipWith_fst_map {α β γ : Type} (f : α → β → γ) (g : γ → α) (h : ∀ a b, g (f a b) = a)
    (xs : List α) (ys : List β) (hlen : xs.length = ys.length) :
    (xs.zipWith f ys).map g = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys => simp [h, ih ys (by simpa using hlen)]

theorem filterMap_map_eq {α β γ : Type} (l : List α) (p : α → Bool) (f : α → β) (g : β → γ) :
    (l.filterMap fun x => if p x then some (f x) else none).map g =
    l.filterMap fun x => if p x then some (g (f x)) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases p a <;> simp [ih]

theorem fastPermState_sound (g : Forest) (k tag : Nat) {ys : List Nat}
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : ∀ tree, g.levels (k - 1) = some tree → ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (h : fastPermState g k tag = some ys) :
    ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset := by
  unfold fastPermState at h
  cases hf : (g.maps k).find tag with
  | none => simp [hf] at h
  | some pr =>
    obtain ⟨path, ai⟩ := pr
    simp only [hf, Option.bind_some] at h
    cases hl : g.levels (k - 1) with
    | none => simp [hl] at h
    | some tree =>
      simp only [hl, Option.bind_some] at h
      cases ha : g.autos[ai]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha, Option.map_some, Option.some.injEq] at h
        have hok := hauto perm (List.mem_of_getElem? ha)
        have hok' := hok
        simp only [autoCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok'
        rcases hnd : tree.get path with ⟨p0, p1, hpacked⟩
        rw [hnd] at h
        refine ⟨(g.nodeVals (p0, p1, hpacked)).map (sigPerm perm), ?_, ?_⟩
        · let F (a : Sig) : Nat := (sigPerm perm a).toNat
          have F0 : F zeroBV = 0 := by
            change (rename6 (rowPerm perm) zeroBV).toNat = 0
            rw [(rename6_const _).1]; simp [zeroBV]
          have Fb (op a b) : F (binBV op a b) = zN op (F a) (F b) := by
            change (sigPerm perm (binBV op a b)).toNat = zN op (sigPerm perm a).toNat (sigPerm perm b).toNat
            rw [zN_full, sigPerm, rename6_bin]; rfl
          have hrawF : g.rawD.map (fun w => F w.1) = rawPermN g.vmask perm := by
            have h1 : g.rawD.map Prod.fst = rawOf g.vmask :=
              zipWith_fst_map _ Prod.fst (fun _ _ => rfl) _ _ hlen
            rw [show g.rawD.map (fun w => F w.1) = (g.rawD.map Prod.fst).map F by rw [List.map_map]; rfl, h1]
            unfold rawOf rawPermN
            rw [filterMap_map_eq]
            apply List.filterMap_congr; intro i hi
            split; · congr 1; exact congrArg BitVec.toNat (hok'.2 i hi)
            · rfl
          rw [← h]; unfold Forest.nodeVals Forest.nodeWires
          rw [List.map_map, List.map_map, selectLive_map]
          change selectLive ((p0 >>> 4) &&& 65535) (decodeN (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) (rawPermN g.vmask perm)) =
            selectLive ((p0 >>> 4) &&& 65535) ((decodeDBank (p0 &&& 15) ((p0 >>> 20) + (p1 <<< 40)) g.rawD).map fun w => F w.1)
          rw [decodeN_eq F F0 Fb, hrawF]
        · exact autoCheck_rotate hok (hnd ▸ hprev tree hl path)

def buildRule (g : Forest) (ops depth : Nat) (bank : List DWire) (ci paid : Nat) : Option BoundPool :=
  (g.cuts[ci]?).bind fun c =>
    let cs := chosenSteps bank ops paid depth
    (makePool c.dom (rawOf g.vmask) cs).map fun pool => (c.dom, c.L, cs.length, pool)

theorem buildRule_sound (g : Forest)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    {ops depth bank ci paid p} (h : buildRule g ops depth bank ci paid = some p) :
    ValidPool (rawOf g.vmask) g.target p := by
  unfold buildRule at h
  cases hc : g.cuts[ci]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    cases hm : makePool c.dom (rawOf g.vmask) (chosenSteps bank ops paid depth) with
    | none => simp [hm] at h
    | some pool =>
      simp only [hm, Option.map_some, Option.some.injEq] at h
      subst p
      exact build_valid (hcuts c (List.mem_of_getElem? hc)) _ hm

-- Fast Nat-based link check (zero allocation of child list!)
noncomputable def linkAt (fl : Nat → Option (List Nat)) (wsN : List Nat) (totH : Nat)
    (x y zVal : Nat) (ka kb : Bool) : Bool :=
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq zVal ys)
      (and (wsN.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
        (ys.all fun v => or (Nat.beq v zVal) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v wsN)))))
    (fl (Nat.add (kwN zVal) (Nat.sub (Nat.sub totH (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))

theorem unique_fst {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haT <;> rcases List.mem_cons.mp hb with rfl | hbT
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbT))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haT))
    · exact ih ht haT hbT

theorem mem_delOne {α} [BEq α] [LawfulBEq α] {v : List α} (nd : v.Nodup) (a w : α) (k : Bool) :
    w ∈ delOne v a k ↔ w ∈ v ∧ (w ≠ a ∨ k = true) := by
  cases k <;> simp [delOne, nd.mem_erase_iff, and_comm]

theorem kept_value {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo, List.mem_map, mem_delOne wn, mem_delOne dn]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨_, hw.1.1, rfl⟩, hw.1.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 ha eq)) id,
      hw.2.imp (fun ne eq => ne (unique_fst nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w, hm, rfl⟩, h1, h2⟩
    exact ⟨w, ⟨⟨hm, h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
      h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩, rfl⟩

theorem linkAt_sound {T : Sig} {k : Nat} {fl : Nat → Option (List Nat)}
    {ws : List DWire} {i j op : Nat} {ka kb : Bool}
    (nd : (ws.map Prod.fst).Nodup) (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j)
    (hfl : ∀ tag ys, fl tag = some ys → ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV T k xs.toFinset)
    (h : linkAt fl (ws.map fun w => w.1.toNat) ((ws.map fun w => kwN w.1.toNat).sum)
          (ws[i]).1.toNat (ws[j]).1.toNat (binBV op (ws[i]).1 (ws[j]).1).toNat ka kb = true) :
    ImpossibleBV T k (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
  let a := ws[i]; let b := ws[j]; let z := binBV op a.1 b.1
  have ha : a ∈ ws := List.getElem_mem hi
  have hb : b ∈ ws := List.getElem_mem hj
  have hne1 : a.1 ≠ b.1 := fun e => hij ((List.Nodup.getElem_inj_iff nd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
  have hne : a ≠ b := fun e => hne1 (congrArg Prod.fst e)
  unfold linkAt at h
  generalize Nat.add (kwN z.toNat) _ = tag at h
  cases hf : fl tag with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs, rfl, himp⟩ := hfl tag ys hf
    rw [hf] at h
    simp only [forceMap_eq, List.map_id', Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      anyEq_iff, Nat.beq_eq, Bool.not_eq_true'] at h
    obtain ⟨h1, h2, h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w, hw, e⟩ := List.mem_map.mp hv; exact BitVec.toNat_inj.mp e ▸ hw
    have hset : (z :: (delTwo ws a b ka kb).map Prod.fst).toFinset = xs.toFinset := by
      ext v; simp only [List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hv)
        · exact back h1
        · obtain ⟨hw, va, vb⟩ := (kept_value nd ha hb ka kb v).mp hv
          obtain ⟨w, hm, rfl⟩ := List.mem_map.mp hw
          rcases h2 _ (List.mem_map_of_mem hm) with ⟨hka, e⟩ | ⟨hkb, e⟩ | hm2
          · rcases va with va | va
            · exact absurd (BitVec.toNat_inj.mp e) va
            · simp [va] at hka
          · rcases vb with vb | vb
            · exact absurd (BitVec.toNat_inj.mp e) vb
            · simp [vb] at hkb
          · exact back hm2
      · intro hv
        rcases h3 _ (List.mem_map_of_mem hv) with e | ⟨⟨hva, hvb⟩, hm⟩
        · exact Or.inl (BitVec.toNat_inj.mp e)
        · refine Or.inr ((kept_value nd ha hb ka kb v).mpr ⟨?_, ?_, ?_⟩)
          · obtain ⟨w, hw, e⟩ := List.mem_map.mp hm
            exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
          · rcases hva with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
          · rcases hvb with rfl | hne'
            · exact Or.inr rfl
            · exact Or.inl fun e => by subst e; rw [Nat.beq_refl] at hne'; exact Bool.noConfusion hne'
    rwa [hset]

-- The unified fast kernel node checker!
noncomputable def checkMove (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsC : List Nat)
    (i j op xi yi ci cj cz : Nat) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if Nat.ble (Nat.succ k) len then true else
  force (restCovN cov ci cj ka kb) fun rs =>
  if !(Nat.beq (Nat.lor rs cz) allW) then true else
  force (zN op xi yi) fun zVal =>
  if or (Nat.beq zVal 0) (or (Nat.beq zVal 18446744073709551615) (anyEq zVal wsN)) then true else
  or (qs.any fun s => fastCost s i j op ka kb)
     (linkAt fl wsN totH xi yi zVal ka kb)

noncomputable def checkPairOp (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j op : Nat) : Bool :=
  force (wsP.getD i 0) fun pi => force (wsP.getD j 0) fun pj =>
  force (wsQ.getD i 0) fun qi => force (wsQ.getD j 0) fun qj =>
  force (Nat.xor (zN op pi pj) (zN op qi qj)) fun cz =>
  let xi := wsN.getD i 0; let yi := wsN.getD j 0
  let ci := wsC.getD i 0; let cj := wsC.getD j 0
  let f := checkMove fl qs k n allW totH cov wsN wsC i j op xi yi ci cj cz
  and (and (f false false) (f true false)) (and (f false true) (f true true))

noncomputable def checkPair (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i j : Nat) : Bool :=
  let f := checkPairOp fl qs k n allW totH cov wsN wsP wsQ wsC i j
  and (and (f 0) (f 1)) (and (f 2) (f 3))

noncomputable def checkPairsFrom (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) (i : Nat) : List Nat → Bool
  | [] => true
  | j :: js => and (checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j)
                   (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)

noncomputable def checkAllPairs (fl : Nat → Option (List Nat)) (qs : List QS)
    (k n allW totH : Nat) (cov : CovN) (wsN wsP wsQ wsC : List Nat) : List Nat → Bool
  | [] => true
  | i :: js => and (checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC i js)
                   (checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js)

noncomputable def fastNodeOK (g : Forest) (k : Nat) (nd : NodeData) : Bool :=
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  let vals := ws.map Prod.fst
  and (decide vals.Nodup) (and (!(vals.contains g.target))
    (if Nat.beq k 0 then true else
      let hints := unpackHints nd.2.2
      let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
      forceMap (fun w : DWire => w.1.toNat) ws fun wsN =>
      forceMap (fun w : DWire => w.2.1) ws fun wsP =>
      forceMap (fun w : DWire => w.2.2) ws fun wsQ =>
      forceMap dcol ws fun wsC =>
      force (wsN.map kwN).sum fun totH =>
      let cov := covOfCols wsC
      let allW := allOnesNat g.pos.length
      forcePools (k - 1) ws pools fun qs =>
      checkAllPairs (fastPermState g k) qs k ws.length allW totH cov wsN wsP wsQ wsC (List.range ws.length)))

-- Enum step & fastNodeOK soundness!
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  binBV d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, d < 4 → ∀ ka kb, a ≠ b → binBV d a b ∉ ws →
      properBV (binBV d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleBV T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    ImpossibleBV T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using LiveBV.ind with
  | stop _ => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : binBV d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := liveBV_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U); let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b by rfl, erase_fin (hn.erase _) b, erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;>
        by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (binBV d a b) U := by
      change (binBV d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := liveBV_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [← List.toFinset_card_of_nodup nd, eq]; omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w = a ∧ k = true) ∨ w ∈ v := by cases k <;> simp [kept]

theorem binary_front {ws : List DWire} (nd : (ws.map Prod.fst).Nodup) {a b : DWire}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    (binBV d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv' := List.mem_map_of_mem (f := Prod.fst) hb
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    kept_value nd ha hb, keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    keep_mem, (nd.erase _).mem_erase_iff, nd.mem_erase_iff, binBV_flip hd a b]
  tauto

theorem checkAllPairs_at {fl qs k n allW totH cov wsN wsP wsQ wsC}
    {js : List Nat} (h : checkAllPairs fl qs k n allW totH cov wsN wsP wsQ wsC js = true)
    {i j : Nat} (hi : i ∈ js) (hj : j ∈ js) (hij : i ≠ j) :
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC i j = true ∨
    checkPair fl qs k n allW totH cov wsN wsP wsQ wsC j i = true := by
  have from_at {a : Nat} {l : List Nat} (hl : checkPairsFrom fl qs k n allW totH cov wsN wsP wsQ wsC a l = true)
      {b : Nat} (hb : b ∈ l) : checkPair fl qs k n allW totH cov wsN wsP wsQ wsC a b = true := by
    induction l with
    | nil => simp at hb
    | cons x l ih =>
      simp only [checkPairsFrom, Bool.and_eq_true] at hl
      rcases List.mem_cons.mp hb with rfl | hbT
      · exact hl.1
      · exact ih hl.2 hbT
  induction js with
  | nil => simp at hi
  | cons a js ih =>
    simp only [checkAllPairs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hi with rfl | hiT
    · exact Or.inl (from_at h.1 ((List.mem_cons.mp hj).resolve_left (Ne.symm hij)))
    · rcases List.mem_cons.mp hj with rfl | hjT
      · exact Or.inr (from_at h.1 hiT)
      · exact ih h.2 hiT hjT

theorem fastNodeOK_sound (g : Forest) (k : Nat) (nd : NodeData)
    (hlen : (rawOf g.vmask).length = g.rawCols.length)
    (hcrit : CritOK g.target g.pos g.neg)
    (hrawF : ∀ w ∈ g.rawD, Faithful g.pos g.neg w)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : k > 0 → ∀ tree, g.levels (k - 1) = some tree →
      ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (hok : fastNodeOK g k nd = true) :
    ImpossibleBV g.target k (g.nodeVals nd).toFinset := by
  let depth := nd.1 &&& 15
  let liveMask := (nd.1 >>> 4) &&& 65535
  let ops := (nd.1 >>> 20) + (nd.2.1 <<< 40)
  let hints := unpackHints nd.2.2
  unfold fastNodeOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hok
  obtain ⟨hnd, hout, hbody⟩ := hok
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  change ImpossibleBV g.target k (ws.map Prod.fst).toFinset
  by_cases hk0 : k = 0
  · subst hk0; intro t ht hlive
    have : t = 0 := by omega
    subst this; obtain ⟨hS, _⟩ := hlive
    exact hout (List.mem_toFinset.mp (by rw [hS]; exact Finset.mem_singleton_self _))
  have hkpos : k > 0 := by omega
  have hk0b : Nat.beq k 0 = false := Bool.eq_false_iff.mpr fun h => hk0 (Nat.eq_of_beq_eq_true h)
  simp only [hk0b, Bool.false_eq_true, ite_false, forceMap_eq, force_eq, forcePools_eq] at hbody
  let pools := hints.filterMap fun h => buildRule g ops depth bank h.1 h.2
  have hpv : ∀ p ∈ pools, ValidPool (rawOf g.vmask) g.target p := by
    intro p hp; obtain ⟨h', _, heq⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g hcuts heq
  have hfl : ∀ tag ys, fastPermState g k tag = some ys →
      ∃ xs : List Sig, ys = xs.map BitVec.toNat ∧ ImpossibleBV g.target (k - 1) xs.toFinset :=
    fun tag ys hs => fastPermState_sound g k tag hlen hauto (hprev hkpos) hs
  have hwsF : ∀ w ∈ ws, Faithful g.pos g.neg w := fun w hw =>
    decodeDBank_faithful depth ops g.rawD hrawF w ((selectLive_sub liveMask bank).subset hw)
  -- Helper: check one ordered pair (i, j)
  have onePair (i j op : Nat) (ka kb : Bool)
      (hi : i < ws.length) (hj : j < ws.length) (hij : i ≠ j) (hop : op < 4)
      (hfr : binBV op (ws[i]).1 (ws[j]).1 ∉ ws.map Prod.fst)
      (hpr : properBV (binBV op (ws[i]).1 (ws[j]).1))
      (hcp : checkPair (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j = true) :
      ImpossibleBV g.target (k - 1) (binBV op (ws[i]).1 (ws[j]).1 :: (delTwo ws ws[i] ws[j] ka kb).map Prod.fst).toFinset := by
    simp only [checkPair, Bool.and_eq_true] at hcp
    have hcop : checkPairOp (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map fun w => w.2.1)
        (ws.map fun w => w.2.2) (ws.map dcol) i j op = true := by
      rcases op_four hop with rfl | rfl | rfl | rfl
      · exact hcp.1.1
      · exact hcp.1.2
      · exact hcp.2.1
      · exact hcp.2.2
    simp only [checkPairOp, force_eq, Bool.and_eq_true] at hcop
    have hcm : checkMove (fastPermState g k) (pools.map (quickSpec (k - 1) ws)) k ws.length
        (allOnesNat g.pos.length) ((ws.map fun w => w.1.toNat).map kwN).sum
        (covOfCols (ws.map dcol)) (ws.map fun w => w.1.toNat) (ws.map dcol) i j op
        ((ws.map fun w => w.1.toNat).getD i 0) ((ws.map fun w => w.1.toNat).getD j 0)
        ((ws.map dcol).getD i 0) ((ws.map dcol).getD j 0)
        (Nat.xor (zN op ((ws.map fun w => w.2.1).getD i 0) ((ws.map fun w => w.2.1).getD j 0))
                 (zN op ((ws.map fun w => w.2.2).getD i 0) ((ws.map fun w => w.2.2).getD j 0))) ka kb = true := by
      cases ka <;> cases kb
      · exact hcop.1.1
      · exact hcop.2.1
      · exact hcop.1.2
      · exact hcop.2.2
    have gN (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.1.toNat).getD t 0 = (ws[t]).1.toNat := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gP (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.1).getD t 0 = (ws[t]).2.1 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gQ (t : Nat) (ht : t < ws.length) : (ws.map fun w : DWire => w.2.2).getD t 0 = (ws[t]).2.2 := by
      simp [List.getD_eq_getElem?_getD, ht]
    have gC (t : Nat) (ht : t < ws.length) : (ws.map dcol).getD t 0 = dcol ws[t] := by
      simp [List.getD_eq_getElem?_getD, ht]
    rw [gN i hi, gN j hj, gP i hi, gP j hj, gQ i hi, gQ j hj, gC i hi, gC j hj] at hcm
    unfold checkMove at hcm
    simp only [force_eq] at hcm
    -- Prove ImpossibleBV directly!
    intro t ht hlive
    have ha : ws[i] ∈ ws := List.getElem_mem hi
    have hb : ws[j] ∈ ws := List.getElem_mem hj
    have hne1 : (ws[i]).1 ≠ (ws[j]).1 := fun e => hij ((List.Nodup.getElem_inj_iff hnd (hi := by simpa using hi) (hj := by simpa using hj)).mp (by simpa using e))
    have hne : ws[i] ≠ ws[j] := fun e => hne1 (congrArg Prod.fst e)
    let rest := delTwo ws ws[i] ws[j] ka kb
    let zD := dbin op ws[i] ws[j]
    have hsub : rest.Sublist ws := delTwo_sub ws ws[i] ws[j] ka kb
    have hndc : (zD.1 :: rest.map Prod.fst).Nodup :=
      List.nodup_cons.mpr ⟨fun hm => hfr ((hsub.map _).subset hm), hnd.sublist (hsub.map _)⟩
    have hsz := liveBV_size hlive
    change (zD.1 :: rest.map Prod.fst).toFinset.card ≤ t + 1 at hsz
    rw [List.toFinset_card_of_nodup hndc] at hsz
    have hlenC : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = (zD.1 :: rest.map Prod.fst).length := by
      rw [List.length_cons, List.length_map, delTwo_len ws ws[i] ws[j] ka kb ha hb hne, Nat.add_comm 1]
    have hbleF : Nat.ble (Nat.succ k) (1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1))) = false := by
      apply Bool.eq_false_iff.mpr; intro hb; have := Nat.ble_eq.mp hb; omega
    rw [hbleF] at hcm; simp only [Bool.false_eq_true, ite_false] at hcm
    -- Cover check must pass!
    have hcovAll := live6_cover_eq hcrit
      (fun w hw => by rcases List.mem_cons.mp hw with rfl | hwr; exact faithful_dbin op (hwsF _ ha) (hwsF _ hb); exact hwsF _ (hsub.subset hwr))
      (show LiveBV g.target t ((zD :: rest).map Prod.fst).toFinset from hlive)
    simp only [List.map_cons, orList] at hcovAll
    rw [delTwo_cov ha hb hne ka kb] at hcovAll
    have hcovAll' : Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD) = allOnesNat g.pos.length :=
      (Nat.lor_comm _ _).trans hcovAll
    have hcovEq : Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length) = true :=
      Nat.beq_eq.mpr hcovAll'
    change (if !(Nat.beq (Nat.lor (restCovN (covOfCols (ws.map dcol)) (dcol ws[i]) (dcol ws[j]) ka kb) (dcol zD)) (allOnesNat g.pos.length)) then true else _) = true at hcm
    rw [hcovEq] at hcm; simp only [Bool.not_true, ite_false] at hcm
    -- zVal is proper and fresh!
    rw [zN_full] at hcm
    have hz0 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 0 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      exact hpr.1 (BitVec.toNat_inj.mp (by simpa [zeroBV] using Nat.eq_of_beq_eq_true he))
    have hz1 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat 18446744073709551615 = false := by
      apply Bool.eq_false_iff.mpr; intro he
      have hall : (oneBV (N := 64)).toNat = 18446744073709551615 := by decide +kernel
      exact hpr.2 (BitVec.toNat_inj.mp (by rw [hall]; exact Nat.eq_of_beq_eq_true he))
    have hzFresh : anyEq (binBV op (ws[i]).1 (ws[j]).1).toNat (ws.map fun w => w.1.toNat) = false := by
      apply Bool.eq_false_iff.mpr; intro hm
      obtain ⟨w, hw, he⟩ := List.mem_map.mp ((anyEq_iff _ _).mp hm)
      exact hfr (BitVec.toNat_inj.mp he.symm ▸ List.mem_map_of_mem hw)
    rw [hz0, hz1, hzFresh] at hcm
    simp only [Bool.or_false, Bool.false_eq_true, ite_false, Bool.or_eq_true, List.any_eq_true] at hcm
    rcases hcm with ⟨_, hqm, hfc⟩ | hlk
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hqm
      exact fastCost_sound (hpv p hp) hi hj hij hop hnd hfr hfc t ht hlive
    · have hsum : ((ws.map fun w : DWire => w.1.toNat).map kwN).sum = (ws.map fun w : DWire => kwN w.1.toNat).sum := by
        rw [List.map_map]; rfl
      rw [hsum] at hlk
      exact linkAt_sound hnd hi hj hij hfl hlk t ht hlive
  -- Apply enum_step!
  apply enum_step hnd hout
  intro a ha b hb d hd ka kb hab hfr hpr _
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb'
  have hij : i ≠ j := fun e => hab (by subst e; rfl)
  rcases checkAllPairs_at hbody (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij with hcp | hcp
  · rw [← binary_front hnd (List.getElem_mem hi) (List.getElem_mem hj) hab]
    exact onePair i j d ka kb hi hj hij hd hfr hpr hcp
  · rw [childTwo_swap _ hnd _ _ d hd ka kb, ← binary_front hnd (List.getElem_mem hj) (List.getElem_mem hi) (Ne.symm hab)]
    exact onePair j i (flipOp d) kb ka hj hi (Ne.symm hij) (flipOp_lt hd)
      (binBV_flip (N := 64) hd _ _ ▸ hfr) (binBV_flip (N := 64) hd _ _ ▸ hpr) hcp

-- Forest validity & induction over levels!
def graphValid (g : Forest) (baseOf : Nat → List Sig × Sig × Nat) : Bool :=
  ((rawOf g.vmask).length == g.rawCols.length) &&
  (List.range g.pos.length).all (fun i =>
    bitBV (g.pos.getD i ⟨0, by decide⟩) g.target != bitBV (g.neg.getD i ⟨0, by decide⟩) g.target) &&
  g.rawD.all (fun w =>
    (List.range g.pos.length).all (fun i =>
      (w.2.1.testBit i == bitBV (g.pos.getD i ⟨0, by decide⟩) w.1) &&
      (w.2.2.testBit i == bitBV (g.neg.getD i ⟨0, by decide⟩) w.1)) &&
    decide (w.2.1 < 2 ^ g.pos.length) && decide (w.2.2 < 2 ^ g.pos.length)) &&
  g.cuts.all (fun c => checkCut g.vmask g.target c baseOf) &&
  g.autos.all (fun p => autoCheck g.target p)

def levelsChecked (g : Forest) : Prop :=
  ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → tree.all (fastNodeOK g k) = true

theorem forest_all (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) :
    ∀ k ≤ g.cap, ∀ tree, g.levels k = some tree → ∀ p, ImpossibleBV g.target k (g.nodeVals (tree.get p)).toFinset := by
  unfold graphValid at hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hlen, hcrit⟩, hrawF⟩, hcuts⟩, hautos⟩ := hg
  have hcrit' : CritOK g.target g.pos g.neg := fun i hi => hcrit i (List.mem_range.mpr hi)
  have hrawF' : ∀ w ∈ g.rawD, Faithful g.pos g.neg w := fun w hw => by
    have := hrawF w hw; exact ⟨fun i hi => this.1.1 i (List.mem_range.mpr hi), this.1.2, this.2⟩
  have hcuts' : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target c.dom c.L :=
    fun c hc => checkCut_sound hb (hcuts c hc)
  intro k
  induction k with
  | zero =>
    intro hk tree htree p
    exact fastNodeOK_sound g 0 (tree.get p) hlen hcrit' hrawF' hcuts' hautos (by omega)
      (BTree.get_all (hl 0 hk tree htree) p)
  | succ k ih =>
    intro hk tree htree p
    exact fastNodeOK_sound g (k + 1) (tree.get p) hlen hcrit' hrawF' hcuts' hautos
      (fun _ t ht q => ih (by omega) t ht q)
      (BTree.get_all (hl (k + 1) hk tree htree) p)

def rootCheck (g : Forest) : Bool :=
  properB g.target && plainWordBV g.target && (rawOf g.vmask).all plainWordBV &&
  (rawOf g.vmask).all (essentialCheck6 g.target (rawOf g.vmask)) &&
  match g.levels g.cap with
  | none => false
  | some tree =>
    let vals := g.nodeVals (tree.get 0)
    vals.all (fun v => (rawOf g.vmask).contains v) && (rawOf g.vmask).all (fun v => vals.contains v)

theorem lower_forest (g : Forest) (baseOf : Nat → List Sig × Sig × Nat)
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (hg : graphValid g baseOf = true) (hl : levelsChecked g) (hr : rootCheck g = true) :
    LowerBV (rawOf g.vmask) g.target (g.cap + 1) := by
  unfold rootCheck at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨hp, hpt⟩, hpr⟩, hess⟩, hroot⟩ := hr
  cases hlev : g.levels g.cap with
  | none => simp [hlev] at hroot
  | some tree =>
    simp only [hlev, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hroot
    have himp := forest_all g baseOf hb hg hl g.cap (Nat.le_refl _) tree hlev 0
    have heq : (g.nodeVals (tree.get 0)).toFinset = (rawOf g.vmask).toFinset := by
      ext v; simp only [List.mem_toFinset]; exact ⟨hroot.1 v, hroot.2 v⟩
    rw [heq] at himp
    exact lowerBV_impossible (proper_of hp) hpt hpr
      (fun a ha => essentialCheck6_sound (List.all_eq_true.mp hess a ha)) himp

-- ============================================================
-- 6. Certificate Data, Verification, Monotone Witness & Main
-- ============================================================

noncomputable section CertData
def tF1 : Sig := 0xe8e8e8e8e8e8e8e8#64
def F1P : List Row := mkRows [3,3,3,5,5,5,6,6,6]
def F1N : List Row := mkRows [1,2,4,1,2,4,1,2,4]
def F1R : List (Nat × Nat) := [(63,73),(455,146),(504,292)]
def F1A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5],[1,2,0,3,4,5],[2,0,1,3,4,5],[2,1,0,3,4,5]]
def F1C : List CutSpec := []
def F1T3 : BTree NodeData := lf 0x70 []
def F1L : Nat → Option (BTree NodeData) | 3 => some F1T3 | _ => none
def F1M : Nat → BST | _ => BE
def tF2 : Sig := 0xa880a880a880a880#64
def F2P : List Row := mkRows [7,7,7,7,11,11,11,11,13,13,13,13]
def F2N : List Row := mkRows [3,5,9,14,3,5,9,14,3,5,9,14]
def F2R : List (Nat × Nat) := [(4095,1911),(255,2457),(3855,2730),(4080,3276)]
def F2A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5]]
def F2C : List CutSpec := [⟨0,1,4,1,0,[3,0,1,2,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F2T4 : BTree NodeData := lf 0xf0 [0x1]
def F2L : Nat → Option (BTree NodeData) | 4 => some F2T4 | _ => none
def F2M : Nat → BST | _ => BE
def tF3 : Sig := 0xeae8eae8eae8eae8#64
def F3P : List Row := mkRows [3,3,3,5,5,5,6,6,6,9,9,9]
def F3N : List Row := mkRows [1,10,12,1,10,12,1,10,12,1,10,12]
def F3R : List (Nat × Nat) := [(3647,585),(455,1170),(504,2340),(3584,3510)]
def F3A : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,3,4,5]]
def F3C : List CutSpec := [⟨8,0,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F3T4 : BTree NodeData := lf 0xf0 [0x1]
def F3L : Nat → Option (BTree NodeData) | 4 => some F3T4 | _ => none
def F3M : Nat → BST | _ => BE
def tF4 : Sig := 0xeee8eee8eee8eee8#64
def F4P : List Row := mkRows [3,3,3,5,5,5,6,6,6,9,9,9,10,10,10]
def F4N : List Row := mkRows [1,2,12,1,2,12,1,2,12,1,2,12,1,2,12]
def F4R : List (Nat × Nat) := [(3647,4681),(29127,9362),(504,18724),(32256,18724)]
def F4A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5]]
def F4C : List CutSpec := [⟨4,0,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f#64⟩]
def F4T4 : BTree NodeData := lf 0xf0 [0x1]
def F4L : Nat → Option (BTree NodeData) | 4 => some F4T4 | _ => none
def F4M : Nat → BST | _ => BE
def tF5 : Sig := 0xe880e880e880e880#64
def F5P : List Row := mkRows [7,7,7,7,7,7,11,11,11,11,11,11,13,13,13,13,13,13,14,14,14,14,14,14]
def F5N : List Row := mkRows [3,5,6,9,10,12,3,5,6,9,10,12,3,5,6,9,10,12,3,5,6,9,10,12]
def F5R : List (Nat × Nat) := [(262143,2929355),(16519167,5592405),(16773183,10119590),(16777152,14913080)]
def F5A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5],[1,2,0,3,4,5],[1,2,3,0,4,5],[1,3,0,2,4,5],[1,3,2,0,4,5],[2,0,1,3,4,5],[2,0,3,1,4,5],[2,1,0,3,4,5],[2,1,3,0,4,5],[2,3,0,1,4,5],[2,3,1,0,4,5],[3,0,1,2,4,5],[3,0,2,1,4,5],[3,1,0,2,4,5],[3,1,2,0,4,5],[3,2,0,1,4,5],[3,2,1,0,4,5]]
def F5C : List CutSpec := [⟨0,2,4,1,0,[0,3,1,2,4,5],0xcccccccccccccccc#64⟩,⟨0,4,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨0,8,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff00#64⟩,⟨0,1,4,1,0,[3,0,1,2,4,5],0xaaaaaaaaaaaaaaaa#64⟩]
def F5T3 : BTree NodeData := nd (lf 0x210801000783 [0x20001]) (lf 0x2531081000473 [])
def F5T4 : BTree NodeData := nd (lf 0x8010003e2 [0x20001]) (nd (lf 0x10810002f2 [0x3]) (lf 0x90810002f2 []))
def F5M4 : BST := BN 268178193 0 (BL 197086774 128) BE
def F5T5 : BTree NodeData := lf 0x10001f1 [0x200040001,0x3]
def F5M5 : BST := BN 294398772 6 (BN 245994181 129 (BN 218854910 385 (BL 205996701 7) BE) (BL 285649811 128)) (BN 338745490 0 (BL 299667920 384) (BL 411344214 1))
def F5T6 : BTree NodeData := lf 0xf0 [0x200040001,0x3]
def F5M6 : BST := BN 264724887 8 (BN 212638182 16 (BL 176322816 10) (BL 214470771 2)) (BN 306802326 0 (BL 287069495 4) BE)
def F5L : Nat → Option (BTree NodeData) | 3 => some F5T3 | 4 => some F5T4 | 5 => some F5T5 | 6 => some F5T6 | _ => none
def F5M : Nat → BST | 4 => F5M4 | 5 => F5M5 | 6 => F5M6 | _ => BE
def tF6 : Sig := 0xfee8fee8fee8fee8#64
def F6P : List Row := mkRows [3,3,3,3,5,5,5,5,6,6,6,6,9,9,9,9,10,10,10,10,12,12,12,12]
def F6N : List Row := mkRows [1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8,1,2,4,8]
def F6R : List (Nat × Nat) := [(61695,1118481),(986895,2236962),(15732720,4473924),(16773120,8947848)]
def F6A : List (List Nat) := [[0,1,2,3,4,5],[0,1,3,2,4,5],[0,2,1,3,4,5],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,3,2,1,4,5],[1,0,2,3,4,5],[1,0,3,2,4,5],[1,2,0,3,4,5],[1,2,3,0,4,5],[1,3,0,2,4,5],[1,3,2,0,4,5],[2,0,1,3,4,5],[2,0,3,1,4,5],[2,1,0,3,4,5],[2,1,3,0,4,5],[2,3,0,1,4,5],[2,3,1,0,4,5],[3,0,1,2,4,5],[3,0,2,1,4,5],[3,1,0,2,4,5],[3,1,2,0,4,5],[3,2,0,1,4,5],[3,2,1,0,4,5]]
def F6C : List CutSpec := [⟨4,0,4,1,0,[0,1,3,2,4,5],0xf0f0f0f0f0f0f0f#64⟩,⟨1,0,4,1,0,[3,0,1,2,4,5],0x5555555555555555#64⟩,⟨2,0,4,1,0,[0,3,1,2,4,5],0x3333333333333333#64⟩,⟨8,0,4,1,0,[0,1,2,3,4,5],0xff00ff00ff00ff#64⟩]
def F6T3 : BTree NodeData := nd (lf 0x1214811000783 [0x20001]) (lf 0x3535091000473 [])
def F6T4 : BTree NodeData := nd (lf 0x48110003e2 [0x10003]) (nd (lf 0x50910002f2 [0x4]) (lf 0xd0910002f2 []))
def F6M4 : BST := BN 292369923 128 (BL 227934542 0) BE
def F6T5 : BTree NodeData := lf 0x110001f1 [0x100030002,0x4]
def F6M5 : BST := BN 267287567 1 (BN 258378692 384 (BN 190227608 6 (BL 164365488 7) BE) (BL 263734569 129)) (BN 283822438 0 (BL 275491737 385) (BL 295564700 128))
def F6T6 : BTree NodeData := lf 0xf0 [0x100030002,0x4]
def F6M6 : BST := BN 261863413 4 (BN 241225197 16 (BL 187951761 0) (BL 253542168 10)) (BN 279404288 8 (BL 278398284 2) BE)
def F6L : Nat → Option (BTree NodeData) | 3 => some F6T3 | 4 => some F6T4 | 5 => some F6T5 | 6 => some F6T6 | _ => none
def F6M : Nat → BST | 4 => F6M4 | 5 => F6M5 | 6 => F6M6 | _ => BE
def tF7 : Sig := 0xeae8e880eae8e880#64
def F7P : List Row := mkRows [7,7,7,7,7,7,7,11,11,11,11,11,11,11,13,13,13,13,13,13,13,14,14,14,14,14,14,14,19,19,19,19,19,19,19,21,21,21,21,21,21,21,22,22,22,22,22,22,22,25,25,25,25,25,25,25]
def F7N : List Row := mkRows [3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28,3,5,6,9,17,26,28]
def F7R : List (Nat × Nat) := [(71499041864679423,15319331015937435),(558586264567807,20993157318136485),(562915862102143,39716784115393350),(71494644352941952,59007793542870120),(72057593769492480,63546854584629360)]
def F7A : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,4,3,5],[0,2,1,3,4,5],[0,2,1,4,3,5]]
def F7C : List CutSpec := [⟨8,0,7,5,0,[0,1,2,4,3,5],0xff00ff00ff00ff#64⟩,⟨0,1,7,6,0,[4,0,1,2,3,5],0xaaaaaaaaaaaaaaaa#64⟩,⟨0,24,2,0,0,[0,1,2,3,4,5],0xff000000ff000000#64⟩,⟨2,16,2,0,0,[0,1,2,3,4,5],0x3333000033330000#64⟩,⟨1,0,3,0,0,[0,1,2,3,4,5],0x5555555555555555#64⟩,⟨0,16,5,3,0,[0,1,2,3,4,5],0xffff0000ffff0000#64⟩,⟨2,8,2,0,0,[0,1,2,3,4,5],0x3300330033003300#64⟩,⟨6,0,2,0,0,[0,1,2,3,4,5],0x303030303030303#64⟩,⟨2,4,2,0,0,[0,1,2,3,4,5],0x3030303030303030#64⟩,⟨2,0,5,2,0,[0,4,1,2,3,5],0x3333333333333333#64⟩,⟨16,0,7,5,0,[0,1,2,3,4,5],0xffff0000ffff#64⟩,⟨0,8,5,3,0,[0,1,2,4,3,5],0xff00ff00ff00ff00#64⟩,⟨16,2,4,1,0,[0,3,1,2,4,5],0xcccc0000cccc#64⟩,⟨8,2,4,1,0,[0,3,1,4,2,5],0xcc00cc00cc00cc#64⟩,⟨0,4,5,4,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f0#64⟩,⟨17,0,2,0,0,[0,1,2,3,4,5],0x555500005555#64⟩,⟨16,4,4,1,0,[0,1,3,2,4,5],0xf0f00000f0f0#64⟩,⟨16,8,4,1,0,[0,1,2,3,4,5],0xff000000ff00#64⟩,⟨10,0,2,0,0,[0,1,2,3,4,5],0x33003300330033#64⟩,⟨9,0,2,0,0,[0,1,2,3,4,5],0x55005500550055#64⟩,⟨8,4,4,1,0,[0,1,3,4,2,5],0xf000f000f000f0#64⟩,⟨8,16,4,1,0,[0,1,2,3,4,5],0xff000000ff0000#64⟩,⟨8,1,4,1,0,[3,0,1,4,2,5],0xaa00aa00aa00aa#64⟩,⟨1,4,2,0,0,[0,1,2,3,4,5],0x5050505050505050#64⟩,⟨1,8,1,0,0,[0,1,2,3,4,5],0x5500550055005500#64⟩,⟨1,16,1,0,0,[0,1,2,3,4,5],0x5555000055550000#64⟩,⟨0,28,1,0,0,[0,1,2,3,4,5],0xf0000000f0000000#64⟩,⟨10,4,1,0,0,[0,1,2,3,4,5],0x30003000300030#64⟩,⟨4,1,4,1,0,[3,0,4,1,2,5],0xa0a0a0a0a0a0a0a#64⟩,⟨8,18,1,0,0,[0,1,2,3,4,5],0xcc000000cc0000#64⟩,⟨0,18,1,0,0,[0,1,2,3,4,5],0xcccc0000cccc0000#64⟩,⟨0,2,5,4,0,[0,4,1,2,3,5],0xcccccccccccccccc#64⟩,⟨6,16,1,0,0,[0,1,2,3,4,5],0x303000003030000#64⟩,⟨4,0,5,2,0,[0,1,4,2,3,5],0xf0f0f0f0f0f0f0f#64⟩,⟨4,16,2,0,0,[0,1,2,3,4,5],0xf0f00000f0f0000#64⟩,⟨8,20,1,0,0,[0,1,2,3,4,5],0xf0000000f00000#64⟩,⟨9,16,1,0,0,[0,1,2,3,4,5],0x55000000550000#64⟩,⟨2,1,4,1,0,[3,4,0,1,2,5],0x2222222222222222#64⟩,⟨0,20,1,0,0,[0,1,2,3,4,5],0xf0f00000f0f00000#64⟩,⟨16,12,1,0,0,[0,1,2,3,4,5],0xf0000000f000#64⟩,⟨9,4,1,0,0,[0,1,2,3,4,5],0x50005000500050#64⟩,⟨1,2,2,0,0,[0,1,2,3,4,5],0x4444444444444444#64⟩,⟨9,2,1,0,0,[0,1,2,3,4,5],0x44004400440044#64⟩,⟨17,2,1,0,0,[0,1,2,3,4,5],0x444400004444#64⟩,⟨6,8,1,0,0,[0,1,2,3,4,5],0x300030003000300#64⟩,⟨1,24,1,0,0,[0,1,2,3,4,5],0x5500000055000000#64⟩,⟨4,2,2,0,0,[0,1,2,3,4,5],0xc0c0c0c0c0c0c0c#64⟩,⟨12,0,2,0,0,[0,1,2,3,4,5],0xf000f000f000f#64⟩,⟨4,8,2,0,0,[0,1,2,3,4,5],0xf000f000f000f00#64⟩,⟨18,8,1,0,0,[0,1,2,3,4,5],0x330000003300#64⟩,⟨16,1,4,1,0,[3,0,1,2,4,5],0xaaaa0000aaaa#64⟩,⟨17,4,1,0,0,[0,1,2,3,4,5],0x505000005050#64⟩,⟨10,16,1,0,0,[0,1,2,3,4,5],0x33000000330000#64⟩,⟨16,10,1,0,0,[0,1,2,3,4,5],0xcc000000cc00#64⟩,⟨18,4,1,0,0,[0,1,2,3,4,5],0x303000003030#64⟩,⟨12,16,1,0,0,[0,1,2,3,4,5],0xf0000000f0000#64⟩,⟨20,8,1,0,0,[0,1,2,3,4,5],0xf0000000f00#64⟩,⟨12,2,1,0,0,[0,1,2,3,4,5],0xc000c000c000c#64⟩,⟨20,2,1,0,0,[0,1,2,3,4,5],0xc0c00000c0c#64⟩,⟨0,26,1,0,0,[0,1,2,3,4,5],0xcc000000cc000000#64⟩]
def F7T3 : BTree NodeData := nd (nd (nd (lf2 0x9d8524841006106 0x20d83 [0xf01]) (nd (lf2 0x9d8524841006106 0xa0f83 [0xf01]) (lf2 0x9d8524841005086 0xe5163 []))) (nd (nd (lf2 0xdd9210863006186 0xe1680 [0x1e02]) (lf2 0xdd9210863006116 0xe1583 [0x31e01])) (nd (lf2 0xdd9210863005096 0x65385 [0x3]) (lf2 0x50c604842104196 0x65487 [])))) (nd (nd (nd (lf2 0x54d434842105116 0xa5f65 [0x4]) (lf2 0xd95434842106186 0x21e80 [])) (nd (lf2 0xd95434842106116 0x21d83 [0x1b01]) (lf2 0xd95434842105186 0xa4087 [0xb02]))) (nd (nd (lf2 0xd95434842105186 0xa4387 [0xb02]) (lf2 0xd95434842106186 0xdd680 [])) (nd (lf2 0xd95434842105186 0x24175 [0x5]) (lf2 0xd95434842104386 0xa4087 []))))
def F7T4_0 := nd (nd (nd (nd (lf2 0xdd2324841002385 0x286 [0x1b011206]) (nd (lf2 0x50c524841003185 0x276 [0x817010007,0x9]) (lf2 0x50c524841002985 0x86 [0x170b1701180a,0x20c]))) (nd (nd (lf2 0x9d8524841003185 0x183 [0xf0b0f010009,0x4]) (lf2 0x9d8524841003185 0x383 [0xf0b0f010007,0x4])) (nd (lf2 0x9d8524841003185 0x163 [0xf010c0d]) (lf2 0x9d8524841003185 0x363 [0x70c0e])))) (nd (nd (nd (lf2 0x592524c810021a5 0x387 [0x9]) (lf2 0xdc5439481002585 0x182 [0x10f])) (nd (lf2 0x5d76250c1003185 0x221 [0x10f]) (lf2 0x14d538801002c05 0x184 [0x10]))) (nd (nd (lf2 0x14d538801002905 0x286 [0x511]) (lf2 0x98f638801002905 0x185 [0x1111])) (nd (lf2 0x594658801002185 0x387 [0x10]) (lf2 0x5ce658801003105 0x365 [0x51312]))))) (nd (nd (nd (lf2 0x58a529401003985 0x143 [0x111]) (nd (lf2 0x58d521481003905 0x80 [0x50c0f0b0013,0xb0f]) (lf2 0x58d521481003905 0x30 [0x701]))) (nd (nd (lf2 0xdd9521481003185 0x280 [0x1000140009]) (lf2 0xdd9521481003185 0x270 [0x15060f01150c,0xe020f0b])) (nd (lf2 0x14c6054c1002d05 0x182 [0x301]) (lf2 0x14c6054c1002c45 0x184 [0x301])))) (nd (nd (nd (lf2 0x14c6054c1002945 0x286 [0x1b0b00090005,0x1a02]) (lf2 0x5d05354c1003445 0x80 [0x31503060010,0x316])) (nd (lf2 0xc5530801002d05 0x182 [0x5161d0b120c,0x17]) (lf2 0xc5530801002945 0x186 [0x120c1f0b1c02,0x501]))) (nd (nd (lf2 0x50c218801002785 0x387 []) (lf2 0x50e528801002d85 0x381 [0x10f])) (nd (lf2 0x149218c01002585 0x287 [0x1d0b1c020018,0x4]) (lf2 0xdd9520841003185 0x280 [0x1e0210111015])))))
def F7T4_1 := nd (nd (nd (nd (lf2 0x1c14308410023c5 0x186 []) (nd (lf2 0xdc9430841002395 0x186 [0x10f]) (lf2 0x148604841002d05 0x183 [0x1e02060c180d]))) (nd (nd (lf2 0x148604841002985 0x286 [0x71b010018,0x41b0b]) (lf2 0x50c524841003195 0x276 [0x40e16020018])) (nd (lf2 0x50c524841002995 0x86 [0x20c17010005]) (lf2 0x9d8524841003185 0x80 [0x70f010018,0x40f0b])))) (nd (nd (nd (lf2 0x9d8524841003185 0x280 [0x1f0b1f010009,0x1a00070019,0x4]) (lf2 0x9d8524841003185 0x260 [0xe020c0d0c0e])) (nd (lf2 0x1c132c841003385 0x376 []) (lf2 0x54d32c841003915 0x165 [0x90f000a]))) (nd (nd (lf2 0x50c604c81002965 0x385 []) (lf2 0x592524c810029a5 0x80 [0x10f])) (nd (lf2 0x592524c810021b5 0x387 [0x10f0018]) (lf2 0x5c46050c1002b85 0x82 []))))) (nd (nd (nd (lf2 0x54c6050c1003865 0x154 [0xa]) (nd (lf2 0x1846050c1002b85 0x282 [0x1d01]) (lf2 0x5c83154c1003505 0x80 [0x3160f0b180c,0x1e02]))) (nd (nd (lf2 0xdd95214a1003185 0x80 [0x1e02100d100e]) (lf2 0x9414354a10031c5 0x76 [])) (nd (lf2 0x5db520861003185 0x80 [0x1e02100d100e]) (lf2 0xdc9430861002785 0x280 [])))) (nd (nd (nd (lf2 0x1d5210853003105 0x163 [0xc12]) (lf2 0x50d210863002705 0x87 [0x7])) (nd (lf2 0xd51210863002585 0x287 [0x1e011406]) (lf2 0x9ca318863002305 0x186 [0x1212]))) (nd (nd (lf2 0x50d210863003315 0x376 [0x160b001b1602]) (lf2 0x50d210863002715 0x87 [0x160b001b])) (nd (lf2 0x551210863003195 0x376 [0x5]) (lf2 0xd51210863003195 0x376 [0x5])))))
def F7T4_2 := nd (nd (nd (nd (lf2 0xd51210863002595 0x287 [0x80e0018]) (nd (lf2 0xdd9210863003385 0x280 [0x90e010019]) (lf2 0xdd9210863003315 0x183 [0x190e02]))) (nd (nd (lf2 0xdd9210863003195 0x85 [0x1c0005]) (lf2 0xdd9210863003195 0x185 [0x9])) (nd (lf2 0xdd9210863003195 0x285 [0x1e01]) (lf2 0xdd9210863003195 0x385 [0xe0b0e010e02])))) (nd (nd (nd (lf2 0x50d219402102595 0x87 [0x1701180a0005]) (lf2 0x1d9219402102985 0x280 [0x191f010009,0x1a1f0b040c,0x1d0406])) (nd (lf2 0x50c604842102b85 0x80 []) (lf2 0x50c604842102395 0x87 [0x1e]))) (nd (nd (lf2 0x50c604842102395 0x387 [0x1a]) (lf2 0xd94604842103985 0x280 [0x1d])) (nd (lf2 0x1c1434842103195 0x365 [0x5]) (lf2 0x1c1434842102595 0x185 [0x20c]))))) (nd (nd (nd (lf2 0x54d434842103915 0x365 [0x4130b]) (nd (lf2 0x54d434842103315 0x76 [0x130b0004]) (lf2 0xd95434842103985 0x180 [0x101b01]))) (nd (nd (lf2 0xd95434842103985 0x280 [0x1a1b010009]) (lf2 0xd95434842103915 0x183 [0x30b0b])) (nd (lf2 0xd95434842103195 0x87 [0xb010b0b0b02]) (lf2 0xd95434842103195 0x187 [0x9])))) (nd (nd (nd (lf2 0xd95434842103195 0x287 [0x9]) (lf2 0xd95434842103195 0x387 [0xb02001a])) (nd (lf2 0xd95434842102b85 0x280 [0x1b0b100a1b01,0x1a]) (lf2 0xd95434842103195 0x175 [0xf0b02001a]))) (nd (nd (lf2 0xd95434842103195 0x375 [0xb02]) (lf2 0xd95434842102395 0x87 [0x20c])) (nd (lf2 0xd95434842102395 0x287 [0xf00040007]) (lf2 0x5d5434842102785 0x80 [0x302])))))
def F7T4_3 := nd (nd (nd (nd (lf2 0x5d5434842102395 0x86 [0x7]) (nd (lf2 0x1d9434842102385 0x280 [0x51b0b1a0c]) (lf2 0x1d9434842102395 0x280 [0x5]))) (nd (nd (lf2 0xdd1534842103195 0x365 [0x1a]) (lf2 0xd95534842103915 0x183 [0x91b01])) (nd (lf2 0x9db534842102185 0x280 [0x1a0c1f010005]) (lf2 0x1c3654842103985 0x270 [0x1702])))) (nd (nd (nd (lf2 0x1c3654842102985 0x280 [0x191f010009,0x1a1f0b]) (lf2 0x1c3654842102995 0x183 [0x14])) (nd (lf2 0x9c3654842102995 0x183 [0xf01]) (lf2 0x5cf654842102995 0x80 [0x5]))) (nd (nd (lf2 0x5cf654842103915 0x373 [0x90f01]) (lf2 0x5cf654842102995 0x384 [0x1a])) (nd (lf2 0xdcf654842102985 0x280 [0x7020003100e]) (lf2 0xdcf654842102995 0x280 [0x5]))))) (nd (nd (nd (nd (lf2 0xdcf654842102995 0x184 [0x1a]) (lf2 0x9c06150c2103385 0x62 [0x1d01080e])) (nd (lf2 0x9c06150c2103385 0x362 [0x1f]) (lf2 0x5d76150c21021c5 0x80 [0x1020]))) (nd (nd (lf2 0x1c8604c52102a85 0x184 [0x18200516]) (lf2 0x9db219422103985 0x143 [0xf0100090a20])) (nd (lf2 0x1c1421413103465 0x143 [0x100f1020]) (lf2 0x50d421413103075 0x76 [0xb0001])))) (nd (nd (nd (lf2 0x5886214131030b5 0x174 [0x5]) (lf2 0x5886214131021b5 0x387 [0x5])) (nd (lf2 0x195435093102875 0x280 []) (lf2 0x5c86055131029c5 0x81 []))) (nd (nd (lf2 0x9c86055131031a5 0x372 [0x9]) (lf2 0x584611414303195 0x172 [0x140c])) (nd (lf2 0x584611414302995 0x82 [0x1e]) (lf2 0x5846114143021d5 0x387 [0x5])))))
def F7T4 : BTree NodeData := nd (nd F7T4_0 F7T4_1) (nd F7T4_2 F7T4_3)
def F7M4 : BST := BN 231460171 640 (BN 195862175 128 (BN 109698355 129 (BL 103271065 641) (BL 139571839 1536)) (BN 212548864 1920 (BL 201372033 1792) (BL 224120805 1152))) (BN 290804543 384 (BN 257380595 768 (BL 246860215 1664) (BL 278011087 896)) (BN 331236520 256 (BL 321581464 1408) (BL 338575886 1280)))
def F7T5_0 := nd (nd (nd (nd (lf 0x54d324841001f04 [0x301040a0911]) (nd (lf 0xd95324841001b84 [0x40b010009]) (lf 0xdd2324841001784 [0x80e070b030c,0xa001d]))) (nd (nd (lf 0x50c524841001d84 [0x206040e0007,0x20c]) (lf 0x5cc524841001504 [0x20c0c0d])) (nd (lf 0x9d8524841001184 [0xf0b0f01]) (lf 0x9d8524841001584 [0xf0b0f010021,0x2060009020c,0xa])))) (nd (nd (lf 0x1d94348410013c4 [0xb0101110008,0x20c]) (nd (lf 0x1c9534841001784 [0x122080a080e,0x30600230f0b]) (lf 0x50e528841001d84 [0x80a08220701,0x70b]))) (nd (nd (lf 0x1c9438841001784 [0xb0100240c0a,0x122]) (lf 0xdd94388410013c4 [0xc22010f0007,0xb0b])) (nd (lf 0xd8a524c410019a4 [0x222010f0d01,0x506]) (lf 0x9da524c410011e4 [0x60d010009]))))) (nd (nd (nd (lf 0x5d7614c810013c4 [0x10f020a000d]) (nd (lf 0x54d524c81001d24 [0x501020a0911]) (lf 0x592524c810019a4 [0x822000a010f,0x70b050c]))) (nd (nd (lf 0xd92524c810019a4 [0xa0a05060822,0xd01]) (lf 0x9da524c810015a4 [0xf0b0c0e0022])) (nd (lf 0x54e524c81001d24 [0x50c000a0009,0x90f]) (lf 0xdd5644c810011e4 [0xf0b0d010009,0x6])))) (nd (nd (nd (lf 0x484654c81001d84 [0x10f]) (lf 0x9d8654c810011e4 [0xd010f0b0009,0x6])) (nd (lf 0xdd1654c810012e4 [0x1060d01010f,0xe02]) (lf 0x487654c810019c4 [0xa0d010511,0x9]))) (nd (nd (lf 0x887654c810019c4 [0x806050f0d01,0x70b]) (lf 0x487654c81001d84 [0x5110d010009,0xa080c])) (nd (lf 0xdc54314810015c4 [0xc02200c22,0x6]) (lf 0x1c95354810015a4 [0xf0b080a0115,0x306001d])))))
def F7T5_1 := nd (nd (nd (nd (lf 0xdc54394810015c4 [0xb0b0b010c22,0x10f0220]) (nd (lf 0xdc95394810015a4 [0xf01080a0009,0x306000c]) (lf 0x94d639481001964 [0x301]))) (nd (nd (lf 0x5c86150c1001784 [0x20a0111090c]) (lf 0x5d76150c10013c4 [0x10f00070021])) (nd (lf 0x5d46250c10011e4 [0x1d0024]) (lf 0x5d76250c10011e4 [0xd0b0d010009,0x2])))) (nd (nd (nd (lf 0x1c96550c10013a4 [0xd0b01220d01,0xe02]) (lf 0xdc96550c10013a4 [0xd0b010f0d01,0xe02])) (nd (lf 0x5c83154c1001504 [0x311080c]) (lf 0x5c83154c1001544 [0x80c0311]))) (nd (nd (lf 0x14d538801001d04 [0x301]) (lf 0x94f538801001d04 [0x301])) (nd (lf 0x18d638801001b04 [0x301]) (lf 0x98f638801001b04 [0x301]))))) (nd (nd (nd (lf 0x594658801001984 [0x10]) (nd (lf 0x5ce658801001704 [0x312001d020a]) (lf 0xd96658801001984 [0x1150010]))) (nd (nd (lf 0x14d538801001d44 [0x301]) (lf 0x94f538801001d44 [0x301])) (nd (lf 0x949329401001d84 [0x32200250018]) (lf 0x54d329401001d44 [0x26000e0312,0x322090f])))) (nd (nd (nd (lf 0xdd53294010015c4 [0xb0100250018,0xd0b]) (lf 0x5cc529401001544 [0x3120c0d001d,0x26])) (nd (lf 0x5cc5294010015c4 [0x1d030c0014]) (lf 0x58a529401001984 [0xf01010f001d,0xf0b]))) (nd (nd (lf 0x50e529401001dc4 [0x70103220018,0x260802]) (lf 0x5ce5294010015c4 [0x40e001d0312])) (nd (lf 0x5d54394010015c4 [0x911001d030c,0xb0b]) (lf 0xdd15394010015c4 [0x2703060312])))))
def F7T5_2 := nd (nd (nd (nd (lf 0x5d35394010015c4 [0x2603060312,0x80e]) (nd (lf 0x548604c81001b84 [0xd0101110005]) (lf 0x948604c81001b84 [0x5001d]))) (nd (nd (lf 0x54c604c81001b44 [0x90f010c0005,0x522]) (lf 0x5d4604c810013c4 [0x2010f000d])) (nd (lf 0x54d524c81001d14 [0xe02050c0911,0xa]) (lf 0x1c1644c810013c4 [0x6020005])))) (nd (nd (nd (lf 0xdd5644c810011d4 [0xe020025]) (lf 0xdd1654c810012d4 [0x10f0e020018])) (nd (lf 0x9c1521481001d84 [0x115]) (lf 0x58d521481001914 [0xe020028]))) (nd (nd (lf 0x58d521481001994 [0xe0205120014,0x701]) (lf 0xdd9521481001194 [0xf0b0e020025,0xf010029])) (nd (lf 0xdd9521481001994 [0x250e020029,0x10f0f0b]) (lf 0x1c1631481001b44 [0x70b080a001d]))))) (nd (nd (nd (lf 0xc1631481001b44 [0x301]) (nd (lf 0x1d94354810013d4 [0x11100280025,0x240002]) (lf 0xc1535481001d44 [0x301]))) (nd (nd (lf 0x9c3529481001584 [0x1d0025]) (lf 0xdd54394810015d4 [0x2200025])) (nd (lf 0x54e60d4810019c4 [0x2401150014]) (lf 0xc153d481001d44 [0x301])))) (nd (nd (nd (lf 0x54c6050c1001b44 [0xd0b010c0018]) (lf 0x5d46050c10013c4 [0x500020018])) (nd (lf 0x1886050c1001bc4 [0xd0100240111]) (lf 0x5515350c1001c54 [0xe02090b0025,0xa0018]))) (nd (nd (lf 0xdc96550c1001394 [0x10f0e020018]) (lf 0x5c83054c1001744 [0x101])) (nd (lf 0x14c6054c1001d44 [0x301]) (lf 0x9c05354c1001544 [0x1700290025,0x301030f0f0b])))))
def F7T5_3 := nd (nd (nd (nd (lf 0x5c85354c1001514 [0xe0203110025,0x29]) (nd (lf 0x5c85354c1001554 [0x3110029]) (lf 0x5d05354c1001454 [0xe02001b]))) (nd (nd (lf 0x5d05354c1001554 [0xe0203060010,0x70b]) (lf 0x9d85354c1001554 [0x30100290025])) (nd (lf 0x9c35454c10015c4 [0x18020d0d01,0x30f]) (lf 0x54d210801001d84 [0x26020e0612])))) (nd (nd (nd (lf 0xd4d210801001d84 [0x26020e0612]) (lf 0x5ca210801001784 [0x20a020d020e,0x122])) (nd (lf 0x5da2108010013c4 [0x1d01110115]) (lf 0xc5530801001d44 [0x301]))) (nd (nd (lf 0xdd5618801001784 [0xc0200100014]) (lf 0xdd56188010015a4 [0x20d001d020e])) (nd (lf 0xdc5438801001784 [0xb0b0b01002a]) (lf 0xc5538801001d04 [0x301]))))) (nd (nd (nd (lf 0x18d538801001d24 [0x301]) (nd (lf 0x18d638801001b24 [0x301]) (lf 0x5c7638801001784 [0x30c00050220,0x306030b0301]))) (nd (nd (lf 0x98f638801001b24 [0x301]) (lf 0x5976388010019a4 [0x1d0a0a0010])) (nd (lf 0x5d76388010015a4 [0x2060c02020e,0x20a090f0f0b]) (lf 0x50c218801001f84 [0x30b0701001d,0x30c010f])))) (nd (nd (nd (lf 0x596218801001984 [0xe020a001d]) (lf 0x50f218801001f84 [0x70100090220])) (nd (lf 0x5d7218801001784 [0x2c002b]) (lf 0x5d72188010015a4 [0x20d020a020e]))) (nd (nd (lf 0xdc5328801001784 [0xb0102200009]) (lf 0xdd53288010015a4 [0xf0b0b01010f,0x20206])) (nd (lf 0x50e528801001da4 [0x802020c050c,0x701020a]) (lf 0xd8e5288010019a4 [0xa0822050c,0x506])))))
def F7T5_4 := nd (nd (nd (nd (lf 0xdc54388010017c4 [0x2a001d0220,0xc22010f]) (nd (lf 0xc5538801001d44 [0x301]) (lf 0xcc9538801001d24 [0x301]))) (nd (nd (lf 0xcc9638801001b24 [0x301]) (lf 0x8c9218c01001f04 [0xe0416050c,0x1d])) (nd (lf 0x149218c01001d84 [0x4160d010018,0x40d0b040c]) (lf 0x94a218c01001d84 [0xd0b0c020018,0x4])))) (nd (nd (nd (lf 0xdd5618c010013c4 [0xd002d]) (lf 0x58a328c01001b24 [0xf0b010c010f,0x8160c02])) (nd (lf 0xdd5628c010011e4 [0x90f000a0d01,0xc020006]) (lf 0xdd5438c01001564 [0x10222010c,0x2]))) (nd (nd (lf 0xdd9520841001194 [0x1500110e02]) (lf 0x1c14308410017c4 [0x5010f])) (nd (lf 0xdc9430841001794 [0x18010f]) (lf 0xdd54308410015d4 [0x24000f]))))) (nd (nd (nd (lf 0xdd94308410013d4 [0x20005]) (nd (lf 0x1c16308410013c4 [0x10b080a0815]) (lf 0x148604841001d84 [0x80d080e0018]))) (nd (nd (lf 0x1c1324841001784 [0x10f0b010018,0x3060a16]) (lf 0x50c524841001d94 [0x602040e0018,0x206020c])) (nd (lf 0x5cc524841001514 [0xc200e020212]) (lf 0x9d8524841001194 [0xf0b002b0e02,0x2c0f01])))) (nd (nd (nd (lf 0x9d8524841001594 [0xe02002c002b,0x10f]) (lf 0x1d94348410013d4 [0x2800080111,0x240005])) (nd (lf 0xdd16348410012d4 [0xf01010f0e02,0x1060020]) (lf 0x50e528841001d94 [0x2506020018,0x701000e]))) (nd (nd (lf 0xdd94388410013d4 [0x201110005]) (lf 0x1c132c841001f84 [0x10f0922])) (nd (lf 0x54d32c841001f14 [0x90c20000a]) (lf 0x5d132c841001794 [0x10f002a])))))
def F7T5_5 := nd (nd (nd (nd (lf 0xdd132c841001794 [0x111]) (nd (lf 0x59532c841001b94 [0xa0420]) (lf 0xdd932c841001b94 [0x122010f]))) (nd (nd (lf 0x1c143c8410017c4 [0x9]) (lf 0xdd543c8410015d4 [0xf002e])) (nd (lf 0xdd943c8410013d4 [0xa0009]) (lf 0x59553c8410019d4 [0x2b000e])))) (nd (nd (nd (lf 0xdc9644c41001394 [0xd01010f0e02,0x200f0b]) (lf 0xd8a524c410019b4 [0x2f010f])) (nd (lf 0x5c4604c81001bc4 [0x25010c0602,0xa]) (lf 0x9c4604c81001bc4 [0x10f0030]))) (nd (nd (lf 0x548604c81001ba4 [0xd01010f000a,0x422]) (lf 0x948604c810019a4 [0xa040e0422,0x6060906])) (nd (lf 0x948604c81001ba4 [0xd01010f000a]) (lf 0x50c604c81001b64 [0x1d080f070b]))))) (nd (nd (nd (lf 0x54c604c81001b64 [0x4010018000a]) (nd (lf 0x184604c81001bc4 [0xc0501000f,0x200602]) (lf 0xd84604c81001bc4 [0xa02000f]))) (nd (nd (lf 0x5d7614c810013d4 [0x200090020]) (lf 0x54d524c81001d34 [0x18000a090f,0xe02])) (nd (lf 0x50e524c81001d34 [0x22]) (lf 0x592524c810019b4 [0xa0018010f])))) (nd (nd (nd (lf 0xd92524c810019b4 [0x50605120025]) (lf 0x9da524c810015b4 [0x2200090014])) (nd (lf 0x54e524c81001d34 [0x50c000a0018,0xe]) (lf 0xd95434c81001974 [0xb0b]))) (nd (nd (lf 0xdd5434c81001574 [0x22]) (lf 0x1c1644c810013e4 [0xa002a010f,0xc01000c0020,0xe0b0006])) (nd (lf 0xdd5644c810011f4 [0xe020018010f]) (lf 0x9d8654c810011f4 [0x18010f])))))
def F7T5_6 := nd (nd (nd (nd (lf 0xdd1654c810012f4 [0x10f0e020018]) (nd (lf 0x1c14314810015e4 [0x50018000c,0x6]) (lf 0xdc54314810015d4 [0xc0220002a,0x6]))) (nd (nd (lf 0xdd94314810011f4 [0x40b010007]) (lf 0x1c14394810015e4 [0x2200090018])) (nd (lf 0xdc54394810015d4 [0x200c220018]) (lf 0xdd94394810011f4 [0xa0031])))) (nd (nd (nd (lf 0xdc95394810015b4 [0x2f0018010f]) (lf 0x94d639481001974 [0x90018])) (nd (lf 0x5c46050c1001bc4 [0xa0018]) (lf 0x9c46050c1001bc4 []))) (nd (nd (lf 0x54c6050c1001b64 [0xd0b000a]) (lf 0x1846050c1001bc4 [0xd010018000c,0xa0006])) (nd (lf 0xd846050c1001bc4 [0x60a02000c]) (lf 0x5c86150c1001794 [0x180111090c,0x8060e02]))))) (nd (nd (nd (lf 0x9c86150c1001794 [0xd0100100e02]) (nd (lf 0x5d76150c10013d4 [0x20002a]) (lf 0x5d76250c10011f4 [0x310018010f]))) (nd (nd (lf 0x5515350c1001c74 [0x250e02000a,0x90b]) (lf 0x9c86550c10015b4 [0xd0100040007])) (nd (lf 0x9d86550c10011f4 [0x4010c]) (lf 0xdc96550c10013b4 [0x10f0e020018])))) (nd (nd (nd (lf 0x5c83154c1001514 [0x30f0e020812]) (lf 0x5c83154c1001554 [0xe02080c0311])) (nd (lf 0x9c33254c1001564 [0x30f080c0017,0xc0608220301]) (lf 0x5d6628c210011c4 [0x26001d0d01]))) (nd (nd (lf 0x1c1644ca10013c4 [0x6020005]) (lf 0x54a6014a1001984 [0xe0026001d])) (nd (lf 0xdd95214a1001194 [0xd000e0e02]) (lf 0x9414354a1001dc4 [0x30c0b01090f,0x402090b001d])))))
def F7T5_7 := nd (nd (nd (nd (lf 0x1d94354a10013d4 [0x5002f0122]) (nd (lf 0x9c35354a10015c4 [0x322000d0026,0x50d01]) (lf 0x1c16394a10013c4 [0x106001d080e]))) (nd (nd (lf 0x9c36250e10013c4 [0xd0b0d010005,0x10f]) (lf 0x94e60d4e1001944 [0x18000d0701])) (nd (lf 0xdd660d4e10019c4 [0xd07010018]) (lf 0x50c218c21001f44 [0x30b000e0322,0x26])))) (nd (nd (nd (lf 0x590218c21001bc4 [0xb0b080e0106,0xa]) (lf 0xd90218c21001bc4 [0xa080e0122])) (nd (lf 0x9ca618c21001384 [0x122080e]) (lf 0x5db520861001194 [0xd000e0e02]))) (nd (nd (lf 0xdc9430861001794 [0x1e000f0018]) (lf 0xdd94308610013d4 [0x50002])) (nd (lf 0xdd94388610013d4 [0x20007002f,0x20c0005]) (lf 0x9c35388610015c4 [0x22000d0026,0x50d01]))))) (nd (nd (nd (lf 0x1c1644ca10013e4 [0x2000a0c0e]) (nd (lf 0xdc94394a10015b4 [0x1e00200031]) (lf 0xdd94394a10011f4 [0x31]))) (nd (nd (lf 0x9c36250e10013e4 [0x31010f000a,0x2]) (lf 0x5ce524c71001d24 [0xd01080a0c20,0x22])) (nd (lf 0x9da524c710019a4 [0x50c0f0b080a,0xd010506]) (lf 0xd8a524c710019a4 [0x222010f0d01,0x506050b])))) (nd (nd (nd (lf 0x9da524c710011e4 [0xf0b0d01080a,0xc200006]) (lf 0x592524cb10019a4 [0x420000a050c,0x822070b])) (nd (lf 0xd92524cb10019a4 [0xa0a070b0506,0x420]) (lf 0xdd5644cb10011e4 [0xd01000a0009,0x6]))) (nd (nd (lf 0x5d94394b10015a4 [0xa0a0e030c,0x4220b0b0220]) (lf 0xdd94394b10015a4 [0xb0b0b010009])) (nd (lf 0xcc56394b1001d24 [0x301]) (lf 0xdd16394b10015a4 [0x70b0004])))))
def F7T5_8 := nd (nd (nd (nd (lf 0xdc94394b10015a4 [0xc0a010f0422,0xb0b0b010220]) (nd (lf 0x5d76250f10011e4 [0xd0b0d010009,0xa]) (lf 0xd51210853001d84 [0x406080e001d]))) (nd (nd (lf 0x1d5210853001584 [0x1d0e010021]) (lf 0x1c46548530019c4 [0x202])) (nd (lf 0x9d85250530019a4 [0xe010d0b0c0e,0x50a]) (lf 0x9d85250530011e4 [0xa020d0b0c0e,0xa0e01])))) (nd (nd (lf 0x5d85290530019a4 [0xc160e01050d]) (nd (lf 0x50d210863001f04 [0xe0007]) (lf 0x551210863001d84 [0x80e06060612,0x4]))) (nd (nd (lf 0xd51210863001d84 [0x80e04060007,0x70b]) (lf 0xdd9210863001784 [0x10a0e010032,0x9])) (nd (lf 0x1d9434863001364 [0x111002d]) (lf 0x9db5448630011e4 [0x70a060031,0x2a0018]))))) (nd (nd (nd (lf 0x9ca318863001704 [0x122010a020c]) (nd (lf 0x596318863001944 [0xf0b00170015,0x80e090a]) (lf 0x1c9438863001724 [0x1220111]))) (nd (nd (lf 0xdd9438863001364 [0x20c010a0111]) (lf 0x5db5488630011e4 [0xa002f0007])) (nd (lf 0x9da5250630011e4 [0xa0a150812]) (lf 0x50c219023001e64 [0x401030a001b,0x40200170322,0x33])))) (nd (nd (nd (lf 0x486600863001b84 [0x1d002c]) (lf 0x50e600863001b64 [0x106010a001d])) (nd (lf 0x5526008630019e4 [0x8020006002c,0x1d090b]) (lf 0xd526008630019e4 [0x8020018000a,0x22]))) (nd (nd (lf 0x50d210863001f14 [0x60b0602001b]) (lf 0x551210863001d94 [0x2c06060612,0x80e])) (nd (lf 0xd51210863001d94 [0x80e0018]) (lf 0xdd9210863001394 [0xe0b0e010e02,0x5001b])))))
def F7T5_9 := nd (nd (nd (nd (lf 0x5db5408630011f4 [0x7]) (nd (lf 0x1d9434863001374 [0xa0b0002001b,0x1]) (lf 0x9db5448630011f4 [0x18002a040e]))) (nd (nd (lf 0xc86608863001b84 [0x50e02002c]) (lf 0x50e608863001b64 [0x60b0026])) (nd (lf 0x5526088630019e4 [0xa0802002c,0x80106010420]) (lf 0xd526088630019e4 [0x2a000f060c,0x4220802])))) (nd (nd (nd (lf 0x50f218863001f14 [0x60b001b0602]) (lf 0x553218863001d94 [0x34002c])) (nd (lf 0xd53218863001d94 [0x18002a]) (lf 0xdd9438863001374 [0x2001b]))) (nd (nd (lf 0x5db5488630011f4 [0x1110018]) (lf 0x9486050630019e4 [0x40a00200022,0x6010015])) (nd (lf 0x9da5250630011f4 [0x28002f]) (lf 0x1c1219402101584 [0x10]))))) (nd (nd (nd (lf 0x1c1219402101d84 [0x20d001d020e]) (nd (lf 0x50d219402101d94 [0x80a00100018,0x40c07010702]) (lf 0x1d9219402101194 [0x10]))) (nd (nd (lf 0x1d9219402101994 [0xf01001d0018,0xf0b040c0019,0x406001a]) (lf 0xdc54394021015d4 [0xc220005002a])) (nd (lf 0x1d94394021011f4 [0x70005]) (lf 0xd94604842101b84 [0xd000e0008,0xa])))) (nd (nd (nd (lf 0xdd4604842101d84 [0x80d080e001d]) (lf 0x50c604842101b94 [0x60c00100701,0x702070b])) (nd (lf 0x5cc604842101b94 [0x60c0014000e]) (lf 0xdcc604842101b94 [0xe0005]))) (nd (nd (lf 0xd94604842101994 [0xd000e0b02,0x5]) (lf 0xd97604842101984 [0xd000e0b02,0xa])) (nd (lf 0x1c1434842101794 [0xa030c0018,0xf]) (lf 0x54d434842101f14 [0x40a0b0b0004])))))
def F7T5_10 := nd (nd (nd (nd (lf 0xd95434842101994 [0x250b0b0b01,0xb02]) (nd (lf 0xd95434842101b94 [0xb01040a0007,0xb0b0004]) (lf 0x5d5434842101794 [0xf03020007]))) (nd (nd (lf 0xdd5434842101794 [0xf020c0007]) (lf 0x1d9434842101394 [0x1e0b0b0b01,0x20c0c0a])) (nd (lf 0x1d9434842101b94 [0xb010007001e,0xf0b0b]) (lf 0x1c1534842101584 [0x212080e])))) (nd (nd (nd (lf 0x1c1534842101594 [0x1d0212080e]) (lf 0x1c1534842101784 [0x80a080e0035])) (nd (lf 0xdd1534842101794 [0x212080a0306]) (lf 0xd95534842101994 [0x35000e001d,0x1c002e0b0b]))) (nd (nd (lf 0x9db534842101194 [0x1d0036]) (lf 0x1c3654842101994 [0xf0b0f01001d,0x5001a0019])) (nd (lf 0x5c3654842101984 [0x7020037001c]) (lf 0x9c3654842101184 [0x25]))))) (nd (nd (nd (lf 0x9c3654842101984 [0x2e0f0b001c,0x1d00370f01]) (nd (lf 0x9c3654842101194 [0x1d0010]) (lf 0x9c3654842101994 [0xf0b0f01001d,0x5001a0019]))) (nd (nd (lf 0x5cf654842101994 [0x9002e000e,0x70b0702]) (lf 0xdcf654842101994 [0x1c002e000e,0x70b0702])) (nd (lf 0x1c3654842101d94 [0x90018001d]) (lf 0x5c3654842101d84 [0x80d080e0009,0x702])))) (nd (nd (nd (lf 0x9c3654842101584 [0x80a080d080e,0xa]) (lf 0x9c3654842101d84 [0x80d080e0009,0xa080a])) (nd (lf 0x9c3654842101594 [0x80d080e0018,0x5001d]) (lf 0x9c3654842101d94 [0x18080f001d]))) (nd (nd (lf 0x9c3654842101384 [0xf0b001c080a,0x370f01002e]) (lf 0x9c3654842101b84 [0x80a0037001c])) (nd (lf 0x5cf654842101b94 [0x90007000e]) (lf 0xdcf654842101b94 [0xe001c])))))
def F7T5_11 := nd (nd (nd (nd (lf 0x9c3654842101784 [0x80d080a080e]) (nd (lf 0x9c36548421011c4 [0x82208150811]) (lf 0x9c36548421019c4 [0x811001d0815]))) (nd (nd (lf 0x9c36548421011e4 [0x80f0820080a,0x6000c0822]) (lf 0x5da528842101194 [0xd000e001d])) (nd (lf 0x5d46050c21011f4 [0xa000c0002,0x20]) (lf 0x9c06150c21017c4 [0xd01080c])))) (nd (nd (nd (lf 0x1886150c2101b94 [0xa0a0106010c,0xe0d01]) (lf 0xd886150c2101b94 [0xa0a0106010c,0x1e000f])) (nd (lf 0x9c36150c21013d4 [0xf0005]) (lf 0x5d76150c21011d4 [0x50024]))) (nd (nd (lf 0x5d76150c21013d4 [0x20002f]) (lf 0xd8b6150c2101b94 [0x1e00240007,0xf])) (nd (lf 0x5515350c2101c74 [0x220d02000a,0x90b]) (lf 0x9c06550c21015e4 [0x60d01000c]))))) (nd (nd (nd (lf 0x9d86550c21011f4 [0x7]) (nd (lf 0x1c16550c21013e4 [0xc0e0c110102]) (lf 0x9c36550c21011e4 [0xd0b00220007]))) (nd (nd (lf 0x9c36550c21011f4 [0xb00010005]) (lf 0x9ca6114121015a4 [0x102])) (nd (lf 0x1c56314121015c4 [0x102]) (lf 0x1c13114121015c4 [0xc060c0f0b01])))) (nd (nd (nd (lf 0x1c14314121015e4 [0x20a0c02000c,0x60222]) (lf 0x1d94314121011f4 [0xa0020001e,0x1000b])) (nd (lf 0xdd94314121011f4 [0x210002002d]) (lf 0x1c8604c52101b84 [0x10c080d0013]))) (nd (nd (lf 0x9d7648c521011d4 [0x260024]) (lf 0x9d46050d21011f4 [0xc002a0018,0x2])) (nd (lf 0x9c06550d21011e4 [0x5080e0811]) (lf 0x9c06550d21011f4 [0x5])))))
def F7T5_12 := nd (nd (nd (nd (lf 0x5d7215422101584 [0x1500110d02]) (nd (lf 0x9db215422101384 [0x1d0811]) (lf 0x50f219422101d84 [0x25070b020e,0x26002a]))) (nd (nd (lf 0xd8f219422101d84 [0x50026002c]) (lf 0x9db219422101984 [0xf0b001d002b,0x2c0f01002e,0x26])) (nd (lf 0x9db219422101584 [0x260010]) (lf 0x9db219422101d84 [0x26020d020e])))) (nd (nd (nd (lf 0x9db2194221015c4 [0x811001d0815]) (lf 0x5d13194221015c4 [0x30c02220220,0x5070b])) (nd (lf 0xdd13194221015c4 [0x306020d]) (lf 0x1d93194221019c4 [0xf0b0c0f0013]))) (nd (nd (lf 0x1d93194221015c4 [0x81500260005,0x306]) (lf 0xdd93194221019c4 [0x13002f])) (nd (lf 0x1d93194221011e4 [0x6080a0815,0xf0b]) (lf 0x9ca319422101584 [0xb0102220026]))))) (nd (nd (nd (lf 0x5d23194221015c4 [0x3060312020e]) (nd (lf 0x5cc619422101544 [0x31200260222]) (lf 0x5cc6194221015c4 [0x222030c0014]))) (nd (nd (lf 0x1c94394221015a4 [0xb0b0b010222,0x5001e0220]) (lf 0x1c9439422101da4 [0xb01020e030c,0xf001f])) (nd (lf 0xd876394221019c4 [0x8150010]) (lf 0x5d7219422101584 [0x1500110026])))) (nd (nd (nd (lf 0x5d7219422101d84 [0x26020d020e]) (lf 0x9db219422101b84 [0x1d08110815,0x26])) (nd (lf 0x9c3219422101584 [0x10]) (lf 0x50f219422101d94 [0x702002a0010,0x20e]))) (nd (nd (lf 0x1c13194221015c4 [0x30600260815,0xc06]) (lf 0x1c14394221015e4 [0x220000a002a,0xc])) (nd (lf 0x1d94394221011f4 [0xa00070005]) (lf 0x1c143c862101794 [0x18002a])))))
def F7T5_13 := nd (nd (nd (nd (lf 0x9c165c862101d84 [0x26080d080e]) (nd (lf 0xdd4604c621019c4 [0xc150d010005,0x6060f0b]) (lf 0xd94604c621019c4 [0x6060415]))) (nd (nd (lf 0xd94604c621019d4 [0x50415]) (lf 0x1c1644c621013c4 [0x1060c150018])) (nd (lf 0x9c2628c62101384 [0xd01001d080a]) (lf 0x5d46050e21011f4 [0xf002f])))) (nd (nd (nd (lf 0x9c06250e21013a4 [0xd01001d0811,0x1e]) (lf 0x9c36550e21011e4 [0xd0b000a000c])) (nd (lf 0x9c36550e21011f4 [0x5]) (lf 0x989411413101dc4 [0x250215]))) (nd (nd (lf 0x5ca6114131015a4 [0x102]) (lf 0x9ca6114131015a4 [0x102])) (nd (lf 0x1d94214131011e4 [0x22080d0013]) (lf 0xdd94214131011e4 [0x180e01080d,0x22]))))) (nd (nd (nd (lf 0x9c64214131015c4 [0x22020a0216,0x30f]) (nd (lf 0x5d06214131014e4 [0x2202160013,0x18]) (lf 0x1c56214131015c4 [0x306020a0601]))) (nd (nd (lf 0xdd16214131014e4 [0x903060215]) (lf 0x9c66214131015c4 [0x102])) (nd (lf 0xd8a6214131019a4 [0x6160025001c]) (lf 0x1c56414131015c4 [0x102])))) (nd (nd (nd (lf 0x1c96414131015a4 [0x1d0e010010]) (lf 0x1c96414131015e4 [0x240035080d,0x22])) (nd (lf 0xdc96414131015a4 [0x80d0215]) (lf 0x98b5214131019a4 [0x1220a160215]))) (nd (nd (lf 0x5ca6514131015a4 [0x102]) (lf 0x9ca6514131015a4 [0x102])) (nd (lf 0x9c02014131015a4 [0x102]) (lf 0xdd12014131014e4 [0x102])))))
def F7T5_14 := nd (nd (nd (nd (lf 0x9c22014131015a4 [0x102]) (nd (lf 0x9c22014131015e4 [0x20a00200215,0x22]) (lf 0x507201413101dc4 [0x6010018]))) (nd (nd (lf 0x50f201413101d64 [0x30b0026]) (lf 0x5db2014131015e4 [0x200302])) (nd (lf 0x1c94014131015a4 [0x102]) (lf 0x1c94014131015e4 [0x110026080d,0x22])))) (nd (nd (nd (lf 0xdc94014131015a4 [0x102]) (lf 0x50e401413101c74 [0x26030b])) (nd (lf 0x1c14114131015c4 [0xc0f0b0b0e01,0x30f]) (lf 0x1c14214131015e4 [0x20a0216080d,0x822000f]))) (nd (nd (lf 0x50d421413101c74 [0x80f]) (lf 0x1d94214131011f4 [0xa0005080d,0x6])) (nd (lf 0xdd94214131011f4 [0x80d0025]) (lf 0x9c24214131015e4 [0xc020022080d,0x20a]))))) (nd (nd (nd (lf 0x9c06214131015e4 [0x30200220018]) (nd (lf 0x5886214131019b4 [0x5]) (lf 0x5d06214131014f4 [0x2200180005]))) (nd (nd (lf 0xdd16214131014f4 [0x25]) (lf 0xd8a6214131019b4 [0x2f0005])) (nd (lf 0x9c36214131015e4 [0x20a00200215,0x302002f]) (lf 0xd91431413101c74 [0xd])))) (nd (nd (nd (lf 0x98b5214131019b4 [0x2f00130820,0x2a]) (lf 0x98b52d4131019a4 [0xb0b01220215])) (nd (lf 0x195435093101874 [0xb00130016]) (lf 0x9c06550931011f4 [0x13080d]))) (nd (nd (lf 0x9c26190931013c4 [0x8220816080d,0xc12]) (lf 0xd4260d4931019e4 [0xf00020601])) (nd (lf 0x1c86055131019a4 [0xe01080d0005]) (lf 0x1c86055131019e4 [0x2200180820,0x601000c0005,0x70b0006])))))
def F7T5_15 := nd (nd (nd (nd (lf 0x5c86055131019e4 [0x500200009,0x70b000c0601,0x220006]) (nd (lf 0x9c86055131019e4 [0x500220018]) (lf 0xdc86055131019a4 [0xe0108200005,0x806]))) (nd (nd (lf 0xdc86055131019e4 [0x2200050615]) (lf 0x4806055131019e4 [0x302])) (nd (lf 0xc806055131019e4 [0xf00220018,0x5]) (lf 0x9c36255131011b4 [0x7020005])))) (nd (nd (nd (lf 0x9c21014143015c4 [0xc0f00020005]) (lf 0x9c21014143015e4 [0x20000a000c,0x6])) (nd (lf 0x9cb1014143015a4 [0x102]) (lf 0x9cb1014143015e4 [0xc00090022,0x6]))) (nd (nd (lf 0x5db1014143015e4 [0x20006000c]) (lf 0x9c06114143015e4 [0xa001e])) (nd (lf 0x5846114143019d4 [0x40c001e]) (lf 0x5c86114143015b4 [0xa0c0c0005]))))) (nd (nd (nd (lf 0x9c86114143015b4 [0xc0c0005]) (nd (lf 0x1c96114143015b4 [0x200005]) (lf 0xdc96114143015b4 [0x50c0c0018]))) (nd (nd (lf 0xd866114143019d4 [0x70005]) (lf 0x9c36114143015e4 [0xc00070302,0x6])) (nd (lf 0x9cb1014143017a4 [0x20e01]) (lf 0x5c85114143015b4 [0x5080c0018,0xa080e])))) (nd (nd (nd (lf 0x9c85114143015b4 [0xe010005080c]) (lf 0x9875114143019d4 [0x250007])) (nd (lf 0x14a6014543019e4 [0x220026040e,0x60b0e01]) (lf 0xd4a6014543019e4 [0xa040e0031]))) (nd (nd (lf 0x98b5214543019b4 [0x8060031]) (lf 0x48260d4543019e4 [0x302])) (nd (lf 0xd4260d4543019e4 [0x302]) (lf 0x9c752d4543015d4 [0x240007])))))
def F7T5 : BTree NodeData := nd (nd (nd (nd F7T5_0 F7T5_1) (nd F7T5_2 F7T5_3)) (nd (nd F7T5_4 F7T5_5) (nd F7T5_6 F7T5_7))) (nd (nd (nd F7T5_8 F7T5_9) (nd F7T5_10 F7T5_11)) (nd (nd F7T5_12 F7T5_13) (nd F7T5_14 F7T5_15)))
def F7M5 : BST := BN 291834311 9600 (BN 245227756 641 (BN 208968353 7168 (BN 192460878 14080 (BN 164966224 12160 (BN 159027718 4354 (BN 128061294 5120 (BL 118732171 8064) BE) (BL 160208492 6528)) (BN 186040231 16256 (BL 168626651 2) (BL 189510211 1024))) (BN 197952555 7424 (BN 196607490 9985 (BN 195717500 1792 (BL 195527286 11904) BE) (BL 197673721 15361)) (BN 205049834 12033 (BL 203623835 1026) (BL 207771657 3200)))) (BN 223293875 14336 (BN 218479326 6144 (BN 212066179 7426 (BN 210911325 7681 (BL 209912690 15360) BE) (BL 216868158 4480)) (BN 222347018 5505 (BL 219403170 4737) (BL 222728867 3072))) (BN 229838637 6784 (BN 228345644 0 (BN 226195856 15488 (BL 225310502 12672) BE) (BL 229338827 10112)) (BN 230874420 3841 (BL 230048129 2177) (BL 241351066 14208))))) (BN 263789216 6912 (BN 251942785 13056 (BN 250210976 13184 (BN 247409637 5632 (BN 245651098 7936 (BL 245272653 13440) BE) (BL 248882887 11522)) (BN 250940080 896 (BL 250353189 14592) (BL 251114374 1152))) (BN 258028946 7808 (BN 256889583 10368 (BN 255863173 258 (BL 254362438 2816) BE) (BL 257005045 5504)) (BN 262176921 13952 (BL 259257201 384) (BL 262659548 7680)))) (BN 276927595 128 (BN 273378245 11008 (BN 266973724 11648 (BN 266313587 9856 (BL 264363068 1920) BE) (BL 268485251 5888)) (BN 273526322 16128 (BL 273415536 2560) (BL 274918719 12545))) (BN 287157688 12544 (BN 285118112 13696 (BN 284491328 7552 (BL 283313761 4608) BE) (BL 285295140 3968)) (BN 289576717 12288 (BL 287232203 2048) (BL 290856982 10241)))))) (BN 339152246 11520 (BN 305566990 4736 (BN 298056192 2432 (BN 297715486 9601 (BN 294331298 4096 (BN 292933672 15744 (BL 292340297 1664) BE) (BL 295479778 9090)) (BN 298000259 10240 (BL 297995072 2304) (BL 298019061 6400))) (BN 303145604 6272 (BN 301871483 12928 (BN 301302126 10881 (BL 299783589 14976) BE) (BL 302773642 10496)) (BN 303918906 15872 (BL 303315293 256) (BL 305122307 4352)))) (BN 327381044 7296 (BN 314287378 9344 (BN 313488891 13312 (BN 310122247 6145 (BL 308256066 3586) BE) (BL 313557454 2944)) (BN 325804597 2049 (BL 320776583 9984) (BL 327299296 3712))) (BN 333774247 1280 (BN 331391576 640 (BN 329218927 12032 (BL 327688549 5378) BE) (BL 331424605 14337)) (BN 336954352 14464 (BL 333919328 1408) (BL 338731893 4225))))) (BN 383146666 6016 (BN 364199347 14848 (BN 355043513 3840 (BN 349018761 16000 (BN 344258081 2176 (BL 343128172 6273) BE) (BL 350311892 15616)) (BN 358631673 9728 (BL 357082242 15104) (BL 361592744 5376))) (BN 376523661 5248 (BN 373900457 15106 (BN 371486002 7040 (BL 369724374 4864) BE) (BL 374167545 10624)) (BN 378173757 14720 (BL 378075604 6656) (BL 379785807 11136)))) (BN 411100343 9088 (BN 396409369 4992 (BN 387840515 5760 (BN 387668255 15232 (BL 384075557 13568) BE) (BL 390480116 4224)) (BN 402673824 11776 (BL 397819482 12416) (BL 406930370 3584))) (BN 425815640 11392 (BN 418903166 3456 (BL 412723457 512) (BL 422151866 2688)) (BN 432459770 768 (BL 429491232 10880) (BL 433572023 3328))))))
def F7T6_0 := nd (nd (nd (nd (nd (lf 0x1324841000f83 [0xa03010111,0x20c]) (lf 0x2324841000f83 [0x21600210115,0x1d000a])) (nd (lf 0x524841000d83 [0x40d040e000a,0x206020c]) (lf 0x2524841000fc3 [0xa01220009,0x1110115]))) (nd (nd (lf 0x1434841000fc3 [0x20c000e0021,0x10f]) (lf 0x1534841000dc3 [0x22000e0212,0xa0501])) (nd (lf 0x1534841000fc3 [0xa002d0029,0x70b010f0501,0x1b]) (nd (lf 0x3534841000dc3 [0x22000a0212,0xe]) (lf 0x3654841000dc3 [0xd000e001d,0xa]))))) (nd (nd (nd (lf 0x3654841000bc3 [0x701000a001d,0x21070b]) (lf 0x3654841000fc3 [0xd000e000a,0x1d])) (nd (lf 0x36548410009e3 [0xd000e001d,0xa]) (nd (lf 0x2528841000d83 [0x7010022000a,0x70b]) (lf 0x1628841000bc3 [0xe000a010f,0xd])))) (nd (nd (lf 0x1438841000fc3 [0x20c01110007,0x402030b0301]) (lf 0x1538841000dc3 [0xa0511020c,0x2060022000e])) (nd (lf 0x165c8410009e3 [0xa000d000e]) (nd (lf 0x2524c41000de3 [0xa0222040d,0x501]) (lf 0x624c41000be3 [0x5010020040a,0x1060022070b,0x416])))))) (nd (nd (nd (nd (lf 0x3624c41000be3 [0x501010f040a,0x1060416070b]) (lf 0x3654c410009e3 [0x220017000d])) (nd (lf 0x614c81000fc3 [0x501020a0111,0x20000c]) (nd (lf 0x3614c81000bc3 [0x90501000d]) (lf 0x3614c81000fc3 [0x111000e0009,0xa000c])))) (nd (nd (lf 0x2324c81000f63 [0x70b01220115,0x1601010602]) (lf 0x1524c81000fa3 [0x501020a0111,0x22])) (nd (lf 0x2524c81000da3 [0x20a05120022,0x40e]) (nd (lf 0x2524c81000fa3 [0xa05010009,0x38010f070b,0x4]) (lf 0x1534c81000f63 [0x20a01120009]))))) (nd (nd (nd (lf 0x1644c81000be3 [0x50101110009,0x20000a]) (lf 0x3644c81000be3 [0x10601110004,0x501])) (nd (lf 0x654c81000de3 [0x70b05010009,0x20600040022]) (nd (lf 0x1654c81000be3 [0x501020a0111,0x10b0020]) (lf 0x3654c810009e3 [0x70b05010009,0x60030000a,0x40e])))) (nd (nd (lf 0x3654c81000de3 [0x70b00300009,0xc020a0501]) (lf 0x3654c81000be3 [0x70b05010009,0x3800200602,0x106])) (nd (lf 0x1618c81000bc3 [0x1d000d0115]) (nd (lf 0x1528c81000fa3 [0xa01150021,0x22]) (lf 0x2528c81000fa3 [0x5010122020a,0x23000e070b,0x4]))))))
def F7T6_1 := nd (nd (nd (nd (nd (lf 0x1648c81000be3 [0x11501120004,0x220106]) (lf 0x3648c81000be3 [0x30b01220007,0x20000a])) (nd (lf 0x1658c81000be3 [0x1d01150021]) (lf 0x3658c81000be3 [0x122020a0112,0x20]))) (nd (nd (lf 0x1431481000de3 [0x30b04220007,0x6040a000c]) (lf 0x1631481000963 [0xc0022000a])) (nd (lf 0x2525481000de3 [0x11101150009,0xa]) (nd (lf 0x1535481000de3 [0xa002d001c,0x70b000c000e]) (lf 0x3635481000be3 [0x40a01120115]))))) (nd (nd (nd (lf 0x1439481000de3 [0x40a030b0031,0xa04020422,0xc0220]) (lf 0x1539481000de3 [0x3010031001c,0x22000e000a,0xc])) (nd (lf 0x1639481000be3 [0x40a01120009,0x20]) (nd (lf 0x6150c1000fc3 [0x50b010c020a,0x900080031,0x2005010111]) (lf 0x36150c1000bc3 [0x50b05010021,0x10f0020])))) (nd (nd (lf 0x36150c1000fc3 [0x10c05010021,0xa]) (lf 0x6250c1000be3 [0x50b05010008,0x200122000a])) (nd (lf 0x36250c1000be3 [0x50b05010009,0xa010f]) (nd (lf 0x15350c1000f63 [0x101050b0021,0x20a]) (lf 0x16550c1000be3 [0x200070021,0x20])))))) (nd (nd (nd (nd (lf 0x36550c1000be3 [0x60200070021,0xc0020]) (lf 0x3154c1000d43 [0x101])) (nd (lf 0x33254c1000d63 [0x101]) (nd (lf 0x33254c1000f63 [0x101]) (lf 0x6254c1000be3 [0x70b0122040a,0x10c01010701,0x1060023])))) (nd (nd (lf 0x36254c1000be3 [0x701040a0111,0x101010c]) (lf 0x24354c1000f63 [0x101])) (nd (lf 0x15454c1000de3 [0x501000a001b,0x6000c030b]) (nd (lf 0x36454c1000be3 [0x10601120021]) (lf 0x1438801000f83 [0x3010025]))))) (nd (nd (nd (lf 0x1538801000f83 [0x25]) (lf 0x3538801000f83 [0x3010010])) (nd (lf 0x1638801000f83 [0x1d00100115]) (nd (lf 0x3638801000f83 [0x11101150005]) (lf 0x658801000f83 [0x20a01150111])))) (nd (nd (lf 0x1658801000f83 [0x1d0010]) (lf 0x2658801000f83 [0x1403010010,0x30b])) (nd (lf 0x3658801000f83 [0x2601150111,0x1d]) (nd (lf 0x1328801000f83 [0x301002e]) (lf 0x2328801000f83 [0x1d00250115,0x301]))))))
def F7T6_2 := nd (nd (nd (nd (nd (lf 0x1528801000f83 [0x1d01150111]) (lf 0x2528801000f83 [0x70b001d0025,0x10f002e])) (nd (lf 0x1438801000fc3 [0x1d01110025]) (lf 0x1538801000fc3 [0x280014002e,0x10f001d0029,0x501]))) (nd (nd (lf 0x3538801000fc3 [0x903010010,0x1d010f0028]) (lf 0x1658801000bc3 [0x701001d002e,0x200402070b])) (nd (lf 0x3658801000bc3 [0xd000e010f,0x1d0026]) (nd (lf 0x1329401000fc3 [0x260018002e,0x20]) (lf 0x2329401000fc3 [0xe001d002e,0x115]))))) (nd (nd (nd (lf 0x529401000dc3 [0x260025001d]) (lf 0x1529401000fc3 [0x10f00340029,0x1d000a])) (nd (lf 0x2529401000dc3 [0x26040e001d,0x402070b]) (nd (lf 0x2529401000fc3 [0x2600340029,0x10f]) (lf 0x1629401000bc3 [0x11500260111,0x402])))) (nd (nd (lf 0x1439401000fc3 [0x26000e0025,0x18001d0111]) (lf 0x1539401000dc3 [0x250029000e,0x70b001d0501,0xa0028])) (nd (lf 0x1539401000fc3 [0x2600250029,0xe]) (nd (lf 0x3539401000dc3 [0x70b000e0026,0x1d0025]) (lf 0x604c81000bc3 [0x1d00100501,0x20010f070b])))))) (nd (nd (nd (nd (lf 0x604c81000fc3 [0x1d01110018,0x501]) (lf 0x1524c81000f93 [0x11105010018,0xa])) (nd (lf 0x2524c81000f93 [0x18002e]) (nd (lf 0x1534c81000f53 [0xa0018002e]) (lf 0x1644c81000bd3 [0x11106020018,0xa0501])))) (nd (nd (lf 0x3644c81000bd3 [0x1110025]) (lf 0x1654c81000bd3 [0x60201110018,0x10b0501])) (nd (lf 0x3654c81000bd3 [0x6020018002e,0x20]) (nd (lf 0x2608c81000bc3 [0x10001d0115,0x501]) (lf 0x1528c81000f93 [0x1d01150029,0x1160024]))))) (nd (nd (nd (lf 0x1648c81000bd3 [0x11501120029]) (lf 0x1658c81000bd3 [0x1d01150029,0x1060024070b])) (nd (lf 0x2601481000bc3 [0xa0025001d,0x2070b0701]) (nd (lf 0x1521481000d93 [0x602000a0025,0x7010029070b]) (lf 0x1631481000b53 [0x112000a001d])))) (nd (nd (lf 0x1631481000bd3 [0x10c001d0014,0x301]) (lf 0x1435481000fd3 [0x2800250111,0x2402020018])) (nd (lf 0x1535481000dd3 [0x60203010028,0x1d]) (nd (lf 0x3535481000dd3 [0xa06020028]) (lf 0x3635481000bd3 [0x11501120029]))))))
def F7T6_3 := nd (nd (nd (nd (nd (lf 0x3529481000d93 [0xa0025001d,0x70b0701]) (lf 0x1439481000fd3 [0x40200180025,0x30101220202])) (nd (lf 0x1639481000bd3 [0xe001d002e]) (nd (lf 0x1659481000bd3 [0x111001d0115,0xa]) (lf 0x260d481000bc3 [0x10f00250026,0x70b0701001d])))) (nd (nd (lf 0x153d481000dd3 [0x30100290025]) (lf 0x163d481000bd3 [0x60201120115,0xa])) (nd (lf 0x6050c1000bc3 [0x50b05010018,0x20010f]) (nd (lf 0x6050c1000fc3 [0x11100180025,0x2020501]) (lf 0x6250c1000fd3 [0x50106020025,0x10f0024]))))) (nd (nd (nd (lf 0x36250c1000bd3 [0x10f05010018,0x50b]) (lf 0x36250c1000fd3 [0x60200180111,0x122010c])) (nd (lf 0x15350c1000f53 [0x602050b0025,0xa00180028]) (nd (lf 0x16550c1000bd3 [0x602001d0025,0x10f0024]) (lf 0x36550c1000bd3 [0x2006020025,0x10f0122])))) (nd (nd (lf 0x3054c1000f43 [0x101]) (lf 0x6054c1000fc3 [0x30101120029])) (nd (lf 0x33254c1000f53 [0x101]) (nd (lf 0x36254c1000bd3 [0x70101110018,0x10c]) (lf 0x24354c1000f53 [0x101])))))) (nd (nd (nd (nd (lf 0x5354c1000d53 [0x101]) (lf 0x15454c1000dd3 [0x501030b0025,0x2906020003])) (nd (lf 0x35454c1000dd3 [0x501030b0029,0x14]) (nd (lf 0x36454c1000bd3 [0x60201120014,0x240106]) (lf 0x260d4c1000bc3 [0x70b000a000e,0x10f0025])))) (nd (nd (lf 0x162d4c1000bd3 [0x602000a0111,0x10c0701]) (lf 0x253d4c1000d53 [0x101])) (nd (lf 0x164d4c1000bd3 [0x10601120010,0x240602]) (nd (lf 0x2528401000de3 [0x40d040e0026]) (lf 0x1210801000f83 [0x1d002d0021,0xa07010026]))))) (nd (nd (nd (lf 0x1210801000fc3 [0x111001d0115,0x26]) (lf 0x2210801000fc3 [0x11101220115])) (nd (lf 0x1610801000bc3 [0x1d000d000e,0x4020026]) (nd (lf 0x1610801000fc3 [0x220021002d,0x20a]) (lf 0x2610801000fc3 [0x701020a0122,0x70031070b,0x2000040023])))) (nd (nd (lf 0x1530801000de3 [0x30102120031,0x22000a020e,0xf000e]) (lf 0x3530801000de3 [0x212020a0031,0x22000f000e])) (nd (lf 0x16508010009e3 [0xd000f000e]) (nd (lf 0x1650801000de3 [0x110015001d,0x260402]) (lf 0x1318801000f83 [0x20a070b0025,0x170216002a,0x1d]))))))
def F7T6_4 := nd (nd (nd (nd (nd (lf 0x1318801000fa3 [0x301020a020d,0x1d010f0017]) (lf 0x2318801000f83 [0x3010025020a,0x1d0216070b])) (nd (lf 0x1618801000f83 [0x70b001d0025,0x2e]) (lf 0x1618801000fa3 [0x20d020a020e,0x10f]))) (nd (nd (lf 0x2618801000f83 [0x70b020a0025,0x2e001d]) (lf 0x3618801000fa3 [0x20d0026020e,0x1d])) (nd (lf 0x1438801000fa3 [0x20c020a0025,0x22004020301,0x206]) (nd (lf 0x1538801000da3 [0x14020a0212,0x1d020e0402]) (lf 0x1538801000fa3 [0x402020a0025]))))) (nd (nd (nd (lf 0x3538801000da3 [0x5020a0212,0x1d]) (lf 0x1638801000fa3 [0x1d0025])) (nd (lf 0x3638801000fa3 [0x11501110009,0x20c020a]) (nd (lf 0x1658801000da3 [0x26020e001d,0x20c04020025,0x206]) (lf 0x1658801000fa3 [0x14001d0010,0x26])))) (nd (nd (lf 0x218801000f83 [0x701001d020a,0x2e070b]) (lf 0x1218801000f83 [0xa01150111,0x1d])) (nd (lf 0x1218801000fa3 [0x20d020a020e,0x1d]) (nd (lf 0x2218801000f83 [0x20a01150111,0x402]) (lf 0x3218801000f83 [0x70b002b001d,0x2c0701002e])))))) (nd (nd (nd (nd (lf 0x3218801000fa3 [0x20d020a020e,0x1d010f]) (lf 0x1318801000fc3 [0x115070b001c,0x2160025001d])) (nd (lf 0x2318801000fc3 [0x70b020a0115,0x216001d0025]) (nd (lf 0x1328801000fa3 [0x30101110009,0xe020c020a]) (lf 0x2328801000fa3 [0x70b001d0115,0x30102160025])))) (nd (nd (lf 0x1528801000fa3 [0x111020a0115,0x1d]) (lf 0x2528801000da3 [0x37001c001d,0x20c0402020a,0x206])) (nd (lf 0x2528801000fa3 [0x37001d001c,0x10f020a]) (nd (lf 0x1438801000fe3 [0x1d00250111,0xe040a020c,0x206020a]) (lf 0x1538801000de3 [0x20a001d0028,0x212020e]))))) (nd (nd (nd (lf 0x3538801000de3 [0x22020a0028]) (lf 0x1638801000be3 [0x112001d0115,0x402])) (nd (lf 0x3638801000be3 [0x111010c0009,0x20000a]) (nd (lf 0x16588010009e3 [0xd000e001d]) (lf 0x1658801000be3 [0xd000e0026,0x1d])))) (nd (nd (lf 0x1218c01000fc3 [0x170115002d,0x50b0416040c,0x21]) (lf 0x2218c01000fc3 [0x1705010018,0x50b0416040c,0x30b0004])) (nd (lf 0x1618c01000bc3 [0x501002d000d,0x10f]) (nd (lf 0x2328c01000f63 [0x112001d0007,0x4020015]) (lf 0x1428c01000fe3 [0xe00390115,0x40a000d010c,0x170206020a]))))))
def F7T6_5 := nd (nd (nd (nd (nd (lf 0x528c01000de3 [0x1602220007,0xc0501020b,0x4050b]) (lf 0x2528c01000de3 [0x20a02220039,0x20f00020420,0xc])) (nd (lf 0x1628c01000be3 [0x10f05010009,0xc0402070b,0x1060416]) (nd (lf 0x2628c01000be3 [0x70b05010008,0x4160020000a,0x106]) (lf 0x1438c01000f63 [0xd030b0007,0x310211010c,0x1d])))) (nd (nd (lf 0x1538c01000f63 [0x20a0112002d,0x501]) (lf 0x1648c01000be3 [0x11205010021])) (nd (lf 0x3648c01000be3 [0x2001120007,0xa05010018,0x10f00310415,0x122]) (nd (lf 0x1520841000d93 [0x1506020011,0xa]) (lf 0x1430841000fd3 [0x12204020025,0x30100110202,0xa010b]))))) (nd (nd (nd (lf 0x1630841000bd3 [0x15001d002e]) (lf 0x604841000fc3 [0xd000e0018,0x10f001d])) (nd (lf 0x1324841000f93 [0x11103010018,0xa020c]) (nd (lf 0x2324841000f93 [0x216001d0115,0x4200021070b,0x116]) (lf 0x524841000d93 [0x40e000a0602,0x206020c040d])))) (nd (nd (lf 0x1434841000fd3 [0x20c00210111,0x2060018001d,0x10c]) (lf 0x1534841000dd3 [0x60203010028,0x22020c])) (nd (lf 0x3534841000dd3 [0x20c00180028]) (nd (lf 0x1634841000bd3 [0x602000d0018,0x10b0301010f]) (lf 0x3634841000bd3 [0x60201120115,0xe])))))) (nd (nd (nd (nd (lf 0x2528841000d93 [0x22000a0602,0x70b0701]) (lf 0x1628841000bd3 [0xd000e001d,0x10f])) (nd (lf 0x1438841000fd3 [0x1800250111,0x402020c001d,0x10b0206010c]) (nd (lf 0x1538841000dd3 [0x30106020028]) (lf 0x1638841000bd3 [0x60201120115,0xa])))) (nd (nd (lf 0x132c841000f93 [0x2e0602000e,0x122000a]) (lf 0x352c841000d93 [0x11001d])) (nd (lf 0x143c841000fd3 [0x40201220025,0x30100110202,0xa010c]) (nd (lf 0x153c841000fd3 [0x10c002b0301,0x140402000e]) (lf 0x163c841000bd3 [0xe001d002e]))))) (nd (nd (nd (lf 0x165c841000bd3 [0x701000a001d,0x10c0020070b,0x106]) (lf 0x165c8410009f3 [0xd000e001d,0xa])) (nd (lf 0x1524c41000fd3 [0x501001d0115,0x10c000a]) (nd (lf 0x2524c41000fd3 [0x180122001c,0x20f000a0420]) (lf 0x624c41000fd3 [0x15001c002e,0x10f0602])))) (nd (nd (lf 0x3624c41000bd3 [0x10f05010018,0x1060416070b]) (lf 0x3624c41000fd3 [0x10c06020115,0x122])) (nd (lf 0x1644c41000bd3 [0x602001d0025,0x10f0415]) (nd (lf 0x3644c41000bd3 [0x602000d0025,0x415]) (lf 0x2524c41000df3 [0x1c02220420,0x17000a]))))))
def F7T6_6 := nd (nd (nd (nd (nd (lf 0x3624c41000bf3 [0x20002d010f,0x17000a]) (lf 0x1628c41000bd3 [0x60205010111,0xa])) (nd (lf 0x1648c41000bd3 [0x60201120025,0x415]) (lf 0x604c81000be3 [0x10f001d0501,0x25070b040e,0xf0020000a,0x3001060416]))) (nd (nd (lf 0x604c81000fe3 [0x1d0030010f,0x501000e020a,0xc]) (lf 0x614c81000fd3 [0xe0602010f,0xc0018])) (nd (lf 0x3614c81000bd3 [0x5010602000d,0xa002d010f]) (nd (lf 0x3614c81000fd3 [0xe0602010f,0xa000c]) (lf 0x1524c81000fb3 [0x18000a010f,0x501000e0602,0x22]))))) (nd (nd (nd (lf 0x2524c81000db3 [0x50100220602,0xa0038040e,0xe050c070b,0x206]) (lf 0x2524c81000fb3 [0x180009000a,0x10f040e0602,0x501])) (nd (lf 0x1434c81000f73 [0x206040f030b,0x1d000d]) (nd (lf 0x1534c81000f73 [0x180009000a,0xe]) (lf 0x1644c81000bf3 [0xa0602010f,0xc00200018,0x60b00060401])))) (nd (nd (lf 0x3644c81000bf3 [0x2501060111,0x401000c0602]) (lf 0x654c81000df3 [0x1600090018,0x20b00220030])) (nd (lf 0x1654c81000bf3 [0x1800200602,0x10b010f]) (nd (lf 0x3654c810009f3 [0x70b05010602,0x90018040e,0x6002e0038,0xa0020]) (lf 0x3654c81000df3 [0x5010030010f,0xa000c0018])))))) (nd (nd (nd (nd (lf 0x3654c81000bf3 [0x1800200602,0x10f040e0009]) (lf 0x2608c81000be3 [0x70b001d0115,0x50104160025])) (nd (lf 0x1618c81000bd3 [0x1d000d0115]) (nd (lf 0x1528c81000fb3 [0xa00070115,0x290122]) (lf 0x1648c81000bf3 [0x1d01120115,0x1060029])))) (nd (nd (lf 0x1658c81000bf3 [0x701150602,0x29010c]) (lf 0x1431481000df3 [0x25000a0007,0x4000c0301,0x600220202,0xb])) (nd (lf 0x1631481000973 [0xa06020012,0x22]) (nd (lf 0x1535481000df3 [0x2d06020301,0x1d001c000a,0xc000f0029]) (lf 0x3635481000bf3 [0x29010c0115,0x602]))))) (nd (nd (nd (lf 0x1439481000df3 [0xe00310422,0x4020023000c,0x301000a0202,0xb0006]) (lf 0x1539481000df3 [0x2900310301,0x22000c001c])) (nd (lf 0x1639481000bf3 [0x602000e010c,0x3a00090018,0xa]) (nd (lf 0x6050c1000be3 [0xa050b0501,0xc00180020,0x10f01220602,0x6]) (lf 0x6050c1000fe3 [0x50b0501010c,0x6000e020a,0x2])))) (nd (nd (lf 0x6150c1000fd3 [0x1060025010c,0x10b05010602,0x20]) (lf 0x36150c1000bd3 [0x2005010602,0x10f0021050b,0x122])) (nd (lf 0x36150c1000fd3 [0x1060025010c,0xa000e0602]) (nd (lf 0x36250c1000bf3 [0xa0021010f,0xc00200018,0x40b00060401]) (lf 0x15350c1000f73 [0x40025000a,0x101010c050b]))))))
def F7T6_7 := nd (nd (nd (nd (nd (lf 0x6550c1000df3 [0x50100110007,0x1e00040025]) (lf 0x16550c1000bf3 [0x2500200602,0x40e0106010c,0x1d])) (nd (lf 0x36550c10009f3 [0x50b05010602,0x2200200021,0x25000f]) (nd (lf 0x36550c1000df3 [0x40501010c,0xa]) (lf 0x36550c1000bf3 [0x700250602,0x10c00200004])))) (nd (nd (lf 0x3154c1000d53 [0x101]) (lf 0x33254c1000d73 [0x101])) (nd (lf 0x3054c1000f63 [0x101]) (nd (lf 0x33254c1000f73 [0x2d0014000e,0xa]) (lf 0x36254c1000bf3 [0xa002d010f,0x2b00180101]))))) (nd (nd (nd (lf 0x24354c1000f73 [0x101]) (lf 0x15454c1000df3 [0x30b05010003,0xc06020025,0x6])) (nd (lf 0x36454c1000bf3 [0x1401060112,0x40e0602]) (nd (lf 0x2328c21000f43 [0xe001d0112,0x26]) (lf 0x1428c21000fc3 [0x40e01160112,0x26001d0017])))) (nd (nd (lf 0x2428c21000fc3 [0x501001d0112,0x26040e]) (lf 0x1528c21000fc3 [0x2605010034,0x17010c])) (nd (lf 0x2528c21000fc3 [0xe001d0034]) (nd (lf 0x2628c21000bc3 [0x3405010122,0x260106]) (lf 0x1538c21000f43 [0x26000e0112])))))) (nd (nd (nd (nd (lf 0x1548c21000fc3 [0x260034]) (lf 0x1648c21000bc3 [0x10600340112])) (nd (lf 0x3648c21000bc3 [0x1805010106,0x260122]) (nd (lf 0x604ca1000bc3 [0x1d05010025,0x260106010f]) (lf 0x604ca1000fc3 [0x11105010018,0x202])))) (nd (nd (lf 0x1644ca1000bd3 [0x26010f0025,0x20]) (lf 0x3644ca1000bd3 [0x10601110025])) (nd (lf 0x1648ca1000bd3 [0x2501120029]) (nd (lf 0x26014a1000bc3 [0xd000e001d]) (lf 0x15214a1000d93 [0xe0026]))))) (nd (nd (nd (lf 0x14354a1000fd3 [0x1d00180025,0x10c000e0402,0x26010b]) (lf 0x35354a1000dd3 [0x301000d0018])) (nd (lf 0x36354a1000bd3 [0x10c0115002e]) (nd (lf 0x35294a1000d93 [0xd000e001d]) (lf 0x14394a1000fd3 [0x2600180025,0x122000e0402])))) (nd (nd (lf 0x16394a1000bd3 [0x1d002e]) (lf 0x260d4a1000bc3 [0x1d000d000e,0x2010f0005])) (nd (lf 0x6250e1000fd3 [0x10c06020025,0x10f00240501]) (nd (lf 0x36250e1000bd3 [0x50b05010018,0x602]) (lf 0x36250e1000fd3 [0x10c06020025,0x1220501]))))))
def F7T6_8 := nd (nd (nd (nd (nd (lf 0x5354e1000d53 [0x101]) (lf 0x260d4e1000bc3 [0x10c0018000d,0x1220701])) (nd (lf 0x162d4e1000bd3 [0x10f0602000d,0x101010c]) (lf 0x253d4e1000d53 [0x101]))) (nd (nd (lf 0x218c21000fc3 [0x10c000e001d,0x170116030b]) (lf 0x2218c21000fc3 [0x40c05010034,0x17010c])) (nd (lf 0x2318c21000f43 [0x15000e0112]) (nd (lf 0x2418c21000fc3 [0x112020d0116,0x3b0211]) (lf 0x2618c21000bc3 [0xa000e003c,0x1060122070b]))))) (nd (nd (nd (lf 0x2328c21000f63 [0x1d000e0112,0x15]) (lf 0x2528c21000de3 [0x222000e0031,0x206020b0023])) (nd (lf 0x2628c21000be3 [0x260501003b]) (nd (lf 0x1438c21000f63 [0x30b0026003c,0x1d00310211]) (lf 0x1648c21000be3 [0x340106040e,0x230415000a,0x120122])))) (nd (nd (lf 0x3648c21000be3 [0xa0106040e,0x3104150018,0x122]) (lf 0x1329421000de3 [0x40a000e0009,0xc0022070b,0x40406])) (nd (lf 0x2329421000de3 [0x40a000e001d,0x40406070b]) (nd (lf 0x1439421000de3 [0x30b000e040a,0xc0009001d,0x4220301]) (lf 0x3520861000d93 [0xd000e001d])))))) (nd (nd (nd (nd (lf 0x1430861000fd3 [0x26000e0025,0x10b01220402]) (lf 0x1630861000bd3 [0x6020122002e,0xe040f])) (nd (lf 0x2524861000d93 [0x6020022000e,0xd]) (nd (lf 0x1438861000fd3 [0xe00180025,0x402040a001d,0x20c010b010c]) (lf 0x3538861000dd3 [0xd020c0018])))) (nd (nd (lf 0x1638861000bd3 [0x10c0115002e]) (lf 0x152c861000d93 [0xf0602000e])) (nd (lf 0x3624c61000bd3 [0x5010602000d,0x10f]) (nd (lf 0x604ca1000be3 [0xa040e003a,0x4160025070b,0x106]) (lf 0x614ca1000fd3 [0x220000f003a,0x18020a]))))) (nd (nd (nd (lf 0x1434ca1000f73 [0x6020420030b,0x206001d003c]) (lf 0x1644ca1000bf3 [0x250026040e,0x90602])) (nd (lf 0x3644ca1000bf3 [0x2501110106,0x40e00040602]) (nd (lf 0x3654ca1000df3 [0x180030000e]) (lf 0x1648ca1000bf3 [0x250112040e,0x600040602])))) (nd (nd (lf 0x14394a1000df3 [0x31000e0422,0x260023000c,0xb0006]) (lf 0x6150e1000fd3 [0x25001e010c,0x501020a0106,0x20010b])) (nd (lf 0x36250e1000bf3 [0x200026010f,0x906020018]) (nd (lf 0x36550e1000df3 [0x25000e010c,0x1e]) (lf 0x33154e1000d53 [0x101]))))))
def F7T6_9 := nd (nd (nd (nd (nd (lf 0x260d4e10009e3 [0xc001c000d,0x22]) (lf 0x2524871000da3 [0xa040d040e])) (nd (lf 0x2524c71000da3 [0xa0501040d,0x222]) (nd (lf 0x2524c71000de3 [0x5010222040d,0xc000a]) (lf 0x3624c71000be3 [0x501010f040a,0x4160020070b,0x106])))) (nd (nd (lf 0x3654c710009e3 [0x220501000d,0xa00070013]) (lf 0x2524cb1000da3 [0x40e00220512,0x17070b020a])) (nd (lf 0x1644cb1000be3 [0x501000a0009,0x20030b]) (nd (lf 0x3644cb1000be3 [0x6030b0004,0x5010422]) (lf 0x3654cb10009e3 [0x40e00090501,0x6000a0030]))))) (nd (nd (nd (lf 0x3654cb1000de3 [0x50100300009,0x20a]) (lf 0x1648cb1000be3 [0x12030b0004,0x22])) (nd (lf 0x14394b1000da3 [0x31030b020e,0x422040a]) (nd (lf 0x16394b1000da3 [0x70b0022002b,0x2200301040a,0x36030c]) (lf 0x14394b1000de3 [0x40a030b0031,0xc020e0422])))) (nd (nd (lf 0x36250f1000be3 [0x50b05010009,0x602]) (lf 0x3254f1000d63 [0x101])) (nd (lf 0x1210853000f83 [0x40c000e001d,0xa0416]) (nd (lf 0x3540853000de3 [0x6010206001d,0x415040e050a,0xc]) (lf 0x514853000dc3 [0x70b000a0415,0x2060416003c])))))) (nd (nd (nd (nd (lf 0x3544853000de3 [0x4150206040e,0x33]) (lf 0x6548530009e3 [0x15001b000e,0x3c00060002])) (nd (lf 0x528853000da3 [0x70b00220015,0x416050a040e]) (nd (lf 0x3548853000de3 [0x11102060212,0x40e001d]) (lf 0x26588530009e3 [0x1b00150026,0x60202])))) (nd (nd (lf 0x515053000dc3 [0x50b000a000e,0x415001d]) (lf 0x525053000da3 [0x222050b040e,0x416001b])) (nd (lf 0x525053000de3 [0x50b0222040e,0x60015000a]) (nd (lf 0x6550530009e3 [0x50b001b000e,0x22]) (lf 0x529053000da3 [0x50b00260416,0x222001b]))))) (nd (nd (nd (lf 0x529053000de3 [0x50b0222001b,0xa0015]) (lf 0x1621453000dc3 [0x70b000a0215,0x2160024003c])) (nd (lf 0x2621453000dc3 [0x601003c001d,0x216070b000a]) (nd (lf 0x1641453000dc3 [0x12000a0216,0x215001d0024]) (lf 0x1210863000f83 [0x40c0032000e,0x6020416010a])))) (nd (nd (lf 0x1430863000f63 [0x30b01220007,0x10a000e0111,0x106]) (lf 0x1540863000de3 [0x41502060212,0x40e])) (nd (lf 0x3540863000de3 [0x415030b020c,0x22000a040e]) (nd (lf 0x2314863000f43 [0x10a000e0212]) (lf 0x1434863000f63 [0xe020c0111]))))))
def F7T6_10 := nd (nd (nd (nd (nd (lf 0x1544863000de3 [0x40e02060415,0x22000a0012]) (lf 0x3544863000de3 [0x40e02060415])) (nd (lf 0x36548630009e3 [0x15000e0017,0x6]) (lf 0x2318863000f43 [0x10a0511020c,0x2010122000e]))) (nd (nd (lf 0x2618863000be3 [0xe01220007,0x106010b0004]) (lf 0x1438863000f63 [0x20c01110007])) (nd (lf 0x1548863000de3 [0x20604150004,0x12000a]) (nd (lf 0x3548863000de3 [0x20601110007,0x22]) (lf 0x16588630009e3 [0x2600150017,0x6000a040e]))))) (nd (nd (nd (lf 0x2628c63000b63 [0xc000e0122,0x1060401]) (lf 0x2525063000de3 [0x50b0222040e,0xc000a0015])) (nd (lf 0x625063000be3 [0xe01220412]) (nd (lf 0x36550630009e3 [0xe00170012,0x22]) (lf 0x2529063000de3 [0x601050b0222,0x40e000a])))) (nd (nd (lf 0x2629063000be3 [0x601050b0122,0x17000c010a,0x602060c010f]) (lf 0x625463000be3 [0xe040c0017,0x106010b])) (nd (lf 0x26294630009a3 [0x22000a0601]) (nd (lf 0x1629463000ba3 [0x170111040c,0x10a040e]) (lf 0x2629463000ba3 [0x40e00170412])))))) (nd (nd (nd (nd (lf 0x2629463000be3 [0x10a00170412,0x40e]) (lf 0x6150e3000b63 [0xc050b010a,0x122])) (nd (lf 0x219023000fe3 [0x330601001b,0x406040c0017,0x40b]) (nd (lf 0x2519023000de3 [0x601020a003c,0x80415050b]) (lf 0x1439023000e63 [0x1b0106020c,0x26003c0402,0x1001d])))) (nd (nd (lf 0x2600863000be3 [0x10a0601001d,0x10b040e0002,0x106]) (lf 0x1210863000f93 [0x70b000e001d,0x40c001b])) (nd (lf 0x1430863000f73 [0x202010a0007,0x20b01220017,0xc010b0106]) (nd (lf 0x1540863000df3 [0x402060212,0x402]) (lf 0x3540863000df3 [0x4020007000a,0x22000f0020,0xc]))))) (nd (nd (nd (lf 0x604863000be3 [0xc0601002d,0x10b0021060b,0x106]) (lf 0x2314863000f53 [0x60202120015])) (nd (lf 0x1434863000f73 [0x202002d000e,0x106020b001b]) (nd (lf 0x1544863000df3 [0x40e00210212,0x4150206]) (lf 0x3544863000df3 [0x21002a040e,0x20c])))) (nd (nd (lf 0x2608863000be3 [0x1d06010026,0x60b0025010f,0x106010b0002]) (lf 0x3218863000f93 [0x602000e0015,0x1b060b])) (nd (lf 0x1438863000f73 [0x106001d0111,0x10b001b0017,0xc]) (nd (lf 0x1548863000df3 [0x402120415,0x40202060034,0x401]) (lf 0x3548863000df3 [0x20c00180415,0x40100220402,0x50b0006]))))))
def F7T6_11 := nd (nd (nd (nd (nd (lf 0x1518c63000d53 [0xc0602000d]) (lf 0x605063000be3 [0x122000e0412,0x4110018010f])) (nd (lf 0x2525063000df3 [0x1b0222040e,0xc04020015]) (nd (lf 0x1435063000e73 [0x602020c000e,0x11001b0026,0x170015]) (lf 0x2609063000be3 [0x10d00260412,0x3b0601])))) (nd (nd (lf 0x2529063000df3 [0xd003b0416,0x50b001b]) (lf 0x16294630009b3 [0xa06020011,0x601])) (nd (lf 0x26294630009b3 [0xa0602003c,0x22070b0601]) (nd (lf 0x1219402100d93 [0x20d020e001d,0x406040c000a]) (lf 0x1439402100df3 [0x301001d0025,0xa040a000c,0x6000b]))))) (nd (nd (nd (lf 0x604842100f83 [0x1d000d000e,0xa0008]) (lf 0x604842100b93 [0x70b0701001d,0xf002e])) (nd (lf 0x604842100f93 [0xd000e001d,0x18]) (nd (lf 0x3604842100f83 [0xd000e001d,0xa]) (lf 0x1434842100f93 [0x40a030b000e,0x20c0302030c])))) (nd (nd (lf 0x1534842100d93 [0x2e000e0212]) (lf 0x1534842100f93 [0x70b000e001d,0x1b000a0035])) (nd (lf 0x3534842100d93 [0x1d000e0212]) (nd (lf 0x3654842100993 [0x70b07020701]) (lf 0x3654842100d93 [0x702000d000e,0xa])))))) (nd (nd (nd (nd (lf 0x3654842100b93 [0x70b0701001d,0xf000a]) (lf 0x3654842100f93 [0xd000e001d,0x9000a])) (nd (lf 0x36548421009d3 [0x110015001d,0x22]) (nd (lf 0x604842100be3 [0xd000e0008,0x40a]) (lf 0x36548421009f3 [0xd000e001d,0x90022000a])))) (nd (nd (lf 0x2608842100bc3 [0x1500110026]) (lf 0x2528842100d93 [0xe000a001d])) (nd (lf 0x1628842100b93 [0xd000e001d,0xa]) (nd (lf 0x604c42100be3 [0x2200200013,0x1060416060b]) (lf 0x6050c2100bf3 [0x10c0602000a,0xf00220020]))))) (nd (nd (nd (lf 0x6150c2100fd3 [0x20a0106010c,0x2005010011]) (lf 0x36150c2100bd3 [0x50106220020,0xf050b])) (nd (lf 0x36150c2100fd3 [0xe0106010c,0xa00240007]) (nd (lf 0x15350c2100f73 [0x50b0004020a,0x10022]) (lf 0x6550c2100df3 [0xb05010007,0x2402020004,0x1e])))) (nd (nd (lf 0x16550c2100bf3 [0xf00200007,0x40e04110102]) (lf 0x36550c21009f3 [0xc00070501,0x310002050b,0x20000a])) (nd (lf 0x36550c2100df3 [0x405010007,0xa000b]) (nd (lf 0x36550c2100bf3 [0xf00200007,0xc]) (lf 0x6054c21009e3 [0x1d04150012,0x40e040a]))))))
def F7T6_12 := nd (nd (nd (nd (nd (lf 0x6054c21009f3 [0x40a0012001d,0x40e]) (lf 0x6054c2100be3 [0x41504220035,0x40e])) (nd (lf 0x24354c2100f73 [0x302000e040a]) (lf 0x15454c2100df3 [0xc0501001d,0x1b00320035,0x6050b]))) (nd (nd (lf 0x36454c2100bf3 [0x12040a0106,0x40e0415]) (lf 0x2611412100de3 [0x102])) (nd (lf 0x1431412100de3 [0xc03010021]) (nd (lf 0x1631412100de3 [0x210015000e,0x30014070b,0xc]) (lf 0x3631412100de3 [0xc000e0021]))))) (nd (nd (nd (lf 0x2651412100de3 [0x102]) (lf 0x101412100dd3 [0x102])) (nd (lf 0x2101412100dd3 [0x102]) (nd (lf 0x1301412100de3 [0x102]) (lf 0x2301412100df3 [0x102])))) (nd (nd (lf 0x1311412100dd3 [0x502000d0015,0x1d]) (lf 0x2311412100dd3 [0xe00150026,0x25070b0406])) (nd (lf 0x1431412100df3 [0x2d0011000e,0x260402000c,0x6001d0021]) (nd (lf 0x1631412100df3 [0x2d0014000e,0xc]) (lf 0x3631412100df3 [0xc000e0005])))))) (nd (nd (nd (nd (lf 0x2608852100ba3 [0xa0026040e,0x106]) (lf 0x604c52100bc3 [0x501000d0415,0x22])) (nd (lf 0x604c52100bd3 [0xd04150018,0x220501]) (nd (lf 0x624c52100b93 [0x501000d001d,0x22]) (lf 0x2428c52100f93 [0x11602110112,0x25040e])))) (nd (nd (lf 0x3648c52100bd3 [0x10604150026]) (lf 0x6050d2100bf3 [0x2a00180020,0xa010c0602,0x22000f])) (nd (lf 0x6550d21009f3 [0x20011000e,0x24001e]) (nd (lf 0x6550d2100df3 [0x21000e010c,0x11001e]) (lf 0x6054d21009e3 [0xc000f000d]))))) (nd (nd (nd (lf 0x6054d21009f3 [0xf0302000d,0xc]) (lf 0x36454d21008f3 [0xc000f0020,0x6])) (nd (lf 0x3215422100f83 [0x11001d]) (nd (lf 0x3219422100d83 [0x26020d020e]) (lf 0x3219422100dc3 [0x1500110222])))) (nd (nd (lf 0x3219422100da3 [0xa0026020e,0x406]) (lf 0x3219422100de3 [0x20d0026020e,0xa])) (nd (lf 0x1319422100dc3 [0x260015002e]) (nd (lf 0x1319422100de3 [0x3010026020d,0x222000a]) (lf 0x2319422100dc3 [0x150026]))))))
def F7T6_13 := nd (nd (nd (nd (nd (lf 0x619422100dc3 [0x2600250222]) (lf 0x3629422100da3 [0x20d0026020e])) (nd (lf 0x1439422100de3 [0x26030c0011,0x40a0025020e,0xc002f]) (nd (lf 0x3639422100de3 [0x150026003b]) (lf 0x3219422100f83 [0x1500110026])))) (nd (nd (lf 0x3219422100d93 [0x7010026001d,0x70b]) (lf 0x1319422100dd3 [0x15002e])) (nd (lf 0x1439422100df3 [0x1100260025,0x301001d000c,0x6]) (nd (lf 0x143c862100f93 [0x302000e0011]) (lf 0x165c862100d93 [0xd000e001d,0xa]))))) (nd (nd (nd (lf 0x165c862100f93 [0xd000e001d,0x90026]) (lf 0x604c62100bc3 [0x10600350415,0x416])) (nd (lf 0x604c62100fc3 [0x415000d0013]) (nd (lf 0x604c62100bd3 [0x2604150018,0x1060416]) (lf 0x604c62100fd3 [0x4150026002e,0x10c])))) (nd (nd (lf 0x3604c62100fc3 [0x302000d0415]) (lf 0x1644c62100bd3 [0x2501060415,0x220018])) (nd (lf 0x3644c62100bd3 [0xd01060415,0x25]) (nd (lf 0x3654c62100dd3 [0xa002e0028]) (lf 0x604c62100be3 [0x40a00200013,0x4160022070b,0x2020106])))))) (nd (nd (nd (nd (lf 0x3654c621009f3 [0x15000d0026,0x13000a]) (lf 0x2628c62100b93 [0x501000a001d])) (nd (lf 0x1648c62100bd3 [0x11200260415]) (nd (lf 0x1439462100df3 [0x40a000e0007,0x220004000c,0xb0006000f]) (lf 0x6054a21009f3 [0xd000e001d,0xf])))) (nd (nd (lf 0x6050e2100bf3 [0x6020018000a,0x220020010c,0x401000c000f,0x40b0006]) (lf 0x6250e2100bb3 [0x5010011001d,0x60a0020])) (nd (lf 0x6250e2100fb3 [0x70024010c,0x1e05010106,0xf]) (nd (lf 0x36550e21009f3 [0x50100070011,0x24000a0002,0xc]) (lf 0x36550e2100df3 [0x705010024,0xa010c]))))) (nd (nd (nd (lf 0x260d4e21009e3 [0xc00110026]) (lf 0x1411413100dc3 [0x2006010025,0x215001b030b])) (nd (lf 0x2411413100dc3 [0xd001c0216]) (nd (lf 0x2611413100de3 [0x102]) (lf 0x1421413100de3 [0x216000d001c,0x22])))) (nd (nd (lf 0x2421413100de3 [0x22000d0035,0x216]) (lf 0x621413100de3 [0x601070b001c,0xc001d0025,0x216030b0023])) (nd (lf 0x1621413100de3 [0x1b0601001c,0x20030b0035,0x22000c]) (nd (lf 0x2621413100de3 [0x70b0035001c,0x230020001d]) (lf 0x3621413100de3 [0x70b00130215,0x21600240025,0x22]))))))
def F7T6_14 := nd (nd (nd (nd (nd (lf 0x1641413100de3 [0x216000d0035,0x21500240023]) (lf 0x3641413100de3 [0xd0216001c])) (nd (lf 0x521413100de3 [0x22000d0013]) (lf 0x3521413100de3 [0x215000d0013,0x220102]))) (nd (nd (lf 0x2621413100be3 [0x6010122040d,0x102]) (lf 0x2651413100de3 [0x102])) (nd (lf 0x2101413100dd3 [0x102]) (nd (lf 0x201413100db3 [0x102]) (lf 0x201413100df3 [0x102]))))) (nd (nd (nd (lf 0x1201413100de3 [0x102]) (lf 0x2201413100db3 [0x102])) (nd (lf 0x2201413100df3 [0x500220215,0x302]) (nd (lf 0x3201413100de3 [0x102]) (lf 0x1401413100de3 [0x102])))) (nd (nd (lf 0x2401413100df3 [0x102]) (lf 0x1411413100dd3 [0x601001b0025,0x2150020])) (nd (lf 0x2411413100dd3 [0x21600260025,0x40f000d]) (nd (lf 0x1421413100df3 [0x25000d0215,0x2202160302]) (lf 0x2421413100df3 [0x11000d0216,0x2200260025])))))) (nd (nd (nd (nd (lf 0x621413100df3 [0x2606010005,0x220018040c,0xf030b]) (lf 0x1621413100df3 [0xc03020215,0x30b00200018,0x22])) (nd (lf 0x2621413100df3 [0x40c001c0018,0xf00220302]) (nd (lf 0x3621413100df3 [0x2202150005]) (lf 0x1431413100d73 [0x420000c030b,0x40f0026])))) (nd (nd (lf 0x1641413100df3 [0x2160010000d]) (lf 0x3641413100df3 [0x6000d0005])) (nd (lf 0x3201413100fe3 [0x102]) (nd (lf 0x521413100df3 [0x1c00200502,0x2200150215]) (lf 0x3521413100df3 [0x2003020215,0x22]))))) (nd (nd (nd (lf 0x2621413100bf3 [0x1c01220420,0x102]) (lf 0x352d413100de3 [0x502000d0215])) (nd (lf 0x262d413100be3 [0x40c0122040d,0xa]) (nd (lf 0x1435093100e73 [0x2010106020c,0x10b040f0420]) (lf 0x6550931009f3 [0x20015000d,0x13002e])))) (nd (nd (lf 0x2609093100bf3 [0x11040d002e,0x60106001d]) (lf 0x2619093100bd3 [0x1600260111,0xd])) (nd (lf 0x2601493100bf3 [0x2a0302002e,0xf0122]) (nd (lf 0x260d4931009e3 [0x2f06010011,0x420000a]) (lf 0x260d4931009f3 [0x30206010011,0x2d000a0420]))))))
def F7T6_15 := nd (nd (nd (nd (nd (lf 0x260d493100be3 [0x40d0015002f,0x22000a040c]) (lf 0x260d493100bf3 [0x40c00150420,0x22000a])) (nd (lf 0x6150d3100b53 [0x50b000c0026]) (nd (lf 0x6055131009e3 [0x606010020,0x22]) (lf 0x6055131009f3 [0x60100200302,0xf00220006,0x180005])))) (nd (nd (lf 0x6255131009b3 [0x200601001d,0x6]) (lf 0x36255131009b3 [0x601000f0020,0x6])) (nd (lf 0x2429423100df3 [0x25040e0216,0x30b000a040a,0x11]) (nd (lf 0x6054a31009e3 [0x11000e]) (lf 0x6054a31009f3 [0xe00110026]))))) (nd (nd (nd (lf 0x26094a31009e3 [0x6000e001d]) (lf 0x101414300dd3 [0x102])) (nd (lf 0x101414300df3 [0x102]) (nd (lf 0x2101414300dd3 [0x102]) (lf 0x2101414300df3 [0x102])))) (nd (nd (lf 0x3101414300de3 [0x102]) (lf 0x611414300df3 [0x201020b0005,0x20000a040c])) (nd (lf 0x1611414300df3 [0x2a000c0302,0x60020040c,0xa]) (nd (lf 0x2611414300df3 [0x302002a040c,0x20000a]) (lf 0x3611414300df3 [0x20040c0005,0xa])))))) (nd (nd (nd (nd (lf 0x3101414300fe3 [0x102]) (lf 0x511414300df3 [0x6000c0502,0x601000a000e])) (nd (lf 0x3511414300df3 [0xc002a0502,0xa0020]) (nd (lf 0x2611414300bf3 [0x10a0102040c,0x6010406]) (lf 0x26014543009e3 [0x60b06010026,0x22])))) (nd (nd (lf 0x16214543009b3 [0x60b06010026,0xa000f]) (lf 0x26214543009b3 [0xa0601001d,0x60b])) (nd (lf 0x2601454300be3 [0x60b040c001e,0x122]) (nd (lf 0x2601454300bf3 [0x4060025040c,0x1106010026,0x20]) (lf 0x521454300df3 [0xe0006000c,0x5020008000a,0x2200110302,0x601]))))) (nd (nd (nd (lf 0x3521454300df3 [0xe000c0021,0x5020006000a,0xf]) (lf 0x1621454300bb3 [0x601040c001e,0x250702])) (nd (lf 0x2621454300bb3 [0x7020601001e,0x25]) (nd (lf 0x2621454300bf3 [0x601040c0122,0xe060b0406]) (lf 0x260d4543009e3 [0x2006010021,0x22060b])))) (nd (nd (lf 0x260d4543009f3 [0x60100200302,0xf0022060b,0x21]) (lf 0x260d454300be3 [0x601040c0021])) (nd (lf 0x260d454300bf3 [0x406000e040c,0xa000b0025]) (nd (lf 0x352d454300df3 [0xf00200021]) (lf 0x262d454300bf3 [0x4060122040c,0xb0601]))))))
def F7T6 : BTree NodeData := nd (nd (nd (nd F7T6_0 F7T6_1) (nd F7T6_2 F7T6_3)) (nd (nd F7T6_4 F7T6_5) (nd F7T6_6 F7T6_7))) (nd (nd (nd F7T6_8 F7T6_9) (nd F7T6_10 F7T6_11)) (nd (nd F7T6_12 F7T6_13) (nd F7T6_14 F7T6_15)))
def F7M6 : BST := BN 337365708 42240 (BN 284601247 27136 (BN 234018150 51329 (BN 208968353 62080 (BN 184685763 12544 (BN 161816775 2176 (BN 135757639 47874 (BN 133989639 52352 (BN 132609251 61824 (BL 94620130 16768) BE) (BL 135129295 31488)) (BN 148778432 12928 (BL 144556073 55040) (BL 154182393 45568))) (BN 176805953 54912 (BN 166636975 22786 (BN 166398722 18817 (BL 164135142 7680) BE) (BL 176503365 12672)) (BN 183022407 40961 (BL 178637691 18816) (BL 183073689 51584)))) (BN 196122692 5249 (BN 193134945 63746 (BN 190457859 3072 (BN 189954911 12546 (BL 187052408 22912) BE) (BL 191464751 26881)) (BN 194847230 16000 (BL 194409379 7682) (BL 195261376 40960))) (BN 204607151 53761 (BN 203703720 26880 (BN 199221944 9345 (BL 197634774 8577) BE) (BL 203877121 15874)) (BN 206098760 24576 (BL 204840928 12160) (BL 207114103 16002))))) (BN 219498750 63617 (BN 214541104 59648 (BN 213638945 29312 (BN 210674369 42368 (BN 210618604 30592 (BL 209831706 39937) BE) (BL 210899370 38016)) (BN 214089095 22784 (BL 213933155 27137) (BL 214168775 31744))) (BN 216846120 53760 (BN 215246098 42752 (BN 215006316 21376 (BL 214686185 42624) BE) (BL 216582684 41346)) (BN 218825811 17792 (BL 217410697 19072) (BL 219302419 57601)))) (BN 225388102 37248 (BN 221592428 25984 (BN 220831746 56064 (BN 220695930 9346 (BL 219924983 63232) BE) (BL 221282118 12800)) (BN 223068107 1792 (BL 222070675 39936) (BL 224803685 44546))) (BN 226506673 23552 (BN 226001244 3074 (BL 225428673 53632) (BL 226233134 60800)) (BN 227459162 384 (BL 226830818 386) (BL 233852086 53889)))))) (BN 267445577 13952 (BN 250601680 52608 (BN 239499950 24960 (BN 237849039 62592 (BN 236775438 59776 (BN 236440331 41474 (BL 235142087 5376) BE) (BL 237407120 10752)) (BN 238774594 21632 (BL 238270736 14336) (BL 239308664 11392))) (BN 247460291 1282 (BN 243255590 51585 (BN 242842249 14720 (BL 242654735 15104) BE) (BL 245203887 44416)) (BN 248214547 56704 (BL 247595036 53888) (BL 249014946 29056)))) (BN 258483712 16770 (BN 256084317 6273 (BN 252958638 61440 (BN 252367680 49538 (BL 250970167 9344) BE) (BL 253444822 64512)) (BN 257884271 8320 (BL 256656891 7040) (BL 258133501 46338))) (BN 261521876 57984 (BN 260810024 55682 (BN 259557816 57472 (BL 258940614 45696) BE) (BL 261135844 51072)) (BN 267132096 18048 (BL 264263269 22272) (BL 267174787 28801))))) (BN 277698924 4352 (BN 273424599 4608 (BN 271766124 3456 (BN 271050642 57600 (BN 270942348 58881 (BL 269964220 4736) BE) (BL 271246973 63616)) (BN 272643818 29184 (BL 272495720 62848) (BL 273292859 39938))) (BN 275617131 17537 (BN 274526544 2432 (BN 274136207 47872 (BL 274014792 62976) BE) (BL 275616828 48768)) (BN 277094137 41600 (BL 276966232 16512) (BL 277337323 53505)))) (BN 281603653 47362 (BN 280938064 29568 (BN 279713448 20864 (BN 279016893 5633 (BL 278338954 24192) BE) (BL 279969510 18560)) (BN 281471786 59778 (BL 281464019 12801) (BL 281535582 51330))) (BN 282641917 49536 (BN 282057634 52738 (BL 281653884 58368) (BL 282083752 26240)) (BN 283892451 41472 (BL 282702511 10369) (BL 284206314 26752))))))) (BN 313396615 55808 (BN 301696030 45185 (BN 292330657 43648 (BN 289219619 42113 (BN 288324981 57858 (BN 287435455 32384 (BN 287165205 38528 (BL 286688574 23553) BE) (BL 287875076 512)) (BN 288905813 5632 (BL 288331175 50944) (BL 289086117 6530))) (BN 291144855 54401 (BN 290727775 19457 (BN 290096228 51968 (BL 289926456 10881) BE) (BL 291084261 55680)) (BN 291553269 41344 (BL 291489824 40450) (BL 292137196 26113)))) (BN 295740541 6144 (BN 293594753 49280 (BN 292648658 29824 (BN 292647620 39808 (BL 292629316 63872) BE) (BL 293439750 20609)) (BN 293962699 43649 (BL 293832404 58112) (BL 295064059 30210))) (BN 299631537 18690 (BN 299167600 39296 (BN 297663693 4480 (BL 295877799 65152) BE) (BL 299607977 14976)) (BN 299851442 10498 (BL 299826766 49154) (BL 301407217 57856))))) (BN 305866382 20736 (BN 302918723 640 (BN 302437463 45440 (BN 302028344 40832 (BN 301882094 14465 (BL 301856179 5760) BE) (BL 302252043 31104)) (BN 302857024 48128 (BL 302722392 53248) (BL 302894426 59264))) (BN 303996297 25728 (BN 303230351 23936 (BN 302989004 24833 (BL 302966744 19456) BE) (BL 303496267 11648)) (BN 304620986 7168 (BL 304206964 61056) (BL 305809761 52482)))) (BN 309371297 19328 (BN 308115289 65408 (BN 307773041 48256 (BN 306582497 15488 (BL 305985374 25856) BE) (BL 307832540 6272)) (BN 308216428 53376 (BL 308128396 5504) (BL 308867272 58625))) (BN 311417785 57344 (BN 310012476 61184 (BL 309956555 30336) (BL 311164736 55552)) (BN 312011531 18050 (BL 311938611 11136) (BL 312827753 52224)))))) (BN 326580572 7552 (BN 320002152 15232 (BN 316910505 37376 (BN 316235430 64641 (BN 315493902 57088 (BN 315068755 21762 (BL 314287378 6784) BE) (BL 315839950 40576)) (BN 316658772 47232 (BL 316454920 44545) (BL 316767191 52992))) (BN 319074243 56449 (BN 318152867 28672 (BN 318069034 63488 (BL 317288111 5120) BE) (BL 318957970 60032)) (BN 319360354 6528 (BL 319299587 10112) (BL 319860129 6400)))) (BN 322147078 41984 (BN 321619268 8576 (BN 321135306 44544 (BN 320291785 5248 (BL 320249049 59137) BE) (BL 321440855 4098)) (BN 321915564 43776 (BL 321884025 43008) (BL 322084866 57728))) (BN 324490919 56320 (BN 323347883 39041 (BN 322762632 7296 (BL 322729722 23168) BE) (BL 323374467 63360)) (BN 326107419 62464 (BL 324606361 9984) (BL 326179027 28162))))) (BN 333184595 49792 (BN 329926048 18176 (BN 328246803 15106 (BN 327268745 46208 (BN 327144477 46592 (BL 326595211 38144) BE) (BL 328049785 44160)) (BN 329080351 20352 (BL 328979719 10624) (BL 329883199 39170))) (BN 331871521 58496 (BN 330589422 19200 (BN 330491627 23681 (BL 330326369 40192) BE) (BL 331115950 48129)) (BN 333046833 31616 (BL 332178535 16640) (BL 333060777 65280)))) (BN 335219078 16256 (BN 334544307 1152 (BN 334110561 30464 (BN 333919328 2688 (BL 333699583 38912) BE) (BL 334476645 46848)) (BN 334743538 24704 (BL 334600519 20480) (BL 335025727 5888))) (BN 335777101 39424 (BN 335548411 37760 (BL 335329726 28160) (BL 335736338 12288)) (BN 336091652 12416 (BL 335975430 55296) (BL 336251313 28930)))))))) (BN 385513612 25088 (BN 359714462 38400 (BN 347097300 5506 (BN 344727717 65410 (BN 341744922 22018 (BN 340631079 27008 (BN 339052548 61568 (BN 338124561 22656 (BL 337429856 23680) BE) (BL 339553359 50946)) (BN 341336665 18944 (BL 340990475 5635) (BL 341610440 58880))) (BN 343686157 13312 (BN 342733755 50434 (BN 342361672 51840 (BL 342141927 64768) BE) (BL 343168064 3200)) (BN 344524206 7936 (BL 344108374 52864) (BL 344533996 30848)))) (BN 345697913 3840 (BN 345410923 25858 (BN 345027715 26368 (BN 344951621 47104 (BL 344785678 23042) BE) (BL 345030742 9474)) (BN 345466784 50560 (BL 345420416 61696) (BL 345694692 10880))) (BN 346488724 48386 (BN 345855967 16384 (BN 345777007 2306 (BL 345725020 63104) BE) (BL 346377885 3968)) (BN 346798865 25600 (BL 346534145 22016) (BL 347083657 18688))))) (BN 353704397 2816 (BN 350066497 15872 (BN 348350174 14848 (BN 347980038 27648 (BN 347946634 19584 (BL 347494892 50304) BE) (BL 348265384 8960)) (BN 348548627 50432 (BL 348492833 8064) (BL 348848997 41218))) (BN 352262186 54656 (BN 351956612 6657 (BN 351776158 23424 (BL 350383643 17408) BE) (BL 352161500 37504)) (BN 353219932 54530 (BL 352550718 11904) (BL 353444253 45184)))) (BN 356818362 13824 (BN 355640673 62336 (BN 354737227 24832 (BN 353909128 9600 (BL 353760519 14080) BE) (BL 355012798 41088)) (BN 355739338 17280 (BL 355733142 61952) (BL 355843170 48640))) (BN 358187243 51328 (BN 357811780 58882 (BL 356859353 44162) (BL 357823970 27392)) (BN 358565683 56960 (BL 358224502 52736) (BL 358825987 4864)))))) (BN 372286239 30080 (BN 365937574 61312 (BN 362706794 9216 (BN 360957329 28288 (BN 360503684 40064 (BN 360250706 16385 (BL 360199214 22144) BE) (BL 360821606 38914)) (BN 362501775 15617 (BL 362374777 27649) (BL 362665959 37122))) (BN 364259639 27264 (BN 363452326 26112 (BN 363032073 2048 (BL 362900951 38656) BE) (BL 363555242 3712)) (BN 365326675 25216 (BL 364546330 54144) (BL 365484953 43136)))) (BN 369263950 64770 (BN 367679516 24320 (BN 366512128 30720 (BN 366047075 24450 (BL 365999785 55424) BE) (BL 366809632 65025)) (BN 368892975 4096 (BL 368025433 59392) (BL 369063866 21120))) (BN 371149138 62208 (BN 370175274 9856 (BN 369539049 28032 (BL 369445350 19840) BE) (BL 370938395 1280)) (BN 371490018 65024 (BL 371474417 11520) (BL 372269270 50176))))) (BN 380530237 1024 (BN 376206994 56192 (BN 374954472 49920 (BN 373927297 13440 (BN 372663221 41216 (BL 372496884 54528) BE) (BL 374515117 60930)) (BN 375819907 10240 (BL 375525261 38272) (BL 376173135 14082))) (BN 377981393 43904 (BN 377335319 39168 (BN 376467777 32000 (BL 376302652 19712) BE) (BL 377887694 52096)) (BN 379535364 58624 (BL 378306229 58752) (BL 380363449 43520)))) (BN 383813953 19714 (BN 381666744 56832 (BN 380728583 45952 (BN 380711614 37632 (BL 380566080 31361) BE) (BL 381089299 58883)) (BN 382970281 64128 (BL 382812048 44800) (BL 383296822 29696))) (BN 384420699 45056 (BN 383967605 21888 (BL 383900119 56448) (BL 384262251 7424)) (BN 384744315 40320 (BL 384602323 64129) (BL 384763920 27776))))))) (BN 419953683 768 (BN 401452436 59520 (BN 392233634 40704 (BN 386410546 3842 (BN 386247911 5890 (BN 385726243 47488 (BN 385698829 46850 (BL 385693063 60288) BE) (BL 385925515 1920)) (BN 386394763 20224 (BL 386304011 9986) (BL 386408977 8192))) (BN 390738167 60416 (BN 388972581 25344 (BN 388779777 60544 (BL 386531208 13187) BE) (BL 390072751 51456)) (BN 391343880 28800 (BL 391210576 64384) (BL 392083071 50816)))) (BN 395492513 63744 (BN 393865941 18304 (BN 393229127 2304 (BN 392863043 14592 (BL 392237798 45824) BE) (BL 393558347 17024)) (BN 395286909 46720 (BL 394851321 43264) (BL 395321696 30722))) (BN 398555948 15235 (BN 398388718 31872 (BN 398306970 8832 (BL 398107237 258) BE) (BL 398545096 46336)) (BN 400374025 51200 (BL 399786224 17536) (BL 401199414 128))))) (BN 409808230 30208 (BN 404906657 20096 (BN 403637290 41090 (BN 401849900 11264 (BN 401626032 48000 (BL 401506416 53504) BE) (BL 402399250 64640)) (BN 403802729 28416 (BL 403764040 49922) (BL 404450395 48384))) (BN 407093902 50048 (BN 406615577 17664 (BN 406384195 49152 (BL 404927002 1664) BE) (BL 406871604 10368)) (BN 408816369 60672 (BL 407955349 10496) (BL 409581821 28290)))) (BN 414091728 48896 (BN 411511339 22528 (BN 411271388 27905 (BN 411254732 16128 (BL 409977883 38530) BE) (BL 411340629 24064)) (BN 412513001 28928 (BL 412270519 13184) (BL 413388712 42112))) (BN 416504244 1408 (BN 415313948 54400 (BL 414123135 38658) (BL 416439793 11008)) (BN 417212257 43392 (BL 416549305 52480) (BL 417608843 20608)))))) (BN 454999790 13057 (BN 438524076 8448 (BN 427236385 15360 (BN 423506951 54016 (BN 421097749 16896 (BN 421010316 17665 (BL 420527906 15616) BE) (BL 421658190 2944)) (BN 425938467 56576 (BL 424558952 47744) (BL 426051187 14464))) (BN 428503244 53120 (BN 428111667 27520 (BN 428056035 45314 (BL 427649539 12032) BE) (BL 428218981 49664)) (BN 431289178 20992 (BL 429150597 11776) (BL 436334316 31360)))) (BN 446407661 4224 (BN 442951008 37888 (BN 442198325 21248 (BN 439535878 62722 (BL 439238353 39552) BE) (BL 442829196 37120)) (BN 444418142 59136 (BL 443384546 59008) (BL 444467754 12034))) (BN 447680697 55936 (BN 447444437 32640 (BN 447090958 7808 (BL 446597165 5634) BE) (BL 447516976 39040)) (BN 451393352 60160 (BL 448935011 49408) (BL 452361174 47360))))) (BN 486340000 19968 (BN 475508155 45312 (BN 467971973 256 (BN 466976666 57216 (BN 466759194 17152 (BL 465134713 40448) BE) (BL 467453447 9472)) (BN 470977110 8704 (BL 469297519 27904) (BL 473189421 60928))) (BN 480250421 46976 (BN 478458569 32256 (BN 478021606 64256 (BL 476855283 44928) BE) (BL 480114446 18432)) (BN 481667640 24448 (BL 480777303 41728) (BL 482354166 30976)))) (BN 498980609 23040 (BN 495640326 59138 (BN 489265913 21760 (BN 488556790 44288 (BL 487235678 26624) BE) (BL 495045574 6656)) (BN 496645931 0 (BL 495678022 23808) (BL 496750935 3584))) (BN 531262159 29952 (BN 509626423 9088 (BL 500359502 29440) (BL 524140927 13568)) (BN 574020288 3328 (BL 547639785 62720) (BL 598088752 13056))))))))
def F7T7_0 := nd (nd (nd (nd (nd (lf 0x48410007c2 [0x30b000a0115,0x2201110301]) (lf 0x48410007e2 [0xd000a000e,0x22])) (nd (lf 0x88410007c2 [0x30b0115000a,0x2201110301,0x2]) (nd (lf 0xc8410007e2 [0xd000a000e,0x122]) (lf 0x4c410007e2 [0x101000a000d])))) (nd (nd (lf 0x4c810007e2 [0xa01010037,0x10f030b000e,0x1600220202,0xc]) (nd (lf 0x8c810007e2 [0x2201010021,0xe0115000a,0x160202030b]) (lf 0x14810005e2 [0x3010022000a,0x6000c030b]))) (nd (lf 0x54810007e2 [0x30b0115000a,0x2203010021]) (nd (lf 0x94810005e2 [0x301000a0022,0xc0002030b,0x6]) (lf 0x94810007e2 [0x3010021000a,0x9030b]))))) (nd (nd (nd (lf 0x50c10007e2 [0x10b01010021,0xc000e000a,0xd0202]) (nd (lf 0x54c10005e2 [0xe000a0012,0x220002]) (lf 0x54c10007e2 [0x3010112000a,0x2d030b001c]))) (nd (lf 0xd4c10005e2 [0x22000a0012]) (nd (lf 0x8801000782 [0x30b0301]) (lf 0x88010007c2 [0x301001d010f,0x2030b])))) (nd (nd (lf 0x94010007c2 [0x30b0026000e,0x20101]) (nd (lf 0x4c810007d2 [0x1010202002e,0x10f001d030b,0xa]) (lf 0x8c810007d2 [0x2e0101001d,0xa0202030b]))) (nd (lf 0x14810007d2 [0xa0025001d,0x101030b0301,0x10b]) (nd (lf 0x54810007d2 [0x11102020029,0x301000a001d,0x34030b]) (lf 0x94810007d2 [0x30b0029001d,0xa02020301,0x34])))))) (nd (nd (nd (nd (lf 0xd4810007d2 [0x202000a0025,0x301010f030b,0x1d]) (lf 0x50c10007d2 [0x10102020025,0xa001d010b])) (nd (lf 0x54c10007d2 [0x20201010025,0xa0029030b,0x1d]) (nd (lf 0xd4c10007d2 [0x202000a0025,0x1d030b0101]) (lf 0x84010007e2 [0xd0026000e,0x2])))) (nd (nd (lf 0x8010007e2 [0x301030b002d,0x210022000a,0xf00200002]) (nd (lf 0x88010007a2 [0x30b0301020a,0x2]) (lf 0x88010007e2 [0x30b001d001c,0x10f0301020a,0x200370020,0xa]))) (nd (lf 0x8c010007e2 [0x30b0101002d,0x20a0017000e,0x200160015,0x32000c000a]) (nd (lf 0x8410007d2 [0x301000a001d,0x202030b]) (lf 0x48410007d2 [0xd02020029,0x301000a001d,0x34010f030b]))))) (nd (nd (nd (lf 0x48410007f2 [0x202000a000e,0x8001d000d,0x10f]) (nd (lf 0x88410007d2 [0x3010202000a,0x1d010f030b]) (lf 0xc8410007d2 [0x30b0301001d,0x200202000a]))) (nd (lf 0xc8410007f2 [0xd000e001d,0x202000a]) (nd (lf 0x4c410007d2 [0x1010202002e,0x1d0015030b,0x2000170016,0xa]) (lf 0x4c410007f2 [0x202000a000d,0x1c002d0101,0x17001d0015])))) (nd (nd (lf 0x8c410007d2 [0x1010202000a,0x15002e030b,0x16001d]) (nd (lf 0x4c810007f2 [0x10f01010202,0xe030b000a,0xf002e001d,0xc002d0016]) (lf 0x8c810007f2 [0x30b0101001d,0x2e000a000e,0x1600150202,0x21]))) (nd (lf 0x14810005f2 [0x220202000a,0x1030b0301,0x6000b000c]) (nd (lf 0x54810005f2 [0x1102020015,0x20000a]) (lf 0x54810007f2 [0x1d0202000a,0x2d030b0301,0x200021010f]))))))
def F7T7_1 := nd (nd (nd (nd (nd (lf 0x94810005f2 [0xa02020022,0xf030b0301,0x6000c]) (lf 0x94810007f2 [0x301000a001d,0x2d0202030b,0xf00200021])) (nd (lf 0xd4810005f2 [0x11000a0015,0x202]) (nd (lf 0x50c10007f2 [0x10b01010202,0x10c000e000a,0xc001d0011,0x6000d0021]) (lf 0x54c10005f2 [0xa02020012,0x220101000e,0xf])))) (nd (nd (lf 0x54c10007f2 [0x1010202000a,0x1d000e030b,0x35001c002d,0x250029]) (nd (lf 0xd4c10005f2 [0xa02020012,0x22000f]) (lf 0x8c210007c2 [0x10c030b0101,0x20017000e]))) (nd (lf 0x4ca10007d2 [0x1010202002e,0xe030b001d,0x10f0026]) (nd (lf 0x8ca10007d2 [0x101002e001d,0xe030b0202,0x26]) (lf 0x14a10007d2 [0xd000e001d]))))) (nd (nd (nd (lf 0x54a10007d2 [0xd01150026,0x3010202001d]) (nd (lf 0x94a10007d2 [0x301001d0026,0x202030b]) (lf 0xd4a10007d2 [0x202000d000e,0x26001d]))) (nd (lf 0x50e10007d2 [0x10102020025,0x1d000e010b,0x10c0026]) (nd (lf 0x54e10007d2 [0x30b000e0026,0x2020025]) (lf 0xd4e10007d2 [0x1010202000d,0x1d])))) (nd (nd (lf 0x8c210007e2 [0x30b003c000e,0x101000c0017,0x15010c0002,0x16]) (nd (lf 0x94210005e2 [0x30b0301000a,0x6000c0022]) (lf 0x8610007d2 [0x3010026001d,0x202030b]))) (nd (lf 0x48610007d2 [0xd0202000e,0x26001d]) (nd (lf 0x88610007d2 [0xd01150026,0xa0202001d,0x301]) (lf 0xc8610007d2 [0xd000e001d,0x202])))))) (nd (nd (nd (nd (lf 0x4c610007d2 [0x1010202000d,0x1d0015]) (nd (lf 0x8c610007d2 [0x30b000e0026,0x1010202002e]) (lf 0x4ca10007f2 [0x1d0202000e,0x26030b010f,0x2e003a003c,0x16]))) (nd (lf 0x8ca10007f2 [0x30b000e001d,0x2e003c0026,0x16]) (nd (lf 0x54a10005f2 [0x1100150026,0x202]) (lf 0x94a10005f2 [0x30100220026,0xc0202030b,0x6])))) (nd (nd (lf 0xd4a10005f2 [0x202000d000e,0xf]) (nd (lf 0x50e10007f2 [0x10b0202000e,0x101010c0026,0xc0011001d]) (lf 0x54e10005f2 [0xe00120026,0x202]))) (nd (lf 0xd4e10005f2 [0xc0202000d,0x22000f]) (nd (lf 0x48710007e2 [0xd000a000e,0x22]) (lf 0xc8710007e2 [0xd000e001d,0x22000a]))))) (nd (nd (nd (lf 0x4c710007e2 [0x101000a000d,0x1d]) (nd (lf 0x4cb10007e2 [0x111000e0202,0x101020a001d,0x160022030b]) (lf 0x8cb10007e2 [0xe0101001d,0x30b0022020a,0x16000c]))) (nd (lf 0x94b10005a2 [0x30b000a0301,0x22]) (nd (lf 0x94b10005e2 [0x301000a0022,0x6000c030b]) (lf 0x50f10007e2 [0x20201010021,0x20a0006000d,0xc001d000e])))) (nd (nd (lf 0x54f10005e2 [0xe000a0012,0x22]) (nd (lf 0x8530007e2 [0xa0201001d,0x30b010a000e,0xc00220015,0x16]) (lf 0x48530007e2 [0x150202000e,0x3c001b030b,0x16]))) (nd (lf 0x88530007e2 [0x30b00150026,0x202000a001b,0x16]) (nd (lf 0x50530007e2 [0x10b0202000e,0x15001d001b]) (lf 0x90530007e2 [0x1b00160026,0x15000a010b,0x1d]))))))
def F7T7_2 := nd (nd (nd (nd (nd (lf 0x14530005c2 [0xa030b0201]) (lf 0x14530005e2 [0x30b0201000a,0x60022])) (nd (lf 0xd5130005e2 [0x60012]) (nd (lf 0x8630007e2 [0x1501220032,0xa000e0201,0x1700160212,0xc0202010a]) (lf 0x48630007e2 [0x212000e0015,0x1b0201000c,0x160202003c,0x17])))) (nd (nd (lf 0x88630007e2 [0x10a001b0015,0x201000c000e,0x202000a030b,0x170016]) (nd (lf 0x8c63000762 [0xe010a0012,0x1]) (lf 0x50630007e2 [0x1b000e0012,0x150201]))) (nd (lf 0x90630007e2 [0x1b00160012,0x201000e010a,0x15]) (nd (lf 0x54630007e2 [0x201000e0012,0xa00150017]) (lf 0x94630005e2 [0x30b0201000a,0x60022]))))) (nd (nd (nd (lf 0x94630007e2 [0x10a00170012,0x150201000e]) (nd (lf 0x50e3000762 [0x10b000c]) (lf 0x55230005e2 [0xa02010006,0x22]))) (nd (lf 0xd5230005e2 [0xa02010006,0x22]) (nd (lf 0x90230007e2 [0x1b00160012,0x10b003c0201,0x11000e000d,0x15]) (lf 0x8630007f2 [0x10a000e001d,0xc0017030b,0x1600150201])))) (nd (nd (lf 0x48630007f2 [0x2020015000e,0xc001b030b,0x16003c0017]) (nd (lf 0x88630007f2 [0x30b00150026,0xc001b0017,0x16]) (lf 0x8c63000772 [0x20200120026,0x1d]))) (nd (lf 0x50630007f2 [0x2020012000e,0x110017001b,0x15001d]) (nd (lf 0x90630007f2 [0x1600120026,0x2d0017001b,0x1d00150011]) (lf 0x54630005f2 [0x2010202000d,0xf0022])))))) (nd (nd (nd (nd (lf 0x94630005f2 [0x2010202000a,0x22000f030b,0x6]) (nd (lf 0x50e3000772 [0x10b0202000c,0x110026000d,0x1d]) (lf 0x55230005f2 [0x602020012]))) (nd (lf 0xd5230005f2 [0x60202000c,0xf0020000a,0x22]) (nd (lf 0x94021005f2 [0x3010026001d,0xa0102030b,0x6000c]) (lf 0x4842100792 [0xd000e001d,0xa])))) (nd (nd (lf 0x48421007d2 [0x220015001d,0x11]) (nd (lf 0x48421007f2 [0xd000e001d,0x22000a]) (lf 0x88421007d2 [0x110015001d,0x20022]))) (nd (lf 0x4c421007f2 [0x101000d0026,0x222000a0015]) (nd (lf 0x94421005f2 [0x1100150026,0x2000a]) (lf 0x50c21007f2 [0x20a010b0101,0x22000e0011,0x1020202010c,0xd000c0222,0x60015000a]))))) (nd (nd (nd (lf 0x54c21005f2 [0xa001d0012,0x150022000e,0x2]) (nd (lf 0x54c21007f2 [0x15000a001d,0x10c0035030b,0xe]) (lf 0xd4c21005f2 [0xa0012001d]))) (nd (lf 0x14121005e2 [0x20011000e,0xd0006000c,0x15]) (nd (lf 0x14121007e2 [0xf000d000e,0x102]) (lf 0x14121005f2 [0xd000e0102,0xf001d0026,0x6000c])))) (nd (nd (lf 0x14121007f2 [0xd000f000e,0x26001d0102]) (nd (lf 0xd4121007e2 [0xf000d000e,0x102]) (lf 0x88521007b2 [0xd000e0026,0x2000a]))) (nd (lf 0x4c521007d2 [0x1010015000d]) (nd (lf 0x8c521007d2 [0x1b0015000e,0x16030b]) (lf 0x50d21007f2 [0x10c0011000e,0xc02020102]))))))
def F7T7_3 := nd (nd (nd (nd (nd (lf 0x54d21005f2 [0xc000f000d,0xb0002]) (lf 0xd4d21005f2 [0x15000e0012])) (nd (lf 0x54221007e2 [0x11000a0015,0x102]) (nd (lf 0x94221005e2 [0x1100150026,0xc0002000a,0x6]) (lf 0x94221007e2 [0x1100150026,0x102000a])))) (nd (nd (lf 0x94221005f2 [0xf001d0026,0x102030b0301,0x6000c]) (nd (lf 0xc862100792 [0x11000e0026,0xd0015001d]) (lf 0xc8621007d2 [0x110015001d,0x22]))) (nd (lf 0xc8621007f2 [0xd000e001d,0x1020022000a]) (nd (lf 0x4c621007d2 [0x302001b0015,0x16000a030b]) (lf 0x4c621007f2 [0x15000d0026,0x202000a]))))) (nd (nd (nd (lf 0x8c621007d2 [0x10100150026,0x16000a001b]) (nd (lf 0x94621005f2 [0x301000a001d,0x6000c030b]) (lf 0x54a21005f2 [0xf000d000e,0x2]))) (nd (lf 0x50e21007f2 [0x10c01010011,0x102000e020a,0x10b000c0202,0x6000a000d]) (nd (lf 0x54e21005f2 [0xa00150012,0xe]) (lf 0xd4e21005f2 [0xc00110026,0x2])))) (nd (nd (lf 0x14131005e2 [0x22000d0201,0x20006]) (nd (lf 0x14131007e2 [0x1c0201000d,0x102]) (lf 0x14131005f2 [0x26000d0201,0x6000f0022]))) (nd (lf 0x14131007f2 [0x1020201000d,0x26001c0015]) (nd (lf 0xd4131007e2 [0x2010102000d,0x1d]) (lf 0x8c53100772 [0x1000d0026])))))) (nd (nd (nd (nd (lf 0x50531007d2 [0x201002e0020,0x110302010b,0x15]) (nd (lf 0x90531007d2 [0x2e0016000d,0x110302]) (lf 0x50931007f2 [0x2e0015000d,0x1020202]))) (nd (lf 0x90931007f2 [0x2e0016000d,0x20200110122,0x1110102]) (nd (lf 0x14931005f2 [0xd0201001d,0x6000a0022]) (lf 0x14931007f2 [0x150201000d,0x1d03020122,0x102])))) (nd (nd (lf 0xd4931005f2 [0x30202010011,0xa00020020]) (nd (lf 0xd4931007f2 [0x3020015000d,0x220102]) (lf 0x50d3100772 [0x302000c000d,0x11010b]))) (nd (lf 0x55131005f2 [0x602010020,0x2200020302,0xf]) (nd (lf 0xd5131005f2 [0x60201000d,0x302]) (lf 0x94231005f2 [0x30b000e0026,0x201000a]))))) (nd (nd (nd (lf 0x90631007d2 [0x20100120026,0x150011010b]) (nd (lf 0x90a31007f2 [0x2e00160012,0x1110122020a,0x202000e020e,0x22000a0102,0x11]) (lf 0x54a31005f2 [0x20011000e]))) (nd (lf 0x94a31005f2 [0x22000e001d,0x2030b0201,0x6]) (nd (lf 0x55231005f2 [0x3020012000e]) (lf 0xd5231005f2 [0x600120026,0x22000f])))) (nd (nd (lf 0x14143005f2 [0x102020b0201,0x20000a000c,0xf0022]) (nd (lf 0x14143007f2 [0x60102000c,0xe020b0201,0x11]) (lf 0x14543005f2 [0x20b02010026,0xf0002000a,0x22]))) (nd (lf 0x14543007f2 [0x2010006000c,0x1e0021000e,0x11020b0302,0x102]) (nd (lf 0xd4543005f2 [0x20b02010020,0xf00020302,0x22]) (lf 0xd4543007f2 [0xc0006000e,0x3020021020b,0xa00110102]))))))
def F7T7 : BTree NodeData := nd (nd F7T7_0 F7T7_1) (nd F7T7_2 F7T7_3)
def F7M7 : BST := BN 372177123 11520 (BN 315409365 4736 (BN 283333201 42496 (BN 249445111 31104 (BN 221609178 40321 (BN 202851723 9600 (BN 184747022 47745 (BN 172577486 9602 (BN 162718549 18305 (BL 118134329 36224) (BL 164135142 55682)) (BN 179934457 44672 (BL 177824751 35457) (BL 184415210 39296))) (BN 194409379 55680 (BN 192079090 22914 (BL 191015889 45057) (BL 192707434 22912)) (BN 199458233 52481 (BL 196852432 33026) (BL 202023710 116096)))) (BN 211526322 44290 (BN 206257174 44288 (BN 204645239 116865 (BL 203257286 127234) (BL 205468202 42880)) (BN 210328763 116864 (BL 207646659 129152) (BL 210913180 46464))) (BN 217191954 11522 (BN 214489854 53248 (BL 214220136 13953) (BL 214686185 63104)) (BN 219924983 38272 (BL 219443232 14081) BE)))) (BN 237726810 129409 (BN 230051522 45953 (BN 225780950 9729 (BN 222300516 124290 (BL 222298885 14722) (BL 222932198 3328)) (BN 227963086 13952 (BL 225848086 41089) (BL 228367327 54656))) (BN 233407167 23554 (BN 230289127 18304 (BL 230097700 26752) (BL 232955718 51202)) (BN 236495245 47744 (BL 235797974 44928) BE))) (BN 245544462 62722 (BN 241029435 34945 (BN 238910303 41985 (BL 237853136 44418) (BL 239715014 129408)) (BN 243952787 53506 (BL 241398062 25346) (BL 244386103 36608))) (BN 248524843 42624 (BN 246720058 116098 (BL 246455305 10112) (BL 247352647 27393)) (BN 249254915 1536 (BL 248641921 7552) BE))))) (BN 266755457 55040 (BN 259714096 59008 (BN 254218566 125312 (BN 251871205 35840 (BN 250458434 56322 (BL 250359011 128258) (BL 251149272 41984)) (BN 253242715 12160 (BL 252573122 121216) (BL 253752316 19969))) (BN 255997967 3841 (BN 254772385 34944 (BL 254295403 31105) (BL 255253149 41474)) (BN 257887455 42368 (BL 257366139 45569) (BL 259591616 27392)))) (BN 265238526 30080 (BN 261683981 45056 (BN 260627830 11904 (BL 260051622 19840) (BL 261421029 2306)) (BN 262737747 42369 (BL 262660910 6528) (BL 262782889 130562))) (BN 266072747 5378 (BN 265440684 61953 (BL 265369763 130050) (BL 266036248 10369)) (BN 266457356 52352 (BL 266302353 41601) BE)))) (BN 276256779 50561 (BN 272896253 13696 (BN 270126325 52480 (BN 268166995 58752 (BL 268097140 12929) (BL 268922538 49792)) (BN 272271146 38528 (BL 272261327 20224) (BL 272849928 20096))) (BN 275099860 64514 (BN 274074681 3840 (BL 273031384 55554) (BL 274744697 31361)) (BN 275424207 10368 (BL 275329604 61952) BE))) (BN 280049256 23936 (BN 277843949 14977 (BN 277026532 121345 (BL 276785937 56448) (BL 277596309 41088)) (BN 278820706 9344 (BL 278227871 61698) (BL 279658347 30722))) (BN 281552754 1408 (BN 281292593 51584 (BL 281079031 25216) (BL 281363601 54784)) (BN 282064080 121985 (BL 281705672 30336) BE)))))) (BN 299895610 18690 (BN 292581333 23680 (BN 288533283 59264 (BN 286282579 12546 (BN 285373689 120577 (BN 284600568 47361 (BL 283875493 125954) (BL 285289521 28416)) (BN 285884177 45442 (BL 285693859 28288) (BL 286275233 32896))) (BN 287764740 44800 (BN 286724569 126210 (BL 286311104 29825) (BL 286811330 48000)) (BN 288100691 19202 (BL 287960563 57473) (BL 288491600 29568)))) (BN 289381413 23042 (BN 288847072 30337 (BN 288649135 61184 (BL 288563792 117250) (BL 288720583 40961)) (BN 289249506 18560 (BL 288850182 15616) (BL 289265501 121344))) (BN 290254562 46082 (BN 289838226 8450 (BL 289521375 64128) (BL 289935522 43136)) (BN 291570910 37122 (BL 290506424 43649) BE)))) (BN 296643287 62080 (BN 295174971 61186 (BN 293341866 29312 (BN 292757252 124032 (BL 292719697 128) (BL 292996582 62720)) (BN 294717577 25472 (BL 293701499 14848) (BL 295097849 48003))) (BN 296133597 24321 (BN 295526736 130048 (BL 295494484 63232) (BL 295608287 36610)) (BN 296617849 40320 (BL 296449042 9728) BE))) (BN 297452557 14720 (BN 296975627 124800 (BN 296795128 57345 (BL 296724207 32770) (BL 296975234 126209)) (BN 297162927 46337 (BL 297102361 39808) (BL 297271101 124288))) (BN 298836259 58624 (BN 297811131 128256 (BL 297575595 127490) (BL 298176439 16384)) (BN 299781917 5377 (BL 299381888 21888) BE))))) (BN 307533869 45441 (BN 304885432 5504 (BN 302159864 11776 (BN 301784210 26240 (BN 300961980 45314 (BL 300345173 127104) (BL 301756239 34432)) (BN 301993844 35456 (BL 301931590 61696) (BL 302047585 52992))) (BN 303310192 128768 (BN 303016883 49536 (BL 302705269 116224) (BL 303034904 59904)) (BN 304506053 125056 (BL 303900820 57088) (BL 304859760 46721)))) (BN 306017939 58240 (BN 305317502 48896 (BN 305166551 54530 (BL 305060193 45952) (BL 305237472 29953)) (BN 305880798 34816 (BL 305325809 3712) (BL 305994569 34946))) (BN 306618783 120064 (BN 306454304 2 (BL 306103216 51072) (BL 306456943 36352)) (BN 307205891 20480 (BL 306684048 57344) BE)))) (BN 311972213 10881 (BN 309423723 123008 (BN 308588323 57601 (BN 307824232 120192 (BL 307791141 54400) (BL 308278213 16512)) (BN 308873379 8321 (BL 308622177 20738) (BL 308954255 57984))) (BN 309989844 40064 (BN 309522073 45440 (BL 309481738 122880) (BL 309819736 121858)) (BN 310812812 117376 (BL 310305327 31233) BE))) (BN 314504797 44416 (BN 313258351 16642 (BN 312412623 116738 (BL 312318858 12032) (BL 312429026 30465)) (BN 313524867 5376 (BL 313416892 121090) (BL 313850208 42242))) (BN 314896648 21762 (BN 314545560 116608 (BL 314531488 19968) (BL 314646304 40705)) (BN 315353830 1152 (BL 315126392 29952) BE))))))) (BN 343182977 24066 (BN 328980775 54528 (BN 323483511 20226 (BN 320166395 34433 (BN 317721878 123520 (BN 317409772 130688 (BN 316662868 4353 (BL 315613294 31746) (BL 317396599 129664)) (BN 317629677 35200 (BL 317465339 47232) (BL 317710403 51328))) (BN 318602710 46720 (BN 318250435 16640 (BL 317727732 55552) (BL 318379872 64001)) (BN 319761183 55808 (BL 319252170 12672) (BL 320005210 128640)))) (BN 320946632 258 (BN 320538431 32768 (BN 320186666 2432 (BL 320173511 40448) (BL 320329828 40704)) (BN 320649507 39170 (BL 320639648 52736) (BL 320854967 58114))) (BN 321527387 126720 (BN 321284638 65280 (BL 321080958 62976) (BL 321520338 43520)) (BN 322968161 128384 (BL 322653095 39424) BE)))) (BN 326085674 28034 (BN 324985738 4608 (BN 324102462 12673 (BN 323587996 50048 (BL 323533506 116994) (BL 324030512 24448)) (BN 324595914 117120 (BL 324413419 119680) (BL 324788730 118017))) (BN 325852116 384 (BN 325342063 47490 (BL 325299840 19584) (BL 325514914 16129)) (BN 326072021 18816 (BL 326047345 10624) BE))) (BN 328451568 35968 (BN 328034231 45568 (BN 326830244 15873 (BL 326551788 4352) (BL 327922910 51200)) (BN 328268792 64000 (BL 328254307 121856) (BL 328304227 53888))) (BN 328608739 13184 (BN 328473769 8448 (BL 328465045 51843) (BL 328485614 12034)) (BN 328875888 126082 (BL 328765701 124418) BE))))) (BN 337497417 52994 (BN 334140382 7808 (BN 332030340 125824 (BN 329592172 14976 (BN 329385646 51842 (BL 329010765 27906) (BL 329589581 126208)) (BN 330040577 118786 (BL 329796849 14080) (BL 330722795 1664))) (BN 333457190 59906 (BN 332846990 32128 (BL 332652603 53377) (BL 333263603 51458)) (BN 333699583 120832 (BL 333550710 21121) (BL 333812303 121984)))) (BN 335936635 22017 (BN 334904789 48641 (BN 334396099 32256 (BL 334176689 118016) (BL 334837980 34176)) (BN 335552811 33536 (BL 335272788 24704) (BL 335849151 46849))) (BN 336833533 23040 (BN 336348791 47360 (BL 336015912 32000) (BL 336365254 25344)) (BN 337416411 26114 (BL 336879776 4096) BE)))) (BN 341094580 53122 (BN 338482921 36098 (BN 337892978 30720 (BN 337702234 6658 (BL 337700774 22786) (BL 337720582 57472)) (BN 338262208 7169 (BL 337951976 8833) (BL 338285191 6146))) (BN 339871319 53504 (BN 339208664 6785 (BL 339003847 20992) (BL 339744557 1794)) (BN 341034420 16128 (BL 340689401 4354) BE))) (BN 342141927 62208 (BN 341507623 36993 (BN 341427941 52354 (BL 341289334 35712) (BL 341475253 40832)) (BN 342039236 24834 (BL 341725432 25858) (BL 342123175 125440))) (BN 342889138 10754 (BN 342254647 43648 (BL 342151273 50817) (BL 342838443 118144)) (BN 343136450 17024 (BL 342989336 64642) BE)))))) (BN 359714462 126464 (BN 351814634 12674 (BN 347401617 41472 (BN 344836486 121728 (BN 344489571 45443 (BN 344004504 24320 (BL 343314885 51840) (BL 344042003 6656)) (BN 344691891 25090 (BL 344564526 1792) (BL 344793709 48640))) (BN 346336753 39937 (BN 346109632 23552 (BL 345939761 37760) (BL 346335322 19200)) (BN 346727535 119554 (BL 346517222 10752) (BL 347347730 123392)))) (BN 349902654 127616 (BN 348654867 5634 (BN 347492448 129536 (BL 347429281 118912) (BL 347661434 27008)) (BN 349327646 15489 (BL 349103290 115840) (BL 349482649 62592))) (BN 351516651 120576 (BN 351208190 56321 (BL 350595690 44162) (BL 351431680 39554)) (BN 351645933 19586 (BL 351628437 22528) BE)))) (BN 355958408 43521 (BN 355069902 28160 (BN 353883400 14849 (BN 353368214 11392 (BL 352488289 63872) (BL 353772030 118914)) (BN 354132130 130049 (BL 354029548 40576) (BL 354816191 18432))) (BN 355739338 49922 (BN 355616300 47488 (BL 355257624 64384) (BL 355714662 33794)) (BN 355888576 56320 (BL 355794357 117888) BE))) (BN 357823970 18176 (BN 356539686 48898 (BN 356049616 25218 (BL 356047990 116353) (BL 356225673 39936)) (BN 357732502 8064 (BL 357338581 63873) (BL 357769990 27265))) (BN 359237854 42497 (BN 358876900 1281 (BL 358382029 122368) (BL 359125723 28930)) (BN 359523157 28672 (BL 359388675 40960) BE))))) (BN 366222780 46208 (BN 363699968 129920 (BN 361263922 17792 (BN 360621602 8320 (BN 360070781 45824 (BL 359897186 5248) (BL 360511990 62848)) (BN 360800067 127488 (BL 360645907 63234) (BL 360955782 26499))) (BN 363189158 60800 (BN 362055863 33025 (BL 361457193 64512) (BL 362920046 129537)) (BN 363555242 48768 (BL 363258535 41728) BE))) (BN 364181682 123776 (BN 364104324 48256 (BN 364007047 130177 (BL 363720436 10880) (BL 364044067 33024)) (BN 364162050 3200 (BL 364160424 122752) (BL 364177249 30464))) (BN 365556901 63362 (BN 364491960 64130 (BL 364206878 46978) (BL 365029665 29824)) (BN 366209373 12675 (BL 365826067 35074) BE)))) (BN 369187519 118528 (BN 367965501 40192 (BN 367407294 128898 (BN 366627232 64640 (BL 366269614 60544) (BL 366752066 125185)) (BN 367775477 54272 (BL 367555562 118656) (BL 367831019 46336))) (BN 368918244 42112 (BN 368307087 48384 (BL 368020541 12288) (BL 368687523 32514)) (BN 369147827 5760 (BL 369026847 46976) BE))) (BN 371006257 36736 (BN 370051850 17920 (BN 369706266 25984 (BL 369545204 15360) (BL 369798635 4224)) (BN 370685879 15232 (BL 370311047 33664) (BL 370998167 64896))) (BN 371422094 49410 (BN 371149192 122243 (BL 371071340 117248) (BL 371251321 11648)) (BN 372123326 56961 (BL 371815812 27136) BE)))))))) (BN 423682826 22272 (BN 396106987 47872 (BN 384956883 12544 (BN 378624456 130561 (BN 375851932 64513 (BN 373926397 120448 (BN 372602768 16256 (BN 372449391 23169 (BL 372423476 126848) (BL 372546668 60032)) (BN 373774164 130560 (BL 372895009 34049) (BL 373777037 41218))) (BN 375069576 39552 (BN 374781607 65024 (BL 374380042 128128) (BL 374826611 6401)) (BN 375185018 6016 (BL 375168701 15744) (BL 375304505 12416)))) (BN 377032500 2562 (BN 376217821 15104 (BN 375964435 128000 (BL 375893106 118400) (BL 376207922 4610)) (BN 376462885 19712 (BL 376426327 28800) (BL 376902175 127232))) (BN 377601029 9088 (BN 377492697 118784 (BL 377058635 26624) (BL 377590171 22144)) (BN 377813089 53120 (BL 377624056 28418) BE)))) (BN 381940545 128896 (BN 379591536 62339 (BN 378887828 50434 (BN 378780715 54912 (BL 378753391 43904) (BL 378783725 640)) (BN 379256415 57600 (BL 379143825 32769) (BL 379440511 19328))) (BN 381199196 123265 (BN 380909310 118272 (BL 380037120 5632) (BL 380973419 31232)) (BN 381647254 12418 (BL 381235215 17536) BE))) (BN 383611045 127872 (BN 382810960 44802 (BN 382305262 14593 (BL 382194255 57216) (BL 382549797 125952)) (BN 383312983 42113 (BL 382839116 40578) (BL 383451016 2048))) (BN 384639503 62721 (BN 384098263 3456 (BL 383924840 57986) (BL 384406779 34560)) (BN 384868531 26112 (BL 384715531 6400) BE))))) (BN 390341258 64768 (BN 387497855 120320 (BN 386468888 0 (BN 385500979 4864 (BN 385154354 17152 (BL 385152654 10626) (BL 385424113 126080)) (BN 386043373 7040 (BL 385935041 36096) (BL 386085507 17537))) (BN 386649357 39042 (BN 386571862 11521 (BL 386494972 55042) (BL 386601365 14594)) (BN 387226069 55936 (BL 386918671 16898) (BL 387423633 1026)))) (BN 389641540 127361 (BN 388332699 120960 (BN 387597374 46848 (BL 387586169 54529) (BL 387664643 119808)) (BN 388942766 14082 (BL 388576689 65282) (BL 389072491 16000))) (BN 390010848 21632 (BN 389706704 30976 (BL 389700199 8832) (BL 389789068 119296)) (BN 390226031 43264 (BL 390083202 29185) BE)))) (BN 392213258 23553 (BN 391453374 26625 (BN 390807918 22656 (BN 390471446 41600 (BL 390416815 18434) (BL 390488415 117760)) (BN 391115022 24064 (BL 390956887 6784) (BL 391405085 115969))) (BN 391979548 31872 (BN 391702894 130944 (BL 391620933 35586) (BL 391893360 768)) (BN 392206976 122496 (BL 392144011 25088) BE))) (BN 394911232 21760 (BN 392616580 57729 (BN 392367184 129666 (BL 392311685 119424) (BL 392610537 38914)) (BN 393447254 45696 (BL 393255846 36992) (BL 394512764 19072))) (BN 395865977 117506 (BN 395580154 56066 (BL 395062844 116736) (BL 395661160 59522)) (BN 395977264 50818 (BL 395958855 51841) BE)))))) (BN 408053632 35328 (BN 401992706 44160 (BN 399554809 57728 (BN 398317191 119426 (BN 396888503 122240 (BN 396458992 54401 (BL 396425951 49665) (BL 396878371 48643)) (BN 397639386 7424 (BL 397498336 15872) (BL 398310776 17921))) (BN 398749788 50816 (BN 398537662 20608 (BL 398376266 29698) (BL 398569914 116992)) (BN 398913790 31360 (BL 398859159 41730) (BL 399077441 50688)))) (BN 400754029 9856 (BN 400418327 17666 (BN 399895718 4865 (BL 399636284 45312) (BL 400241273 50560)) (BN 400728569 125441 (BL 400421892 125568) (BL 400735696 2176))) (BN 401057777 27648 (BN 400863627 1 (BL 400839517 14336) (BL 401052881 13058)) (BN 401592188 17280 (BL 401058924 61825) BE)))) (BN 405881807 48128 (BN 404500496 8705 (BN 403834530 124544 (BN 402737335 28032 (BL 402275410 63360) (BL 403505188 58112)) (BN 404291343 122624 (BL 404103504 21376) (BL 404295111 38016))) (BN 405090763 59520 (BN 404736893 63746 (BL 404675734 50176) (BL 404906161 58369)) (BN 405511359 120578 (BL 405330847 62336) BE))) (BN 406770330 58496 (BN 406078082 35584 (BN 405953124 123393 (BL 405941861 128257) (BL 405993454 61056)) (BN 406658949 33408 (BL 406181763 42240) (BL 406759535 9858))) (BN 407592714 117632 (BN 407097335 33920 (BL 406818610 64258) (BL 407145881 60673)) (BN 408049396 33152 (BL 407997153 61824) BE))))) (BN 415681792 11264 (BN 412027393 37889 (BN 409305971 21761 (BN 408736655 35458 (BN 408375736 25730 (BL 408066397 2688) (BL 408443251 116352)) (BN 408930300 7168 (BL 408880278 37504) (BL 409281861 127744))) (BN 410625123 1280 (BN 409517176 130816 (BL 409500121 38656) (BL 410034532 60288)) (BN 411843786 8322 (BL 410644834 36480) BE))) (BN 414389416 8704 (BN 413348505 60161 (BN 412778684 512 (BL 412036058 124162) (BL 413278187 57856)) (BN 413723167 56704 (BL 413699676 15874) (BL 414287598 31744))) (BN 415174864 18944 (BN 414941835 50177 (BL 414453579 48512) (BL 415101293 121472)) (BN 415362036 39040 (BL 415240482 60416) BE)))) (BN 420036993 37506 (BN 417878205 7680 (BN 417253929 17408 (BN 416923280 57346 (BL 416121172 55296) (BL 416954322 118530)) (BN 417355740 12928 (BL 417322622 18048) (BL 417817055 6273))) (BN 419492640 26496 (BN 418809650 20610 (BL 418273115 8194) (BL 418873381 56192)) (BN 419899916 33280 (BL 419666851 4992) BE))) (BN 422034102 23424 (BN 421056441 22530 (BN 420469737 39681 (BL 420219606 18689) (BL 420966784 30592)) (BN 421437646 24577 (BL 421293613 49408) (BL 421936889 38146))) (BN 422895923 2944 (BN 422448371 35329 (BL 422207810 18688) (BL 422628637 24960)) (BN 423242623 115970 (BL 423004534 128130) BE))))))) (BN 459001586 29441 (BN 441212442 15235 (BN 431937907 35072 (BN 427009223 39168 (BN 425035723 52864 (BN 424327816 30848 (BN 424124136 124672 (BL 423753280 129282) (BL 424208150 32512)) (BN 424643232 34048 (BL 424563516 29440) (BL 424951762 8576))) (BN 425829883 54144 (BN 425648949 58882 (BL 425365624 29954) (BL 425696273 11008)) (BN 426791424 19456 (BL 426715459 13570) (BL 426845532 21120)))) (BN 429569603 18945 (BN 427940001 2560 (BN 427672926 57857 (BL 427633010 10242) (BL 427711468 7936)) (BN 428551117 63744 (BL 428479337 18050) (BL 429498785 45826))) (BN 431324448 25728 (BN 430537469 62465 (BL 429814293 52608) (BL 431070981 29056)) (BN 431919066 7298 (BL 431500530 56832) BE)))) (BN 436788167 22784 (BN 435031721 28801 (BN 434053485 14592 (BN 432765436 41344 (BL 432107781 22785) (BL 433369940 14464)) (BN 434370791 12800 (BL 434056987 25856) (BL 434714529 1920))) (BN 436661509 55424 (BN 435787799 120962 (BL 435196243 8962) (BL 435893972 59776)) (BN 436724009 63488 (BL 436703396 31616) BE))) (BN 439130263 10240 (BN 437420158 125184 (BN 436887405 38402 (BL 436788199 35073) (BL 436977195 15875)) (BN 438780981 125058 (BL 438642837 1024) (BL 438979813 129793))) (BN 440713540 16896 (BN 440023531 40450 (BL 439398958 50304) (BL 440290228 13440)) (BN 441118056 38912 (BL 440974703 22658) BE))))) (BN 450444795 121088 (BN 445082414 59650 (BN 443156873 34688 (BN 442198801 36864 (BN 442047025 60928 (BL 441305386 123137) (BL 442093282 123904)) (BN 442296873 9216 (BL 442262086 24192) (BL 442356784 45184))) (BN 444249250 50305 (BN 443732579 6402 (BL 443587856 7296) (BL 443845241 129024)) (BN 444872152 41346 (BL 444658715 4226) (BL 444912498 130432)))) (BN 447169349 129281 (BN 446221906 11650 (BN 446025072 123264 (BL 445166353 51968) (BL 446056508 50944)) (BN 446740432 30850 (BL 446311279 122112) (BL 447085181 117504))) (BN 449152810 37120 (BN 448174591 119936 (BL 447539349 61440) (BL 449025623 63616)) (BN 449560400 13056 (BL 449191565 896) BE)))) (BN 454467416 127360 (BN 452389641 61441 (BN 451421696 126336 (BN 450559242 55297 (BL 450535626 125696) (BL 450739217 43776)) (BN 451787780 32384 (BL 451433470 27904) (BL 451957880 2178))) (BN 454194866 65152 (BN 453354842 52096 (BL 452392962 49024) (BL 453638868 27778)) (BN 454276614 126592 (BL 454251368 20737) BE))) (BN 457290144 50432 (BN 456314982 5120 (BN 455788100 28544 (BL 454581084 21250) (BL 455981693 130304)) (BN 456821696 53376 (BL 456751523 45185) (BL 457175308 116993))) (BN 457932993 51712 (BN 457520880 123905 (BL 457514178 38018) (BL 457633909 11136)) (BN 458931754 20736 (BL 458287146 56960) BE)))))) (BN 481939083 27264 (BN 469389009 38144 (BN 464599678 37376 (BN 462701082 58498 (BN 460831985 130305 (BN 460156449 27776 (BL 459488178 124160) (BL 460751294 29184)) (BN 461455208 126976 (BL 460835306 32640) (BL 462272091 33792))) (BN 463449388 61568 (BN 463058094 20354 (BL 462757640 7682) (BL 463164445 53378)) (BN 464230444 61312 (BL 463843245 49920) (BL 464500371 51456)))) (BN 466416646 47104 (BN 465672174 6144 (BN 464757326 6912 (BL 464652684 21504) (BL 465442031 41602)) (BN 465854206 65408 (BL 465725235 8192) (BL 465963224 125697))) (BN 468269658 38400 (BN 467113162 65026 (BL 467094043 49664) (BL 467464595 16768)) (BN 468956015 43392 (BL 468466811 13442) BE)))) (BN 475843186 6272 (BN 473496739 15488 (BN 472588382 119040 (BN 471071654 24194 (BL 470296481 30594) (BL 471720910 53760)) (BN 473101069 58880 (BL 473095028 23296) (BL 473112849 39169))) (BN 474637954 29696 (BN 474114518 119552 (BL 473884375 31362) (BL 474167579 13568)) (BN 475574253 58368 (BL 474858990 2816) BE))) (BN 478534346 23808 (BN 476809227 130818 (BN 475900040 56834 (BL 475897181 13312) (BL 476569537 21249)) (BN 477749068 36738 (BL 476817342 256) (BL 477813973 60672))) (BN 479945353 2304 (BN 479025597 22016 (BL 478895110 51457) (BL 479127961 20352)) (BN 481667634 257 (BL 480545180 8066) BE))))) (BN 502485061 48642 (BN 487911709 56064 (BN 484016597 60160 (BN 483021272 122370 (BN 482695485 37888 (BL 482098689 3072) (BL 482960632 124416)) (BN 483384638 23809 (BL 483080298 64256) (BL 483812692 121602))) (BN 485762628 7810 (BN 485592975 24832 (BL 484339525 31488) (BL 485655578 56576)) (BN 487309979 47616 (BL 486543869 25600) BE))) (BN 494431211 34304 (BN 490541033 116480 (BN 489328928 46080 (BL 488176140 130176) (BL 490505870 56577)) (BN 492105738 24576 (BL 491137829 39680) (BL 492911610 21505))) (BN 496618484 23168 (BN 495256436 37121 (BL 494502906 6274) (BL 495329403 63489)) (BN 502450635 129025 (BL 501353954 23297) BE)))) (BN 522943094 26880 (BN 511973478 123136 (BN 503771747 51969 (BN 502679462 28928 (BL 502654466 43008) (BL 503075354 49152)) (BN 509775698 59392 (BL 504219460 17664) (BL 511096810 123648))) (BN 517049205 43009 (BN 515574178 115968 (BL 513312311 129280) (BL 515821862 10496)) (BN 518218042 37632 (BL 517330776 41216) BE))) (BN 552533827 124928 (BN 532612781 37633 (BN 525491549 123649 (BL 524170437 59393) (BL 530983179 8960)) (BN 541954681 9472 (BL 534595668 21248) (BL 543756718 59648))) (BN 576144247 121600 (BN 560976171 54016 (BL 559508487 52224) (BL 573626431 62464)) (BN 582803880 44032 (BL 582068775 129792) BE))))))))
def F7T8 : BTree NodeData := nd (nd (nd (lf 0x10003e1 [0x10b0101000a,0x2]) (nd (lf 0x10003d1 [0x10b01010002]) (lf 0x10003f1 [0x10b01010002,0xa]))) (nd (nd (lf 0x210003d1 [0x10b01010002]) (lf 0x210003f1 [0x10b000e0002,0x1010026])) (nd (lf 0x310003e1 [0x101000a0002,0x10b]) (lf 0x130003e1 [0x10b00010002])))) (nd (nd (nd (lf 0x230003e1 [0x200010012]) (lf 0x230003f1 [0x10b00010002,0x17000c])) (nd (lf 0x21003f1 [0x10100220026,0xa0002010b,0x1d]) (lf 0x121003f1 [0x1020011000e,0x2010b0101,0x15000d]))) (nd (nd (lf 0x221003f1 [0x10b00150026,0x101000a0002,0x11]) (lf 0x131003f1 [0x102000d0001,0x2010b])) (nd (lf 0x231003f1 [0xe000a0001,0x2010b0102]) (lf 0x143003f1 [0x102000b0001,0x2000c]))))
def F7M8 : BST := BN 354965618 385 (BN 306674906 2176 (BN 281825493 27648 (BN 259176297 2944 (BN 239820481 14721 (BN 225240092 1408 (BN 218233755 26881 (BN 195642955 13314 (BL 179934457 10624) BE) (BN 223251888 1409 (BL 223073011 14592) BE)) (BN 234970189 14720 (BN 229477865 15616 (BL 225956237 13569) BE) (BL 238098200 27008))) (BN 258311398 28544 (BN 253806698 10754 (BN 246152908 27264 (BL 240778227 26114) BE) (BN 255034834 27393 (BL 254926683 2177) BE)) (BN 258843025 4224 (BN 258688022 9345 (BL 258556462 14976) BE) (BL 259173707 7937)))) (BN 271329439 4480 (BN 268137246 8576 (BN 263322697 384 (BN 261280137 30081 (BL 259627746 13568) BE) (BN 267130366 8833 (BL 263369027 11393) BE)) (BN 270108032 1665 (BN 269981978 26880 (BL 269061017 128) BE) (BL 270995489 29953))) (BN 279788003 4096 (BN 273464700 25728 (BN 273031384 12672 (BL 271726919 6016) BE) (BL 276679013 29952)) (BN 281473728 2432 (BN 280700049 32002 (BL 280645715 29056) BE) (BL 281678405 14593))))) (BN 298686133 29698 (BN 289003468 6400 (BN 285364365 1920 (BN 283850982 1664 (BN 282977635 27010 (BL 281907044 25216) BE) (BN 284879179 4352 (BL 283961293 3841) BE)) (BN 288230347 9728 (BN 286444736 9217 (BL 285693859 29312) BE) (BL 288706343 27392))) (BN 294519281 5121 (BN 291590342 8960 (BN 290499626 12290 (BL 289602138 8961) BE) (BL 294317259 13312)) (BN 295114845 13697 (BN 295094462 9088 (BL 294887080 28929) BE) (BL 295834054 10370)))) (BN 303873140 13440 (BN 301778310 5888 (BN 300074086 6913 (BN 299306890 16002 (BL 298941970 5634) BE) (BN 301339924 5248 (BL 301320439 768) BE)) (BN 302961625 10497 (BN 302890704 27650 (BL 301932958 9089) BE) (BL 303398207 6401))) (BN 305711744 28288 (BN 304448450 32000 (BN 304408201 5120 (BL 304276398 27778) BE) (BL 304502804 13696)) (BN 306170731 769 (BN 305878926 26496 (BL 305757610 6912) BE) (BL 306342027 7040)))))) (BN 337180489 13184 (BN 322944786 16000 (BN 315353830 3456 (BN 312513448 6914 (BN 310096072 5376 (BN 310024344 30082 (BL 309782268 4736) BE) (BN 312503158 27904 (BL 311663055 896) BE)) (BN 314553064 512 (BN 312850545 10496 (BL 312620801 11266) BE) (BL 315117250 11392))) (BN 320956582 16001 (BN 317039160 6273 (BN 316058805 9472 (BL 315601992 12928) BE) (BL 317685509 130)) (BN 321286184 32513 (BN 321276933 3329 (BL 321204162 26882) BE) (BL 321396434 8706)))) (BN 331016281 16129 (BN 325481504 15489 (BN 323803520 14850 (BN 323796174 28032 (BL 323771498 30592) BE) (BN 324573081 30850 (BL 324560965 4609) BE)) (BN 327182559 7424 (BN 326769257 26753 (BL 326116189 4864) BE) (BL 330040577 2))) (BN 333527047 14978 (BN 332674883 7808 (BN 332635510 12801 (BL 332105859 3840) BE) (BL 333015425 642)) (BN 335802894 28290 (BN 335211601 7297 (BL 334396099 5760) BE) (BL 336040315 30976))))) (BN 342838443 30336 (BN 339478930 1280 (BN 338013367 31104 (BN 337892268 7936 (BN 337593568 26240 (BL 337525175 7809) BE) (BN 337997372 30594 (BL 337951976 12417) BE)) (BN 338633202 11136 (BN 338502320 30848 (BL 338482921 31234) BE) (BL 339446083 6658))) (BN 341833873 25856 (BN 341397455 7042 (BN 341141378 6528 (BL 340430887 27649) BE) (BL 341581755 9600)) (BN 342524430 12800 (BN 342199000 12033 (BL 342078601 26368) BE) (BL 342812526 14594)))) (BN 346944664 640 (BN 346138253 3072 (BN 343857602 2688 (BN 343852474 27523 (BL 342863659 31105) BE) (BN 345137402 29440 (BL 344734968 26241) BE)) (BN 346624998 27521 (BN 346543936 8064 (BL 346394320 29825) BE) (BL 346789000 5504))) (BN 352481002 29696 (BN 350342824 3584 (BN 348354620 3585 (BL 347755950 11264) BE) (BL 350363235 16258)) (BN 352631377 28801 (BN 352612103 10242 (BL 352542623 6402) BE) (BL 354064335 26624))))))) (BN 395063108 1152 (BN 370912470 2816 (BN 363636990 3968 (BN 360590171 31490 (BN 357912284 16003 (BN 356849876 27138 (BN 356261156 25984 (BL 355480469 14208) BE) (BN 357112828 9216 (BL 356878401 28417) BE)) (BN 359942053 14080 (BN 359677769 31616 (BL 358875446 6274) BE) (BL 360072921 13824))) (BN 361318256 5378 (BN 361054447 28162 (BN 360747656 9857 (BL 360667373 15232) BE) (BL 361073721 3201)) (BN 362506679 7680 (BN 362342200 2050 (BL 362150689 11265) BE) (BL 363200932 26112)))) (BN 367317790 15490 (BN 365237347 7810 (BN 364923213 13825 (BN 364351385 10368 (BL 363725342 27906) BE) (BN 365118912 4354 (BL 365054209 28546) BE)) (BN 366433102 16256 (BN 366002928 27266 (BL 365555172 28928) BE) (BL 366799179 6272))) (BN 368848554 8704 (BN 368475163 31872 (BN 368325100 15744 (BL 368082444 14336) BE) (BL 368557527 13056)) (BN 370784544 11778 (BN 369767998 5122 (BL 369403556 15872) BE) (BL 370811812 30080))))) (BN 380483810 10112 (BN 376426327 10240 (BN 374490606 9856 (BN 372104195 8320 (BN 371255640 14848 (BL 371117833 1026) BE) (BN 373025156 3328 (BL 372793729 27776) BE)) (BN 375849252 8322 (BN 375241523 15488 (BL 375216850 11520) BE) (BL 376267976 8577))) (BN 379367905 3330 (BN 378210342 10498 (BN 377492697 0 (BL 376524788 256) BE) (BL 378404743 7426)) (BN 379944741 31874 (BN 379632086 7811 (BL 379560177 12546) BE) (BL 380029415 6657)))) (BN 389037592 7298 (BN 384721583 4865 (BN 381645491 2178 (BN 381133869 1154 (BL 380595248 26754) BE) (BN 383367772 26752 (BL 382857115 9344) BE)) (BN 388204320 8194 (BN 385935041 31232 (BL 384868671 28160) BE) (BL 388737037 2690))) (BN 391299459 8832 (BN 390092808 32514 (BN 390087835 11394 (BL 389700199 12416) BE) (BL 390213907 4992)) (BN 392180564 7168 (BN 392046646 25344 (BL 391810116 7296) BE) (BL 394810735 11648)))))) (BN 428063185 14466 (BN 412821944 3200 (BN 402203612 4995 (BN 398142543 29824 (BN 396646664 1538 (BN 395689846 32128 (BL 395229057 4608) BE) (BN 398016541 32512 (BL 397360437 10752) BE)) (BN 400976269 4866 (BN 400683995 26369 (BL 399077441 15360) BE) (BL 401878605 27522))) (BN 408009058 9984 (BN 406198673 31744 (BN 404379600 28800 (BL 403253079 7552) BE) (BL 406441385 25345)) (BN 411812610 16130 (BN 410706366 25346 (BL 408721689 6786) BE) (BL 411933709 25472)))) (BN 420917561 12032 (BN 416593607 14464 (BN 414195576 27520 (BN 413139250 11008 (BL 412862853 7938) BE) (BN 415602358 2560 (BL 414585134 16128) BE)) (BN 419481999 11010 (BN 419161799 25601 (BL 416637394 29568) BE) (BL 420326029 1792))) (BN 423116428 6787 (BN 422403797 9985 (BN 421759585 5506 (BL 421038660 6784) BE) (BL 422702648 26370)) (BN 425888952 6785 (BN 425176321 1793 (BL 423454040 31488) BE) (BL 427604143 2305))))) (BN 454665640 32640 (BN 443474065 28161 (BN 435596962 28416 (BN 431777638 6656 (BN 429814293 31360 (BL 429101662 30464) BE) (BN 435031721 10241 (BL 432432745 9986) BE)) (BN 441208378 30466 (BN 439715124 13952 (BL 438595773 32642) BE) (BL 442356784 2048))) (BN 449181431 29184 (BN 446900780 10880 (BN 446188149 15104 (BL 444493694 32384) BE) (BL 448157468 3712)) (BN 451869528 12160 (BN 450799128 11776 (BL 449348012 11904) BE) (BL 453286747 8066)))) (BN 467966391 30209 (BN 459524047 28673 (BN 456751523 2049 (BN 455524180 27136 (BL 454673755 28672) BE) (BN 458294865 15106 (BL 457801766 12288) BE)) (BN 465193867 11777 (BN 463449388 1024 (BL 463116099 30208) BE) (BL 466244110 5632))) (BN 493678275 6144 (BN 488978219 1536 (BN 480535875 8192 (BL 471891732 12544) BE) (BL 489829891 25600)) (BN 502120619 32256 (BN 500799507 30720 (BL 498272235 2304) BE) (BL 509241851 8448)))))))
def F7T9 : BTree NodeData := lf 0x1f0 [0xb00010002]
def F7M9 : BST := BN 318680735 897 (BN 273085718 258 (BN 251559376 1793 (BN 233163896 514 (BL 221863534 256) (BL 247312352 129)) (BN 255754696 1153 (BL 252151608 898) (BL 258556462 384))) (BN 299060575 128 (BN 282885295 2 (BL 280616016 512) (BL 291327639 1538)) (BN 310757002 899 (BL 307502919 1152) (BL 318082065 1410)))) (BN 335249328 1409 (BN 330399036 1408 (BN 324906712 1280 (BL 320668939 896) (BL 330277937 1792)) (BN 332476804 1411 (BL 331249461 1282) (BL 333527047 386))) (BN 352975840 770 (BN 340869124 768 (BL 339174669 1920) (BL 341581755 640)) (BN 375216850 0 (BL 356261156 1664) (BL 383659194 1536))))
def F7L : Nat → Option (BTree NodeData) | 3 => some F7T3 | 4 => some F7T4 | 5 => some F7T5 | 6 => some F7T6 | 7 => some F7T7 | 8 => some F7T8 | 9 => some F7T9 | _ => none
def F7M : Nat → BST | 4 => F7M4 | 5 => F7M5 | 6 => F7M6 | 7 => F7M7 | 8 => F7M8 | 9 => F7M9 | _ => BE
def tRt : Sig := 0xeae8e880e880e880#64
def RtP : List Row := mkRows [51,53,54,57,51,53,54,57,51,53,57,7,11,7,13,7,14,11,13,7,11,7,13,7,14,11,13,51,54,57,53,54,57,53,54,57,51,54,57,51,53,51,53,53,54,57,51,54,57,51,53,51,53,54,11,14,13,14,13,14,11,14]
def RtN : List Row := mkRows [19,21,22,25,35,37,38,41,49,49,49,19,19,21,21,22,22,25,25,35,35,37,37,38,38,41,41,58,58,58,60,60,60,19,19,19,21,21,21,22,22,25,25,35,35,35,37,37,37,38,38,41,41,49,58,58,60,60,19,19,21,21]
def RtR : List (Nat × Nat) := [(1540072585834725307,4339779533176471483),(4245437271898831189,920486456858351701),(3437545205713988198,3677120864855384166),(4593988593459352712,276977982709825672),(18014398375266303,4602687615131975439),(18014398375266303,288221588648101872)]
def RtA : List (List Nat) := [[0,1,2,3,4,5],[0,1,2,3,5,4],[0,2,1,3,4,5],[0,2,1,3,5,4]]
def RtC : List CutSpec := [⟨0,16,10,7,0,[0,1,2,3,5,4],0xffff0000ffff0000#64⟩]
def RtT9 : BTree NodeData := lf 0x3f0 [0x1]
def RtL : Nat → Option (BTree NodeData) | 9 => some RtT9 | _ => none
def RtM : Nat → BST | _ => BE
end CertData
noncomputable section CertVerify
abbrev ok (f : Forest) (k : Nat) (t : BTree NodeData) := t.all (fastNodeOK f k) = true
def base0 (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
private theorem base0_s : ∀ k, k ≠ 0 → LowerBV (base0 k).1 (base0 k).2.1 (base0 k).2.2 := fun _ _ _ _ _ _ => Nat.zero_le _
def fF1 : Forest := ⟨7,tF1,3,F1P,F1N,F1R,F1A,F1C,F1L,F1M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1v : graphValid fF1 base0 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F1k3 : ok fF1 3 F1T3 := by decide +kernel
private theorem F1lv : levelsChecked fF1 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fF1,F1L] at ht
  subst ht; exact F1k3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF1 : LowerBV (rawOf 7) tF1 4 :=
  lower_forest fF1 base0 base0_s F1v F1lv (by decide +kernel)
def base1 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | _ => ([],0,0)
private theorem base1_s : ∀ k, k ≠ 0 → LowerBV (base1 k).1 (base1 k).2.1 (base1 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 0 | _ + 2 => exact fun _ _ _ _ => Nat.zero_le _
def fF2 : Forest := ⟨15,tF2,4,F2P,F2N,F2R,F2A,F2C,F2L,F2M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2v : graphValid fF2 base1 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F2k4 : ok fF2 4 F2T4 := by decide +kernel
private theorem F2lv : levelsChecked fF2 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF2,F2L] at ht
  subst ht; exact F2k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF2 : LowerBV (rawOf 15) tF2 5 :=
  lower_forest fF2 base1 base1_s F2v F2lv (by decide +kernel)
def base2 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | _ => ([],0,0)
private theorem base2_s : ∀ k, k ≠ 0 → LowerBV (base2 k).1 (base2 k).2.1 (base2 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _
def fF3 : Forest := ⟨15,tF3,4,F3P,F3N,F3R,F3A,F3C,F3L,F3M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3v : graphValid fF3 base2 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F3k4 : ok fF3 4 F3T4 := by decide +kernel
private theorem F3lv : levelsChecked fF3 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF3,F3L] at ht
  subst ht; exact F3k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF3 : LowerBV (rawOf 15) tF3 5 :=
  lower_forest fF3 base2 base2_s F3v F3lv (by decide +kernel)
def base3 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | _ => ([],0,0)
private theorem base3_s : ∀ k, k ≠ 0 → LowerBV (base3 k).1 (base3 k).2.1 (base3 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _
def fF4 : Forest := ⟨15,tF4,4,F4P,F4N,F4R,F4A,F4C,F4L,F4M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4v : graphValid fF4 base3 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F4k4 : ok fF4 4 F4T4 := by decide +kernel
private theorem F4lv : levelsChecked fF4 := by
  intro k hk tree ht; change k ≤ 4 at hk; interval_cases k
  all_goals simp [fF4,F4L] at ht
  subst ht; exact F4k4
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF4 : LowerBV (rawOf 15) tF4 5 :=
  lower_forest fF4 base3 base3_s F4v F4lv (by decide +kernel)
def base4 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | _ => ([],0,0)
private theorem base4_s : ∀ k, k ≠ 0 → LowerBV (base4 k).1 (base4 k).2.1 (base4 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 0 | _ + 5 => exact fun _ _ _ _ => Nat.zero_le _
def fF5 : Forest := ⟨15,tF5,6,F5P,F5N,F5R,F5A,F5C,F5L,F5M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5v : graphValid fF5 base4 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k3 : ok fF5 3 F5T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k4 : ok fF5 4 F5T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k5 : ok fF5 5 F5T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F5k6 : ok fF5 6 F5T6 := by decide +kernel
private theorem F5lv : levelsChecked fF5 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF5,F5L] at ht
  · subst ht; exact F5k3
  · subst ht; exact F5k4
  · subst ht; exact F5k5
  · subst ht; exact F5k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF5 : LowerBV (rawOf 15) tF5 7 :=
  lower_forest fF5 base4 base4_s F5v F5lv (by decide +kernel)
def base5 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,7) | _ => ([],0,0)
private theorem base5_s : ∀ k, k ≠ 0 → LowerBV (base5 k).1 (base5 k).2.1 (base5 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 0 | _ + 6 => exact fun _ _ _ _ => Nat.zero_le _
def fF6 : Forest := ⟨15,tF6,6,F6P,F6N,F6R,F6A,F6C,F6L,F6M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6v : graphValid fF6 base5 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k3 : ok fF6 3 F6T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k4 : ok fF6 4 F6T4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k5 : ok fF6 5 F6T5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F6k6 : ok fF6 6 F6T6 := by decide +kernel
private theorem F6lv : levelsChecked fF6 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fF6,F6L] at ht
  · subst ht; exact F6k3
  · subst ht; exact F6k4
  · subst ht; exact F6k5
  · subst ht; exact F6k6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF6 : LowerBV (rawOf 15) tF6 7 :=
  lower_forest fF6 base5 base5_s F6v F6lv (by decide +kernel)
def base6 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,7) | 6 => (rawOf 15,tF6,7) | _ => ([],0,0)
private theorem base6_s : ∀ k, k ≠ 0 → LowerBV (base6 k).1 (base6 k).2.1 (base6 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 0 | _ + 7 => exact fun _ _ _ _ => Nat.zero_le _
def fF7 : Forest := ⟨31,tF7,9,F7P,F7N,F7R,F7A,F7C,F7L,F7M⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7v : graphValid fF7 base6 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k3 : ok fF7 3 F7T3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k4_0 : ok fF7 4 F7T4_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k4_1 : ok fF7 4 F7T4_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k4_2 : ok fF7 4 F7T4_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k4_3 : ok fF7 4 F7T4_3 := by decide +kernel
private theorem F7k4 : ok fF7 4 F7T4 := by
  simp only [ok,F7T4,nd,BTree.all,F7k4_0,F7k4_1,F7k4_2,F7k4_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_0 : ok fF7 5 F7T5_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_1 : ok fF7 5 F7T5_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_2 : ok fF7 5 F7T5_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_3 : ok fF7 5 F7T5_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_4 : ok fF7 5 F7T5_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_5 : ok fF7 5 F7T5_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_6 : ok fF7 5 F7T5_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_7 : ok fF7 5 F7T5_7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_8 : ok fF7 5 F7T5_8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_9 : ok fF7 5 F7T5_9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_10 : ok fF7 5 F7T5_10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_11 : ok fF7 5 F7T5_11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_12 : ok fF7 5 F7T5_12 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_13 : ok fF7 5 F7T5_13 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_14 : ok fF7 5 F7T5_14 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k5_15 : ok fF7 5 F7T5_15 := by decide +kernel
private theorem F7k5 : ok fF7 5 F7T5 := by
  simp only [ok,F7T5,nd,BTree.all,F7k5_0,F7k5_1,F7k5_2,F7k5_3,F7k5_4,F7k5_5,F7k5_6,F7k5_7,F7k5_8,F7k5_9,F7k5_10,F7k5_11,F7k5_12,F7k5_13,F7k5_14,F7k5_15,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_0 : ok fF7 6 F7T6_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_1 : ok fF7 6 F7T6_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_2 : ok fF7 6 F7T6_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_3 : ok fF7 6 F7T6_3 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_4 : ok fF7 6 F7T6_4 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_5 : ok fF7 6 F7T6_5 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_6 : ok fF7 6 F7T6_6 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_7 : ok fF7 6 F7T6_7 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_8 : ok fF7 6 F7T6_8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_9 : ok fF7 6 F7T6_9 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_10 : ok fF7 6 F7T6_10 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_11 : ok fF7 6 F7T6_11 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_12 : ok fF7 6 F7T6_12 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_13 : ok fF7 6 F7T6_13 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_14 : ok fF7 6 F7T6_14 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k6_15 : ok fF7 6 F7T6_15 := by decide +kernel
private theorem F7k6 : ok fF7 6 F7T6 := by
  simp only [ok,F7T6,nd,BTree.all,F7k6_0,F7k6_1,F7k6_2,F7k6_3,F7k6_4,F7k6_5,F7k6_6,F7k6_7,F7k6_8,F7k6_9,F7k6_10,F7k6_11,F7k6_12,F7k6_13,F7k6_14,F7k6_15,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k7_0 : ok fF7 7 F7T7_0 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k7_1 : ok fF7 7 F7T7_1 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k7_2 : ok fF7 7 F7T7_2 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k7_3 : ok fF7 7 F7T7_3 := by decide +kernel
private theorem F7k7 : ok fF7 7 F7T7 := by
  simp only [ok,F7T7,nd,BTree.all,F7k7_0,F7k7_1,F7k7_2,F7k7_3,Bool.and_true]
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k8 : ok fF7 8 F7T8 := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem F7k9 : ok fF7 9 F7T9 := by decide +kernel
private theorem F7lv : levelsChecked fF7 := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fF7,F7L] at ht
  · subst ht; exact F7k3
  · subst ht; exact F7k4
  · subst ht; exact F7k5
  · subst ht; exact F7k6
  · subst ht; exact F7k7
  · subst ht; exact F7k8
  · subst ht; exact F7k9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowF7 : LowerBV (rawOf 31) tF7 10 :=
  lower_forest fF7 base6 base6_s F7v F7lv (by decide +kernel)
def base7 : Nat → List Sig × Sig × Nat | 1 => (rawOf 7,tF1,4) | 2 => (rawOf 15,tF2,5) | 3 => (rawOf 15,tF3,5) | 4 => (rawOf 15,tF4,5) | 5 => (rawOf 15,tF5,7) | 6 => (rawOf 15,tF6,7) | 7 => (rawOf 31,tF7,10) | _ => ([],0,0)
private theorem base7_s : ∀ k, k ≠ 0 → LowerBV (base7 k).1 (base7 k).2.1 (base7 k).2.2 := by
  intro k _; match k with
  | 1 => exact lowF1
  | 2 => exact lowF2
  | 3 => exact lowF3
  | 4 => exact lowF4
  | 5 => exact lowF5
  | 6 => exact lowF6
  | 7 => exact lowF7
  | 0 | _ + 8 => exact fun _ _ _ _ => Nat.zero_le _
def fRt : Forest := ⟨63,tRt,9,RtP,RtN,RtR,RtA,RtC,RtL,RtM⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtv : graphValid fRt base7 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
private theorem Rtk9 : ok fRt 9 RtT9 := by decide +kernel
private theorem Rtlv : levelsChecked fRt := by
  intro k hk tree ht; change k ≤ 9 at hk; interval_cases k
  all_goals simp [fRt,RtL] at ht
  subst ht; exact Rtk9
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowRt : LowerBV (rawOf 63) tRt 10 :=
  lower_forest fRt base7 base7_s Rtv Rtlv (by decide +kernel)
end CertVerify

def targetFun (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3941132416 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [13, 15]⟩], 16⟩

private theorem witnessMonotone : Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

def idx6 (x : Fin 6 → Bool) : Nat :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
  (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0)
private theorem sum_fin6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = idx6 x := by
  simp [Fin.sum_univ_six, idx6]
private theorem witnessCorrectFast : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    smallCircuit.eval [b0, b1, b2, b3, b4, b5] =
    Nat.testBit (3941132416 * 2 ^ 32 + 3900762240)
      ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
       (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)) := by
  decide +kernel
private theorem witnessCorrect (x : Fin 6 → Bool) : smallCircuit.eval (List.ofFn x) = targetFun x := by
  rw [targetFun, sum_fin6, idx6, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
      List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact witnessCorrectFast (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def sample6 (r : Row) (i : Fin 6) : Bool := bitBV r ((rawOf 63).getD i.val zeroBV)
private theorem raw63_list : List.ofFn (fun i : Fin 6 => (rawOf 63).getD i.val zeroBV) = rawOf 63 := rfl
private theorem sample6_eq (r : Row) :
    List.ofFn (sample6 r) = ((rawOf 63).map observeBV).map (fun f => f r) := by
  rw [← raw63_list, List.map_map, List.map_ofFn]; rfl
private theorem sample6_targetFast : ∀ r : Row, Nat.testBit (3941132416 * 2 ^ 32 + 3900762240) (idx6 (sample6 r)) = bitBV r tRt := by decide +kernel
private theorem sample6_target (r : Row) : targetFun (sample6 r) = bitBV r tRt := by
  rw [targetFun, sum_fin6]; exact sample6_targetFast r

private theorem fanInTwo_ops {C : Circuit} (h : FanInTwo C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg; refine ⟨?_, hl⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho

private theorem mainProof (s : ℕ) (h : HasCircuitSize 6 targetFun s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun x := by
  classical
  obtain ⟨C, hFanIn, hSize, hEval⟩ := h
  by_cases big : 11 ≤ C.size
  · have hsc : smallCircuit.size = 11 := rfl
    exact ⟨smallCircuit, witnessMonotone, by omega, witnessCorrect⟩
  have hfit := fanInTwo_ops hFanIn
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C, ?_, hSize, hEval⟩
    intro g hg; obtain ⟨ops, ar⟩ := hfit g hg; refine ⟨?_, ar⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have hlt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h1 | h1
    · exact h1
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h1) g hg
      simp [isNot, hop] at eq
  obtain ⟨q, bank, hq, hreach, hsup⟩ := circuit_reach ((rawOf 63).map observeBV) C.gates ((rawOf 63).map observeBV)
    0 ((rawOf 63).map observeBV) hfit Reach.start (fun a ha => Or.inl ha)
  have hout : (execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false) = observeBV tRt := by
    funext r
    have hev := execWires_at C.gates ((rawOf 63).map observeBV) r
    have hr1 : ((execWires C.gates ((rawOf 63).map observeBV)).getD C.output (fun _ => false)) r =
        ((execWires C.gates ((rawOf 63).map observeBV)).map (fun f => f r)).getD C.output false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (execWires C.gates ((rawOf 63).map observeBV))[C.output]? <;> rfl
    rw [hr1, hev, ← sample6_eq r]
    exact (hEval (sample6 r)).trans (sample6_target r)
  have havail : Available bank (observeBV tRt) := hout ▸ avail_getD hsup C.output
  have hlb := lowRt q bank hreach havail
  simp [Circuit.size] at big
  omega

end PEqualNP.Outside.L_meta_12945

open PEqualNP.Outside.L_meta_12945 in
theorem PEqualNP.Outside.L_meta_12945 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132416 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132416 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  mainProof
