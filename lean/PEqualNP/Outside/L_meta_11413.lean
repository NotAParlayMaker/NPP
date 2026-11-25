import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11413
open PEqualNP.CircuitLowerBounds

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
  extraZ : Nat
  perm : List Nat

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
  domOk && properB G && rawOk && plainWordBV G && freeRaw.all plainWordBV &&
  (if c.kind == 0 then
     let es := freeRaw.filter (essentialCheck6 G freeRaw)
     decide (c.L ≤ es.length - 1)
   else
     let (bRoots, bT, bL) := baseOf c.kind
     let g : Row → Row := fun r => fixRow c.extraZ 0 (rowPerm c.perm r)
     let singles := rawOf (freeMask &&& c.extraZ)
     properB bT &&
     (rename6 g G == bT) &&
     freeRaw.all (fun a => freeWord6 bRoots (rename6 g a)) &&
     singles.all (essentialCheck6 G freeRaw) &&
     singles.all (fun a => rename6 g a == zeroBV || rename6 g a == oneBV) &&
     decide (c.L ≤ bL + singles.length))

theorem checkCut_sound {vmask : Nat} {T : Sig} {c : CutSpec}
    {baseOf : Nat → List Sig × Sig × Nat}
    (hb : ∀ k, k ≠ 0 → LowerBV (baseOf k).1 (baseOf k).2.1 (baseOf k).2.2)
    (ok : checkCut vmask T c baseOf = true) :
    Slice (rawOf vmask) T (subcube6 c.z c.o) c.L := by
  unfold checkCut at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨domOk, pG⟩, rawOk⟩, nG⟩, nFR⟩, hbody⟩ := ok
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
    obtain ⟨⟨⟨⟨⟨pbT, hEq⟩, hCov⟩, hEss⟩, hConst⟩, hLe⟩ := hbody
    let b := baseOf c.kind
    let g : Row → Row := fun r => fixRow c.extraZ 0 (rowPerm c.perm r)
    let singles := rawOf (freeMask &&& c.extraZ)
    have hnd : singles.Nodup := rawOf_nodup _
    have hlo := lowerBV_slice (proper_of pG) nG nFR (proper_of pbT) g
      ((observe6_rename g G).symm.trans (congrArg observeBV hEq))
      (fun a ha => by rw [← observe6_rename]; exact freeWord6_sound (List.all_eq_true.mp hCov a ha))
      singles.toFinset
      (fun a ha => essentialCheck6_sound (List.all_eq_true.mp hEss a (List.mem_toFinset.mp ha)))
      (fun a ha => by
        rw [← observe6_rename]
        have hc := List.all_eq_true.mp hConst a (List.mem_toFinset.mp ha)
        simp only [Bool.or_eq_true, beq_iff_eq] at hc
        rcases hc with h0 | h1
        · rw [h0]; exact ⟨false, funext bitBV_zero⟩
        · rw [h1]; exact ⟨true, funext bitBV_one⟩)
      b.2.2 (hb c.kind hk)
    rw [List.toFinset_card_of_nodup hnd] at hlo
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

def treeSplit {α} (f : α → Bool) : Nat → BTree α → Prop
  | 0, t => t.all f = true
  | _ + 1, .leaf a => f a = true
  | d + 1, .node l r => treeSplit f d l ∧ treeSplit f d r

theorem treeSplit_sound {α} {f : α → Bool} {d : Nat} {t : BTree α} (h : treeSplit f d t) :
    t.all f = true := by
  induction d generalizing t with
  | zero => exact h
  | succ d ih =>
    cases t with
    | leaf a => exact h
    | node l r => simp only [BTree.all, Bool.and_eq_true]; exact ⟨ih h.1, ih h.2⟩

inductive BST where
  | nil
  | node (key path ai : Nat) (l r : BST)

def BST.find : BST → Nat → Option (Nat × Nat)
  | .nil, _ => none
  | .node k p a l r, x =>
    if Nat.beq x k then some (p, a)
    else if Nat.ble x k then l.find x else r.find x

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

abbrev NodeData := Nat × Nat × Nat × List (Nat × Nat)

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
    let rest := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then rest else
      ((ops >>> 8) &&& 3, (bank.getD (ops &&& 15) (zeroBV, 0, 0)).1,
        (bank.getD ((ops >>> 4) &&& 15) (zeroBV, 0, 0)).1) :: rest

def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n * (n + 971)) % 2305843009213693921

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
  let (depth, ops, liveMask, _) := nd
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
    let (depth, ops, liveMask, _) := tree.get path
    selectLive liveMask (decodeN depth ops (rawPermN g.vmask perm))

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
        rcases hnd : tree.get path with ⟨depth, ops, liveMask, hints⟩
        rw [hnd] at h
        refine ⟨(g.nodeVals (depth, ops, liveMask, hints)).map (sigPerm perm), ?_, ?_⟩
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
          change selectLive liveMask (decodeN depth ops (rawPermN g.vmask perm)) =
            selectLive liveMask ((decodeDBank depth ops g.rawD).map fun w => F w.1)
          rw [decodeN_eq F F0 Fb, hrawF]
        · exact autoCheck_rotate hok (hnd ▸ hprev tree hl path)

def buildRule (g : Forest) (ops depth : Nat) (bank : List DWire) (ci paid : Nat) : Option BoundPool :=
  (g.cuts[ci]?).bind fun c =>
    let d := subcube6 c.z c.o
    let cs := chosenSteps bank ops paid depth
    (makePool d (rawOf g.vmask) cs).map fun pool => (d, c.L, cs.length, pool)

theorem buildRule_sound (g : Forest)
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target (subcube6 c.z c.o) c.L)
    {ops depth bank ci paid p} (h : buildRule g ops depth bank ci paid = some p) :
    ValidPool (rawOf g.vmask) g.target p := by
  unfold buildRule at h
  cases hc : g.cuts[ci]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    cases hm : makePool (subcube6 c.z c.o) (rawOf g.vmask) (chosenSteps bank ops paid depth) with
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
  if or (Nat.beq zVal 0) (or (Nat.beq zVal (allOnesNat 64)) (anyEq zVal wsN)) then true else
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
  let (depth, ops, liveMask, hints) := nd
  let bank := decodeDBank depth ops g.rawD
  let ws := selectLive liveMask bank
  let vals := ws.map Prod.fst
  and (decide vals.Nodup) (and (!(vals.contains g.target))
    (if Nat.beq k 0 then true else
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
    (hcuts : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target (subcube6 c.z c.o) c.L)
    (hauto : ∀ p ∈ g.autos, autoCheck g.target p = true)
    (hprev : k > 0 → ∀ tree, g.levels (k - 1) = some tree →
      ∀ p, ImpossibleBV g.target (k - 1) (g.nodeVals (tree.get p)).toFinset)
    (hok : fastNodeOK g k nd = true) :
    ImpossibleBV g.target k (g.nodeVals nd).toFinset := by
  rcases nd with ⟨depth, ops, liveMask, hints⟩
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
    have hz1 : Nat.beq (binBV op (ws[i]).1 (ws[j]).1).toNat (allOnesNat 64) = false := by
      apply Bool.eq_false_iff.mpr; intro he
      have hall : (oneBV (N := 64)).toNat = allOnesNat 64 := by decide +kernel
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
  have hcuts' : ∀ c ∈ g.cuts, Slice (rawOf g.vmask) g.target (subcube6 c.z c.o) c.L :=
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
-- 6. Targets, 7-Variable Reduction, Monotone Witness & Main
-- ============================================================

def tK3 : Sig := (x0 &&& x3) ||| (x0 &&& x5) ||| (x3 &&& x5)
def tP4 : Sig := (x2 &&& x4) ||| (x2 &&& x5) ||| (x3 &&& x5)
def tC5 : Sig := (x1 &&& x3) ||| (x1 &&& x4) ||| (x2 &&& x4) ||| (x2 &&& x5) ||| (x3 &&& x5)
def tG6 : Sig := (x0 &&& x3) ||| (x1 &&& x3) ||| (x0 &&& x4) ||| (x1 &&& x4) |||
                 (x2 &&& x4) ||| (x0 &&& x5) ||| (x2 &&& x5) ||| (x3 &&& x5)
-- ===== Certificate K3 (vmask=41, cap=3) =====
def cK3W : Nat := 9
def cK3Pos : List Row := [⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩]
def cK3Neg : List Row := [⟨1,by decide⟩,⟨8,by decide⟩,⟨32,by decide⟩,⟨1,by decide⟩,⟨8,by decide⟩,⟨32,by decide⟩,⟨1,by decide⟩,⟨8,by decide⟩,⟨32,by decide⟩]
def cK3RawCols : List (Nat × Nat) := [(63,73),(455,146),(504,292)]
def cK3Autos : List (List Nat) := [[0,1,2,3,4,5]]
def cK3Cuts : List CutSpec := []
def cK3T3 : BTree NodeData := .leaf (0,0,7,[])
def cK3Levels : Nat → Option (BTree NodeData)
  | 3 => some cK3T3
  | _ => none
def cK3Maps : Nat → BST
  | _ => .nil
-- ===== Certificate P4 (vmask=60, cap=3) =====
def cP4W : Nat := 9
def cP4Pos : List Row := [⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩]
def cP4Neg : List Row := [⟨12,by decide⟩,⟨24,by decide⟩,⟨48,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨48,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨48,by decide⟩]
def cP4RawCols : List (Nat × Nat) := [(63,73),(448,219),(7,438),(504,292)]
def cP4Autos : List (List Nat) := [[0,1,2,3,4,5]]
def cP4Cuts : List CutSpec := [⟨0,8,2,0,0,[0,1,2,3,4,5]⟩,⟨8,0,2,0,0,[0,1,2,3,4,5]⟩,⟨0,16,2,0,0,[0,1,2,3,4,5]⟩,⟨16,0,2,0,0,[0,1,2,3,4,5]⟩]
def cP4T2 : BTree NodeData := .node (.leaf (1,560,22,[])) (.leaf (1,816,22,[]))
def cP4T3 : BTree NodeData := .leaf (0,0,15,[(0,0),(1,0),(2,0),(3,0)])
def cP4M3 : BST := .node 4161325539581474008 1 0 (.node 2501761038765748984 0 0 (.nil) (.nil)) (.nil)
def cP4Levels : Nat → Option (BTree NodeData)
  | 2 => some cP4T2
  | 3 => some cP4T3
  | _ => none
def cP4Maps : Nat → BST
  | 3 => cP4M3
  | _ => .nil
-- ===== Certificate C5 (vmask=62, cap=6) =====
def cC5W : Nat := 25
def cC5Pos : List Row := [⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩]
def cC5Neg : List Row := [⟨6,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨6,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨6,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨6,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨6,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩]
def cC5RawCols : List (Nat × Nat) := [(1023,9741609),(1047552,3247203),(32505887,6494406),(32736,21648020),(33521664,25977624)]
def cC5Autos : List (List Nat) := [[0,1,2,3,4,5],[0,3,4,5,1,2],[0,5,1,2,3,4],[0,2,3,4,5,1],[0,4,5,1,2,3],[0,1,5,4,3,2],[0,3,2,1,5,4],[0,5,4,3,2,1],[0,2,1,5,4,3],[0,4,3,2,1,5]]
def cC5Cuts : List CutSpec := [⟨0,12,2,0,0,[0,1,2,3,4,5]⟩,⟨32,4,2,0,0,[0,1,2,3,4,5]⟩,⟨0,4,3,0,0,[0,1,2,3,4,5]⟩,⟨32,8,2,0,0,[0,1,2,3,4,5]⟩,⟨4,0,4,2,0,[0,2,1,5,4,3]⟩,⟨4,16,2,0,0,[0,1,2,3,4,5]⟩,⟨0,16,3,0,0,[0,1,2,3,4,5]⟩,⟨0,32,3,0,0,[0,1,2,3,4,5]⟩,⟨0,48,2,0,0,[0,1,2,3,4,5]⟩,⟨2,0,4,2,0,[0,1,2,3,4,5]⟩,⟨0,2,3,0,0,[0,1,2,3,4,5]⟩,⟨32,0,4,2,0,[0,2,3,4,5,1]⟩,⟨0,8,3,0,0,[0,1,2,3,4,5]⟩,⟨16,0,4,2,0,[0,3,4,5,1,2]⟩,⟨8,0,4,2,0,[0,3,2,1,5,4]⟩,⟨4,32,2,0,0,[0,1,2,3,4,5]⟩,⟨0,34,2,0,0,[0,1,2,3,4,5]⟩,⟨8,2,2,0,0,[0,1,2,3,4,5]⟩,⟨2,16,2,0,0,[0,1,2,3,4,5]⟩,⟨0,24,2,0,0,[0,1,2,3,4,5]⟩,⟨10,0,2,0,0,[0,1,2,3,4,5]⟩]
def cC5T3 : BTree NodeData := .node (.leaf (3,375179792,144,[(0,0)])) (.leaf (3,374933024,136,[(1,0)]))
def cC5T4 : BTree NodeData := .node (.node (.node (.leaf (2,870672,90,[(2,0),(3,0),(4,2),(5,2)])) (.node (.leaf (2,871696,86,[(6,0),(4,2),(7,0)])) (.leaf (2,872720,78,[(0,0),(8,0)])))) (.node (.node (.leaf (2,870672,91,[(9,2),(10,0),(2,0),(4,2),(3,0),(6,0),(11,0),(7,0)])) (.leaf (2,871696,87,[(9,2),(10,0),(2,0),(12,0),(7,0)]))) (.node (.leaf (2,838160,112,[(9,2),(13,1)])) (.leaf (2,330256,120,[(7,1),(9,2),(11,1),(6,2),(13,1)]))))) (.node (.node (.leaf (2,592400,120,[(9,2),(14,1),(13,1),(6,2),(11,1)])) (.node (.leaf (2,591136,108,[(4,1),(9,2)])) (.leaf (2,869664,92,[(2,0),(14,2),(6,0)])))) (.node (.node (.leaf (2,871712,86,[(0,0),(6,0),(7,0)])) (.leaf (2,872736,78,[(15,0),(12,0)]))) (.node (.leaf (2,591392,104,[(9,2),(4,1)])) (.leaf (2,591392,120,[(7,1),(9,2),(11,1),(1,0)])))))
def cC5M4 : BST := .node 3503189890977770564 0 0 (.node 2901123184108150261 1 0 (.nil) (.nil)) (.nil)
def cC5T5 : BTree NodeData := .node (.node (.node (.leaf (1,272,62,[(0,0),(1,0),(5,0),(4,0),(13,1),(9,0)])) (.leaf (1,272,63,[(16,0),(0,0),(9,0),(4,0),(17,0),(14,0),(1,0),(13,0),(11,0)]))) (.node (.leaf (1,528,60,[(9,0),(13,1),(0,0),(14,1),(18,0),(6,0)])) (.leaf (1,528,62,[(0,0),(4,0),(15,0),(18,0),(2,0),(13,1),(11,1),(14,0),(13,0),(6,0),(11,0)])))) (.node (.node (.leaf (1,288,62,[(0,0),(19,0),(3,0),(14,0),(9,0)])) (.leaf (1,288,63,[(20,0),(10,0),(0,0),(19,0),(16,0),(9,0),(14,0)]))) (.node (.leaf (1,544,58,[(9,0),(4,1),(18,0),(0,0),(13,1),(2,0)])) (.leaf (1,544,62,[(0,0),(3,0),(14,0),(18,0),(13,1),(4,0),(13,0),(6,0),(11,0)]))))
def cC5M5 : BST := .node 5975901722456773512 13 0 (.node 4359968408847315736 14 0 (.node 3291598063440658434 7 0 (.node 3056187636244911889 6 0 (.node 2849051040443233956 5 0 (.nil) (.nil)) (.nil)) (.node 3701524157919105824 15 8 (.nil) (.nil))) (.node 5461792660225952466 5 8 (.node 5128982473266413238 14 4 (.node 4996817786919705270 3 0 (.nil) (.nil)) (.nil)) (.node 5597434771937631683 15 0 (.nil) (.nil)))) (.node 6645919329783291919 11 0 (.node 6494106378713911591 4 0 (.node 6243131143861895839 12 0 (.node 5981455590742285106 1 4 (.nil) (.nil)) (.nil)) (.node 6522261159617382153 1 0 (.nil) (.nil))) (.node 8431014506453645400 10 0 (.node 8357437303951298093 0 0 (.node 8180039271601629648 2 8 (.nil) (.nil)) (.nil)) (.node 10294345431691031902 2 0 (.nil) (.nil))))
def cC5T6 : BTree NodeData := .leaf (0,0,31,[(4,0),(9,0),(14,0),(13,0),(11,0)])
def cC5M6 : BST := .node 7464445609317237933 3 0 (.node 6608863763290776825 1 8 (.node 6098233667321207817 3 2 (.node 5307840414339748114 3 3 (.node 4686625462515999322 2 7 (.node 4645476368084035281 2 5 (.node 4438669166505482793 3 8 (.nil) (.nil)) (.nil)) (.node 4769615239037002830 2 0 (.nil) (.nil))) (.node 5553573808003768572 3 5 (.node 5367612528804998433 3 4 (.nil) (.nil)) (.node 5727058703070406434 2 8 (.nil) (.nil)))) (.node 6485402312133296783 3 7 (.node 6305959268173849339 1 7 (.node 6305680008084217339 0 7 (.node 6267290583419726197 2 6 (.nil) (.nil)) (.nil)) (.node 6369509197999435339 1 2 (.nil) (.nil))) (.node 6578989100977275403 6 7 (.node 6558974589321274385 3 9 (.nil) (.nil)) (.node 6582380245695751994 2 2 (.nil) (.nil))))) (.node 6898089109589971351 2 9 (.node 6822552160409204307 1 9 (.node 6719153078119914507 0 4 (.node 6718600599328662075 2 4 (.node 6648433655664848625 1 3 (.nil) (.nil)) (.nil)) (.node 6744505875002456042 7 8 (.nil) (.nil))) (.node 6843454007941167466 3 6 (.node 6836097382242634593 6 0 (.nil) (.nil)) (.node 6895328406611744173 7 7 (.nil) (.nil)))) (.node 7304520656544732242 7 4 (.node 7043548508064757135 0 2 (.node 7021898586319813455 1 0 (.node 6951313076581008530 6 5 (.nil) (.nil)) (.nil)) (.node 7200204052801024195 7 3 (.nil) (.nil))) (.node 7412477088821996575 0 5 (.node 7308015204068418741 6 9 (.nil) (.nil)) (.node 7445937446465044653 7 5 (.nil) (.nil)))))) (.node 8611795976670822588 5 1 (.node 8112376697171737431 1 4 (.node 7927686973556004313 6 3 (.node 7663966830810140243 6 8 (.node 7530626644915750788 0 3 (.node 7517760879077556923 2 3 (.nil) (.nil)) (.nil)) (.node 7874371703795685323 7 0 (.nil) (.nil))) (.node 8058325924465468366 3 1 (.node 8043752738210292061 0 8 (.nil) (.nil)) (.node 8067832207893279703 1 5 (.nil) (.nil)))) (.node 8519288373435485803 6 2 (.node 8201869882192375198 1 1 (.node 8173326753676190015 0 0 (.node 8164715810526839580 7 2 (.nil) (.nil)) (.nil)) (.node 8333772726625357960 6 6 (.nil) (.nil))) (.node 8599648200224727766 2 1 (.node 8548880619581099874 1 6 (.nil) (.nil)) (.node 8611516716581190588 4 4 (.nil) (.nil))))) (.node 9349385216561730384 4 2 (.node 8958806714059547264 5 0 (.node 8714915798870480388 5 3 (.node 8675345906496408588 5 2 (.node 8625456732526906148 7 9 (.nil) (.nil)) (.nil)) (.node 8780362135680901275 7 6 (.nil) (.nil))) (.node 9024437307825635324 6 4 (.node 9023950151239840228 0 9 (.nil) (.nil)) (.node 9187182693642935161 0 6 (.nil) (.nil)))) (.node 10364162632962441615 7 1 (.node 10004740335633013512 5 4 (.node 9597108788121382551 4 3 (.nil) (.nil)) (.node 10110234881415923824 4 0 (.nil) (.nil))) (.node 10506387695222668919 0 1 (.node 10492011838686003847 6 1 (.nil) (.nil)) (.node 10916313789701116309 4 1 (.nil) (.nil))))))
def cC5Levels : Nat → Option (BTree NodeData)
  | 3 => some cC5T3
  | 4 => some cC5T4
  | 5 => some cC5T5
  | 6 => some cC5T6
  | _ => none
def cC5Maps : Nat → BST
  | 4 => cC5M4
  | 5 => cC5M5
  | 6 => cC5M6
  | _ => .nil
-- ===== Certificate G6 (vmask=63, cap=8) =====
def cG6W : Nat := 40
def cG6Pos : List Row := [⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩,⟨9,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨10,by decide⟩,⟨17,by decide⟩,⟨17,by decide⟩,⟨17,by decide⟩,⟨17,by decide⟩,⟨17,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨18,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨20,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨33,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨36,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩,⟨40,by decide⟩]
def cG6Neg : List Row := [⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨24,by decide⟩,⟨34,by decide⟩,⟨48,by decide⟩]
def cG6RawCols : List (Nat × Nat) := [(1040219167,35468117025),(1016800,319213053225),(33318502400,106404351075),(1065151890431,212808702150),(33553408,709362340500),(1099478073344,851234808600)]
def cG6Autos : List (List Nat) := [[0,1,2,3,4,5],[0,2,1,5,4,3]]
def cG6Cuts : List CutSpec := [⟨20,0,5,1,2,[0,1,2,3,4,5]⟩,⟨4,48,2,0,0,[0,1,2,3,4,5]⟩,⟨0,2,4,0,0,[0,1,2,3,4,5]⟩,⟨16,0,6,1,6,[0,1,2,3,4,5]⟩,⟨8,0,5,2,1,[0,3,2,1,5,4]⟩,⟨34,0,4,2,0,[2,0,3,4,5,1]⟩,⟨16,2,3,0,0,[0,1,2,3,4,5]⟩,⟨6,0,5,1,16,[0,1,2,3,4,5]⟩,⟨18,0,5,1,4,[0,1,2,3,4,5]⟩,⟨0,12,3,0,0,[0,1,2,3,4,5]⟩,⟨9,0,4,2,0,[0,3,2,1,5,4]⟩,⟨2,16,3,0,0,[0,1,2,3,4,5]⟩,⟨0,32,4,0,0,[0,1,2,3,4,5]⟩,⟨2,0,6,1,20,[0,1,2,3,4,5]⟩,⟨17,0,4,2,0,[0,3,4,5,1,2]⟩,⟨4,2,3,0,0,[0,1,2,3,4,5]⟩,⟨1,0,7,3,0,[0,1,2,3,4,5]⟩,⟨32,4,3,0,0,[0,1,2,3,4,5]⟩,⟨0,24,3,0,0,[0,1,2,3,4,5]⟩,⟨1,8,3,0,0,[0,1,2,3,4,5]⟩,⟨10,0,3,0,0,[0,1,2,3,4,5]⟩,⟨16,4,3,0,0,[0,1,2,3,4,5]⟩,⟨2,8,3,0,0,[0,1,2,3,4,5]⟩,⟨52,0,2,0,0,[0,1,2,3,4,5]⟩,⟨32,8,3,0,0,[0,1,2,3,4,5]⟩,⟨4,3,2,0,0,[0,1,2,3,4,5]⟩,⟨0,7,2,0,0,[0,1,2,3,4,5]⟩,⟨0,48,3,0,0,[0,1,2,3,4,5]⟩,⟨3,0,4,2,0,[0,1,2,3,4,5]⟩,⟨0,8,4,0,0,[0,1,2,3,4,5]⟩,⟨1,32,3,0,0,[0,1,2,3,4,5]⟩,⟨0,16,4,0,0,[0,1,2,3,4,5]⟩,⟨12,0,4,2,0,[2,3,0,1,5,4]⟩,⟨0,3,2,0,0,[0,1,2,3,4,5]⟩,⟨8,32,3,0,0,[0,1,2,3,4,5]⟩,⟨4,32,3,0,0,[0,1,2,3,4,5]⟩,⟨32,0,5,2,1,[0,2,3,4,5,1]⟩,⟨3,8,2,0,0,[0,1,2,3,4,5]⟩,⟨4,0,6,1,18,[0,1,2,3,4,5]⟩,⟨0,34,3,0,0,[0,1,2,3,4,5]⟩,⟨8,2,3,0,0,[0,1,2,3,4,5]⟩,⟨42,0,2,0,0,[0,1,2,3,4,5]⟩,⟨0,6,2,0,0,[0,1,2,3,4,5]⟩,⟨0,4,4,0,0,[0,1,2,3,4,5]⟩,⟨2,4,3,0,0,[0,1,2,3,4,5]⟩,⟨22,0,4,1,0,[0,1,2,3,4,5]⟩,⟨1,2,3,0,0,[0,1,2,3,4,5]⟩,⟨40,16,2,0,0,[0,1,2,3,4,5]⟩,⟨44,0,2,0,0,[0,1,2,3,4,5]⟩,⟨33,0,4,2,0,[0,2,3,4,5,1]⟩,⟨20,8,2,0,0,[0,1,2,3,4,5]⟩,⟨40,0,3,0,0,[0,1,2,3,4,5]⟩,⟨41,0,2,0,0,[0,1,2,3,4,5]⟩,⟨16,12,2,0,0,[0,1,2,3,4,5]⟩,⟨4,34,2,0,0,[0,1,2,3,4,5]⟩,⟨36,0,3,0,0,[0,1,2,3,4,5]⟩,⟨26,0,2,0,0,[0,1,2,3,4,5]⟩,⟨4,16,3,0,0,[0,1,2,3,4,5]⟩,⟨2,48,2,0,0,[0,1,2,3,4,5]⟩,⟨0,5,2,0,0,[0,1,2,3,4,5]⟩,⟨1,16,3,0,0,[0,1,2,3,4,5]⟩,⟨48,4,2,0,0,[0,1,2,3,4,5]⟩,⟨6,1,2,0,0,[0,1,2,3,4,5]⟩,⟨5,0,4,2,0,[0,2,1,5,4,3]⟩,⟨34,8,2,0,0,[0,1,2,3,4,5]⟩,⟨5,32,2,0,0,[0,1,2,3,4,5]⟩,⟨3,16,2,0,0,[0,1,2,3,4,5]⟩,⟨9,32,2,0,0,[0,1,2,3,4,5]⟩,⟨32,5,1,0,0,[0,1,2,3,4,5]⟩,⟨8,48,2,0,0,[0,1,2,3,4,5]⟩,⟨1,4,3,0,0,[0,1,2,3,4,5]⟩,⟨8,34,2,0,0,[0,1,2,3,4,5]⟩,⟨24,2,2,0,0,[0,1,2,3,4,5]⟩,⟨16,34,2,0,0,[0,1,2,3,4,5]⟩,⟨10,4,1,0,0,[0,1,2,3,4,5]⟩,⟨12,2,2,0,0,[0,1,2,3,4,5]⟩,⟨9,2,2,0,0,[0,1,2,3,4,5]⟩,⟨32,12,2,0,0,[0,1,2,3,4,5]⟩,⟨34,4,2,0,0,[0,1,2,3,4,5]⟩,⟨32,24,2,0,0,[0,1,2,3,4,5]⟩,⟨12,32,2,0,0,[0,1,2,3,4,5]⟩]
def cG6T3 : BTree NodeData := .leaf (5,728790838331729,1296,[(0,25),(1,0)])
def cG6T4 : BTree NodeData := .node (.node (.node (.node (.node (.leaf (4,914679448848,848,[(2,8),(3,14),(4,4),(5,4)])) (.node (.leaf (4,950080423184,836,[(6,4),(7,12)])) (.leaf (4,420476668688,528,[(8,10)])))) (.node (.leaf (4,637389573424,772,[(8,1)])) (.node (.leaf (4,932933094704,770,[(9,0),(10,4)])) (.leaf (4,415388488496,624,[(11,1),(3,13),(12,8)]))))) (.node (.node (.leaf (4,968854374192,672,[(13,13),(14,2),(15,0)])) (.node (.leaf (4,419652504368,674,[(3,13),(4,2)])) (.leaf (4,420476668449,529,[(16,15),(8,10),(17,0)])))) (.node (.node (.leaf (4,420476668209,529,[(16,15),(18,0),(17,0)])) (.leaf (4,415389024561,688,[(19,8)]))) (.node (.leaf (4,930247181617,816,[(13,8)])) (.leaf (4,933468407089,788,[(7,12),(8,12),(10,8),(20,0)])))))) (.node (.node (.node (.leaf (4,420476668465,529,[(16,15),(8,10),(17,0)])) (.node (.leaf (4,964594860849,656,[(10,8),(21,3),(22,0)])) (.leaf (4,420476684081,517,[(23,0),(16,15)])))) (.node (.node (.leaf (4,969928427313,581,[(16,15),(7,12),(4,10),(24,0)])) (.leaf (4,969963030321,525,[(16,15),(7,12),(4,10),(6,0)]))) (.node (.leaf (4,383711792961,772,[(23,0),(16,11)])) (.leaf (4,383713890113,769,[(23,0),(16,15)]))))) (.node (.node (.leaf (4,969963294529,517,[(23,0),(16,15)])) (.node (.leaf (4,419418951489,517,[(23,0),(16,15)])) (.leaf (4,962465713985,516,[(23,0)])))) (.node (.node (.leaf (4,420476667985,529,[(16,15),(8,10),(17,0)])) (.leaf (4,914140744017,848,[(5,6),(19,1)]))) (.node (.leaf (4,694530132305,657,[(0,13),(16,15),(5,2),(25,0),(26,0)])) (.leaf (4,412978335057,540,[(25,0),(20,0),(27,8)]))))))) (.node (.node (.node (.node (.leaf (4,420440539729,516,[(7,12)])) (.node (.leaf (4,966757024337,644,[(28,8),(7,12),(8,4)])) (.leaf (4,420440539729,548,[(25,0)])))) (.node (.leaf (4,964575986257,664,[(8,12),(29,0),(30,0)])) (.node (.leaf (4,966723469905,652,[(30,0),(3,3),(7,12),(31,3),(29,0)])) (.leaf (4,415088607825,664,[(32,3),(30,0)]))))) (.node (.node (.leaf (4,417236091473,652,[(4,3),(30,0),(7,12)])) (.node (.leaf (4,417504526929,644,[(11,0),(7,12),(23,0),(33,0)])) (.leaf (4,964611637841,664,[(28,8),(34,0),(35,0),(9,0)])))) (.node (.node (.leaf (4,965685379665,660,[(22,0),(28,8),(11,0)])) (.leaf (4,966759121489,652,[(34,0),(28,8),(7,12)]))) (.node (.leaf (4,413243116369,562,[(36,12),(8,14),(19,0)])) (.leaf (4,933468410179,774,[(8,12),(0,12),(10,8),(27,0)])))))) (.node (.node (.node (.leaf (4,933467620675,780,[(24,4),(37,0),(7,9)])) (.node (.leaf (4,962464679235,540,[(0,14),(30,0),(11,0),(29,0)])) (.leaf (4,365458181443,838,[(23,0),(13,14),(17,0),(38,7),(25,8)])))) (.node (.node (.leaf (4,365459230019,837,[(23,0),(25,8),(17,0),(38,7),(13,10)])) (.leaf (4,967828668995,644,[(1,0),(13,3)]))) (.node (.leaf (4,967811891779,644,[(32,8),(11,0),(13,3)])) (.leaf (4,413245212227,580,[(32,12),(25,0)]))))) (.node (.node (.leaf (4,413245212227,540,[(0,14),(4,12),(30,0)])) (.node (.leaf (4,417523925331,646,[(30,0),(32,2),(39,0),(24,0)])) (.leaf (4,417523926355,645,[(16,15),(32,2),(39,0),(24,0)])))) (.node (.node (.leaf (4,382638590547,770,[(24,0),(7,9),(33,0)])) (.leaf (4,412386431571,642,[(14,1),(7,3),(31,8),(33,0)]))) (.node (.leaf (4,413460173395,641,[(16,15),(31,8),(33,0),(7,3)])) (.leaf (4,412435714643,652,[(24,8),(4,12),(7,3),(40,8)])))))))
def cG6M4 : BST := .node 4467489550607689698 0 0 (.nil) (.nil)
def cG6T5 : BTree NodeData := .node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf (3,910460176,424,[(2,0),(28,0),(5,4),(27,2),(7,4)])) (.leaf (3,908379408,432,[(2,0),(8,4),(28,0),(5,4)]))) (.node (.leaf (3,925156624,368,[(15,0),(8,4)])) (.node (.leaf (3,893699344,452,[(2,4),(7,4),(5,0)])) (.leaf (3,927253776,356,[(6,0),(7,4)]))))) (.node (.node (.leaf (3,891602192,472,[(41,0),(2,4),(24,1),(18,4)])) (.leaf (3,925156624,376,[(20,0),(39,0),(8,4),(29,0),(15,0)]))) (.node (.leaf (3,339002640,484,[(24,1),(2,4),(7,4),(9,0),(42,0),(39,0)])) (.node (.leaf (3,892650768,468,[(2,4),(8,4),(7,4),(5,0)])) (.leaf (3,893699344,460,[(7,4),(5,0),(2,4),(29,5)])))))) (.node (.node (.node (.leaf (3,927253776,364,[(41,0),(6,0),(7,4),(20,0),(29,0)])) (.leaf (3,911525136,412,[(28,0),(7,4),(8,4),(29,0)]))) (.node (.leaf (3,122995984,348,[(20,0),(7,4),(2,0),(8,4),(28,0)])) (.node (.leaf (3,892667152,452,[(2,4),(5,0)])) (.leaf (3,911541520,396,[(8,4),(7,4),(28,0)]))))) (.node (.node (.leaf (3,908936464,408,[(40,0),(8,4)])) (.node (.leaf (3,909985040,404,[(2,0),(7,4),(28,0),(17,0),(8,4)])) (.leaf (3,911033616,396,[(40,0),(7,4),(28,0)])))) (.node (.leaf (3,388842768,376,[(15,0),(8,4),(36,1),(40,0),(24,0),(43,0)])) (.node (.leaf (3,389891344,372,[(40,0),(8,4),(7,4),(36,1),(17,0),(29,0)])) (.leaf (3,390939920,364,[(6,0),(7,4),(36,1),(24,1),(39,0)]))))))) (.node (.node (.node (.node (.leaf (3,912082192,412,[(34,0),(7,4),(8,4),(2,0)])) (.leaf (3,911034640,394,[(28,2),(5,4),(18,2),(2,0)]))) (.node (.leaf (3,925191440,346,[(8,6),(29,1),(2,0),(43,1),(4,4),(35,0),(16,6)])) (.node (.leaf (3,927288592,334,[(11,0),(7,6),(29,1),(16,6)])) (.leaf (3,925207824,314,[(17,0),(8,6),(29,0)]))))) (.node (.node (.leaf (3,927304976,302,[(7,6),(24,0),(31,0)])) (.node (.leaf (3,928353552,286,[(7,6),(8,6),(12,0),(2,0),(29,0)])) (.leaf (3,388861200,306,[(17,0),(8,6)])))) (.node (.leaf (3,925209872,314,[(8,6),(27,0),(43,0),(2,0),(5,4),(4,0)])) (.node (.leaf (3,926258448,310,[(5,4),(29,0),(7,6),(8,6),(2,0),(43,0)])) (.leaf (3,927307024,302,[(5,4),(34,0),(31,0),(7,6),(2,0)])))))) (.node (.node (.node (.leaf (3,643615504,400,[(17,0)])) (.leaf (3,391957264,464,[(41,0),(8,6),(17,0)]))) (.node (.leaf (3,660392720,464,[(8,6),(4,1),(36,2),(5,2)])) (.node (.leaf (3,393005840,432,[(44,0),(45,0),(36,2)])) (.leaf (3,893176592,464,[(8,6),(4,1),(36,2),(5,2)]))))) (.node (.node (.leaf (3,373082896,432,[(29,0),(10,0),(8,2),(5,2)])) (.node (.leaf (3,391957264,344,[(41,0),(8,6)])) (.leaf (3,393005840,312,[(45,0),(10,0),(46,0),(44,0)])))) (.node (.leaf (3,929385232,312,[(45,0),(5,0),(44,0),(46,0)])) (.node (.leaf (3,925191952,368,[(5,4),(8,6),(43,1)])) (.leaf (3,929386256,308,[(47,0),(48,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,929386256,284,[(47,0)])) (.leaf (3,925208336,312,[(8,4),(29,0),(43,0)]))) (.node (.leaf (3,910984496,424,[(1,0),(32,4)])) (.node (.leaf (3,908379440,432,[(24,0),(10,0),(3,7)])) (.leaf (3,925156656,368,[(9,0),(24,0)]))))) (.node (.node (.leaf (3,928302384,340,[(9,0),(18,0),(35,1),(3,1)])) (.leaf (3,908379440,434,[(25,0),(8,5),(24,0),(10,0)]))) (.node (.leaf (3,925156656,370,[(25,0),(8,5),(24,0),(2,0)])) (.node (.leaf (3,910476592,422,[(7,5),(10,0),(24,0)])) (.leaf (3,928302384,342,[(25,0),(8,5),(24,0),(2,0)])))))) (.node (.node (.node (.leaf (3,625788208,452,[(0,3),(10,4)])) (.leaf (3,643614000,404,[(18,0),(32,4)]))) (.node (.leaf (3,391955760,340,[(22,0),(32,0),(27,1),(0,7),(10,0)])) (.node (.leaf (3,391955760,372,[(27,1),(24,0),(32,0),(5,0),(12,1),(3,1)])) (.leaf (3,624756016,484,[(0,5),(10,2),(36,2),(29,2),(12,1),(49,2)]))))) (.node (.node (.leaf (3,355812656,468,[(27,1),(35,1),(29,2),(26,0)])) (.node (.leaf (3,624510256,468,[(7,5),(10,2),(8,5),(29,0)])) (.leaf (3,858604848,464,[(24,0),(10,2),(50,0)])))) (.node (.leaf (3,908936496,408,[(17,0),(10,2),(3,7),(31,2)])) (.node (.leaf (3,321750320,436,[(24,0),(0,3),(10,0)])) (.leaf (3,910477616,422,[(24,0),(7,5),(10,0),(32,4),(29,0)]))))))) (.node (.node (.node (.node (.leaf (3,911526192,406,[(32,4),(24,0),(18,0),(7,5)])) (.leaf (3,391956784,338,[(10,0),(27,1),(39,1),(51,0),(8,7),(13,6)]))) (.node (.leaf (3,391956784,370,[(39,1),(24,0),(27,1),(17,0)])) (.node (.leaf (3,924141872,376,[(24,4),(34,0),(31,1),(3,6),(27,0),(2,1),(44,0)])) (.leaf (3,356354352,434,[(52,0),(18,0),(22,0),(17,0)]))))) (.node (.node (.leaf (3,388042032,354,[(8,1),(10,0),(0,1),(34,0),(17,1)])) (.node (.leaf (3,391187760,358,[(51,0),(8,1),(12,1),(0,1),(24,0)])) (.leaf (3,660671792,294,[(8,1),(32,0),(10,0),(34,0)])))) (.node (.leaf (3,924142896,340,[(18,0),(9,0)])) (.node (.leaf (3,925191472,338,[(26,0),(18,0)])) (.leaf (3,910511408,390,[(1,0),(9,0)])))))) (.node (.node (.node (.leaf (3,924142896,372,[(52,0),(53,0),(25,0),(27,0),(36,4),(4,0)])) (.leaf (3,925191472,370,[(26,0),(24,0),(53,0),(39,0),(22,0),(27,0),(36,4),(4,0)]))) (.node (.leaf (3,387534128,340,[(24,0),(32,0),(3,1)])) (.node (.leaf (3,625560880,454,[(8,3),(10,4),(0,3),(24,0),(9,0)])) (.leaf (3,924143920,364,[(24,4),(34,0),(43,1),(17,4),(2,1)]))))) (.node (.node (.leaf (3,924160304,316,[(40,0),(31,0),(24,0),(6,0),(43,0)])) (.node (.leaf (3,925208880,314,[(44,0),(17,0),(0,1),(29,0)])) (.leaf (3,928354608,286,[(35,0),(22,0),(31,0),(2,0),(34,0)])))) (.node (.leaf (3,876450096,422,[(8,1)])) (.node (.leaf (3,924161328,316,[(34,0),(6,0),(35,0)])) (.leaf (3,927307056,302,[(35,0),(22,0),(31,0),(24,0),(34,0)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (3,387814704,284,[(24,0),(6,0),(10,0),(9,4)])) (.leaf (3,354977584,496,[(48,0),(8,5)]))) (.node (.leaf (3,660375344,338,[(8,5),(32,0),(36,1)])) (.node (.leaf (3,390154032,356,[(51,0),(8,1),(7,1)])) (.leaf (3,925189936,338,[(40,0),(5,1)]))))) (.node (.node (.leaf (3,355288880,464,[(48,0),(3,6),(34,0)])) (.leaf (3,388843312,368,[(51,0),(21,1),(31,1)]))) (.node (.leaf (3,393037616,308,[(47,0),(48,0)])) (.node (.leaf (3,388843312,370,[(25,0),(8,5),(36,1),(2,0)])) (.leaf (3,929400624,436,[(7,1)])))))) (.node (.node (.node (.leaf (3,571836208,432,[(13,1)])) (.leaf (3,373655344,422,[(41,0),(19,0),(32,0),(40,0),(42,0)]))) (.node (.leaf (3,643139376,406,[(7,5),(40,0),(3,7),(19,0),(47,0)])) (.node (.leaf (3,660146992,338,[(3,5),(36,1),(7,1),(32,0)])) (.leaf (3,375196464,482,[(8,5),(4,2),(49,2)]))))) (.node (.node (.leaf (3,643631920,482,[(8,5),(4,2),(36,3),(12,2)])) (.node (.leaf (3,393022256,354,[(19,0),(25,0),(13,7),(32,0)])) (.leaf (3,659639088,338,[(0,1),(36,1),(7,1),(32,0)])))) (.node (.leaf (3,392252208,306,[(47,0),(41,0)])) (.node (.leaf (3,927288112,354,[(48,0),(34,0),(39,0)])) (.leaf (3,374164272,450,[(41,0),(47,0)]))))))) (.node (.node (.node (.node (.leaf (3,642599728,450,[(8,3),(51,0)])) (.leaf (3,393038640,402,[(1,0)]))) (.node (.leaf (3,661474096,402,[(1,0),(54,0)])) (.node (.leaf (3,393038640,306,[(1,0)])) (.leaf (3,374704944,434,[(19,0),(32,0),(51,0),(40,0),(27,3),(34,0)]))))) (.node (.node (.leaf (3,660179760,338,[(0,1),(36,1),(7,1),(4,4)])) (.node (.leaf (3,387011376,356,[(40,0),(36,1),(0,1)])) (.leaf (3,924144432,372,[(0,5),(34,0),(11,1),(36,5),(2,0)])))) (.node (.leaf (3,925193008,370,[(8,5),(34,0),(36,5)])) (.node (.leaf (3,388846384,354,[(5,1),(4,6),(19,0),(43,1),(55,1)])) (.leaf (3,375214896,390,[(12,0),(49,0),(13,7),(7,7),(2,2)])))))) (.node (.node (.node (.leaf (3,393040688,294,[(51,0),(13,7),(7,7),(2,0)])) (.leaf (3,388846384,370,[(8,5),(51,0),(55,1),(43,1),(5,1),(34,0)]))) (.node (.leaf (3,925209392,354,[(4,4),(44,1),(40,4),(17,1),(42,0)])) (.node (.leaf (3,929403696,422,[(8,1)])) (.leaf (3,925210416,338,[(47,0),(41,0)]))))) (.node (.node (.leaf (3,929404720,406,[(47,0),(32,0),(40,0)])) (.node (.leaf (3,924161840,308,[(6,0),(35,0)])) (.leaf (3,339248944,480,[(22,0),(4,2)])))) (.node (.leaf (3,373851952,424,[(11,0),(4,2)])) (.node (.leaf (3,925157168,368,[(4,4),(17,1),(21,1),(31,1),(34,4)])) (.leaf (3,929351472,436,[(32,0),(18,0),(20,0),(24,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,373606192,422,[(41,0),(19,0),(7,5),(40,0)])) (.leaf (3,389891888,340,[(40,0),(18,0),(38,7)]))) (.node (.leaf (3,393037616,284,[(47,0)])) (.node (.leaf (3,926254896,436,[(7,1)])) (.leaf (3,339052336,422,[(39,4),(22,0),(32,0),(2,4),(41,0),(42,0)]))))) (.node (.node (.leaf (3,892700464,406,[(6,4),(7,5),(2,4),(19,0)])) (.leaf (3,374655792,434,[(27,2),(24,0),(39,2),(32,0)]))) (.node (.leaf (3,660130608,338,[(0,1),(36,1),(7,1),(4,4)])) (.node (.leaf (3,356322096,482,[(8,5),(4,2),(16,6),(49,2)])) (.leaf (3,893193008,482,[(8,5),(4,2),(36,3)])))))) (.node (.node (.node (.leaf (3,389876528,354,[(8,1),(29,0),(32,0)])) (.leaf (3,393022256,298,[(37,0)]))) (.node (.leaf (3,339561264,450,[(41,0),(24,0)])) (.node (.leaf (3,876432176,450,[(24,0),(4,2),(8,3)])) (.leaf (3,374164272,394,[(41,0),(47,0)]))))) (.node (.node (.leaf (3,355830576,434,[(34,0),(17,0),(27,3),(39,3),(32,0)])) (.node (.leaf (3,925175600,354,[(4,4),(44,1),(40,4),(17,1),(42,0)])) (.leaf (3,929369904,294,[(32,0),(14,0),(13,7),(34,0),(24,0),(2,0)])))) (.node (.leaf (3,929369904,422,[(56,0),(47,0),(32,0)])) (.node (.leaf (3,924143408,340,[(32,4),(18,0),(0,7),(2,1)])) (.leaf (3,925191984,338,[(4,4),(8,7),(18,0),(2,1),(44,1)]))))))) (.node (.node (.node (.node (.leaf (3,929386288,406,[(18,0),(51,0),(32,0),(22,0)])) (.leaf (3,393039664,406,[(51,0),(18,0),(32,0),(22,0)]))) (.node (.leaf (3,375213872,406,[(27,0),(51,0),(32,0),(39,0)])) (.node (.leaf (3,393039664,310,[(30,0),(32,0),(40,0),(18,0),(3,7),(13,7),(2,0),(49,0)])) (.leaf (3,926257968,422,[(8,1)]))))) (.node (.node (.leaf (3,924161840,284,[(6,0),(4,4)])) (.node (.leaf (3,391220544,278,[(8,6),(12,0),(0,6)])) (.leaf (3,388861248,306,[(17,0),(3,6)])))) (.node (.leaf (3,858048320,480,[(3,6),(4,1),(24,1),(29,1),(7,1)])) (.node (.leaf (3,388843328,360,[(21,0),(36,1)])) (.leaf (3,356337472,460,[(24,1),(0,6)])))))) (.node (.node (.node (.leaf (3,389891904,356,[(0,6),(36,1)])) (.leaf (3,388058944,354,[(8,6),(36,1),(43,1)]))) (.node (.leaf (3,659640128,326,[(0,6),(8,6),(36,1)])) (.node (.leaf (3,387010368,364,[(0,6),(36,1),(4,1),(2,1),(8,6)])) (.leaf (3,392253248,302,[(23,0),(56,0)]))))) (.node (.node (.leaf (3,924143424,356,[(0,6),(12,1),(36,5)])) (.node (.leaf (3,924143424,364,[(53,0),(6,0),(12,1),(36,5)])) (.leaf (3,387534656,452,[(0,6),(8,6)])))) (.node (.leaf (3,387534656,332,[(0,6),(4,1),(8,6)])) (.node (.leaf (3,387534656,364,[(24,1),(0,6),(4,1),(13,1)])) (.leaf (3,892948288,454,[(0,6),(8,6),(4,1),(36,1)])))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf (3,624232737,449,[(16,7),(32,0),(0,4),(7,4)])) (.leaf (3,386469153,356,[(25,0),(7,6)]))) (.node (.leaf (3,923094305,372,[(17,4),(0,6),(7,6),(32,4)])) (.node (.leaf (3,927288609,357,[(16,7),(57,0),(7,6),(12,1),(25,0)])) (.leaf (3,923110689,316,[(0,6),(19,0),(36,0)]))))) (.node (.node (.leaf (3,925207841,313,[(17,0),(16,7),(29,0),(45,0),(32,0)])) (.leaf (3,927304993,301,[(17,0),(16,7),(32,4),(31,0),(12,0)]))) (.node (.leaf (3,928353569,285,[(17,0),(32,4),(16,7),(12,0),(29,0)])) (.node (.leaf (3,923112737,316,[(0,6),(30,0),(17,0),(32,6),(29,0)])) (.leaf (3,926258465,309,[(0,6),(16,7),(29,0),(12,0)])))))) (.node (.node (.node (.leaf (3,927307041,301,[(17,0),(16,7),(12,0),(4,0),(38,6)])) (.leaf (3,389649697,277,[(0,6),(16,7),(29,0)]))) (.node (.leaf (3,929386017,305,[(58,0),(16,7)])) (.node (.leaf (3,643615265,401,[(43,0),(36,2),(8,2)])) (.leaf (3,386714145,376,[(50,0),(17,0),(4,1),(51,0)]))))) (.node (.node (.leaf (3,373082657,433,[(50,0),(17,0),(20,0)])) (.node (.leaf (3,390908449,361,[(11,0),(16,7),(4,1),(17,0)])) (.leaf (3,391957025,345,[(9,0),(8,6),(17,0),(16,7),(4,1)])))) (.node (.leaf (3,923093537,376,[(5,4),(4,1),(8,6),(30,1),(36,4),(24,4)])) (.node (.leaf (3,926239265,369,[(5,4),(16,7),(22,0)])) (.leaf (3,927287841,361,[(48,0),(5,4),(16,7)]))))))) (.node (.node (.node (.node (.leaf (3,641550881,401,[(8,2),(16,7),(43,0),(4,2)])) (.leaf (3,386469409,356,[(25,0),(13,6)]))) (.node (.leaf (3,923094561,372,[(8,6),(5,4),(38,6),(30,1),(32,4),(51,0)])) (.node (.leaf (3,927288865,357,[(17,4),(16,7),(11,0),(25,0)])) (.leaf (3,929386017,309,[(17,0),(0,6),(16,7),(9,0),(35,0)]))))) (.node (.node (.leaf (3,923110945,316,[(20,0),(24,0),(8,4),(38,6)])) (.node (.leaf (3,927305249,301,[(32,4),(16,7),(31,0),(12,0)])) (.leaf (3,928353825,285,[(24,0),(32,4),(16,7),(12,0)])))) (.node (.leaf (3,929387041,301,[(25,0),(5,0),(16,7),(4,0)])) (.node (.leaf (3,891650097,408,[(10,4),(8,4),(5,0)])) (.leaf (3,641550385,401,[(8,2),(16,7),(5,0),(4,2)])))))) (.node (.node (.node (.leaf (3,393037873,281,[(45,0),(16,7),(32,0),(5,0)])) (.leaf (3,923112497,284,[(7,4),(5,0),(8,4),(4,4)]))) (.node (.leaf (3,925209649,281,[(8,4),(16,7),(4,4),(43,0)])) (.node (.leaf (3,321749297,436,[(19,0),(0,3),(24,0),(4,2)])) (.leaf (3,858620209,432,[(20,0),(24,0),(34,2),(31,4),(36,4)]))))) (.node (.node (.leaf (3,858620209,436,[(20,0),(0,3),(24,0),(34,2),(36,4)])) (.node (.leaf (3,355303729,440,[(34,2),(31,4),(20,0),(13,6),(18,0)])) (.leaf (3,623739185,440,[(32,2),(24,0),(0,3),(20,0),(19,4)])))) (.node (.leaf (3,121471281,436,[(19,0),(32,2),(18,0),(34,2),(49,0)])) (.node (.leaf (3,910477617,421,[(24,0),(16,7),(38,5),(18,0)])) (.leaf (3,911526193,405,[(24,0),(0,5),(16,7),(18,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,643615025,401,[(18,0),(4,4)])) (.leaf (3,911001905,421,[(41,0),(9,0),(16,7)]))) (.node (.leaf (3,912050481,405,[(50,0),(16,7),(35,0),(9,0),(59,0)])) (.node (.leaf (3,124078385,313,[(23,0),(16,7),(20,0)])) (.leaf (3,661211441,313,[(17,0),(16,7),(24,0),(45,0),(32,0)]))))) (.node (.node (.leaf (3,923095345,364,[(24,4),(34,0),(43,1),(23,0),(17,4),(30,0)])) (.leaf (3,124080433,301,[(20,0),(24,0),(39,0)]))) (.node (.leaf (3,661213489,301,[(24,0),(16,7),(45,0),(6,0),(12,0)])) (.node (.leaf (3,660705585,301,[(24,0),(16,7),(45,0),(31,0),(12,0)])) (.leaf (3,923111729,316,[(47,0),(45,4),(60,0)])))))) (.node (.node (.node (.leaf (3,925208881,313,[(47,0),(17,0),(16,7),(8,4)])) (.leaf (3,928354609,285,[(45,4),(24,0),(16,7)]))) (.node (.leaf (3,392007985,269,[(16,7),(12,0),(32,6),(29,4),(43,0)])) (.node (.leaf (3,385979697,348,[(9,4),(39,0),(18,4)])) (.leaf (3,660706609,285,[(35,0),(24,0),(16,7)]))))) (.node (.node (.leaf (3,923112753,316,[(30,0),(35,0),(27,0),(29,0),(16,3)])) (.node (.leaf (3,925209905,313,[(17,0),(16,7),(21,0),(29,0)])) (.leaf (3,927307057,301,[(35,0),(24,0),(16,7),(31,0)])))) (.node (.leaf (3,386766129,284,[(24,0),(59,0),(38,7)])) (.node (.leaf (3,924680497,436,[(46,0),(32,2),(6,0),(39,0)])) (.leaf (3,892174641,402,[(5,2),(8,6),(46,4)]))))))) (.node (.node (.node (.node (.leaf (3,907903281,436,[(46,0),(7,2),(8,2),(39,0)])) (.leaf (3,386762033,372,[(39,0),(7,4),(8,4),(10,0)]))) (.node (.leaf (3,908952881,433,[(15,0),(16,7),(8,4),(39,0)])) (.node (.leaf (3,894272817,453,[(7,4),(16,7),(5,0),(2,4),(33,0),(20,0)])) (.leaf (3,911050033,421,[(25,0),(41,0)]))))) (.node (.node (.leaf (3,912098609,405,[(26,0),(20,0)])) (.node (.leaf (3,386765105,294,[(7,6),(6,0)])) (.leaf (3,660706609,279,[(8,6),(16,7),(7,6),(12,0)])))) (.node (.leaf (3,923112753,310,[(8,6),(30,0),(7,6),(5,4)])) (.node (.leaf (3,924161329,309,[(35,0),(6,0),(16,7),(5,0)])) (.leaf (3,925209905,307,[(8,6),(16,7),(12,0),(43,0),(5,4)])))))) (.node (.node (.node (.leaf (3,927307057,295,[(6,0),(16,7),(5,4),(7,6)])) (.leaf (3,386766129,406,[(7,6),(3,7),(16,7)]))) (.node (.leaf (3,388863281,403,[(8,6),(35,0),(16,7)])) (.node (.leaf (3,390960433,391,[(7,6),(24,0),(16,7),(26,0)])) (.leaf (3,390960433,327,[(7,6),(24,0),(16,7),(2,4),(33,0)]))))) (.node (.node (.leaf (3,874348849,428,[(53,0),(39,0),(7,2)])) (.node (.leaf (3,891126065,412,[(20,0),(46,0),(7,2),(19,0),(8,2)])) (.leaf (3,321749297,434,[(8,6),(24,0),(19,0),(2,0)])))) (.node (.leaf (3,388858161,314,[(17,0),(8,6),(16,0),(29,4)])) (.node (.leaf (3,339575089,422,[(7,6),(24,0),(19,0),(26,0),(13,6),(14,0)])) (.leaf (3,893223217,406,[(53,0),(7,6),(4,2)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (3,390955313,302,[(41,0),(46,0),(7,6)])) (.leaf (3,392003889,286,[(8,6),(12,0),(7,6),(29,4),(2,0),(4,6)]))) (.node (.leaf (3,908920113,425,[(25,0),(61,0),(20,0)])) (.node (.leaf (3,106759473,397,[(36,2),(16,7),(7,4),(3,5),(29,2)])) (.leaf (3,912065841,397,[(25,0),(7,4),(16,7),(4,4),(5,0)]))))) (.node (.node (.leaf (3,923092273,348,[(40,0),(7,4),(8,4),(5,0)])) (.leaf (3,339035441,453,[(29,2),(16,7),(7,4),(2,4),(33,0),(9,0),(42,0),(5,0)]))) (.node (.leaf (3,908936497,409,[(15,0),(24,0),(8,4),(16,7)])) (.node (.leaf (3,911033649,397,[(6,0),(16,7),(7,4),(53,0),(29,2)])) (.leaf (3,923060529,370,[(33,0),(8,6),(24,0),(32,0)])))))) (.node (.node (.node (.leaf (3,927254833,355,[(24,0),(16,7),(13,6),(4,4),(8,6)])) (.leaf (3,911526193,403,[(8,6),(24,0),(16,7),(13,6),(2,0)]))) (.node (.leaf (3,390908209,355,[(40,0),(11,0),(16,7),(27,1),(20,0),(36,1)])) (.node (.leaf (3,386763057,314,[(15,0),(20,0),(8,6),(39,4)])) (.leaf (3,893225265,403,[(61,0),(13,6),(16,7)]))))) (.node (.node (.leaf (3,390957361,299,[(15,0),(16,7),(20,0),(27,0),(8,0),(36,0)])) (.node (.leaf (3,392005937,283,[(25,0),(8,6),(16,7)])) (.leaf (3,390679857,327,[(7,6),(24,0),(16,7),(39,0),(33,0)])))) (.node (.leaf (3,911035697,391,[(53,0),(7,6),(16,7)])) (.node (.leaf (3,923111729,302,[(7,6),(19,0),(24,0),(2,0)])) (.leaf (3,924160305,301,[(45,0),(16,7),(24,0),(2,0)]))))))) (.node (.node (.node (.node (.leaf (3,925208881,299,[(40,0),(17,0),(16,7),(2,0),(43,0)])) (.leaf (3,928354609,271,[(7,6),(16,7),(2,0),(29,0),(43,0),(12,0)]))) (.node (.leaf (3,386765105,302,[(53,0),(20,0),(24,4)])) (.node (.leaf (3,388862257,299,[(6,0),(20,0),(16,7),(17,0)])) (.leaf (3,392007985,271,[(7,6),(16,7),(12,0),(29,4),(4,6),(43,0)]))))) (.node (.node (.leaf (3,385979697,286,[(8,6),(7,6),(20,0),(49,0)])) (.node (.leaf (3,923112753,286,[(8,6),(19,0),(7,6)])) (.leaf (3,924161329,285,[(9,0),(6,0),(16,7),(15,0),(40,0)])))) (.node (.leaf (3,925209905,283,[(8,6),(16,7),(40,0),(43,0),(29,0)])) (.node (.leaf (3,927307057,271,[(6,0),(16,7),(7,6),(29,0)])) (.leaf (3,390698289,271,[(7,6),(6,0),(16,7),(29,0)])))))) (.node (.node (.node (.leaf (3,386766129,286,[(25,0),(8,6),(24,0)])) (.leaf (3,388863281,283,[(26,0),(8,6),(13,6),(4,6),(29,4)]))) (.node (.leaf (3,390960433,271,[(7,6),(16,7),(31,0),(25,0),(29,4)])) (.node (.leaf (3,643615281,401,[(4,4),(36,2),(8,2)])) (.leaf (3,391957041,337,[(8,6),(16,7),(51,0),(12,1)]))))) (.node (.node (.leaf (3,386469425,356,[(7,6),(10,0),(27,0)])) (.node (.leaf (3,923094577,372,[(7,6),(19,0),(8,6),(5,4)])) (.leaf (3,925191729,369,[(58,0),(16,7),(44,0),(5,4)])))) (.node (.leaf (3,927288881,357,[(7,6),(16,7),(5,4),(11,0),(62,0)])) (.node (.leaf (3,923110961,316,[(19,0),(7,4),(8,4),(24,0),(4,4)])) (.leaf (3,923095601,364,[(24,4),(7,6),(34,0),(30,0),(23,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,929387057,301,[(24,0),(16,7),(45,0),(40,0)])) (.leaf (3,374702897,404,[(22,0),(32,0),(47,0),(10,0)]))) (.node (.leaf (3,374702897,436,[(51,0),(39,0),(32,0),(10,0),(27,3)])) (.node (.leaf (3,660146993,337,[(3,5),(16,7),(32,0),(36,1)])) (.leaf (3,374164273,449,[(51,0),(16,7),(8,2)]))))) (.node (.node (.leaf (3,642599729,449,[(51,0),(16,7),(3,3)])) (.node (.leaf (3,357387057,449,[(39,0),(16,7),(36,1)])) (.leaf (3,625822513,449,[(39,0),(16,7),(36,1)])))) (.node (.leaf (3,390941489,353,[(51,0),(16,7),(0,1)])) (.node (.leaf (3,374704945,433,[(51,0),(16,7),(32,0),(27,3),(39,0)])) (.leaf (3,386501425,368,[(0,1),(39,4),(4,4),(63,1),(47,0),(51,4)])))))) (.node (.node (.node (.leaf (3,660179761,337,[(0,1),(16,7),(4,4),(36,1)])) (.leaf (3,923095857,356,[(54,0),(33,0),(23,0)]))) (.node (.leaf (3,925193009,353,[(16,7),(35,1),(43,1),(36,5),(22,0)])) (.node (.leaf (3,923095857,372,[(54,0),(3,5),(16,3),(36,5),(23,0)])) (.leaf (3,925193009,369,[(3,5),(39,0),(16,7),(36,5),(36,1),(35,1)]))))) (.node (.node (.leaf (3,923113265,340,[(47,0)])) (.node (.leaf (3,925210417,337,[(47,0),(16,7)])) (.leaf (3,929404721,405,[(47,0),(16,7),(32,0),(27,0)])))) (.node (.leaf (3,355828529,436,[(51,0),(22,0),(32,0),(18,2)])) (.node (.leaf (3,625312561,396,[(0,3),(4,4)])) (.leaf (3,374655793,433,[(27,2),(24,0),(16,7),(32,0)]))))))) (.node (.node (.node (.node (.leaf (3,386452273,368,[(0,1),(34,4),(4,4),(63,1),(47,0),(24,0)])) (.leaf (3,660130609,337,[(0,1),(16,7),(4,4),(36,1)]))) (.node (.leaf (3,355830577,433,[(22,0),(16,7),(39,0),(27,3),(17,0),(32,0)])) (.node (.leaf (3,123014961,453,[(24,0),(32,4),(16,7),(39,0)])) (.leaf (3,928321329,325,[(32,4),(16,7),(24,0)]))))) (.node (.node (.leaf (3,928321329,453,[(24,0),(32,4),(16,7)])) (.node (.leaf (3,928321329,341,[(47,0),(0,5),(16,7)])) (.leaf (3,393039665,405,[(51,0),(16,7),(18,0),(32,0),(34,0)])))) (.node (.leaf (3,375213873,405,[(27,0),(51,0),(16,7),(32,0)])) (.node (.leaf (3,123048753,397,[(6,0),(32,4),(16,7),(12,0)])) (.leaf (3,928355121,269,[(32,4),(16,7),(12,0)])))))) (.node (.node (.node (.leaf (3,928355121,397,[(47,0),(6,0),(16,7)])) (.leaf (3,928355121,285,[(47,0),(8,4),(16,7),(32,4)]))) (.node (.leaf (3,923113265,284,[(32,4),(51,0),(27,0)])) (.node (.leaf (3,643630897,389,[(16,7),(3,5),(7,4),(36,2)])) (.leaf (3,386746161,372,[(58,0),(2,0),(7,4),(8,4),(49,1)]))))) (.node (.node (.leaf (3,388843313,369,[(15,0),(8,4),(36,1),(16,7)])) (.node (.leaf (3,390940465,357,[(6,0),(7,4),(16,7),(36,1)])) (.leaf (3,375211825,405,[(58,0),(16,7),(7,4),(51,0),(8,4)])))) (.node (.leaf (3,386765617,294,[(7,6),(10,0),(2,0)])) (.node (.leaf (3,927307569,327,[(7,6),(16,7),(11,0),(4,4),(33,0)])) (.leaf (3,923113265,310,[(51,0),(7,6),(8,6)]))))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf (3,925210417,307,[(8,6),(16,7),(12,0),(43,0)])) (.leaf (3,927307569,295,[(7,6),(16,7),(31,0),(5,4),(25,0)]))) (.node (.leaf (3,336954161,428,[(39,0),(10,4),(7,2),(8,2)])) (.node (.leaf (3,873825073,428,[(39,0),(22,0),(7,2)])) (.leaf (3,890602289,412,[(10,4),(7,2),(8,2),(2,0),(22,0)]))))) (.node (.node (.leaf (3,371525425,425,[(39,0),(22,0),(16,7)])) (.leaf (3,892667697,453,[(2,4),(5,0),(7,4),(16,7),(8,4)]))) (.node (.leaf (3,374671153,397,[(22,0),(8,4),(7,4),(16,7),(4,2)])) (.node (.leaf (3,372049713,425,[(39,0),(22,0),(16,7)])) (.leaf (3,893191985,453,[(16,7),(3,5),(7,4),(5,0),(4,2),(34,0)])))))) (.node (.node (.node (.leaf (3,389875505,357,[(24,0),(16,7),(7,4),(2,0)])) (.leaf (3,375195441,397,[(25,0),(22,0),(4,2),(36,2)]))) (.node (.leaf (3,643630897,397,[(7,4),(16,7),(3,5),(36,2),(4,2),(34,0)])) (.node (.leaf (3,372066097,409,[(32,2),(16,7),(2,0),(8,4)])) (.leaf (3,339560241,453,[(24,0),(16,7),(4,2),(7,4),(8,0)]))))) (.node (.node (.leaf (3,389891889,341,[(22,0),(7,4),(16,7),(8,4),(2,0)])) (.node (.leaf (3,374163249,397,[(22,0),(16,7),(2,0),(7,4),(4,2)])) (.leaf (3,923112241,302,[(64,0),(6,0),(7,6)])))) (.node (.leaf (3,925209393,299,[(17,0),(16,7),(13,6),(4,4)])) (.node (.leaf (3,928355121,271,[(7,6),(16,7),(12,0),(4,4),(43,0)])) (.leaf (3,923113265,286,[(25,0),(8,6),(4,4)]))))))) (.node (.node (.node (.node (.leaf (3,925210417,283,[(8,6),(16,7),(4,4),(43,0)])) (.leaf (3,927307569,271,[(7,6),(16,7),(31,0),(4,4),(25,0)]))) (.node (.leaf (3,386469185,364,[(27,0),(8,4),(10,1),(0,4)])) (.node (.leaf (3,388566337,361,[(27,0),(32,1),(16,7)])) (.leaf (3,391712065,333,[(8,4),(16,7),(31,0),(0,4),(4,1),(12,1)]))))) (.node (.node (.leaf (3,923095361,364,[(27,0),(8,4),(0,4),(60,0),(18,0)])) (.node (.leaf (3,925192513,361,[(27,0),(16,7),(8,4),(18,0),(35,1),(43,1)])) (.leaf (3,120934721,357,[(8,4),(16,7),(4,1),(12,1),(0,4)])))) (.node (.leaf (3,923112769,316,[(0,6),(34,0),(30,0),(16,3)])) (.node (.leaf (3,925209921,313,[(8,4),(16,7),(31,0),(12,0),(17,0)])) (.leaf (3,926258497,309,[(0,6),(24,0),(16,7)])))))) (.node (.node (.node (.leaf (3,923112769,302,[(7,6),(30,0),(2,0)])) (.leaf (3,924161345,301,[(34,0),(16,7),(45,0),(2,0),(5,0)]))) (.node (.leaf (3,925209921,299,[(8,4),(16,7),(2,0),(29,0),(38,0)])) (.node (.leaf (3,926258497,295,[(7,6),(16,7),(2,0),(5,4),(29,0)])) (.leaf (3,374655553,393,[(16,7),(12,2),(5,2),(38,5)]))))) (.node (.node (.leaf (3,643615297,401,[(17,0),(3,6),(27,0)])) (.node (.leaf (3,923078209,364,[(47,0),(60,0),(7,6)])) (.leaf (3,925175361,361,[(47,0),(16,7),(43,1)])))) (.node (.leaf (3,374672961,397,[(31,0),(16,7),(7,2),(5,2),(12,0),(29,5),(9,0),(3,4)])) (.node (.leaf (3,928321089,333,[(7,6),(16,7),(4,4),(24,1),(44,0)])) (.leaf (3,386469441,364,[(53,0),(27,0),(34,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,388566593,361,[(27,0),(16,7),(4,1),(34,0),(32,0)])) (.leaf (3,372837953,421,[(53,0),(16,7),(24,0)]))) (.node (.leaf (3,391712321,333,[(7,6),(16,7),(27,0),(4,1),(44,0),(12,0)])) (.node (.leaf (3,923095617,364,[(7,6),(60,0),(34,0),(24,4)])) (.leaf (3,925192769,361,[(5,4),(16,7),(34,0),(29,1),(3,4),(35,0)]))))) (.node (.node (.leaf (3,926241345,357,[(7,6),(16,7),(34,0),(5,4),(29,1)])) (.leaf (3,923113025,284,[(7,4),(5,0),(3,6),(29,0)]))) (.node (.leaf (3,925210177,281,[(9,0),(16,7),(3,6)])) (.node (.leaf (3,385961793,356,[(49,1),(0,6)])) (.leaf (3,388058945,353,[(16,7),(3,6),(36,1),(43,1)])))))) (.node (.node (.node (.leaf (3,374427457,389,[(23,0),(16,7)])) (.leaf (3,659640129,325,[(0,6),(16,7),(36,1)]))) (.node (.leaf (3,385961793,364,[(0,6),(10,1),(36,1),(34,0)])) (.node (.leaf (3,388058945,361,[(32,1),(16,7),(36,1),(3,6),(34,0)])) (.leaf (3,392253249,301,[(23,0),(16,7),(40,0)]))))) (.node (.node (.leaf (3,923094849,332,[(0,6),(16,3),(33,0),(29,1)])) (.node (.leaf (3,925192001,329,[(26,0),(16,7)])) (.leaf (3,923094849,364,[(53,0),(51,1),(16,3)])))) (.node (.leaf (3,925192001,361,[(26,0),(29,1),(4,5),(12,0)])) (.node (.leaf (3,386486081,364,[(0,6),(10,1),(16,1),(12,0)])) (.leaf (3,892948289,453,[(0,6),(16,7),(36,1),(4,1),(34,0)]))))))) (.node (.node (.node (.node (.leaf (3,393039681,261,[(16,7),(61,0)])) (.leaf (3,393039681,389,[(23,0),(16,7)]))) (.node (.leaf (3,393039681,293,[(23,0),(16,7)])) (.node (.leaf (3,393039681,269,[(53,0),(16,7)])) (.leaf (3,923113281,300,[(23,0),(34,0)]))))) (.node (.node (.leaf (3,386746177,364,[(40,0),(49,1),(7,4)])) (.node (.leaf (3,388843329,361,[(40,0),(16,7),(36,1),(21,0)])) (.leaf (3,389891905,357,[(39,0),(16,7),(7,4),(40,0),(36,1)])))) (.node (.leaf (3,375211841,397,[(23,0),(16,7),(34,0)])) (.node (.leaf (3,929386305,271,[(39,0),(16,7),(7,6),(22,0)])) (.leaf (3,393039681,263,[(7,6),(16,7),(11,0),(25,0)])))))) (.node (.node (.node (.leaf (3,393039681,271,[(53,0),(40,0),(16,7),(34,0)])) (.leaf (3,386502465,294,[(7,6),(10,0),(34,0)]))) (.node (.leaf (3,923113281,302,[(23,0),(39,0),(7,6),(12,0)])) (.node (.leaf (3,925210433,299,[(39,0),(5,4),(16,7),(29,0),(12,0)])) (.leaf (3,926259009,295,[(7,6),(16,7),(12,0),(29,0),(5,4),(2,0)]))))) (.node (.node (.leaf (3,386504513,270,[(7,6),(49,0),(24,0)])) (.node (.leaf (3,374130769,417,[(17,0),(8,2),(27,0)])) (.leaf (3,643614801,401,[(17,0),(8,2)])))) (.node (.leaf (3,391956561,337,[(8,6),(27,0),(16,7)])) (.node (.leaf (3,929385553,285,[(48,0),(16,7),(24,0),(27,0),(40,0),(3,7)])) (.leaf (3,356352337,412,[(41,0),(27,0),(35,0),(5,0)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (3,625836369,396,[(0,3),(5,0),(29,4)])) (.leaf (3,355780945,465,[(27,2),(16,7),(29,1),(26,0),(18,0),(32,0)]))) (.node (.leaf (3,386451793,376,[(34,4),(65,0),(0,1),(18,0)])) (.node (.leaf (3,892914001,465,[(0,5),(5,2),(16,7)])) (.leaf (3,625838417,393,[(34,0),(16,7)]))))) (.node (.node (.leaf (3,386469201,356,[(25,0),(13,6)])) (.leaf (3,893193553,453,[(0,5),(5,2),(16,7),(12,0)]))) (.node (.leaf (3,923094353,348,[(26,0),(27,0),(29,1),(9,0),(4,5),(4,4),(18,0)])) (.node (.leaf (3,925191505,345,[(41,0),(26,0),(27,0),(4,4),(29,0)])) (.leaf (3,661474641,285,[(20,0),(16,7),(17,0),(38,7),(27,0),(3,0)])))))) (.node (.node (.node (.leaf (3,625839441,389,[(0,3),(16,7)])) (.leaf (3,388583761,329,[(34,0),(16,7),(0,1)]))) (.node (.leaf (3,389907793,341,[(40,0),(16,7),(8,4),(7,4),(5,0)])) (.node (.leaf (3,386765137,270,[(7,6),(6,0),(18,0)])) (.leaf (3,607486545,388,[(7,4),(66,0),(53,0),(25,0)]))))) (.node (.node (.leaf (3,607486545,396,[(67,0),(7,4),(53,0)])) (.node (.leaf (3,389382737,404,[(25,0),(8,4)])) (.leaf (3,389382737,412,[(67,0),(25,0),(22,0)])))) (.node (.leaf (3,657818193,404,[(25,0),(8,4)])) (.node (.leaf (3,657818193,412,[(25,0),(4,3),(8,4),(29,0)])) (.leaf (3,390431313,396,[(25,0),(4,3)]))))))) (.node (.node (.node (.node (.leaf (3,386469457,324,[(7,6),(25,0)])) (.leaf (3,386469457,452,[(7,6),(10,1),(53,0)]))) (.node (.leaf (3,392760913,261,[(16,7),(53,0)])) (.node (.leaf (3,392760913,389,[(53,0),(16,7)])) (.leaf (3,386469457,332,[(7,6),(10,1),(53,0)]))))) (.node (.node (.leaf (3,392760913,269,[(53,0),(16,7)])) (.node (.leaf (3,388334161,440,[(65,0),(8,4),(37,0),(28,0),(34,4)])) (.leaf (3,339051089,428,[(37,0),(7,4),(24,2),(34,0),(36,2)])))) (.node (.leaf (3,607486545,420,[(67,0),(7,4)])) (.node (.leaf (3,87392849,412,[(67,0),(7,4),(8,4),(16,3)])) (.leaf (3,355828305,412,[(27,0),(30,0),(7,4),(8,4),(29,0),(36,2),(10,0)])))))) (.node (.node (.node (.leaf (3,624263761,412,[(4,3),(7,4),(30,0),(8,4),(24,0)])) (.leaf (3,892699217,404,[(68,0),(8,4),(7,4),(36,2),(25,0)]))) (.node (.leaf (3,892699217,412,[(37,0),(69,0),(34,0),(7,4),(22,0)])) (.node (.leaf (3,389382737,436,[(68,0),(8,4),(25,0),(28,0),(27,0)])) (.leaf (3,657818193,436,[(68,0),(8,4),(7,4),(28,0),(10,0),(36,2)]))))) (.node (.node (.leaf (3,893747793,396,[(68,0),(24,2),(34,0),(7,4),(25,0)])) (.node (.leaf (3,390431313,428,[(68,0),(69,0),(59,0),(30,0)])) (.leaf (3,927302225,300,[(47,0),(7,4)])))) (.node (.leaf (3,391479889,412,[(25,0),(34,0),(8,4),(16,0)])) (.node (.leaf (3,659915345,412,[(67,0),(7,4),(8,4),(36,2),(10,0)])) (.leaf (3,929369681,301,[(45,0),(16,7),(24,0),(22,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,386469457,356,[(7,6),(27,0),(25,0),(10,1)])) (.leaf (3,392760913,293,[(27,0),(16,7),(45,0)]))) (.node (.leaf (3,385961553,348,[(7,6),(10,1),(8,6)])) (.node (.leaf (3,923094609,348,[(30,0),(27,0),(7,6),(4,5),(29,0),(4,4),(36,4),(3,6)])) (.leaf (3,925191761,345,[(27,0),(16,7),(22,0),(35,0),(29,0),(3,6)]))))) (.node (.node (.leaf (3,927288913,333,[(11,0),(16,7),(7,6),(29,1),(3,1)])) (.node (.leaf (3,386485841,348,[(7,6),(24,0),(3,6)])) (.leaf (3,388582993,345,[(8,6),(16,7),(32,1)])))) (.node (.leaf (3,372854353,405,[(24,0),(7,2),(16,7),(12,0)])) (.node (.leaf (3,390680145,333,[(7,6),(16,7),(24,0)])) (.leaf (3,390942289,325,[(7,6),(16,7),(11,0),(62,0),(3,2)])))))) (.node (.node (.node (.leaf (3,858096465,464,[(61,0),(49,4),(58,0)])) (.leaf (3,372605777,404,[(47,0),(49,0),(17,0),(38,7),(38,5)]))) (.node (.leaf (3,372605777,412,[(40,0),(49,0),(24,0),(17,0),(18,3),(38,5),(3,7)])) (.node (.leaf (3,393005905,273,[(16,7),(47,0),(3,7),(58,0)])) (.leaf (3,393005905,401,[(61,0),(50,0)]))))) (.node (.node (.leaf (3,661441361,401,[(61,0)])) (.node (.leaf (3,386714449,344,[(40,0),(10,1),(31,1)])) (.leaf (3,393005905,281,[(50,0),(40,0)])))) (.node (.leaf (3,393005905,277,[(17,0),(0,5),(16,7)])) (.node (.leaf (3,386714449,348,[(0,5),(17,0),(10,1)])) (.leaf (3,923110225,344,[(15,0),(40,4),(24,4),(4,1),(31,1)]))))))) (.node (.node (.node (.node (.leaf (3,641043281,405,[(32,1),(16,7),(17,0),(45,4)])) (.leaf (3,373656401,397,[(17,0),(16,7),(15,0),(24,0),(6,0)]))) (.node (.leaf (3,372869969,401,[(0,5),(16,7),(40,0),(24,0)])) (.node (.leaf (3,658082641,337,[(36,4),(4,1),(0,1)])) (.leaf (3,929369937,285,[(0,5),(24,0),(16,7)]))))) (.node (.node (.leaf (3,386469713,348,[(0,5),(40,0),(10,1),(18,0)])) (.node (.leaf (3,925208401,337,[(61,0),(16,7)])) (.leaf (3,929402705,405,[(48,0),(47,0),(16,7),(24,0)])))) (.node (.leaf (3,642355025,397,[(0,3),(24,0),(16,7)])) (.node (.leaf (3,355828561,412,[(51,0),(49,0),(17,0),(27,2)])) (.leaf (3,624266065,405,[(35,0),(16,7),(43,4),(45,4)])))))) (.node (.node (.node (.leaf (3,392777553,405,[(35,0),(16,7),(27,0),(24,0)])) (.leaf (3,372854609,405,[(48,0),(16,7),(27,4),(24,0),(3,7),(40,0)]))) (.node (.leaf (3,929369937,271,[(7,6),(24,0),(16,7)])) (.node (.leaf (3,923110225,314,[(7,4),(36,4),(8,6),(70,0),(4,0),(24,4)])) (.leaf (3,926255953,307,[(54,0),(16,7),(3,0)]))))) (.node (.node (.leaf (3,927304529,299,[(25,0),(36,4),(18,0),(15,0),(29,0)])) (.node (.leaf (3,923111249,310,[(7,6),(40,0),(8,6),(36,4)])) (.leaf (3,925208401,307,[(71,0),(8,6),(16,7),(36,4)])))) (.node (.leaf (3,927305553,295,[(40,0),(16,7),(7,6),(36,4),(25,0)])) (.node (.leaf (3,923112273,302,[(7,6),(6,0),(36,4),(40,4)])) (.leaf (3,925209425,299,[(6,0),(16,7),(36,4),(40,4),(29,0)])))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf (3,926258001,295,[(7,6),(6,0),(16,7),(36,4),(2,0)])) (.leaf (3,386501699,294,[(8,4),(0,4),(10,0),(27,0)]))) (.node (.leaf (3,911049027,422,[(27,0),(0,2),(8,2),(60,0),(25,0)])) (.node (.leaf (3,911050051,421,[(11,0),(16,7),(0,2),(25,0),(27,0)])) (.leaf (3,912098627,405,[(0,6),(16,7),(8,0),(31,0)]))))) (.node (.node (.leaf (3,911051075,419,[(27,0),(16,7),(8,2),(57,0),(26,0)])) (.leaf (3,386765123,358,[(27,0),(8,4),(0,4),(10,0),(26,0),(31,0)]))) (.node (.leaf (3,387813699,357,[(27,0),(16,7),(0,4),(11,0),(26,0)])) (.node (.leaf (3,912101699,391,[(27,0),(8,4),(16,7),(0,4)])) (.leaf (3,660706627,279,[(8,6),(16,7),(0,6),(12,0)])))))) (.node (.node (.node (.leaf (3,923112771,310,[(0,6),(30,0),(8,6)])) (.leaf (3,924161347,309,[(0,6),(16,7),(2,0),(12,0)]))) (.node (.leaf (3,925209923,307,[(8,6),(16,7),(12,0),(43,0)])) (.node (.leaf (3,927307075,295,[(11,0),(35,0),(16,7),(25,0)])) (.leaf (3,386504003,278,[(8,6),(49,0)]))))) (.node (.node (.leaf (3,385975619,364,[(9,4),(37,0),(24,4),(5,0)])) (.node (.leaf (3,911312195,397,[(7,5),(24,0),(16,7),(4,4)])) (.leaf (3,912098627,397,[(39,0),(24,0),(16,7),(22,0)])))) (.node (.leaf (3,660706627,271,[(39,0),(16,7),(22,0),(35,0),(43,0)])) (.node (.leaf (3,923112771,302,[(39,0),(30,0),(24,0),(35,0)])) (.leaf (3,924161347,301,[(35,0),(2,0),(16,7),(24,0)]))))))) (.node (.node (.node (.node (.leaf (3,388863299,267,[(24,0),(16,7),(44,0)])) (.leaf (3,387809603,316,[(40,0),(0,6),(27,4),(60,0),(36,0)]))) (.node (.leaf (3,388858179,314,[(17,0),(8,6),(16,0),(29,4)])) (.node (.leaf (3,356352323,406,[(0,6),(19,0),(8,6),(26,0),(27,0),(31,0)])) (.leaf (3,893223235,406,[(0,6),(19,0),(8,6),(31,0)]))))) (.node (.node (.leaf (3,893223235,438,[(69,0),(3,6),(31,0),(4,2)])) (.node (.leaf (3,357400899,430,[(56,0),(60,0),(25,0),(24,0),(9,0)])) (.leaf (3,894271811,398,[(60,0),(0,2),(8,2),(4,2),(29,4)])))) (.node (.leaf (3,392003907,286,[(0,6),(12,0),(8,6),(29,4),(2,0)])) (.node (.leaf (3,386762051,316,[(22,0),(0,6),(27,4),(36,0)])) (.leaf (3,388859203,313,[(17,0),(3,6),(16,7)])))))) (.node (.node (.node (.leaf (3,87917891,437,[(25,0),(16,3),(26,0),(3,4),(3,2),(29,0),(13,1)])) (.leaf (3,624788803,405,[(4,2),(0,6),(16,7),(13,1)]))) (.node (.leaf (3,893224259,405,[(0,6),(16,7),(22,0)])) (.node (.leaf (3,893224259,437,[(3,6),(12,0),(31,0)])) (.leaf (3,894272835,397,[(0,2),(16,7),(31,0),(29,4)]))))) (.node (.node (.leaf (3,392004931,285,[(11,0),(16,7),(0,6),(29,4)])) (.node (.leaf (3,386763075,314,[(72,0),(57,0),(27,4),(8,6)])) (.leaf (3,387811651,313,[(39,0),(16,7),(3,6),(29,4),(4,6)])))) (.node (.leaf (3,893225283,403,[(8,6),(17,0),(16,7),(31,0)])) (.node (.leaf (3,357402947,427,[(61,0),(8,2),(34,2),(17,0),(39,0),(55,0)])) (.leaf (3,894273859,395,[(8,2),(16,7),(31,0),(43,4),(26,0),(0,0),(4,2)])))))))) (.node (.node (.node (.node (.node (.leaf (3,392005955,283,[(8,6),(16,7),(12,0),(29,4)])) (.leaf (3,385961283,342,[(56,0),(0,6),(10,0)]))) (.node (.leaf (3,387009859,341,[(56,0),(0,6),(16,7)])) (.node (.leaf (3,660688195,279,[(56,0),(16,7),(0,6)])) (.leaf (3,385961283,374,[(56,0),(0,6),(8,6),(25,0),(17,0),(4,0),(16,1)]))))) (.node (.node (.leaf (3,387009859,373,[(3,6),(17,0),(16,7),(25,0),(0,6),(4,0),(13,1),(13,2)])) (.leaf (3,388058435,371,[(56,0),(3,6),(26,0),(13,6),(4,0),(38,1)]))) (.node (.leaf (3,356601155,455,[(56,0),(23,0),(13,6),(38,3),(73,0),(53,0)])) (.node (.leaf (3,923094339,342,[(0,6),(19,0),(8,6),(27,0),(4,4),(14,0)])) (.leaf (3,924142915,341,[(0,6),(22,0),(16,7),(25,0),(27,0)])))))) (.node (.node (.node (.leaf (3,925191491,339,[(8,6),(16,7),(29,0),(21,0),(26,0),(4,4)])) (.leaf (3,912084291,407,[(34,0),(3,6)]))) (.node (.leaf (3,386748739,334,[(60,0),(0,4),(8,4),(26,0),(29,6)])) (.node (.leaf (3,387797315,333,[(0,4),(16,7),(5,0),(2,1),(31,0),(29,6)])) (.leaf (3,923112771,318,[(8,6),(39,0),(24,0),(31,0),(34,0),(0,6),(43,0),(29,0)]))))) (.node (.node (.leaf (3,924161347,317,[(8,2),(22,0),(34,0),(16,7),(24,0),(0,6),(31,0),(12,0)])) (.node (.leaf (3,386504003,286,[(8,6),(49,0),(0,6),(29,0),(31,0)])) (.leaf (3,387552579,285,[(0,6),(29,0),(16,7),(8,6)])))) (.node (.leaf (3,388601155,283,[(8,6),(16,7),(29,0),(43,0),(31,0)])) (.node (.leaf (3,386766147,286,[(25,0),(8,6),(24,0)])) (.leaf (3,387814723,285,[(0,6),(40,0),(16,7)]))))))) (.node (.node (.node (.node (.leaf (3,388863299,283,[(47,0),(8,6),(16,7)])) (.leaf (3,387285571,420,[(25,0),(10,0),(27,0)]))) (.node (.leaf (3,655721027,420,[(7,3),(10,0),(27,0)])) (.node (.leaf (3,370508355,420,[(32,0),(10,0),(11,0),(27,0),(40,0)])) (.leaf (3,638943811,420,[(7,3),(10,0),(27,0)]))))) (.node (.node (.leaf (3,374702659,390,[(32,0),(10,0),(7,7),(40,0),(27,0),(13,3)])) (.node (.leaf (3,374702659,422,[(27,0),(32,0),(10,0),(40,0),(13,7)])) (.leaf (3,643138115,390,[(10,0),(32,0),(7,7),(40,0),(27,0),(13,3)])))) (.node (.leaf (3,643138115,422,[(5,3),(27,0),(32,0),(10,0)])) (.node (.leaf (3,643139139,389,[(16,7),(32,0),(27,0),(13,1),(40,0),(36,3)])) (.leaf (3,643139139,421,[(27,0),(36,3),(16,7),(32,0),(40,0)])))))) (.node (.node (.node (.leaf (3,928351811,325,[(32,4),(16,7),(11,0),(13,1)])) (.leaf (3,643139139,391,[(40,0),(8,4),(16,7),(32,0)]))) (.node (.leaf (3,374704707,419,[(27,0),(16,7),(40,0),(32,0)])) (.node (.leaf (3,386501187,354,[(74,0),(27,4),(33,0),(55,0),(51,4)])) (.leaf (3,929404483,391,[(5,1),(16,7),(32,0),(27,0)]))))) (.node (.node (.leaf (3,893747779,390,[(60,0),(8,2),(0,2)])) (.node (.leaf (3,893747779,422,[(36,3),(8,2),(0,2),(60,0),(26,0)])) (.leaf (3,928350787,278,[(0,6),(12,0)])))) (.node (.leaf (3,928352835,275,[(8,6),(16,7)])) (.node (.leaf (3,386748995,358,[(73,0),(0,4),(31,0)])) (.leaf (3,387797571,357,[(0,4),(16,7),(31,0),(8,0),(25,0)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (3,388846147,355,[(31,0),(16,7),(8,4),(36,1),(26,0),(43,1),(0,0),(55,0)])) (.leaf (3,375214659,391,[(73,0),(16,7),(0,4)]))) (.node (.leaf (3,355828291,390,[(32,0),(10,0),(51,0),(29,2),(13,3),(40,0)])) (.node (.leaf (3,355828291,422,[(51,0),(27,0),(32,0),(10,0),(39,3)])) (.leaf (3,892699203,390,[(10,0),(32,0),(7,7),(34,0),(2,4),(13,3),(5,3)]))))) (.node (.node (.leaf (3,892699203,422,[(5,3),(34,0),(32,0),(10,0)])) (.leaf (3,892700227,389,[(16,7),(32,0),(34,0),(13,1),(2,4),(36,3)]))) (.node (.leaf (3,892700227,421,[(36,3),(16,7),(32,0),(2,4),(20,0),(12,0),(13,1)])) (.node (.leaf (3,892700227,391,[(2,4),(8,4),(16,7),(32,0)])) (.leaf (3,355830339,419,[(51,0),(16,7),(27,0),(39,3),(17,0)])))))) (.node (.node (.node (.leaf (3,923094595,326,[(32,4),(51,0)])) (.leaf (3,925191747,323,[(51,0),(16,7)]))) (.node (.leaf (3,929386051,391,[(51,0),(22,0),(16,7),(32,0),(29,0)])) (.node (.leaf (3,393039427,391,[(22,0),(16,7),(32,0),(34,0)])) (.leaf (3,375213635,391,[(39,0),(16,7),(32,0),(34,0)]))))) (.node (.node (.leaf (3,925210179,267,[(16,7),(4,4),(43,0)])) (.node (.leaf (3,923108931,316,[(11,0),(4,4),(0,6),(36,0),(27,4)])) (.leaf (3,925206083,313,[(17,0),(4,4),(3,6),(16,7)])))) (.node (.leaf (3,928351811,285,[(0,6),(16,7),(12,0),(4,4)])) (.node (.leaf (3,923094595,342,[(0,6),(51,0),(8,6),(27,0),(23,0)])) (.leaf (3,924143171,341,[(0,6),(16,7),(4,4),(22,0),(2,1),(25,0)]))))))) (.node (.node (.node (.node (.leaf (3,925191747,339,[(8,6),(27,0),(21,0),(16,7),(26,0)])) (.leaf (3,929386051,279,[(23,0),(16,7),(8,6),(27,0)]))) (.node (.leaf (3,923112003,302,[(19,0),(0,4),(8,4),(24,0)])) (.node (.leaf (3,923113027,286,[(0,6),(51,0),(8,6)])) (.leaf (3,924161603,285,[(0,6),(16,7),(4,4),(2,0)]))))) (.node (.node (.leaf (3,925210179,283,[(8,6),(16,7),(44,0),(4,4),(3,6)])) (.node (.leaf (3,87394115,421,[(36,3),(16,7),(8,4),(25,0),(26,0)])) (.leaf (3,892700483,421,[(71,0),(16,7),(36,3),(39,0),(12,0)])))) (.node (.leaf (3,385961795,358,[(0,6),(10,0),(36,1),(8,6),(25,0)])) (.node (.leaf (3,388058947,355,[(8,6),(16,7),(36,1),(32,0),(26,0)])) (.leaf (3,923094851,358,[(19,0),(0,6),(8,6),(24,0),(36,4)])))))) (.node (.node (.node (.leaf (3,924143427,357,[(73,0),(16,7),(0,6),(36,4)])) (.leaf (3,925192003,355,[(73,0),(16,7),(43,1)]))) (.node (.leaf (3,386748227,358,[(0,6),(49,1),(8,6),(25,0)])) (.node (.leaf (3,387796803,357,[(0,6),(5,1),(16,7),(2,0)])) (.leaf (3,388845379,355,[(71,0),(8,6),(16,7)]))))) (.node (.node (.leaf (3,375213891,391,[(8,2),(16,7),(0,2),(29,0),(12,0)])) (.node (.leaf (3,386504515,270,[(0,4),(8,4),(49,0),(29,4)])) (.leaf (3,874877011,419,[(8,1)])))) (.node (.leaf (3,925208659,307,[(5,4),(16,7),(31,0),(3,0),(43,0)])) (.node (.leaf (3,923111507,302,[(32,4),(5,4),(60,0),(33,0)])) (.leaf (3,924160083,301,[(32,4),(16,7),(36,4),(2,0)])))))))) (.node (.node (.node (.node (.node (.leaf (3,912097619,406,[(73,0),(30,0),(32,2)])) (.leaf (3,912098643,405,[(32,2),(16,7),(27,0),(39,0),(25,0)]))) (.node (.leaf (3,912099667,403,[(73,0),(16,7),(35,0),(26,0)])) (.node (.leaf (3,386765139,294,[(25,0),(39,4)])) (.leaf (3,912101715,391,[(73,0),(16,7),(32,2)]))))) (.node (.node (.leaf (3,386766163,342,[(27,0),(32,0),(39,0),(10,0),(26,0)])) (.node (.leaf (3,390960467,327,[(73,0),(16,7),(32,0),(64,0)])) (.leaf (3,387809619,316,[(19,0),(6,0),(9,4),(5,0),(40,0),(12,4)])))) (.node (.leaf (3,390955347,302,[(11,0),(51,0),(9,4)])) (.node (.leaf (3,386762067,316,[(22,0),(51,0),(27,4),(9,4)])) (.leaf (3,388859219,313,[(21,0),(16,7),(12,4),(4,6),(29,4),(36,6)])))))) (.node (.node (.node (.leaf (3,390956371,301,[(27,0),(51,0),(16,7),(9,4),(12,0)])) (.leaf (3,386765139,302,[(62,0),(51,0),(73,0),(53,0)]))) (.node (.leaf (3,387813715,301,[(53,0),(51,0),(16,7)])) (.node (.leaf (3,370508371,404,[(24,0),(32,0)])) (.leaf (3,929400403,405,[(8,1)]))))) (.node (.node (.leaf (3,373655123,391,[(39,0),(16,7),(32,0),(24,0),(33,0),(42,0)])) (.node (.leaf (3,386501203,338,[(74,0),(0,1),(7,1),(4,4),(33,0)])) (.leaf (3,373918291,387,[(7,5),(16,7),(24,0),(25,0)])))) (.node (.leaf (3,923112019,326,[(56,0),(32,4),(25,0)])) (.node (.leaf (3,925209171,323,[(16,7),(4,4),(44,1),(39,4),(42,0),(57,0)])) (.leaf (3,929403475,391,[(56,0),(16,7),(0,3)]))))))) (.node (.node (.node (.node (.leaf (3,872780371,390,[(3,1)])) (.leaf (3,923112019,278,[(25,0),(11,0)]))) (.node (.leaf (3,69571155,387,[(3,1)])) (.node (.leaf (3,622167635,405,[(8,1)])) (.leaf (3,386501203,370,[(39,4),(24,0),(0,1),(7,1),(27,4)]))))) (.node (.node (.leaf (3,625316435,391,[(3,1)])) (.node (.leaf (3,923113043,310,[(26,0),(27,0),(5,4)])) (.leaf (3,926254675,405,[(8,1)])))) (.node (.leaf (3,923112019,270,[(25,0),(32,4)])) (.node (.leaf (3,118854227,397,[(7,3),(16,7),(4,4),(31,0)])) (.leaf (3,924160595,397,[(32,4),(16,7),(11,0)])))))) (.node (.node (.node (.leaf (3,926257747,391,[(3,1)])) (.leaf (3,873828947,397,[(0,1)]))) (.node (.leaf (3,924160595,285,[(32,4),(16,7),(2,0),(31,0),(3,0)])) (.node (.leaf (3,923108947,316,[(20,0),(24,0),(27,4),(32,4)])) (.leaf (3,925206099,313,[(21,0),(24,0),(16,7),(4,4)]))))) (.node (.node (.leaf (3,927303251,301,[(32,4),(24,0),(16,7),(31,0),(12,0)])) (.node (.leaf (3,923112019,302,[(73,0),(32,4),(24,0)])) (.leaf (3,924160595,301,[(32,4),(24,0),(16,7),(2,0)])))) (.node (.leaf (3,925209171,299,[(44,0),(24,0),(16,7),(4,4)])) (.node (.leaf (3,873828947,429,[(3,1)])) (.leaf (3,924160595,317,[(11,0),(24,0),(32,4),(18,0),(6,0)])))))))))))
def cG6M5 : BST := .node 4503848364561009162 12 0 (.node 3429582770309315671 18 0 (.node 2621156321439025413 9 0 (.node 2519768759977565330 1 0 (.node 2145014628008492831 24 0 (.node 2127341211589864766 58 0 (.nil) (.nil)) (.node 2278937327366244503 48 0 (.nil) (.nil))) (.node 2575314138439870473 2 0 (.node 2567854099780859563 17 0 (.nil) (.nil)) (.node 2588761785399505398 3 0 (.nil) (.nil)))) (.node 3201454950153539359 27 0 (.node 2891992241045931491 25 0 (.node 2881894480351065794 45 0 (.nil) (.nil)) (.node 3152474430186125372 26 0 (.nil) (.nil))) (.node 3421387256922747839 52 0 (.node 3224794176151520736 4 0 (.nil) (.nil)) (.nil)))) (.node 3987017607905497333 10 0 (.node 3712715110332422570 54 0 (.node 3637339888081481287 14 0 (.node 3625768009791740215 42 0 (.nil) (.nil)) (.node 3706541618704329611 53 0 (.nil) (.nil))) (.node 3877677736760794433 6 0 (.node 3782222090841027325 50 0 (.nil) (.nil)) (.nil))) (.node 4249363476156253085 12 1 (.node 4103851059063478678 21 0 (.node 4101425715330502214 46 0 (.nil) (.nil)) (.node 4176505584692471656 57 0 (.nil) (.nil))) (.node 4452750159510805584 15 0 (.node 4301050153295813279 22 1 (.nil) (.nil)) (.nil))))) (.node 5424347022430763511 7 0 (.node 4861570837012457049 61 0 (.node 4760316013791253738 62 0 (.node 4680886927848739460 22 0 (.node 4617829792504490214 56 1 (.nil) (.nil)) (.node 4708176162420793401 55 0 (.nil) (.nil))) (.node 4825605468474538579 49 0 (.node 4800398651903062204 5 0 (.nil) (.nil)) (.nil))) (.node 5327478570210244887 46 1 (.node 5135553631276667228 16 0 (.node 5065226836164388374 44 0 (.nil) (.nil)) (.node 5158805185127237352 43 0 (.nil) (.nil))) (.node 5424334302430904385 19 0 (.node 5412478510273428985 59 0 (.nil) (.nil)) (.nil)))) (.node 6297627734284085641 13 0 (.node 6092260228170335893 11 1 (.node 5758679656080484151 63 0 (.node 5481006342627590671 30 0 (.nil) (.nil)) (.node 6080884975247596269 28 0 (.nil) (.nil))) (.node 6262786157499312727 11 0 (.node 6114637566813735470 0 0 (.nil) (.nil)) (.nil))) (.node 7117393446766596499 51 0 (.node 6830543991852128885 56 0 (.node 6750902582574114676 60 0 (.nil) (.nil)) (.node 7104119099358307650 20 0 (.nil) (.nil))) (.node 8241529035100575333 29 0 (.node 7321484763980541434 23 0 (.nil) (.nil)) (.nil)))))
def cG6T6 : BTree NodeData := .node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf (2,296208,248,[(40,0),(8,0),(39,0),(7,0)])) (.leaf (2,312592,244,[(39,0),(7,0),(8,0)]))) (.node (.leaf (2,312592,252,[(40,0),(7,0),(8,0),(39,0),(9,0),(4,0),(18,0)])) (.node (.leaf (2,328976,236,[(39,0),(7,0),(40,0),(8,0)])) (.leaf (2,869648,220,[(40,0),(8,0),(7,0),(16,2)]))))) (.node (.node (.leaf (2,869648,252,[(39,0),(7,0),(40,0),(8,0),(36,1),(17,0),(24,0),(47,0),(16,2)])) (.leaf (2,313616,250,[(75,0),(64,0),(8,2),(40,0),(38,1),(18,0),(32,0)]))) (.node (.leaf (2,837904,242,[(40,0),(8,2),(36,2),(34,0),(39,0)])) (.node (.leaf (2,870672,218,[(5,0),(8,2),(64,0),(2,0),(4,2),(28,2),(16,2),(2,2)])) (.leaf (2,887056,186,[(28,0),(8,2),(39,0),(17,0),(9,0),(4,0)])))))) (.node (.node (.node (.leaf (2,331024,238,[(72,0),(64,0),(7,2),(40,0),(9,0),(4,0),(3,1)])) (.leaf (2,593168,230,[(40,0),(7,2),(2,0)]))) (.node (.leaf (2,347408,222,[(39,0),(8,2),(40,0),(7,2),(16,2),(22,0),(5,0)])) (.node (.leaf (2,609552,214,[(39,0),(8,2),(7,2)])) (.leaf (2,871696,214,[(8,2),(5,0),(7,2),(16,2),(2,2)]))))) (.node (.node (.leaf (2,871696,222,[(40,0),(22,0),(7,2),(8,2),(16,2),(4,0),(28,0)])) (.leaf (2,363792,190,[(40,0),(7,2),(8,2),(24,0),(10,0),(28,0)]))) (.node (.leaf (2,625936,182,[(39,0),(7,2),(8,2)])) (.node (.leaf (2,888080,182,[(28,0),(7,2),(8,2),(39,0),(24,0)])) (.leaf (2,888080,190,[(40,0),(24,0),(7,2),(8,2),(29,0)]))))))) (.node (.node (.node (.node (.leaf (2,872720,206,[(7,2),(5,0),(2,2),(64,0),(16,2),(28,2)])) (.leaf (2,889104,174,[(7,2),(47,0),(28,0),(18,0)]))) (.node (.leaf (2,365840,190,[(34,0),(8,2),(7,2),(2,0),(5,0),(49,0),(28,0)])) (.node (.leaf (2,627984,158,[(40,0),(7,2),(8,2)])) (.leaf (2,890128,158,[(28,0),(7,2),(8,2),(16,2),(29,0)]))))) (.node (.node (.leaf (2,890128,190,[(39,0),(8,2),(7,2),(34,0),(5,0),(16,2),(4,0)])) (.leaf (2,838416,240,[(8,2),(41,0),(58,0),(36,2)]))) (.node (.leaf (2,838416,248,[(41,0),(8,2),(51,0)])) (.node (.leaf (2,346896,248,[(58,0),(24,0),(4,1),(36,0)])) (.leaf (2,347920,244,[(58,0),(7,2)])))))) (.node (.node (.node (.leaf (2,347920,220,[(22,0),(8,2),(7,2)])) (.leaf (2,347920,252,[(41,0),(58,0),(7,2),(51,0),(5,0)]))) (.node (.leaf (2,610064,244,[(58,0),(7,2),(36,0)])) (.node (.leaf (2,610064,252,[(58,0),(7,2),(4,1),(24,0),(5,0),(22,0)])) (.leaf (2,872208,220,[(22,0),(8,2),(7,2),(29,0)]))))) (.node (.node (.leaf (2,364304,188,[(24,0),(7,0),(8,0),(29,0)])) (.node (.leaf (2,628496,156,[(7,0),(36,0),(8,0),(51,0),(29,0)])) (.leaf (2,296240,250,[(76,0),(8,1),(22,0),(7,1),(40,0),(38,1),(39,1),(16,2)])))) (.node (.leaf (2,820528,248,[(50,0),(32,0),(71,0),(36,2)])) (.node (.leaf (2,820528,250,[(76,0),(8,1),(22,0),(10,0),(40,0),(16,2),(39,1),(34,0)])) (.leaf (2,312624,244,[(50,0),(24,0),(3,1)])))))))) (.node (.node (.node (.node (.node (.leaf (2,312624,246,[(25,0),(8,1),(24,0),(39,0),(7,1),(4,0)])) (.leaf (2,836912,244,[(10,0),(32,0),(47,0),(0,3),(34,0)]))) (.node (.leaf (2,836912,246,[(25,0),(8,1),(10,0),(34,0),(22,0),(24,0),(28,0)])) (.node (.leaf (2,329008,238,[(25,0),(40,0),(8,1),(39,1),(7,1),(3,1),(22,0),(16,2),(36,2)])) (.leaf (2,853296,236,[(53,0),(10,0),(36,2),(34,0)]))))) (.node (.node (.leaf (2,853296,238,[(25,0),(22,0),(40,0),(7,1),(39,1),(16,2),(36,2),(34,0),(10,0)])) (.leaf (2,345392,252,[(34,0),(24,0),(27,1),(9,2),(5,0),(17,0),(38,1),(3,3),(4,0),(27,0),(18,0),(13,1)]))) (.node (.leaf (2,345392,222,[(25,0),(76,0),(8,1),(24,0),(40,0),(29,0)])) (.node (.leaf (2,607536,220,[(7,1),(8,1),(29,0),(16,2),(10,2)])) (.leaf (2,607536,252,[(22,0),(8,1),(7,1),(24,0),(10,0),(38,1),(27,0),(3,1)])))))) (.node (.node (.node (.leaf (2,869680,220,[(24,0),(0,3),(26,0),(47,0),(9,0),(38,2),(17,0),(3,1)])) (.leaf (2,869680,222,[(25,0),(8,1),(40,0),(7,1),(10,0),(76,0),(29,0)]))) (.node (.leaf (2,886064,188,[(10,0),(0,3),(18,0),(39,0),(24,0),(43,0),(36,0)])) (.node (.leaf (2,886064,190,[(39,0),(22,0),(6,0),(7,1),(10,0)])) (.leaf (2,313648,246,[(18,0),(7,1),(24,0),(0,1),(32,0),(43,0),(4,0)]))))) (.node (.node (.leaf (2,837936,242,[(10,0),(47,0),(40,0),(8,3),(34,0),(13,2)])) (.leaf (2,837936,246,[(50,0),(26,0),(10,0),(7,1),(77,0),(43,0),(63,0)]))) (.node (.leaf (2,346416,250,[(24,0),(34,0),(39,1),(27,1),(10,0),(13,2),(40,0),(3,3),(16,2),(18,0),(38,1)])) (.node (.leaf (2,608560,218,[(50,0),(7,1)])) (.leaf (2,608560,250,[(50,0),(7,1),(24,0),(10,0),(32,0),(16,2),(18,0),(12,0)]))))))) (.node (.node (.node (.node (.leaf (2,887088,186,[(10,0),(8,3),(18,0),(76,0),(17,0),(2,0),(16,2),(12,0)])) (.leaf (2,887088,190,[(44,0),(0,1),(17,0),(32,0),(9,0),(13,0),(36,0)]))) (.node (.leaf (2,68912,230,[(8,1),(0,1),(10,0),(34,0),(24,0)])) (.node (.leaf (2,347440,214,[(50,0),(22,0)])) (.leaf (2,347440,246,[(50,0),(22,0),(24,0),(39,0),(38,2),(27,0),(3,1),(36,0),(4,0)]))))) (.node (.node (.leaf (2,609584,214,[(32,0),(10,0),(3,3),(40,0),(7,3),(25,0)])) (.leaf (2,609584,246,[(24,0),(32,0),(10,0),(18,0),(40,0),(3,3),(13,3),(36,0),(49,0)]))) (.node (.leaf (2,348464,238,[(71,0),(24,0),(9,2),(10,0),(38,3),(34,0),(17,0),(3,1)])) (.node (.leaf (2,610608,206,[(53,0),(8,1),(9,0)])) (.leaf (2,610608,238,[(53,0),(8,1),(34,0),(0,1),(24,0),(39,0),(9,0),(36,0),(10,0)])))))) (.node (.node (.node (.leaf (2,364848,190,[(47,0),(53,0),(22,0),(0,1),(14,0),(10,0),(36,0)])) (.leaf (2,889136,174,[(10,0),(9,0),(38,3),(27,0),(24,0),(76,0),(2,0)]))) (.node (.leaf (2,889136,190,[(47,0),(53,0),(8,1),(57,0)])) (.node (.leaf (2,365872,190,[(35,0),(22,0),(27,0),(24,0),(13,0),(34,0),(38,0),(49,0),(3,0),(10,0)])) (.leaf (2,628016,158,[(53,0),(5,0)]))))) (.node (.node (.leaf (2,890160,158,[(10,0),(8,3),(9,0),(39,0),(38,3),(2,0)])) (.node (.leaf (2,890160,190,[(39,0),(24,0),(35,0),(27,0),(10,0)])) (.leaf (2,296752,244,[(32,0),(0,1),(7,1),(35,0),(36,1)])))) (.node (.leaf (2,296752,242,[(40,0),(8,1),(7,1),(39,0)])) (.node (.leaf (2,558896,244,[(8,1),(32,0),(35,0),(36,1)])) (.leaf (2,821040,242,[(32,0),(8,1),(35,0),(34,0),(36,1)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (2,329520,244,[(47,0),(0,1),(8,1)])) (.leaf (2,329520,230,[(40,0),(7,1),(39,1),(8,1)]))) (.node (.leaf (2,591664,244,[(47,0),(7,1),(3,1)])) (.node (.leaf (2,853808,230,[(40,0),(7,1),(39,1),(5,1)])) (.leaf (2,83760,244,[(51,0),(8,1),(7,1)]))))) (.node (.node (.leaf (2,345904,214,[(40,0),(8,1),(7,1)])) (.leaf (2,345904,246,[(5,1),(34,0),(8,1),(40,0),(7,1),(12,0),(36,1)]))) (.node (.leaf (2,870192,244,[(47,0),(48,0)])) (.node (.leaf (2,870192,214,[(40,0),(8,1),(7,1)])) (.leaf (2,870192,246,[(71,0),(7,1),(8,1),(58,0),(36,1),(40,0),(2,0)])))))) (.node (.node (.node (.leaf (2,362288,244,[(32,0),(47,0),(0,3),(34,0),(19,0),(4,0),(20,0)])) (.leaf (2,362288,182,[(15,0),(39,0),(6,0)]))) (.node (.leaf (2,362288,246,[(26,0),(41,0),(8,1),(32,0),(40,0),(15,0)])) (.node (.leaf (2,624432,244,[(7,1),(8,1),(4,0),(34,0),(58,0),(36,1)])) (.leaf (2,330544,242,[(47,0),(8,1),(0,1)]))))) (.node (.node (.leaf (2,330544,230,[(32,0),(0,1),(7,1),(3,1),(35,0),(36,1)])) (.leaf (2,592688,242,[(7,1),(32,0),(3,1),(48,0),(35,0),(34,0),(36,1)]))) (.node (.leaf (2,854832,226,[(8,1),(4,2),(73,0)])) (.node (.leaf (2,854832,230,[(26,0),(38,1),(35,0),(36,1)])) (.leaf (2,84784,242,[(0,1),(7,1),(32,0),(36,1),(13,1),(3,1),(4,0)]))))))) (.node (.node (.node (.node (.leaf (2,346928,242,[(71,0),(3,3),(47,0)])) (.leaf (2,346928,214,[(26,0),(0,1)]))) (.node (.leaf (2,346928,246,[(48,0),(26,0),(0,1),(43,0),(36,1)])) (.node (.leaf (2,609072,242,[(34,0),(0,1),(7,1),(3,1)])) (.leaf (2,871216,210,[(47,0),(41,0),(40,0),(3,3)]))))) (.node (.node (.leaf (2,871216,242,[(47,0),(5,1),(4,0)])) (.leaf (2,871216,214,[(26,0),(0,1)]))) (.node (.leaf (2,871216,246,[(26,0),(0,1),(36,1),(35,0),(34,0)])) (.node (.leaf (2,363312,242,[(32,0),(47,0),(40,0),(8,3),(51,0),(34,0),(3,1)])) (.leaf (2,363312,182,[(44,0),(17,0),(21,0)])))))) (.node (.node (.node (.leaf (2,625456,242,[(7,1),(0,1),(4,0),(51,0),(3,1),(35,0),(34,0)])) (.leaf (2,86832,230,[(51,0),(8,1),(0,1)]))) (.node (.leaf (2,348976,246,[(47,0),(8,1),(0,1),(23,0),(36,1),(12,0)])) (.node (.leaf (2,873264,230,[(48,0),(5,1)])) (.leaf (2,873264,246,[(48,0),(8,1),(5,1),(73,0),(0,1)]))))) (.node (.node (.leaf (2,365360,230,[(32,0),(56,0),(40,0),(51,0),(34,0),(19,0)])) (.node (.leaf (2,365360,246,[(47,0),(56,0),(0,1),(27,0)])) (.leaf (2,627504,230,[(0,1),(8,1),(4,0),(51,0),(34,0),(73,0)])))) (.node (.leaf (2,366384,214,[(32,0),(47,0),(40,0),(8,3),(51,0),(27,0)])) (.node (.leaf (2,366384,182,[(73,0),(35,0)])) (.leaf (2,366384,246,[(51,0),(32,0),(34,0),(39,1),(27,1),(13,3),(3,3),(58,0),(35,0),(73,0)])))))))) (.node (.node (.node (.node (.node (.leaf (2,628528,214,[(32,0),(47,0),(40,0),(8,3),(34,0)])) (.leaf (2,628528,246,[(47,0),(5,1),(32,0),(34,0),(12,0)]))) (.node (.leaf (2,558896,248,[(41,0),(8,1)])) (.node (.leaf (2,313136,244,[(32,0),(47,0),(18,0),(34,0),(20,0)])) (.leaf (2,313136,246,[(41,0),(40,0),(8,1),(7,1),(4,0),(5,0)]))))) (.node (.node (.leaf (2,575280,244,[(7,1),(8,1),(4,0),(34,0),(58,0),(36,1)])) (.leaf (2,870192,220,[(47,0),(32,2),(36,0)]))) (.node (.leaf (2,362288,188,[(32,0),(47,0),(6,0),(39,0),(4,0),(20,0),(36,0)])) (.node (.leaf (2,362288,190,[(41,0),(6,0),(15,0),(32,0)])) (.leaf (2,314160,242,[(32,0),(47,0),(40,0),(8,3),(24,0),(34,0),(3,1)])))))) (.node (.node (.node (.leaf (2,576304,242,[(7,1),(0,1),(4,0),(24,0),(3,1),(35,0),(34,0),(36,1)])) (.leaf (2,854832,234,[(8,1),(4,2),(73,0)]))) (.node (.leaf (2,871216,218,[(41,0),(47,0)])) (.node (.leaf (2,363312,186,[(32,0),(47,0),(40,0),(13,3),(17,0),(4,0),(34,0)])) (.leaf (2,331568,230,[(32,0),(56,0),(40,0),(24,0),(36,1),(34,0)]))))) (.node (.node (.leaf (2,331568,246,[(47,0),(56,0),(0,1),(27,0),(14,0)])) (.leaf (2,855856,230,[(0,1),(8,1),(4,0),(34,0),(24,0),(73,0),(36,1)]))) (.node (.leaf (2,347952,214,[(32,0),(18,0),(40,0),(51,0),(3,3)])) (.node (.leaf (2,347952,246,[(41,0),(32,0),(34,0),(27,1),(51,0),(3,3),(13,2),(36,0)])) (.leaf (2,872240,214,[(32,0),(18,0),(40,0),(8,3),(34,0)]))))))) (.node (.node (.node (.node (.leaf (2,872240,246,[(5,1),(32,0),(34,0),(36,1),(18,0),(3,3)])) (.leaf (2,365360,174,[(32,0),(56,0),(40,0),(27,0),(51,0)]))) (.node (.leaf (2,365360,190,[(47,0),(56,0),(0,1),(27,0)])) (.node (.leaf (2,366384,158,[(32,0),(27,0),(51,0),(39,0),(3,3),(2,0)])) (.leaf (2,366384,190,[(41,0),(73,0),(32,0),(51,0),(58,0),(35,0)]))))) (.node (.node (.leaf (2,628528,158,[(32,0),(5,0),(3,3),(47,0),(4,0),(36,0)])) (.leaf (2,836928,244,[(47,0),(0,2),(16,2)]))) (.node (.leaf (2,869696,220,[(47,0),(0,2)])) (.node (.leaf (2,886080,188,[(0,2),(14,0),(18,0),(40,0),(36,0)])) (.leaf (2,101696,182,[(8,2),(4,0),(0,2),(27,0),(51,0)])))))) (.node (.node (.node (.leaf (2,888128,182,[(0,2),(8,2),(14,0),(27,0),(24,0)])) (.leaf (2,888128,190,[(47,0),(0,2),(29,0),(8,2)]))) (.node (.leaf (2,313152,236,[(53,0),(0,2),(13,1),(36,1)])) (.node (.leaf (2,870208,236,[(0,2),(36,1),(53,0)])) (.leaf (2,85824,230,[(0,2),(36,1),(8,2)]))))) (.node (.node (.leaf (2,85824,238,[(0,2),(8,2),(4,1),(36,1),(73,0),(53,0)])) (.node (.leaf (2,347968,230,[(73,0),(0,2)])) (.leaf (2,347968,238,[(73,0),(53,0),(0,2),(8,2),(36,1),(4,1),(51,0)])))) (.node (.leaf (2,610112,198,[(8,2),(0,2)])) (.node (.leaf (2,610112,230,[(73,0),(0,2),(8,2)])) (.leaf (2,610112,206,[(8,2),(4,1),(0,2)])))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf (2,610112,238,[(73,0),(0,2),(4,1),(8,2),(36,1),(53,0)])) (.leaf (2,330017,233,[(9,0),(16,3),(17,0),(7,0),(0,0)]))) (.node (.leaf (2,593185,229,[(32,0),(16,3),(7,2),(27,0)])) (.node (.leaf (2,347425,245,[(17,0),(35,0),(0,2),(16,3),(7,2),(13,2),(32,0)])) (.leaf (2,609569,213,[(32,0),(16,3),(7,2),(0,2)]))))) (.node (.node (.leaf (2,609569,245,[(17,0),(35,0),(0,2),(16,3),(7,2),(13,2),(36,0)])) (.leaf (2,871713,213,[(17,0),(0,2),(16,3)]))) (.node (.leaf (2,363809,189,[(17,0),(0,2),(29,0),(16,3),(32,0),(7,0)])) (.node (.leaf (2,625953,181,[(17,0),(16,3),(38,2),(0,2)])) (.leaf (2,348449,237,[(61,0),(16,3),(7,2),(9,2),(17,0),(35,0),(3,1)])))))) (.node (.node (.node (.leaf (2,872737,205,[(17,0),(16,3)])) (.leaf (2,365857,189,[(27,0),(0,2),(16,3),(34,0),(17,0),(5,0),(7,0)]))) (.node (.leaf (2,628001,157,[(0,2),(16,3),(36,0),(24,0),(29,0)])) (.node (.leaf (2,331297,233,[(64,0),(16,3)])) (.leaf (2,347681,241,[(58,0),(16,3)]))))) (.node (.node (.leaf (2,347681,249,[(41,0),(58,0),(16,3),(8,2),(51,0)])) (.leaf (2,609825,241,[(58,0),(16,3)]))) (.node (.leaf (2,609825,249,[(58,0),(64,0),(16,3),(4,1),(5,0)])) (.node (.leaf (2,313889,249,[(17,0),(32,0),(16,3),(8,2),(38,0)])) (.leaf (2,838177,241,[(17,0),(8,2),(16,3)]))))))) (.node (.node (.node (.node (.leaf (2,838177,249,[(9,0),(8,2),(17,0),(16,3),(4,1),(51,0)])) (.leaf (2,346657,249,[(9,0),(8,2),(5,0),(16,3),(36,0),(32,0),(43,0)]))) (.node (.leaf (2,870945,217,[(9,0),(16,3),(8,2)])) (.node (.leaf (2,593441,229,[(32,0),(13,2),(16,3),(27,0)])) (.leaf (2,347681,245,[(35,0),(8,2),(16,3),(5,0),(38,2),(43,0),(32,0)]))))) (.node (.node (.leaf (2,609825,213,[(32,0),(8,2),(16,3)])) (.leaf (2,609825,245,[(8,2),(32,0),(16,3),(5,0),(38,2),(43,0),(36,0)]))) (.node (.leaf (2,871969,213,[(5,0),(16,3),(8,2),(38,2),(3,2)])) (.node (.leaf (2,364065,189,[(24,0),(32,0),(8,0),(16,3),(29,0)])) (.leaf (2,626209,181,[(16,3),(38,2),(4,0),(8,0),(5,0),(34,0)])))))) (.node (.node (.node (.leaf (2,348705,237,[(61,0),(16,3),(35,0),(34,0),(9,2),(5,0),(17,0),(24,0),(3,1)])) (.leaf (2,872993,205,[(17,0),(16,3),(38,2)]))) (.node (.leaf (2,366113,189,[(17,0),(34,0),(16,3),(8,0),(5,0),(38,2)])) (.node (.leaf (2,628257,157,[(16,3),(38,2),(36,0),(8,0),(51,0),(24,0),(29,0)])) (.leaf (2,360497,188,[(10,0),(7,0),(8,0),(5,0),(34,0),(36,0)]))))) (.node (.node (.leaf (2,870449,217,[(8,2),(16,3),(4,2),(5,0)])) (.node (.leaf (2,625713,181,[(16,3),(7,0),(4,0),(8,0),(5,0),(39,0)])) (.leaf (2,365617,157,[(16,3),(7,0),(8,0),(4,0),(5,0),(12,0)])))) (.node (.leaf (2,365617,189,[(5,0),(12,0),(7,0),(16,3),(4,0),(8,0)])) (.node (.leaf (2,627761,157,[(16,3),(8,0),(7,0),(4,0),(36,0)])) (.leaf (2,885041,188,[(18,0),(20,0),(0,3),(9,0),(19,0),(36,0),(13,2)])))))))) (.node (.node (.node (.node (.node (.leaf (2,885041,252,[(20,0),(9,0),(19,0),(18,0),(24,0),(13,2),(16,1)])) (.leaf (2,313649,245,[(24,0),(0,1),(16,3),(18,0),(43,0),(32,0),(4,0)]))) (.node (.leaf (2,837937,241,[(47,0),(16,3),(18,0),(4,0),(3,3),(34,0),(20,0),(7,0)])) (.node (.leaf (2,837937,245,[(50,0),(26,0),(16,3),(9,0),(34,0),(17,0),(7,0)])) (.leaf (2,346417,249,[(53,0),(34,0),(16,3),(24,0),(13,2),(38,1)]))))) (.node (.node (.leaf (2,608561,217,[(50,0),(16,3),(13,2)])) (.leaf (2,608561,249,[(24,0),(0,1),(16,3),(32,0),(13,2),(4,0),(18,0),(36,0)]))) (.node (.leaf (2,100657,249,[(20,0),(18,0),(24,0),(16,3),(0,1),(4,0)])) (.node (.leaf (2,887089,185,[(50,0),(16,3),(17,0),(18,0),(4,2)])) (.leaf (2,887089,249,[(50,0),(16,3),(24,0),(20,0),(13,2),(4,0)])))))) (.node (.node (.node (.leaf (2,887089,189,[(17,0),(45,0),(16,3),(9,0),(32,0),(36,0)])) (.leaf (2,348465,237,[(24,0),(34,0),(16,3),(9,2),(38,2),(17,0),(4,0),(3,1)]))) (.node (.leaf (2,610609,205,[(53,0),(16,3),(0,1),(9,0)])) (.node (.leaf (2,610609,237,[(24,0),(0,1),(16,3),(36,0),(12,0),(9,0)])) (.leaf (2,102705,237,[(18,0),(0,1),(16,3),(24,0),(20,0)]))))) (.node (.node (.leaf (2,364849,189,[(47,0),(45,0),(16,3),(36,0)])) (.leaf (2,889137,173,[(53,0),(16,3),(32,2),(9,0),(24,0),(12,0),(27,0)]))) (.node (.leaf (2,889137,237,[(53,0),(16,3),(24,0),(8,0),(20,0)])) (.node (.leaf (2,889137,189,[(47,0),(53,0),(16,3),(45,0)])) (.leaf (2,103729,221,[(56,0),(9,0),(16,3),(20,0),(38,1),(3,1)]))))))) (.node (.node (.node (.node (.leaf (2,365873,189,[(35,0),(16,3),(24,0),(27,0),(5,0),(38,0),(3,0)])) (.leaf (2,628017,157,[(50,0),(16,3),(3,0)]))) (.node (.leaf (2,890161,157,[(16,3),(9,0),(32,2),(0,3),(35,0),(24,0),(3,0)])) (.node (.leaf (2,890161,221,[(56,0),(9,0),(16,3),(20,0),(24,0),(13,2)])) (.leaf (2,890161,189,[(35,0),(24,0),(16,3),(27,0)]))))) (.node (.node (.leaf (2,885041,182,[(7,2),(8,2),(39,0),(5,2),(46,0),(20,0)])) (.leaf (2,885041,246,[(41,0),(46,0),(8,2),(7,2),(2,0)]))) (.node (.leaf (2,886065,245,[(26,0),(39,0),(8,0),(16,3),(7,0)])) (.node (.leaf (2,870705,211,[(26,0),(16,3)])) (.leaf (2,887089,179,[(8,2),(16,3),(17,0),(39,0),(15,0)])))))) (.node (.node (.node (.leaf (2,887089,243,[(25,0),(39,0),(8,2),(20,0)])) (.leaf (2,872753,199,[(7,2),(16,3),(5,0),(25,0),(2,2),(20,0)]))) (.node (.leaf (2,889137,167,[(7,2),(16,3),(6,0),(31,0)])) (.node (.leaf (2,889137,231,[(25,0),(41,0),(6,0),(20,0)])) (.leaf (2,103729,215,[(39,0),(8,2),(16,3),(7,2),(20,0)]))))) (.node (.node (.leaf (2,365873,183,[(7,2),(12,0),(8,2),(16,3),(5,0)])) (.node (.leaf (2,890161,151,[(8,2),(16,3),(7,2)])) (.leaf (2,890161,215,[(26,0),(20,0),(2,0),(8,2)])))) (.node (.leaf (2,890161,183,[(7,2),(12,0),(8,2),(16,3),(5,0)])) (.node (.leaf (2,885041,190,[(41,0),(8,2),(7,2),(16,1),(36,0)])) (.leaf (2,853297,237,[(25,0),(53,0),(39,0),(4,0),(7,0)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (2,345393,221,[(26,0),(8,0),(40,0),(9,0),(16,3),(7,0),(4,0),(18,0)])) (.leaf (2,345393,253,[(41,0),(39,0),(24,0),(7,0),(5,0),(16,3),(34,0),(8,0)]))) (.node (.leaf (2,869681,221,[(24,0),(7,0),(8,0),(16,3),(29,0),(40,0),(4,0)])) (.node (.leaf (2,313649,243,[(26,0),(8,2),(24,0),(39,0),(16,3),(32,0),(13,2)])) (.leaf (2,837937,243,[(41,0),(40,0),(8,2),(16,3)]))))) (.node (.node (.leaf (2,870705,219,[(41,0),(26,0),(8,2),(16,3),(4,2),(24,0),(2,0)])) (.leaf (2,887089,187,[(41,0),(8,2),(16,3),(4,0)]))) (.node (.leaf (2,331057,231,[(24,0),(7,2),(16,3),(26,0),(13,2),(4,0),(39,0)])) (.node (.leaf (2,593201,231,[(41,0),(7,2),(16,3),(26,0),(20,0),(40,0),(4,0)])) (.leaf (2,609585,215,[(39,0),(8,2),(7,2),(16,3),(26,0),(20,0)])))))) (.node (.node (.node (.leaf (2,871729,215,[(53,0),(7,2),(16,3),(4,0)])) (.leaf (2,872753,207,[(24,0),(7,2),(16,3),(20,0),(25,0)]))) (.node (.leaf (2,364849,175,[(40,0),(7,2),(24,0),(16,3),(2,0),(8,0),(36,0)])) (.node (.leaf (2,889137,175,[(41,0),(7,2),(16,3),(20,0),(4,0)])) (.leaf (2,103729,159,[(20,0),(8,2),(7,2),(16,3),(4,0)]))))) (.node (.node (.leaf (2,365873,159,[(40,0),(8,2),(7,2),(16,3),(29,0),(5,0)])) (.leaf (2,365873,191,[(41,0),(29,0),(27,0),(2,0),(8,2),(16,3),(7,2),(5,0),(51,0),(20,0)]))) (.node (.leaf (2,628017,159,[(40,0),(7,2),(8,2),(16,3)])) (.node (.leaf (2,890161,159,[(20,0),(8,2),(16,3),(7,2),(4,0)])) (.leaf (2,890161,191,[(24,0),(35,0),(20,0),(39,0),(8,2),(16,3),(5,0),(2,0)]))))))) (.node (.node (.node (.node (.leaf (2,838193,241,[(8,2),(16,3),(4,0),(34,0),(5,2),(36,2),(58,0)])) (.leaf (2,593457,229,[(7,2),(16,3),(4,0),(27,0)]))) (.node (.leaf (2,347697,245,[(58,0),(7,2),(16,3),(8,2),(5,0),(27,0),(36,0),(4,0)])) (.node (.leaf (2,609841,213,[(7,2),(16,3),(8,2),(4,0)])) (.leaf (2,609841,245,[(7,2),(16,3),(8,2),(4,0),(5,0),(27,0),(36,0)]))))) (.node (.node (.leaf (2,871985,213,[(5,0),(16,3),(7,2),(8,2),(3,2)])) (.leaf (2,364081,189,[(24,0),(7,0),(8,0),(16,3),(4,0),(29,0)]))) (.node (.leaf (2,348721,237,[(24,0),(34,0),(16,3),(7,2),(38,2),(3,1)])) (.node (.leaf (2,365105,173,[(8,0),(16,3),(7,0),(27,0),(29,0),(4,2),(12,0)])) (.leaf (2,366129,189,[(27,0),(5,0),(7,0),(16,3),(8,0),(29,0),(12,0)])))))) (.node (.node (.node (.leaf (2,628273,157,[(16,3),(7,0),(36,0),(8,0),(29,0),(4,2)])) (.leaf (2,361265,244,[(10,0),(32,0),(47,0),(39,0),(0,3)]))) (.node (.leaf (2,330545,241,[(47,0),(16,3),(38,1)])) (.node (.leaf (2,330545,229,[(32,0),(16,3),(0,1),(36,1),(39,0)])) (.leaf (2,592689,225,[(32,0),(16,3)]))))) (.node (.node (.leaf (2,592689,241,[(47,0),(16,3)])) (.node (.leaf (2,854833,229,[(26,0),(16,3),(32,0),(39,0),(36,1)])) (.leaf (2,871217,209,[(47,0),(16,3)])))) (.node (.leaf (2,871217,241,[(47,0),(16,3)])) (.node (.leaf (2,871217,213,[(26,0),(0,1),(16,3),(32,0)])) (.leaf (2,871217,245,[(26,0),(0,1),(36,1),(54,0),(16,3)])))))))) (.node (.node (.node (.node (.node (.leaf (2,363313,241,[(32,0),(16,3),(47,0),(51,0),(39,0)])) (.leaf (2,363313,181,[(17,0),(16,3),(45,0)]))) (.node (.leaf (2,625457,241,[(0,1),(16,3),(51,0),(4,0),(38,1),(39,0)])) (.node (.leaf (2,86833,229,[(51,0),(16,3),(0,1),(38,1),(4,0)])) (.leaf (2,348977,229,[(54,0),(16,3)]))))) (.node (.node (.leaf (2,348977,245,[(47,0),(0,1),(16,3),(23,0),(36,1)])) (.leaf (2,611121,229,[(39,0),(16,3),(0,1),(38,1)]))) (.node (.leaf (2,873265,229,[(48,0),(16,3)])) (.node (.leaf (2,873265,245,[(48,0),(16,3),(0,1),(36,1),(39,0)])) (.leaf (2,365361,229,[(32,0),(16,3),(51,0),(39,0),(22,0),(8,0)])))))) (.node (.node (.node (.leaf (2,365361,245,[(47,0),(0,1),(16,3),(32,0),(27,0)])) (.leaf (2,627505,229,[(0,1),(16,3),(51,0),(4,0),(38,1),(39,0)]))) (.node (.leaf (2,366385,213,[(32,0),(16,3),(47,0),(51,0),(27,0)])) (.node (.leaf (2,366385,245,[(51,0),(39,0),(32,0),(16,3),(27,1)])) (.leaf (2,628529,213,[(32,0),(16,3),(47,0),(39,0),(0,3)]))))) (.node (.node (.leaf (2,628529,245,[(47,0),(32,0),(16,3),(36,1),(39,0)])) (.node (.leaf (2,361265,188,[(32,0),(10,0),(47,0),(0,3),(34,0),(36,0)])) (.leaf (2,314161,241,[(32,0),(16,3),(47,0),(24,0),(34,0)])))) (.node (.leaf (2,576305,241,[(0,1),(16,3),(4,0),(38,1),(34,0),(24,0),(36,1)])) (.node (.leaf (2,363313,185,[(32,0),(16,3),(47,0),(17,0),(34,0)])) (.leaf (2,331569,229,[(32,0),(16,3),(24,0),(36,1),(39,0),(8,0)]))))))) (.node (.node (.node (.node (.leaf (2,331569,245,[(47,0),(0,1),(16,3),(4,0),(27,0)])) (.leaf (2,855857,229,[(0,1),(16,3),(4,0),(24,0),(38,1),(39,0),(36,1)]))) (.node (.leaf (2,347953,245,[(51,0),(32,0),(16,3),(39,0),(27,1),(36,0)])) (.node (.leaf (2,872241,213,[(32,0),(16,3),(18,0),(34,0),(0,3)])) (.leaf (2,872241,245,[(34,0),(36,1),(32,0),(16,3),(18,0),(3,3)]))))) (.node (.node (.leaf (2,611121,205,[(0,1),(16,3),(4,2)])) (.leaf (2,365361,173,[(32,0),(16,3),(27,0),(12,0),(51,0),(8,0)]))) (.node (.leaf (2,365361,189,[(47,0),(0,1),(16,3),(36,0)])) (.node (.leaf (2,366385,157,[(32,0),(16,3),(27,0),(51,0),(0,3)])) (.leaf (2,366385,189,[(51,0),(27,0),(32,0),(16,3),(12,0)])))))) (.node (.node (.node (.leaf (2,628529,157,[(32,0),(16,3),(36,0),(47,0),(0,3),(3,0)])) (.leaf (2,361265,246,[(39,0),(22,0),(7,2),(8,2),(16,3),(10,0)]))) (.node (.leaf (2,329521,229,[(39,0),(16,3),(8,0),(7,0)])) (.node (.leaf (2,853809,229,[(26,0),(39,0),(16,3),(7,0)])) (.leaf (2,345905,245,[(5,0),(2,0),(7,0),(16,3),(8,0)]))))) (.node (.node (.leaf (2,870193,245,[(39,0),(8,0),(16,3),(7,0),(36,1)])) (.node (.leaf (2,363313,243,[(64,0),(16,3),(8,2),(39,0),(32,0),(38,1)])) (.leaf (2,873265,199,[(7,2),(16,3),(5,0),(25,0),(64,0)])))) (.node (.leaf (2,365361,231,[(64,0),(6,0),(7,2),(16,3),(39,0),(3,1)])) (.node (.leaf (2,889649,167,[(7,2),(2,0),(16,3)])) (.leaf (2,366385,215,[(26,0),(22,0),(8,2),(2,0),(36,0)]))))))))))) (.node (.node (.node (.node (.node (.node (.node (.node (.leaf (2,366385,183,[(27,0),(7,2),(16,3),(8,2),(5,0)])) (.leaf (2,628529,151,[(8,2),(16,3),(36,0),(7,2)]))) (.node (.leaf (2,628529,215,[(2,0),(8,2),(16,3),(7,2),(5,0)])) (.node (.leaf (2,890673,183,[(8,2),(2,0),(5,0),(16,3),(7,2)])) (.leaf (2,361265,190,[(22,0),(32,0),(8,2),(10,0),(34,0),(51,0),(16,3)]))))) (.node (.node (.leaf (2,329521,237,[(25,0),(8,0),(39,0),(4,2),(16,3),(26,0)])) (.leaf (2,853809,237,[(26,0),(4,2),(39,0),(16,3),(7,0)]))) (.node (.leaf (2,870193,221,[(26,0),(4,2),(8,0),(16,3),(7,0),(36,0)])) (.node (.leaf (2,314161,243,[(26,0),(64,0),(32,0),(8,2),(16,3),(7,0)])) (.leaf (2,363313,187,[(64,0),(16,3),(8,2),(32,0),(38,0)])))))) (.node (.node (.node (.leaf (2,331569,231,[(64,0),(16,3),(7,2),(26,0),(32,0),(39,0),(8,0)])) (.leaf (2,872241,215,[(8,2),(32,0),(16,3),(5,0),(4,0)]))) (.node (.leaf (2,873265,207,[(64,0),(16,3),(7,2),(25,0)])) (.node (.leaf (2,365361,175,[(64,0),(16,3),(32,0),(3,0)])) (.leaf (2,366385,159,[(22,0),(32,0),(8,2),(16,3),(7,2),(36,0)]))))) (.node (.node (.leaf (2,366385,191,[(51,0),(27,0),(22,0),(8,2),(32,0),(16,3),(5,0),(39,0)])) (.leaf (2,628529,159,[(7,2),(16,3),(8,2),(4,0),(36,0),(32,0)]))) (.node (.leaf (2,837953,241,[(47,0),(16,3),(8,2)])) (.node (.leaf (2,593217,237,[(27,0),(8,0),(16,3),(0,0),(4,1)])) (.leaf (2,348481,237,[(47,0),(0,0),(16,3),(8,0),(18,0)]))))))) (.node (.node (.node (.node (.leaf (2,365889,189,[(47,0),(0,2),(16,3),(5,0),(4,0),(8,0)])) (.leaf (2,345409,237,[(27,0),(7,0),(40,0),(16,3),(8,0),(5,0)]))) (.node (.leaf (2,313665,235,[(26,0),(40,0),(8,2),(39,2),(16,3),(38,1),(36,1)])) (.node (.leaf (2,837953,227,[(40,0),(16,3),(39,2),(8,2)])) (.leaf (2,347457,207,[(39,0),(22,0),(16,3),(7,2),(8,2),(26,0),(40,0),(3,2),(5,0)]))))) (.node (.node (.leaf (2,871745,199,[(5,0),(16,3),(8,2),(7,2),(3,2)])) (.leaf (2,871745,207,[(40,0),(22,0),(7,2),(16,3),(8,2),(3,2),(4,0)]))) (.node (.leaf (2,365889,175,[(34,0),(7,2),(16,3),(5,0),(8,0)])) (.node (.leaf (2,313921,233,[(64,0),(16,3),(4,0)])) (.leaf (2,347713,237,[(41,0),(7,2),(16,3),(51,0),(22,0),(12,0)])))))) (.node (.node (.node (.leaf (2,609857,237,[(64,0),(7,2),(16,3),(4,1),(5,0),(12,0)])) (.leaf (2,626241,165,[(16,3),(7,0),(4,0)]))) (.node (.leaf (2,366145,141,[(16,3),(7,0),(5,0),(12,0)])) (.node (.leaf (2,366145,173,[(34,0),(16,3),(7,0),(5,0)])) (.leaf (2,838209,241,[(47,0),(16,3),(3,2)]))))) (.node (.node (.leaf (2,331329,237,[(47,0),(16,3),(7,2),(4,0),(3,0),(5,0)])) (.node (.leaf (2,593473,237,[(41,0),(7,2),(16,3),(34,0),(27,0)])) (.leaf (2,364097,189,[(47,0),(7,0),(29,0),(3,2),(16,3)])))) (.node (.leaf (2,626241,181,[(16,3),(7,0),(4,0),(3,2),(5,0),(34,0)])) (.node (.leaf (2,348737,237,[(18,0),(7,2),(16,3),(5,0),(34,0),(38,2),(36,0),(3,0)])) (.leaf (2,366145,157,[(3,2),(16,3),(7,0),(18,0),(5,0),(34,0)])))))))) (.node (.node (.node (.node (.node (.leaf (2,366145,189,[(34,0),(5,0),(7,0),(16,3),(3,2)])) (.leaf (2,628289,157,[(16,3),(7,0),(36,0),(3,2),(51,0),(24,0),(29,0)]))) (.node (.leaf (2,85825,229,[(0,2),(36,1),(16,3)])) (.node (.leaf (2,85825,237,[(0,2),(36,1),(16,3),(4,1),(34,0),(53,0)])) (.leaf (2,347969,205,[(53,0),(16,3),(4,0)]))))) (.node (.node (.leaf (2,347969,237,[(53,0),(16,3),(39,0),(51,0),(0,2),(36,1)])) (.leaf (2,610113,237,[(39,0),(16,3),(0,2),(4,1),(36,1),(12,0),(53,0)]))) (.node (.leaf (2,872257,197,[(0,2),(16,3)])) (.node (.leaf (2,872257,229,[(0,2),(36,1),(16,3)])) (.leaf (2,872257,205,[(53,0),(16,3)])))))) (.node (.node (.node (.leaf (2,872257,237,[(53,0),(16,3),(36,1),(34,0)])) (.leaf (2,366401,173,[(34,0),(16,3),(0,0)]))) (.node (.leaf (2,345921,237,[(40,0),(5,0),(7,0),(16,3),(34,0)])) (.node (.leaf (2,870209,237,[(40,0),(7,0),(39,0),(16,3),(36,1),(3,2)])) (.leaf (2,314177,235,[(26,0),(40,0),(16,3),(39,2),(24,0),(13,2),(38,1),(34,0),(36,1),(32,0)]))))) (.node (.node (.leaf (2,838465,227,[(40,0),(16,3),(39,2),(13,2),(3,2)])) (.leaf (2,347969,207,[(40,0),(22,0),(7,2),(16,3),(26,0),(4,0),(5,0)]))) (.node (.leaf (2,872257,199,[(5,0),(16,3),(3,2),(7,2)])) (.node (.leaf (2,872257,207,[(53,0),(40,0),(7,2),(16,3),(4,0)])) (.leaf (2,364353,175,[(40,0),(24,0),(7,2),(16,3),(13,2),(3,0)]))))))) (.node (.node (.node (.node (.leaf (2,626497,167,[(7,2),(16,3),(4,0),(34,0)])) (.leaf (2,366401,175,[(39,0),(7,2),(34,0),(16,3),(5,0)]))) (.node (.leaf (2,628545,143,[(7,2),(16,3),(36,0),(24,0)])) (.node (.leaf (2,837713,241,[(17,0),(8,2),(16,3)])) (.leaf (2,347217,221,[(51,0),(16,3),(7,2),(8,2),(24,0),(38,2),(4,0),(3,2),(18,0)]))))) (.node (.node (.leaf (2,363601,189,[(51,0),(29,0),(8,0),(7,0),(16,3)])) (.leaf (2,625745,181,[(16,3),(8,0),(7,0),(36,0),(4,0)]))) (.node (.leaf (2,364625,173,[(16,3),(8,0),(7,0),(36,0),(51,0),(18,0)])) (.node (.leaf (2,627793,157,[(16,3),(7,0),(36,0),(8,0),(40,0),(24,0),(29,0)])) (.leaf (2,885073,188,[(5,0),(0,3),(27,0),(78,0),(43,0),(29,0),(16,0)])))))) (.node (.node (.node (.leaf (2,313681,249,[(24,0),(34,0),(16,3),(27,2),(18,0),(32,0),(27,0),(36,0)])) (.leaf (2,313681,245,[(26,0),(78,0),(0,1),(38,1),(17,0),(27,0)]))) (.node (.leaf (2,575825,249,[(24,0),(34,0),(16,3),(0,1),(5,0),(18,0)])) (.node (.leaf (2,837969,245,[(78,0),(0,1),(26,0),(5,0),(17,0),(38,1)])) (.leaf (2,887121,185,[(5,0),(16,3),(9,0),(27,0),(3,3)]))))) (.node (.node (.leaf (2,887121,189,[(1,0),(9,0),(16,3),(35,0),(5,0),(43,0)])) (.node (.leaf (2,331089,237,[(27,0),(16,3),(24,0),(9,1),(12,0),(9,0),(38,1),(17,0),(5,0)])) (.leaf (2,593233,229,[(1,0),(16,3),(13,2)])))) (.node (.leaf (2,855377,237,[(24,0),(0,1),(16,3),(5,2),(12,0),(9,0),(38,1),(4,0),(13,2),(5,0)])) (.node (.leaf (2,347473,221,[(27,0),(35,0),(16,3),(29,1),(9,0),(5,0),(4,1),(4,0),(18,0)])) (.leaf (2,871761,213,[(5,0),(16,3),(0,3),(17,0),(38,3),(26,0),(3,2)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (2,871761,221,[(69,0),(5,0),(16,3),(17,0),(34,0),(38,3),(4,0)])) (.leaf (2,888145,181,[(5,0),(16,3),(0,3),(9,0),(43,0)]))) (.node (.leaf (2,888145,189,[(18,0),(34,0),(9,0),(16,3),(5,0)])) (.node (.leaf (2,610641,205,[(34,0),(16,3),(0,1),(13,0)])) (.leaf (2,889169,173,[(5,0),(16,3),(18,0),(34,0),(78,0),(43,0),(13,0)]))))) (.node (.node (.leaf (2,889169,189,[(18,0),(45,0),(16,3),(5,0)])) (.leaf (2,885073,158,[(7,2),(5,0),(8,2),(40,0),(29,0)]))) (.node (.leaf (2,886097,221,[(40,0),(8,0),(16,3),(7,0),(5,0)])) (.node (.leaf (2,837969,211,[(40,0),(16,3),(8,2)])) (.leaf (2,887121,155,[(8,2),(16,3),(9,0),(40,0),(5,0)])))))) (.node (.node (.node (.leaf (2,331089,207,[(40,0),(22,0),(16,3),(7,2),(26,0),(9,0),(5,0)])) (.leaf (2,888145,151,[(8,2),(16,3),(5,0),(7,2)]))) (.node (.leaf (2,888145,159,[(40,0),(7,2),(29,0),(8,2),(16,3)])) (.node (.leaf (2,889169,143,[(7,2),(16,3),(5,0),(18,0)])) (.leaf (2,837969,243,[(40,0),(5,2),(8,2),(16,3),(12,0),(34,0),(36,2)]))))) (.node (.node (.leaf (2,593233,231,[(40,0),(7,2),(16,3),(25,0)])) (.leaf (2,347473,223,[(41,0),(39,0),(7,2),(22,0),(16,3),(8,2),(25,0),(36,0)]))) (.node (.leaf (2,609617,215,[(7,2),(12,0),(8,2),(16,3),(5,0),(36,0)])) (.node (.leaf (2,361041,156,[(8,0),(7,0),(28,0),(29,0)])) (.leaf (2,593489,197,[(7,2),(16,3)]))))))) (.node (.node (.node (.node (.leaf (2,593489,205,[(7,2),(4,1),(16,3)])) (.leaf (2,364113,157,[(29,0),(16,3),(7,0),(8,0)]))) (.node (.leaf (2,361041,188,[(8,0),(7,0),(67,0),(36,2),(28,0),(29,0),(16,0)])) (.node (.leaf (2,331345,237,[(24,0),(7,2),(16,3),(4,0),(36,0),(12,0)])) (.leaf (2,593489,229,[(27,0),(16,3),(7,2)]))))) (.node (.node (.leaf (2,85585,221,[(7,2),(4,1),(16,3),(8,2)])) (.leaf (2,347729,221,[(27,0),(16,3),(7,2),(22,0),(8,2),(38,2),(29,0),(4,0),(36,0),(3,2)]))) (.node (.leaf (2,609873,221,[(7,2),(4,1),(16,3),(8,2)])) (.node (.leaf (2,872017,213,[(8,2),(16,3),(7,2),(36,0),(3,2)])) (.leaf (2,872017,221,[(34,0),(16,3),(7,2),(8,2),(36,0),(38,2),(4,0),(3,2)])))))) (.node (.node (.node (.leaf (2,364113,189,[(24,0),(34,0),(7,0),(16,3),(29,0),(8,0)])) (.leaf (2,626257,181,[(16,3),(7,0),(4,0),(8,0),(36,2),(12,0)]))) (.node (.leaf (2,873041,205,[(7,2),(16,3),(36,0),(24,0),(4,1)])) (.node (.leaf (2,366161,189,[(27,0),(5,0),(7,0),(16,3),(8,0),(24,0)])) (.leaf (2,361297,220,[(49,0),(47,0),(17,0),(0,3),(38,1),(24,0)]))))) (.node (.node (.leaf (2,838481,209,[(47,0),(16,3),(3,3)])) (.node (.leaf (2,838481,217,[(47,0),(16,3)])) (.leaf (2,838481,213,[(17,0),(0,1),(16,3)])))) (.node (.leaf (2,838481,221,[(26,0),(0,1),(16,3),(50,0),(17,0)])) (.node (.leaf (2,363345,217,[(47,0),(16,3),(17,0),(36,0),(15,0),(24,0),(3,3),(7,0)])) (.leaf (2,363345,157,[(9,0),(16,3),(45,0)])))))))) (.node (.node (.node (.node (.node (.leaf (2,363345,221,[(48,0),(17,0),(45,0),(16,3),(36,0)])) (.leaf (2,625489,217,[(0,1),(16,3),(36,0),(24,0),(32,1),(50,0),(4,1)]))) (.node (.leaf (2,331601,221,[(72,0),(0,1),(16,3),(47,0),(29,0),(36,0)])) (.node (.leaf (2,593745,221,[(40,0),(0,1),(16,3),(53,0)])) (.leaf (2,364369,213,[(16,3),(47,0),(17,0),(36,0),(0,3),(24,0),(18,0)]))))) (.node (.node (.leaf (2,364369,157,[(50,0),(16,3)])) (.leaf (2,364369,221,[(48,0),(16,3),(24,0),(40,0),(50,0),(18,1),(3,3)]))) (.node (.leaf (2,626513,213,[(16,3),(47,0),(17,0),(36,0),(0,3),(24,0)])) (.node (.leaf (2,626513,221,[(47,0),(16,3),(32,1),(24,0),(29,0)])) (.leaf (2,365393,205,[(16,3),(17,0),(24,0),(36,0),(6,0),(38,3),(8,0),(40,0)])))))) (.node (.node (.node (.leaf (2,365393,221,[(47,0),(61,0),(45,0),(16,3),(18,0)])) (.leaf (2,627537,205,[(0,1),(16,3),(36,0),(24,0),(53,0)]))) (.node (.leaf (2,361297,188,[(49,0),(47,0),(17,0),(0,3),(36,0),(24,0)])) (.node (.leaf (2,363345,185,[(47,0),(16,3),(21,0),(36,0),(24,0),(55,0),(7,0)])) (.leaf (2,363345,189,[(48,0),(43,0),(45,0),(16,3)]))))) (.node (.node (.leaf (2,347985,221,[(48,0),(16,3),(24,0),(27,0),(51,0),(3,3),(3,2)])) (.node (.leaf (2,610129,213,[(16,3),(17,0),(27,0),(36,0),(0,3),(24,0)])) (.leaf (2,610129,221,[(32,1),(24,0),(16,3),(4,1),(27,0),(3,3),(3,2)])))) (.node (.leaf (2,364369,181,[(16,3),(36,0),(18,0),(17,0),(51,0),(0,3)])) (.node (.leaf (2,364369,189,[(48,0),(53,0),(16,3),(51,0),(36,0),(50,0)])) (.leaf (2,349009,221,[(47,0),(23,0),(16,3),(8,0),(18,0)]))))))) (.node (.node (.node (.node (.leaf (2,611153,205,[(0,1),(16,3),(36,0),(24,0),(53,0),(4,2)])) (.leaf (2,365393,173,[(23,0),(16,3),(17,0),(36,0),(18,0),(4,0),(8,0)]))) (.node (.leaf (2,365393,189,[(47,0),(45,0),(16,3),(61,0)])) (.node (.leaf (2,361297,222,[(58,0),(40,0),(7,2),(8,2),(16,1),(49,0)])) (.leaf (2,363345,219,[(58,0),(40,0),(16,3),(8,2),(15,0),(38,1)]))))) (.node (.node (.leaf (2,331601,207,[(40,0),(7,2),(16,3),(24,0),(26,0),(13,2)])) (.leaf (2,364369,215,[(58,0),(40,0),(7,2),(16,3),(8,2),(4,0)]))) (.node (.leaf (2,364369,159,[(40,0),(7,2),(8,2),(16,3),(29,0)])) (.node (.leaf (2,626513,151,[(8,2),(16,3),(4,0),(7,2)])) (.leaf (2,626513,215,[(40,0),(8,2),(16,3),(7,2)])))))) (.node (.node (.node (.leaf (2,365393,207,[(6,0),(7,2),(16,3),(40,0),(3,1)])) (.leaf (2,361297,190,[(58,0),(7,2),(49,0),(24,0),(51,0),(8,2),(16,3)]))) (.node (.leaf (2,363345,187,[(58,0),(16,3),(8,2),(24,0),(51,0),(36,0),(38,0)])) (.node (.leaf (2,593745,231,[(40,0),(7,2),(16,3),(25,0),(27,0)])) (.leaf (2,347985,223,[(58,0),(51,0),(39,0),(24,0),(8,2),(7,2),(16,3),(36,0),(12,0),(20,0)]))))) (.node (.node (.leaf (2,610129,215,[(39,0),(8,2),(16,3),(7,2)])) (.node (.leaf (2,364369,183,[(58,0),(16,3),(7,2),(8,2),(36,0),(4,0)])) (.leaf (2,364369,191,[(51,0),(29,0),(40,0),(7,2),(8,2),(16,3),(71,0),(36,0)])))) (.node (.leaf (2,626513,183,[(7,2),(16,3),(8,2),(36,0),(4,0)])) (.node (.leaf (2,365393,175,[(7,2),(16,3),(36,0),(24,0),(6,0),(51,0),(3,0),(31,0),(23,0),(40,0)])) (.leaf (2,362563,171,[(8,0),(16,3),(4,0),(0,0),(17,0),(36,0),(34,0)])))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf (2,625731,167,[(8,0),(16,3),(4,0),(0,0),(27,0)])) (.leaf (2,365635,175,[(51,0),(8,0),(16,3),(0,0),(12,0)]))) (.node (.leaf (2,627779,143,[(16,3),(8,0),(0,0),(4,0),(36,0)])) (.node (.leaf (2,885059,182,[(0,2),(8,2),(27,0),(56,0),(60,0),(25,0)])) (.leaf (2,885059,246,[(56,0),(0,2),(60,0),(27,0),(16,1)]))))) (.node (.node (.leaf (2,886083,181,[(0,2),(16,3),(11,0),(2,0)])) (.leaf (2,886083,245,[(27,0),(0,2),(16,3),(11,0)]))) (.node (.leaf (2,887107,179,[(8,2),(16,3),(27,0),(57,0),(43,0)])) (.node (.leaf (2,887107,243,[(56,0),(27,0),(16,3),(31,0),(38,1)])) (.leaf (2,889155,231,[(27,0),(8,0),(16,3),(0,0),(31,0)])))))) (.node (.node (.node (.leaf (2,103747,215,[(56,0),(16,3),(0,2),(8,2)])) (.leaf (2,365891,183,[(8,2),(12,0),(16,3),(0,2)]))) (.node (.leaf (2,628035,151,[(8,2),(16,3),(36,0),(0,2)])) (.node (.leaf (2,890179,151,[(8,2),(16,3),(0,2),(12,0)])) (.leaf (2,890179,215,[(56,0),(16,3),(0,2),(8,2)]))))) (.node (.node (.leaf (2,890179,183,[(12,0),(8,2),(16,3),(0,2)])) (.leaf (2,885059,174,[(72,0),(9,0),(25,0),(24,0),(13,3),(19,0),(2,0)]))) (.node (.leaf (2,885059,238,[(56,0),(24,0),(9,0),(3,2),(16,1)])) (.node (.leaf (2,99651,237,[(24,0),(7,1),(16,3),(4,0),(5,0)])) (.leaf (2,886083,173,[(16,3),(9,0),(32,2),(24,0),(39,0),(22,0),(12,0),(13,0)]))))))) (.node (.node (.node (.node (.leaf (2,886083,237,[(9,0),(24,0),(16,3),(22,0),(8,0),(4,0)])) (.leaf (2,886083,175,[(64,0),(39,0),(16,3),(45,0),(40,0)]))) (.node (.leaf (2,100675,235,[(56,0),(16,3),(24,0),(13,1),(3,2)])) (.node (.leaf (2,887107,171,[(72,0),(16,3),(64,0),(26,0),(2,0),(17,0)])) (.leaf (2,887107,235,[(56,0),(24,0),(16,3),(3,2)]))))) (.node (.node (.leaf (2,887107,175,[(17,0),(45,0),(16,3),(32,0),(43,0)])) (.leaf (2,103747,207,[(56,0),(16,3),(9,0),(22,0),(5,0)]))) (.node (.leaf (2,365891,175,[(39,0),(16,3),(35,0),(24,0),(13,0),(38,0)])) (.node (.leaf (2,890179,143,[(16,3),(39,0),(9,0),(24,0),(32,2),(12,0)])) (.leaf (2,890179,207,[(56,0),(9,0),(16,3),(22,0),(3,2)])))))) (.node (.node (.node (.leaf (2,890179,175,[(35,0),(24,0),(39,0),(16,3)])) (.leaf (2,885059,190,[(72,0),(0,2),(8,2),(24,0),(27,0),(16,1)]))) (.node (.leaf (2,886083,189,[(0,2),(16,3),(22,0),(24,0),(4,2),(27,0),(2,0),(8,0),(39,0),(4,0),(36,0)])) (.node (.leaf (2,886083,253,[(22,0),(56,0),(31,0),(0,2),(24,0),(4,2),(13,0)])) (.leaf (2,887107,187,[(56,0),(16,3),(8,2),(17,0),(27,0),(72,0),(4,0),(36,0)]))))) (.node (.node (.leaf (2,85315,215,[(56,0),(0,2),(16,3),(8,2)])) (.node (.leaf (2,85315,247,[(56,0),(0,2),(16,3),(8,2),(17,0),(4,0),(29,0),(73,0)])) (.leaf (2,347459,215,[(27,0),(0,2),(16,3),(8,2),(31,0),(4,0)])))) (.node (.leaf (2,609603,215,[(56,0),(16,3),(0,2),(8,2)])) (.node (.leaf (2,871747,215,[(8,2),(29,0),(16,3),(0,2),(4,0),(31,0)])) (.leaf (2,871747,247,[(69,0),(3,2),(27,0),(17,0),(4,0),(16,3),(8,2),(0,2),(29,0)])))))))) (.node (.node (.node (.node (.node (.leaf (2,348483,239,[(34,0),(24,0),(8,0),(0,0),(16,3),(39,0),(9,0),(36,0)])) (.leaf (2,872771,207,[(31,0),(0,0),(8,0),(16,3),(4,0),(29,2)]))) (.node (.leaf (2,103747,159,[(56,0),(0,2),(16,3),(8,2),(36,0),(5,0),(4,0)])) (.node (.leaf (2,365891,191,[(34,0),(24,0),(8,2),(16,3),(0,2),(31,0),(29,0),(39,0),(23,0),(51,0),(56,0)])) (.leaf (2,628035,159,[(8,2),(29,0),(0,2),(16,3),(31,0)]))))) (.node (.node (.leaf (2,890179,159,[(56,0),(0,2),(16,3),(8,2),(4,0)])) (.leaf (2,890179,191,[(34,0),(24,0),(8,2),(39,0),(27,0),(16,3),(0,2),(56,0),(36,0),(29,0)]))) (.node (.leaf (2,361027,166,[(26,0),(7,3),(2,0),(10,0)])) (.node (.leaf (2,361027,230,[(32,0),(10,0),(7,3),(40,0),(27,0),(25,0)])) (.leaf (2,362051,229,[(32,0),(16,3),(11,0),(40,0),(27,0),(8,0)])))))) (.node (.node (.node (.leaf (2,362051,167,[(2,0),(45,0),(16,3)])) (.leaf (2,362051,231,[(41,0),(40,0),(45,0),(16,3),(26,0),(11,0)]))) (.node (.leaf (2,624195,229,[(7,1),(16,3),(4,0),(27,0)])) (.node (.leaf (2,363075,227,[(32,0),(16,3),(40,0),(27,0),(13,3),(26,0)])) (.leaf (2,625219,227,[(7,1),(16,3),(4,0),(27,0),(55,0)]))))) (.node (.node (.leaf (2,366147,199,[(32,0),(16,3),(40,0),(7,3),(27,0),(13,1)])) (.leaf (2,366147,231,[(27,0),(16,3),(32,0),(40,0),(13,3),(39,1)]))) (.node (.leaf (2,628291,199,[(32,0),(16,3),(40,0),(7,3),(27,0),(13,1)])) (.node (.leaf (2,628291,231,[(27,0),(5,1),(16,3),(32,0),(55,0)])) (.leaf (2,361027,182,[(0,2),(8,2),(27,0),(53,0),(10,0),(25,0)]))))))) (.node (.node (.node (.node (.leaf (2,361027,246,[(53,0),(27,0),(8,2),(31,0),(16,3)])) (.leaf (2,362051,245,[(53,0),(27,0),(16,3),(8,0),(11,0)]))) (.node (.leaf (2,363075,179,[(8,2),(16,3),(27,0),(32,0),(43,0)])) (.node (.leaf (2,363075,243,[(27,0),(8,2),(16,3),(32,0),(31,0),(38,1)])) (.leaf (2,873027,199,[(31,0),(8,0),(0,0),(16,3)]))))) (.node (.node (.leaf (2,873027,231,[(36,1),(8,0),(0,0),(16,3),(31,0)])) (.leaf (2,366147,215,[(53,0),(8,2),(16,3),(31,0),(36,0)]))) (.node (.leaf (2,366147,183,[(0,2),(12,0),(8,2),(16,3),(4,0)])) (.node (.leaf (2,628291,151,[(8,2),(16,3),(36,0),(0,2)])) (.leaf (2,628291,215,[(53,0),(27,0),(8,2),(16,3),(31,0)])))))) (.node (.node (.node (.leaf (2,361027,174,[(32,0),(10,0),(7,3),(40,0),(51,0),(34,0),(25,0)])) (.leaf (2,362051,173,[(32,0),(16,3),(20,0),(2,0),(12,0),(51,0),(8,0)]))) (.node (.leaf (2,362051,175,[(25,0),(41,0),(2,0),(8,0),(16,3),(36,0)])) (.node (.leaf (2,363075,171,[(32,0),(16,3),(40,0),(34,0),(13,3),(26,0),(36,0)])) (.leaf (2,347715,199,[(32,0),(16,3),(51,0),(29,0),(13,1),(40,0)]))))) (.node (.node (.leaf (2,347715,231,[(51,0),(27,0),(16,3),(32,0),(39,1)])) (.node (.leaf (2,872003,199,[(32,0),(16,3),(40,0),(7,3),(34,0),(13,1)])) (.leaf (2,872003,231,[(34,0),(5,1),(16,3),(32,0),(38,2)])))) (.node (.leaf (2,366147,143,[(32,0),(16,3),(39,0),(51,0),(12,0)])) (.node (.leaf (2,366147,175,[(51,0),(39,0),(32,0),(16,3),(12,0)])) (.leaf (2,361027,190,[(53,0),(10,0),(8,2),(32,0),(51,0),(34,0),(16,1)]))))))))) (.node (.node (.node (.node (.node (.node (.leaf (2,362051,189,[(53,0),(16,3),(32,0),(51,0),(27,0),(13,0),(4,0),(39,0)])) (.leaf (2,363075,187,[(32,0),(8,2),(16,3),(27,0),(17,0),(38,0),(34,0),(36,0)]))) (.node (.leaf (2,347715,215,[(53,0),(16,3),(8,2),(27,0),(0,2),(31,0)])) (.node (.leaf (2,872003,215,[(53,0),(8,2),(16,3),(0,2),(31,0)])) (.leaf (2,872003,247,[(34,0),(53,0),(36,1),(4,0),(3,2),(0,2),(17,0),(73,0)]))))) (.node (.node (.leaf (2,365123,175,[(24,0),(8,0),(16,3),(0,0),(4,0)])) (.leaf (2,366147,159,[(53,0),(16,3),(8,2),(32,0),(36,0)]))) (.node (.leaf (2,366147,191,[(51,0),(12,0),(0,2),(53,0),(27,0),(8,2),(16,3),(4,0),(36,0)])) (.node (.leaf (2,628291,159,[(8,2),(16,3),(0,2),(4,0),(36,0)])) (.leaf (2,362307,165,[(16,3),(39,0),(0,0),(8,0)])))))) (.node (.node (.node (.leaf (2,362307,173,[(0,0),(16,3),(8,0),(39,0),(29,0),(4,2),(13,0),(12,0)])) (.leaf (2,85827,231,[(0,2),(36,1),(16,3),(8,2)]))) (.node (.leaf (2,347971,231,[(73,0),(16,3),(0,2),(8,2),(36,0),(39,0),(4,0)])) (.node (.leaf (2,610115,199,[(0,2),(16,3),(8,2),(4,0)])) (.leaf (2,610115,231,[(24,0),(16,3),(8,2),(0,2),(4,0),(39,0),(36,0)]))))) (.node (.node (.leaf (2,872259,231,[(0,2),(36,1),(16,3),(8,2)])) (.leaf (2,366403,175,[(24,0),(39,0),(16,3),(8,0),(0,0),(12,0)]))) (.node (.leaf (2,628547,143,[(0,0),(16,3),(36,0),(8,0),(29,0)])) (.node (.leaf (2,360531,182,[(49,0),(5,0),(3,3),(38,3),(17,0),(3,0)])) (.leaf (2,362579,179,[(5,0),(16,3),(3,3),(43,0),(32,0)]))))))) (.node (.node (.node (.node (.leaf (2,362579,183,[(21,0),(5,0),(16,3),(32,0)])) (.leaf (2,364627,183,[(23,0),(5,0),(16,3),(0,1)]))) (.node (.leaf (2,627795,151,[(5,0),(16,3),(0,3),(17,0),(31,0)])) (.node (.leaf (2,360531,190,[(32,0),(5,0),(10,0),(3,3),(47,0),(36,0),(16,1),(3,0)])) (.leaf (2,361555,189,[(5,0),(32,0),(16,3),(3,3),(47,0),(4,0),(36,0),(13,0),(3,0)]))))) (.node (.node (.leaf (2,625747,183,[(73,0),(16,3),(5,0),(32,0),(36,0),(38,0),(3,0)])) (.leaf (2,364627,175,[(5,0),(32,0),(16,3),(31,0),(23,0),(56,0),(3,0),(4,0),(36,0)]))) (.node (.leaf (2,364627,191,[(18,0),(56,0),(23,0),(32,0),(16,3),(5,0),(31,0)])) (.node (.leaf (2,885075,182,[(26,0),(27,0),(51,0),(8,3),(39,0),(30,0),(43,0)])) (.leaf (2,885075,246,[(41,0),(73,0),(35,0),(51,0),(30,0),(16,1)])))))) (.node (.node (.node (.leaf (2,99667,245,[(51,0),(8,1),(16,3),(7,1),(12,0)])) (.leaf (2,886099,181,[(58,0),(16,3),(6,0),(36,2),(26,0),(43,0),(38,3)]))) (.node (.leaf (2,886099,245,[(73,0),(16,3),(51,0),(35,0),(58,0)])) (.node (.leaf (2,886099,183,[(39,0),(8,1),(16,3),(7,1),(5,0)])) (.leaf (2,100691,243,[(51,0),(16,3),(0,1),(7,1),(12,0),(13,1),(3,1)]))))) (.node (.node (.leaf (2,887123,179,[(16,3),(39,0),(8,3),(27,0),(36,2),(43,0),(35,0)])) (.node (.leaf (2,887123,243,[(41,0),(73,0),(16,3),(51,0),(35,0)])) (.leaf (2,887123,183,[(21,0),(35,0),(44,0),(16,3),(17,0)])))) (.node (.leaf (2,102739,231,[(51,0),(16,3),(8,1),(0,1),(12,0),(36,0)])) (.node (.leaf (2,889171,167,[(73,0),(16,3),(11,0),(39,0),(5,2)])) (.leaf (2,889171,231,[(73,0),(16,3),(51,0),(35,0),(36,0)])))))))) (.node (.node (.node (.node (.node (.leaf (2,889171,183,[(73,0),(57,0),(16,3)])) (.leaf (2,890195,215,[(58,0),(16,3),(32,0),(73,0)]))) (.node (.leaf (2,885075,190,[(41,0),(48,0),(3,3),(27,0),(16,1),(18,0)])) (.node (.leaf (2,886099,189,[(48,0),(16,3),(3,3),(51,0),(27,0),(13,0),(36,0),(18,0),(4,0)])) (.leaf (2,886099,191,[(22,0),(40,0),(5,0),(39,0),(16,3),(15,0),(6,0),(29,0)]))))) (.node (.node (.leaf (2,889171,175,[(41,0),(48,0),(16,3),(3,0),(36,0),(4,0)])) (.leaf (2,889171,191,[(11,0),(73,0),(53,0),(57,0),(51,0),(29,0)]))) (.node (.leaf (2,361043,214,[(32,0),(10,0),(8,3),(39,0),(25,0)])) (.node (.leaf (2,362067,213,[(32,0),(16,3),(3,3),(24,0),(27,0)])) (.leaf (2,362067,215,[(56,0),(39,0),(16,3),(32,0),(26,0)])))))) (.node (.node (.node (.leaf (2,624211,213,[(7,1),(16,3),(8,1),(4,0)])) (.leaf (2,363091,211,[(32,0),(16,3),(8,3),(39,0),(26,0),(3,1)]))) (.node (.leaf (2,625235,211,[(0,1),(16,3),(7,1),(4,0),(3,1)])) (.node (.leaf (2,365139,199,[(32,0),(16,3),(56,0),(39,0)])) (.leaf (2,365139,151,[(11,0),(16,3),(57,0)]))))) (.node (.node (.leaf (2,365139,215,[(56,0),(16,3),(32,0),(11,0),(57,0)])) (.node (.leaf (2,627283,199,[(0,1),(16,3),(8,1),(4,0)])) (.leaf (2,361043,246,[(39,0),(24,0),(32,0),(27,0),(16,1),(10,0)])))) (.node (.leaf (2,362067,245,[(58,0),(32,0),(16,3),(24,0),(73,0),(13,1),(36,0)])) (.node (.leaf (2,362067,183,[(58,0),(15,0),(16,3),(5,0),(6,0)])) (.leaf (2,624211,245,[(27,0),(7,1),(16,3),(8,1),(5,0),(36,0)]))))))) (.node (.node (.node (.node (.leaf (2,363091,243,[(27,0),(24,0),(16,3),(39,0),(32,0),(38,1),(36,0)])) (.leaf (2,363091,183,[(44,0),(0,1),(17,0),(16,3),(32,0),(12,0)]))) (.node (.leaf (2,625235,243,[(24,0),(12,0),(16,3),(7,1),(0,1),(13,1),(3,1),(36,0)])) (.node (.leaf (2,365139,231,[(73,0),(64,0),(16,3),(32,0),(3,1),(36,0)])) (.leaf (2,365139,183,[(73,0),(57,0),(16,3)]))))) (.node (.node (.leaf (2,627283,231,[(27,0),(24,0),(8,1),(16,3),(0,1),(36,0)])) (.leaf (2,366163,183,[(73,0),(16,3),(35,0),(5,0)]))) (.node (.leaf (2,361043,158,[(32,0),(10,0),(3,3),(40,0),(7,3),(25,0)])) (.node (.leaf (2,362067,157,[(32,0),(16,3),(6,0),(3,0),(20,0)])) (.leaf (2,362067,159,[(26,0),(6,0),(20,0),(32,0)])))))) (.node (.node (.node (.leaf (2,363091,155,[(32,0),(16,3),(40,0),(13,3),(26,0)])) (.leaf (2,365139,143,[(32,0),(16,3),(56,0),(40,0)]))) (.node (.leaf (2,365139,159,[(56,0),(18,0),(32,0),(16,3),(8,1)])) (.node (.leaf (2,361043,190,[(79,0),(32,0),(10,0),(40,0),(16,1),(13,3)])) (.leaf (2,362067,189,[(79,0),(32,0),(16,3),(13,0),(4,0),(3,0)]))))) (.node (.node (.leaf (2,362067,191,[(20,0),(6,0),(24,0),(32,0),(16,3),(5,0),(2,0)])) (.node (.leaf (2,363091,187,[(64,0),(16,3),(32,0),(79,0),(36,0),(38,0)])) (.leaf (2,872019,215,[(5,0),(32,0),(16,3),(3,3),(27,0),(18,0)])))) (.node (.leaf (2,365139,175,[(64,0),(32,0),(16,3),(3,0),(13,0)])) (.node (.leaf (2,365139,191,[(18,0),(56,0),(32,0),(24,0),(16,3),(3,1),(13,0)])) (.leaf (2,366163,191,[(51,0),(29,0),(39,0),(5,0),(16,3),(32,0),(12,0),(53,0),(9,0)])))))))))))
def cG6M6 : BST := .node 6430260565533247257 118 0 (.node 5357678740793682034 38 0 (.node 4656001981384937364 981 0 (.node 3811946388926362670 950 0 (.node 3415303520169478851 354 0 (.node 3106415484712749405 886 1 (.node 2950216886221395306 334 0 (.node 2873393188955816772 174 1 (.node 2643802806880673417 10 0 (.node 1539618982254103629 361 0 (.nil) (.nil)) (.node 2793544244466746459 418 0 (.nil) (.nil))) (.node 2944445686244818544 295 1 (.node 2921380680486349398 244 0 (.nil) (.nil)) (.nil))) (.node 3049807716368279249 206 1 (.node 3036668175727087347 117 0 (.node 2981113451522415050 249 0 (.nil) (.nil)) (.nil)) (.node 3092920465923586005 286 0 (.node 3080841496909504070 867 0 (.nil) (.nil)) (.nil)))) (.node 3201365229821597215 21 0 (.node 3164405163484264767 1011 0 (.node 3141594378824784816 48 0 (.node 3123319530030113726 909 0 (.nil) (.nil)) (.node 3157665189975954308 926 0 (.nil) (.nil))) (.node 3187348248058467316 246 1 (.node 3183598161851759330 866 0 (.nil) (.nil)) (.nil))) (.node 3328900935454402852 377 0 (.node 3247962982319457533 293 0 (.node 3218653139667118232 910 0 (.nil) (.nil)) (.nil)) (.node 3394155449637019804 77 0 (.node 3354148622611884358 947 0 (.nil) (.nil)) (.nil))))) (.node 3637339888081481287 429 0 (.node 3514415234835811037 73 1 (.node 3428932566022955430 174 0 (.node 3420745994530647060 304 0 (.node 3418110681766319927 327 0 (.nil) (.nil)) (.node 3423593177299457580 337 1 (.nil) (.nil))) (.node 3511697470610298547 7 1 (.node 3445737953100973369 997 0 (.nil) (.nil)) (.nil))) (.node 3547650483943683260 176 0 (.node 3539079012169899540 846 1 (.node 3531118062406455027 149 0 (.nil) (.nil)) (.nil)) (.node 3611291324300044605 917 0 (.node 3584483542271101771 453 0 (.nil) (.nil)) (.nil)))) (.node 3753907686159463024 297 0 (.node 3698489980287351392 368 0 (.node 3663074243351238325 178 0 (.node 3659730388893787708 438 0 (.nil) (.nil)) (.node 3696540294560120192 41 0 (.nil) (.nil))) (.node 3749603199362970254 78 1 (.node 3724268770382350345 201 0 (.nil) (.nil)) (.nil))) (.node 3778262317355819568 410 0 (.node 3769521996803224345 941 0 (.node 3760148628499831495 497 0 (.nil) (.nil)) (.nil)) (.node 3802984323548802541 944 0 (.node 3797548420790937674 994 0 (.nil) (.nil)) (.nil)))))) (.node 4342830740075039829 105 0 (.node 4117915060416229476 220 1 (.node 4002551141458197696 355 0 (.node 3941044156884902417 85 0 (.node 3869071591265253840 345 0 (.node 3845455690751076878 233 0 (.nil) (.nil)) (.node 3873861375035805559 289 0 (.nil) (.nil))) (.node 3993999752614697982 2 1 (.node 3975363574435633150 905 1 (.nil) (.nil)) (.nil))) (.node 4031353508972034017 881 0 (.node 4010885817329409267 136 0 (.node 4005854498420561997 366 0 (.nil) (.nil)) (.nil)) (.node 4047265982559928677 877 0 (.node 4031416004546832617 905 0 (.nil) (.nil)) (.nil)))) (.node 4215860221169240309 220 0 (.node 4179860287954404782 984 0 (.node 4165267573633074062 68 1 (.node 4128513040272254828 261 0 (.nil) (.nil)) (.node 4175728898042025744 19 0 (.nil) (.nil))) (.node 4213314086052788682 945 0 (.node 4201845853311116739 476 0 (.nil) (.nil)) (.nil))) (.node 4316503004440968680 272 0 (.node 4277098828184336441 2 0 (.node 4249999108770554385 940 0 (.nil) (.nil)) (.nil)) (.node 4332679203936749397 961 0 (.node 4325113947590319115 0 0 (.nil) (.nil)) (.nil))))) (.node 4558240184539711439 285 0 (.node 4495270737862817615 325 0 (.node 4448276380532295842 30 1 (.node 4392100833603159833 432 0 (.node 4373597075551848394 971 1 (.nil) (.nil)) (.node 4438685489954616383 172 1 (.nil) (.nil))) (.node 4484412903195301972 484 1 (.node 4454442962649695989 375 0 (.nil) (.nil)) (.nil))) (.node 4519410640687452038 468 1 (.node 4512458702891625112 113 0 (.node 4501490627281315401 78 0 (.nil) (.nil)) (.nil)) (.node 4546626255134094099 44 1 (.node 4541183674682928543 251 0 (.nil) (.nil)) (.nil)))) (.node 4621789657045421921 234 0 (.node 4566537730591400665 166 1 (.node 4563279040892332761 899 0 (.node 4561677462951013321 994 1 (.nil) (.nil)) (.node 4563500231813036561 43 1 (.nil) (.nil))) (.node 4611494411393914707 109 0 (.node 4606014267654566991 973 0 (.nil) (.nil)) (.nil))) (.node 4643854204938842542 933 0 (.node 4624924989201755111 329 0 (.node 4622513189018409596 472 0 (.nil) (.nil)) (.nil)) (.node 4653310765975067667 337 0 (.node 4646906168444906458 999 1 (.nil) (.nil)) (.nil))))))) (.node 5053780299417289932 101 0 (.node 4836809324706094625 23 1 (.node 4750563674336645999 889 0 (.node 4722989237139075166 475 0 (.node 4681715612488709021 10 1 (.node 4678668793283559969 845 0 (.node 4669844819359864165 880 0 (.nil) (.nil)) (.node 4680886927848739460 25 0 (.nil) (.nil))) (.node 4718774852504597527 296 0 (.node 4681717415662810748 193 0 (.nil) (.nil)) (.nil))) (.node 4735795111547384668 4 0 (.node 4730472055463754977 349 0 (.node 4724590672615373322 446 0 (.nil) (.nil)) (.nil)) (.node 4741759310033339051 969 0 (.node 4737707826799648178 245 0 (.nil) (.nil)) (.nil)))) (.node 4800649582815512857 864 0 (.node 4773431126060728266 270 0 (.node 4765833459251089954 950 1 (.node 4765756827417092853 942 1 (.nil) (.nil)) (.node 4771654653673832962 295 0 (.nil) (.nil))) (.node 4798007515178429137 280 0 (.node 4790888534787637971 221 0 (.nil) (.nil)) (.nil))) (.node 4816794813050093607 361 1 (.node 4812416345279597763 216 0 (.node 4806829977335594410 1019 1 (.nil) (.nil)) (.nil)) (.node 4835445025344384808 309 0 (.node 4835123756372283460 223 0 (.nil) (.nil)) (.nil))))) (.node 4951931486581030562 384 0 (.node 4881185157485183426 298 0 (.node 4855486909369355431 460 1 (.node 4851686241592515057 50 0 (.node 4842580520483543091 978 0 (.nil) (.nil)) (.node 4854821650161563533 413 0 (.nil) (.nil))) (.node 4861848129911411273 135 0 (.node 4861268311898856454 885 0 (.nil) (.nil)) (.nil))) (.node 4925729646763641154 278 0 (.node 4925727894416849134 227 0 (.node 4900754139873164523 398 0 (.nil) (.nil)) (.nil)) (.node 4951068998281875029 11 0 (.node 4934184082001729105 46 0 (.nil) (.nil)) (.nil)))) (.node 4989553294309898382 103 0 (.node 4965738571953075852 306 0 (.node 4963182013101562228 243 0 (.node 4952658445384481705 358 0 (.nil) (.nil)) (.node 4965033588797039833 449 0 (.nil) (.nil))) (.node 4982890644259815629 310 0 (.node 4973426322092355655 854 0 (.nil) (.nil)) (.nil))) (.node 5007350267493967210 1005 0 (.node 5002540601760010012 910 1 (.node 4999479792002335497 872 0 (.nil) (.nil)) (.nil)) (.node 5050028828437230389 350 0 (.node 5019847454060377717 168 0 (.nil) (.nil)) (.nil)))))) (.node 5215322847922138629 66 1 (.node 5152925472229181819 179 0 (.node 5132874843659893981 426 0 (.node 5114942507350403187 389 0 (.node 5090813022327186850 409 0 (.node 5054359085438073566 419 1 (.nil) (.nil)) (.node 5114456356553851935 946 0 (.nil) (.nil))) (.node 5128086757507944132 166 0 (.node 5118395545056937920 229 0 (.nil) (.nil)) (.nil))) (.node 5140535244563754586 321 0 (.node 5134877962714837337 123 0 (.node 5134516767093820712 161 0 (.nil) (.nil)) (.nil)) (.node 5151685404511786441 425 0 (.node 5146107133861872999 59 0 (.nil) (.nil)) (.nil)))) (.node 5178080648064233034 102 0 (.node 5169199123616238386 470 0 (.node 5157877906124560889 115 0 (.node 5153148630340563395 143 1 (.nil) (.nil)) (.node 5157975646019207525 231 0 (.nil) (.nil))) (.node 5174850369317171726 402 0 (.node 5169729783610873789 38 1 (.nil) (.nil)) (.nil))) (.node 5192304244212394320 482 0 (.node 5191462861745720906 906 0 (.node 5181315224222673562 134 0 (.nil) (.nil)) (.nil)) (.node 5196932779088179952 499 0 (.node 5196932774889051656 305 1 (.nil) (.nil)) (.nil))))) (.node 5270535330575394590 281 0 (.node 5250092966075251994 919 0 (.node 5234081393686281306 911 1 (.node 5231483358766231038 266 0 (.node 5226720907528540997 233 1 (.nil) (.nil)) (.node 5232436115796240548 478 0 (.nil) (.nil))) (.node 5249804156955847467 121 0 (.node 5245371119822832198 181 0 (.nil) (.nil)) (.nil))) (.node 5255501115927116123 846 0 (.node 5255342687272660942 290 0 (.node 5255013959341321027 334 1 (.nil) (.nil)) (.nil)) (.node 5266872891982131164 849 1 (.node 5265629496571240522 140 0 (.nil) (.nil)) (.nil)))) (.node 5307207963457611235 996 0 (.node 5294214177850051998 990 0 (.node 5293514375257644968 300 0 (.node 5286753159292896638 466 0 (.nil) (.nil)) (.node 5294092004891679258 170 0 (.nil) (.nil))) (.node 5302561860494150517 461 0 (.node 5296601818858198413 494 0 (.nil) (.nil)) (.nil))) (.node 5328322462914994238 1004 0 (.node 5321296204484231511 942 0 (.node 5320021072013903670 230 0 (.nil) (.nil)) (.nil)) (.node 5355018809506053736 455 0 (.node 5344913070401422873 126 0 (.nil) (.nil)) (.nil)))))))) (.node 5884723982088424687 264 0 (.node 5611224951179416501 319 0 (.node 5468270918595617202 995 1 (.node 5403989361458834895 8 0 (.node 5386346917535928687 311 1 (.node 5363496206645966428 479 0 (.node 5360579739121343349 222 0 (.node 5359290573940137692 394 0 (.nil) (.nil)) (.node 5361857581059477952 960 0 (.nil) (.nil))) (.node 5385430277494384764 341 0 (.node 5375932271536049796 311 0 (.nil) (.nil)) (.nil))) (.node 5391986243980196527 274 0 (.node 5386888224310652247 305 0 (.node 5386676234016671247 998 0 (.nil) (.nil)) (.nil)) (.node 5395119087346736462 45 1 (.node 5392032902808430132 84 0 (.nil) (.nil)) (.nil)))) (.node 5451217268349306107 903 0 (.node 5418906268145857710 496 0 (.node 5416870429879064235 357 0 (.node 5405782467448307581 204 0 (.nil) (.nil)) (.node 5416999005576358881 454 0 (.nil) (.nil))) (.node 5449341503615232724 206 0 (.node 5432292985300854107 901 0 (.nil) (.nil)) (.nil))) (.node 5458319225404255830 104 0 (.node 5456029536424902563 370 0 (.node 5454682462387083895 141 0 (.nil) (.nil)) (.nil)) (.node 5464238965587828127 408 0 (.node 5462462267295008325 94 0 (.nil) (.nil)) (.nil))))) (.node 5528321639535385310 485 0 (.node 5491786450603986160 277 0 (.node 5483846241216727645 406 0 (.node 5479212357515151008 217 0 (.node 5470862422482557235 353 0 (.nil) (.nil)) (.node 5480068024610693351 411 0 (.nil) (.nil))) (.node 5486541384795394181 302 1 (.node 5485274882032477811 159 0 (.nil) (.nil)) (.nil))) (.node 5509227344522935370 458 0 (.node 5507201938318570464 13 0 (.node 5496585118169990402 469 0 (.nil) (.nil)) (.nil)) (.node 5518225619176182405 492 0 (.node 5517581914427966421 340 1 (.nil) (.nil)) (.nil)))) (.node 5565835427797237963 55 0 (.node 5557754287804566577 39 1 (.node 5540421308533658660 47 0 (.node 5538127704373477826 874 0 (.nil) (.nil)) (.node 5544804057193284727 507 1 (.nil) (.nil))) (.node 5563447631708879834 322 0 (.node 5562650435494903220 62 0 (.nil) (.nil)) (.nil))) (.node 5575945046472689702 390 0 (.node 5569856443521594433 1013 0 (.node 5568296014074727348 862 0 (.nil) (.nil)) (.nil)) (.node 5591671648136581780 882 0 (.node 5589651071517115265 980 0 (.nil) (.nil)) (.nil)))))) (.node 5755080312346392159 189 0 (.node 5679826789312557957 139 1 (.node 5654619338522059949 492 1 (.node 5642644233832123612 883 0 (.node 5635804341976341745 952 0 (.node 5631268434343900491 273 0 (.nil) (.nil)) (.node 5636936151291523377 68 0 (.nil) (.nil))) (.node 5654377876749568207 333 0 (.node 5653670490016618174 252 0 (.nil) (.nil)) (.nil))) (.node 5673778322823363660 9 0 (.node 5672863073103440794 365 0 (.node 5658517034698438614 30 0 (.nil) (.nil)) (.nil)) (.node 5678072767821774353 922 0 (.node 5677519621989669133 240 0 (.nil) (.nil)) (.nil)))) (.node 5720866944186410640 324 0 (.node 5711863570156686847 40 0 (.node 5703822031287113050 237 0 (.node 5685443120402255277 132 0 (.nil) (.nil)) (.node 5710535823067934431 925 0 (.nil) (.nil))) (.node 5719724086272497438 374 1 (.node 5712561583734710029 92 0 (.nil) (.nil)) (.nil))) (.node 5738432877631818114 249 1 (.node 5732060238443373307 1017 0 (.node 5723947390263293176 199 0 (.nil) (.nil)) (.nil)) (.node 5751574661597946618 373 0 (.node 5741732071972878406 364 0 (.nil) (.nil)) (.nil))))) (.node 5826796524357511625 869 0 (.node 5795610168268959307 966 1 (.node 5772889629424045022 65 0 (.node 5766892528629599657 457 0 (.node 5763713987570404017 948 0 (.nil) (.nil)) (.node 5772146328026860651 98 0 (.nil) (.nil))) (.node 5788446868644570010 453 1 (.node 5773917202861456823 17 0 (.nil) (.nil)) (.nil))) (.node 5815507811592803747 157 0 (.node 5805757611520249442 988 1 (.node 5800113857642739474 510 0 (.nil) (.nil)) (.nil)) (.node 5826352574066896513 112 0 (.node 5821539283188843972 405 0 (.nil) (.nil)) (.nil)))) (.node 5851941013694621116 428 0 (.node 5848056825995567492 995 0 (.node 5836954770903428276 269 0 (.node 5829641778801333200 389 1 (.nil) (.nil)) (.node 5844522494783248116 1004 1 (.nil) (.nil))) (.node 5851332831549191969 902 0 (.node 5850948257631878047 941 1 (.nil) (.nil)) (.nil))) (.node 5869009662990698910 973 1 (.node 5862382814444682789 158 0 (.node 5860995363402105569 354 1 (.nil) (.nil)) (.nil)) (.node 5882521876074268580 385 0 (.node 5880669358126838813 133 1 (.nil) (.nil)) (.nil))))))) (.node 6213124690870222456 246 0 (.node 6057731211208829875 226 0 (.node 5967296818451461767 851 0 (.node 5916479701218289737 1001 0 (.node 5896033901440432349 348 0 (.node 5894726509720291268 974 0 (.node 5890653287838405976 260 0 (.nil) (.nil)) (.node 5895115142319414363 124 0 (.nil) (.nil))) (.node 5913057593115089325 109 1 (.node 5910823645831830344 216 1 (.nil) (.nil)) (.nil))) (.node 5942288771263316378 886 0 (.node 5926580209650323393 930 0 (.node 5926531287851049926 397 0 (.nil) (.nil)) (.nil)) (.node 5960963976668791652 96 0 (.node 5958317544164632556 73 0 (.nil) (.nil)) (.nil)))) (.node 5997171480764963189 74 1 (.node 5986553600313114711 293 1 (.node 5968365950559558509 69 0 (.node 5967322634576784412 423 0 (.nil) (.nil)) (.node 5968847283985068944 326 0 (.nil) (.nil))) (.node 5995877977425349964 1006 0 (.node 5990556222814405723 256 0 (.nil) (.nil)) (.nil))) (.node 6021206025195038489 421 0 (.node 6019185969420340132 155 0 (.node 6013473157635375676 951 0 (.nil) (.nil)) (.nil)) (.node 6036741373139034989 81 1 (.node 6023590075945059732 188 0 (.nil) (.nil)) (.nil))))) (.node 6132813592476642406 1014 1 (.node 6096573421217851132 398 1 (.node 6079070975832097983 70 0 (.node 6065422619034077072 137 0 (.node 6064481972022694339 852 1 (.nil) (.nil)) (.node 6068092536503301825 27 0 (.nil) (.nil))) (.node 6084893325783808239 498 0 (.node 6082834701625391150 879 0 (.nil) (.nil)) (.nil))) (.node 6115138080536673586 380 1 (.node 6103741416987204893 928 0 (.node 6100726802093018511 472 1 (.nil) (.nil)) (.nil)) (.node 6120847273796275239 988 0 (.node 6117767048014192123 484 0 (.nil) (.nil)) (.nil)))) (.node 6179801305687793394 417 0 (.node 6161779547280472768 462 0 (.node 6144701569598186043 5 0 (.node 6139900479590347646 214 0 (.nil) (.nil)) (.node 6151686429678857980 122 0 (.nil) (.nil))) (.node 6176818623108047047 169 0 (.node 6172454604504351264 1003 0 (.nil) (.nil)) (.nil))) (.node 6194604485104960185 180 0 (.node 6187311069600533191 441 0 (.node 6185507197284823535 909 1 (.nil) (.nil)) (.nil)) (.node 6210779005814599970 482 1 (.node 6195501918641886604 190 0 (.nil) (.nil)) (.nil)))))) (.node 6327301303247245720 904 0 (.node 6266439960630541446 77 1 (.node 6235337769199949383 1021 0 (.node 6227540115579267723 133 0 (.node 6217926361500565697 388 0 (.node 6215059071764043199 225 0 (.nil) (.nil)) (.node 6224982640563241469 20 0 (.nil) (.nil))) (.node 6232114263939981230 302 0 (.node 6231962128993508958 125 0 (.nil) (.nil)) (.nil))) (.node 6243532415286008737 370 1 (.node 6240446530986649185 286 1 (.node 6239257532581837616 884 0 (.nil) (.nil)) (.nil)) (.node 6260278813119982181 331 1 (.node 6254225431150313930 212 1 (.nil) (.nil)) (.nil)))) (.node 6305041236797861753 380 0 (.node 6285744733141240119 975 0 (.node 6277543774199776692 45 0 (.node 6268480413295190424 29 0 (.nil) (.nil)) (.node 6285726195233034735 979 0 (.nil) (.nil))) (.node 6299105007550971912 934 0 (.node 6295673084251598710 401 0 (.nil) (.nil)) (.nil))) (.node 6313440906495415947 276 0 (.node 6307925050599392510 923 0 (.node 6305683435563882685 888 0 (.nil) (.nil)) (.nil)) (.node 6317561300355112151 287 0 (.node 6314204413788965580 416 0 (.nil) (.nil)) (.nil))))) (.node 6408165438399677825 963 0 (.node 6376514037470531359 489 0 (.node 6357220216646534962 875 0 (.node 6331262725577253647 878 0 (.node 6331049124216764168 868 1 (.nil) (.nil)) (.node 6350723229944701818 356 0 (.nil) (.nil))) (.node 6369772113146353181 365 1 (.node 6364347341940725587 110 0 (.nil) (.nil)) (.nil))) (.node 6387695300092037971 197 0 (.node 6385094888344950549 427 0 (.node 6381386378942841927 88 0 (.nil) (.nil)) (.nil)) (.node 6397687867270151733 37 0 (.node 6396082941113427123 198 0 (.nil) (.nil)) (.nil)))) (.node 6415153897232564239 399 0 (.node 6410893801986071705 167 0 (.node 6410558842318627219 74 0 (.node 6408440797900476323 477 0 (.nil) (.nil)) (.nil)) (.node 6411774279148728119 308 1 (.node 6411752402681053977 1009 0 (.nil) (.nil)) (.nil))) (.node 6429314724220377872 18 0 (.node 6424631439606472995 346 0 (.node 6423815965006274181 232 0 (.nil) (.nil)) (.nil)) (.node 6429710758550694205 967 0 (.node 6429431498461062205 427 1 (.nil) (.nil)) (.nil))))))))) (.node 7440472916648777438 284 0 (.node 6949690913435815791 213 0 (.node 6690377916701273769 129 0 (.node 6553118666105517185 335 0 (.node 6494670681268317982 415 0 (.node 6472381473716619974 1002 0 (.node 6454264273594764955 202 0 (.node 6449154541868747019 501 0 (.node 6434835749441432220 36 0 (.nil) (.nil)) (.node 6453408211151888252 392 0 (.nil) (.nil))) (.node 6470646239762747161 367 0 (.node 6466882306995327433 184 0 (.nil) (.nil)) (.nil))) (.node 6483532347258077007 330 0 (.node 6478171050611751646 959 0 (.node 6476307421015113467 148 1 (.nil) (.nil)) (.nil)) (.node 6488311280060003612 66 0 (.node 6483983756803095262 871 0 (.nil) (.nil)) (.nil)))) (.node 6513573394357039227 425 1 (.node 6510652896571465901 312 1 (.node 6508829021888147726 465 0 (.node 6508816213537911494 42 0 (.nil) (.nil)) (.node 6508829060347587086 362 0 (.nil) (.nil))) (.node 6512079740750727148 386 0 (.node 6511132603944265981 226 1 (.nil) (.nil)) (.nil))) (.node 6536169086411546811 143 0 (.node 6535963852833664855 144 0 (.node 6519061519133445737 505 0 (.nil) (.nil)) (.nil)) (.node 6546906423151466237 235 0 (.node 6543146539744087962 856 0 (.nil) (.nil)) (.nil))))) (.node 6617795055588473269 985 0 (.node 6568669230664597193 175 1 (.node 6561820850687846620 407 0 (.node 6553373511166605454 177 0 (.node 6553360702816369222 22 0 (.nil) (.nil)) (.node 6558697784785155730 54 0 (.nil) (.nil))) (.node 6564999951516893847 473 0 (.node 6561886399980490182 491 0 (.nil) (.nil)) (.nil))) (.node 6588511770275210559 393 1 (.node 6587769676952662783 239 0 (.node 6574762175932096040 965 0 (.nil) (.nil)) (.nil)) (.node 6614798297404963151 108 0 (.node 6606431677790734492 921 0 (.nil) (.nil)) (.nil)))) (.node 6673199404364426917 471 1 (.node 6659897364878808975 315 0 (.node 6654647398731584326 28 0 (.node 6648667448572013078 873 0 (.nil) (.nil)) (.node 6657156703358842595 154 0 (.nil) (.nil))) (.node 6664018292135109043 23 0 (.node 6662310487387383105 495 0 (.nil) (.nil)) (.nil))) (.node 6682161985296759359 471 0 (.node 6679433779849693347 854 1 (.node 6678394148671774115 43 0 (.nil) (.nil)) (.nil)) (.node 6689359002391621727 989 0 (.node 6687317380462312122 913 0 (.nil) (.nil)) (.nil)))))) (.node 6818294732155003781 53 0 (.node 6756095823722061346 859 0 (.node 6726072242672734978 271 0 (.node 6722492969722142818 86 0 (.node 6704960007908818563 267 1 (.node 6700646061030446442 12 0 (.nil) (.nil)) (.node 6714458140391940761 431 0 (.nil) (.nil))) (.node 6725849084561353402 307 0 (.node 6722611529212801286 937 0 (.nil) (.nil)) (.nil))) (.node 6734159349368161902 952 1 (.node 6731854909915173060 207 0 (.node 6729215615413751949 258 0 (.nil) (.nil)) (.nil)) (.node 6751793024528186763 439 1 (.node 6743969719660337200 428 1 (.nil) (.nil)) (.nil)))) (.node 6785289365343187417 954 0 (.node 6763608138934617267 191 0 (.node 6759608522150065275 893 0 (.node 6759544909149675221 371 0 (.nil) (.nil)) (.node 6760241808350638659 404 0 (.nil) (.nil))) (.node 6779871101721911536 238 0 (.node 6773465785864686447 64 0 (.nil) (.nil)) (.nil))) (.node 6806223020720790689 451 0 (.node 6803403611942821991 887 0 (.node 6789700448774888751 982 0 (.nil) (.nil)) (.nil)) (.node 6807005006018452889 911 0 (.node 6806799772440570933 400 0 (.nil) (.nil)) (.nil))))) (.node 6868297304932962282 971 0 (.node 6835025738780150849 253 0 (.node 6834245163939231017 369 0 (.node 6825536967093095808 162 0 (.node 6825079991711011629 303 0 (.nil) (.nil)) (.node 6832707733840102707 456 0 (.nil) (.nil))) (.node 6834597702463858417 393 0 (.node 6834557534084920385 150 0 (.nil) (.nil)) (.nil))) (.node 6850112003419304924 186 0 (.node 6847925458144149835 182 0 (.node 6837688475636951018 976 0 (.nil) (.nil)) (.nil)) (.node 6853921448396297210 999 0 (.node 6851741937046985347 896 0 (.nil) (.nil)) (.nil)))) (.node 6904934682360934875 79 0 (.node 6887953892356081543 144 1 (.node 6880584901629817687 138 0 (.node 6869336936110881514 474 0 (.nil) (.nil)) (.node 6881916932771174463 87 0 (.nil) (.nil))) (.node 6901753318232264937 14 0 (.node 6900129403494241861 870 0 (.nil) (.nil)) (.nil))) (.node 6928508334105081257 224 0 (.node 6928349897515382845 312 0 (.node 6908284073741502403 991 0 (.nil) (.nil)) (.nil)) (.node 6943486268146948285 1016 0 (.node 6942218189500594000 924 0 (.nil) (.nil)) (.nil))))))) (.node 7176704529630864394 403 0 (.node 7066695649496580198 876 0 (.node 6997813841126332955 299 0 (.node 6972127862607165425 80 0 (.node 6968886655701799454 400 1 (.node 6950269699456599425 419 0 (.node 6950171433875014726 288 0 (.nil) (.nil)) (.node 6950708462578445893 163 0 (.nil) (.nil))) (.node 6971807367776960780 847 0 (.node 6971706453601032452 275 0 (.nil) (.nil)) (.nil))) (.node 6984539705945084979 894 0 (.node 6977390668272866601 382 0 (.node 6974986988379561178 849 0 (.nil) (.nil)) (.nil)) (.node 6997318910573764127 72 0 (.node 6986723636345712709 153 0 (.nil) (.nil)) (.nil)))) (.node 7033647164109289027 145 0 (.node 7027721150066920659 57 0 (.node 7016441598308196704 183 0 (.node 7011441699818935759 316 0 (.nil) (.nil)) (.node 7017779660139421848 972 1 (.nil) (.nil))) (.node 7033110577143830362 500 0 (.node 7028825945636048415 987 0 (.nil) (.nil)) (.nil))) (.node 7050483284581893987 850 0 (.node 7040812879251658357 951 1 (.node 7036486734180277508 445 0 (.nil) (.nil)) (.nil)) (.node 7065109737634764245 58 0 (.node 7055572068058691134 956 0 (.nil) (.nil)) (.nil))))) (.node 7134867989861121721 82 0 (.node 7103844223675402386 152 0 (.node 7079267834557701515 142 0 (.node 7070834105076095515 344 0 (.node 7069916520302750880 283 0 (.nil) (.nil)) (.node 7077427901192993211 67 0 (.nil) (.nil))) (.node 7097289592965022141 897 0 (.node 7094384887564833681 263 0 (.nil) (.nil)) (.nil))) (.node 7118253053776571012 56 0 (.node 7114886102387265953 907 1 (.node 7107841761734565689 1001 1 (.nil) (.nil)) (.nil)) (.node 7126881839110636212 282 0 (.node 7123896810081650195 227 1 (.nil) (.nil)) (.nil)))) (.node 7160634430676775413 448 0 (.node 7155442522008264667 868 0 (.node 7140960464869256709 383 0 (.node 7140863468404442931 395 0 (.nil) (.nil)) (.node 7141701531964389419 63 0 (.nil) (.nil))) (.node 7159447963933334202 360 0 (.node 7158328887386522019 938 0 (.nil) (.nil)) (.nil))) (.node 7167405574119624226 259 0 (.node 7166844827546702626 91 0 (.node 7161540110589766381 196 0 (.nil) (.nil)) (.nil)) (.node 7167684838408384522 391 0 (.node 7167405578318752522 171 1 (.nil) (.nil)) (.nil)))))) (.node 7327174310685361002 90 0 (.node 7231536935901993578 440 1 (.node 7199393599825726592 99 0 (.node 7180938499759483698 114 0 (.node 7176905191684408580 891 0 (.node 7176808833372784594 459 1 (.nil) (.nil)) (.node 7177081208970314435 895 0 (.nil) (.nil))) (.node 7186577816311328079 318 0 (.node 7185339767620889907 194 0 (.nil) (.nil)) (.nil))) (.node 7215501275303977031 255 0 (.node 7213616141397886099 420 0 (.node 7211615814407982577 97 0 (.nil) (.nil)) (.nil)) (.node 7231122305589785807 481 0 (.node 7231000132631413067 918 0 (.nil) (.nil)) (.nil)))) (.node 7267171360320612802 387 0 (.node 7257585656118657449 468 0 (.node 7237070301033140675 1015 0 (.node 7231994916203477831 1015 1 (.nil) (.nil)) (.node 7247098036925531909 503 0 (.nil) (.nil))) (.node 7263031959794499087 1014 0 (.node 7261668031525432737 32 0 (.nil) (.nil)) (.nil))) (.node 7299899975477360754 1008 0 (.node 7269476213007156330 1018 0 (.node 7268012006414246451 119 0 (.nil) (.nil)) (.nil)) (.node 7325684162557350966 424 0 (.node 7315259816369214353 436 0 (.nil) (.nil)) (.nil))))) (.node 7406316410596997497 892 0 (.node 7370712800810364296 165 0 (.node 7360634557056893283 107 1 (.node 7334107302077840334 127 0 (.node 7330494369978396183 291 0 (.nil) (.nil)) (.node 7356474115734016806 957 0 (.nil) (.nil))) (.node 7368180683624322999 169 1 (.node 7366454146569611541 378 0 (.nil) (.nil)) (.nil))) (.node 7380334554338909476 860 0 (.node 7378905023256670262 430 1 (.node 7373992864450928253 853 0 (.nil) (.nil)) (.nil)) (.node 7394918406204950504 175 0 (.node 7381683092510602907 912 0 (.nil) (.nil)) (.nil)))) (.node 7417729308482994775 863 0 (.node 7410724193199302451 935 0 (.node 7409327971823019776 210 0 (.node 7407002186271359226 89 0 (.nil) (.nil)) (.nil)) (.node 7417537503589433249 943 0 (.node 7417166123933986530 340 0 (.nil) (.nil)) (.nil))) (.node 7430103414609841640 105 1 (.node 7424232253553911169 949 0 (.node 7421367794297383149 444 1 (.nil) (.nil)) (.nil)) (.node 7439096064855692063 195 0 (.node 7438652931782255667 34 0 (.nil) (.nil)) (.nil)))))))) (.node 8271707439713825060 61 0 (.node 7766073668068759228 915 0 (.node 7616462708297091531 460 0 (.node 7567875960866042603 172 0 (.node 7468958301907128868 865 0 (.node 7456492463892093467 81 0 (.node 7440714671211810586 379 0 (.node 7440558840373037399 93 0 (.nil) (.nil)) (.node 7450117926265842658 487 1 (.nil) (.nil))) (.node 7458762180726155068 435 0 (.node 7458682485516188030 502 0 (.nil) (.nil)) (.nil))) (.node 7501079814680841634 900 0 (.node 7471009807901937994 1000 0 (.node 7470981246486565819 31 0 (.nil) (.nil)) (.nil)) (.node 7527806693631710689 215 1 (.node 7527179048362426350 257 0 (.nil) (.nil)) (.nil)))) (.node 7596513688277231315 188 1 (.node 7587569688192970344 268 0 (.node 7585042024951072209 420 1 (.node 7574866411494769162 39 0 (.nil) (.nil)) (.node 7586700186086700376 211 0 (.nil) (.nil))) (.node 7593081135798301972 262 0 (.node 7591893723626359983 444 0 (.nil) (.nil)) (.nil))) (.node 7604420853181496934 294 0 (.node 7599001230838154203 241 0 (.node 7598585029190324715 338 0 (.nil) (.nil)) (.nil)) (.node 7613906476693232524 148 0 (.node 7608472197753235888 372 0 (.nil) (.nil)) (.nil))))) (.node 7691685301629706264 499 1 (.node 7657092070506081345 855 0 (.node 7634158206008953087 212 0 (.node 7627527908815027013 26 0 (.node 7624779498555597753 33 0 (.nil) (.nil)) (.node 7631684949290339403 857 0 (.nil) (.nil))) (.node 7656593963698218369 439 0 (.node 7644644972488627614 176 1 (.nil) (.nil)) (.nil))) (.node 7662335613990214835 208 0 (.node 7661459311140591319 203 0 (.node 7657775071926144449 452 0 (.nil) (.nil)) (.nil)) (.node 7676068665455599013 929 0 (.node 7669827816879982682 1 0 (.nil) (.nil)) (.nil)))) (.node 7727502107994195001 183 1 (.node 7709976179073313272 51 0 (.node 7707226207531201848 146 0 (.node 7696837407357797164 123 1 (.nil) (.nil)) (.node 7707295203893019965 215 0 (.nil) (.nil))) (.node 7722707138376037484 437 0 (.node 7722027727056826347 296 1 (.nil) (.nil)) (.nil))) (.node 7739345216309072557 493 0 (.node 7733994868647394888 1010 0 (.node 7728915134719870262 204 1 (.nil) (.nil)) (.nil)) (.node 7757053976846279356 71 0 (.node 7740420464456843573 107 0 (.nil) (.nil)) (.nil)))))) (.node 8035811093608873505 986 0 (.node 7908306068853239549 343 0 (.node 7824051159855755078 852 0 (.node 7798354015612860116 156 0 (.node 7766457231900311428 15 1 (.node 7766448360536767227 930 1 (.nil) (.nil)) (.node 7766690321577504022 414 0 (.nil) (.nil))) (.node 7814931230837100480 953 0 (.node 7814346897611049792 3 0 (.nil) (.nil)) (.nil))) (.node 7841765866640754150 848 0 (.node 7840029509088289030 873 1 (.node 7830825872584053589 128 0 (.nil) (.nil)) (.nil)) (.node 7904774451311162945 890 0 (.node 7881584124654297354 936 0 (.nil) (.nil)) (.nil)))) (.node 7991131123555747404 866 1 (.node 7959507198513591423 508 0 (.node 7927470736595766188 916 0 (.node 7917783327953598949 132 1 (.nil) (.nil)) (.node 7945866855397740887 931 0 (.nil) (.nil))) (.node 7990710583113481488 44 0 (.node 7964459211336202302 60 0 (.nil) (.nil)) (.nil))) (.node 7999824434055376952 339 0 (.node 7999824429856248656 151 0 (.node 7999655519095676720 983 1 (.nil) (.nil)) (.nil)) (.node 8034348466777060899 434 0 (.node 8025537854539113858 408 1 (.nil) (.nil)) (.nil))))) (.node 8157051132721599968 313 0 (.node 8124477902401257311 430 0 (.node 8098470690860105858 447 0 (.node 8064540503886790464 304 1 (.node 8043305601502897385 920 0 (.nil) (.nil)) (.node 8065523561585058917 944 1 (.nil) (.nil))) (.node 8121139358372909626 171 0 (.node 8119798955695779692 509 0 (.nil) (.nil)) (.nil))) (.node 8150349350630676437 504 0 (.node 8150272482178068429 120 0 (.node 8132410046381620413 993 0 (.nil) (.nil)) (.nil)) (.node 8156768842833366953 368 1 (.node 8155149791761460512 139 0 (.nil) (.nil)) (.nil)))) (.node 8236759939768232472 962 0 (.node 8186162091003886445 1020 0 (.node 8170070871109806450 280 1 (.node 8159824396493826897 301 0 (.nil) (.nil)) (.node 8179144029356985996 983 0 (.nil) (.nil))) (.node 8205831846734986365 972 0 (.node 8200426124901679234 359 0 (.nil) (.nil)) (.nil))) (.node 8251851656896239450 228 0 (.node 8240751967062500979 320 0 (.node 8236925873769073763 352 0 (.nil) (.nil)) (.nil)) (.node 8266629645826811336 1019 0 (.node 8264209430986979529 200 0 (.nil) (.nil)) (.nil))))))) (.node 8768791304332956003 483 0 (.node 8534629088573964683 250 0 (.node 8425643588352677117 205 0 (.node 8374537722593091614 861 0 (.node 8326966973380605537 141 1 (.node 8302978176158587490 279 0 (.node 8299550251876256880 111 0 (.nil) (.nil)) (.node 8306680240886086990 493 1 (.nil) (.nil))) (.node 8355792949876188277 363 0 (.node 8355319474315497615 342 0 (.nil) (.nil)) (.nil))) (.node 8397865083330223971 847 1 (.node 8397834146561718171 147 0 (.node 8390316338891622061 328 0 (.nil) (.nil)) (.nil)) (.node 8405707166754170167 898 0 (.node 8401755470204318043 197 1 (.nil) (.nil)) (.nil)))) (.node 8475878995360158029 504 1 (.node 8433652253916866731 332 0 (.node 8426523800719975440 422 0 (.node 8425919143944645025 314 0 (.nil) (.nil)) (.node 8428502664235838250 292 0 (.nil) (.nil))) (.node 8475857626959063429 376 0 (.node 8446038990112440658 1007 0 (.nil) (.nil)) (.nil))) (.node 8499106697620201277 966 0 (.node 8478291467203246445 463 0 (.node 8478195362171982181 467 0 (.nil) (.nil)) (.nil)) (.node 8534071662160692543 52 0 (.node 8515891340203244880 242 0 (.nil) (.nil)) (.nil))))) (.node 8685344699137494561 443 0 (.node 8579996965588253840 152 1 (.node 8560985931976524985 992 0 (.node 8545863188654892847 254 0 (.node 8543339805530468301 185 0 (.nil) (.nil)) (.node 8560548917016173563 76 0 (.nil) (.nil))) (.node 8573913117016830103 1012 0 (.node 8569750490972274287 173 0 (.nil) (.nil)) (.nil))) (.node 8635381789312517119 160 0 (.node 8601958119888879338 336 0 (.node 8593281485338772254 7 0 (.nil) (.nil)) (.nil)) (.node 8685310920647808438 858 0 (.node 8678405752531959988 490 0 (.nil) (.nil)) (.nil)))) (.node 8724248055072737055 106 0 (.node 8715602748572057690 955 0 (.node 8714432460186306522 247 0 (.node 8694339642431596635 977 0 (.nil) (.nil)) (.node 8715146817303639130 442 0 (.nil) (.nil))) (.node 8724246815068714015 209 0 (.node 8724166377475464983 970 0 (.nil) (.nil)) (.nil))) (.node 8738884131710054363 433 0 (.node 8734707456185985558 187 0 (.node 8724530482878717775 450 0 (.nil) (.nil)) (.nil)) (.node 8768710866753922711 486 0 (.node 8745500529084252578 374 0 (.nil) (.nil)) (.nil)))))) (.node 9408593587220902553 116 0 (.node 9009757081028744284 267 0 (.node 8882843665407528259 958 0 (.node 8798815798844571568 397 1 (.node 8776482948259720410 927 0 (.node 8768791304347171743 49 0 (.nil) (.nil)) (.node 8795416311689522917 317 0 (.nil) (.nil))) (.node 8858123635721606002 95 0 (.node 8816489801747926514 16 0 (.nil) (.nil)) (.nil))) (.node 8934227038313497936 968 0 (.node 8929135147487894568 932 0 (.node 8892019110298727571 914 0 (.nil) (.nil)) (.nil)) (.node 9005414423722495825 488 0 (.node 8968426488230285189 265 0 (.nil) (.nil)) (.nil)))) (.node 9156661222419095557 412 0 (.node 9069444847431590516 1023 0 (.node 9044455578964757270 130 0 (.node 9018453429463525305 6 0 (.nil) (.nil)) (.node 9061932532219034595 219 0 (.nil) (.nil))) (.node 9149949294579933530 308 0 (.node 9139372706685474115 24 0 (.nil) (.nil)) (.nil))) (.node 9339380844232483011 15 0 (.node 9289256175304871468 192 0 (.node 9232572195177960996 440 0 (.nil) (.nil)) (.nil)) (.node 9398097957635252385 506 0 (.node 9371492726815634215 236 0 (.nil) (.nil)) (.nil))))) (.node 10071910376565732477 83 0 (.node 9630278208028209351 381 0 (.node 9481605906492710315 459 0 (.node 9472202651438678243 323 0 (.node 9467230049956045243 487 0 (.nil) (.nil)) (.node 9472681536043675875 347 0 (.nil) (.nil))) (.node 9539592214200114713 396 0 (.node 9482645537670629547 351 0 (.nil) (.nil)) (.nil))) (.node 9960200483549409061 964 0 (.node 9880319556160190211 131 0 (.node 9816071418343028802 100 0 (.nil) (.nil)) (.nil)) (.node 10028320660400146272 1022 0 (.node 10002674115854770413 507 0 (.nil) (.nil)) (.nil)))) (.node 10304974045699930073 339 1 (.node 10251230088334023474 218 0 (.node 10251228848315784694 35 0 (.node 10170788488624216000 164 0 (.nil) (.nil)) (.nil)) (.node 10290460570929456927 331 0 (.node 10253421729569970865 464 0 (.nil) (.nil)) (.nil))) (.node 10689170661644269618 908 0 (.node 10661154942794232084 939 0 (.node 10460986500258433761 75 0 (.nil) (.nil)) (.nil)) (.node 11315593789525717533 907 0 (.node 10691121692130166820 480 0 (.nil) (.nil)) (.nil)))))))))
def cG6T7 : BTree NodeData := .node (.node (.node (.node (.node (.leaf (1,272,126,[(7,0),(8,0),(40,0),(39,0),(5,0),(28,0),(16,0),(4,0)])) (.node (.leaf (1,784,124,[(7,0),(8,0),(5,0),(36,0)])) (.leaf (1,304,126,[(9,0),(10,0),(0,1),(18,0),(7,1),(24,0),(16,0),(36,0),(64,0),(13,0),(38,0)])))) (.node (.leaf (1,816,118,[(8,1),(32,0),(4,0),(7,1),(0,1)])) (.node (.leaf (1,816,126,[(32,0),(8,1),(47,0),(40,0),(4,0),(51,0),(34,0),(13,0),(36,0)])) (.leaf (1,320,126,[(0,0),(8,0),(47,0),(14,0),(18,0),(27,0),(4,0),(16,0),(36,0)]))))) (.node (.node (.leaf (1,832,110,[(0,0),(8,0)])) (.node (.leaf (1,289,125,[(7,0),(16,1),(0,0),(32,0),(9,0),(17,0),(13,0),(36,0)])) (.leaf (1,545,121,[(8,0),(16,1),(5,0)])))) (.node (.node (.leaf (1,545,125,[(8,0),(16,1),(38,0),(32,0),(9,0),(5,0),(13,0),(3,0),(36,0)])) (.leaf (1,49,125,[(7,0),(16,1),(8,0),(4,0),(5,0),(38,0),(34,0),(3,0),(36,0)]))) (.node (.leaf (1,305,125,[(16,1),(9,0),(32,0),(18,0),(3,1),(24,0),(13,0),(4,0),(36,0),(3,0)])) (.leaf (1,305,119,[(7,0),(16,1),(8,0),(39,0),(5,0)])))))) (.node (.node (.node (.leaf (1,305,127,[(7,0),(16,1),(8,0),(29,0),(20,0),(5,0),(39,0),(4,0),(24,0)])) (.node (.leaf (1,561,117,[(7,0),(16,1),(8,0)])) (.leaf (1,561,125,[(7,0),(16,1),(8,0),(4,0),(29,0),(5,0),(38,0),(3,0),(36,0)])))) (.node (.node (.leaf (1,817,117,[(16,1),(32,0),(0,1)])) (.leaf (1,817,125,[(32,0),(16,1),(47,0),(0,1),(51,0),(34,0),(36,0)]))) (.node (.leaf (1,817,119,[(7,0),(8,0),(16,1),(39,0),(5,0)])) (.leaf (1,817,127,[(32,0),(8,0),(16,1),(7,0),(5,0),(39,0),(4,0),(34,0),(51,0)]))))) (.node (.node (.leaf (1,321,125,[(8,0),(16,1),(0,0),(47,0),(18,0),(27,0),(4,0),(13,0),(36,0)])) (.node (.leaf (1,321,111,[(8,0),(16,1),(7,0),(5,0),(39,0),(40,0),(3,0),(4,0)])) (.leaf (1,577,109,[(7,0),(16,1),(5,0),(4,0)])))) (.node (.node (.leaf (1,577,125,[(7,0),(16,1),(3,0),(47,0),(18,0),(27,0),(5,0),(13,0),(38,0),(4,0),(36,0)])) (.leaf (1,833,109,[(0,0),(16,1),(4,0)]))) (.node (.leaf (1,833,111,[(7,0),(16,1),(3,0),(5,0),(39,0),(40,0),(13,0),(0,0),(4,0)])) (.leaf (1,81,125,[(8,0),(16,1),(7,0),(36,0),(51,0),(24,0),(38,0),(4,0),(3,0)]))))))) (.node (.node (.node (.node (.leaf (1,337,125,[(80,0),(16,1),(5,0),(0,1),(27,0),(13,0),(4,0),(3,0)])) (.node (.leaf (1,337,95,[(7,0),(16,1),(8,0),(40,0),(5,0),(4,0)])) (.leaf (1,337,127,[(5,0),(7,0),(16,1),(8,0),(34,0),(64,0),(36,0),(40,0),(4,0)])))) (.node (.leaf (1,593,93,[(7,0),(16,1),(8,0)])) (.node (.leaf (1,593,125,[(8,0),(16,1),(7,0),(36,0),(34,0),(38,0),(4,0),(3,0)])) (.leaf (1,849,93,[(16,1),(0,1),(36,0),(3,0)]))))) (.node (.node (.leaf (1,849,125,[(36,0),(16,1),(0,1),(47,0),(17,0),(51,0),(24,0),(4,0),(3,0)])) (.node (.leaf (1,849,95,[(7,0),(16,1),(8,0),(40,0),(4,0)])) (.leaf (1,849,127,[(7,0),(36,0),(16,1),(8,0),(24,0),(40,0),(51,0),(4,0)])))) (.node (.node (.leaf (1,67,111,[(8,0),(16,1),(0,0),(4,0),(51,0),(34,0),(13,0),(38,0),(36,0)])) (.leaf (1,323,119,[(0,0),(16,1),(8,0),(27,0),(36,0),(31,0)]))) (.node (.leaf (1,323,111,[(64,0),(16,1),(32,0),(9,0),(13,0),(3,0),(4,0),(36,0),(38,0)])) (.leaf (1,323,127,[(8,0),(16,1),(0,0),(29,0),(4,0),(27,0),(24,0),(56,0),(36,0)])))))) (.node (.node (.node (.leaf (1,579,103,[(16,1),(7,1),(32,0)])) (.node (.leaf (1,579,119,[(0,0),(8,0),(16,1),(27,0),(4,0),(36,0)])) (.leaf (1,579,111,[(32,0),(16,1),(51,0),(7,1),(40,0),(34,0),(38,0),(36,0)])))) (.node (.node (.leaf (1,579,127,[(32,0),(8,0),(16,1),(0,0),(27,0),(51,0),(4,0),(34,0),(36,0)])) (.leaf (1,835,103,[(0,0),(16,1),(8,0)]))) (.node (.leaf (1,835,111,[(0,0),(16,1),(8,0),(4,0),(24,0),(13,0),(38,0),(36,0)])) (.leaf (1,83,119,[(5,0),(16,1),(0,1),(17,0),(3,1),(38,1),(13,0),(38,0),(3,0)]))))) (.node (.node (.leaf (1,83,127,[(5,0),(32,0),(16,1),(3,1),(47,0),(4,0),(36,0),(13,0),(38,0),(3,0)])) (.node (.leaf (1,339,119,[(16,1),(39,0),(8,1),(36,0),(27,0),(38,1),(38,0),(35,0)])) (.leaf (1,339,127,[(16,1),(51,0),(39,0),(9,0),(13,1),(38,1),(3,1),(27,0),(4,0),(36,0),(18,0),(13,0),(38,0),(3,0)])))) (.node (.node (.leaf (1,595,87,[(16,1),(8,1),(32,0),(7,1),(0,1)])) (.leaf (1,595,119,[(16,1),(39,0),(8,1),(36,0),(27,0),(38,1),(13,0),(38,0),(32,0),(3,0)]))) (.node (.leaf (1,595,95,[(32,0),(16,1),(8,1),(40,0),(3,1),(7,1),(13,0)])) (.leaf (1,595,127,[(32,0),(16,1),(39,0),(13,1),(3,1),(36,0),(27,0),(4,0),(40,0),(13,0),(38,0),(3,0)])))))))
def cG6M7 : BST := .node 7921675399566312510 293 0 (.node 6808545244974027618 285 0 (.node 5880301350696988829 73 0 (.node 5345853990754579226 274 0 (.node 5092136854207696627 138 1 (.node 4830289616100930367 258 0 (.node 4052187267502083388 950 0 (.node 3552700320546144197 950 1 (.node 3423615689979801723 306 0 (.node 3361460598046464056 74 0 (.nil) (.nil)) (.node 3538831384318175660 181 0 (.nil) (.nil))) (.node 3753907686159463024 201 0 (.node 3574464642200015580 905 0 (.nil) (.nil)) (.nil))) (.node 4750563674336645999 117 0 (.node 4621210348382912497 465 1 (.node 4163833780637910414 969 0 (.nil) (.nil)) (.node 4655722717096177068 485 0 (.nil) (.nil))) (.node 4789388189929542328 955 1 (.node 4760845061413357145 34 0 (.nil) (.nil)) (.nil)))) (.node 4950439589123384155 238 1 (.node 4872377966450545836 930 0 (.node 4842580520483543091 886 0 (.node 4835223894785010218 146 0 (.nil) (.nil)) (.node 4855207645080595135 228 1 (.nil) (.nil))) (.node 4936713081811242404 1013 0 (.node 4925727894416849134 467 0 (.nil) (.nil)) (.nil))) (.node 5004280810883528598 994 0 (.node 4985093298140687168 465 0 (.node 4951357988397473189 150 1 (.nil) (.nil)) (.node 4988028935843009512 282 0 (.nil) (.nil))) (.node 5083839308156007401 501 0 (.node 5004545905594054202 398 1 (.nil) (.nil)) (.nil))))) (.node 5211722195032631708 409 0 (.node 5160489768815093389 373 0 (.node 5137770373429082554 434 0 (.node 5131706746581768427 225 1 (.node 5113856051161770613 474 1 (.nil) (.nil)) (.node 5136398927318267004 314 0 (.nil) (.nil))) (.node 5158165189976025677 341 0 (.node 5146017413529930855 997 0 (.nil) (.nil)) (.nil))) (.node 5196932774889051656 403 0 (.node 5180857430873135609 478 0 (.node 5176067647102583890 429 0 (.nil) (.nil)) (.node 5190082014960707460 138 0 (.nil) (.nil))) (.node 5199994841774402391 488 0 (.node 5199314284407989718 123 1 (.nil) (.nil)) (.nil)))) (.node 5282304060928993226 98 0 (.node 5250390879786754850 921 0 (.node 5222392539597099184 210 0 (.node 5211731936705651140 453 0 (.nil) (.nil)) (.node 5227778965919375844 22 1 (.nil) (.nil))) (.node 5262803478375639321 301 0 (.node 5252506614961990481 246 1 (.nil) (.nil)) (.nil))) (.node 5305825251326124109 401 1 (.node 5303647169087107867 374 1 (.node 5294204153519100186 177 0 (.nil) (.nil)) (.nil)) (.node 5337608233935473121 469 0 (.node 5307141716610794366 334 1 (.nil) (.nil)) (.nil)))))) (.node 5571440696461727497 297 0 (.node 5476198632709312746 29 1 (.node 5407845718101915984 170 1 (.node 5386676234016671247 995 0 (.node 5367880443418068405 894 0 (.node 5349702854171974592 174 0 (.nil) (.nil)) (.node 5371655267073740338 153 0 (.nil) (.nil))) (.node 5406802043352954879 456 0 (.node 5392780508827183899 182 0 (.nil) (.nil)) (.nil))) (.node 5456143305583716908 50 0 (.node 5414206905361975988 18 0 (.node 5411603601364372200 878 1 (.nil) (.nil)) (.node 5445063959007420278 118 1 (.nil) (.nil))) (.node 5472704085185626247 105 0 (.node 5463499931282249781 910 0 (.nil) (.nil)) (.nil)))) (.node 5544225082015085436 315 0 (.node 5511372769939749389 361 0 (.node 5498462271649058915 114 0 (.node 5485820507787120911 368 0 (.nil) (.nil)) (.node 5509227344522935370 362 0 (.nil) (.nil))) (.node 5531655194831758088 906 0 (.node 5519172629319120660 336 0 (.nil) (.nil)) (.nil))) (.node 5557841314073243802 48 0 (.node 5553305116576701768 266 1 (.node 5546325021796714394 294 0 (.nil) (.nil)) (.node 5555943508008378245 21 0 (.nil) (.nil))) (.node 5566899013571539581 438 0 (.node 5563090761429133724 350 0 (.nil) (.nil)) (.nil))))) (.node 5736809024175307845 206 0 (.node 5667297306543437305 330 0 (.node 5641392030869643338 170 0 (.node 5619329202217013722 505 0 (.node 5614120875105938658 945 0 (.nil) (.nil)) (.node 5639675259774079447 414 0 (.nil) (.nil))) (.node 5642197371719162974 882 0 (.node 5641944509660895770 298 0 (.nil) (.nil)) (.nil))) (.node 5690815813899196833 233 0 (.node 5682879132042599722 390 1 (.node 5673127064416738947 217 0 (.nil) (.nil)) (.node 5683477143717943997 945 1 (.nil) (.nil))) (.node 5731936184727972707 974 0 (.node 5694458235498010866 418 0 (.nil) (.nil)) (.nil)))) (.node 5820529236231738510 977 1 (.node 5788161072933750672 131 0 (.node 5768192893232241476 231 0 (.node 5747534328413920511 981 0 (.nil) (.nil)) (.node 5777806537896515795 161 0 (.nil) (.nil))) (.node 5817771812580363374 426 1 (.node 5798772246176461166 1017 0 (.nil) (.nil)) (.nil))) (.node 5860745809190171288 464 0 (.node 5856517346200420342 234 0 (.node 5844147031985612288 380 1 (.nil) (.nil)) (.nil)) (.node 5873525393044459692 142 0 (.node 5872873546969444739 94 0 (.nil) (.nil)) (.nil))))))) (.node 6433516170423507122 508 1 (.node 6227312088085713505 1018 0 (.node 6066262629895758968 977 0 (.node 6023590075945059732 252 1 (.node 5974202217829182566 74 1 (.node 5944550905963359469 118 0 (.node 5929098723797568050 208 0 (.nil) (.nil)) (.node 5966339939605738398 6 0 (.nil) (.nil))) (.node 6003956517856123803 54 0 (.node 5998748326761078715 85 0 (.nil) (.nil)) (.nil))) (.node 6052362057230754015 286 0 (.node 6042555132436579328 22 0 (.node 6031970533371826458 389 0 (.nil) (.nil)) (.node 6048867509707067516 446 0 (.nil) (.nil))) (.node 6065983369806126968 497 0 (.node 6059744394656436273 457 0 (.nil) (.nil)) (.nil)))) (.node 6147051527102539774 188 1 (.node 6120114152863463491 258 1 (.node 6100741908377644223 489 0 (.node 6066958720435655328 182 1 (.nil) (.nil)) (.node 6111503209714113056 438 1 (.nil) (.nil))) (.node 6135922094452368690 145 1 (.node 6128938204073918031 904 0 (.nil) (.nil)) (.nil))) (.node 6200378384300104004 409 1 (.node 6147239921727060045 994 1 (.node 6147210452511138636 944 0 (.nil) (.nil)) (.node 6192568867659042533 202 0 (.nil) (.nil))) (.node 6215404441709936536 444 1 (.node 6208698340654908556 5 0 (.nil) (.nil)) (.nil))))) (.node 6323692498518231295 1016 1 (.node 6274973498078086062 878 0 (.node 6260666861150149914 86 0 (.node 6236750188202507070 140 0 (.node 6236015636534173708 225 0 (.nil) (.nil)) (.node 6239747524962396830 98 1 (.nil) (.nil))) (.node 6272029644634369883 494 0 (.node 6267616872379553189 482 0 (.nil) (.nil)) (.nil))) (.node 6310958393003594477 137 0 (.node 6280006285342752593 450 1 (.node 6277453318261089637 269 0 (.nil) (.nil)) (.node 6280560125812631436 401 0 (.nil) (.nil))) (.node 6319228810566754578 913 0 (.node 6312877641004679594 336 1 (.nil) (.nil)) (.nil)))) (.node 6408163471334737033 163 1 (.node 6338872429084613731 63 0 (.node 6331049124216764168 916 1 (.node 6329608599726889947 389 1 (.nil) (.nil)) (.node 6334137043154437459 498 0 (.nil) (.nil))) (.node 6384128312307629956 330 1 (.node 6382832566717927126 185 1 (.nil) (.nil)) (.nil))) (.node 6408442735497760345 883 1 (.node 6408313683972475517 146 1 (.node 6408165438399677825 419 0 (.nil) (.nil)) (.nil)) (.node 6409580300808650547 162 0 (.node 6409226922403324033 163 0 (.nil) (.nil)) (.nil)))))) (.node 6657358848964321547 408 0 (.node 6509493702595410157 20 1 (.node 6475067998201675731 313 1 (.node 6458793604185514906 321 0 (.node 6440875067933208866 14 0 (.node 6438908192856605232 44 1 (.nil) (.nil)) (.node 6441512822931150762 62 0 (.nil) (.nil))) (.node 6470222549167617535 114 1 (.node 6469670489134883663 41 0 (.nil) (.nil)) (.nil))) (.node 6493014509327275279 308 1 (.node 6488311280060003612 458 0 (.node 6486837556945492353 952 0 (.nil) (.nil)) (.node 6488384378339326032 240 0 (.nil) (.nil))) (.node 6498671854526202022 81 0 (.node 6494417627136767638 214 0 (.nil) (.nil)) (.nil)))) (.node 6610358246229989745 942 0 (.node 6559621911030654606 322 0 (.node 6542396355755599819 1021 0 (.node 6518193359007910559 201 1 (.nil) (.nil)) (.node 6548007132123475499 474 0 (.nil) (.nil))) (.node 6586758262351121506 274 1 (.node 6560086350131576404 188 0 (.nil) (.nil)) (.nil))) (.node 6621385138111583124 249 0 (.node 6617890590587896625 169 0 (.node 6610922489213198213 158 1 (.nil) (.nil)) (.nil)) (.node 6637871124318988381 0 1 (.node 6627892283808085325 479 0 (.nil) (.nil)) (.nil))))) (.node 6717492827817429526 305 0 (.node 6681751828390818409 135 1 (.node 6679370318871880347 195 0 (.node 6672033826718339587 238 0 (.node 6661737316734817391 905 1 (.nil) (.nil)) (.node 6672997667772297794 277 0 (.nil) (.nil))) (.node 6679713044138453643 375 0 (.node 6679433779849693347 119 0 (.nil) (.nil)) (.nil))) (.node 6703724644689092216 86 1 (.node 6687471802076379808 885 1 (.node 6684730168770665326 956 1 (.nil) (.nil)) (.node 6687878131234362018 993 0 (.nil) (.nil))) (.node 6716316906027451129 973 0 (.node 6710852079175019319 282 1 (.nil) (.nil)) (.nil)))) (.node 6779979405311716593 109 1 (.node 6752395981628741055 464 1 (.node 6736040146681650838 937 0 (.node 6720884487482041867 393 0 (.nil) (.nil)) (.node 6740975218695211558 84 1 (.nil) (.nil))) (.node 6779488648223276900 502 1 (.node 6763282153831408860 284 0 (.nil) (.nil)) (.nil))) (.node 6793372677017272330 962 0 (.node 6792115772820328944 484 1 (.node 6781770930095840481 81 1 (.nil) (.nil)) (.nil)) (.node 6806500313619744913 955 0 (.node 6795316151929270767 82 0 (.nil) (.nil)) (.nil)))))))) (.node 7356142829833157862 158 0 (.node 7071207115276371855 43 0 (.node 6951475707121726789 16 0 (.node 6869336936110881514 311 0 (.node 6829786049501823155 272 0 (.node 6818368825777079439 351 1 (.node 6818091532878125215 75 0 (.node 6817045817542277762 885 0 (.nil) (.nil)) (.node 6818100728142880803 102 0 (.nil) (.nil))) (.node 6819251371119343176 240 1 (.node 6819153016881771423 907 0 (.nil) (.nil)) (.nil))) (.node 6856684831853961207 265 0 (.node 6839357588740381299 443 0 (.node 6835601281737488584 970 0 (.nil) (.nil)) (.node 6843996578958915171 57 0 (.nil) (.nil))) (.node 6869113777999499938 67 0 (.node 6856723550334072705 190 0 (.nil) (.nil)) (.nil)))) (.node 6924937063582743321 230 0 (.node 6900072205097593277 972 1 (.node 6870050243445330913 314 1 (.node 6869616200399641810 183 0 (.nil) (.nil)) (.node 6895343826641065125 312 0 (.nil) (.nil))) (.node 6909062663689174854 502 0 (.node 6908597949004649412 337 0 (.nil) (.nil)) (.nil))) (.node 6938860109656177599 914 0 (.node 6928119453486357949 457 1 (.node 6925314887822747313 913 1 (.nil) (.nil)) (.node 6933532562740641355 356 1 (.nil) (.nil))) (.node 6950548963745359721 1015 0 (.node 6950269699456599425 503 0 (.nil) (.nil)) (.nil))))) (.node 7023076663782215853 910 1 (.node 6977336764853304626 482 1 (.node 6958979131939869579 470 0 (.node 6956280517597014884 965 0 (.node 6951680940699608745 379 1 (.nil) (.nil)) (.node 6957933226601922889 70 0 (.nil) (.nil))) (.node 6962765496295204279 319 0 (.node 6961559425593150317 149 0 (.nil) (.nil)) (.nil))) (.node 7008700807245550781 206 1 (.node 6997811869736526883 151 0 (.node 6986930875382279992 996 1 (.nil) (.nil)) (.node 6998091134025287179 271 1 (.nil) (.nil))) (.node 7020747435895741210 925 0 (.node 7014773672342169876 302 0 (.nil) (.nil)) (.nil)))) (.node 7042808717236261302 421 0 (.node 7034670717220612253 354 0 (.node 7028616258688645795 104 0 (.node 7024445127594650245 428 0 (.nil) (.nil)) (.node 7029044981947430436 394 1 (.nil) (.nil))) (.node 7042770391109143594 77 0 (.node 7036209377784221789 186 0 (.nil) (.nil)) (.nil))) (.node 7059997235324503649 194 1 (.node 7057445091736918925 26 1 (.node 7056400382833619248 373 1 (.nil) (.nil)) (.nil)) (.node 7067443667779426215 967 0 (.node 7066103463402566858 25 0 (.nil) (.nil)) (.nil)))))) (.node 7226971912020725152 245 0 (.node 7150321451361639164 13 0 (.node 7095069067587742390 109 0 (.node 7089359874328140737 399 1 (.node 7079530146423170977 923 0 (.node 7071663411213264781 73 1 (.nil) (.nil)) (.node 7089296413350327737 947 0 (.nil) (.nil))) (.node 7094789807498110390 1005 0 (.node 7094789803298982094 473 0 (.nil) (.nil)) (.nil))) (.node 7117765558612869418 929 0 (.node 7112975774842317699 189 0 (.node 7108729823443825950 105 1 (.nil) (.nil)) (.node 7113406759544182123 192 1 (.nil) (.nil))) (.node 7148417228980516340 246 0 (.node 7126990142700441269 902 0 (.nil) (.nil)) (.nil)))) (.node 7187018142398451123 17 0 (.node 7161044353577568384 300 1 (.node 7158328887386522019 154 0 (.node 7155442522008264667 916 0 (.nil) (.nil)) (.node 7158618997413328390 902 1 (.nil) (.nil))) (.node 7186567791980376267 1009 0 (.node 7167405574119624226 203 0 (.nil) (.nil)) (.nil))) (.node 7189571250790401603 290 0 (.node 7189414742701724290 1014 1 (.node 7187029308900120243 26 0 (.nil) (.nil)) (.node 7189517931911598630 366 0 (.nil) (.nil))) (.node 7203052330629320225 94 1 (.node 7201962154954658012 938 0 (.nil) (.nil)) (.nil))))) (.node 7267233973755054915 423 0 (.node 7231844081888853407 259 0 (.node 7231289421220652471 167 1 (.node 7230524971735903151 979 0 (.node 7230231103987504724 1002 0 (.nil) (.nil)) (.node 7231001884951094711 251 0 (.nil) (.nil))) (.node 7231564602913822383 51 0 (.node 7231562631676908851 209 0 (.nil) (.nil)) (.nil))) (.node 7256564158166339223 394 0 (.node 7242549790308215653 941 0 (.node 7241056907599168696 185 0 (.nil) (.nil)) (.node 7249025872282813383 115 1 (.nil) (.nil))) (.node 7266649644812520095 65 0 (.node 7263414918094683419 83 0 (.nil) (.nil)) (.nil)))) (.node 7325209098354254324 953 0 (.node 7314581512550621969 223 0 (.node 7279263030589328904 399 0 (.node 7279039872477947328 179 0 (.nil) (.nil)) (.node 7286610981911708401 1022 0 (.nil) (.nil))) (.node 7323584361756405056 275 0 (.node 7320457940746092094 213 0 (.nil) (.nil)) (.nil))) (.node 7345101871414011855 38 0 (.node 7343705920964671592 40 0 (.node 7336638427688530167 402 0 (.nil) (.nil)) (.nil)) (.node 7355863569743525862 78 0 (.node 7355863565544397566 370 0 (.nil) (.nil)) (.nil))))))) (.node 7565368616486712057 172 0 (.node 7451854122026904104 917 0 (.node 7383499379461706761 442 0 (.node 7361966820071282025 404 1 (.node 7358649775455851804 162 1 (.node 7356818973842150785 152 0 (.node 7356420210614474774 398 0 (.nil) (.nil)) (.node 7358363355210437613 310 0 (.nil) (.nil))) (.node 7361607035178056135 891 1 (.node 7360195793935046815 79 0 (.nil) (.nil)) (.nil))) (.node 7373298167110285663 1008 0 (.node 7369803585689241422 374 0 (.node 7363168122860906189 236 0 (.nil) (.nil)) (.node 7370189438559696423 232 0 (.nil) (.nil))) (.node 7374480521789597595 448 1 (.node 7373508191020781207 343 0 (.nil) (.nil)) (.nil)))) (.node 7424720208319026991 971 0 (.node 7410777931481961747 167 0 (.node 7401590982984211451 490 0 (.node 7395869452057639747 379 0 (.nil) (.nil)) (.node 7407737964214974273 87 1 (.nil) (.nil))) (.node 7419692759658743862 70 1 (.node 7411737297993500742 901 0 (.nil) (.nil)) (.nil))) (.node 7442079804976467066 134 0 (.node 7426718052686492189 276 0 (.node 7425746631214901814 273 0 (.nil) (.nil)) (.node 7436588720476361517 7 0 (.nil) (.nil))) (.node 7446135472262669179 422 0 (.node 7444596811699059643 226 0 (.nil) (.nil)) (.nil))))) (.node 7501729852208105673 915 0 (.node 7480478753388834105 216 0 (.node 7477369762257873605 39 0 (.node 7455454399890409805 222 0 (.node 7453751928091769661 976 0 (.nil) (.nil)) (.node 7458682485516188030 1010 0 (.nil) (.nil))) (.node 7479926274597581673 472 0 (.node 7478085744570003963 449 1 (.nil) (.nil)) (.nil))) (.node 7489456240901618367 91 1 (.node 7486694139370108858 990 0 (.node 7481133209754819245 187 0 (.nil) (.nil)) (.node 7488223790921749758 450 0 (.nil) (.nil))) (.node 7499998889168867533 417 0 (.node 7489845414602386962 1017 1 (.nil) (.nil)) (.nil)))) (.node 7533706759751784861 298 1 (.node 7507710398742555126 29 0 (.node 7505618889064006991 410 0 (.node 7503832097438283439 267 0 (.nil) (.nil)) (.node 7505831550271375640 1000 0 (.nil) (.nil))) (.node 7517568645202624389 933 0 (.node 7508348824201461306 281 0 (.nil) (.nil)) (.nil))) (.node 7543896187308656027 145 0 (.node 7535078677342833358 476 1 (.node 7534308143923043555 342 0 (.nil) (.nil)) (.nil)) (.node 7556237329956747531 357 0 (.node 7555427324168876405 932 1 (.nil) (.nil)) (.nil)))))) (.node 7705642510351905475 932 0 (.node 7647142660668522343 441 0 (.node 7604779683210087064 264 0 (.node 7596513688277231315 252 0 (.node 7576583387513813256 289 0 (.node 7573276652125856661 993 1 (.nil) (.nil)) (.node 7577331668598071616 59 0 (.nil) (.nil))) (.node 7600040862016073435 433 0 (.node 7599971813447334133 100 1 (.nil) (.nil)) (.nil))) (.node 7624299823189248788 46 0 (.node 7618631707364652376 412 0 (.node 7616183444008331235 228 0 (.nil) (.nil)) (.node 7623185600496776417 210 1 (.nil) (.nil))) (.node 7633389372329293794 505 1 (.node 7629172662636583926 462 0 (.nil) (.nil)) (.nil)))) (.node 7669348871463464078 214 1 (.node 7666072617977833675 20 0 (.node 7658951966761260773 371 1 (.node 7655539562668947841 430 0 (.nil) (.nil)) (.node 7660921869951786717 248 1 (.nil) (.nil))) (.node 7668844312467706516 254 0 (.node 7668689101894346820 325 0 (.nil) (.nil)) (.nil))) (.node 7689464998467971900 236 1 (.node 7673561321076268467 193 0 (.node 7670455784559854963 453 1 (.nil) (.nil)) (.nil)) (.node 7703153567221882538 218 0 (.node 7691473311335725264 19 0 (.nil) (.nil)) (.nil))))) (.node 7819868020796727208 921 1 (.node 7768784160987970598 334 0 (.node 7740057646004138147 380 0 (.node 7719313195964088234 89 0 (.node 7712638751849928128 968 0 (.nil) (.nil)) (.node 7725698618706779060 345 0 (.nil) (.nil))) (.node 7768297004402175502 1006 0 (.node 7754090622437406042 348 1 (.nil) (.nil)) (.nil))) (.node 7801714729689512892 404 0 (.node 7797541920650321996 178 0 (.node 7792120962658375556 55 0 (.nil) (.nil)) (.node 7800036204353751113 946 0 (.nil) (.nil))) (.node 7805972487193673002 10 0 (.node 7804874183333676733 200 0 (.nil) (.nil)) (.nil)))) (.node 7879761015096261157 100 0 (.node 7833590473482321497 406 0 (.node 7832658307478650186 197 0 (.node 7820491008518465710 116 0 (.nil) (.nil)) (.node 7833398668588759971 47 0 (.nil) (.nil))) (.node 7876156073042016566 405 0 (.node 7863678022570217051 304 0 (.nil) (.nil)) (.nil))) (.node 7893306236929691443 504 0 (.node 7886905743242640487 469 1 (.node 7883901153806911677 400 0 (.nil) (.nil)) (.nil)) (.node 7913018134267892149 889 0 (.node 7912246547998317819 393 1 (.nil) (.nil)) (.nil))))))))) (.node 8992823035909931236 147 0 (.node 8554793423265635375 42 0 (.node 8211881625817819871 449 0 (.node 8042594101467055246 329 0 (.node 7968494856192437181 257 0 (.node 7945511968271052696 926 0 (.node 7932367277501302798 48 1 (.node 7924886646425226675 437 0 (.node 7923147538535924422 220 1 (.nil) (.nil)) (.node 7928585693361554256 270 0 (.nil) (.nil))) (.node 7943503602670426704 320 1 (.node 7938826666570070531 937 1 (.nil) (.nil)) (.nil))) (.node 7950807863572404399 441 1 (.node 7947228739366616587 426 0 (.node 7945669305777742295 408 1 (.nil) (.nil)) (.node 7948034080216136223 242 0 (.nil) (.nil))) (.node 7968391504525765171 37 0 (.node 7952537261298801023 1004 0 (.nil) (.nil)) (.nil)))) (.node 8002971507896928235 322 1 (.node 7990100443355101950 960 0 (.node 7980400109718018470 390 0 (.node 7977134431209228329 150 0 (.nil) (.nil)) (.node 7985663493610402910 999 0 (.nil) (.nil))) (.node 8000147069919856581 103 0 (.node 7999824429856248656 355 0 (.nil) (.nil)) (.nil))) (.node 8030449700969547319 341 1 (.node 8015293313321290031 986 0 (.node 8006439782755678705 1020 0 (.nil) (.nil)) (.node 8026109538486778625 300 0 (.nil) (.nil))) (.node 8037617682651586260 985 0 (.node 8036475735856696576 276 1 (.nil) (.nil)) (.nil))))) (.node 8100757362751813985 68 0 (.node 8081653982281707095 468 0 (.node 8071872558005705509 295 1 (.node 8049671025700029421 436 0 (.node 8049515194861256234 332 0 (.nil) (.nil)) (.node 8065846331813651840 72 0 (.nil) (.nil))) (.node 8080381879038302353 933 1 (.node 8079107441006870305 396 0 (.nil) (.nil)) (.nil))) (.node 8099391092946419290 492 1 (.node 8093630455958625293 425 0 (.node 8091518349664993054 303 0 (.nil) (.nil)) (.node 8093732069724065658 958 0 (.nil) (.nil))) (.node 8100747621078794553 900 0 (.node 8100730781877332727 175 0 (.nil) (.nil)) (.nil)))) (.node 8149983740482585537 892 0 (.node 8132545523362826189 898 0 (.node 8116372456989196746 466 0 (.node 8109974125183916424 266 0 (.nil) (.nil)) (.node 8125047049262032231 497 1 (.nil) (.nil))) (.node 8149856892972267163 477 0 (.node 8136328538467465578 290 1 (.nil) (.nil)) (.nil))) (.node 8171975518590338206 951 0 (.node 8170578703029232608 112 0 (.node 8164507876256035817 306 1 (.nil) (.nil)) (.nil)) (.node 8208937772374103692 961 0 (.node 8173802764090916173 328 0 (.nil) (.nil)) (.nil)))))) (.node 8371694855076285719 0 0 (.node 8329426784442032981 1020 1 (.node 8265902553933363532 194 0 (.node 8251361068267014785 295 0 (.node 8228555380665825385 49 0 (.node 8212443955666006074 52 0 (.nil) (.nil)) (.node 8238237200811950219 220 0 (.nil) (.nil))) (.node 8257412907488081045 356 0 (.node 8252577234307726150 171 0 (.nil) (.nil)) (.nil))) (.node 8290603980323551950 261 0 (.node 8272176648102711647 262 0 (.node 8267957251956497977 340 1 (.nil) (.nil)) (.node 8276089481089733021 386 0 (.nil) (.nil))) (.node 8321795132723209990 155 0 (.node 8302690425109282122 475 0 (.nil) (.nil)) (.nil)))) (.node 8356404586389387617 369 0 (.node 8340318323670498969 510 0 (.node 8334702424593918680 939 0 (.node 8331601494044759900 165 0 (.nil) (.nil)) (.node 8337320085283004611 377 0 (.nil) (.nil))) (.node 8355595400256189685 920 1 (.node 8342293371979750188 304 1 (.nil) (.nil)) (.nil))) (.node 8363289145504817240 414 1 (.node 8362583314998775003 58 0 (.node 8361729511231789092 388 0 (.nil) (.nil)) (.node 8363083911926935284 448 0 (.nil) (.nil))) (.node 8370780442926052689 113 0 (.node 8365224058755475591 364 0 (.nil) (.nil)) (.nil))))) (.node 8446401830335143966 148 1 (.node 8425292506079059841 496 0 (.node 8380538204388464648 463 0 (.node 8377783195672942675 382 0 (.node 8374912749241580897 278 0 (.nil) (.nil)) (.node 8378420950670884571 353 0 (.nil) (.nil))) (.node 8425219407799737421 326 0 (.node 8395589588088850300 919 1 (.nil) (.nil)) (.nil))) (.node 8429748442461622956 168 0 (.node 8426557134782930114 205 0 (.node 8426404718004488192 444 0 (.nil) (.nil)) (.node 8428228019001899887 181 1 (.nil) (.nil))) (.node 8445203040278032970 943 0 (.node 8440318814037731089 384 0 (.nil) (.nil)) (.nil)))) (.node 8503146301152101503 132 0 (.node 8497169410978771858 436 1 (.node 8453076630224033294 18 1 (.node 8452952431692584479 24 0 (.nil) (.nil)) (.node 8473877667366992572 988 1 (.nil) (.nil))) (.node 8500552627686099544 313 0 (.node 8499310963057365691 348 0 (.nil) (.nil)) (.nil))) (.node 8539789559937263563 912 0 (.node 8532140828025453664 192 0 (.node 8505567978219786610 92 0 (.nil) (.nil)) (.nil)) (.node 8547266373969723554 129 0 (.node 8544293783656187635 34 1 (.nil) (.nil)) (.nil))))))) (.node 8738265685624095944 884 0 (.node 8655645792292684941 156 0 (.node 8589352438313898495 928 1 (.node 8571008647839006018 247 0 (.node 8570735482068698466 151 1 (.node 8564800411547819134 991 0 (.node 8563706725424601246 120 0 (.nil) (.nil)) (.node 8566115517417827134 919 0 (.nil) (.nil))) (.node 8570809512779576806 160 0 (.node 8570735486267826762 499 1 (.nil) (.nil)) (.nil))) (.node 8584675502213542322 233 1 (.node 8571571431903106154 367 0 (.node 8571014746357458762 271 0 (.nil) (.nil)) (.node 8580640782789191185 956 0 (.nil) (.nil))) (.node 8588809827271148279 50 1 (.node 8587835499602807638 972 0 (.nil) (.nil)) (.nil)))) (.node 8618714349501652843 208 1 (.node 8611516712827564238 56 1 (.node 8609856466278705607 241 0 (.node 8608680544488727210 45 0 (.nil) (.nil)) (.node 8611339528256966046 60 1 (.nil) (.nil))) (.node 8613182955884418890 483 0 (.node 8611547736307084238 440 0 (.nil) (.nil)) (.nil))) (.node 8636885832713737417 172 1 (.node 8632016377778092340 104 1 (.node 8621769903162112787 949 0 (.nil) (.nil)) (.node 8634564676183044762 38 1 (.nil) (.nil))) (.node 8653225033767184938 61 0 (.node 8644709137581586980 383 0 (.nil) (.nil)) (.nil))))) (.node 8713239808617686066 883 0 (.node 8693501822085533402 144 0 (.node 8677883346434945367 212 1 (.node 8673867799122085589 130 0 (.node 8665256855972735154 894 1 (.nil) (.nil)) (.node 8675840562051709226 244 0 (.nil) (.nil))) (.node 8685310920647808438 378 0 (.node 8681001176321834618 980 0 (.nil) (.nil)) (.nil))) (.node 8700908883435303699 157 0 (.node 8700530074801999340 133 0 (.node 8698863952081020994 135 0 (.nil) (.nil)) (.node 8700748007430394986 235 0 (.nil) (.nil))) (.node 8712962515718731842 931 0 (.node 8712616519587729512 455 0 (.nil) (.nil)) (.nil)))) (.node 8715411416875583602 431 0 (.node 8714002146896651074 99 0 (.node 8714000179831710282 907 1 (.node 8713998242108689276 173 0 (.nil) (.nil)) (.node 8714001140464103298 102 1 (.nil) (.nil))) (.node 8714279439795605298 351 0 (.node 8714011342161406662 122 0 (.nil) (.nil)) (.nil))) (.node 8728219459940449154 361 1 (.node 8721175685497197093 1016 0 (.node 8719852715044322854 427 0 (.nil) (.nil)) (.nil)) (.node 8732896396040805327 160 1 (.node 8731721227201657380 263 0 (.nil) (.nil)) (.nil)))))) (.node 8855945735003609898 279 0 (.node 8806245063850615323 439 0 (.node 8755408282579788794 476 0 (.node 8749755189525205263 204 0 (.node 8745453372713761427 509 0 (.node 8739352878920480371 2 1 (.nil) (.nil)) (.node 8745915923055325110 887 0 (.nil) (.nil))) (.node 8753729576047503660 309 0 (.node 8750252556739024250 928 0 (.nil) (.nil)) (.nil))) (.node 8783084550692339111 996 0 (.node 8773215239983264630 926 1 (.node 8757213137248791143 954 0 (.nil) (.nil)) (.node 8777334222380651082 230 1 (.nil) (.nil))) (.node 8805078413479211659 880 0 (.node 8787707465102341206 184 0 (.nil) (.nil)) (.nil)))) (.node 8844501112394341733 352 0 (.node 8836483229261377504 461 0 (.node 8819849230049753561 934 0 (.node 8819651599734387964 88 0 (.nil) (.nil)) (.node 8824030067504883808 969 1 (.nil) (.nil))) (.node 8844044579160884826 391 1 (.node 8842633337917875506 15 0 (.nil) (.nil)) (.nil))) (.node 8847230490301479461 896 0 (.node 8846461548517348356 957 1 (.node 8846452666181092964 909 0 (.nil) (.nil)) (.nil)) (.node 8855129134756480360 191 0 (.node 8847435723879361417 365 0 (.nil) (.nil)) (.nil))))) (.node 8942597769281232347 978 0 (.node 8901064445706826862 462 1 (.node 8883698505481789959 144 1 (.node 8873702372440657029 392 0 (.node 8871032837754600357 85 1 (.nil) (.nil)) (.node 8876822736447093532 256 0 (.nil) (.nil))) (.node 8890427424976658461 988 0 (.node 8885733514324974939 496 1 (.nil) (.nil)) (.nil))) (.node 8931580558482742173 76 0 (.node 8916194954726962994 110 0 (.node 8915440302243491934 78 1 (.nil) (.nil)) (.node 8918025483746183438 966 0 (.nil) (.nil))) (.node 8938681005127669453 237 0 (.node 8933728992305058574 959 0 (.nil) (.nil)) (.nil)))) (.node 8980295000387619715 881 0 (.node 8978299347817622667 481 0 (.node 8963195557461294796 920 0 (.node 8947725241672311697 472 1 (.nil) (.nil)) (.node 8968595734671300097 962 1 (.nil) (.nil))) (.node 8979678518848877403 221 0 (.node 8978834376269271043 53 0 (.nil) (.nil)) (.nil))) (.node 8984895828243061163 44 0 (.node 8984167396190934364 451 0 (.node 8980661580746274152 1011 1 (.nil) (.nil)) (.nil)) (.node 8990566877267638575 124 0 (.node 8985664518777474449 90 0 (.nil) (.nil)) (.nil)))))))) (.node 9669282212139196350 308 0 (.node 9310206294850019472 8 0 (.node 9126426059651332439 897 0 (.node 9100961592897348911 248 0 (.node 9067227433131001292 207 0 (.node 9031977195327476199 957 0 (.node 9010796712206663516 487 0 (.node 8993308510573353057 245 1 (.nil) (.nil)) (.node 9013676172631395277 1 0 (.nil) (.nil))) (.node 9059769212580900307 1003 0 (.node 9032600922325293410 890 0 (.nil) (.nil)) (.nil))) (.node 9093184640147097481 936 1 (.node 9084497218342010314 1005 1 (.node 9071534718402153801 232 1 (.nil) (.nil)) (.node 9087607638592813730 337 1 (.nil) (.nil))) (.node 9095237015126255828 486 0 (.node 9095098401894277558 360 0 (.nil) (.nil)) (.nil)))) (.node 9123365523412370792 327 0 (.node 9112057762027086162 267 1 (.node 9111497011255036266 107 0 (.node 9101152860426244016 338 0 (.nil) (.nil)) (.node 9112057757827957866 3 0 (.nil) (.nil))) (.node 9122319587160620912 139 0 (.node 9112337022116718162 123 0 (.nil) (.nil)) (.nil))) (.node 9123937436639854052 358 0 (.node 9123928241375098464 331 0 (.node 9123927234942550688 358 1 (.nil) (.nil)) (.node 9123932570702005360 291 1 (.nil) (.nil))) (.node 9125041062580336553 4 0 (.node 9124205534274052688 1023 0 (.nil) (.nil)) (.nil))))) (.node 9252559432396322896 335 0 (.node 9175886951942304162 294 1 (.node 9160383884795353596 895 0 (.node 9155842017533772500 911 1 (.node 9130674714073157895 16 1 (.nil) (.nil)) (.node 9160178651217471640 96 0 (.nil) (.nil))) (.node 9173910855318553955 323 0 (.node 9169585551858794281 260 0 (.nil) (.nil)) (.nil))) (.node 9221924665213896430 340 0 (.node 9214899372186148103 1014 0 (.node 9176469150370874981 60 0 (.nil) (.nil)) (.node 9216171158329062713 911 0 (.nil) (.nil))) (.node 9233956161983331198 41 1 (.node 9230535608363246865 888 0 (.nil) (.nil)) (.nil)))) (.node 9286748830925540922 128 0 (.node 9265871829482057288 215 0 (.node 9256378760659540354 333 0 (.node 9253970673639332216 903 1 (.nil) (.nil)) (.node 9257361818357808807 877 0 (.nil) (.nil))) (.node 9280614048704405401 296 0 (.node 9268602204792177528 255 0 (.nil) (.nil)) (.nil))) (.node 9302608947055580900 499 0 (.node 9295271482950171422 318 0 (.node 9288233090518915828 391 0 (.nil) (.nil)) (.nil)) (.node 9308603986248366558 229 0 (.node 9304100936454776823 69 0 (.nil) (.nil)) (.nil)))))) (.node 9482261973839077347 387 0 (.node 9393582171990718888 103 1 (.node 9361628336058760800 299 0 (.node 9348607099606116843 493 0 (.node 9324719434392581630 400 1 (.node 9317083846780303072 283 0 (.nil) (.nil)) (.node 9332954520454959421 346 0 (.nil) (.nil))) (.node 9357651336150759087 984 1 (.node 9352188827832036521 420 0 (.nil) (.nil)) (.nil))) (.node 9385366854920144226 91 0 (.node 9378190072324778636 982 0 (.node 9363194686822643046 17 1 (.nil) (.nil)) (.node 9385211024081371039 397 0 (.nil) (.nil))) (.node 9392842202996492579 1001 0 (.node 9391691241559886087 121 0 (.nil) (.nil)) (.nil)))) (.node 9446139763358785098 385 0 (.node 9420722806685110906 407 0 (.node 9395590613255921839 506 0 (.node 9394126406663011960 359 0 (.nil) (.nil)) (.node 9399586880618036111 141 0 (.nil) (.nil))) (.node 9444131369896493839 93 0 (.node 9423602267109842667 97 0 (.nil) (.nil)) (.nil))) (.node 9464165595883495268 922 0 (.node 9459347759505442838 454 0 (.node 9457826794902013171 459 0 (.nil) (.nil)) (.node 9461279230505237916 84 0 (.nil) (.nil))) (.node 9473723616042107910 198 0 (.node 9469695307059347697 1019 0 (.nil) (.nil)) (.nil))))) (.node 9541687810949820873 136 0 (.node 9534753026018398848 339 0 (.node 9492562595398479436 106 0 (.node 9482924801959389843 983 0 (.node 9482645537670629547 471 0 (.nil) (.nil)) (.node 9492404500477349516 9 0 (.nil) (.nil))) (.node 9514542321383178235 500 0 (.node 9514081741399578279 488 1 (.nil) (.nil)) (.nil))) (.node 9537107084676937164 166 0 (.node 9536359713042198624 11 0 (.node 9536359708843070328 71 0 (.nil) (.nil)) (.node 9536838593448067960 507 0 (.nil) (.nil))) (.node 9537405640737702528 211 0 (.node 9537313191566998728 209 1 (.nil) (.nil)) (.nil)))) (.node 9586395244849322371 316 0 (.node 9573070682252028164 935 0 (.node 9562776832906843460 12 0 (.node 9553822945402739104 115 0 (.nil) (.nil)) (.node 9569471935094794326 126 0 (.nil) (.nil))) (.node 9583836949797001345 435 0 (.node 9576497228122542653 452 0 (.nil) (.nil)) (.nil))) (.node 9660660642863451583 30 0 (.node 9620418221047595218 447 0 (.node 9616044678861836078 176 0 (.nil) (.nil)) (.nil)) (.node 9669004831357879438 492 0 (.node 9668725571268247438 180 0 (.nil) (.nil)) (.nil))))))) (.node 10593111645891671067 987 0 (.node 10139427181979294746 918 0 (.node 9892188068317524737 307 0 (.node 9785762983094554922 984 0 (.node 9705205132141909311 33 0 (.node 9699871515534925557 357 1 (.node 9682665587213962998 484 0 (.nil) (.nil)) (.node 9701706160554612996 891 0 (.nil) (.nil))) (.node 9732554761183465438 148 0 (.node 9712854646979741791 372 0 (.nil) (.nil)) (.nil))) (.node 9831239979397834250 224 0 (.node 9795682123099360211 5 1 (.node 9795476889521478255 320 0 (.nil) (.nil)) (.node 9806964044212262113 36 0 (.nil) (.nil))) (.node 9851757749238038317 1004 1 (.node 9849926262007625958 101 0 (.nil) (.nil)) (.nil)))) (.node 9948508368911854759 936 0 (.node 9924468415861625625 924 0 (.node 9902350396774204564 508 0 (.node 9892571632149076937 143 0 (.nil) (.nil)) (.node 9924007835878025669 1000 1 (.nil) (.nil))) (.node 9945425808879782093 196 0 (.node 9942034664161305502 948 0 (.nil) (.nil)) (.nil))) (.node 10081159005926897078 940 0 (.node 10025970773340283468 432 0 (.node 10016015568746604114 908 0 (.nil) (.nil)) (.node 10052145636816034673 23 0 (.nil) (.nil))) (.node 10139235377085733220 1007 0 (.node 10094660028271369215 944 1 (.nil) (.nil)) (.nil))))) (.node 10366656570201356765 424 0 (.node 10276737222786491682 292 0 (.node 10258373969795774272 28 0 (.node 10222962885758530361 880 1 (.node 10192742451739613736 981 1 (.nil) (.nil)) (.node 10235310772117680822 952 1 (.nil) (.nil))) (.node 10266062340455384061 480 0 (.node 10261683843716485707 28 1 (.nil) (.nil)) (.nil))) (.node 10317446332128198457 975 0 (.node 10304621507175302673 227 0 (.node 10301265186308771353 287 0 (.nil) (.nil)) (.node 10312276491252651954 2 0 (.nil) (.nil))) (.node 10363465262522663923 989 0 (.node 10323176169071195833 416 0 (.nil) (.nil)) (.nil)))) (.node 10438382231859799438 66 0 (.node 10406567490374305976 159 0 (.node 10397355058161966303 31 0 (.node 10389533049440047939 948 1 (.nil) (.nil)) (.node 10403908905976713011 180 1 (.nil) (.nil))) (.node 10429771288710449003 289 1 (.node 10406594071248787234 324 0 (.nil) (.nil)) (.nil))) (.node 10519434574898216242 280 0 (.node 10460711025566344993 495 0 (.node 10455693601469240412 253 0 (.nil) (.nil)) (.nil)) (.node 10568924505517826149 360 1 (.node 10558678030901846596 413 0 (.nil) (.nil)) (.nil)))))) (.node 11017190570001227539 35 0 (.node 10875532559387752483 243 0 (.node 10751039748775006219 927 0 (.node 10675988434933831451 992 0 (.node 10612216353505598935 411 0 (.node 10607775055336859683 111 0 (.nil) (.nil)) (.node 10650906369848423085 317 0 (.nil) (.nil))) (.node 10686663317264939072 460 0 (.node 10686374912885437897 239 0 (.nil) (.nil)) (.nil))) (.node 10864498444830455233 288 0 (.node 10784343851619095226 125 0 (.node 10783360793920826773 349 0 (.nil) (.nil)) (.node 10845626268434236812 80 0 (.nil) (.nil))) (.node 10870637120044792383 127 0 (.node 10869543433921574495 376 0 (.nil) (.nil)) (.nil)))) (.node 10917176236753939295 316 1 (.node 10890512210710515571 489 1 (.node 10876572190565671715 87 0 (.node 10875589132867403262 381 0 (.nil) (.nil)) (.node 10877408140400079403 95 0 (.nil) (.nil))) (.node 10916886953072624359 56 0 (.node 10895189146810871744 96 1 (.nil) (.nil)) (.nil))) (.node 10991147629144781687 250 0 (.node 10981677270548682475 1012 0 (.node 10971093564469708403 161 1 (.nil) (.nil)) (.nil)) (.node 11006584715927368235 491 0 (.node 11003860649716312347 347 0 (.nil) (.nil)) (.nil))))) (.node 11416854835147011883 963 0 (.node 11160965843253453609 511 0 (.node 11073586283322180574 216 1 (.node 11019843184720531219 291 0 (.node 11019276137430896651 219 0 (.nil) (.nil)) (.node 11021248125372556851 415 0 (.nil) (.nil))) (.node 11153067198798452710 64 0 (.node 11125488308231361213 344 0 (.nil) (.nil)) (.nil))) (.node 11350190433363289252 27 0 (.node 11288800395845567695 32 0 (.node 11285515227345850652 893 0 (.nil) (.nil)) (.node 11325666127378354626 445 0 (.nil) (.nil))) (.node 11401073723623229077 998 0 (.node 11373064141627974541 879 0 (.nil) (.nil)) (.nil)))) (.node 11743872171951995922 164 0 (.node 11527761373710869679 212 0 (.node 11429202231909344041 199 0 (.node 11417333719752009515 363 0 (.nil) (.nil)) (.node 11429769279198978609 395 0 (.nil) (.nil))) (.node 11608445655552554149 1011 0 (.node 11594069799015889077 903 0 (.nil) (.nil)) (.nil))) (.node 11868613541403816709 268 0 (.node 11859659653899712353 371 0 (.node 11787059051158131364 899 0 (.nil) (.nil)) (.nil)) (.node 11973522644388173159 108 0 (.node 11882333936619515902 964 0 (.nil) (.nil)) (.nil)))))))))
def cG6T8 : BTree NodeData := .leaf (0,0,63,[(16,0),(7,0),(8,0),(0,0)])
def cG6M8 : BST := .node 8386781261398915423 50 0 (.node 7407737964214974273 47 1 (.node 6997811869736526883 15 1 (.node 6065983365606998672 54 0 (.node 5282024796640232930 52 0 (.node 5157885925687265381 9 0 (.node 4951078724108712893 18 1 (.nil) (.nil)) (.node 5199035020119229422 3 1 (.nil) (.nil))) (.node 5880022086408228533 46 0 (.node 5820249971942978214 54 1 (.nil) (.nil)) (.nil))) (.node 6818089565687447439 45 1 (.node 6610643224924437917 10 1 (.node 6239468260673636534 52 1 (.nil) (.nil)) (.node 6779700141022956297 57 1 (.nil) (.nil))) (.node 6881918755602665439 60 1 (.node 6818368825777079439 23 1 (.nil) (.nil)) (.nil)))) (.node 7231010156931892175 43 1 (.node 7121273320894006925 28 1 (.node 7091398658580505503 19 1 (.node 7071384146924504485 46 1 (.nil) (.nil)) (.node 7094789803298982094 57 0 (.nil) (.nil))) (.node 7189626235501403687 5 1 (.node 7160843213268078725 6 1 (.nil) (.nil)) (.nil))) (.node 7334961718012434407 22 1 (.node 7256915432605686142 50 1 (.node 7231562635723144607 29 1 (.nil) (.nil)) (.nil)) (.node 7355863565544397566 10 0 (.node 7348506939845864693 12 0 (.nil) (.nil)) (.nil))))) (.node 7863398758281456755 16 0 (.node 7555958065667987235 17 0 (.node 7517828950654908677 13 0 (.node 7463722634184238630 25 0 (.node 7410498667193201451 43 0 (.nil) (.nil)) (.node 7504871728616202671 51 1 (.nil) (.nil))) (.node 7555948323994967803 62 0 (.node 7534308143923043555 28 0 (.nil) (.nil)) (.nil))) (.node 7765789660022844956 42 0 (.node 7712613610404254295 14 1 (.node 7658951962562132477 59 1 (.nil) (.nil)) (.nil)) (.node 7820424761671648841 27 0 (.node 7816930214147962342 30 0 (.nil) (.nil)) (.nil)))) (.node 8099111828657658994 8 1 (.node 8011745316709913390 44 0 (.node 7958347004068274753 14 0 (.node 7924886646425226675 1 0 (.nil) (.nil)) (.node 7976855166920468033 18 0 (.nil) (.nil))) (.node 8043036202518980888 1 1 (.node 8030170436680787023 9 1 (.nil) (.nil)) (.nil))) (.node 8229514850986414302 62 1 (.node 8176376388413370343 12 1 (.node 8149704476193825241 4 0 (.nil) (.nil)) (.nil)) (.node 8342014107690989892 16 1 (.node 8238285253608512361 44 1 (.nil) (.nil)) (.nil)))))) (.node 9400626511795955343 5 0 (.node 9061290177184329974 60 0 (.node 8685736311279420115 20 0 (.node 8580241765496509803 6 0 (.node 8556162295813522161 20 1 (.node 8440096531159234413 25 1 (.nil) (.nil)) (.node 8570735482068698466 15 0 (.nil) (.nil))) (.node 8677125368130069680 26 1 (.node 8624786254774967531 22 0 (.nil) (.nil)) (.nil))) (.node 8916479933421411166 42 1 (.node 8846182284228588060 21 1 (.node 8714279439795605298 23 0 (.nil) (.nil)) (.nil)) (.node 9031697931038715903 21 0 (.node 8980661576547145856 31 0 (.nil) (.nil)) (.nil)))) (.node 9187755464099638688 2 1 (.node 9124482915055369600 13 1 (.node 9123926274184420688 61 1 (.node 9112057757827957866 3 0 (.nil) (.nil)) (.node 9124205534274052688 55 0 (.nil) (.nil))) (.node 9142543226230492421 0 1 (.node 9137866290130136248 30 1 (.nil) (.nil)) (.nil))) (.node 9303648578233500132 31 1 (.node 9292771693284131375 26 0 (.node 9256108378707035450 53 1 (.nil) (.nil)) (.nil)) (.node 9397235367077478752 11 1 (.node 9372842387650981890 48 0 (.nil) (.nil)) (.nil))))) (.node 10109518345724612651 49 1 (.node 9699592251246165261 17 1 (.node 9536846865428865424 27 1 (.node 9521983852306405256 51 0 (.node 9471216271662777364 2 0 (.nil) (.nil)) (.node 9536359708843070328 29 0 (.nil) (.nil))) (.node 9668725567069119142 8 0 (.node 9554862576580658336 59 0 (.nil) (.nil)) (.nil))) (.node 9861794774164960484 49 0 (.node 9713574672711947522 63 1 (.node 9702697787762578765 58 0 (.nil) (.nil)) (.nil)) (.node 10078651661547566532 24 0 (.node 9964788671059105726 7 0 (.nil) (.nil)) (.nil)))) (.node 11004421396289233947 19 0 (.node 10876366956987789759 0 0 (.node 10404948537154632243 24 1 (.node 10267373667498260517 56 0 (.nil) (.nil)) (.node 10661152844464402638 48 1 (.nil) (.nil))) (.node 10982962076627042929 58 1 (.node 10876572190565671715 47 0 (.nil) (.nil)) (.nil))) (.node 11337534639535689152 53 0 (.node 11286498285044119105 63 0 (.node 11018797252825899019 45 0 (.nil) (.nil)) (.nil)) (.node 11428723347304346409 61 0 (.node 11414347490767681337 11 0 (.nil) (.nil)) (.nil))))))
def cG6Levels : Nat → Option (BTree NodeData)
  | 3 => some cG6T3
  | 4 => some cG6T4
  | 5 => some cG6T5
  | 6 => some cG6T6
  | 7 => some cG6T7
  | 8 => some cG6T8
  | _ => none
def cG6Maps : Nat → BST
  | 4 => cG6M4
  | 5 => cG6M5
  | 6 => cG6M6
  | 7 => cG6M7
  | 8 => cG6M8
  | _ => .nil
-- ============================================================
-- 7. Forest Definitions & Verified Certificates
-- ============================================================

def baseEmpty (_ : Nat) : List Sig × Sig × Nat := ([], 0, 0)
theorem baseEmpty_sound : ∀ k, k ≠ 0 → LowerBV (baseEmpty k).1 (baseEmpty k).2.1 (baseEmpty k).2.2 :=
  fun _ _ _ _ _ _ => Nat.zero_le _

-- K3 (mask 41, cap 3 -> L = 4)
def fK3 : Forest := ⟨41, tK3, 3, cK3Pos, cK3Neg, cK3RawCols, cK3Autos, cK3Cuts, cK3Levels, cK3Maps⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fK3_valid : graphValid fK3 baseEmpty = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fK3_L3 : cK3T3.all (fastNodeOK fK3 3) = true := by decide +kernel
theorem fK3_levels : levelsChecked fK3 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fK3, cK3Levels] at ht
  subst ht; exact fK3_L3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowK3 : LowerBV (rawOf 41) tK3 4 :=
  lower_forest fK3 baseEmpty baseEmpty_sound fK3_valid fK3_levels (by decide +kernel)

-- P4 (mask 60, cap 3 -> L = 4)
def fP4 : Forest := ⟨60, tP4, 3, cP4Pos, cP4Neg, cP4RawCols, cP4Autos, cP4Cuts, cP4Levels, cP4Maps⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fP4_valid : graphValid fP4 baseEmpty = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fP4_L2 : cP4T2.all (fastNodeOK fP4 2) = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fP4_L3 : cP4T3.all (fastNodeOK fP4 3) = true := by decide +kernel
theorem fP4_levels : levelsChecked fP4 := by
  intro k hk tree ht; change k ≤ 3 at hk; interval_cases k
  all_goals simp [fP4, cP4Levels] at ht
  · subst ht; exact fP4_L2
  · subst ht; exact fP4_L3
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowP4 : LowerBV (rawOf 60) tP4 4 :=
  lower_forest fP4 baseEmpty baseEmpty_sound fP4_valid fP4_levels (by decide +kernel)

-- Base map for C5 (kind 1 = K3, kind 2 = P4)
def baseC5 : Nat → List Sig × Sig × Nat
  | 1 => (rawOf 41, tK3, 4)
  | 2 => (rawOf 60, tP4, 4)
  | _ => ([], 0, 0)
theorem baseC5_sound : ∀ k, k ≠ 0 → LowerBV (baseC5 k).1 (baseC5 k).2.1 (baseC5 k).2.2 := by
  intro k _
  match k with
  | 1 => exact lowK3
  | 2 => exact lowP4
  | 0 | _ + 3 => exact fun _ _ _ _ => Nat.zero_le _

-- C5 (mask 62, cap 6 -> L = 7)
def fC5 : Forest := ⟨62, tC5, 6, cC5Pos, cC5Neg, cC5RawCols, cC5Autos, cC5Cuts, cC5Levels, cC5Maps⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fC5_valid : graphValid fC5 baseC5 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fC5_L3 : cC5T3.all (fastNodeOK fC5 3) = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fC5_L4 : cC5T4.all (fastNodeOK fC5 4) = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fC5_L5 : cC5T5.all (fastNodeOK fC5 5) = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fC5_L6 : cC5T6.all (fastNodeOK fC5 6) = true := by decide +kernel
theorem fC5_levels : levelsChecked fC5 := by
  intro k hk tree ht; change k ≤ 6 at hk; interval_cases k
  all_goals simp [fC5, cC5Levels] at ht
  · subst ht; exact fC5_L3
  · subst ht; exact fC5_L4
  · subst ht; exact fC5_L5
  · subst ht; exact fC5_L6
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowC5 : LowerBV (rawOf 62) tC5 7 :=
  lower_forest fC5 baseC5 baseC5_sound fC5_valid fC5_levels (by decide +kernel)

-- Base map for G6 (kind 1 = K3, kind 2 = P4, kind 3 = C5)
def baseG6 : Nat → List Sig × Sig × Nat
  | 1 => (rawOf 41, tK3, 4)
  | 2 => (rawOf 60, tP4, 4)
  | 3 => (rawOf 62, tC5, 7)
  | _ => ([], 0, 0)
theorem baseG6_sound : ∀ k, k ≠ 0 → LowerBV (baseG6 k).1 (baseG6 k).2.1 (baseG6 k).2.2 := by
  intro k _
  match k with
  | 1 => exact lowK3
  | 2 => exact lowP4
  | 3 => exact lowC5
  | 0 | _ + 4 => exact fun _ _ _ _ => Nat.zero_le _

-- G6 (mask 63, cap 8 -> L = 9)
def fG6 : Forest := ⟨63, tG6, 8, cG6Pos, cG6Neg, cG6RawCols, cG6Autos, cG6Cuts, cG6Levels, cG6Maps⟩
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_valid : graphValid fG6 baseG6 = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L3 : cG6T3.all (fastNodeOK fG6 3) = true := by decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L4 : cG6T4.all (fastNodeOK fG6 4) = true := by
  apply treeSplit_sound (d := 2); simp only [treeSplit, cG6T4]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L5 : cG6T5.all (fastNodeOK fG6 5) = true := by
  apply treeSplit_sound (d := 4); simp only [treeSplit, cG6T5]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L6 : cG6T6.all (fastNodeOK fG6 6) = true := by
  apply treeSplit_sound (d := 4); simp only [treeSplit, cG6T6]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L7 : cG6T7.all (fastNodeOK fG6 7) = true := by
  apply treeSplit_sound (d := 2); simp only [treeSplit, cG6T7]; repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem fG6_L8 : cG6T8.all (fastNodeOK fG6 8) = true := by decide +kernel
theorem fG6_levels : levelsChecked fG6 := by
  intro k hk tree ht; change k ≤ 8 at hk; interval_cases k
  all_goals simp [fG6, cG6Levels] at ht
  · subst ht; exact fG6_L3
  · subst ht; exact fG6_L4
  · subst ht; exact fG6_L5
  · subst ht; exact fG6_L6
  · subst ht; exact fG6_L7
  · subst ht; exact fG6_L8
set_option maxRecDepth 32768 in set_option maxHeartbeats 0 in
theorem lowG6 : LowerBV (rawOf 63) tG6 9 :=
  lower_forest fG6 baseG6 baseG6_sound fG6_valid fG6_levels (by decide +kernel)

-- ============================================================
-- 8. Lift G6 (L=9) to 7-variable Graph (L=10) + Monotone Witness
-- ============================================================

abbrev Sig7 := BitVec 128
abbrev Row7 := Fin 128

def var7 (i : Nat) : Sig7 := tableBV fun r => r.val.testBit i
def inputs7 : List Sig7 := ([0, 1, 2, 3, 4, 5, 6] : List Nat).map var7

def target7 (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def sample7 (r : Row7) (i : Fin 7) : Bool := bitBV r (inputs7.getD i.val zeroBV)
def graph7 : Sig7 := tableBV fun r => target7 (sample7 r)

def lift6to7 (r : Row) : Row7 :=
  ⟨r.val % 16 + (r.val / 16) * 32, by omega⟩

theorem graph7_proper : properBV graph7 := by unfold properBV; decide +kernel
theorem graph7_plain : plainWordBV graph7 = true := by decide +kernel
theorem inputs7_plain : inputs7.all plainWordBV = true := by decide +kernel
theorem tG6_proper : properBV tG6 := by unfold properBV; decide +kernel

theorem lift6to7_goal : restrictRows lift6to7 (observeBV graph7) = observeBV tG6 := by
  funext r
  have h : ∀ r : Row, bitBV (lift6to7 r) graph7 = bitBV r tG6 := by decide +kernel
  exact h r

theorem lift6to7_vars : ∀ a ∈ inputs7, Available ((rawOf 63).map observeBV) (restrictRows lift6to7 (observeBV a)) := by
  have h0 : restrictRows lift6to7 (observeBV (var7 0)) = observeBV x0 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 0) = bitBV r x0) r
  have h1 : restrictRows lift6to7 (observeBV (var7 1)) = observeBV x1 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 1) = bitBV r x1) r
  have h2 : restrictRows lift6to7 (observeBV (var7 2)) = observeBV x2 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 2) = bitBV r x2) r
  have h3 : restrictRows lift6to7 (observeBV (var7 3)) = observeBV x3 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 3) = bitBV r x3) r
  have h4 : restrictRows lift6to7 (observeBV (var7 4)) = fun _ => false := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 4) = false) r
  have h5 : restrictRows lift6to7 (observeBV (var7 5)) = observeBV x4 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 5) = bitBV r x4) r
  have h6 : restrictRows lift6to7 (observeBV (var7 6)) = observeBV x5 := by
    funext r; exact (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 6) = bitBV r x5) r
  intro a ha
  simp only [inputs7, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h0]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))
  · rw [h1]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))
  · rw [h2]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))
  · rw [h3]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))
  · rw [h4]; exact Or.inr (Or.inl ⟨false, rfl⟩)
  · rw [h5]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))
  · rw [h6]; exact Or.inl (List.mem_map_of_mem (by decide +kernel))

theorem x4_ess7 : EssentialBV graph7 inputs7 (var7 4) := by
  refine ⟨⟨1, by decide⟩, ⟨17, by decide⟩, by decide +kernel, ?_⟩
  intro v hv hne
  simp only [inputs7, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact absurd rfl hne
  · decide +kernel
  · decide +kernel

theorem lowG7 : LowerBV inputs7 graph7 10 := by
  have h4c : Constant (restrictRows lift6to7 (observeBV (var7 4))) :=
    ⟨false, funext fun r => (by decide +kernel : ∀ r : Row, bitBV (lift6to7 r) (var7 4) = false) r⟩
  have h := lowerBV_slice graph7_proper graph7_plain inputs7_plain tG6_proper lift6to7
    lift6to7_goal lift6to7_vars {var7 4}
    (fun a ha => (Finset.mem_singleton.mp ha) ▸ x4_ess7)
    (fun a ha => (Finset.mem_singleton.mp ha) ▸ h4c)
    9 lowG6
  simpa using h

-- Explicit 11-gate monotone witness for L-meta-11413
def smallCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [7, 3]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [14, 6]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [16, 15]⟩], 17⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target7 x := by
  decide +kernel

theorem inputs7_list : List.ofFn (fun i : Fin 7 => inputs7.getD i.val zeroBV) = inputs7 := rfl

theorem sample7_eq (r : Row7) : List.ofFn (sample7 r) = (inputs7.map observeBV).map (fun f => f r) := by
  rw [← inputs7_list, List.map_map, List.map_ofFn]; rfl

theorem noNotReuse {gates : List Gate}
    (fit : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg; obtain ⟨ops, ar⟩ := fit g hg; refine ⟨?_, ar⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

theorem replaceShort (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = target7 x) :
    ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x) = target7 x := by
  classical
  by_cases big : 11 ≤ gates.length
  · exact ⟨smallCircuit.gates, smallCircuit.output, witnessMonotone, big, witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates, o, noNotReuse fit mono, Nat.le_refl _, correct⟩
  push Not at mono
  obtain ⟨g, hg, hop⟩ := mono
  have hlt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot, hop] at eq
  obtain ⟨q, bank, hq, hreach, hsup⟩ := circuit_reach (inputs7.map observeBV) gates (inputs7.map observeBV)
    0 (inputs7.map observeBV) fit Reach.start (fun a ha => Or.inl ha)
  have hout : (execWires gates (inputs7.map observeBV)).getD o (fun _ => false) = observeBV graph7 := by
    funext r
    have hev := execWires_at gates (inputs7.map observeBV) r
    have hr1 : ((execWires gates (inputs7.map observeBV)).getD o (fun _ => false)) r =
        ((execWires gates (inputs7.map observeBV)).map (fun f => f r)).getD o false := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases (execWires gates (inputs7.map observeBV))[o]? <;> rfl
    rw [hr1, hev, ← sample7_eq r]
    exact (correct (sample7 r)).trans (bitBV_table (fun r => target7 (sample7 r)) r).symm
  have havail : Available bank (observeBV graph7) := hout ▸ avail_getD hsup o
  have h10 := lowG7 q bank hreach havail
  omega

end PEqualNP.Outside.L_meta_11413

open PEqualNP.Outside.L_meta_11413 in
theorem PEqualNP.Outside.L_meta_11413 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort gates o fit correct
