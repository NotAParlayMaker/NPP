import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16927

-- The signed circuit search uses the live-wire compression from L-meta-1423.
-- A NOT gate costs one gate in the given circuit and zero in the signed search.
-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 54 pairs of assignments.
abbrev W := BitVec 108
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 54 := ((x >>> 54) ^^^ x).setWidth 54
def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 54+i.val < 108 := by omega
  have hi' : i.val < 108 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 54) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 9 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 9) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 9 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 9) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 108 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 108)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 108) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 108) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 108) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#108)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 108, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 108) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 6) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection t ht (lift low run)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 108, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

def signal0 : W := (0x94d8c5cd : BitVec 54) ++ (0x39c3df : BitVec 54)
def signal1 : W := (0x1319e0c4c : BitVec 54) ++ (0x73be1c1c : BitVec 54)
def signal2 : W := (0x1b5decdcd : BitVec 54) ++ (0x73bfdfdf : BitVec 54)
def signal3 : W := (0x23c0a6de4 : BitVec 54) ++ (0x7c001fe0 : BitVec 54)
def signal4 : W := (0x3a91ee8a0 : BitVec 54) ++ (0x3803fe000 : BitVec 54)
def signal5 : W := (0x3bdd48109 : BitVec 54) ++ (0x3ffc00000 : BitVec 54)
def signal6 : W := (0x80810b8045c : BitVec 54) ++ (0x38001c : BitVec 54)
def signal7 : W := (0xa4c002946d6 : BitVec 54) ++ (0x39c3df : BitVec 54)
def signal8 : W := (0x15d0000a7ee4 : BitVec 54) ++ (0x1c000001fe0 : BitVec 54)
def signal9 : W := (0x1898002a1c54 : BitVec 54) ++ (0x3838003e1c1c : BitVec 54)
def signal10 : W := (0x1adc002b5ed6 : BitVec 54) ++ (0x3838003fdfdf : BitVec 54)
def signal11 : W := (0x1f00002b68a0 : BitVec 54) ++ (0x3e00003fe000 : BitVec 54)
def signal12 : W := (0x1fdc00211212 : BitVec 54) ++ (0x3ffc00000000 : BitVec 54)
def signal13 : W := (0x1fdfbdf5931b : BitVec 54) ++ (0x3fffffc00000 : BitVec 54)
def signal14 : W := (0x10040140847c4 : BitVec 54) ++ (0x3c0 : BitVec 54)
def signal15 : W := (0x1404c14c0075f : BitVec 54) ++ (0x3df : BitVec 54)
def signal16 : W := (0x21090700a1c44 : BitVec 54) ++ (0x70001c00 : BitVec 54)
def signal17 : W := (0x280b85280145c : BitVec 54) ++ (0x3873801c1c : BitVec 54)
def signal18 : W := (0x300d054001744 : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal19 : W := (0x380f85680175c : BitVec 54) ++ (0x701f87f801ffc : BitVec 54)
def signal20 : W := (0x3c02056c00109 : BitVec 54) ++ (0x7c0007fc00000 : BitVec 54)
def signal21 : W := (0x3c0f056c0174d : BitVec 54) ++ (0x7c1c07fc01fe0 : BitVec 54)
def signal22 : W := (0x3c0fc42001212 : BitVec 54) ++ (0x7c1fc00000000 : BitVec 54)
def signal23 : W := (0x3c0ffeb1efab2 : BitVec 54) ++ (0x7c1ff803fe000 : BitVec 54)
def signal24 : W := (0x3df2056eb69a9 : BitVec 54) ++ (0x7fe007fffe000 : BitVec 54)
def signal25 : W := (0x3dffc42211212 : BitVec 54) ++ (0x7fffc00000000 : BitVec 54)
def signal26 : W := (0x80a008039c080 : BitVec 54) ++ (0x39c000 : BitVec 54)
def signal27 : W := (0x84a0c80f1801b : BitVec 54) ++ (0x39c01f : BitVec 54)
def signal28 : W := (0x9400094d08109 : BitVec 54) ++ (0x0 : BitVec 54)
def signal29 : W := (0x942448441c383 : BitVec 54) ++ (0x1c3c3 : BitVec 54)
def signal30 : W := (0x94a4c00210212 : BitVec 54) ++ (0x0 : BitVec 54)
def signal31 : W := (0x94a4c94f1875f : BitVec 54) ++ (0x39c3df : BitVec 54)
def signal32 : W := (0x94a4c94f9c7df : BitVec 54) ++ (0x39c3df : BitVec 54)
def signal33 : W := (0xbcafc42211212 : BitVec 54) ++ (0x7c1fc00000000 : BitVec 54)
def signal34 : W := (0x103801213e0800 : BitVec 54) ++ (0x3800003e0000 : BitVec 54)
def signal35 : W := (0x10a82903b40018 : BitVec 54) ++ (0x383803be001c : BitVec 54)
def signal36 : W := (0x12a02173940008 : BitVec 54) ++ (0x73800000 : BitVec 54)
def signal37 : W := (0x12a023ffd48109 : BitVec 54) ++ (0x3ffc00000 : BitVec 54)
def signal38 : W := (0x12a0b97394145c : BitVec 54) ++ (0x3873801c1c : BitVec 54)
def signal39 : W := (0x12a8b953b4145c : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal40 : W := (0x12b0b163061800 : BitVec 54) ++ (0x383873861c00 : BitVec 54)
def signal41 : W := (0x12b0b1730e1c44 : BitVec 54) ++ (0x383873861c00 : BitVec 54)
def signal42 : W := (0x12b0b1739e1c4c : BitVec 54) ++ (0x73801c00 : BitVec 54)
def signal43 : W := (0x12b0b1739e1c4c : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal44 : W := (0x12b0b973861c5c : BitVec 54) ++ (0x383873861c1c : BitVec 54)
def signal45 : W := (0x12b8b842201010 : BitVec 54) ++ (0x383800000000 : BitVec 54)
def signal46 : W := (0x12b8b9632e1c54 : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal47 : W := (0x12b8b973be1c5c : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal48 : W := (0x12bfb973bf7cfc : BitVec 54) ++ (0x3e3873bffc1c : BitVec 54)
def signal49 : W := (0x12bffc42211212 : BitVec 54) ++ (0x3ffc00000000 : BitVec 54)
def signal50 : W := (0x182a0181358000 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal51 : W := (0x18aa2983b58018 : BitVec 54) ++ (0x383e3b83bfe01c : BitVec 54)
def signal52 : W := (0x18e02183d48009 : BitVec 54) ++ (0x38c00383c00000 : BitVec 54)
def signal53 : W := (0x18e023bfd48109 : BitVec 54) ++ (0x38c003ffc00000 : BitVec 54)
def signal54 : W := (0x18ea2c02210012 : BitVec 54) ++ (0x38fe3c00000000 : BitVec 54)
def signal55 : W := (0x18ea2e3e2b6df6 : BitVec 54) ++ (0x38fe3c7c001fe0 : BitVec 54)
def signal56 : W := (0x18f5f183defeed : BitVec 54) ++ (0x38c1c383c01fe0 : BitVec 54)
def signal57 : W := (0x19e02197d48109 : BitVec 54) ++ (0x38c00383c00000 : BitVec 54)
def signal58 : W := (0x1abab9f3bfdcdc : BitVec 54) ++ (0x383873bfdc1c : BitVec 54)
def signal59 : W := (0x1afabdf3ff9c5f : BitVec 54) ++ (0x383873bfdc1f : BitVec 54)
def signal60 : W := (0x1b2ad1d5359744 : BitVec 54) ++ (0x3f3fc3fc3fffe0 : BitVec 54)
def signal61 : W := (0x1be021d7d48109 : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal62 : W := (0x1be021f7d48109 : BitVec 54) ++ (0x73800000 : BitVec 54)
def signal63 : W := (0x1beafc42211212 : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal64 : W := (0x1bf2f5e747db83 : BitVec 54) ++ (0x38387387dfc3 : BitVec 54)
def signal65 : W := (0x1bf8b9f7fe9d5d : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal66 : W := (0x1bfafc42211212 : BitVec 54) ++ (0x383800000000 : BitVec 54)
def signal67 : W := (0x1bfafd73bf1e5e : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal68 : W := (0x1bfafdf7ffdfdf : BitVec 54) ++ (0x383873bfdfdf : BitVec 54)
def signal69 : W := (0x241502280a68a0 : BitVec 54) ++ (0x0 : BitVec 54)
def signal70 : W := (0x241503a91ee8a0 : BitVec 54) ++ (0x3803fe000 : BitVec 54)
def signal71 : W := (0x2415d2280a7ee4 : BitVec 54) ++ (0x1c000001fe0 : BitVec 54)
def signal72 : W := (0x2505420c0063a0 : BitVec 54) ++ (0x701c00c0003e0 : BitVec 54)
def signal73 : W := (0x2515d20c0a7fe4 : BitVec 54) ++ (0x701c00c001fe0 : BitVec 54)
def signal74 : W := (0x26159268023820 : BitVec 54) ++ (0x701c07c001c20 : BitVec 54)
def signal75 : W := (0x261592780a7ce4 : BitVec 54) ++ (0x70001c00 : BitVec 54)
def signal76 : W := (0x2615927c0a7de4 : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal77 : W := (0x2615d2680a7ee4 : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal78 : W := (0x2700027c000100 : BitVec 54) ++ (0x700007c000000 : BitVec 54)
def signal79 : W := (0x2715d040001200 : BitVec 54) ++ (0x701c000000000 : BitVec 54)
def signal80 : W := (0x2715d27c0a7fe4 : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal81 : W := (0x27d5f27eca7fed : BitVec 54) ++ (0x7c1c07fc01fe0 : BitVec 54)
def signal82 : W := (0x2c07028801e0a0 : BitVec 54) ++ (0x3806038001e000 : BitVec 54)
def signal83 : W := (0x2c0703a91fe8a0 : BitVec 54) ++ (0x380603803fe000 : BitVec 54)
def signal84 : W := (0x2d40028c408101 : BitVec 54) ++ (0x3fc0038c400000 : BitVec 54)
def signal85 : W := (0x2d45428c40e3a1 : BitVec 54) ++ (0x3fc1c38c4003e0 : BitVec 54)
def signal86 : W := (0x2d474400010202 : BitVec 54) ++ (0x3fc7c400000000 : BitVec 54)
def signal87 : W := (0x2d4745319f0e4e : BitVec 54) ++ (0x3fc7c473be1c1c : BitVec 54)
def signal88 : W := (0x2d589a8c6a9d55 : BitVec 54) ++ (0x3ff83b8c7e1c1c : BitVec 54)
def signal89 : W := (0x2d5f4ebcfbefff : BitVec 54) ++ (0x39c3df : BitVec 54)
def signal90 : W := (0x2e5f9ee8f3b83b : BitVec 54) ++ (0x701c07c39dc3f : BitVec 54)
def signal91 : W := (0x2e87bada81f4fc : BitVec 54) ++ (0x38063bf381fc1c : BitVec 54)
def signal92 : W := (0x2f55d2fcdaffed : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal93 : W := (0x2f5fde7c2b7ff6 : BitVec 54) ++ (0x701c07c001fe0 : BitVec 54)
def signal94 : W := (0x2f5fdefcfbffff : BitVec 54) ++ (0x701c07c39dfff : BitVec 54)
def signal95 : W := (0x34350329062820 : BitVec 54) ++ (0x383e0380062000 : BitVec 54)
def signal96 : W := (0x343503290e68a0 : BitVec 54) ++ (0x383e0380062000 : BitVec 54)
def signal97 : W := (0x343503a91ee8a0 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal98 : W := (0x343d03293e68a0 : BitVec 54) ++ (0x3800003e0000 : BitVec 54)
def signal99 : W := (0x343f03292f68a0 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal100 : W := (0x35754f3dc62f7f : BitVec 54) ++ (0x383e03800623df : BitVec 54)
def signal101 : W := (0x35ad6b0fb463b8 : BitVec 54) ++ (0x739f80fbe03fc : BitVec 54)
def signal102 : W := (0x36a0236b040000 : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal103 : W := (0x36a023ffd48109 : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal104 : W := (0x36aa6f6b2d46d6 : BitVec 54) ++ (0x3fc003fff9c3df : BitVec 54)
def signal105 : W := (0x36b5b042001000 : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal106 : W := (0x36b5b0d6d8d5cd : BitVec 54) ++ (0x3ffffc0039c3df : BitVec 54)
def signal107 : W := (0x36bdbb7bbe7cfc : BitVec 54) ++ (0x383873be1c1c : BitVec 54)
def signal108 : W := (0x36bffc42211212 : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal109 : W := (0x37b5f37f9e7fec : BitVec 54) ++ (0x701c07f801fe0 : BitVec 54)
def signal110 : W := (0x37bdfb7fbe7ffc : BitVec 54) ++ (0x739f87fbe1ffc : BitVec 54)
def signal111 : W := (0x3c2003a9148000 : BitVec 54) ++ (0x38000380000000 : BitVec 54)
def signal112 : W := (0x3c3503a91ee8a0 : BitVec 54) ++ (0x38000380000000 : BitVec 54)
def signal113 : W := (0x3c3703a907e8a0 : BitVec 54) ++ (0x383e038007e000 : BitVec 54)
def signal114 : W := (0x3c3f0000210000 : BitVec 54) ++ (0x383e0000000000 : BitVec 54)
def signal115 : W := (0x3c3f03a93fe8a0 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal116 : W := (0x3c3f0bb9bfecfc : BitVec 54) ++ (0x383e03803fe01c : BitVec 54)
def signal117 : W := (0x3c7f0fa9ffe8bb : BitVec 54) ++ (0x383e03803fe01f : BitVec 54)
def signal118 : W := (0x3cff2fab3fe8b2 : BitVec 54) ++ (0x38fe3f803fe000 : BitVec 54)
def signal119 : W := (0x3d7f03bdffe9a9 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal120 : W := (0x3d7f4fa93feab2 : BitVec 54) ++ (0x383e03803fe000 : BitVec 54)
def signal121 : W := (0x3d7f4fbdffefff : BitVec 54) ++ (0x383e03803fe3df : BitVec 54)
def signal122 : W := (0x3de0238fd48109 : BitVec 54) ++ (0x3fc0038fc00000 : BitVec 54)
def signal123 : W := (0x3ebfbbeb3ff8b0 : BitVec 54) ++ (0x383e3b803fe000 : BitVec 54)
def signal124 : W := (0x3ebfbbfbbffcfc : BitVec 54) ++ (0x383e3bf3bffc1c : BitVec 54)
def signal125 : W := (0x3f3fd3fd3fffe4 : BitVec 54) ++ (0x3f3fc3fc3fffe0 : BitVec 54)
def signal126 : W := (0x3fe02042000000 : BitVec 54) ++ (0x3fc00000000000 : BitVec 54)
def signal127 : W := (0x3fe023ffd48109 : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal128 : W := (0x3fe767ffd5830b : BitVec 54) ++ (0x3fc7c7ffc00000 : BitVec 54)
def signal129 : W := (0x3fea6ffff5831b : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal130 : W := (0x3fea6ffffdc7df : BitVec 54) ++ (0x3fc003fff9c3df : BitVec 54)
def signal131 : W := (0x3ff0b3ffde9d4d : BitVec 54) ++ (0x3fc003ffc01c00 : BitVec 54)
def signal132 : W := (0x3ff523ffdee9a9 : BitVec 54) ++ (0x3fc003ffc00000 : BitVec 54)
def signal133 : W := (0x3ff5b3ffd6b929 : BitVec 54) ++ (0x3fc1c3ffc01c20 : BitVec 54)
def signal134 : W := (0x3ff5f3ffd49309 : BitVec 54) ++ (0x3fc1c3ffc00000 : BitVec 54)
def signal135 : W := (0x3ff5f3ffdeffed : BitVec 54) ++ (0x3fc1c3ffc01fe0 : BitVec 54)
def signal136 : W := (0x3ff8bbfffe9d5d : BitVec 54) ++ (0x3ff83bfffe1c1c : BitVec 54)
def signal137 : W := (0x3fff23ffffe9a9 : BitVec 54) ++ (0x3ffe03ffffe000 : BitVec 54)
def signal138 : W := (0x3ffffc42211212 : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal139 : W := (0x3ffffcd6f1931b : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal140 : W := (0x3ffffcd6f9d7df : BitVec 54) ++ (0x3ffffc0039c3df : BitVec 54)
def signal141 : W := (0x3ffffd73bf1e5e : BitVec 54) ++ (0x3ffffc73be1c1c : BitVec 54)
def signal142 : W := (0x3ffffe6a2b7ab2 : BitVec 54) ++ (0x3ffffc00000000 : BitVec 54)
def signal143 : W := (0x3ffffe7e2b7ff6 : BitVec 54) ++ (0x3ffffc7c001fe0 : BitVec 54)
def signal144 : W := (0x3ffffece619313 : BitVec 54) ++ (0x3fffff8c400000 : BitVec 54)
def signal145 : W := (0x3fffff6b273a32 : BitVec 54) ++ (0x3fffff80062000 : BitVec 54)
def signal146 : W := (0x3fffffeb359212 : BitVec 54) ++ (0x3fffff80000000 : BitVec 54)
def signal147 : W := (0x3fffffeb3ffab2 : BitVec 54) ++ (0x3fffff803fe000 : BitVec 54)
def signal148 : W := (0x3ffffffff5931b : BitVec 54) ++ (0x3fffffffc00000 : BitVec 54)

def ins : List W := [signal32,signal47,signal80,signal115,signal127,signal138]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok0 : everyKey (fun q => !doneTest q) layer0=true := by decide +kernel
theorem closed0 : Closed 0 layer0 := closed_nil _ ok0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok1 : everyKey (rowOK 0 layer0) layer1=true := by decide +kernel
theorem closed1 : Closed 1 layer1 := closed_next 0 (by decide) _ _ closed0 ok1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok2 : everyKey (rowOK 1 layer1) layer2=true := by decide +kernel
theorem closed2 : Closed 2 layer2 := closed_next 1 (by decide) _ _ closed1 ok2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal32,signal80,signal88,signal115,signal138] (.node [signal32,signal47,signal55,signal115,signal127] (.node [signal23,signal32,signal47,signal80,signal127] (.node [signal13,signal32,signal47,signal80,signal115] .nil .nil) (.node [signal24,signal32,signal47,signal80,signal138] .nil .nil)) (.node [signal32,signal47,signal60,signal127,signal138] (.node [signal32,signal47,signal56,signal115,signal138] .nil .nil) (.node [signal32,signal80,signal87,signal115,signal127] .nil .nil))) (.node [signal47,signal80,signal104,signal115,signal138] (.node [signal32,signal101,signal115,signal127,signal138] (.node [signal32,signal80,signal91,signal127,signal138] .nil .nil) (.node [signal47,signal80,signal100,signal127,signal138] .nil .nil)) (.node [signal47,signal90,signal115,signal127,signal138] (.node [signal47,signal80,signal106,signal115,signal127] .nil .nil) (.node [signal64,signal80,signal115,signal127,signal138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal32,signal47,signal71,signal115,signal127,signal138] (.node [signal30,signal47,signal80,signal115,signal127,signal140] (.node [signal14,signal47,signal94,signal115,signal127,signal138] (.node [signal6,signal68,signal80,signal115,signal127,signal138] (.node [signal3,signal32,signal47,signal54,signal115,signal127] (.node [signal1,signal32,signal80,signal86,signal115,signal127] (.node [signal0,signal47,signal80,signal105,signal115,signal127] .nil .nil) (.node [signal2,signal32,signal47,signal80,signal115,signal127] .nil .nil)) (.node [signal5,signal12,signal32,signal47,signal80,signal115] (.node [signal4,signal22,signal32,signal47,signal80,signal127] .nil .nil) .nil)) (.node [signal9,signal32,signal80,signal84,signal115,signal138] (.node [signal8,signal32,signal47,signal52,signal115,signal138] (.node [signal7,signal47,signal80,signal102,signal115,signal138] .nil .nil) .nil) (.node [signal11,signal20,signal32,signal47,signal80,signal138] (.node [signal10,signal32,signal47,signal80,signal115,signal138] .nil .nil) .nil))) (.node [signal21,signal32,signal47,signal80,signal127,signal138] (.node [signal17,signal32,signal80,signal82,signal127,signal138] (.node [signal16,signal32,signal110,signal115,signal127,signal138] (.node [signal15,signal47,signal80,signal95,signal127,signal138] .nil .nil) .nil) (.node [signal19,signal32,signal47,signal80,signal127,signal138] (.node [signal18,signal32,signal47,signal50,signal127,signal138] .nil .nil) .nil)) (.node [signal27,signal47,signal74,signal115,signal127,signal138] (.node [signal26,signal47,signal80,signal121,signal127,signal138] (.node [signal25,signal32,signal47,signal80,signal115,signal127] .nil .nil) .nil) (.node [signal29,signal40,signal80,signal115,signal127,signal138] (.node [signal28,signal47,signal80,signal115,signal130,signal138] .nil .nil) .nil)))) (.node [signal32,signal45,signal80,signal115,signal127,signal141] (.node [signal32,signal38,signal80,signal115,signal127,signal138] (.node [signal32,signal35,signal72,signal115,signal127,signal138] (.node [signal32,signal33,signal47,signal80,signal115,signal127] (.node [signal31,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal34,signal80,signal124,signal127,signal138] .nil .nil)) (.node [signal32,signal37,signal47,signal80,signal115,signal138] (.node [signal32,signal36,signal80,signal115,signal136,signal138] .nil .nil) .nil)) (.node [signal32,signal42,signal80,signal115,signal127,signal138] (.node [signal32,signal41,signal80,signal115,signal127,signal138] (.node [signal32,signal39,signal80,signal115,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal44,signal80,signal115,signal127,signal138] (.node [signal32,signal43,signal80,signal115,signal127,signal138] .nil .nil) .nil))) (.node [signal32,signal47,signal61,signal80,signal115,signal138] (.node [signal32,signal47,signal51,signal115,signal127,signal138] (.node [signal32,signal47,signal49,signal80,signal115,signal127] (.node [signal32,signal46,signal80,signal115,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal57,signal80,signal115,signal138] (.node [signal32,signal47,signal53,signal80,signal115,signal138] .nil .nil) .nil)) (.node [signal32,signal47,signal66,signal80,signal115,signal127] (.node [signal32,signal47,signal63,signal80,signal115,signal127] (.node [signal32,signal47,signal62,signal80,signal115,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal70,signal80,signal127,signal138] (.node [signal32,signal47,signal69,signal125,signal127,signal138] .nil .nil) .nil))))) (.node [signal32,signal47,signal80,signal115,signal127,signal146] (.node [signal32,signal47,signal80,signal108,signal115,signal127] (.node [signal32,signal47,signal80,signal83,signal127,signal138] (.node [signal32,signal47,signal77,signal115,signal127,signal138] (.node [signal32,signal47,signal75,signal115,signal127,signal138] (.node [signal32,signal47,signal73,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal76,signal115,signal127,signal138] .nil .nil)) (.node [signal32,signal47,signal79,signal115,signal127,signal143] (.node [signal32,signal47,signal78,signal115,signal135,signal138] .nil .nil) .nil)) (.node [signal32,signal47,signal80,signal98,signal127,signal138] (.node [signal32,signal47,signal80,signal97,signal127,signal138] (.node [signal32,signal47,signal80,signal96,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal80,signal103,signal115,signal138] (.node [signal32,signal47,signal80,signal99,signal127,signal138] .nil .nil) .nil))) (.node [signal32,signal47,signal80,signal115,signal126,signal148] (.node [signal32,signal47,signal80,signal113,signal127,signal138] (.node [signal32,signal47,signal80,signal112,signal127,signal138] (.node [signal32,signal47,signal80,signal111,signal137,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal80,signal115,signal122,signal138] (.node [signal32,signal47,signal80,signal114,signal127,signal147] .nil .nil) .nil)) (.node [signal32,signal47,signal80,signal115,signal127,signal142] (.node [signal32,signal47,signal80,signal115,signal127,signal139] (.node [signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal80,signal115,signal127,signal145] (.node [signal32,signal47,signal80,signal115,signal127,signal144] .nil .nil) .nil)))) (.node [signal32,signal47,signal81,signal115,signal127,signal138] (.node [signal32,signal47,signal80,signal116,signal127,signal138] (.node [signal32,signal47,signal80,signal115,signal132,signal138] (.node [signal32,signal47,signal80,signal115,signal129,signal138] (.node [signal32,signal47,signal80,signal115,signal128,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal115,signal131,signal138] .nil .nil)) (.node [signal32,signal47,signal80,signal115,signal134,signal138] (.node [signal32,signal47,signal80,signal115,signal133,signal138] .nil .nil) .nil)) (.node [signal32,signal47,signal80,signal119,signal127,signal138] (.node [signal32,signal47,signal80,signal118,signal127,signal138] (.node [signal32,signal47,signal80,signal117,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal47,signal80,signal123,signal127,signal138] (.node [signal32,signal47,signal80,signal120,signal127,signal138] .nil .nil) .nil))) (.node [signal32,signal59,signal80,signal115,signal127,signal138] (.node [signal32,signal47,signal109,signal115,signal127,signal138] (.node [signal32,signal47,signal93,signal115,signal127,signal138] (.node [signal32,signal47,signal92,signal115,signal127,signal138] .nil .nil) .nil) (.node [signal32,signal58,signal80,signal115,signal127,signal138] (.node [signal32,signal48,signal80,signal115,signal127,signal138] .nil .nil) .nil)) (.node [signal32,signal80,signal85,signal115,signal127,signal138] (.node [signal32,signal67,signal80,signal115,signal127,signal138] (.node [signal32,signal65,signal80,signal115,signal127,signal138] .nil .nil) .nil) (.node [signal47,signal80,signal89,signal115,signal127,signal138] (.node [signal32,signal80,signal107,signal115,signal127,signal138] .nil .nil) .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal32,signal47,signal54,signal80,signal115,signal127,signal138] (.node [signal18,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal8,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal4,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal1,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal0,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal3,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil)) (.node [signal6,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal5,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal7,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil))) (.node [signal14,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal11,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal9,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal12,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil)) (.node [signal16,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal15,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal17,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil)))) (.node [signal32,signal34,signal47,signal80,signal115,signal127,signal138] (.node [signal27,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal22,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal20,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal26,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil)) (.node [signal29,signal32,signal47,signal80,signal115,signal127,signal138] (.node [signal28,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal30,signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil))) (.node [signal32,signal45,signal47,signal80,signal115,signal127,signal138] (.node [signal32,signal36,signal47,signal80,signal115,signal127,signal138] (.node [signal32,signal35,signal47,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal40,signal47,signal80,signal115,signal127,signal138] .nil .nil)) (.node [signal32,signal47,signal52,signal80,signal115,signal127,signal138] (.node [signal32,signal47,signal50,signal80,signal115,signal127,signal138] .nil .nil) .nil)))) (.node [signal32,signal47,signal80,signal111,signal115,signal127,signal138] (.node [signal32,signal47,signal80,signal84,signal115,signal127,signal138] (.node [signal32,signal47,signal74,signal80,signal115,signal127,signal138] (.node [signal32,signal47,signal69,signal80,signal115,signal127,signal138] (.node [signal32,signal47,signal68,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal72,signal80,signal115,signal127,signal138] .nil .nil)) (.node [signal32,signal47,signal79,signal80,signal115,signal127,signal138] (.node [signal32,signal47,signal78,signal80,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal82,signal115,signal127,signal138] .nil .nil))) (.node [signal32,signal47,signal80,signal102,signal115,signal127,signal138] (.node [signal32,signal47,signal80,signal94,signal115,signal127,signal138] (.node [signal32,signal47,signal80,signal86,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal95,signal115,signal127,signal138] .nil .nil)) (.node [signal32,signal47,signal80,signal110,signal115,signal127,signal138] (.node [signal32,signal47,signal80,signal105,signal115,signal127,signal138] .nil .nil) .nil))) (.node [signal32,signal47,signal80,signal115,signal127,signal136,signal138] (.node [signal32,signal47,signal80,signal115,signal125,signal127,signal138] (.node [signal32,signal47,signal80,signal115,signal121,signal127,signal138] (.node [signal32,signal47,signal80,signal114,signal115,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal115,signal124,signal127,signal138] .nil .nil)) (.node [signal32,signal47,signal80,signal115,signal127,signal130,signal138] (.node [signal32,signal47,signal80,signal115,signal126,signal127,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal115,signal127,signal135,signal138] .nil .nil))) (.node [signal32,signal47,signal80,signal115,signal127,signal138,signal143] (.node [signal32,signal47,signal80,signal115,signal127,signal138,signal140] (.node [signal32,signal47,signal80,signal115,signal127,signal137,signal138] .nil .nil) (.node [signal32,signal47,signal80,signal115,signal127,signal138,signal141] .nil .nil)) (.node [signal32,signal47,signal80,signal115,signal127,signal138,signal148] (.node [signal32,signal47,signal80,signal115,signal127,signal138,signal147] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal32,signal47,signal80,signal115,signal127,signal138] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 4277074666 * 2 ^ 32 + 4272615552
theorem row : ∀j : Fin 108, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[5,0]⟩,⟨.and,[1,4]⟩,⟨.and,[1,6]⟩,⟨.or,[4,5]⟩,⟨.and,[9,0]⟩,⟨.or,[2,7]⟩,⟨.or,[8,3]⟩,⟨.and,[11,12]⟩,⟨.or,[10,13]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16927

open PEqualNP.Outside.L_meta_16927 in
theorem PEqualNP.Outside.L_meta_16927 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, hfan, hsize, hev⟩ := h
  obtain ⟨gates, o⟩ := C
  have hleg : ∀ g ∈ gates, legal g := by
    intro g hg
    obtain ⟨hop, cap⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, cap⟩
  obtain ⟨ds, p, mono, len, ev⟩ := replace table 9 ins (by decide) row rfl reject upper gates o hleg hev
  refine ⟨⟨ds, p⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, cap⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hop, cap⟩
  · exact le_trans len hsize
  · exact ev
