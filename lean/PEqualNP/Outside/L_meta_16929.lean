import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16929

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

-- The upper and lower halves represent opposite target labels on 52 pairs of assignments.
abbrev W := BitVec 104
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 52 := ((x >>> 52) ^^^ x).setWidth 52
def cuts (ws : List W) : BitVec 52 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 52) ++ (0 : BitVec 52)
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

def differs (i : Fin 52) (w : W) : Prop :=
  w.getLsbD (52+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 52) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 52+i.val < 104 := by omega
  have hi' : i.val < 104 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 52) :
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
  change (cuts ws)[j] = (BitVec.allOnes 52)[j]
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
  · change reachable av (BitVec.allOnes 104 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 104)
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

private def bit (k : Fin 104) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 104) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 104) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#104)[k.val] = false; simp
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 104) :
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def signal0 : W := (0x2532e2eb : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal1 : W := (0x4c6e2629 : BitVec 52) ++ (0x1cee0e08 : BitVec 52)
def signal2 : W := (0x6d7ee6eb : BitVec 52) ++ (0x1cefefef : BitVec 52)
def signal3 : W := (0x8f0456f0 : BitVec 52) ++ (0x1f000ff0 : BitVec 52)
def signal4 : W := (0xea4ef450 : BitVec 52) ++ (0xe00ff000 : BitVec 52)
def signal5 : W := (0xef788082 : BitVec 52) ++ (0xfff00000 : BitVec 52)
def signal6 : W := (0x20204222229 : BitVec 52) ++ (0x0 : BitVec 52)
def signal7 : W := (0x2930003636d : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal8 : W := (0x57400045f70 : BitVec 52) ++ (0x7000000ff0 : BitVec 52)
def signal9 : W := (0x62600062e29 : BitVec 52) ++ (0xe0e000e0e08 : BitVec 52)
def signal10 : W := (0x6b700076f6d : BitVec 52) ++ (0xe0e000fefef : BitVec 52)
def signal11 : W := (0x7c000077450 : BitVec 52) ++ (0xf80000ff000 : BitVec 52)
def signal12 : W := (0x7f700010904 : BitVec 52) ++ (0xfff00000000 : BitVec 52)
def signal13 : W := (0x7f7ef798986 : BitVec 52) ++ (0xffffff00000 : BitVec 52)
def signal14 : W := (0x4010050043e0 : BitVec 52) ++ (0x1e0 : BitVec 52)
def signal15 : W := (0x5013053003af : BitVec 52) ++ (0x1e7 : BitVec 52)
def signal16 : W := (0x84241c040e20 : BitVec 52) ++ (0x1c000e00 : BitVec 52)
def signal17 : W := (0xa02e14a00a29 : BitVec 52) ++ (0xe1ce00e08 : BitVec 52)
def signal18 : W := (0xc03415000ba0 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal19 : W := (0xe03e15a00ba9 : BitVec 52) ++ (0x1c07e1fe00ff8 : BitVec 52)
def signal20 : W := (0xf00815b00082 : BitVec 52) ++ (0x1f0001ff00000 : BitVec 52)
def signal21 : W := (0xf03c15b00ba2 : BitVec 52) ++ (0x1f0701ff00ff0 : BitVec 52)
def signal22 : W := (0xf03f10800904 : BitVec 52) ++ (0x1f07f00000000 : BitVec 52)
def signal23 : W := (0xf03ffacefd54 : BitVec 52) ++ (0x1f07fe00ff000 : BitVec 52)
def signal24 : W := (0xf7c815b774d2 : BitVec 52) ++ (0x1ff801ffff000 : BitVec 52)
def signal25 : W := (0xf7ff10810904 : BitVec 52) ++ (0x1ffff00000000 : BitVec 52)
def signal26 : W := (0x202802003e040 : BitVec 52) ++ (0x1e000 : BitVec 52)
def signal27 : W := (0x212832033a00f : BitVec 52) ++ (0x1e007 : BitVec 52)
def signal28 : W := (0x2500025308082 : BitVec 52) ++ (0x0 : BitVec 52)
def signal29 : W := (0x250912111c1c6 : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal30 : W := (0x2529300010104 : BitVec 52) ++ (0x0 : BitVec 52)
def signal31 : W := (0x252932533a3af : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal32 : W := (0x252932533e3ef : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal33 : W := (0x2f2bf10810904 : BitVec 52) ++ (0x1f07f00000000 : BitVec 52)
def signal34 : W := (0x40e00484e2400 : BitVec 52) ++ (0xe00000e0000 : BitVec 52)
def signal35 : W := (0x42a0a40ea2009 : BitVec 52) ++ (0xe0e00ee0008 : BitVec 52)
def signal36 : W := (0x4a8085ce80000 : BitVec 52) ++ (0x1ce00000 : BitVec 52)
def signal37 : W := (0x4a808fff88082 : BitVec 52) ++ (0xfff00000 : BitVec 52)
def signal38 : W := (0x4aa2e54ea2a29 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal39 : W := (0x4ac2c58cc0c00 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal40 : W := (0x4ac2c5cee2e29 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal41 : W := (0x4ae2e10800800 : BitVec 52) ++ (0xe0e00000000 : BitVec 52)
def signal42 : W := (0x4ae2e58ce2e29 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal43 : W := (0x4ae2e5cee2e29 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal44 : W := (0x4afff10810904 : BitVec 52) ++ (0xfff00000000 : BitVec 52)
def signal45 : W := (0x60a80604ba000 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal46 : W := (0x62a8a60eba009 : BitVec 52) ++ (0xe0f8ee0eff008 : BitVec 52)
def signal47 : W := (0x6380860f88002 : BitVec 52) ++ (0xe3000e0f00000 : BitVec 52)
def signal48 : W := (0x63808eff88082 : BitVec 52) ++ (0xe3000fff00000 : BitVec 52)
def signal49 : W := (0x63a8b00810004 : BitVec 52) ++ (0xe3f8f00000000 : BitVec 52)
def signal50 : W := (0x63a8b60cba004 : BitVec 52) ++ (0xe3f8fe00ff000 : BitVec 52)
def signal51 : W := (0x63a8b8f8556f4 : BitVec 52) ++ (0xe3f8f1f000ff0 : BitVec 52)
def signal52 : W := (0x63d7c60fcdf72 : BitVec 52) ++ (0xe3070e0f00ff0 : BitVec 52)
def signal53 : W := (0x6780865f88082 : BitVec 52) ++ (0xe3000e0f00000 : BitVec 52)
def signal54 : W := (0x6cab4754baba0 : BitVec 52) ++ (0xfcff0ff0ffff0 : BitVec 52)
def signal55 : W := (0x6f80875f88082 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal56 : W := (0x6f8087df88082 : BitVec 52) ++ (0x1ce00000 : BitVec 52)
def signal57 : W := (0x6fabf10810904 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal58 : W := (0x6fcbd79ddcdc6 : BitVec 52) ++ (0xe0e1cefefef : BitVec 52)
def signal59 : W := (0x6fe2e7dfeaeab : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal60 : W := (0x6febf10810904 : BitVec 52) ++ (0xe0e00000000 : BitVec 52)
def signal61 : W := (0x6febf5cef2f2d : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal62 : W := (0x6febf7dffefef : BitVec 52) ++ (0xe0e1cefefef : BitVec 52)
def signal63 : W := (0x905408a045450 : BitVec 52) ++ (0x0 : BitVec 52)
def signal64 : W := (0x90540ea4ef450 : BitVec 52) ++ (0xe00ff000 : BitVec 52)
def signal65 : W := (0x905748a045f70 : BitVec 52) ++ (0x7000000ff0 : BitVec 52)
def signal66 : W := (0x94150830051d0 : BitVec 52) ++ (0x1c070030001f0 : BitVec 52)
def signal67 : W := (0x9457483045ff0 : BitVec 52) ++ (0x1c07003000ff0 : BitVec 52)
def signal68 : W := (0x985649a041c10 : BitVec 52) ++ (0x1c0701f000e10 : BitVec 52)
def signal69 : W := (0x985649a045c50 : BitVec 52) ++ (0x1c0701f000e10 : BitVec 52)
def signal70 : W := (0x985649e045e70 : BitVec 52) ++ (0x1c000e00 : BitVec 52)
def signal71 : W := (0x985649f045ef0 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal72 : W := (0x985749a045f70 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal73 : W := (0x9c0009f000080 : BitVec 52) ++ (0x1c0001f000000 : BitVec 52)
def signal74 : W := (0x9c57410000900 : BitVec 52) ++ (0x1c07000000000 : BitVec 52)
def signal75 : W := (0x9c5749a045d50 : BitVec 52) ++ (0x1c07000000000 : BitVec 52)
def signal76 : W := (0x9c5749b045dd0 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal77 : W := (0x9c5749f045ff0 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal78 : W := (0x9c7769f267ff9 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal79 : W := (0x9d5779f345fff : BitVec 52) ++ (0x1c0701f000ff7 : BitVec 52)
def signal80 : W := (0x9f57c9fb45ff2 : BitVec 52) ++ (0x1f0701ff00ff0 : BitVec 52)
def signal81 : W := (0xb01c0a201d050 : BitVec 52) ++ (0xe0180e001f000 : BitVec 52)
def signal82 : W := (0xb01c0ea4ff450 : BitVec 52) ++ (0xe0180e00ff000 : BitVec 52)
def signal83 : W := (0xb5000a3108082 : BitVec 52) ++ (0xff000e3100000 : BitVec 52)
def signal84 : W := (0xb51d100010104 : BitVec 52) ++ (0xff1f100000000 : BitVec 52)
def signal85 : W := (0xb51d14c6f272d : BitVec 52) ++ (0xff1f11cee0e08 : BitVec 52)
def signal86 : W := (0xb5626a316aeab : BitVec 52) ++ (0xffe0ee31e0e08 : BitVec 52)
def signal87 : W := (0xb57d3af37f7ff : BitVec 52) ++ (0x1e1e7 : BitVec 52)
def signal88 : W := (0xb97e7ba37bc1f : BitVec 52) ++ (0x1c0701f01ee17 : BitVec 52)
def signal89 : W := (0xba1eeb6a1da79 : BitVec 52) ++ (0xe018efce1fe08 : BitVec 52)
def signal90 : W := (0xbd574bf34dff2 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal91 : W := (0xbd7f79f055ff4 : BitVec 52) ++ (0x1c0701f000ff0 : BitVec 52)
def signal92 : W := (0xbd7f7bf37ffff : BitVec 52) ++ (0x1c0701f01eff7 : BitVec 52)
def signal93 : W := (0xbf1ff10810904 : BitVec 52) ++ (0xff1ff00000000 : BitVec 52)
def signal94 : W := (0xd0d40ca4c1410 : BitVec 52) ++ (0xe0f80e00e1000 : BitVec 52)
def signal95 : W := (0xd0d40ca4c5450 : BitVec 52) ++ (0xe0f80e00e1000 : BitVec 52)
def signal96 : W := (0xd0d40ea4ef450 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal97 : W := (0xd0f40ca4e7450 : BitVec 52) ++ (0xe00000e0000 : BitVec 52)
def signal98 : W := (0xd0fc0ca4f7450 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal99 : W := (0xd5d53cf7c17bf : BitVec 52) ++ (0xe0f80e00e11e7 : BitVec 52)
def signal100 : W := (0xd6b5ac3ea71d9 : BitVec 52) ++ (0x1ce7e03ee01f8 : BitVec 52)
def signal101 : W := (0xda808dac80000 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal102 : W := (0xda808fff88082 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal103 : W := (0xdaa9bdacb636d : BitVec 52) ++ (0xff000fff1e1e7 : BitVec 52)
def signal104 : W := (0xdad6c10800800 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal105 : W := (0xdad6c35b2eaeb : BitVec 52) ++ (0xfffff0001e1e7 : BitVec 52)
def signal106 : W := (0xdaf6edeee7e79 : BitVec 52) ++ (0xe0e1cee0e08 : BitVec 52)
def signal107 : W := (0xdafff10810904 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal108 : W := (0xded7cdfec5ff0 : BitVec 52) ++ (0x1c0701fe00ff0 : BitVec 52)
def signal109 : W := (0xdef7edfee7ff9 : BitVec 52) ++ (0x1ce7e1fee0ff8 : BitVec 52)
def signal110 : W := (0xf0800ea488000 : BitVec 52) ++ (0xe0000e0000000 : BitVec 52)
def signal111 : W := (0xf0d40ea4cd450 : BitVec 52) ++ (0xe0000e0000000 : BitVec 52)
def signal112 : W := (0xf0dc0ea4dd450 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal113 : W := (0xf0fc000010000 : BitVec 52) ++ (0xe0f8000000000 : BitVec 52)
def signal114 : W := (0xf0fc0ea4ff450 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal115 : W := (0xf0fc2ee6ff679 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal116 : W := (0xf1fc3ea7ff45f : BitVec 52) ++ (0xe0f80e00ff007 : BitVec 52)
def signal117 : W := (0xf3fcbeacff454 : BitVec 52) ++ (0xe3f8fe00ff000 : BitVec 52)
def signal118 : W := (0xf5fc0ef7ff4d2 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal119 : W := (0xf5fd3ea4ff554 : BitVec 52) ++ (0xe0f80e00ff000 : BitVec 52)
def signal120 : W := (0xf5fd3ef7ff7ff : BitVec 52) ++ (0xe0f80e00ff1e7 : BitVec 52)
def signal121 : W := (0xf7808e3f88082 : BitVec 52) ++ (0xff000e3f00000 : BitVec 52)
def signal122 : W := (0xfafeefacffc50 : BitVec 52) ++ (0xe0f8ee00ff000 : BitVec 52)
def signal123 : W := (0xfafeefeeffe79 : BitVec 52) ++ (0xe0f8efceffe08 : BitVec 52)
def signal124 : W := (0xfcff4ff4ffff0 : BitVec 52) ++ (0xfcff0ff0ffff0 : BitVec 52)
def signal125 : W := (0xff80810800000 : BitVec 52) ++ (0xff00000000000 : BitVec 52)
def signal126 : W := (0xff808fbd88082 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal127 : W := (0xff808fff88082 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal128 : W := (0xff9d9fff98186 : BitVec 52) ++ (0xff1f1fff00000 : BitVec 52)
def signal129 : W := (0xffa0afffaa2ab : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal130 : W := (0xffa9bfff98186 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal131 : W := (0xffa9bfffbe3ef : BitVec 52) ++ (0xff000fff1e1e7 : BitVec 52)
def signal132 : W := (0xffc2cfffc8ea2 : BitVec 52) ++ (0xff000fff00e00 : BitVec 52)
def signal133 : W := (0xffd48fffcd4d2 : BitVec 52) ++ (0xff000fff00000 : BitVec 52)
def signal134 : W := (0xffd6cfffc9c92 : BitVec 52) ++ (0xff070fff00e10 : BitVec 52)
def signal135 : W := (0xffd7cfff88982 : BitVec 52) ++ (0xff070fff00000 : BitVec 52)
def signal136 : W := (0xffd7cfffcdff2 : BitVec 52) ++ (0xff070fff00ff0 : BitVec 52)
def signal137 : W := (0xffdfd10810904 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal138 : W := (0xffe2efffeaeab : BitVec 52) ++ (0xffe0efffe0e08 : BitVec 52)
def signal139 : W := (0xfffc8fffff4d2 : BitVec 52) ++ (0xfff80fffff000 : BitVec 52)
def signal140 : W := (0xfffff10810904 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal141 : W := (0xfffff14a32b2d : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal142 : W := (0xfffff35b18986 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal143 : W := (0xfffff35b3ebef : BitVec 52) ++ (0xfffff0001e1e7 : BitVec 52)
def signal144 : W := (0xfffff58cf2d04 : BitVec 52) ++ (0xfffff000e0000 : BitVec 52)
def signal145 : W := (0xfffff5cef2f2d : BitVec 52) ++ (0xfffff1cee0e08 : BitVec 52)
def signal146 : W := (0xfffff9a855d54 : BitVec 52) ++ (0xfffff00000000 : BitVec 52)
def signal147 : W := (0xfffff9f855ff4 : BitVec 52) ++ (0xfffff1f000ff0 : BitVec 52)
def signal148 : W := (0xfffffb3918986 : BitVec 52) ++ (0xfffffe3100000 : BitVec 52)
def signal149 : W := (0xfffffdacd1d14 : BitVec 52) ++ (0xfffffe00e1000 : BitVec 52)
def signal150 : W := (0xffffffac98904 : BitVec 52) ++ (0xfffffe0000000 : BitVec 52)
def signal151 : W := (0xffffffacffd54 : BitVec 52) ++ (0xfffffe00ff000 : BitVec 52)
def signal152 : W := (0xffffffff98986 : BitVec 52) ++ (0xffffffff00000 : BitVec 52)

def ins : List W := [signal32,signal43,signal77,signal114,signal127,signal140]
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
def layer4 : BinaryTree (List W) := (.node [signal32,signal77,signal86,signal114,signal140] (.node [signal32,signal43,signal51,signal114,signal127] (.node [signal23,signal32,signal43,signal77,signal127] (.node [signal13,signal32,signal43,signal77,signal114] .nil .nil) (.node [signal24,signal32,signal43,signal77,signal140] .nil .nil)) (.node [signal32,signal43,signal54,signal127,signal140] (.node [signal32,signal43,signal52,signal114,signal140] .nil .nil) (.node [signal32,signal77,signal85,signal114,signal127] .nil .nil))) (.node [signal43,signal77,signal103,signal114,signal140] (.node [signal32,signal100,signal114,signal127,signal140] (.node [signal32,signal77,signal89,signal127,signal140] .nil .nil) (.node [signal43,signal77,signal99,signal127,signal140] .nil .nil)) (.node [signal43,signal88,signal114,signal127,signal140] (.node [signal43,signal77,signal105,signal114,signal127] .nil .nil) (.node [signal58,signal77,signal114,signal127,signal140] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal32,signal43,signal72,signal114,signal127,signal140] (.node [signal31,signal43,signal77,signal114,signal127,signal140] (.node [signal14,signal43,signal92,signal114,signal127,signal140] (.node [signal6,signal62,signal77,signal114,signal127,signal140] (.node [signal3,signal32,signal43,signal49,signal114,signal127] (.node [signal1,signal32,signal77,signal84,signal114,signal127] (.node [signal0,signal43,signal77,signal104,signal114,signal127] .nil .nil) (.node [signal2,signal32,signal43,signal77,signal114,signal127] .nil .nil)) (.node [signal5,signal12,signal32,signal43,signal77,signal114] (.node [signal4,signal22,signal32,signal43,signal77,signal127] .nil .nil) .nil)) (.node [signal9,signal32,signal77,signal83,signal114,signal140] (.node [signal8,signal32,signal43,signal47,signal114,signal140] (.node [signal7,signal43,signal77,signal101,signal114,signal140] .nil .nil) .nil) (.node [signal11,signal20,signal32,signal43,signal77,signal140] (.node [signal10,signal32,signal43,signal77,signal114,signal140] .nil .nil) .nil))) (.node [signal25,signal32,signal43,signal77,signal114,signal127] (.node [signal18,signal32,signal43,signal45,signal127,signal140] (.node [signal16,signal32,signal109,signal114,signal127,signal140] (.node [signal15,signal43,signal77,signal94,signal127,signal140] .nil .nil) (.node [signal17,signal32,signal77,signal81,signal127,signal140] .nil .nil)) (.node [signal21,signal32,signal43,signal77,signal127,signal140] (.node [signal19,signal32,signal43,signal77,signal127,signal140] .nil .nil) .nil)) (.node [signal28,signal43,signal77,signal114,signal131,signal140] (.node [signal27,signal43,signal68,signal114,signal127,signal140] (.node [signal26,signal43,signal77,signal120,signal127,signal140] .nil .nil) .nil) (.node [signal30,signal43,signal77,signal114,signal127,signal143] (.node [signal29,signal39,signal77,signal114,signal127,signal140] .nil .nil) .nil)))) (.node [signal32,signal43,signal50,signal114,signal127,signal140] (.node [signal32,signal40,signal77,signal114,signal127,signal140] (.node [signal32,signal36,signal77,signal114,signal138,signal140] (.node [signal32,signal34,signal77,signal123,signal127,signal140] (.node [signal32,signal33,signal43,signal77,signal114,signal127] .nil .nil) (.node [signal32,signal35,signal66,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal38,signal77,signal114,signal127,signal140] (.node [signal32,signal37,signal43,signal77,signal114,signal140] .nil .nil) .nil)) (.node [signal32,signal43,signal44,signal77,signal114,signal127] (.node [signal32,signal42,signal77,signal114,signal127,signal140] (.node [signal32,signal41,signal77,signal114,signal127,signal145] .nil .nil) .nil) (.node [signal32,signal43,signal48,signal77,signal114,signal140] (.node [signal32,signal43,signal46,signal114,signal127,signal140] .nil .nil) .nil))) (.node [signal32,signal43,signal64,signal77,signal127,signal140] (.node [signal32,signal43,signal57,signal77,signal114,signal127] (.node [signal32,signal43,signal55,signal77,signal114,signal140] (.node [signal32,signal43,signal53,signal77,signal114,signal140] .nil .nil) (.node [signal32,signal43,signal56,signal77,signal114,signal140] .nil .nil)) (.node [signal32,signal43,signal63,signal124,signal127,signal140] (.node [signal32,signal43,signal60,signal77,signal114,signal127] .nil .nil) .nil)) (.node [signal32,signal43,signal69,signal114,signal127,signal140] (.node [signal32,signal43,signal67,signal114,signal127,signal140] (.node [signal32,signal43,signal65,signal114,signal127,signal140] .nil .nil) .nil) (.node [signal32,signal43,signal71,signal114,signal127,signal140] (.node [signal32,signal43,signal70,signal114,signal127,signal140] .nil .nil) .nil))))) (.node [signal32,signal43,signal77,signal114,signal127,signal148] (.node [signal32,signal43,signal77,signal110,signal139,signal140] (.node [signal32,signal43,signal77,signal95,signal127,signal140] (.node [signal32,signal43,signal76,signal114,signal127,signal140] (.node [signal32,signal43,signal74,signal114,signal127,signal147] (.node [signal32,signal43,signal73,signal114,signal136,signal140] .nil .nil) (.node [signal32,signal43,signal75,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal77,signal93,signal114,signal127] (.node [signal32,signal43,signal77,signal82,signal127,signal140] .nil .nil) .nil)) (.node [signal32,signal43,signal77,signal98,signal127,signal140] (.node [signal32,signal43,signal77,signal97,signal127,signal140] (.node [signal32,signal43,signal77,signal96,signal127,signal140] .nil .nil) .nil) (.node [signal32,signal43,signal77,signal107,signal114,signal127] (.node [signal32,signal43,signal77,signal102,signal114,signal140] .nil .nil) .nil))) (.node [signal32,signal43,signal77,signal114,signal127,signal137] (.node [signal32,signal43,signal77,signal114,signal121,signal140] (.node [signal32,signal43,signal77,signal112,signal127,signal140] (.node [signal32,signal43,signal77,signal111,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal113,signal127,signal151] .nil .nil)) (.node [signal32,signal43,signal77,signal114,signal126,signal140] (.node [signal32,signal43,signal77,signal114,signal125,signal152] .nil .nil) .nil)) (.node [signal32,signal43,signal77,signal114,signal127,signal142] (.node [signal32,signal43,signal77,signal114,signal127,signal141] (.node [signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) .nil) (.node [signal32,signal43,signal77,signal114,signal127,signal146] (.node [signal32,signal43,signal77,signal114,signal127,signal144] .nil .nil) .nil)))) (.node [signal32,signal43,signal77,signal118,signal127,signal140] (.node [signal32,signal43,signal77,signal114,signal133,signal140] (.node [signal32,signal43,signal77,signal114,signal129,signal140] (.node [signal32,signal43,signal77,signal114,signal127,signal150] (.node [signal32,signal43,signal77,signal114,signal127,signal149] .nil .nil) (.node [signal32,signal43,signal77,signal114,signal128,signal140] .nil .nil)) (.node [signal32,signal43,signal77,signal114,signal132,signal140] (.node [signal32,signal43,signal77,signal114,signal130,signal140] .nil .nil) .nil)) (.node [signal32,signal43,signal77,signal115,signal127,signal140] (.node [signal32,signal43,signal77,signal114,signal135,signal140] (.node [signal32,signal43,signal77,signal114,signal134,signal140] .nil .nil) .nil) (.node [signal32,signal43,signal77,signal117,signal127,signal140] (.node [signal32,signal43,signal77,signal116,signal127,signal140] .nil .nil) .nil))) (.node [signal32,signal43,signal91,signal114,signal127,signal140] (.node [signal32,signal43,signal79,signal114,signal127,signal140] (.node [signal32,signal43,signal77,signal122,signal127,signal140] (.node [signal32,signal43,signal77,signal119,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal78,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal90,signal114,signal127,signal140] (.node [signal32,signal43,signal80,signal114,signal127,signal140] .nil .nil) .nil)) (.node [signal32,signal61,signal77,signal114,signal127,signal140] (.node [signal32,signal59,signal77,signal114,signal127,signal140] (.node [signal32,signal43,signal108,signal114,signal127,signal140] .nil .nil) .nil) (.node [signal43,signal77,signal87,signal114,signal127,signal140] (.node [signal32,signal77,signal106,signal114,signal127,signal140] .nil .nil) .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal32,signal43,signal49,signal77,signal114,signal127,signal140] (.node [signal18,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal8,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal4,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal1,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal0,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal3,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil)) (.node [signal6,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal5,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal7,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil))) (.node [signal14,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal11,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal9,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal12,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil)) (.node [signal16,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal15,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal17,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil)))) (.node [signal32,signal34,signal43,signal77,signal114,signal127,signal140] (.node [signal27,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal22,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal20,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal26,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil)) (.node [signal29,signal32,signal43,signal77,signal114,signal127,signal140] (.node [signal28,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal30,signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil))) (.node [signal32,signal41,signal43,signal77,signal114,signal127,signal140] (.node [signal32,signal36,signal43,signal77,signal114,signal127,signal140] (.node [signal32,signal35,signal43,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal32,signal39,signal43,signal77,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal47,signal77,signal114,signal127,signal140] (.node [signal32,signal43,signal45,signal77,signal114,signal127,signal140] .nil .nil) .nil)))) (.node [signal32,signal43,signal77,signal110,signal114,signal127,signal140] (.node [signal32,signal43,signal77,signal83,signal114,signal127,signal140] (.node [signal32,signal43,signal68,signal77,signal114,signal127,signal140] (.node [signal32,signal43,signal63,signal77,signal114,signal127,signal140] (.node [signal32,signal43,signal62,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal66,signal77,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal74,signal77,signal114,signal127,signal140] (.node [signal32,signal43,signal73,signal77,signal114,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal81,signal114,signal127,signal140] .nil .nil))) (.node [signal32,signal43,signal77,signal101,signal114,signal127,signal140] (.node [signal32,signal43,signal77,signal92,signal114,signal127,signal140] (.node [signal32,signal43,signal77,signal84,signal114,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal94,signal114,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal77,signal109,signal114,signal127,signal140] (.node [signal32,signal43,signal77,signal104,signal114,signal127,signal140] .nil .nil) .nil))) (.node [signal32,signal43,signal77,signal114,signal127,signal138,signal140] (.node [signal32,signal43,signal77,signal114,signal124,signal127,signal140] (.node [signal32,signal43,signal77,signal114,signal120,signal127,signal140] (.node [signal32,signal43,signal77,signal113,signal114,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal114,signal123,signal127,signal140] .nil .nil)) (.node [signal32,signal43,signal77,signal114,signal127,signal131,signal140] (.node [signal32,signal43,signal77,signal114,signal125,signal127,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal114,signal127,signal136,signal140] .nil .nil))) (.node [signal32,signal43,signal77,signal114,signal127,signal140,signal147] (.node [signal32,signal43,signal77,signal114,signal127,signal140,signal143] (.node [signal32,signal43,signal77,signal114,signal127,signal139,signal140] .nil .nil) (.node [signal32,signal43,signal77,signal114,signal127,signal140,signal145] .nil .nil)) (.node [signal32,signal43,signal77,signal114,signal127,signal140,signal152] (.node [signal32,signal43,signal77,signal114,signal127,signal140,signal151] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal32,signal43,signal77,signal114,signal127,signal140] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 4277074666 * 2 ^ 32 + 4272617608
theorem row : ∀j : Fin 104, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[5,1]⟩,⟨.and,[4,1]⟩,⟨.or,[7,2]⟩,⟨.and,[1,5]⟩,⟨.or,[9,3]⟩,⟨.and,[8,10]⟩,⟨.or,[6,4]⟩,⟨.and,[0,12]⟩,⟨.or,[13,11]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_16929

open PEqualNP.Outside.L_meta_16929 in
theorem PEqualNP.Outside.L_meta_16929 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272617608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272617608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
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
