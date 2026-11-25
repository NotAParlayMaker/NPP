import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16465

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

abbrev W := BitVec 64

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 32 := ((x >>> 32) ^^^ x).setWidth 32
def cuts (ws : List W) : BitVec 32 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 32) ++ (0 : BitVec 32)
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

def differs (i : Fin 32) (w : W) : Prop :=
  w.getLsbD (32+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 32) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 32+i.val < 64 := by omega
  have hi' : i.val < 64 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 32) :
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
  change (cuts ws)[j] = (BitVec.allOnes 32)[j]
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

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
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
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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

def targetFun (T : ℕ) (x : Fin 6 → Bool) : Bool :=
  Nat.testBit T (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (T : ℕ) (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 64,
      targetFun T (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun T x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def optimizedM (tbl : List (ℕ × ℕ × List W)) : ℕ → ℕ → List W → Bool
  | 0, e, ws => !(tbl.contains (0, e, ws)) && (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => !(tbl.contains (k + 1, extra, ws)) &&
    ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a, b, r) => dispatch extra (optimizedM tbl k) a b r))

theorem dispatch_mono {e : ℕ} {n1 n2 : ℕ → List W → Bool}
    (h : ∀ e' l, n1 e' l = true → n2 e' l = true) {a b : W} {r : List W}
    (hd : dispatch e n1 a b r = true) : dispatch e n2 a b r = true := by
  unfold dispatch at *
  simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at *
  obtain ⟨w, hw, hx⟩ := hd
  refine ⟨w, hw, ?_⟩
  rcases hx with ((⟨h1, h2⟩ | ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩)⟩) | ⟨h1, h2⟩)
  · exact Or.inl (Or.inl ⟨h1, h _ _ h2⟩)
  · exact Or.inl (Or.inr ⟨h1, Or.inl ⟨h2, h _ _ h3⟩⟩)
  · exact Or.inl (Or.inr ⟨h1, Or.inr ⟨h2, h _ _ h3⟩⟩)
  · exact Or.inr ⟨h1, h _ _ h2⟩

theorem optM_sound (tbl : List (ℕ × ℕ × List W))
    (htbl : ∀ t ∈ tbl, optimized t.1 t.2.1 t.2.2 = false) :
    ∀ k e ws, optimized k e ws = true → optimizedM tbl k e ws = true := by
  intro k
  induction k with
  | zero =>
    intro e ws h
    have hn : tbl.contains (0, e, ws) = false := by
      rcases hc : tbl.contains (0, e, ws) with _ | _
      · rfl
      · have := htbl _ (List.elem_iff.mp hc); simp_all
    simp only [optimizedM, hn, Bool.not_false, Bool.true_and]
    simpa [optimized] using h
  | succ k ih =>
    intro e ws h
    have hn : tbl.contains (k + 1, e, ws) = false := by
      rcases hc : tbl.contains (k + 1, e, ws) with _ | _
      · rfl
      · have := htbl _ (List.elem_iff.mp hc); simp_all
    simp only [optimizedM, hn, Bool.not_false, Bool.true_and]
    simp only [optimized, Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨p, hp, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, dispatch_mono (fun e' l => ih e' l) hd⟩

theorem opt_false_of_M {tbl : List (ℕ × ℕ × List W)}
    (htbl : ∀ t ∈ tbl, optimized t.1 t.2.1 t.2.2 = false) {k e : ℕ} {ws : List W}
    (h : optimizedM tbl k e ws = false) : optimized k e ws = false := by
  rcases ho : optimized k e ws with _ | _
  · rfl
  · have := optM_sound tbl htbl k e ws ho; simp_all

theorem singles_perm {α : Type} : ∀ {l : List α} {a : α} {rest : List α},
    (a, rest) ∈ singles l → l.Perm (a :: rest)
  | [], _, _, h => by simp [singles] at h
  | x :: xs, a, rest, h => by
    simp only [singles, List.mem_cons, List.mem_map, Prod.mk.injEq, Prod.exists] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨b, bs, hm, rfl, rfl⟩
    · exact .refl _
    · exact ((singles_perm hm).cons x).trans (.swap _ _ _)

theorem pairs_perm {α : Type} : ∀ {l : List α} {a b : α} {r : List α},
    (a, b, r) ∈ pairs l → l.Perm (a :: b :: r)
  | [], _, _, _, h => by simp [pairs] at h
  | x :: xs, a, b, r, h => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq, Prod.exists] at h
    rcases h with ⟨c, cs, hm, rfl, rfl, rfl⟩ | ⟨c, d, cs, hm, rfl, rfl, rfl⟩
    · exact (singles_perm hm).cons x
    · have := (pairs_perm hm).cons x
      exact this.trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)) |>.trans (by
        exact List.Perm.refl _)

theorem pick_two_pos {α : Type} [DecidableEq α] : ∀ {l : List α} {a b : α} {r : List α},
    l.Perm (a :: b :: r) → ∃ r', ((a, b, r') ∈ pairs l ∨ (b, a, r') ∈ pairs l) ∧ r.Perm r'
  | [], _, _, _, h => absurd h.length_eq (by simp)
  | x :: xs, a, b, r, h => by
    by_cases hxa : x = a
    · subst hxa
      have hxs : xs.Perm (b :: r) := List.Perm.cons_inv h
      obtain ⟨rest, hm, hp⟩ := pick_one (hxs.mem_iff.mpr (List.mem_cons_self ..))
      refine ⟨rest, .inl ?_, List.Perm.cons_inv (hxs.symm.trans hp)⟩
      simp only [pairs, List.mem_append, List.mem_map]
      exact .inl ⟨(b, rest), hm, rfl⟩
    by_cases hxb : x = b
    · subst hxb
      have hxs : xs.Perm (a :: r) := List.Perm.cons_inv (h.trans (.swap _ _ _))
      obtain ⟨rest, hm, hp⟩ := pick_one (hxs.mem_iff.mpr (List.mem_cons_self ..))
      refine ⟨rest, .inr ?_, List.Perm.cons_inv (hxs.symm.trans hp)⟩
      simp only [pairs, List.mem_append, List.mem_map]
      exact .inl ⟨(a, rest), hm, rfl⟩
    · have hxr : x ∈ r := by
        have := h.subset (List.mem_cons_self ..)
        simp only [List.mem_cons] at this
        rcases this with e | e | e
        · exact absurd e hxa
        · exact absurd e hxb
        · exact e
      have hr := List.perm_cons_erase hxr
      have h2 : (x :: xs).Perm (x :: a :: b :: r.erase x) :=
        h.trans (((hr.cons b).cons a).trans (((List.Perm.swap _ _ _).cons a).trans (List.Perm.swap _ _ _)))
      obtain ⟨r', hm, hp⟩ := pick_two_pos (List.Perm.cons_inv h2)
      refine ⟨x :: r', ?_, hr.trans (hp.cons x)⟩
      simp only [pairs, List.mem_append, List.mem_map]
      rcases hm with hm | hm
      · exact .inl (.inr ⟨(a, b, r'), hm, rfl⟩)
      · exact .inr (.inr ⟨(b, a, r'), hm, rfl⟩)

theorem cuts_perm {l l' : List W} (h : l.Perm l') : cuts l = cuts l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [cuts, List.foldr_cons] at ih ⊢; rw [ih]
  | swap x y l => simp only [cuts, List.foldr_cons]; ac_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def PermInv (next : ℕ → List W → Bool) : Prop := ∀ e l l', l.Perm l' → next e l = next e l'

theorem dispatch_perm {next : ℕ → List W → Bool} (hn : PermInv next) (e : ℕ) (a b : W) {r r' : List W}
    (h : r.Perm r') : dispatch e next a b r = dispatch e next a b r' := by
  unfold dispatch
  dsimp only
  rw [cuts_perm h]
  congr 1; funext w
  rw [hn _ (w :: r) (w :: r') (h.cons w), hn _ (w :: a :: r) (w :: a :: r') ((h.cons a).cons w),
    hn _ (w :: b :: r) (w :: b :: r') ((h.cons b).cons w),
    hn _ (w :: a :: b :: r) (w :: a :: b :: r') (((h.cons b).cons a).cons w)]

theorem dispatch_swap {next : ℕ → List W → Bool} (hn : PermInv next) (e : ℕ) (a b : W) (r : List W) :
    dispatch e next a b r = dispatch e next b a r := by
  unfold dispatch
  have hops : (ops b a).Perm (ops a b) := by
    simp only [ops, BitVec.and_comm b a, BitVec.or_comm b a]
    exact ((List.Perm.swap _ _ _).cons _).cons _
  dsimp only
  rw [hops.any_eq]
  congr 1; funext w
  rw [hn _ (w :: b :: a :: r) (w :: a :: b :: r) ((List.Perm.swap _ _ _).cons w),
    show sep w ||| cuts r ||| sep b ||| sep a = sep w ||| cuts r ||| sep a ||| sep b by ac_rfl]
  cases next e (w :: r) <;> cases next (e - 1) (w :: a :: r) <;> cases next (e - 1) (w :: b :: r) <;>
    simp [Bool.or_comm]

theorem beq_single_perm {l l' : List W} (h : l.Perm l') (g : W) : (l == [g]) = (l' == [g]) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]
  constructor
  · rintro rfl; exact (List.perm_singleton.mp h.symm)
  · rintro rfl; exact (List.perm_singleton.mp h)

theorem optimized_perm : ∀ k, PermInv (optimized k) := by
  intro k
  induction k with
  | zero => intro e l l' h; simp only [optimized]; rw [beq_single_perm h, beq_single_perm h]
  | succ k ih =>
    have one : ∀ e (l l' : List W), l.Perm l' →
        (pairs l).any (fun (a, b, r) => dispatch e (optimized k) a b r) = true →
        (pairs l').any (fun (a, b, r) => dispatch e (optimized k) a b r) = true := by
      intro e l l' h hl
      obtain ⟨⟨a, b, r⟩, hm, hd⟩ := List.any_eq_true.mp hl
      obtain ⟨r', hm', hp⟩ := pick_two_pos (h.symm.trans (pairs_perm hm))
      apply List.any_eq_true.mpr
      rcases hm' with hm' | hm'
      · exact ⟨(a, b, r'), hm', by simpa [dispatch_perm ih e a b hp] using hd⟩
      · exact ⟨(b, a, r'), hm', by simpa [← dispatch_swap ih e a b r', dispatch_perm ih e a b hp] using hd⟩
    intro e l l' h
    simp only [optimized]
    rw [beq_single_perm h, beq_single_perm h]
    congr 1
    rw [Bool.eq_iff_iff]
    exact ⟨one e l l' h, one e l' l h.symm⟩

def hit (tbl : List (ℕ × ℕ × List W)) (k e : ℕ) (ws : List W) : Bool :=
  tbl.any (fun t => t.1 == k && t.2.1 == e && t.2.2.isPerm ws)

def optimizedP (tbl : List (ℕ × ℕ × List W)) : ℕ → ℕ → List W → Bool
  | 0, e, ws => !(hit tbl 0 e ws) && (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => !(hit tbl (k + 1) extra ws) &&
    ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a, b, r) => dispatch extra (optimizedP tbl k) a b r))

theorem hit_false {tbl : List (ℕ × ℕ × List W)}
    (htbl : ∀ t ∈ tbl, optimized t.1 t.2.1 t.2.2 = false) {k e : ℕ} {ws : List W}
    (h : optimized k e ws = true) : hit tbl k e ws = false := by
  rcases hc : hit tbl k e ws with _ | _
  · rfl
  · obtain ⟨t, ht, hx⟩ := List.any_eq_true.mp hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at hx
    obtain ⟨⟨h1, h2⟩, hp⟩ := hx
    have := htbl t ht
    rw [optimized_perm t.1 t.2.1 _ _ hp, h1, h2, h] at this
    exact absurd this (by simp)

theorem optP_sound (tbl : List (ℕ × ℕ × List W))
    (htbl : ∀ t ∈ tbl, optimized t.1 t.2.1 t.2.2 = false) :
    ∀ k e ws, optimized k e ws = true → optimizedP tbl k e ws = true := by
  intro k
  induction k with
  | zero =>
    intro e ws h
    simp only [optimizedP, hit_false htbl h, Bool.not_false, Bool.true_and]
    simpa [optimized] using h
  | succ k ih =>
    intro e ws h
    simp only [optimizedP, hit_false htbl h, Bool.not_false, Bool.true_and]
    simp only [optimized, Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨p, hp, hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, dispatch_mono (fun e' l => ih e' l) hd⟩

theorem opt_false_of_P {tbl : List (ℕ × ℕ × List W)}
    (htbl : ∀ t ∈ tbl, optimized t.1 t.2.1 t.2.2 = false) {k e : ℕ} {ws : List W}
    (h : optimizedP tbl k e ws = false) : optimized k e ws = false := by
  rcases ho : optimized k e ws with _ | _
  · rfl
  · have := optP_sound tbl htbl k e ws ho; simp_all

theorem tbl_nil : ∀ u ∈ ([] : List (ℕ × ℕ × List W)), optimized u.1 u.2.1 u.2.2 = false :=
  fun _ h => absurd h List.not_mem_nil

theorem tbl_cons {t : ℕ × ℕ × List W} {l : List (ℕ × ℕ × List W)}
    (h1 : optimized t.1 t.2.1 t.2.2 = false) (h2 : ∀ u ∈ l, optimized u.1 u.2.1 u.2.2 = false) :
    ∀ u ∈ t :: l, optimized u.1 u.2.1 u.2.2 = false :=
  List.forall_mem_cons.2 ⟨h1, h2⟩

def a0 : W := 0x8081222490a5
def a1 : W := 0x2ca0c1e12fe4f1e5
def a2 : W := 0x420c9e97622d9ebf
def a3 : W := 0x754b426cfddbdefe
def a4 : W := 0x8ab401129eb60353
def a5 : W := 0x93412c08d3496d08
def a6 : W := 0x6eacdff76fedffff
def a7 : W := 0x2ca041600dc06140
def a8 : W := 0x420c1e1640090e1a
def a9 : W := 0x240040602dc0d0e4
def a10 : W := 0x7debc3edffffffff
def a11 : W := 0x8a0818102242101
def a12 : W := 0x514b020cd01b0e1a
def a13 : W := 0x8a001000ea40141
def a14 : W := 0xaeb4c1f3bff6f3f7
def a15 : W := 0x2400c0e12140f0a4
def a16 : W := 0x8214001290120212
def a17 : W := 0x3406100
def a18 : W := 0xbfe1ede9ffedfded
def a19 : W := 0x2ca0c1e12ca490e5
def a20 : W := 0x93412c08d0090c08
def a21 : W := 0x4008020460099ebe
def a22 : W := 0x774fdeffffffdeff
def a23 : W := 0x2049c9302240001
def a24 : W := 0x354340689dd24040
def a25 : W := 0x204001202240213
def a26 : W := 0xcabc9f97febf9fff
def a27 : W := 0x40089e8560099cac
def a28 : W := 0x88b001009c920140
def a29 : W := 0x2000c0042090c08
def a30 : W := 0xd34dbe9ff36dffbf
def a31 : W := 0x400c9297202492b7
def a32 : W := 0x9141200891406100
def a33 : W := 0x9c920252
def a34 : W := 0xffff437effffdfff
def a35 : W := 0x754b426c6149dcac
def a36 : W := 0x8ab4011202240101
def a37 : W := 0x11410008d1494c08
def a38 : W := 0xf74b6e6cffdbfffe
def a39 : W := 0x640a42642c9292f6
def a40 : W := 0x82002c0002002100
def a41 : W := 0x8200000092000100
def a42 : W := 0x9bf52d1adfff6f5b
def a43 : W := 0x8b401120cb60253
def a44 : W := 0x11412c0841496c08
def a45 : W := 0x2ea0cde16fedfded
def a46 : W := 0x714b024cf1db8e5e
def a47 : W := 0xb5085a3cbd085abc
def a48 : W := 0x2000c0040090c08
def a49 : W := 0x40090c08
def a50 : W := 0x714b024cb1d28256
def a51 : W := 0x8ab40d12debf0f5b
def a52 : W := 0xc0040090c08
def a53 : W := 0x88b401129cb60353
def a54 : W := 0xb7085e3cff095ebc
def a55 : W := 0xb508523cbd0052b4
def a56 : W := 0xd14db29fb164f3b7
def a57 : W := 0x240040202d0050a4
def a58 : W := 0x8a081c102e4a141
def a59 : W := 0x80812364f1a5
def a60 : W := 0x2ca041600c800040
def a61 : W := 0xd34d3e1ed0090e1a
def a62 : W := 0xf54b5a7cfddbdefe
def a63 : W := 0x840058300c0050a0
def a64 : W := 0x2000004021c08044
def a65 : W := 0x0
def a66 : W := 0xca0c1a10e2471a1
def a67 : W := 0x20008004
def a68 : W := 0x620c9ed763ed9eff
def a69 : W := 0x2000004001c00040
def a70 : W := 0x420c9e97422d1ebb
def a71 : W := 0x800040
def a72 : W := 0xaab40152bff68357
def a73 : W := 0x2000004021408004
def a74 : W := 0x8ab401129e360313
def a75 : W := 0x1400000
def a76 : W := 0xb3412c48f3c9ed4c
def a77 : W := 0x2000004020808044
def a78 : W := 0x93412c08d2096d08
def a79 : W := 0x2000000021000004
def a80 : W := 0xb5085a7cbdc8dafc
def a81 : W := 0x4000c08040
def a82 : W := 0x95085a3c9c085ab8
def a83 : W := 0xb7497e3cff497fbc
def a84 : W := 0x240852342c0012b4
def a85 : W := 0x40088285622d9ebf
def a86 : W := 0x7fefdfffffffffff
def a87 : W := 0x2041c1200000000
def a88 : W := 0x3de341689dd26140
def a89 : W := 0xf34b2e4cf3dbef5e
def a90 : W := 0x600a024420928256
def a91 : W := 0x4043004040d38442
def a92 : W := 0x8a001009eb60353
def a93 : W := 0xffffc3ffffffffff
def a94 : W := 0x754bc2ed6149fcac
def a95 : W := 0x8214001200000000
def a96 : W := 0x11410008d3496d08
def a97 : W := 0xffebefedffffffff
def a98 : W := 0x6caac3e52cb692f7
def a99 : W := 0x82002c0000000000
def a100 : W := 0x3508422cbd085abc
def a101 : W := 0xfdebdbfdffffffff
def a102 : W := 0x48e381c142f7a543
def a103 : W := 0x8000181000000000
def a104 : W := 0x8081022410a1
def a105 : W := 0x4eacdfb76e2dffbf
def a106 : W := 0xca041200c006100
def a107 : W := 0x420c1e1660098e1e
def a108 : W := 0x8a001000e240101
def a109 : W := 0x8eb4c1b39eb673f3
def a110 : W := 0x400c0a1000070a0
def a111 : W := 0x8214001290920252
def a112 : W := 0x2006100
def a113 : W := 0x9fe1eda9df6d7da9
def a114 : W := 0xca0c1a10c2410a1
def a115 : W := 0x93412c08d1490c08
def a116 : W := 0x40040200c0050a0
def a117 : W := 0xbda8dbbdbf2c7bbd
def a118 : W := 0xb1081a1cb1080a1c
def a119 : W := 0x4008020440090e1a
def a120 : W := 0x534f9e9ff23f9ebf
def a121 : W := 0x2049c93222490a5
def a122 : W := 0x1143000890120000
def a123 : W := 0x90120212
def a124 : W := 0xdbff031edebf0f5b
def a125 : W := 0x514b020c40090c08
def a126 : W := 0x8ab401120ea40141
def a127 : W := 0x11410008d0090c08
def a128 : W := 0xd34b2e0cd35b6f1a
def a129 : W := 0x400a020400120212
def a130 : W := 0x82002c0003406100
def a131 : W := 0x1108020c90080a18
def a132 : W := 0xf54b5a3cfd1b5ebe
def a133 : W := 0x4043000040130402
def a134 : W := 0xa40058302d0050a4
def a135 : W := 0x2240001
def a136 : W := 0x4aac9f976ead9fff
def a137 : W := 0x8a001000c800140
def a138 : W := 0x420c9e9760099ebe
def a139 : W := 0x79eb034cffff8f5f
def a140 : W := 0x714b024cf15b8e1e
def a141 : W := 0x2000100
def a142 : W := 0x9be12d08dfed6d49
def a143 : W := 0x8a001000ca40041
def a144 : W := 0x93412c08d1496c08
def a145 : W := 0xc000000
def a146 : W := 0xbda85b3cbfac5bfd
def a147 : W := 0x8a0010002a40141
def a148 : W := 0xb5085a3cb1085abc
def a149 : W := 0x90920252
def a150 : W := 0x714b024c61498c0c
def a151 : W := 0xbda8dbfdbfecfbfd
def a152 : W := 0x2048093222492b7
def a153 : W := 0xeebcdff7ffffffff
def a154 : W := 0x40081e0440090c08
def a155 : W := 0xacb041609dd26140
def a156 : W := 0x20000040b1d28256
def a157 : W := 0x8eb4c1b30e2471a1
def a158 : W := 0x8200000093406100
def a159 : W := 0xbff5edfbffffffff
def a160 : W := 0x11412c0840090c08
def a161 : W := 0x2cb4c1f32cb692f7
def a162 : W := 0xa4004030bd0052b4
def a163 : W := 0xbfbcdbffbffefbff
def a164 : W := 0xab481c302f6a143
def a165 : W := 0x11081a0c00080808
def a166 : W := 0x8081200090a4
def a167 : W := 0x660cdef7636dfebf
def a168 : W := 0x2400406001406000
def a169 : W := 0x420c1e16422d0e1b
def a170 : W := 0x754bc2edf1dbfefe
def a171 : W := 0x514b020cd09b0e5a
def a172 : W := 0x1406000
def a173 : W := 0xb741ece9f349fdac
def a174 : W := 0x2400c0e1200090a4
def a175 : W := 0x93412c08d2090d08
def a176 : W := 0x24004020210050a4
def a177 : W := 0xb508dafdbd48fabc
def a178 : W := 0x80c10040a000
def a179 : W := 0x91081a1c9c080a18
def a180 : W := 0x204001200000212
def a181 : W := 0xc21c9e97f23f9ebf
def a182 : W := 0x40089e85622d9cad
def a183 : W := 0x8010000090120000
def a184 : W := 0xf35f025ef1db8e5e
def a185 : W := 0x714b024c61c98c4c
def a186 : W := 0x8200000090000000
def a187 : W := 0x93552c1ad35b6f1a
def a188 : W := 0x14001200120212
def a189 : W := 0x11412c0843496d08
def a190 : W := 0x8000001090000210
def a191 : W := 0xb71c5a3ebd1a5abe
def a192 : W := 0x214000200120002
def a193 : W := 0x35085a2c2d0858ac
def a194 : W := 0x2000000
def a195 : W := 0x420c9e97636dffbf
def a196 : W := 0x1406100
def a197 : W := 0x420c9e97602d9ebf
def a198 : W := 0x714b024cf3dbef5e
def a199 : W := 0x714b024cf09b8e5e
def a200 : W := 0x8ab401129ff66353
def a201 : W := 0x8ab401129cb60253
def a202 : W := 0x1004000
def a203 : W := 0xb5085a3cbf487bbc
def a204 : W := 0x2402100
def a205 : W := 0xb5085a3cbc081abc
def a206 : W := 0x11410008d1490c08
def a207 : W := 0x2008c81622d9cad
def a208 : W := 0xffedffffffedffff
def a209 : W := 0x400c121600000212
def a210 : W := 0xbde161689dc06140
def a211 : W := 0x82002c0002006100
def a212 : W := 0x31410048f1c98c4c
def a213 : W := 0x8ea0eda10e2471a1
def a214 : W := 0x8aa001009ea40141
def a215 : W := 0x3541ece96149fcac
def a216 : W := 0xb5004828bd0858ac
def a217 : W := 0xbfe9fffdffedfffd
def a218 : W := 0x8121400000210
def a219 : W := 0xae1a5c142e5a541
def a220 : W := 0x8081202490a5
def a221 : W := 0x6eacdff76ead9eff
def a222 : W := 0x420c1e1642090e1a
def a223 : W := 0x7debc3edfdff9eff
def a224 : W := 0x514b020cd15b0e1a
def a225 : W := 0xaeb4c1f3beb693f7
def a226 : W := 0x8214001292120312
def a227 : W := 0x240040202c0010a4
def a228 : W := 0xbda8dbfdbdacdafd
def a229 : W := 0x8a081c100a48041
def a230 : W := 0x91081a1c91084a18
def a231 : W := 0xd34dbe9ff22d9ebf
def a232 : W := 0x400c9297222492b7
def a233 : W := 0x9141200890000000
def a234 : W := 0xf34b2e4cf1db8e5e
def a235 : W := 0x600a024421d28256
def a236 : W := 0x9bf52d1adebf0f5b
def a237 : W := 0x8b401120eb60353
def a238 : W := 0x9100080890080808
def a239 : W := 0xb7497e3cfd095ebc
def a240 : W := 0x241240040010400
def a241 : W := 0x240852342d0052b4
def a242 : W := 0x714b82cdf3ff9eff
def a243 : W := 0x714b024cd1db0e5a
def a244 : W := 0x8ab48193beb693f7
def a245 : W := 0x8ab401129c920352
def a246 : W := 0x9341ac89f36dfdad
def a247 : W := 0x93412c08d1496d08
def a248 : W := 0x200010a4
def a249 : W := 0xb508dabdbf2cdabd
def a250 : W := 0x808102248001
def a251 : W := 0xb5085a3c9d084a18
def a252 : W := 0x4008020460098e1e
def a253 : W := 0x3143004891d20040
def a254 : W := 0x6008024461c98e5e
def a255 : W := 0xea4ddb30e2471a1
def a256 : W := 0xaa401120ea40353
def a257 : W := 0x6408dee56149fcac
def a258 : W := 0x2000c0043496d08
def a259 : W := 0x6cacd3f72ca492f7
def a260 : W := 0x24085a342d085abc
def a261 : W := 0xffacdfffffedffff
def a262 : W := 0x4aa485c342e5a543
def a263 : W := 0x9100000890000000
def a264 : W := 0x7deb436cfddbef5e
def a265 : W := 0x514b020cf01b8e1e
def a266 : W := 0xaeb441729ff66353
def a267 : W := 0x8214001292360213
def a268 : W := 0xbfe16d68dfc96d48
def a269 : W := 0x93412c08d2090c08
def a270 : W := 0x240040200d004000
def a271 : W := 0xbda85b7cbdc87bfc
def a272 : W := 0x8a0014000c02140
def a273 : W := 0x91081a1cb0081abc
def a274 : W := 0x734f1e5ef1db8e5e
def a275 : W := 0x31430048b1d28044
def a276 : W := 0xcabc1f16debf0f5b
def a277 : W := 0x88b001009eb60141
def a278 : W := 0xd34d3e1ed3496f1a
def a279 : W := 0x9141200893406100
def a280 : W := 0x81a1400080a18
def a281 : W := 0xf70c5e3efd095ebe
def a282 : W := 0x4204040240010402
def a283 : W := 0xb5004028bd0050a4
def a284 : W := 0x660cdeb76f2ddebf
def a285 : W := 0x420c9e97422d8e1b
def a286 : W := 0x514b024cd0db8e5a
def a287 : W := 0xaeb44132bfb653f7
def a288 : W := 0x8ab4011292b60353
def a289 : W := 0xb7416c28ff497dac
def a290 : W := 0x93412c08d2492d08
def a291 : W := 0x734f9edff3ff9eff
def a292 : W := 0x2049c93022410a1
def a293 : W := 0xfbff035effff8f5f
def a294 : W := 0x8ab401120e240101
def a295 : W := 0x91081a1c90080a18
def a296 : W := 0x81a1420081abc
def a297 : W := 0xf70cdebfff2ddebf
def a298 : W := 0x4204848342258403
def a299 : W := 0xb50040289d004000
def a300 : W := 0x3108020cb1080a1c
def a301 : W := 0x800000109c000210
def a302 : W := 0xbfbc5b3ebfbe5bff
def a303 : W := 0xab4010202b60143
def a304 : W := 0x35085a2c210858ac
def a305 : W := 0x9100080891084808
def a306 : W := 0x241240042412500
def a307 : W := 0x89a95222c9abd
def a308 : W := 0xbda041689dc06140
def a309 : W := 0x3108024cb1c88a5c
def a310 : W := 0x8ca0d9b10e2471a1
def a311 : W := 0x88a001109ea40351
def a312 : W := 0x3508daed2148f8ac
def a313 : W := 0x9100080893486908
def a314 : W := 0x2ca8d3f52ca492f5
def a315 : W := 0x4aac9fd762edbfff
def a316 : W := 0x420c1e1660091ebe
def a317 : W := 0x79eb83cdf3ffaf5f
def a318 : W := 0x714b020cf11b0e1e
def a319 : W := 0x8ab481d39ef6a353
def a320 : W := 0x821400129c120212
def a321 : W := 0x9be1adc9d3eded49
def a322 : W := 0x93412c08d1094c08
def a323 : W := 0xd30c9e9ff22d9ebf
def a324 : W := 0x42048483622594a7
def a325 : W := 0xf14b1a5cf1db8e5e
def a326 : W := 0x6043004061d38446
def a327 : W := 0x9bbc1b1e9ebe0b5b
def a328 : W := 0xab401020eb60143
def a329 : W := 0x93493e1cd3496f18
def a330 : W := 0x241240043416500
def a331 : W := 0x2ca0c1e1bff6f3f7
def a332 : W := 0x2ca0c1e12f64f1a5
def a333 : W := 0x212
def a334 : W := 0x420c9e97f2bf9eff
def a335 : W := 0x90920040
def a336 : W := 0x420c9e97622d9cad
def a337 : W := 0x90000000
def a338 : W := 0x93412c08d3db6f5a
def a339 : W := 0x920252
def a340 : W := 0x93412c0843496d08
def a341 : W := 0x90000210
def a342 : W := 0xb5085a3cbd9a5afe
def a343 : W := 0x920042
def a344 : W := 0xb5085a3c2d0858ac
def a345 : W := 0x28a001402fe48145
def a346 : W := 0xd35f021ed01b0e1a
def a347 : W := 0x420c0216622d8e1f
def a348 : W := 0xfbff9fdfffff9fff
def a349 : W := 0x9c81000010a0
def a350 : W := 0xb9f301489dd20140
def a351 : W := 0x93410008d3490d08
def a352 : W := 0xfbff2f5effffef5f
def a353 : W := 0x2c0000006000
def a354 : W := 0x68be03562cb68257
def a355 : W := 0xb108021cbd080a1c
def a356 : W := 0xffff5b7effffdfff
def a357 : W := 0x4005820000050a0
def a358 : W := 0x4af7014242f78543
def a359 : W := 0x7debc3ed6fedfded
def a360 : W := 0xca0c1a10ea471e1
def a361 : W := 0x4008020460098c0c
def a362 : W := 0x734f9edf636d9ebf
def a363 : W := 0x2049c93022412b3
def a364 : W := 0x3143004801400000
def a365 : W := 0x1141000841490c08
def a366 : W := 0xf34b2e4cf349ed0c
def a367 : W := 0x600a024420008004
def a368 : W := 0x82002c0092006100
def a369 : W := 0x3108020c2108080c
def a370 : W := 0xf54b5a7cfd49debc
def a371 : W := 0x4043004040418400
def a372 : W := 0x840058309c0052b0
def a373 : W := 0xaeb4c1f32fe4f1e5
def a374 : W := 0x2400c0e121c0f0e4
def a375 : W := 0x204001202240001
def a376 : W := 0xcabc9f976e2d9fbf
def a377 : W := 0x40089e8560099ebe
def a378 : W := 0x88b001000c000100
def a379 : W := 0x8200000002000100
def a380 : W := 0x9bf52d1adf6d6d09
def a381 : W := 0x8b401120c240001
def a382 : W := 0x11412c08d1496c08
def a383 : W := 0x800000100c000000
def a384 : W := 0xbfbc5b3ebf2c5bbd
def a385 : W := 0xab4010202240101
def a386 : W := 0x35085a2cb1085abc
def a387 : W := 0x3de1c1e9ffedfded
def a388 : W := 0x2ca0c1e12ea4f1e5
def a389 : W := 0x534d9e9ff36d9ebf
def a390 : W := 0x1141000891400000
def a391 : W := 0x420c9e97222492b7
def a392 : W := 0x9bf5011adfff0f5b
def a393 : W := 0x8ab401120eb60353
def a394 : W := 0x1100000891080808
def a395 : W := 0xb5495a3cfd495ebc
def a396 : W := 0x41000040410400
def a397 : W := 0xa4085a342c0052b4
def a398 : W := 0x2000004023c0e144
def a399 : W := 0xd34b2e0cd01b0e1a
def a400 : W := 0x42080e0462098e1e
def a401 : W := 0xf34fbedff3ffffff
def a402 : W := 0x49093002410a1
def a403 : W := 0xb143204891d26140
def a404 : W := 0x8200000092920352
def a405 : W := 0x714b2e4c6149ec0c
def a406 : W := 0xb1080a0cb1084a1c
def a407 : W := 0xf74b7e7cffdbfffe
def a408 : W := 0x40050300c0010a0
def a409 : W := 0x4243244042d3a542
def a410 : W := 0x6caac3e52ff6f3f7
def a411 : W := 0xca0c1a10f6471a1
def a412 : W := 0x4008020420008216
def a413 : W := 0x620e9ed762bf9eff
def a414 : W := 0x2049c93422d1ca9
def a415 : W := 0x2002004000920040
def a416 : W := 0xeabe0356beb68357
def a417 : W := 0x8ab401129e240101
def a418 : W := 0x2008020420000214
def a419 : W := 0xf50a5a7cbd9adafe
def a420 : W := 0x4002004000928042
def a421 : W := 0x950058389d0858a8
def a422 : W := 0xaea0ede12fe4f1e5
def a423 : W := 0x2ca0c1e12de490e5
def a424 : W := 0x2000c0002000000
def a425 : W := 0xc20cbe97622dffbf
def a426 : W := 0x400c9297602d9ebf
def a427 : W := 0x8000200000006100
def a428 : W := 0x8ab42d129eb66353
def a429 : W := 0x8b401129cb60253
def a430 : W := 0x8000080000004000
def a431 : W := 0xb7087e3cbf087bbc
def a432 : W := 0x200240002002100
def a433 : W := 0x3508523cbd081abc
def a434 : W := 0x6ca8c3e56fedffff
def a435 : W := 0x2ca0c1e10fe471e1
def a436 : W := 0xcabc0316febf8f5f
def a437 : W := 0x8ab401129eb60141
def a438 : W := 0xd3492e0cf349ef1e
def a439 : W := 0x93412c0893406100
def a440 : W := 0x8020420080a1c
def a441 : W := 0xf5085a3cfd09debe
def a442 : W := 0x4000000040018402
def a443 : W := 0xb50058389d0050a0
def a444 : W := 0x200080c123e490e5
def a445 : W := 0x534f1e1ed01b0e1a
def a446 : W := 0x204001292b60253
def a447 : W := 0x714b9ecd61499cac
def a448 : W := 0x13410c08d3490c08
def a449 : W := 0x600e92d720b692f7
def a450 : W := 0x31081a1cb1081abc
def a451 : W := 0xf74fdeffffffdeff
def a452 : W := 0x424784c342f78443
def a453 : W := 0x840040200c004000
def a454 : W := 0x3de3c1e9bff6f1e5
def a455 : W := 0xca0c1a12e24f1a5
def a456 : W := 0xbbf7015a9ff60353
def a457 : W := 0x8ab401120e240313
def a458 : W := 0xb3432c48d3db6d48
def a459 : W := 0x82002c0042096d08
def a460 : W := 0x3100000891000000
def a461 : W := 0xb54b5a7cbdda5afc
def a462 : W := 0x43004000d20040
def a463 : W := 0x84085a342c085abc
def a464 : W := 0x2ea4ddf32fe4f1e5
def a465 : W := 0x2ca041602dc0e144
def a466 : W := 0x8ab49d939eb613f3
def a467 : W := 0x88b001009c920352
def a468 : W := 0x9345bc9bd36d7da9
def a469 : W := 0x91412008d1496d08
def a470 : W := 0x1810000010a0
def a471 : W := 0xb70cdebfbf2c5abd
def a472 : W := 0x204848302240001
def a473 : W := 0xb508422cbd084a1c
def a474 : W := 0x3da8c3edbfecfbfd
def a475 : W := 0xca0c1e10ee4f1e1
def a476 : W := 0x730c9e9ff32d9ebf
def a477 : W := 0x42049c93422594a3
def a478 : W := 0xbbbc031ebfbe0b5f
def a479 : W := 0x8ab401120eb60143
def a480 : W := 0xb3492e0cf3496f1c
def a481 : W := 0x82412c0042416500
def a482 : W := 0xd14b1a1cd01b0e1a
def a483 : W := 0x40081a1460099ebe
def a484 : W := 0xb54340689dd24040
def a485 : W := 0x800000109c920252
def a486 : W := 0x754b5a6c6149dcac
def a487 : W := 0x91410808d1494c08
def a488 : W := 0x640a52742c9292f6
def a489 : W := 0x6ce3c1e16ff7f5e7
def a490 : W := 0x2ca0c1a12f2471a5
def a491 : W := 0x424f9ed762ff9eff
def a492 : W := 0x20c9e97222c1abd
def a493 : W := 0xcaf70152def78753
def a494 : W := 0x8ab401129e240311
def a495 : W := 0xd3432c48d3dbed4a
def a496 : W := 0x93002c0893086908
def a497 : W := 0xaca0d9f12fe4f1e5
def a498 : W := 0x28a081c123e4a145
def a499 : W := 0xc60cdeb76e2ddebf
def a500 : W := 0x420c8687622d8e1f
def a501 : W := 0x8eb459329eb653f3
def a502 : W := 0xab4010292b60353
def a503 : W := 0x97417c38df497da8
def a504 : W := 0x13412408d3492d08
def a505 : W := 0xaea0c1e1bfe4f1e5
def a506 : W := 0x2ca0c1e12de4f0e5
def a507 : W := 0x200000002000000
def a508 : W := 0xc20c9e97f22d9fbf
def a509 : W := 0x400c9e97602d9ebf
def a510 : W := 0x8000000090000100
def a511 : W := 0xf34b024cf3db8f5e
def a512 : W := 0x714b024c61db8e5e
def a513 : W := 0x8000000090000000
def a514 : W := 0xb7085a3cbf085bbc
def a515 : W := 0x200000002000100
def a516 : W := 0x35085a3c2d085abc
def a517 : W := 0x8a001000fe46141
def a518 : W := 0x93552c1ad01b0e1a
def a519 : W := 0x2040c12422d0e1b
def a520 : W := 0xdbfdbf9fffffffff
def a521 : W := 0x40089285200090a4
def a522 : W := 0x99f121089dd26140
def a523 : W := 0x11410008d1db0e5a
def a524 : W := 0x8ab42d120e246101
def a525 : W := 0x910008189d084a18
def a526 : W := 0xbffd7f3effff7fff
def a527 : W := 0xaf5250242f72543
def a528 : W := 0x24085224200010a4
def a529 : W := 0x2cb4c1f32ff6f3f7
def a530 : W := 0x2400c0e12340f1a4
def a531 : W := 0x4001200240213
def a532 : W := 0x4abc9f976ebf9eff
def a533 : W := 0x8b001000c920040
def a534 : W := 0x42089e8562099cac
def a535 : W := 0x79ff035efdff8e5f
def a536 : W := 0x714b024cf1498c0c
def a537 : W := 0x100c000210
def a538 : W := 0xbdbc5b3ebdbe5aff
def a539 : W := 0x8b4010200b60043
def a540 : W := 0xb5085a2cb10858ac
def a541 : W := 0x3de1ede96fedfded
def a542 : W := 0x2ca0c1e12ea491e5
def a543 : W := 0x534dbe9f636dfebf
def a544 : W := 0x1141200801406000
def a545 : W := 0x420c9297222492b7
def a546 : W := 0x714b2e4cf1dbee5e
def a547 : W := 0x600a0244b0928256
def a548 : W := 0x1100080801084808
def a549 : W := 0xb5497e3cfd497ebc
def a550 : W := 0x41240040412400
def a551 : W := 0xa4085234bc0012b4
def a552 : W := 0x2ea4c1f32fe4f3f7
def a553 : W := 0x2ca0c1e12dc0f1e4
def a554 : W := 0x734f025ef3ff8e5f
def a555 : W := 0x714b024cf1db8c4c
def a556 : W := 0x93452c1ad36d6f1b
def a557 : W := 0x91412c08d1496d08
def a558 : W := 0x1000000210
def a559 : W := 0xb70c5a3ebf2c5abf
def a560 : W := 0x204000202240003
def a561 : W := 0xb5085a2cbd0858ac
def a562 : W := 0x8a081812ea491e5
def a563 : W := 0xc21c1e16d01b0e1a
def a564 : W := 0x40080204f09b8e5e
def a565 : W := 0x8ab49d930e2411a1
def a566 : W := 0x82000c00d2090d08
def a567 : W := 0x48bc93972cb692f7
def a568 : W := 0x80081a14bc081abc
def a569 : W := 0xffbcdfbfffbfdfff
def a570 : W := 0x3500402801004000
def a571 : W := 0x4ab4858342b78543
def a572 : W := 0xacb0c1e1bff6f1e5
def a573 : W := 0x2400c0e12364f0a5
def a574 : W := 0xf9fb034cfddb8f5e
def a575 : W := 0x714b024c61498e1e
def a576 : W := 0x9bf12d08dfdb6d48
def a577 : W := 0x13412c0843496c08
def a578 : W := 0x800000009c000000
def a579 : W := 0xbdb85b3cbd9a5bfc
def a580 : W := 0x8b0010000920140
def a581 : W := 0x35085a3c21085abc
def a582 : W := 0x6ca8dfe56fedfded
def a583 : W := 0x2ca041600fe46141
def a584 : W := 0x714b9ecdf1db9efe
def a585 : W := 0x3143004891d20252
def a586 : W := 0xd349be8df349fdac
def a587 : W := 0x9341200893406100
def a588 : W := 0x81a04200818ac
def a589 : W := 0xf508debdfd09debc
def a590 : W := 0x4000848140018400
def a591 : W := 0xb50040389d004210
def a592 : W := 0xaca0c1f1bfe4f3f5
def a593 : W := 0x2ca0c1e123e4f1e5
def a594 : W := 0xc20c9e97fe2d9ebf
def a595 : W := 0x420c9e87622d9caf
def a596 : W := 0xf14b025cfddb8e5e
def a597 : W := 0x714b024c61db8c4e
def a598 : W := 0x93412c18df496f18
def a599 : W := 0x13412c0843496d08
def a600 : W := 0x2ca041202fa451e5
def a601 : W := 0x931c1a1e901a0a1a
def a602 : W := 0x20c1a16222c1abf
def a603 : W := 0xbdb041289d924140
def a604 : W := 0x3108020cb19a0a5e
def a605 : W := 0x8eb459320e2451a1
def a606 : W := 0x9300080893084908
def a607 : W := 0x2cbc53362cb612f7
def a608 : W := 0x2eb4c1e32ff6f1e7
def a609 : W := 0x2400c0e12d40f0a4
def a610 : W := 0x4abc9f9762bf9fff
def a611 : W := 0x40089e9560099ebc
def a612 : W := 0x7bff034ef3ff8f5f
def a613 : W := 0x714b024cf1498e1c
def a614 : W := 0x9bf52d0ad3ff6d4b
def a615 : W := 0x91412c08d1496c08
def a616 : W := 0x3da8dbed2fecf9ed
def a617 : W := 0x8a081c10ee4a141
def a618 : W := 0x770cdebf632ddebf
def a619 : W := 0x4204849342258613
def a620 : W := 0x754b5a6cf1dbdefe
def a621 : W := 0x40430040d0d38652
def a622 : W := 0xb7497e2cf3497dac
def a623 : W := 0x82412400d2412500
def a624 : W := 0x2ca0c1e12de4f1e5
def a625 : W := 0x734b0e4cf3db8e5e
def a626 : W := 0x80000080808
def a627 : W := 0x200040042010400
def a628 : W := 0x5149020cf1498e1e
def a629 : W := 0x8204bc93022471a1
def a630 : W := 0x8204001292240313
def a631 : W := 0x5149be8d6149fcac
def a632 : W := 0x91081a1cb1085abc
def a633 : W := 0xf74dfebfff6dffbf
def a634 : W := 0x240040200c000000
def a635 : W := 0x4245a4834265a503
def a636 : W := 0xbde1e1e9bfe4f1e5
def a637 : W := 0x2ca0c1e12ea490e5
def a638 : W := 0xf14b224cf1dbef5e
def a639 : W := 0x600a0244609b8e5e
def a640 : W := 0x9bf5211a9ff66353
def a641 : W := 0xab401120eb60253
def a642 : W := 0x9100000891004000
def a643 : W := 0xb5497a3cbd487bbc
def a644 : W := 0x41200000402100
def a645 : W := 0x24085a342c081abc
def a646 : W := 0x6cacd3f72fe4f3f7
def a647 : W := 0x2ca041600fc06140
def a648 : W := 0x714f92dff1ff9eff
def a649 : W := 0x31430048d1db0c48
def a650 : W := 0xcabc9397beb693f7
def a651 : W := 0x8ab001009e920140
def a652 : W := 0x81214200012b4
def a653 : W := 0xf50cdabfbd2cdabf
def a654 : W := 0x4004808300248003
def a655 : W := 0xb50048289d084808
def a656 : W := 0xbda0c9e9bfecf9ed
def a657 : W := 0x2ca0c1e12ee4b1e5
def a658 : W := 0xd30c9e9ff32ddebf
def a659 : W := 0x420c9697622596b7
def a660 : W := 0xf14b0a4cf1dbce5e
def a661 : W := 0x604b024460d38656
def a662 : W := 0x9bb4091a9fbe4b5b
def a663 : W := 0xab401120eb60353
def a664 : W := 0x240040202f4071a4
def a665 : W := 0x93493e1cd0090e18
def a666 : W := 0x2081e1462091ebc
def a667 : W := 0xb54160289d406100
def a668 : W := 0x3149020cf1490e1c
def a669 : W := 0x86007c300e0071a0
def a670 : W := 0x820000109e000310
def a671 : W := 0x35497e2c61497cac
def a672 : W := 0x2ee1e5e16fe5f5e5
def a673 : W := 0x2ca0c1e12da4d0e5
def a674 : W := 0x424dbe97626dbfbf
def a675 : W := 0x400c9a97202c9abf
def a676 : W := 0x734b264cf3dbaf5e
def a677 : W := 0x710a024cb19a8a5e
def a678 : W := 0x8af52512def72753
def a679 : W := 0x88b401129cb60253
def a680 : W := 0x2ca8d3f52fe4f3f5
def a681 : W := 0x8a081c103e4e141
def a682 : W := 0x660cdeb76e2d9ebf
def a683 : W := 0x42048c83422d8c0b
def a684 : W := 0x754b527cfddb9efe
def a685 : W := 0x51430048d1db8c4a
def a686 : W := 0xaebc5336beb613f7
def a687 : W := 0x8ab4010292b60143
def a688 : W := 0x2ca8dbf52fecfbfd
def a689 : W := 0x2ca0c1e10fe4e141
def a690 : W := 0x714b1a5cf1db9efe
def a691 : W := 0x71430048d1d38442
def a692 : W := 0x8abc1b16bebe1bff
def a693 : W := 0x8ab401029eb60143
def a694 : W := 0x93493e1cf3497fbc
def a695 : W := 0x93412408d3416500
def a696 : W := 0x2400c0a12f24d0a5
def a697 : W := 0xd30c1e1ed0090e1a
def a698 : W := 0x7108020cf1098e1e
def a699 : W := 0x8604dcb30e2450a1
def a700 : W := 0x820400129e240213
def a701 : W := 0x7508dead6109dcac
def a702 : W := 0x93000c08d3094c08
def a703 : W := 0x640cd2b72c2492b7
def a704 : W := 0x6ea4c5e36fe5f5e7
def a705 : W := 0x2ca041602dc071e4
def a706 : W := 0x734f86cff3ff8e5f
def a707 : W := 0x314b024cb1da0a5c
def a708 : W := 0xcab48593deb78753
def a709 : W := 0x88b001109c920350
def a710 : W := 0xd345ac8bd36ded0b
def a711 : W := 0x9141280891486908
def a712 : W := 0xbda0c1e9bfe4f1e5
def a713 : W := 0x8a081c122e4b1e5
def a714 : W := 0xf54b426cfddbce5e
def a715 : W := 0x404b024460db8e5e
def a716 : W := 0xbfb4413a9fb64353
def a717 : W := 0xab4011202b60353
def a718 : W := 0xb7416c28df496d08
def a719 : W := 0x2412c0042492d08
def w0 : List W := [a0, a1, a2, a3, a4, a5]
def w1 : List W := [a1, a2, a6, a3, a4, a5]
def w2 : List W := [a7, a1, a2, a3, a4, a5]
def w3 : List W := [a1, a8, a2, a3, a4, a5]
def w4 : List W := [a9, a1, a2, a3, a4, a5]
def w5 : List W := [a1, a2, a3, a10, a4, a5]
def w6 : List W := [a11, a1, a2, a3, a4, a5]
def w7 : List W := [a1, a2, a12, a3, a4, a5]
def w8 : List W := [a13, a1, a2, a3, a4, a5]
def w9 : List W := [a1, a2, a3, a4, a5, a14]
def w10 : List W := [a15, a1, a2, a3, a4, a5]
def w11 : List W := [a1, a2, a3, a16, a4, a5]
def w12 : List W := [a17, a1, a2, a3, a4, a5]
def w13 : List W := [a1, a2, a3, a4, a5, a18]
def w14 : List W := [a19, a1, a2, a3, a4, a5]
def w15 : List W := [a1, a2, a3, a4, a20, a5]
def w16 : List W := [a1, a21, a2, a3, a4, a5]
def w17 : List W := [a1, a2, a3, a22, a4, a5]
def w18 : List W := [a23, a1, a2, a3, a4, a5]
def w19 : List W := [a1, a24, a2, a3, a4, a5]
def w20 : List W := [a25, a1, a2, a3, a4, a5]
def w21 : List W := [a1, a2, a3, a4, a5, a26]
def w22 : List W := [a1, a27, a2, a3, a4, a5]
def w23 : List W := [a1, a2, a3, a28, a4, a5]
def w24 : List W := [a29, a1, a2, a3, a4, a5]
def w25 : List W := [a1, a2, a3, a4, a5, a30]
def w26 : List W := [a1, a31, a2, a3, a4, a5]
def w27 : List W := [a1, a2, a3, a4, a32, a5]
def w28 : List W := [a33, a1, a2, a3, a4, a5]
def w29 : List W := [a1, a2, a3, a4, a5, a34]
def w30 : List W := [a1, a2, a35, a3, a4, a5]
def w31 : List W := [a1, a2, a3, a36, a4, a5]
def w32 : List W := [a37, a1, a2, a3, a4, a5]
def w33 : List W := [a1, a2, a3, a4, a5, a38]
def w34 : List W := [a1, a2, a39, a3, a4, a5]
def w35 : List W := [a1, a2, a3, a40, a4, a5]
def w36 : List W := [a1, a2, a3, a41, a4, a5]
def w37 : List W := [a1, a2, a3, a4, a5, a42]
def w38 : List W := [a43, a1, a2, a3, a4, a5]
def w39 : List W := [a44, a1, a2, a3, a4, a5]
def w40 : List W := [a1, a45, a46, a4, a47, a30]
def w41 : List W := [a48, a1, a46, a4, a47, a30]
def w42 : List W := [a49, a1, a46, a4, a47, a30]
def w43 : List W := [a1, a50, a46, a4, a47, a30]
def w44 : List W := [a1, a46, a51, a47, a30]
def w45 : List W := [a29, a1, a46, a51, a47, a30]
def w46 : List W := [a1, a46, a4, a51, a47, a30]
def w47 : List W := [a52, a1, a46, a4, a47, a30]
def w48 : List W := [a29, a1, a46, a53, a47, a30]
def w49 : List W := [a29, a1, a46, a4, a54, a30]
def w50 : List W := [a29, a1, a46, a4, a55, a30]
def w51 : List W := [a29, a1, a46, a4, a47, a30]
def w52 : List W := [a1, a46, a4, a47, a56]
def w53 : List W := [a29, a1, a46, a4, a47, a56]
def w54 : List W := [a1, a46, a4, a47, a56, a30]
def w55 : List W := [a29, a57, a1, a46, a4, a30]
def w56 : List W := [a29, a58, a1, a46, a4, a30]
def w57 : List W := [a59, a29, a46, a4, a47]
def w58 : List W := [a59, a29, a1, a46, a4, a47]
def w59 : List W := [a59, a29, a46, a4, a47, a30]
def w60 : List W := [a29, a60, a1, a46, a4, a47]
def w61 : List W := [a29, a46, a4, a47, a61, a30]
def w62 : List W := [a29, a1, a46, a4, a30, a62]
def w63 : List W := [a29, a1, a46, a63, a4, a30]
def w64 : List W := [a64, a1, a2, a46, a4, a5, a47]
def w65 : List W := [a1, a2, a46, a4, a5, a47]
def w66 : List W := [a1, a1, a2, a46, a4, a5, a47]
def w67 : List W := [a65, a1, a2, a46, a4, a5, a47]
def w68 : List W := [a66, a64, a2, a46, a4, a5, a47]
def w69 : List W := [a66, a1, a2, a46, a4, a5, a47]
def w70 : List W := [a67, a1, a2, a46, a4, a5, a47]
def w71 : List W := [a1, a2, a68, a46, a4, a5, a47]
def w72 : List W := [a69, a1, a2, a46, a4, a5, a47]
def w73 : List W := [a1, a70, a2, a46, a4, a5, a47]
def w74 : List W := [a1, a2, a46, a46, a4, a5, a47]
def w75 : List W := [a64, a1, a2, a12, a4, a5, a47]
def w76 : List W := [a1, a2, a12, a46, a4, a5, a47]
def w77 : List W := [a71, a1, a2, a46, a4, a5, a47]
def w78 : List W := [a1, a2, a46, a4, a5, a72, a47]
def w79 : List W := [a73, a1, a2, a46, a4, a5, a47]
def w80 : List W := [a1, a2, a46, a74, a4, a5, a47]
def w81 : List W := [a75, a1, a2, a46, a4, a5, a47]
def w82 : List W := [a1, a2, a46, a4, a76, a47]
def w83 : List W := [a64, a1, a2, a46, a4, a76, a47]
def w84 : List W := [a1, a2, a46, a4, a5, a76, a47]
def w85 : List W := [a77, a1, a2, a46, a4, a5, a47]
def w86 : List W := [a1, a2, a46, a4, a78, a47]
def w87 : List W := [a64, a1, a2, a46, a4, a78, a47]
def w88 : List W := [a1, a2, a46, a4, a78, a5, a47]
def w89 : List W := [a79, a1, a2, a46, a4, a5, a47]
def w90 : List W := [a1, a2, a46, a4, a5, a80]
def w91 : List W := [a64, a1, a2, a46, a4, a5, a80]
def w92 : List W := [a1, a2, a46, a4, a5, a47, a80]
def w93 : List W := [a81, a1, a2, a46, a4, a5, a47]
def w94 : List W := [a1, a2, a46, a4, a5, a82]
def w95 : List W := [a64, a1, a2, a46, a4, a5, a82]
def w96 : List W := [a1, a2, a46, a4, a5, a82, a47]
def w97 : List W := [a64, a2, a10, a4, a5, a47]
def w98 : List W := [a64, a1, a2, a10, a4, a5, a47]
def w99 : List W := [a64, a2, a46, a10, a4, a5, a47]
def w100 : List W := [a64, a57, a1, a2, a46, a4, a5]
def w101 : List W := [a58, a64, a1, a2, a46, a4, a5]
def w102 : List W := [a64, a1, a2, a46, a4, a5, a62]
def w103 : List W := [a64, a1, a2, a46, a63, a4, a5]
def w104 : List W := [a64, a1, a2, a46, a4, a5, a83]
def w105 : List W := [a64, a84, a1, a2, a46, a4, a5]
def w106 : List W := [a66, a1, a2, a10, a4, a5, a47]
def w107 : List W := [a2, a12, a46, a10, a4, a5, a47]
def w108 : List W := [a1, a2, a46, a10, a4, a5, a47]
def w109 : List W := [a2, a46, a10, a4, a5, a14, a47]
def w110 : List W := [a15, a2, a46, a10, a4, a5, a47]
def w111 : List W := [a57, a1, a2, a46, a10, a4, a5]
def w112 : List W := [a58, a1, a2, a46, a10, a4, a5]
def w113 : List W := [a1, a85, a46, a4, a5, a47]
def w114 : List W := [a1, a85, a2, a46, a4, a5, a47]
def w115 : List W := [a1, a85, a46, a10, a4, a5, a47]
def w116 : List W := [a1, a2, a46, a86, a4, a5, a47]
def w117 : List W := [a87, a1, a2, a46, a4, a5, a47]
def w118 : List W := [a1, a88, a46, a4, a5, a47]
def w119 : List W := [a1, a88, a2, a46, a4, a5, a47]
def w120 : List W := [a1, a88, a46, a10, a4, a5, a47]
def w121 : List W := [a1, a2, a10, a4, a5, a47, a89]
def w122 : List W := [a1, a2, a90, a10, a4, a5, a47]
def w123 : List W := [a1, a2, a10, a4, a5, a62]
def w124 : List W := [a1, a2, a46, a10, a4, a5, a62]
def w125 : List W := [a1, a2, a10, a4, a5, a47, a62]
def w126 : List W := [a1, a91, a2, a10, a4, a5, a47]
def w127 : List W := [a1, a2, a46, a10, a63, a4, a5]
def w128 : List W := [a92, a1, a2, a46, a5, a47]
def w129 : List W := [a92, a1, a2, a46, a10, a5, a47]
def w130 : List W := [a92, a1, a2, a46, a4, a5, a47]
def w131 : List W := [a1, a2, a46, a4, a5, a47, a93]
def w132 : List W := [a1, a2, a46, a94, a5, a47]
def w133 : List W := [a1, a2, a46, a94, a10, a5, a47]
def w134 : List W := [a1, a2, a46, a94, a4, a5, a47]
def w135 : List W := [a1, a2, a46, a95, a4, a5, a47]
def w136 : List W := [a96, a1, a2, a46, a4, a47]
def w137 : List W := [a96, a1, a2, a46, a10, a4, a47]
def w138 : List W := [a96, a1, a2, a46, a4, a5, a47]
def w139 : List W := [a1, a2, a46, a4, a5, a47, a97]
def w140 : List W := [a1, a2, a98, a46, a4, a47]
def w141 : List W := [a1, a2, a98, a46, a10, a4, a47]
def w142 : List W := [a1, a2, a98, a46, a4, a5, a47]
def w143 : List W := [a1, a2, a46, a99, a4, a5, a47]
def w144 : List W := [a1, a100, a2, a46, a4, a5]
def w145 : List W := [a1, a100, a2, a46, a10, a4, a5]
def w146 : List W := [a1, a100, a2, a46, a4, a5, a47]
def w147 : List W := [a1, a2, a46, a4, a5, a47, a101]
def w148 : List W := [a1, a2, a102, a46, a4, a5]
def w149 : List W := [a1, a2, a102, a46, a10, a4, a5]
def w150 : List W := [a1, a2, a102, a46, a4, a5, a47]
def w151 : List W := [a1, a2, a46, a103, a4, a5, a47]
def w152 : List W := [a1, a2, a46, a10, a4, a5, a83]
def w153 : List W := [a84, a1, a2, a46, a10, a4, a5]
def w154 : List W := [a104, a1, a2, a46, a4, a5, a47]
def w155 : List W := [a1, a2, a105, a46, a4, a5, a47]
def w156 : List W := [a106, a1, a2, a46, a4, a5, a47]
def w157 : List W := [a1, a107, a2, a46, a4, a5, a47]
def w158 : List W := [a108, a1, a2, a46, a4, a5, a47]
def w159 : List W := [a1, a2, a46, a4, a109, a5, a47]
def w160 : List W := [a110, a1, a2, a46, a4, a5, a47]
def w161 : List W := [a1, a2, a46, a111, a4, a5, a47]
def w162 : List W := [a112, a1, a2, a46, a4, a5, a47]
def w163 : List W := [a1, a2, a46, a4, a5, a113, a47]
def w164 : List W := [a114, a1, a2, a46, a4, a5, a47]
def w165 : List W := [a1, a2, a46, a4, a115, a5, a47]
def w166 : List W := [a116, a1, a2, a46, a4, a5]
def w167 : List W := [a116, a66, a1, a2, a46, a4, a5]
def w168 : List W := [a116, a1, a2, a46, a4, a5, a47]
def w169 : List W := [a1, a2, a46, a4, a5, a47, a117]
def w170 : List W := [a11, a1, a2, a46, a4, a5]
def w171 : List W := [a11, a66, a1, a2, a46, a4, a5]
def w172 : List W := [a11, a1, a2, a46, a4, a5, a47]
def w173 : List W := [a1, a2, a46, a4, a5, a118, a47]
def w174 : List W := [a66, a2, a12, a4, a5, a47]
def w175 : List W := [a66, a1, a2, a12, a4, a5, a47]
def w176 : List W := [a66, a2, a12, a46, a4, a5, a47]
def w177 : List W := [a66, a2, a46, a4, a5, a14, a47]
def w178 : List W := [a66, a15, a2, a46, a4, a5, a47]
def w179 : List W := [a66, a57, a1, a2, a46, a4, a5]
def w180 : List W := [a58, a66, a1, a2, a46, a4, a5]
def w181 : List W := [a66, a1, a2, a46, a4, a5, a62]
def w182 : List W := [a66, a1, a2, a46, a63, a4, a5]
def w183 : List W := [a66, a1, a2, a46, a4, a5, a83]
def w184 : List W := [a66, a84, a1, a2, a46, a4, a5]
def w185 : List W := [a57, a1, a2, a12, a46, a4, a5]
def w186 : List W := [a58, a1, a2, a12, a46, a4, a5]
def w187 : List W := [a1, a119, a2, a46, a4, a5, a47]
def w188 : List W := [a1, a2, a120, a46, a4, a5, a47]
def w189 : List W := [a121, a1, a2, a46, a4, a5, a47]
def w190 : List W := [a122, a1, a2, a46, a4, a5, a47]
def w191 : List W := [a123, a1, a2, a46, a4, a5, a47]
def w192 : List W := [a1, a2, a46, a4, a5, a47, a124]
def w193 : List W := [a1, a2, a125, a46, a4, a5, a47]
def w194 : List W := [a1, a2, a46, a126, a4, a5, a47]
def w195 : List W := [a127, a1, a2, a46, a4, a5, a47]
def w196 : List W := [a1, a2, a46, a4, a5, a47, a128]
def w197 : List W := [a1, a129, a2, a46, a4, a5, a47]
def w198 : List W := [a1, a2, a46, a130, a4, a5, a47]
def w199 : List W := [a131, a1, a2, a46, a4, a5, a47]
def w200 : List W := [a1, a2, a46, a4, a5, a132]
def w201 : List W := [a1, a2, a12, a46, a4, a5, a132]
def w202 : List W := [a1, a2, a46, a4, a5, a47, a132]
def w203 : List W := [a1, a133, a2, a46, a4, a5, a47]
def w204 : List W := [a1, a2, a46, a4, a5, a134]
def w205 : List W := [a1, a2, a12, a46, a4, a5, a134]
def w206 : List W := [a1, a2, a46, a4, a5, a134, a47]
def w207 : List W := [a1, a2, a12, a4, a5, a47, a89]
def w208 : List W := [a1, a2, a12, a90, a4, a5, a47]
def w209 : List W := [a1, a2, a12, a4, a5, a62]
def w210 : List W := [a1, a2, a12, a46, a4, a5, a62]
def w211 : List W := [a1, a2, a12, a4, a5, a47, a62]
def w212 : List W := [a1, a91, a2, a12, a4, a5, a47]
def w213 : List W := [a1, a2, a12, a46, a63, a4, a5]
def w214 : List W := [a1, a2, a12, a46, a4, a5, a83]
def w215 : List W := [a84, a1, a2, a12, a46, a4, a5]
def w216 : List W := [a13, a1, a2, a46, a4, a5, a47]
def w217 : List W := [a13, a15, a2, a46, a4, a5, a47]
def w218 : List W := [a15, a1, a2, a46, a4, a5, a47]
def w219 : List W := [a135, a1, a2, a46, a4, a5, a47]
def w220 : List W := [a1, a2, a136, a46, a4, a5, a47]
def w221 : List W := [a137, a1, a2, a46, a4, a5, a47]
def w222 : List W := [a1, a138, a2, a46, a4, a5, a47]
def w223 : List W := [a1, a2, a46, a139, a4, a5, a47]
def w224 : List W := [a1, a2, a140, a46, a4, a5, a47]
def w225 : List W := [a1, a2, a46, a4, a4, a5, a47]
def w226 : List W := [a13, a1, a2, a46, a16, a5, a47]
def w227 : List W := [a1, a2, a46, a16, a4, a5, a47]
def w228 : List W := [a141, a1, a2, a46, a4, a5, a47]
def w229 : List W := [a1, a2, a46, a4, a5, a142, a47]
def w230 : List W := [a143, a1, a2, a46, a4, a5, a47]
def w231 : List W := [a1, a2, a46, a4, a144, a5, a47]
def w232 : List W := [a145, a1, a2, a46, a4, a5, a47]
def w233 : List W := [a1, a2, a46, a4, a5, a47, a146]
def w234 : List W := [a147, a1, a2, a46, a4, a5, a47]
def w235 : List W := [a1, a2, a46, a4, a5, a148, a47]
def w236 : List W := [a13, a2, a46, a5, a14, a47]
def w237 : List W := [a13, a1, a2, a46, a5, a14, a47]
def w238 : List W := [a13, a2, a46, a4, a5, a14, a47]
def w239 : List W := [a13, a57, a1, a2, a46, a4, a5]
def w240 : List W := [a13, a58, a1, a2, a46, a4, a5]
def w241 : List W := [a149, a13, a1, a2, a46, a5, a47]
def w242 : List W := [a13, a1, a2, a150, a46, a5, a47]
def w243 : List W := [a13, a1, a2, a46, a4, a5, a62]
def w244 : List W := [a13, a1, a2, a46, a63, a4, a5]
def w245 : List W := [a13, a1, a2, a46, a4, a5, a83]
def w246 : List W := [a13, a84, a1, a2, a46, a4, a5]
def w247 : List W := [a0, a2, a46, a4, a5, a14, a47]
def w248 : List W := [a8, a2, a46, a4, a5, a14, a47]
def w249 : List W := [a15, a1, a2, a46, a5, a14, a47]
def w250 : List W := [a2, a46, a16, a4, a5, a14, a47]
def w251 : List W := [a1, a2, a46, a4, a5, a14, a47]
def w252 : List W := [a57, a1, a2, a46, a4, a5, a14]
def w253 : List W := [a2, a46, a4, a5, a14, a47, a151]
def w254 : List W := [a58, a2, a46, a4, a5, a14]
def w255 : List W := [a58, a1, a2, a46, a4, a5, a14]
def w256 : List W := [a58, a2, a46, a4, a5, a14, a47]
def w257 : List W := [a152, a1, a2, a46, a4, a5, a47]
def w258 : List W := [a1, a2, a46, a4, a5, a47, a153]
def w259 : List W := [a1, a154, a2, a46, a4, a5, a47]
def w260 : List W := [a1, a2, a46, a4, a5, a155, a47]
def w261 : List W := [a156, a1, a2, a46, a4, a5, a47]
def w262 : List W := [a1, a2, a46, a4, a157, a5, a47]
def w263 : List W := [a1, a2, a46, a4, a5, a14, a62]
def w264 : List W := [a1, a2, a46, a63, a4, a5, a14]
def w265 : List W := [a1, a2, a46, a5, a42, a14, a47]
def w266 : List W := [a43, a1, a2, a46, a5, a14, a47]
def w267 : List W := [a1, a2, a46, a158, a4, a5, a47]
def w268 : List W := [a1, a2, a46, a4, a5, a47, a159]
def w269 : List W := [a160, a1, a2, a46, a4, a5, a47]
def w270 : List W := [a1, a161, a2, a46, a4, a5, a47]
def w271 : List W := [a1, a2, a46, a4, a5, a14, a83]
def w272 : List W := [a84, a1, a2, a46, a4, a5, a14]
def w273 : List W := [a1, a2, a46, a4, a5, a162]
def w274 : List W := [a1, a2, a46, a4, a5, a162, a14]
def w275 : List W := [a1, a2, a46, a4, a5, a162, a47]
def w276 : List W := [a1, a2, a46, a4, a5, a47, a163]
def w277 : List W := [a164, a1, a2, a46, a4, a5]
def w278 : List W := [a164, a1, a2, a46, a4, a5, a14]
def w279 : List W := [a164, a1, a2, a46, a4, a5, a47]
def w280 : List W := [a165, a1, a2, a46, a4, a5, a47]
def w281 : List W := [a166, a1, a2, a46, a4, a5, a47]
def w282 : List W := [a1, a2, a167, a46, a4, a5, a47]
def w283 : List W := [a168, a1, a2, a46, a4, a5, a47]
def w284 : List W := [a1, a169, a2, a46, a4, a5, a47]
def w285 : List W := [a1, a2, a46, a170, a4, a5, a47]
def w286 : List W := [a1, a2, a171, a46, a4, a5, a47]
def w287 : List W := [a172, a1, a2, a46, a4, a5, a47]
def w288 : List W := [a1, a2, a46, a4, a5, a47, a173]
def w289 : List W := [a174, a1, a2, a46, a4, a5, a47]
def w290 : List W := [a1, a2, a46, a4, a175, a5, a47]
def w291 : List W := [a176, a1, a2, a46, a4, a5, a47]
def w292 : List W := [a1, a2, a46, a4, a5, a47, a177]
def w293 : List W := [a178, a1, a2, a46, a4, a5, a47]
def w294 : List W := [a1, a2, a46, a4, a179, a5, a47]
def w295 : List W := [a0, a15, a2, a46, a4, a5, a47]
def w296 : List W := [a15, a8, a2, a46, a4, a5, a47]
def w297 : List W := [a15, a2, a46, a16, a5, a47]
def w298 : List W := [a15, a1, a2, a46, a16, a5, a47]
def w299 : List W := [a15, a2, a46, a16, a4, a5, a47]
def w300 : List W := [a57, a15, a1, a2, a46, a4, a5]
def w301 : List W := [a15, a2, a46, a4, a5, a47, a151]
def w302 : List W := [a58, a15, a2, a46, a4, a5]
def w303 : List W := [a58, a15, a1, a2, a46, a4, a5]
def w304 : List W := [a58, a15, a2, a46, a4, a5, a47]
def w305 : List W := [a149, a15, a1, a2, a46, a5, a47]
def w306 : List W := [a15, a1, a2, a150, a46, a5, a47]
def w307 : List W := [a15, a1, a2, a46, a4, a5, a62]
def w308 : List W := [a15, a1, a2, a46, a63, a4, a5]
def w309 : List W := [a15, a1, a2, a46, a4, a5, a83]
def w310 : List W := [a15, a84, a1, a2, a46, a4, a5]
def w311 : List W := [a57, a1, a2, a46, a16, a4, a5]
def w312 : List W := [a58, a1, a2, a46, a16, a4, a5]
def w313 : List W := [a180, a1, a2, a46, a4, a5, a47]
def w314 : List W := [a1, a46, a4, a5, a47, a181]
def w315 : List W := [a1, a2, a46, a4, a5, a47, a181]
def w316 : List W := [a1, a46, a16, a4, a5, a47, a181]
def w317 : List W := [a1, a182, a46, a4, a5, a47]
def w318 : List W := [a1, a182, a2, a46, a4, a5, a47]
def w319 : List W := [a1, a182, a46, a16, a4, a5, a47]
def w320 : List W := [a1, a2, a46, a183, a4, a5, a47]
def w321 : List W := [a1, a2, a46, a4, a5, a47, a184]
def w322 : List W := [a1, a2, a185, a46, a4, a5, a47]
def w323 : List W := [a1, a2, a46, a16, a4, a5, a62]
def w324 : List W := [a1, a2, a46, a16, a63, a4, a5]
def w325 : List W := [a1, a2, a46, a186, a4, a5, a47]
def w326 : List W := [a1, a2, a46, a4, a187, a47]
def w327 : List W := [a1, a2, a46, a16, a4, a187, a47]
def w328 : List W := [a1, a2, a46, a4, a5, a187, a47]
def w329 : List W := [a188, a1, a2, a46, a4, a5, a47]
def w330 : List W := [a189, a1, a2, a46, a4, a47]
def w331 : List W := [a189, a1, a2, a46, a16, a4, a47]
def w332 : List W := [a189, a1, a2, a46, a4, a5, a47]
def w333 : List W := [a1, a2, a46, a190, a4, a5, a47]
def w334 : List W := [a1, a2, a46, a4, a5, a191]
def w335 : List W := [a1, a2, a46, a16, a4, a5, a191]
def w336 : List W := [a1, a2, a46, a4, a5, a47, a191]
def w337 : List W := [a192, a1, a2, a46, a4, a5, a47]
def w338 : List W := [a1, a193, a2, a46, a4, a5]
def w339 : List W := [a1, a193, a2, a46, a16, a4, a5]
def w340 : List W := [a1, a193, a2, a46, a4, a5, a47]
def w341 : List W := [a1, a2, a46, a16, a5, a42, a47]
def w342 : List W := [a43, a1, a2, a46, a16, a5, a47]
def w343 : List W := [a1, a2, a46, a16, a4, a5, a83]
def w344 : List W := [a84, a1, a2, a46, a16, a4, a5]
def w345 : List W := [a17, a1, a2, a46, a4, a5, a47]
def w346 : List W := [a17, a19, a2, a46, a4, a5, a47]
def w347 : List W := [a19, a1, a2, a46, a4, a5, a47]
def w348 : List W := [a194, a1, a2, a46, a4, a5, a47]
def w349 : List W := [a1, a195, a46, a4, a5, a47]
def w350 : List W := [a17, a1, a195, a46, a4, a5, a47]
def w351 : List W := [a1, a2, a195, a46, a4, a5, a47]
def w352 : List W := [a196, a1, a2, a46, a4, a5, a47]
def w353 : List W := [a1, a197, a46, a4, a5, a47]
def w354 : List W := [a17, a1, a197, a46, a4, a5, a47]
def w355 : List W := [a1, a197, a2, a46, a4, a5, a47]
def w356 : List W := [a1, a2, a198, a4, a5, a47]
def w357 : List W := [a17, a1, a2, a198, a4, a5, a47]
def w358 : List W := [a1, a2, a46, a198, a4, a5, a47]
def w359 : List W := [a1, a2, a199, a4, a5, a47]
def w360 : List W := [a17, a1, a2, a199, a4, a5, a47]
def w361 : List W := [a1, a2, a199, a46, a4, a5, a47]
def w362 : List W := [a1, a2, a46, a200, a5, a47]
def w363 : List W := [a17, a1, a2, a46, a200, a5, a47]
def w364 : List W := [a1, a2, a46, a4, a200, a5, a47]
def w365 : List W := [a1, a2, a46, a201, a5, a47]
def w366 : List W := [a17, a1, a2, a46, a201, a5, a47]
def w367 : List W := [a1, a2, a46, a201, a4, a5, a47]
def w368 : List W := [a1, a2, a46, a4, a5, a5, a47]
def w369 : List W := [a17, a1, a2, a46, a4, a20, a47]
def w370 : List W := [a1, a2, a46, a4, a20, a5, a47]
def w371 : List W := [a202, a1, a2, a46, a4, a5, a47]
def w372 : List W := [a1, a2, a46, a4, a5, a203]
def w373 : List W := [a17, a1, a2, a46, a4, a5, a203]
def w374 : List W := [a1, a2, a46, a4, a5, a47, a203]
def w375 : List W := [a204, a1, a2, a46, a4, a5, a47]
def w376 : List W := [a1, a2, a46, a4, a5, a205]
def w377 : List W := [a17, a1, a2, a46, a4, a5, a205]
def w378 : List W := [a1, a2, a46, a4, a5, a205, a47]
def w379 : List W := [a17, a0, a2, a46, a4, a5, a47]
def w380 : List W := [a17, a8, a2, a46, a4, a5, a47]
def w381 : List W := [a17, a2, a46, a4, a47, a18]
def w382 : List W := [a17, a1, a2, a46, a4, a47, a18]
def w383 : List W := [a17, a2, a46, a4, a5, a47, a18]
def w384 : List W := [a17, a57, a1, a2, a46, a4, a5]
def w385 : List W := [a17, a58, a1, a2, a46, a4, a5]
def w386 : List W := [a17, a29, a1, a2, a46, a4, a47]
def w387 : List W := [a17, a1, a31, a2, a46, a4, a47]
def w388 : List W := [a17, a206, a1, a2, a46, a4, a47]
def w389 : List W := [a17, a1, a2, a90, a46, a4, a47]
def w390 : List W := [a17, a1, a2, a46, a4, a5, a62]
def w391 : List W := [a17, a1, a2, a46, a63, a4, a5]
def w392 : List W := [a17, a1, a2, a46, a4, a42, a47]
def w393 : List W := [a17, a44, a1, a2, a46, a4, a47]
def w394 : List W := [a17, a1, a2, a46, a4, a5, a83]
def w395 : List W := [a17, a84, a1, a2, a46, a4, a5]
def w396 : List W := [a19, a1, a2, a46, a4, a47, a18]
def w397 : List W := [a2, a46, a4, a20, a5, a47, a18]
def w398 : List W := [a57, a1, a2, a46, a4, a5, a18]
def w399 : List W := [a58, a1, a2, a46, a4, a5, a18]
def w400 : List W := [a1, a2, a46, a4, a5, a47, a18]
def w401 : List W := [a1, a2, a46, a4, a47, a18, a30]
def w402 : List W := [a1, a2, a46, a4, a32, a47, a18]
def w403 : List W := [a207, a1, a46, a4, a5, a47]
def w404 : List W := [a207, a1, a2, a46, a4, a5, a47]
def w405 : List W := [a207, a1, a46, a4, a5, a47, a18]
def w406 : List W := [a1, a2, a46, a4, a5, a47, a208]
def w407 : List W := [a1, a209, a2, a46, a4, a5, a47]
def w408 : List W := [a1, a46, a4, a5, a47, a210]
def w409 : List W := [a1, a2, a46, a4, a5, a47, a210]
def w410 : List W := [a1, a46, a4, a5, a47, a210, a18]
def w411 : List W := [a1, a2, a46, a4, a47, a18, a89]
def w412 : List W := [a1, a2, a46, a211, a4, a47, a18]
def w413 : List W := [a1, a2, a46, a4, a5, a18, a62]
def w414 : List W := [a1, a2, a46, a63, a4, a5, a18]
def w415 : List W := [a1, a212, a2, a46, a4, a5, a47]
def w416 : List W := [a1, a2, a46, a4, a213, a5, a47]
def w417 : List W := [a1, a2, a46, a214, a4, a5, a47]
def w418 : List W := [a1, a215, a2, a46, a4, a5, a47]
def w419 : List W := [a1, a2, a46, a4, a5, a83, a18]
def w420 : List W := [a84, a1, a2, a46, a4, a5, a18]
def w421 : List W := [a1, a2, a46, a4, a5, a216]
def w422 : List W := [a1, a2, a46, a4, a5, a216, a47]
def w423 : List W := [a1, a2, a46, a4, a5, a216, a18]
def w424 : List W := [a1, a2, a46, a4, a5, a47, a217]
def w425 : List W := [a218, a1, a2, a46, a4, a5, a47]
def w426 : List W := [a219, a1, a2, a46, a4, a5]
def w427 : List W := [a219, a1, a2, a46, a4, a5, a47]
def w428 : List W := [a219, a1, a2, a46, a4, a5, a18]
def w429 : List W := [a220, a1, a2, a46, a4, a5, a47]
def w430 : List W := [a1, a2, a221, a46, a4, a5, a47]
def w431 : List W := [a60, a1, a2, a46, a4, a5, a47]
def w432 : List W := [a1, a222, a2, a46, a4, a5, a47]
def w433 : List W := [a1, a2, a46, a223, a4, a5, a47]
def w434 : List W := [a1, a2, a224, a46, a4, a5, a47]
def w435 : List W := [a1, a2, a46, a4, a5, a225, a47]
def w436 : List W := [a1, a2, a46, a226, a4, a5, a47]
def w437 : List W := [a227, a1, a2, a46, a4, a5]
def w438 : List W := [a227, a19, a1, a2, a46, a4, a5]
def w439 : List W := [a227, a1, a2, a46, a4, a5, a47]
def w440 : List W := [a1, a2, a46, a4, a5, a47, a228]
def w441 : List W := [a229, a1, a2, a46, a4, a5]
def w442 : List W := [a229, a19, a1, a2, a46, a4, a5]
def w443 : List W := [a229, a1, a2, a46, a4, a5, a47]
def w444 : List W := [a1, a2, a46, a4, a230, a5, a47]
def w445 : List W := [a19, a2, a46, a4, a20, a47]
def w446 : List W := [a19, a1, a2, a46, a4, a20, a47]
def w447 : List W := [a19, a2, a46, a4, a20, a5, a47]
def w448 : List W := [a57, a19, a1, a2, a46, a4, a5]
def w449 : List W := [a58, a19, a1, a2, a46, a4, a5]
def w450 : List W := [a29, a19, a1, a2, a46, a4, a47]
def w451 : List W := [a19, a1, a31, a2, a46, a4, a47]
def w452 : List W := [a206, a19, a1, a2, a46, a4, a47]
def w453 : List W := [a19, a1, a2, a90, a46, a4, a47]
def w454 : List W := [a19, a1, a2, a46, a4, a5, a62]
def w455 : List W := [a19, a1, a2, a46, a63, a4, a5]
def w456 : List W := [a19, a1, a2, a46, a4, a42, a47]
def w457 : List W := [a44, a19, a1, a2, a46, a4, a47]
def w458 : List W := [a19, a1, a2, a46, a4, a5, a83]
def w459 : List W := [a84, a19, a1, a2, a46, a4, a5]
def w460 : List W := [a0, a2, a46, a4, a20, a5, a47]
def w461 : List W := [a8, a2, a46, a4, a20, a5, a47]
def w462 : List W := [a57, a1, a2, a46, a4, a20, a5]
def w463 : List W := [a58, a1, a2, a46, a4, a20, a5]
def w464 : List W := [a48, a1, a2, a46, a4, a5, a47]
def w465 : List W := [a1, a2, a46, a4, a5, a47, a231]
def w466 : List W := [a1, a232, a2, a46, a4, a5, a47]
def w467 : List W := [a1, a2, a46, a4, a233, a5, a47]
def w468 : List W := [a1, a2, a46, a4, a20, a47, a30]
def w469 : List W := [a1, a2, a46, a4, a32, a20, a47]
def w470 : List W := [a1, a2, a46, a4, a5, a47, a234]
def w471 : List W := [a1, a2, a235, a46, a4, a5, a47]
def w472 : List W := [a1, a2, a46, a4, a20, a47, a89]
def w473 : List W := [a1, a2, a46, a211, a4, a20, a47]
def w474 : List W := [a1, a2, a46, a4, a20, a5, a62]
def w475 : List W := [a1, a2, a46, a63, a4, a20, a5]
def w476 : List W := [a1, a2, a46, a4, a5, a236, a47]
def w477 : List W := [a237, a1, a2, a46, a4, a5, a47]
def w478 : List W := [a1, a2, a46, a4, a238, a5, a47]
def w479 : List W := [a1, a2, a46, a4, a5, a239]
def w480 : List W := [a1, a2, a46, a4, a20, a5, a239]
def w481 : List W := [a1, a2, a46, a4, a5, a47, a239]
def w482 : List W := [a240, a1, a2, a46, a4, a5, a47]
def w483 : List W := [a241, a1, a2, a46, a4, a5]
def w484 : List W := [a241, a1, a2, a46, a4, a20, a5]
def w485 : List W := [a241, a1, a2, a46, a4, a5, a47]
def w486 : List W := [a1, a2, a46, a4, a20, a5, a83]
def w487 : List W := [a84, a1, a2, a46, a4, a20, a5]
def w488 : List W := [a0, a1, a2, a46, a4, a5, a47]
def w489 : List W := [a0, a7, a2, a46, a4, a5, a47]
def w490 : List W := [a7, a1, a2, a46, a4, a5, a47]
def w491 : List W := [a1, a2, a2, a46, a4, a5, a47]
def w492 : List W := [a0, a1, a8, a46, a4, a5, a47]
def w493 : List W := [a1, a8, a2, a46, a4, a5, a47]
def w494 : List W := [a1, a2, a46, a242, a4, a5, a47]
def w495 : List W := [a1, a2, a243, a46, a4, a5, a47]
def w496 : List W := [a1, a2, a46, a4, a244, a5, a47]
def w497 : List W := [a1, a2, a46, a245, a4, a5, a47]
def w498 : List W := [a1, a2, a46, a4, a246, a47]
def w499 : List W := [a0, a1, a2, a46, a4, a246, a47]
def w500 : List W := [a1, a2, a46, a4, a5, a246, a47]
def w501 : List W := [a1, a2, a46, a4, a247, a47]
def w502 : List W := [a0, a1, a2, a46, a4, a247, a47]
def w503 : List W := [a1, a2, a46, a4, a247, a5, a47]
def w504 : List W := [a248, a1, a2, a46, a4, a5, a47]
def w505 : List W := [a1, a2, a46, a4, a5, a47, a249]
def w506 : List W := [a250, a1, a2, a46, a4, a5, a47]
def w507 : List W := [a1, a2, a46, a4, a5, a251, a47]
def w508 : List W := [a0, a6, a46, a4, a5, a47]
def w509 : List W := [a0, a1, a6, a46, a4, a5, a47]
def w510 : List W := [a0, a2, a6, a46, a4, a5, a47]
def w511 : List W := [a0, a57, a1, a2, a46, a4, a5]
def w512 : List W := [a0, a58, a1, a2, a46, a4, a5]
def w513 : List W := [a0, a1, a252, a46, a4, a5, a47]
def w514 : List W := [a0, a1, a253, a46, a4, a5, a47]
def w515 : List W := [a0, a1, a46, a4, a5, a47, a26]
def w516 : List W := [a0, a1, a27, a46, a4, a5, a47]
def w517 : List W := [a0, a29, a1, a46, a4, a5, a47]
def w518 : List W := [a0, a1, a46, a4, a32, a5, a47]
def w519 : List W := [a0, a1, a2, a46, a4, a5, a62]
def w520 : List W := [a0, a1, a2, a46, a63, a4, a5]
def w521 : List W := [a0, a1, a2, a46, a4, a5, a83]
def w522 : List W := [a0, a84, a1, a2, a46, a4, a5]
def w523 : List W := [a7, a1, a6, a46, a4, a5, a47]
def w524 : List W := [a8, a2, a6, a46, a4, a5, a47]
def w525 : List W := [a1, a2, a6, a46, a4, a5, a47]
def w526 : List W := [a57, a1, a2, a6, a46, a4, a5]
def w527 : List W := [a58, a1, a2, a6, a46, a4, a5]
def w528 : List W := [a1, a6, a46, a4, a5, a47, a30]
def w529 : List W := [a1, a31, a6, a46, a4, a5, a47]
def w530 : List W := [a1, a2, a254, a46, a4, a5, a47]
def w531 : List W := [a255, a1, a2, a46, a4, a5, a47]
def w532 : List W := [a256, a1, a2, a46, a4, a5, a47]
def w533 : List W := [a1, a2, a257, a46, a4, a5, a47]
def w534 : List W := [a258, a1, a2, a46, a4, a47]
def w535 : List W := [a258, a1, a2, a6, a46, a4, a47]
def w536 : List W := [a258, a1, a2, a46, a4, a5, a47]
def w537 : List W := [a1, a2, a259, a46, a4, a47]
def w538 : List W := [a1, a2, a259, a6, a46, a4, a47]
def w539 : List W := [a1, a2, a259, a46, a4, a5, a47]
def w540 : List W := [a260, a1, a2, a46, a4, a5]
def w541 : List W := [a260, a1, a2, a6, a46, a4, a5]
def w542 : List W := [a260, a1, a2, a46, a4, a5, a47]
def w543 : List W := [a1, a2, a46, a4, a5, a47, a261]
def w544 : List W := [a1, a2, a262, a46, a4, a5]
def w545 : List W := [a1, a2, a262, a6, a46, a4, a5]
def w546 : List W := [a1, a2, a262, a46, a4, a5, a47]
def w547 : List W := [a1, a2, a46, a4, a263, a5, a47]
def w548 : List W := [a1, a2, a6, a46, a4, a5, a62]
def w549 : List W := [a1, a2, a6, a46, a63, a4, a5]
def w550 : List W := [a1, a2, a6, a46, a4, a5, a83]
def w551 : List W := [a84, a1, a2, a6, a46, a4, a5]
def w552 : List W := [a1, a2, a46, a264, a4, a5, a47]
def w553 : List W := [a1, a2, a265, a46, a4, a5, a47]
def w554 : List W := [a1, a2, a46, a4, a5, a266, a47]
def w555 : List W := [a1, a2, a46, a267, a4, a5, a47]
def w556 : List W := [a1, a2, a46, a4, a5, a47, a268]
def w557 : List W := [a1, a2, a46, a4, a269, a5, a47]
def w558 : List W := [a270, a1, a2, a46, a4, a5, a47]
def w559 : List W := [a1, a2, a46, a4, a5, a47, a271]
def w560 : List W := [a272, a1, a2, a46, a4, a5, a47]
def w561 : List W := [a1, a2, a46, a4, a273, a5, a47]
def w562 : List W := [a7, a8, a46, a4, a5, a47]
def w563 : List W := [a7, a1, a8, a46, a4, a5, a47]
def w564 : List W := [a7, a8, a2, a46, a4, a5, a47]
def w565 : List W := [a57, a7, a1, a2, a46, a4, a5]
def w566 : List W := [a58, a7, a1, a2, a46, a4, a5]
def w567 : List W := [a7, a1, a252, a46, a4, a5, a47]
def w568 : List W := [a7, a1, a253, a46, a4, a5, a47]
def w569 : List W := [a7, a1, a46, a4, a5, a47, a26]
def w570 : List W := [a7, a1, a27, a46, a4, a5, a47]
def w571 : List W := [a29, a7, a1, a46, a4, a5, a47]
def w572 : List W := [a7, a1, a46, a4, a32, a5, a47]
def w573 : List W := [a7, a1, a2, a46, a4, a5, a62]
def w574 : List W := [a7, a1, a2, a46, a63, a4, a5]
def w575 : List W := [a7, a1, a2, a46, a4, a5, a83]
def w576 : List W := [a84, a7, a1, a2, a46, a4, a5]
def w577 : List W := [a57, a1, a8, a2, a46, a4, a5]
def w578 : List W := [a58, a1, a8, a2, a46, a4, a5]
def w579 : List W := [a1, a2, a46, a274, a4, a5, a47]
def w580 : List W := [a1, a275, a2, a46, a4, a5, a47]
def w581 : List W := [a1, a2, a46, a4, a5, a47, a276]
def w582 : List W := [a1, a2, a46, a277, a4, a5, a47]
def w583 : List W := [a1, a2, a46, a4, a5, a47, a278]
def w584 : List W := [a1, a2, a46, a4, a279, a5, a47]
def w585 : List W := [a280, a1, a2, a46, a4, a5, a47]
def w586 : List W := [a1, a2, a46, a4, a5, a281]
def w587 : List W := [a1, a8, a2, a46, a4, a5, a281]
def w588 : List W := [a1, a2, a46, a4, a5, a47, a281]
def w589 : List W := [a1, a282, a2, a46, a4, a5, a47]
def w590 : List W := [a1, a2, a46, a4, a5, a283]
def w591 : List W := [a1, a8, a2, a46, a4, a5, a283]
def w592 : List W := [a1, a2, a46, a4, a5, a283, a47]
def w593 : List W := [a1, a8, a46, a4, a5, a47, a30]
def w594 : List W := [a1, a31, a8, a46, a4, a5, a47]
def w595 : List W := [a1, a8, a2, a46, a4, a5, a62]
def w596 : List W := [a1, a8, a2, a46, a63, a4, a5]
def w597 : List W := [a1, a8, a2, a46, a4, a5, a83]
def w598 : List W := [a84, a1, a8, a2, a46, a4, a5]
def w599 : List W := [a57, a1, a2, a46, a4, a5]
def w600 : List W := [a57, a57, a1, a2, a46, a4, a5]
def w601 : List W := [a57, a1, a1, a2, a46, a4, a5]
def w602 : List W := [a65, a57, a1, a2, a46, a4, a5]
def w603 : List W := [a58, a57, a2, a46, a4, a5]
def w604 : List W := [a58, a1, a2, a46, a4, a5]
def w605 : List W := [a58, a57, a1, a2, a46, a4, a5]
def w606 : List W := [a248, a57, a1, a2, a46, a4, a5]
def w607 : List W := [a57, a1, a2, a284, a46, a4, a5]
def w608 : List W := [a270, a57, a1, a2, a46, a4, a5]
def w609 : List W := [a57, a1, a285, a2, a46, a4, a5]
def w610 : List W := [a79, a57, a1, a2, a46, a4, a5]
def w611 : List W := [a1, a2, a3, a4, a5]
def w612 : List W := [a57, a1, a2, a3, a4, a5]
def w613 : List W := [a1, a2, a46, a3, a4, a5]
def w614 : List W := [a57, a1, a2, a46, a3, a4, a5]
def w615 : List W := [a116, a57, a1, a2, a46, a4, a5]
def w616 : List W := [a57, a1, a2, a286, a4, a5]
def w617 : List W := [a57, a1, a2, a286, a46, a4, a5]
def w618 : List W := [a145, a57, a1, a2, a46, a4, a5]
def w619 : List W := [a57, a1, a2, a46, a4, a5, a287]
def w620 : List W := [a176, a57, a1, a2, a46, a4, a5]
def w621 : List W := [a57, a1, a2, a46, a288, a4, a5]
def w622 : List W := [a202, a57, a1, a2, a46, a4, a5]
def w623 : List W := [a1, a2, a46, a4, a5, a289]
def w624 : List W := [a57, a1, a2, a46, a4, a5, a289]
def w625 : List W := [a227, a57, a1, a2, a46, a4, a5]
def w626 : List W := [a57, a1, a2, a46, a4, a290, a5]
def w627 : List W := [a57, a1, a252, a2, a46, a4, a5]
def w628 : List W := [a57, a1, a2, a46, a291, a4, a5]
def w629 : List W := [a292, a57, a1, a2, a46, a4, a5]
def w630 : List W := [a57, a1, a253, a2, a46, a4, a5]
def w631 : List W := [a25, a57, a1, a2, a46, a4, a5]
def w632 : List W := [a57, a1, a2, a46, a4, a5, a26]
def w633 : List W := [a57, a1, a27, a2, a46, a4, a5]
def w634 : List W := [a57, a1, a2, a46, a28, a4, a5]
def w635 : List W := [a29, a57, a1, a2, a46, a4, a5]
def w636 : List W := [a57, a1, a2, a46, a4, a5, a30]
def w637 : List W := [a57, a1, a31, a2, a46, a4, a5]
def w638 : List W := [a57, a1, a2, a46, a4, a32, a5]
def w639 : List W := [a149, a57, a1, a2, a46, a4, a5]
def w640 : List W := [a57, a1, a2, a46, a4, a5, a293]
def w641 : List W := [a57, a1, a2, a150, a46, a4, a5]
def w642 : List W := [a57, a1, a2, a46, a294, a4, a5]
def w643 : List W := [a206, a57, a1, a2, a46, a4, a5]
def w644 : List W := [a57, a1, a2, a46, a4, a5, a89]
def w645 : List W := [a57, a1, a2, a90, a46, a4, a5]
def w646 : List W := [a57, a1, a2, a46, a211, a4, a5]
def w647 : List W := [a57, a1, a2, a46, a41, a4, a5]
def w648 : List W := [a57, a1, a2, a46, a4, a5, a42]
def w649 : List W := [a43, a57, a1, a2, a46, a4, a5]
def w650 : List W := [a44, a57, a1, a2, a46, a4, a5]
def w651 : List W := [a57, a1, a2, a46, a4, a5, a47]
def w652 : List W := [a58, a57, a2, a46, a4, a5, a47]
def w653 : List W := [a58, a1, a2, a46, a4, a5, a47]
def w654 : List W := [a1, a2, a284, a46, a4, a5, a47]
def w655 : List W := [a1, a285, a2, a46, a4, a5, a47]
def w656 : List W := [a1, a2, a3, a4, a5, a47]
def w657 : List W := [a57, a1, a2, a3, a4, a5, a47]
def w658 : List W := [a1, a2, a46, a3, a4, a5, a47]
def w659 : List W := [a1, a2, a286, a4, a5, a47]
def w660 : List W := [a57, a1, a2, a286, a4, a5, a47]
def w661 : List W := [a1, a2, a286, a46, a4, a5, a47]
def w662 : List W := [a1, a2, a46, a4, a5, a287, a47]
def w663 : List W := [a1, a2, a46, a288, a4, a5, a47]
def w664 : List W := [a1, a2, a46, a4, a5, a47, a289]
def w665 : List W := [a1, a2, a46, a4, a290, a5, a47]
def w666 : List W := [a1, a2, a46, a4, a5, a47, a47]
def w667 : List W := [a57, a1, a2, a46, a4, a295, a5]
def w668 : List W := [a1, a2, a46, a4, a295, a5, a47]
def w669 : List W := [a57, a2, a46, a4, a5, a151]
def w670 : List W := [a57, a1, a2, a46, a4, a5, a151]
def w671 : List W := [a57, a2, a46, a4, a5, a47, a151]
def w672 : List W := [a296, a57, a1, a2, a46, a4, a5]
def w673 : List W := [a57, a1, a2, a46, a4, a5, a297]
def w674 : List W := [a57, a1, a298, a2, a46, a4, a5]
def w675 : List W := [a57, a1, a2, a46, a4, a5, a299]
def w676 : List W := [a57, a1, a300, a2, a46, a4, a5]
def w677 : List W := [a57, a1, a2, a46, a4, a5, a62]
def w678 : List W := [a57, a1, a91, a2, a46, a4, a5]
def w679 : List W := [a57, a1, a2, a46, a63, a4, a5]
def w680 : List W := [a57, a1, a2, a46, a301, a4, a5]
def w681 : List W := [a57, a1, a2, a46, a4, a5, a302]
def w682 : List W := [a303, a57, a1, a2, a46, a4, a5]
def w683 : List W := [a57, a1, a304, a2, a46, a4, a5]
def w684 : List W := [a57, a1, a2, a46, a4, a305, a5]
def w685 : List W := [a57, a1, a2, a46, a4, a5, a83]
def w686 : List W := [a306, a57, a1, a2, a46, a4, a5]
def w687 : List W := [a57, a84, a1, a2, a46, a4, a5]
def w688 : List W := [a58, a1, a2, a46, a4, a5, a151]
def w689 : List W := [a2, a46, a4, a295, a5, a47, a151]
def w690 : List W := [a1, a2, a46, a4, a5, a47, a151]
def w691 : List W := [a307, a1, a2, a46, a4, a5, a47]
def w692 : List W := [a1, a2, a46, a4, a5, a47, a308]
def w693 : List W := [a1, a2, a46, a4, a5, a151, a62]
def w694 : List W := [a1, a2, a46, a63, a4, a5, a151]
def w695 : List W := [a1, a309, a2, a46, a4, a5, a47]
def w696 : List W := [a1, a2, a46, a4, a310, a5, a47]
def w697 : List W := [a1, a2, a46, a311, a4, a5, a47]
def w698 : List W := [a1, a312, a2, a46, a4, a5, a47]
def w699 : List W := [a1, a2, a46, a4, a5, a83, a151]
def w700 : List W := [a84, a1, a2, a46, a4, a5, a151]
def w701 : List W := [a1, a2, a46, a4, a313, a5, a47]
def w702 : List W := [a1, a314, a2, a46, a4, a5, a47]
def w703 : List W := [a58, a58, a1, a2, a46, a4, a5]
def w704 : List W := [a58, a1, a1, a2, a46, a4, a5]
def w705 : List W := [a65, a58, a1, a2, a46, a4, a5]
def w706 : List W := [a250, a58, a1, a2, a46, a4, a5]
def w707 : List W := [a58, a1, a2, a315, a46, a4, a5]
def w708 : List W := [a272, a58, a1, a2, a46, a4, a5]
def w709 : List W := [a58, a1, a316, a2, a46, a4, a5]
def w710 : List W := [a81, a58, a1, a2, a46, a4, a5]
def w711 : List W := [a1, a2, a46, a317, a4, a5]
def w712 : List W := [a58, a1, a2, a46, a317, a4, a5]
def w713 : List W := [a11, a58, a1, a2, a46, a4, a5]
def w714 : List W := [a58, a1, a2, a318, a46, a4, a5]
def w715 : List W := [a147, a58, a1, a2, a46, a4, a5]
def w716 : List W := [a58, a1, a2, a46, a4, a319, a5]
def w717 : List W := [a178, a58, a1, a2, a46, a4, a5]
def w718 : List W := [a58, a1, a2, a46, a320, a4, a5]
def w719 : List W := [a204, a58, a1, a2, a46, a4, a5]
def w720 : List W := [a1, a2, a46, a4, a5, a321]
def w721 : List W := [a58, a1, a2, a46, a4, a5, a321]
def w722 : List W := [a229, a58, a1, a2, a46, a4, a5]
def w723 : List W := [a58, a1, a2, a46, a4, a322, a5]
def w724 : List W := [a58, a1, a252, a2, a46, a4, a5]
def w725 : List W := [a58, a1, a2, a46, a291, a4, a5]
def w726 : List W := [a292, a58, a1, a2, a46, a4, a5]
def w727 : List W := [a58, a1, a253, a2, a46, a4, a5]
def w728 : List W := [a25, a58, a1, a2, a46, a4, a5]
def w729 : List W := [a58, a1, a2, a46, a4, a5, a26]
def w730 : List W := [a58, a1, a27, a2, a46, a4, a5]
def w731 : List W := [a58, a1, a2, a46, a28, a4, a5]
def w732 : List W := [a29, a58, a1, a2, a46, a4, a5]
def w733 : List W := [a58, a1, a2, a46, a4, a5, a30]
def w734 : List W := [a58, a1, a31, a2, a46, a4, a5]
def w735 : List W := [a58, a1, a2, a46, a4, a32, a5]
def w736 : List W := [a149, a58, a1, a2, a46, a4, a5]
def w737 : List W := [a58, a1, a2, a46, a4, a5, a293]
def w738 : List W := [a58, a1, a2, a150, a46, a4, a5]
def w739 : List W := [a58, a1, a2, a46, a294, a4, a5]
def w740 : List W := [a58, a206, a1, a2, a46, a4, a5]
def w741 : List W := [a58, a1, a2, a46, a4, a5, a89]
def w742 : List W := [a58, a1, a2, a90, a46, a4, a5]
def w743 : List W := [a58, a1, a2, a46, a211, a4, a5]
def w744 : List W := [a58, a1, a2, a46, a41, a4, a5]
def w745 : List W := [a58, a1, a2, a46, a4, a5, a42]
def w746 : List W := [a58, a43, a1, a2, a46, a4, a5]
def w747 : List W := [a58, a44, a1, a2, a46, a4, a5]
def w748 : List W := [a1, a2, a315, a46, a4, a5, a47]
def w749 : List W := [a1, a316, a2, a46, a4, a5, a47]
def w750 : List W := [a1, a2, a46, a317, a4, a5, a47]
def w751 : List W := [a1, a2, a318, a46, a4, a5, a47]
def w752 : List W := [a1, a2, a46, a4, a319, a5, a47]
def w753 : List W := [a1, a2, a46, a320, a4, a5, a47]
def w754 : List W := [a1, a2, a46, a4, a5, a321, a47]
def w755 : List W := [a1, a2, a46, a4, a322, a5, a47]
def w756 : List W := [a58, a2, a46, a4, a295, a5]
def w757 : List W := [a58, a1, a2, a46, a4, a295, a5]
def w758 : List W := [a58, a2, a46, a4, a295, a5, a47]
def w759 : List W := [a296, a58, a1, a2, a46, a4, a5]
def w760 : List W := [a58, a1, a2, a46, a4, a5, a297]
def w761 : List W := [a58, a1, a298, a2, a46, a4, a5]
def w762 : List W := [a58, a1, a2, a46, a4, a5, a299]
def w763 : List W := [a58, a1, a300, a2, a46, a4, a5]
def w764 : List W := [a58, a1, a2, a46, a4, a5, a62]
def w765 : List W := [a58, a1, a91, a2, a46, a4, a5]
def w766 : List W := [a58, a1, a2, a46, a63, a4, a5]
def w767 : List W := [a58, a1, a2, a46, a301, a4, a5]
def w768 : List W := [a58, a1, a2, a46, a4, a5, a302]
def w769 : List W := [a58, a303, a1, a2, a46, a4, a5]
def w770 : List W := [a58, a1, a304, a2, a46, a4, a5]
def w771 : List W := [a58, a1, a2, a46, a4, a305, a5]
def w772 : List W := [a58, a1, a2, a46, a4, a5, a83]
def w773 : List W := [a306, a58, a1, a2, a46, a4, a5]
def w774 : List W := [a58, a84, a1, a2, a46, a4, a5]
def w775 : List W := [a1, a2, a46, a4, a5, a47, a323]
def w776 : List W := [a1, a324, a2, a46, a4, a5, a47]
def w777 : List W := [a1, a2, a46, a4, a5, a47, a325]
def w778 : List W := [a1, a2, a326, a46, a4, a5, a47]
def w779 : List W := [a1, a2, a46, a4, a295, a5, a62]
def w780 : List W := [a1, a2, a46, a63, a4, a295, a5]
def w781 : List W := [a1, a2, a46, a4, a5, a327, a47]
def w782 : List W := [a328, a1, a2, a46, a4, a5, a47]
def w783 : List W := [a1, a2, a46, a4, a5, a329, a47]
def w784 : List W := [a330, a1, a2, a46, a4, a5, a47]
def w785 : List W := [a1, a2, a46, a4, a295, a5, a83]
def w786 : List W := [a84, a1, a2, a46, a4, a295, a5]
def w787 : List W := [a331, a2, a46, a4, a5, a47]
def w788 : List W := [a149, a331, a2, a46, a4, a5, a47]
def w789 : List W := [a1, a331, a2, a46, a4, a5, a47]
def w790 : List W := [a332, a2, a46, a4, a5, a47]
def w791 : List W := [a149, a332, a2, a46, a4, a5, a47]
def w792 : List W := [a332, a1, a2, a46, a4, a5, a47]
def w793 : List W := [a333, a1, a2, a46, a4, a5, a47]
def w794 : List W := [a1, a334, a46, a4, a5, a47]
def w795 : List W := [a149, a1, a334, a46, a4, a5, a47]
def w796 : List W := [a1, a2, a334, a46, a4, a5, a47]
def w797 : List W := [a335, a1, a2, a46, a4, a5, a47]
def w798 : List W := [a1, a336, a46, a4, a5, a47]
def w799 : List W := [a149, a1, a336, a46, a4, a5, a47]
def w800 : List W := [a1, a336, a2, a46, a4, a5, a47]
def w801 : List W := [a149, a1, a2, a46, a4, a5, a47]
def w802 : List W := [a149, a1, a2, a150, a4, a5, a47]
def w803 : List W := [a1, a2, a150, a46, a4, a5, a47]
def w804 : List W := [a149, a1, a2, a46, a294, a5, a47]
def w805 : List W := [a1, a2, a46, a294, a4, a5, a47]
def w806 : List W := [a337, a1, a2, a46, a4, a5, a47]
def w807 : List W := [a1, a2, a46, a4, a338, a47]
def w808 : List W := [a149, a1, a2, a46, a4, a338, a47]
def w809 : List W := [a1, a2, a46, a4, a5, a338, a47]
def w810 : List W := [a339, a1, a2, a46, a4, a5, a47]
def w811 : List W := [a1, a2, a46, a4, a340, a47]
def w812 : List W := [a149, a1, a2, a46, a4, a340, a47]
def w813 : List W := [a1, a2, a46, a4, a340, a5, a47]
def w814 : List W := [a341, a1, a2, a46, a4, a5, a47]
def w815 : List W := [a1, a2, a46, a4, a5, a342]
def w816 : List W := [a149, a1, a2, a46, a4, a5, a342]
def w817 : List W := [a1, a2, a46, a4, a5, a47, a342]
def w818 : List W := [a343, a1, a2, a46, a4, a5, a47]
def w819 : List W := [a1, a2, a46, a4, a5, a344]
def w820 : List W := [a149, a1, a2, a46, a4, a5, a344]
def w821 : List W := [a1, a2, a46, a4, a5, a344, a47]
def w822 : List W := [a149, a1, a252, a2, a4, a5, a47]
def w823 : List W := [a149, a292, a1, a2, a4, a5, a47]
def w824 : List W := [a149, a1, a2, a5, a47, a293]
def w825 : List W := [a149, a1, a2, a46, a5, a47, a293]
def w826 : List W := [a149, a1, a2, a4, a5, a47, a293]
def w827 : List W := [a149, a1, a2, a46, a4, a5, a62]
def w828 : List W := [a149, a1, a2, a46, a63, a4, a5]
def w829 : List W := [a149, a1, a2, a46, a5, a42, a47]
def w830 : List W := [a149, a43, a1, a2, a46, a5, a47]
def w831 : List W := [a149, a1, a2, a46, a4, a5, a83]
def w832 : List W := [a149, a84, a1, a2, a46, a4, a5]
def w833 : List W := [a345, a1, a2, a46, a4, a5, a47]
def w834 : List W := [a1, a2, a46, a4, a5, a47, a346]
def w835 : List W := [a1, a347, a2, a46, a4, a5, a47]
def w836 : List W := [a1, a2, a46, a4, a5, a47, a348]
def w837 : List W := [a349, a1, a2, a46, a4, a5, a47]
def w838 : List W := [a1, a2, a46, a4, a5, a47, a350]
def w839 : List W := [a1, a2, a150, a46, a5, a47, a293]
def w840 : List W := [a1, a2, a294, a4, a5, a47, a293]
def w841 : List W := [a1, a2, a46, a4, a5, a62, a293]
def w842 : List W := [a1, a2, a46, a63, a4, a5, a293]
def w843 : List W := [a1, a2, a46, a4, a5, a47, a293]
def w844 : List W := [a1, a2, a46, a4, a5, a83, a293]
def w845 : List W := [a84, a1, a2, a46, a4, a5, a293]
def w846 : List W := [a1, a2, a46, a4, a351, a5, a47]
def w847 : List W := [a1, a2, a46, a4, a5, a47, a352]
def w848 : List W := [a353, a1, a2, a46, a4, a5, a47]
def w849 : List W := [a1, a2, a354, a46, a4, a5, a47]
def w850 : List W := [a1, a2, a46, a4, a5, a355, a47]
def w851 : List W := [a1, a2, a46, a4, a5, a47, a356]
def w852 : List W := [a357, a1, a2, a46, a4, a5, a47]
def w853 : List W := [a1, a2, a358, a46, a4, a5, a47]
def w854 : List W := [a1, a2, a46, a359, a4, a5, a47]
def w855 : List W := [a360, a1, a2, a46, a4, a5, a47]
def w856 : List W := [a1, a361, a2, a46, a4, a5, a47]
def w857 : List W := [a1, a2, a46, a362, a4, a5, a47]
def w858 : List W := [a363, a1, a2, a46, a4, a5, a47]
def w859 : List W := [a1, a364, a2, a46, a4, a5, a47]
def w860 : List W := [a365, a1, a2, a46, a4, a5, a47]
def w861 : List W := [a1, a2, a46, a4, a5, a47, a366]
def w862 : List W := [a1, a2, a367, a46, a4, a5, a47]
def w863 : List W := [a1, a2, a46, a368, a4, a5, a47]
def w864 : List W := [a1, a369, a2, a46, a4, a5, a47]
def w865 : List W := [a1, a2, a46, a4, a5, a370]
def w866 : List W := [a1, a2, a150, a46, a4, a5, a370]
def w867 : List W := [a1, a2, a46, a4, a5, a47, a370]
def w868 : List W := [a1, a371, a2, a46, a4, a5, a47]
def w869 : List W := [a1, a2, a46, a372, a4, a5]
def w870 : List W := [a1, a2, a150, a46, a372, a4, a5]
def w871 : List W := [a1, a2, a46, a372, a4, a5, a47]
def w872 : List W := [a1, a2, a150, a294, a5, a47]
def w873 : List W := [a1, a2, a150, a46, a294, a5, a47]
def w874 : List W := [a1, a2, a150, a294, a4, a5, a47]
def w875 : List W := [a1, a2, a150, a46, a4, a5, a62]
def w876 : List W := [a1, a2, a150, a46, a63, a4, a5]
def w877 : List W := [a1, a2, a150, a46, a5, a42, a47]
def w878 : List W := [a43, a1, a2, a150, a46, a5, a47]
def w879 : List W := [a1, a2, a150, a46, a4, a5, a83]
def w880 : List W := [a84, a1, a2, a150, a46, a4, a5]
def w881 : List W := [a1, a2, a46, a4, a5, a373, a47]
def w882 : List W := [a374, a1, a2, a46, a4, a5, a47]
def w883 : List W := [a1, a252, a2, a294, a4, a5, a47]
def w884 : List W := [a292, a1, a2, a294, a4, a5, a47]
def w885 : List W := [a375, a1, a2, a46, a4, a5, a47]
def w886 : List W := [a1, a2, a46, a4, a5, a47, a376]
def w887 : List W := [a1, a377, a2, a46, a4, a5, a47]
def w888 : List W := [a1, a2, a46, a378, a4, a5, a47]
def w889 : List W := [a1, a2, a46, a294, a4, a5, a62]
def w890 : List W := [a1, a2, a46, a63, a294, a4, a5]
def w891 : List W := [a1, a2, a46, a379, a4, a5, a47]
def w892 : List W := [a1, a2, a46, a4, a5, a380, a47]
def w893 : List W := [a381, a1, a2, a46, a4, a5, a47]
def w894 : List W := [a382, a1, a2, a46, a4, a5, a47]
def w895 : List W := [a1, a2, a46, a383, a4, a5, a47]
def w896 : List W := [a1, a2, a46, a4, a5, a47, a384]
def w897 : List W := [a385, a1, a2, a46, a4, a5, a47]
def w898 : List W := [a1, a386, a2, a46, a4, a5, a47]
def w899 : List W := [a1, a2, a46, a294, a4, a5, a83]
def w900 : List W := [a84, a1, a2, a46, a294, a4, a5]
def w901 : List W := [a1, a387, a2, a46, a4, a5, a47]
def w902 : List W := [a388, a1, a2, a46, a4, a5, a47]
def w903 : List W := [a49, a1, a2, a46, a4, a5, a47]
def w904 : List W := [a1, a2, a389, a46, a4, a5, a47]
def w905 : List W := [a390, a1, a2, a46, a4, a5, a47]
def w906 : List W := [a1, a391, a2, a46, a4, a5, a47]
def w907 : List W := [a206, a1, a2, a46, a4, a5, a47]
def w908 : List W := [a206, a1, a2, a90, a4, a5, a47]
def w909 : List W := [a1, a2, a90, a46, a4, a5, a47]
def w910 : List W := [a1, a2, a46, a4, a5, a392, a47]
def w911 : List W := [a1, a2, a46, a393, a4, a5, a47]
def w912 : List W := [a206, a1, a2, a46, a211, a4, a47]
def w913 : List W := [a1, a2, a46, a211, a4, a5, a47]
def w914 : List W := [a394, a1, a2, a46, a4, a5, a47]
def w915 : List W := [a1, a2, a46, a4, a5, a395]
def w916 : List W := [a206, a1, a2, a46, a4, a5, a395]
def w917 : List W := [a1, a2, a46, a4, a5, a47, a395]
def w918 : List W := [a396, a1, a2, a46, a4, a5, a47]
def w919 : List W := [a1, a2, a46, a4, a5, a397]
def w920 : List W := [a206, a1, a2, a46, a4, a5, a397]
def w921 : List W := [a1, a2, a46, a4, a5, a397, a47]
def w922 : List W := [a206, a1, a2, a46, a4, a47, a30]
def w923 : List W := [a206, a1, a2, a46, a4, a32, a47]
def w924 : List W := [a206, a1, a2, a4, a47, a89]
def w925 : List W := [a206, a1, a2, a46, a4, a47, a89]
def w926 : List W := [a206, a1, a2, a4, a5, a47, a89]
def w927 : List W := [a206, a1, a2, a46, a4, a5, a62]
def w928 : List W := [a206, a1, a2, a46, a63, a4, a5]
def w929 : List W := [a206, a1, a2, a46, a4, a5, a83]
def w930 : List W := [a206, a84, a1, a2, a46, a4, a5]
def w931 : List W := [a398, a1, a2, a46, a4, a5, a47]
def w932 : List W := [a1, a2, a46, a4, a5, a47, a399]
def w933 : List W := [a29, a1, a2, a46, a4, a47, a89]
def w934 : List W := [a1, a31, a2, a46, a4, a47, a89]
def w935 : List W := [a1, a400, a2, a46, a4, a5, a47]
def w936 : List W := [a1, a2, a46, a4, a5, a47, a401]
def w937 : List W := [a402, a1, a2, a46, a4, a5, a47]
def w938 : List W := [a1, a2, a46, a4, a5, a403, a47]
def w939 : List W := [a1, a2, a90, a46, a4, a47, a89]
def w940 : List W := [a1, a2, a211, a4, a5, a47, a89]
def w941 : List W := [a1, a2, a46, a4, a5, a89, a62]
def w942 : List W := [a1, a2, a46, a63, a4, a5, a89]
def w943 : List W := [a1, a2, a46, a4, a5, a47, a89]
def w944 : List W := [a1, a2, a46, a4, a42, a47, a89]
def w945 : List W := [a44, a1, a2, a46, a4, a47, a89]
def w946 : List W := [a1, a2, a46, a404, a4, a5, a47]
def w947 : List W := [a1, a2, a46, a405, a4, a5, a47]
def w948 : List W := [a1, a2, a46, a4, a5, a83, a89]
def w949 : List W := [a84, a1, a2, a46, a4, a5, a89]
def w950 : List W := [a1, a2, a46, a4, a5, a406, a47]
def w951 : List W := [a1, a2, a46, a4, a5, a407]
def w952 : List W := [a1, a2, a46, a4, a5, a47, a407]
def w953 : List W := [a1, a2, a46, a4, a5, a89, a407]
def w954 : List W := [a408, a1, a2, a46, a4, a5]
def w955 : List W := [a408, a1, a2, a46, a4, a5, a47]
def w956 : List W := [a408, a1, a2, a46, a4, a5, a89]
def w957 : List W := [a1, a2, a409, a46, a4, a5, a47]
def w958 : List W := [a1, a2, a410, a46, a4, a5, a47]
def w959 : List W := [a411, a1, a2, a46, a4, a5, a47]
def w960 : List W := [a1, a412, a2, a46, a4, a5, a47]
def w961 : List W := [a1, a2, a413, a46, a4, a5, a47]
def w962 : List W := [a414, a1, a2, a46, a4, a5, a47]
def w963 : List W := [a415, a1, a2, a46, a4, a5, a47]
def w964 : List W := [a1, a2, a90, a46, a4, a47, a30]
def w965 : List W := [a1, a2, a90, a46, a4, a32, a47]
def w966 : List W := [a1, a2, a46, a4, a5, a47, a416]
def w967 : List W := [a1, a2, a46, a417, a4, a5, a47]
def w968 : List W := [a418, a1, a2, a46, a4, a5, a47]
def w969 : List W := [a1, a2, a46, a4, a5, a419]
def w970 : List W := [a1, a2, a90, a46, a4, a5, a419]
def w971 : List W := [a1, a2, a46, a4, a5, a47, a419]
def w972 : List W := [a1, a420, a2, a46, a4, a5, a47]
def w973 : List W := [a1, a2, a46, a4, a5, a421]
def w974 : List W := [a1, a2, a90, a46, a4, a5, a421]
def w975 : List W := [a1, a2, a46, a4, a5, a421, a47]
def w976 : List W := [a1, a2, a90, a211, a4, a47]
def w977 : List W := [a1, a2, a90, a46, a211, a4, a47]
def w978 : List W := [a1, a2, a90, a211, a4, a5, a47]
def w979 : List W := [a1, a2, a90, a46, a4, a5, a62]
def w980 : List W := [a1, a2, a90, a46, a63, a4, a5]
def w981 : List W := [a1, a2, a90, a46, a4, a5, a83]
def w982 : List W := [a84, a1, a2, a90, a46, a4, a5]
def w983 : List W := [a1, a2, a46, a4, a5, a422, a47]
def w984 : List W := [a423, a1, a2, a46, a4, a5, a47]
def w985 : List W := [a424, a1, a2, a46, a4, a5, a47]
def w986 : List W := [a1, a46, a4, a5, a47, a425]
def w987 : List W := [a1, a2, a46, a4, a5, a47, a425]
def w988 : List W := [a1, a46, a211, a4, a5, a47, a425]
def w989 : List W := [a1, a426, a46, a4, a5, a47]
def w990 : List W := [a1, a426, a2, a46, a4, a5, a47]
def w991 : List W := [a1, a426, a46, a211, a4, a5, a47]
def w992 : List W := [a1, a2, a46, a427, a4, a5, a47]
def w993 : List W := [a29, a1, a2, a46, a211, a4, a47]
def w994 : List W := [a1, a31, a2, a46, a211, a4, a47]
def w995 : List W := [a1, a2, a46, a211, a4, a5, a62]
def w996 : List W := [a1, a2, a46, a211, a63, a4, a5]
def w997 : List W := [a1, a2, a46, a428, a5, a47]
def w998 : List W := [a1, a2, a46, a211, a428, a5, a47]
def w999 : List W := [a1, a2, a46, a4, a428, a5, a47]
def w1000 : List W := [a429, a1, a2, a46, a5, a47]
def w1001 : List W := [a429, a1, a2, a46, a211, a5, a47]
def w1002 : List W := [a429, a1, a2, a46, a4, a5, a47]
def w1003 : List W := [a1, a2, a46, a430, a4, a5, a47]
def w1004 : List W := [a1, a2, a46, a4, a5, a431]
def w1005 : List W := [a1, a2, a46, a211, a4, a5, a431]
def w1006 : List W := [a1, a2, a46, a4, a5, a47, a431]
def w1007 : List W := [a432, a1, a2, a46, a4, a5, a47]
def w1008 : List W := [a1, a433, a2, a46, a4, a5]
def w1009 : List W := [a1, a433, a2, a46, a211, a4, a5]
def w1010 : List W := [a1, a433, a2, a46, a4, a5, a47]
def w1011 : List W := [a1, a2, a46, a211, a4, a42, a47]
def w1012 : List W := [a44, a1, a2, a46, a211, a4, a47]
def w1013 : List W := [a1, a2, a46, a211, a4, a5, a83]
def w1014 : List W := [a84, a1, a2, a46, a211, a4, a5]
def w1015 : List W := [a1, a2, a434, a46, a4, a5, a47]
def w1016 : List W := [a435, a1, a2, a46, a4, a5, a47]
def w1017 : List W := [a1, a252, a2, a46, a4, a5, a47]
def w1018 : List W := [a292, a1, a252, a46, a4, a5, a47]
def w1019 : List W := [a292, a1, a2, a46, a4, a5, a47]
def w1020 : List W := [a1, a253, a252, a2, a4, a5, a47]
def w1021 : List W := [a1, a253, a2, a46, a4, a5, a47]
def w1022 : List W := [a1, a2, a46, a4, a5, a47, a436]
def w1023 : List W := [a1, a2, a46, a437, a4, a5, a47]
def w1024 : List W := [a1, a2, a46, a4, a5, a47, a438]
def w1025 : List W := [a1, a2, a46, a4, a439, a5, a47]
def w1026 : List W := [a440, a1, a2, a46, a4, a5, a47]
def w1027 : List W := [a1, a2, a46, a4, a5, a441]
def w1028 : List W := [a1, a252, a2, a46, a4, a5, a441]
def w1029 : List W := [a1, a2, a46, a4, a5, a47, a441]
def w1030 : List W := [a1, a442, a2, a46, a4, a5, a47]
def w1031 : List W := [a1, a2, a46, a4, a5, a443]
def w1032 : List W := [a1, a252, a2, a46, a4, a5, a443]
def w1033 : List W := [a1, a2, a46, a4, a5, a443, a47]
def w1034 : List W := [a1, a252, a291, a4, a5, a47]
def w1035 : List W := [a1, a252, a2, a291, a4, a5, a47]
def w1036 : List W := [a1, a252, a46, a291, a4, a5, a47]
def w1037 : List W := [a1, a252, a46, a4, a5, a47, a30]
def w1038 : List W := [a1, a252, a31, a46, a4, a5, a47]
def w1039 : List W := [a1, a252, a2, a46, a4, a5, a62]
def w1040 : List W := [a1, a252, a2, a46, a63, a4, a5]
def w1041 : List W := [a1, a252, a2, a46, a4, a5, a83]
def w1042 : List W := [a84, a1, a252, a2, a46, a4, a5]
def w1043 : List W := [a444, a1, a2, a46, a4, a5, a47]
def w1044 : List W := [a1, a2, a445, a46, a4, a5, a47]
def w1045 : List W := [a292, a1, a2, a291, a4, a5, a47]
def w1046 : List W := [a1, a253, a46, a291, a4, a5, a47]
def w1047 : List W := [a1, a2, a46, a291, a4, a5, a47]
def w1048 : List W := [a1, a46, a291, a4, a5, a47, a26]
def w1049 : List W := [a1, a27, a46, a291, a4, a5, a47]
def w1050 : List W := [a1, a2, a46, a291, a4, a5, a62]
def w1051 : List W := [a1, a2, a46, a291, a63, a4, a5]
def w1052 : List W := [a446, a1, a2, a46, a4, a5, a47]
def w1053 : List W := [a1, a2, a46, a447, a4, a5, a47]
def w1054 : List W := [a448, a1, a2, a46, a4, a5, a47]
def w1055 : List W := [a1, a2, a449, a46, a4, a5, a47]
def w1056 : List W := [a1, a450, a2, a46, a4, a5, a47]
def w1057 : List W := [a1, a2, a46, a4, a5, a47, a451]
def w1058 : List W := [a1, a2, a452, a46, a4, a5, a47]
def w1059 : List W := [a1, a2, a46, a453, a4, a5, a47]
def w1060 : List W := [a1, a2, a46, a291, a4, a5, a83]
def w1061 : List W := [a84, a1, a2, a46, a291, a4, a5]
def w1062 : List W := [a1, a454, a2, a46, a4, a5, a47]
def w1063 : List W := [a455, a1, a2, a46, a4, a5, a47]
def w1064 : List W := [a1, a2, a46, a4, a5, a47, a456]
def w1065 : List W := [a1, a2, a46, a457, a4, a5, a47]
def w1066 : List W := [a1, a2, a46, a4, a458, a47]
def w1067 : List W := [a1, a253, a2, a46, a4, a458, a47]
def w1068 : List W := [a1, a2, a46, a4, a5, a458, a47]
def w1069 : List W := [a1, a2, a46, a459, a4, a47]
def w1070 : List W := [a1, a253, a2, a46, a459, a4, a47]
def w1071 : List W := [a1, a2, a46, a459, a4, a5, a47]
def w1072 : List W := [a1, a460, a2, a46, a4, a5, a47]
def w1073 : List W := [a1, a2, a46, a4, a5, a461]
def w1074 : List W := [a1, a253, a2, a46, a4, a5, a461]
def w1075 : List W := [a1, a2, a46, a4, a5, a47, a461]
def w1076 : List W := [a462, a1, a2, a46, a4, a5, a47]
def w1077 : List W := [a1, a2, a46, a463, a4, a5]
def w1078 : List W := [a1, a253, a2, a46, a463, a4, a5]
def w1079 : List W := [a1, a2, a46, a463, a4, a5, a47]
def w1080 : List W := [a292, a1, a253, a4, a5, a47]
def w1081 : List W := [a292, a1, a253, a2, a4, a5, a47]
def w1082 : List W := [a292, a1, a253, a46, a4, a5, a47]
def w1083 : List W := [a1, a253, a46, a4, a5, a47, a30]
def w1084 : List W := [a1, a253, a31, a46, a4, a5, a47]
def w1085 : List W := [a1, a253, a2, a46, a4, a5, a62]
def w1086 : List W := [a1, a253, a2, a46, a63, a4, a5]
def w1087 : List W := [a1, a253, a2, a46, a4, a5, a83]
def w1088 : List W := [a84, a1, a253, a2, a46, a4, a5]
def w1089 : List W := [a1, a464, a2, a46, a4, a5, a47]
def w1090 : List W := [a465, a1, a2, a46, a4, a5, a47]
def w1091 : List W := [a1, a2, a46, a4, a466, a5, a47]
def w1092 : List W := [a1, a2, a46, a467, a4, a5, a47]
def w1093 : List W := [a1, a2, a46, a4, a468, a47]
def w1094 : List W := [a292, a1, a2, a46, a4, a468, a47]
def w1095 : List W := [a1, a2, a46, a4, a5, a468, a47]
def w1096 : List W := [a1, a2, a46, a4, a469, a47]
def w1097 : List W := [a292, a1, a2, a46, a4, a469, a47]
def w1098 : List W := [a1, a2, a46, a4, a469, a5, a47]
def w1099 : List W := [a470, a1, a2, a46, a4, a5, a47]
def w1100 : List W := [a1, a2, a46, a4, a5, a47, a471]
def w1101 : List W := [a472, a1, a2, a46, a4, a5, a47]
def w1102 : List W := [a1, a2, a46, a4, a5, a473, a47]
def w1103 : List W := [a292, a1, a46, a4, a5, a47, a26]
def w1104 : List W := [a292, a1, a27, a46, a4, a5, a47]
def w1105 : List W := [a292, a1, a2, a46, a4, a5, a62]
def w1106 : List W := [a292, a1, a2, a46, a63, a4, a5]
def w1107 : List W := [a292, a1, a2, a46, a4, a5, a83]
def w1108 : List W := [a292, a84, a1, a2, a46, a4, a5]
def w1109 : List W := [a1, a474, a2, a46, a4, a5, a47]
def w1110 : List W := [a475, a1, a2, a46, a4, a5, a47]
def w1111 : List W := [a1, a2, a46, a476, a4, a5, a47]
def w1112 : List W := [a1, a477, a2, a46, a4, a5, a47]
def w1113 : List W := [a1, a300, a2, a46, a4, a5, a47]
def w1114 : List W := [a1, a300, a91, a2, a4, a5, a47]
def w1115 : List W := [a1, a91, a2, a46, a4, a5, a47]
def w1116 : List W := [a1, a2, a46, a4, a5, a47, a478]
def w1117 : List W := [a1, a2, a46, a479, a4, a5, a47]
def w1118 : List W := [a1, a2, a46, a4, a5, a480, a47]
def w1119 : List W := [a1, a2, a46, a481, a4, a5, a47]
def w1120 : List W := [a1, a2, a46, a63, a4, a5]
def w1121 : List W := [a1, a300, a2, a46, a63, a4, a5]
def w1122 : List W := [a1, a2, a46, a63, a4, a5, a47]
def w1123 : List W := [a1, a300, a2, a4, a5, a62]
def w1124 : List W := [a1, a300, a2, a46, a4, a5, a62]
def w1125 : List W := [a1, a300, a2, a4, a5, a47, a62]
def w1126 : List W := [a1, a300, a2, a46, a4, a5, a83]
def w1127 : List W := [a84, a1, a300, a2, a46, a4, a5]
def w1128 : List W := [a9, a1, a2, a46, a4, a5]
def w1129 : List W := [a9, a1, a2, a46, a4, a5, a62]
def w1130 : List W := [a1, a2, a46, a4, a5, a62, a101]
def w1131 : List W := [a11, a1, a2, a46, a4, a5, a62]
def w1132 : List W := [a1, a2, a46, a4, a5, a482, a62]
def w1133 : List W := [a25, a1, a2, a46, a4, a5, a62]
def w1134 : List W := [a1, a2, a46, a4, a5, a26, a62]
def w1135 : List W := [a1, a27, a2, a46, a4, a5, a62]
def w1136 : List W := [a1, a2, a46, a28, a4, a5, a62]
def w1137 : List W := [a29, a1, a2, a46, a4, a5, a62]
def w1138 : List W := [a1, a2, a46, a4, a5, a30, a62]
def w1139 : List W := [a1, a31, a2, a46, a4, a5, a62]
def w1140 : List W := [a1, a2, a46, a4, a32, a5, a62]
def w1141 : List W := [a1, a483, a2, a46, a4, a5, a62]
def w1142 : List W := [a1, a2, a46, a4, a5, a62, a451]
def w1143 : List W := [a472, a1, a2, a46, a4, a5, a62]
def w1144 : List W := [a1, a2, a46, a4, a5, a484, a62]
def w1145 : List W := [a1, a2, a46, a4, a5, a62]
def w1146 : List W := [a1, a2, a46, a46, a4, a5, a62]
def w1147 : List W := [a1, a2, a46, a4, a5, a62, a62]
def w1148 : List W := [a65, a1, a2, a46, a4, a5, a62]
def w1149 : List W := [a1, a2, a63, a4, a5, a62]
def w1150 : List W := [a1, a2, a46, a63, a4, a5, a62]
def w1151 : List W := [a1, a2, a46, a41, a4, a5, a62]
def w1152 : List W := [a1, a2, a46, a4, a5, a42, a62]
def w1153 : List W := [a43, a1, a2, a46, a4, a5, a62]
def w1154 : List W := [a44, a1, a2, a46, a4, a5, a62]
def w1155 : List W := [a1, a2, a46, a485, a4, a5, a62]
def w1156 : List W := [a1, a2, a46, a4, a5, a62, a356]
def w1157 : List W := [a385, a1, a2, a46, a4, a5, a62]
def w1158 : List W := [a1, a2, a46, a486, a4, a5, a62]
def w1159 : List W := [a1, a2, a46, a4, a487, a5, a62]
def w1160 : List W := [a1, a2, a46, a4, a5, a62, a407]
def w1161 : List W := [a432, a1, a2, a46, a4, a5, a62]
def w1162 : List W := [a1, a2, a488, a46, a4, a5]
def w1163 : List W := [a1, a2, a488, a46, a4, a5, a62]
def w1164 : List W := [a9, a1, a2, a46, a4, a5, a47]
def w1165 : List W := [a1, a2, a46, a4, a5, a47, a482]
def w1166 : List W := [a296, a1, a2, a46, a4, a5, a62]
def w1167 : List W := [a1, a2, a46, a4, a5, a62, a297]
def w1168 : List W := [a1, a298, a2, a46, a4, a5, a62]
def w1169 : List W := [a1, a2, a46, a4, a5, a299, a62]
def w1170 : List W := [a1, a483, a2, a46, a4, a5, a47]
def w1171 : List W := [a1, a2, a46, a4, a5, a47, a484]
def w1172 : List W := [a1, a91, a2, a46, a4, a5, a62]
def w1173 : List W := [a1, a2, a63, a4, a5, a47, a62]
def w1174 : List W := [a1, a2, a46, a4, a5, a47, a62]
def w1175 : List W := [a1, a2, a46, a301, a4, a5, a62]
def w1176 : List W := [a1, a2, a46, a4, a5, a302, a62]
def w1177 : List W := [a303, a1, a2, a46, a4, a5, a62]
def w1178 : List W := [a1, a304, a2, a46, a4, a5, a62]
def w1179 : List W := [a1, a2, a46, a485, a4, a5, a47]
def w1180 : List W := [a1, a2, a46, a486, a4, a5, a47]
def w1181 : List W := [a1, a2, a46, a4, a305, a5, a62]
def w1182 : List W := [a1, a2, a46, a4, a5, a83, a62]
def w1183 : List W := [a306, a1, a2, a46, a4, a5, a62]
def w1184 : List W := [a84, a1, a2, a46, a4, a5, a62]
def w1185 : List W := [a1, a2, a46, a4, a487, a5, a47]
def w1186 : List W := [a1, a2, a488, a46, a4, a5, a47]
def w1187 : List W := [a1, a2, a489, a46, a4, a5, a47]
def w1188 : List W := [a490, a1, a2, a46, a4, a5, a47]
def w1189 : List W := [a1, a2, a491, a46, a4, a5, a47]
def w1190 : List W := [a492, a1, a2, a46, a4, a5, a47]
def w1191 : List W := [a1, a2, a46, a4, a5, a47, a493]
def w1192 : List W := [a1, a2, a46, a494, a4, a5, a47]
def w1193 : List W := [a1, a2, a46, a4, a5, a47, a495]
def w1194 : List W := [a1, a2, a46, a4, a496, a5, a47]
def w1195 : List W := [a1, a91, a2, a63, a4, a5]
def w1196 : List W := [a1, a91, a2, a46, a63, a4, a5]
def w1197 : List W := [a1, a91, a2, a63, a4, a5, a47]
def w1198 : List W := [a1, a91, a2, a46, a4, a5, a83]
def w1199 : List W := [a84, a1, a91, a2, a46, a4, a5]
def w1200 : List W := [a116, a1, a2, a46, a63, a4, a5]
def w1201 : List W := [a1, a2, a46, a63, a4, a5, a497]
def w1202 : List W := [a498, a1, a2, a46, a4, a5]
def w1203 : List W := [a498, a1, a2, a46, a63, a4, a5]
def w1204 : List W := [a1, a2, a46, a103, a63, a4, a5]
def w1205 : List W := [a470, a1, a2, a46, a63, a4, a5]
def w1206 : List W := [a1, a2, a46, a63, a4, a5, a499]
def w1207 : List W := [a1, a500, a2, a46, a63, a4, a5]
def w1208 : List W := [a1, a2, a46, a453, a63, a4, a5]
def w1209 : List W := [a25, a1, a2, a46, a63, a4, a5]
def w1210 : List W := [a1, a2, a46, a63, a4, a5, a26]
def w1211 : List W := [a1, a27, a2, a46, a63, a4, a5]
def w1212 : List W := [a1, a2, a46, a63, a28, a4, a5]
def w1213 : List W := [a29, a1, a2, a46, a63, a4, a5]
def w1214 : List W := [a1, a2, a46, a63, a4, a5, a30]
def w1215 : List W := [a1, a31, a2, a46, a63, a4, a5]
def w1216 : List W := [a1, a2, a46, a63, a4, a32, a5]
def w1217 : List W := [a65, a1, a2, a46, a63, a4, a5]
def w1218 : List W := [a1, a2, a46, a46, a63, a4, a5]
def w1219 : List W := [a1, a2, a46, a63, a63, a4, a5]
def w1220 : List W := [a1, a2, a46, a383, a63, a4, a5]
def w1221 : List W := [a1, a2, a46, a63, a4, a501, a5]
def w1222 : List W := [a357, a1, a2, a46, a63, a4, a5]
def w1223 : List W := [a502, a1, a2, a46, a63, a4, a5]
def w1224 : List W := [a1, a2, a46, a430, a63, a4, a5]
def w1225 : List W := [a1, a2, a46, a4, a5, a503]
def w1226 : List W := [a1, a2, a46, a63, a4, a5, a503]
def w1227 : List W := [a408, a1, a2, a46, a63, a4, a5]
def w1228 : List W := [a504, a1, a2, a46, a63, a4, a5]
def w1229 : List W := [a1, a2, a46, a41, a63, a4, a5]
def w1230 : List W := [a1, a2, a46, a63, a4, a5, a42]
def w1231 : List W := [a43, a1, a2, a46, a63, a4, a5]
def w1232 : List W := [a44, a1, a2, a46, a63, a4, a5]
def w1233 : List W := [a1, a2, a46, a4, a5, a497, a47]
def w1234 : List W := [a498, a1, a2, a46, a4, a5, a47]
def w1235 : List W := [a1, a2, a46, a4, a5, a47, a499]
def w1236 : List W := [a1, a500, a2, a46, a4, a5, a47]
def w1237 : List W := [a296, a1, a2, a46, a63, a4, a5]
def w1238 : List W := [a1, a2, a46, a63, a4, a5, a297]
def w1239 : List W := [a1, a298, a2, a46, a63, a4, a5]
def w1240 : List W := [a1, a2, a46, a63, a4, a5, a299]
def w1241 : List W := [a1, a2, a46, a4, a501, a5, a47]
def w1242 : List W := [a502, a1, a2, a46, a4, a5, a47]
def w1243 : List W := [a1, a2, a46, a4, a5, a503, a47]
def w1244 : List W := [a504, a1, a2, a46, a4, a5, a47]
def w1245 : List W := [a1, a2, a46, a301, a63, a4, a5]
def w1246 : List W := [a1, a2, a46, a63, a4, a5, a302]
def w1247 : List W := [a303, a1, a2, a46, a63, a4, a5]
def w1248 : List W := [a1, a304, a2, a46, a63, a4, a5]
def w1249 : List W := [a1, a2, a46, a63, a4, a305, a5]
def w1250 : List W := [a1, a2, a46, a63, a4, a5, a83]
def w1251 : List W := [a306, a1, a2, a46, a63, a4, a5]
def w1252 : List W := [a84, a1, a2, a46, a63, a4, a5]
def w1253 : List W := [a1, a2, a46, a4, a5, a505, a47]
def w1254 : List W := [a506, a1, a2, a46, a4, a5, a47]
def w1255 : List W := [a507, a1, a2, a46, a4, a5, a47]
def w1256 : List W := [a1, a46, a4, a5, a47, a508]
def w1257 : List W := [a1, a2, a46, a4, a5, a47, a508]
def w1258 : List W := [a1, a46, a41, a4, a5, a47, a508]
def w1259 : List W := [a1, a509, a46, a4, a5, a47]
def w1260 : List W := [a1, a509, a2, a46, a4, a5, a47]
def w1261 : List W := [a1, a509, a46, a41, a4, a5, a47]
def w1262 : List W := [a1, a2, a46, a510, a4, a5, a47]
def w1263 : List W := [a1, a2, a46, a4, a5, a47, a511]
def w1264 : List W := [a1, a2, a512, a46, a4, a5, a47]
def w1265 : List W := [a1, a2, a46, a41, a4, a5, a47]
def w1266 : List W := [a43, a1, a2, a46, a41, a5, a47]
def w1267 : List W := [a43, a1, a2, a46, a4, a5, a47]
def w1268 : List W := [a44, a1, a2, a46, a41, a4, a47]
def w1269 : List W := [a44, a1, a2, a46, a4, a5, a47]
def w1270 : List W := [a1, a2, a46, a513, a4, a5, a47]
def w1271 : List W := [a1, a2, a46, a4, a5, a514]
def w1272 : List W := [a1, a2, a46, a41, a4, a5, a514]
def w1273 : List W := [a1, a2, a46, a4, a5, a47, a514]
def w1274 : List W := [a515, a1, a2, a46, a4, a5, a47]
def w1275 : List W := [a1, a516, a2, a46, a4, a5]
def w1276 : List W := [a1, a516, a2, a46, a41, a4, a5]
def w1277 : List W := [a1, a516, a2, a46, a4, a5, a47]
def w1278 : List W := [a1, a2, a46, a41, a42, a47]
def w1279 : List W := [a1, a2, a46, a41, a4, a42, a47]
def w1280 : List W := [a1, a2, a46, a41, a5, a42, a47]
def w1281 : List W := [a1, a2, a46, a41, a4, a5, a83]
def w1282 : List W := [a84, a1, a2, a46, a41, a4, a5]
def w1283 : List W := [a517, a1, a2, a46, a4, a5, a47]
def w1284 : List W := [a1, a2, a46, a4, a5, a518, a47]
def w1285 : List W := [a1, a2, a46, a5, a42, a47, a26]
def w1286 : List W := [a1, a2, a46, a28, a5, a42, a47]
def w1287 : List W := [a1, a2, a46, a4, a42, a47, a30]
def w1288 : List W := [a1, a2, a46, a4, a32, a42, a47]
def w1289 : List W := [a519, a1, a2, a46, a4, a5, a47]
def w1290 : List W := [a1, a2, a46, a4, a5, a47, a520]
def w1291 : List W := [a1, a521, a2, a46, a4, a5, a47]
def w1292 : List W := [a1, a2, a46, a4, a5, a522, a47]
def w1293 : List W := [a523, a1, a2, a46, a4, a5, a47]
def w1294 : List W := [a1, a2, a46, a4, a524, a5, a47]
def w1295 : List W := [a43, a1, a2, a46, a4, a42, a47]
def w1296 : List W := [a44, a1, a2, a46, a5, a42, a47]
def w1297 : List W := [a1, a2, a46, a4, a5, a42, a47]
def w1298 : List W := [a1, a2, a46, a301, a5, a42, a47]
def w1299 : List W := [a1, a304, a2, a46, a5, a42, a47]
def w1300 : List W := [a1, a2, a46, a4, a42, a83]
def w1301 : List W := [a1, a2, a46, a4, a5, a42, a83]
def w1302 : List W := [a1, a2, a46, a4, a42, a47, a83]
def w1303 : List W := [a306, a1, a2, a46, a4, a42, a47]
def w1304 : List W := [a84, a1, a2, a46, a4, a5, a42]
def w1305 : List W := [a1, a2, a46, a4, a525, a5, a47]
def w1306 : List W := [a1, a2, a46, a4, a5, a47, a526]
def w1307 : List W := [a527, a1, a2, a46, a4, a5, a47]
def w1308 : List W := [a528, a1, a2, a46, a4, a5, a47]
def w1309 : List W := [a1, a529, a2, a46, a4, a5, a47]
def w1310 : List W := [a530, a1, a2, a46, a4, a5, a47]
def w1311 : List W := [a531, a1, a2, a46, a4, a5, a47]
def w1312 : List W := [a1, a2, a532, a46, a4, a5, a47]
def w1313 : List W := [a533, a1, a2, a46, a4, a5, a47]
def w1314 : List W := [a1, a534, a2, a46, a4, a5, a47]
def w1315 : List W := [a1, a2, a46, a535, a4, a5, a47]
def w1316 : List W := [a1, a2, a536, a46, a4, a5, a47]
def w1317 : List W := [a537, a1, a2, a46, a4, a5, a47]
def w1318 : List W := [a1, a2, a46, a4, a5, a47, a538]
def w1319 : List W := [a539, a1, a2, a46, a4, a5, a47]
def w1320 : List W := [a1, a2, a46, a4, a5, a540, a47]
def w1321 : List W := [a43, a1, a2, a46, a5, a47, a26]
def w1322 : List W := [a43, a1, a2, a46, a28, a5, a47]
def w1323 : List W := [a43, a44, a1, a2, a46, a47]
def w1324 : List W := [a43, a44, a1, a2, a46, a4, a47]
def w1325 : List W := [a43, a44, a1, a2, a46, a5, a47]
def w1326 : List W := [a43, a1, a2, a46, a301, a5, a47]
def w1327 : List W := [a43, a1, a304, a2, a46, a5, a47]
def w1328 : List W := [a43, a1, a2, a46, a4, a5, a83]
def w1329 : List W := [a43, a84, a1, a2, a46, a4, a5]
def w1330 : List W := [a1, a541, a2, a46, a4, a5, a47]
def w1331 : List W := [a542, a1, a2, a46, a4, a5, a47]
def w1332 : List W := [a52, a1, a2, a46, a4, a5, a47]
def w1333 : List W := [a1, a2, a543, a46, a4, a5, a47]
def w1334 : List W := [a544, a1, a2, a46, a4, a5, a47]
def w1335 : List W := [a1, a545, a2, a46, a4, a5, a47]
def w1336 : List W := [a1, a2, a46, a546, a4, a5, a47]
def w1337 : List W := [a1, a2, a547, a46, a4, a5, a47]
def w1338 : List W := [a548, a1, a2, a46, a4, a5, a47]
def w1339 : List W := [a1, a2, a46, a4, a5, a549]
def w1340 : List W := [a44, a1, a2, a46, a4, a5, a549]
def w1341 : List W := [a1, a2, a46, a4, a5, a47, a549]
def w1342 : List W := [a550, a1, a2, a46, a4, a5, a47]
def w1343 : List W := [a1, a2, a46, a4, a5, a551]
def w1344 : List W := [a44, a1, a2, a46, a4, a5, a551]
def w1345 : List W := [a1, a2, a46, a4, a5, a551, a47]
def w1346 : List W := [a44, a1, a2, a46, a4, a47, a30]
def w1347 : List W := [a44, a1, a2, a46, a4, a32, a47]
def w1348 : List W := [a44, a1, a2, a46, a4, a83]
def w1349 : List W := [a44, a1, a2, a46, a4, a5, a83]
def w1350 : List W := [a44, a1, a2, a46, a4, a47, a83]
def w1351 : List W := [a306, a44, a1, a2, a46, a4, a47]
def w1352 : List W := [a44, a84, a1, a2, a46, a4, a5]
def w1353 : List W := [a1, a552, a2, a46, a4, a5, a47]
def w1354 : List W := [a553, a1, a2, a46, a4, a5, a47]
def w1355 : List W := [a25, a1, a2, a46, a4, a5, a47]
def w1356 : List W := [a25, a1, a27, a46, a4, a5, a47]
def w1357 : List W := [a1, a27, a2, a46, a4, a5, a47]
def w1358 : List W := [a1, a2, a46, a554, a4, a5, a47]
def w1359 : List W := [a1, a2, a555, a46, a4, a5, a47]
def w1360 : List W := [a25, a1, a2, a46, a28, a5, a47]
def w1361 : List W := [a1, a2, a46, a28, a4, a5, a47]
def w1362 : List W := [a1, a2, a46, a4, a556, a47]
def w1363 : List W := [a25, a1, a2, a46, a4, a556, a47]
def w1364 : List W := [a1, a2, a46, a4, a5, a556, a47]
def w1365 : List W := [a1, a2, a46, a4, a557, a47]
def w1366 : List W := [a25, a1, a2, a46, a4, a557, a47]
def w1367 : List W := [a1, a2, a46, a4, a557, a5, a47]
def w1368 : List W := [a558, a1, a2, a46, a4, a5, a47]
def w1369 : List W := [a1, a2, a46, a4, a5, a559]
def w1370 : List W := [a25, a1, a2, a46, a4, a5, a559]
def w1371 : List W := [a1, a2, a46, a4, a5, a47, a559]
def w1372 : List W := [a560, a1, a2, a46, a4, a5, a47]
def w1373 : List W := [a1, a2, a46, a4, a5, a561]
def w1374 : List W := [a25, a1, a2, a46, a4, a5, a561]
def w1375 : List W := [a1, a2, a46, a4, a5, a561, a47]
def w1376 : List W := [a25, a1, a46, a5, a47, a26]
def w1377 : List W := [a25, a1, a2, a46, a5, a47, a26]
def w1378 : List W := [a25, a1, a46, a4, a5, a47, a26]
def w1379 : List W := [a25, a1, a2, a46, a4, a5, a83]
def w1380 : List W := [a25, a84, a1, a2, a46, a4, a5]
def w1381 : List W := [a562, a1, a2, a46, a4, a5, a47]
def w1382 : List W := [a1, a2, a46, a4, a5, a47, a563]
def w1383 : List W := [a1, a27, a2, a46, a5, a47, a26]
def w1384 : List W := [a1, a46, a28, a4, a5, a47, a26]
def w1385 : List W := [a1, a46, a4, a5, a47, a26, a30]
def w1386 : List W := [a1, a31, a46, a4, a5, a47, a26]
def w1387 : List W := [a1, a46, a4, a5, a47, a26, a297]
def w1388 : List W := [a1, a298, a46, a4, a5, a47, a26]
def w1389 : List W := [a1, a2, a46, a4, a5, a47, a26]
def w1390 : List W := [a1, a564, a2, a4, a5, a47]
def w1391 : List W := [a1, a564, a2, a46, a4, a5, a47]
def w1392 : List W := [a1, a564, a2, a4, a5, a47, a26]
def w1393 : List W := [a1, a2, a4, a565, a5, a47]
def w1394 : List W := [a1, a2, a46, a4, a565, a5, a47]
def w1395 : List W := [a1, a2, a4, a565, a5, a47, a26]
def w1396 : List W := [a1, a2, a46, a4, a5, a83, a26]
def w1397 : List W := [a84, a1, a2, a46, a4, a5, a26]
def w1398 : List W := [a1, a2, a46, a566, a4, a5, a47]
def w1399 : List W := [a1, a2, a567, a46, a4, a5, a47]
def w1400 : List W := [a1, a2, a46, a568, a4, a5]
def w1401 : List W := [a1, a2, a46, a568, a4, a5, a47]
def w1402 : List W := [a1, a2, a46, a568, a4, a5, a26]
def w1403 : List W := [a1, a2, a46, a4, a5, a47, a569]
def w1404 : List W := [a1, a570, a2, a46, a4, a5, a47]
def w1405 : List W := [a1, a2, a571, a46, a4, a5]
def w1406 : List W := [a1, a2, a571, a46, a4, a5, a47]
def w1407 : List W := [a1, a2, a571, a46, a4, a5, a26]
def w1408 : List W := [a2, a46, a4, a5, a572, a47]
def w1409 : List W := [a1, a2, a46, a4, a5, a572, a47]
def w1410 : List W := [a2, a46, a28, a4, a5, a572, a47]
def w1411 : List W := [a573, a2, a46, a4, a5, a47]
def w1412 : List W := [a573, a1, a2, a46, a4, a5, a47]
def w1413 : List W := [a573, a2, a46, a28, a4, a5, a47]
def w1414 : List W := [a1, a27, a46, a28, a5, a47]
def w1415 : List W := [a1, a27, a2, a46, a28, a5, a47]
def w1416 : List W := [a1, a27, a46, a28, a4, a5, a47]
def w1417 : List W := [a1, a2, a46, a4, a5, a47, a574]
def w1418 : List W := [a1, a2, a575, a46, a4, a5, a47]
def w1419 : List W := [a1, a2, a46, a4, a5, a576, a47]
def w1420 : List W := [a577, a1, a2, a46, a4, a5, a47]
def w1421 : List W := [a1, a2, a46, a578, a4, a5, a47]
def w1422 : List W := [a1, a2, a46, a4, a5, a47, a579]
def w1423 : List W := [a580, a1, a2, a46, a4, a5, a47]
def w1424 : List W := [a1, a581, a2, a46, a4, a5, a47]
def w1425 : List W := [a1, a2, a46, a28, a4, a5, a83]
def w1426 : List W := [a84, a1, a2, a46, a28, a4, a5]
def w1427 : List W := [a1, a2, a582, a46, a4, a5, a47]
def w1428 : List W := [a583, a1, a2, a46, a4, a5, a47]
def w1429 : List W := [a1, a2, a46, a584, a4, a5, a47]
def w1430 : List W := [a1, a585, a2, a46, a4, a5, a47]
def w1431 : List W := [a1, a2, a46, a4, a5, a47, a586]
def w1432 : List W := [a1, a2, a46, a4, a587, a5, a47]
def w1433 : List W := [a588, a1, a2, a46, a4, a5, a47]
def w1434 : List W := [a1, a2, a46, a4, a5, a47, a589]
def w1435 : List W := [a1, a590, a2, a46, a4, a5, a47]
def w1436 : List W := [a1, a2, a46, a4, a5, a591, a47]
def w1437 : List W := [a1, a27, a46, a4, a5, a47, a30]
def w1438 : List W := [a1, a27, a31, a46, a4, a5, a47]
def w1439 : List W := [a1, a27, a46, a4, a5, a47, a297]
def w1440 : List W := [a1, a27, a298, a46, a4, a5, a47]
def w1441 : List W := [a1, a27, a2, a46, a4, a5, a83]
def w1442 : List W := [a84, a1, a27, a2, a46, a4, a5]
def w1443 : List W := [a2, a46, a4, a5, a592, a47]
def w1444 : List W := [a1, a2, a46, a4, a5, a592, a47]
def w1445 : List W := [a2, a46, a301, a4, a5, a592, a47]
def w1446 : List W := [a593, a2, a46, a4, a5, a47]
def w1447 : List W := [a593, a1, a2, a46, a4, a5, a47]
def w1448 : List W := [a593, a2, a46, a301, a4, a5, a47]
def w1449 : List W := [a1, a46, a4, a5, a47, a594]
def w1450 : List W := [a1, a2, a46, a4, a5, a47, a594]
def w1451 : List W := [a1, a46, a301, a4, a5, a47, a594]
def w1452 : List W := [a1, a595, a46, a4, a5, a47]
def w1453 : List W := [a1, a595, a2, a46, a4, a5, a47]
def w1454 : List W := [a1, a595, a46, a301, a4, a5, a47]
def w1455 : List W := [a296, a1, a2, a46, a301, a4, a5]
def w1456 : List W := [a1, a298, a2, a46, a301, a4, a5]
def w1457 : List W := [a1, a2, a46, a4, a5, a47, a596]
def w1458 : List W := [a1, a2, a597, a46, a4, a5, a47]
def w1459 : List W := [a1, a2, a46, a301, a4, a5, a47]
def w1460 : List W := [a303, a1, a2, a46, a301, a5, a47]
def w1461 : List W := [a303, a1, a2, a46, a4, a5, a47]
def w1462 : List W := [a1, a2, a46, a4, a598, a47]
def w1463 : List W := [a1, a2, a46, a301, a4, a598, a47]
def w1464 : List W := [a1, a2, a46, a4, a5, a598, a47]
def w1465 : List W := [a599, a1, a2, a46, a4, a47]
def w1466 : List W := [a599, a1, a2, a46, a301, a4, a47]
def w1467 : List W := [a599, a1, a2, a46, a4, a5, a47]
def w1468 : List W := [a1, a304, a2, a46, a301, a4, a5]
def w1469 : List W := [a1, a304, a2, a46, a4, a5, a47]
def w1470 : List W := [a1, a2, a46, a301, a5, a302]
def w1471 : List W := [a1, a2, a46, a301, a4, a5, a302]
def w1472 : List W := [a1, a2, a46, a301, a5, a47, a302]
def w1473 : List W := [a1, a2, a46, a301, a4, a5, a83]
def w1474 : List W := [a84, a1, a2, a46, a301, a4, a5]
def w1475 : List W := [a600, a1, a2, a46, a4, a5, a47]
def w1476 : List W := [a1, a2, a46, a4, a601, a5, a47]
def w1477 : List W := [a1, a2, a46, a4, a5, a302, a297]
def w1478 : List W := [a1, a2, a46, a4, a5, a299, a302]
def w1479 : List W := [a602, a1, a2, a46, a4, a5, a47]
def w1480 : List W := [a1, a2, a46, a4, a5, a47, a603]
def w1481 : List W := [a1, a604, a2, a46, a4, a5, a47]
def w1482 : List W := [a1, a2, a46, a4, a605, a5, a47]
def w1483 : List W := [a303, a1, a2, a46, a4, a5, a302]
def w1484 : List W := [a1, a304, a2, a46, a5, a47, a302]
def w1485 : List W := [a1, a2, a46, a4, a5, a47, a302]
def w1486 : List W := [a1, a2, a46, a4, a5, a83, a302]
def w1487 : List W := [a84, a1, a2, a46, a4, a5, a302]
def w1488 : List W := [a1, a2, a46, a4, a606, a5, a47]
def w1489 : List W := [a1, a607, a2, a46, a4, a5, a47]
def w1490 : List W := [a1, a608, a2, a46, a4, a5, a47]
def w1491 : List W := [a609, a1, a2, a46, a4, a5, a47]
def w1492 : List W := [a1, a2, a610, a46, a4, a5, a47]
def w1493 : List W := [a1, a611, a2, a46, a4, a5, a47]
def w1494 : List W := [a1, a2, a46, a612, a4, a5, a47]
def w1495 : List W := [a1, a2, a613, a46, a4, a5, a47]
def w1496 : List W := [a1, a2, a46, a4, a5, a614, a47]
def w1497 : List W := [a1, a2, a46, a4, a615, a5, a47]
def w1498 : List W := [a296, a303, a1, a2, a46, a4, a5]
def w1499 : List W := [a303, a1, a298, a2, a46, a4, a5]
def w1500 : List W := [a303, a1, a304, a2, a46, a5]
def w1501 : List W := [a303, a1, a304, a2, a46, a4, a5]
def w1502 : List W := [a303, a1, a304, a2, a46, a5, a47]
def w1503 : List W := [a303, a1, a2, a46, a4, a5, a83]
def w1504 : List W := [a303, a84, a1, a2, a46, a4, a5]
def w1505 : List W := [a1, a616, a2, a46, a4, a5, a47]
def w1506 : List W := [a617, a1, a2, a46, a4, a5, a47]
def w1507 : List W := [a1, a2, a46, a618, a4, a5, a47]
def w1508 : List W := [a1, a619, a2, a46, a4, a5, a47]
def w1509 : List W := [a1, a2, a46, a620, a4, a5, a47]
def w1510 : List W := [a1, a621, a2, a46, a4, a5, a47]
def w1511 : List W := [a1, a2, a46, a4, a5, a47, a622]
def w1512 : List W := [a1, a2, a46, a623, a4, a5, a47]
def w1513 : List W := [a1, a304, a2, a46, a4, a5, a297]
def w1514 : List W := [a1, a304, a2, a46, a4, a5, a299]
def w1515 : List W := [a1, a304, a2, a46, a4, a5, a83]
def w1516 : List W := [a84, a1, a304, a2, a46, a4, a5]
def w1517 : List W := [a1, a45, a2, a46, a4, a5, a47]
def w1518 : List W := [a624, a1, a2, a46, a4, a5, a47]
def w1519 : List W := [a29, a1, a2, a46, a4, a5, a47]
def w1520 : List W := [a29, a1, a31, a46, a4, a5, a47]
def w1521 : List W := [a1, a31, a2, a46, a4, a5, a47]
def w1522 : List W := [a1, a2, a46, a625, a4, a5, a47]
def w1523 : List W := [a1, a2, a50, a46, a4, a5, a47]
def w1524 : List W := [a1, a2, a46, a51, a5, a47]
def w1525 : List W := [a29, a1, a2, a46, a51, a5, a47]
def w1526 : List W := [a1, a2, a46, a4, a51, a5, a47]
def w1527 : List W := [a1, a2, a46, a53, a5, a47]
def w1528 : List W := [a29, a1, a2, a46, a53, a5, a47]
def w1529 : List W := [a1, a2, a46, a53, a4, a5, a47]
def w1530 : List W := [a29, a1, a2, a46, a4, a32, a47]
def w1531 : List W := [a1, a2, a46, a4, a32, a5, a47]
def w1532 : List W := [a626, a1, a2, a46, a4, a5, a47]
def w1533 : List W := [a1, a2, a46, a4, a5, a54]
def w1534 : List W := [a29, a1, a2, a46, a4, a5, a54]
def w1535 : List W := [a1, a2, a46, a4, a5, a47, a54]
def w1536 : List W := [a627, a1, a2, a46, a4, a5, a47]
def w1537 : List W := [a1, a2, a46, a4, a5, a55]
def w1538 : List W := [a29, a1, a2, a46, a4, a5, a55]
def w1539 : List W := [a1, a2, a46, a4, a5, a55, a47]
def w1540 : List W := [a29, a1, a2, a46, a4, a47, a30]
def w1541 : List W := [a29, a1, a46, a4, a5, a47, a30]
def w1542 : List W := [a29, a1, a2, a46, a4, a5, a83]
def w1543 : List W := [a29, a84, a1, a2, a46, a4, a5]
def w1544 : List W := [a59, a2, a46, a4, a5, a47]
def w1545 : List W := [a59, a1, a2, a46, a4, a5, a47]
def w1546 : List W := [a59, a2, a46, a4, a5, a47, a30]
def w1547 : List W := [a2, a46, a4, a5, a47, a61]
def w1548 : List W := [a1, a2, a46, a4, a5, a47, a61]
def w1549 : List W := [a2, a46, a4, a5, a47, a61, a30]
def w1550 : List W := [a1, a31, a2, a46, a4, a47, a30]
def w1551 : List W := [a1, a46, a4, a32, a5, a47, a30]
def w1552 : List W := [a1, a2, a46, a4, a5, a47, a30]
def w1553 : List W := [a1, a2, a628, a46, a4, a5, a47]
def w1554 : List W := [a1, a2, a46, a629, a4, a5, a47]
def w1555 : List W := [a1, a2, a46, a630, a4, a5, a47]
def w1556 : List W := [a1, a2, a631, a46, a4, a5, a47]
def w1557 : List W := [a1, a2, a46, a4, a5, a83, a30]
def w1558 : List W := [a84, a1, a2, a46, a4, a5, a30]
def w1559 : List W := [a1, a2, a46, a4, a632, a5, a47]
def w1560 : List W := [a1, a2, a46, a4, a5, a47, a633]
def w1561 : List W := [a634, a1, a2, a46, a4, a5, a47]
def w1562 : List W := [a1, a2, a635, a46, a4, a5, a47]
def w1563 : List W := [a1, a2, a46, a4, a5, a47, a636]
def w1564 : List W := [a637, a1, a2, a46, a4, a5, a47]
def w1565 : List W := [a1, a31, a46, a4, a32, a47]
def w1566 : List W := [a1, a31, a2, a46, a4, a32, a47]
def w1567 : List W := [a1, a31, a46, a4, a32, a5, a47]
def w1568 : List W := [a1, a2, a46, a4, a5, a47, a638]
def w1569 : List W := [a1, a2, a639, a46, a4, a5, a47]
def w1570 : List W := [a1, a2, a46, a4, a5, a640, a47]
def w1571 : List W := [a641, a1, a2, a46, a4, a5, a47]
def w1572 : List W := [a1, a2, a46, a4, a642, a5, a47]
def w1573 : List W := [a1, a2, a46, a4, a5, a643]
def w1574 : List W := [a1, a2, a46, a4, a32, a5, a643]
def w1575 : List W := [a1, a2, a46, a4, a5, a47, a643]
def w1576 : List W := [a644, a1, a2, a46, a4, a5, a47]
def w1577 : List W := [a645, a1, a2, a46, a4, a5]
def w1578 : List W := [a645, a1, a2, a46, a4, a32, a5]
def w1579 : List W := [a645, a1, a2, a46, a4, a5, a47]
def w1580 : List W := [a1, a2, a46, a4, a32, a5, a83]
def w1581 : List W := [a84, a1, a2, a46, a4, a32, a5]
def w1582 : List W := [a1, a2, a646, a46, a4, a5, a47]
def w1583 : List W := [a647, a1, a2, a46, a4, a5, a47]
def w1584 : List W := [a1, a2, a46, a648, a4, a5, a47]
def w1585 : List W := [a1, a649, a2, a46, a4, a5, a47]
def w1586 : List W := [a1, a2, a46, a4, a5, a47, a650]
def w1587 : List W := [a1, a2, a46, a651, a4, a5, a47]
def w1588 : List W := [a652, a1, a2, a46, a4, a5, a47]
def w1589 : List W := [a1, a2, a46, a4, a5, a47, a653]
def w1590 : List W := [a1, a654, a2, a46, a4, a5, a47]
def w1591 : List W := [a1, a2, a46, a4, a5, a655, a47]
def w1592 : List W := [a1, a31, a2, a46, a4, a5, a83]
def w1593 : List W := [a84, a1, a31, a2, a46, a4, a5]
def w1594 : List W := [a1, a2, a46, a4, a5, a47, a656]
def w1595 : List W := [a657, a1, a2, a46, a4, a5, a47]
def w1596 : List W := [a1, a2, a46, a4, a5, a47, a658]
def w1597 : List W := [a1, a659, a2, a46, a4, a5, a47]
def w1598 : List W := [a1, a2, a46, a4, a5, a47, a660]
def w1599 : List W := [a1, a2, a661, a46, a4, a5, a47]
def w1600 : List W := [a1, a2, a46, a4, a5, a662, a47]
def w1601 : List W := [a663, a1, a2, a46, a4, a5, a47]
def w1602 : List W := [a1, a2, a46, a4, a305, a5, a47]
def w1603 : List W := [a306, a1, a2, a46, a4, a305, a47]
def w1604 : List W := [a306, a1, a2, a46, a4, a5, a47]
def w1605 : List W := [a84, a1, a2, a46, a4, a5]
def w1606 : List W := [a84, a1, a2, a46, a4, a305, a5]
def w1607 : List W := [a84, a1, a2, a46, a4, a5, a47]
def w1608 : List W := [a1, a2, a46, a4, a305, a83]
def w1609 : List W := [a1, a2, a46, a4, a305, a5, a83]
def w1610 : List W := [a1, a2, a46, a4, a305, a47, a83]
def w1611 : List W := [a664, a1, a2, a46, a4, a5]
def w1612 : List W := [a664, a1, a2, a46, a4, a5, a83]
def w1613 : List W := [a1, a2, a46, a4, a5, a83, a217]
def w1614 : List W := [a229, a1, a2, a46, a4, a5, a83]
def w1615 : List W := [a1, a2, a46, a4, a5, a665, a83]
def w1616 : List W := [a666, a1, a2, a46, a4, a5, a83]
def w1617 : List W := [a1, a2, a46, a4, a5, a83, a633]
def w1618 : List W := [a1, a654, a2, a46, a4, a5, a83]
def w1619 : List W := [a1, a2, a46, a4, a5, a667, a83]
def w1620 : List W := [a1, a668, a2, a46, a4, a5, a83]
def w1621 : List W := [a1, a2, a46, a4, a5, a83, a407]
def w1622 : List W := [a1, a420, a2, a46, a4, a5, a83]
def w1623 : List W := [a1, a2, a46, a669, a4, a5]
def w1624 : List W := [a1, a2, a46, a669, a4, a5, a83]
def w1625 : List W := [a1, a2, a46, a670, a4, a5, a83]
def w1626 : List W := [a1, a2, a46, a4, a5, a83, a526]
def w1627 : List W := [a539, a1, a2, a46, a4, a5, a83]
def w1628 : List W := [a1, a671, a2, a46, a4, a5, a83]
def w1629 : List W := [a1, a2, a46, a4, a5, a83]
def w1630 : List W := [a1, a2, a46, a4, a5, a5, a83]
def w1631 : List W := [a1, a2, a46, a4, a5, a83, a83]
def w1632 : List W := [a65, a1, a2, a46, a4, a5, a83]
def w1633 : List W := [a84, a1, a2, a46, a4, a83]
def w1634 : List W := [a84, a1, a2, a46, a4, a5, a83]
def w1635 : List W := [a664, a1, a2, a46, a4, a5, a47]
def w1636 : List W := [a1, a2, a46, a4, a5, a665, a47]
def w1637 : List W := [a296, a1, a2, a46, a4, a5, a83]
def w1638 : List W := [a1, a2, a46, a4, a5, a83, a297]
def w1639 : List W := [a1, a298, a2, a46, a4, a5, a83]
def w1640 : List W := [a1, a2, a46, a4, a5, a299, a83]
def w1641 : List W := [a666, a1, a2, a46, a4, a5, a47]
def w1642 : List W := [a1, a2, a46, a4, a5, a47, a667]
def w1643 : List W := [a1, a668, a2, a46, a4, a5, a47]
def w1644 : List W := [a1, a2, a46, a669, a4, a5, a47]
def w1645 : List W := [a1, a2, a46, a670, a4, a5, a47]
def w1646 : List W := [a1, a671, a2, a46, a4, a5, a47]
def w1647 : List W := [a306, a1, a2, a46, a4, a5, a83]
def w1648 : List W := [a84, a1, a2, a46, a4, a47, a83]
def w1649 : List W := [a1, a2, a46, a4, a5, a47, a83]
def w1650 : List W := [a1, a672, a2, a46, a4, a5, a47]
def w1651 : List W := [a673, a1, a2, a46, a4, a5, a47]
def w1652 : List W := [a1, a2, a674, a46, a4, a5, a47]
def w1653 : List W := [a1, a675, a2, a46, a4, a5, a47]
def w1654 : List W := [a1, a2, a46, a676, a4, a5, a47]
def w1655 : List W := [a1, a2, a677, a46, a4, a5, a47]
def w1656 : List W := [a1, a2, a46, a678, a5, a47]
def w1657 : List W := [a306, a1, a2, a46, a678, a5, a47]
def w1658 : List W := [a1, a2, a46, a4, a678, a5, a47]
def w1659 : List W := [a1, a2, a46, a679, a5, a47]
def w1660 : List W := [a306, a1, a2, a46, a679, a5, a47]
def w1661 : List W := [a1, a2, a46, a679, a4, a5, a47]
def w1662 : List W := [a306, a84, a1, a2, a46, a4]
def w1663 : List W := [a306, a84, a1, a2, a46, a4, a5]
def w1664 : List W := [a306, a84, a1, a2, a46, a4, a47]
def w1665 : List W := [a227, a84, a1, a2, a46, a4, a5]
def w1666 : List W := [a84, a1, a680, a2, a46, a4, a5]
def w1667 : List W := [a218, a84, a1, a2, a46, a4, a5]
def w1668 : List W := [a681, a1, a2, a46, a4, a5]
def w1669 : List W := [a681, a84, a1, a2, a46, a4, a5]
def w1670 : List W := [a652, a84, a1, a2, a46, a4, a5]
def w1671 : List W := [a84, a1, a2, a682, a46, a4, a5]
def w1672 : List W := [a634, a84, a1, a2, a46, a4, a5]
def w1673 : List W := [a84, a1, a683, a2, a46, a4, a5]
def w1674 : List W := [a418, a84, a1, a2, a46, a4, a5]
def w1675 : List W := [a1, a2, a46, a684, a4, a5]
def w1676 : List W := [a84, a1, a2, a46, a684, a4, a5]
def w1677 : List W := [a408, a84, a1, a2, a46, a4, a5]
def w1678 : List W := [a84, a1, a2, a685, a46, a4, a5]
def w1679 : List W := [a537, a84, a1, a2, a46, a4, a5]
def w1680 : List W := [a84, a1, a2, a46, a4, a5, a686]
def w1681 : List W := [a528, a84, a1, a2, a46, a4, a5]
def w1682 : List W := [a84, a1, a2, a46, a687, a4, a5]
def w1683 : List W := [a65, a84, a1, a2, a46, a4, a5]
def w1684 : List W := [a84, a84, a1, a2, a46, a4, a5]
def w1685 : List W := [a84, a1, a2, a46, a4, a5, a5]
def w1686 : List W := [a1, a680, a2, a46, a4, a5, a47]
def w1687 : List W := [a681, a1, a2, a46, a4, a5, a47]
def w1688 : List W := [a1, a2, a682, a46, a4, a5, a47]
def w1689 : List W := [a1, a683, a2, a46, a4, a5, a47]
def w1690 : List W := [a1, a2, a46, a684, a4, a5, a47]
def w1691 : List W := [a1, a2, a685, a46, a4, a5, a47]
def w1692 : List W := [a1, a2, a46, a4, a5, a686, a47]
def w1693 : List W := [a1, a2, a46, a687, a4, a5, a47]
def w1694 : List W := [a296, a84, a1, a2, a46, a4, a5]
def w1695 : List W := [a84, a1, a2, a46, a4, a5, a297]
def w1696 : List W := [a84, a1, a298, a2, a46, a4, a5]
def w1697 : List W := [a84, a1, a2, a46, a4, a5, a299]
def w1698 : List W := [a1, a688, a2, a46, a4, a5, a47]
def w1699 : List W := [a689, a1, a2, a46, a4, a5, a47]
def w1700 : List W := [a296, a1, a2, a46, a4, a5, a47]
def w1701 : List W := [a296, a1, a298, a46, a4, a5, a47]
def w1702 : List W := [a1, a298, a2, a46, a4, a5, a47]
def w1703 : List W := [a1, a2, a46, a690, a4, a5, a47]
def w1704 : List W := [a1, a2, a691, a46, a4, a5, a47]
def w1705 : List W := [a1, a2, a46, a4, a692, a5, a47]
def w1706 : List W := [a1, a2, a46, a693, a4, a5, a47]
def w1707 : List W := [a1, a2, a46, a4, a5, a694, a47]
def w1708 : List W := [a1, a2, a46, a4, a695, a5, a47]
def w1709 : List W := [a296, a1, a2, a46, a4, a5, a299]
def w1710 : List W := [a1, a2, a46, a4, a5, a299, a47]
def w1711 : List W := [a296, a1, a46, a4, a5, a297]
def w1712 : List W := [a296, a1, a2, a46, a4, a5, a297]
def w1713 : List W := [a296, a1, a46, a4, a5, a47, a297]
def w1714 : List W := [a696, a1, a2, a46, a4, a5, a47]
def w1715 : List W := [a1, a2, a46, a4, a5, a47, a697]
def w1716 : List W := [a1, a298, a2, a46, a4, a5, a297]
def w1717 : List W := [a1, a46, a4, a5, a299, a47, a297]
def w1718 : List W := [a1, a2, a46, a4, a5, a47, a297]
def w1719 : List W := [a1, a2, a698, a46, a4, a5, a47]
def w1720 : List W := [a1, a2, a46, a699, a4, a5, a47]
def w1721 : List W := [a1, a2, a46, a700, a4, a5, a47]
def w1722 : List W := [a1, a2, a46, a701, a4, a5, a47]
def w1723 : List W := [a1, a2, a46, a4, a702, a5, a47]
def w1724 : List W := [a1, a2, a703, a46, a4, a5, a47]
def w1725 : List W := [a1, a2, a704, a46, a4, a5, a47]
def w1726 : List W := [a705, a1, a2, a46, a4, a5, a47]
def w1727 : List W := [a1, a2, a46, a706, a4, a5, a47]
def w1728 : List W := [a1, a707, a2, a46, a4, a5, a47]
def w1729 : List W := [a1, a2, a46, a4, a5, a47, a708]
def w1730 : List W := [a1, a2, a46, a709, a4, a5, a47]
def w1731 : List W := [a1, a2, a46, a4, a5, a47, a710]
def w1732 : List W := [a1, a2, a46, a4, a711, a5, a47]
def w1733 : List W := [a1, a298, a46, a4, a5, a299]
def w1734 : List W := [a1, a298, a2, a46, a4, a5, a299]
def w1735 : List W := [a1, a298, a46, a4, a5, a299, a47]
def w1736 : List W := [a1, a2, a46, a4, a5, a47, a712]
def w1737 : List W := [a713, a1, a2, a46, a4, a5, a47]
def w1738 : List W := [a1, a2, a46, a4, a5, a47, a714]
def w1739 : List W := [a1, a715, a2, a46, a4, a5, a47]
def w1740 : List W := [a1, a2, a46, a4, a5, a47, a716]
def w1741 : List W := [a717, a1, a2, a46, a4, a5, a47]
def w1742 : List W := [a1, a2, a46, a4, a5, a47, a718]
def w1743 : List W := [a719, a1, a2, a46, a4, a5, a47]
def w1744 : List W := [a1, a46, a4, a5, a2, a47]

theorem s0 : optimized 5 0 w0 = false := by
  decide +kernel

theorem s1 : optimized 5 0 w1 = false := by
  decide +kernel

theorem s2 : optimized 5 0 w2 = false := by
  decide +kernel

theorem s3 : optimized 5 0 w3 = false := by
  decide +kernel

theorem s4 : optimized 5 0 w4 = false := by
  decide +kernel

theorem s5 : optimized 5 0 w5 = false := by
  decide +kernel

theorem s6 : optimized 5 0 w6 = false := by
  decide +kernel

theorem s7 : optimized 5 0 w7 = false := by
  decide +kernel

theorem s8 : optimized 5 0 w8 = false := by
  decide +kernel

theorem s9 : optimized 5 0 w9 = false := by
  decide +kernel

theorem s10 : optimized 5 0 w10 = false := by
  decide +kernel

theorem s11 : optimized 5 0 w11 = false := by
  decide +kernel

theorem s12 : optimized 5 0 w12 = false := by
  decide +kernel

theorem s13 : optimized 5 0 w13 = false := by
  decide +kernel

theorem s14 : optimized 5 0 w14 = false := by
  decide +kernel

theorem s15 : optimized 5 0 w15 = false := by
  decide +kernel

theorem s16 : optimized 5 0 w16 = false := by
  decide +kernel

theorem s17 : optimized 5 0 w17 = false := by
  decide +kernel

theorem s18 : optimized 5 0 w18 = false := by
  decide +kernel

theorem s19 : optimized 5 0 w19 = false := by
  decide +kernel

theorem s20 : optimized 5 0 w20 = false := by
  decide +kernel

theorem s21 : optimized 5 0 w21 = false := by
  decide +kernel

theorem s22 : optimized 5 0 w22 = false := by
  decide +kernel

theorem s23 : optimized 5 0 w23 = false := by
  decide +kernel

theorem s24 : optimized 5 0 w24 = false := by
  decide +kernel

theorem s25 : optimized 5 0 w25 = false := by
  decide +kernel

theorem s26 : optimized 5 0 w26 = false := by
  decide +kernel

theorem s27 : optimized 5 0 w27 = false := by
  decide +kernel

theorem s28 : optimized 5 0 w28 = false := by
  decide +kernel

theorem s29 : optimized 5 0 w29 = false := by
  decide +kernel

theorem s30 : optimized 5 0 w30 = false := by
  decide +kernel

theorem s31 : optimized 5 0 w31 = false := by
  decide +kernel

theorem s32 : optimized 5 0 w32 = false := by
  decide +kernel

theorem s33 : optimized 5 0 w33 = false := by
  decide +kernel

theorem s34 : optimized 5 0 w34 = false := by
  decide +kernel

theorem s35 : optimized 5 0 w35 = false := by
  decide +kernel

theorem s36 : optimized 5 0 w36 = false := by
  decide +kernel

theorem s37 : optimized 5 0 w37 = false := by
  decide +kernel

theorem s38 : optimized 5 0 w38 = false := by
  decide +kernel

theorem s39 : optimized 5 0 w39 = false := by
  decide +kernel

theorem s40 : optimized 5 0 w40 = false := by
  decide +kernel

theorem s41 : optimized 5 0 w41 = false := by
  decide +kernel

theorem s42 : optimized 5 0 w42 = false := by
  decide +kernel

theorem s43 : optimized 5 0 w43 = false := by
  decide +kernel

theorem s44 : optimized 5 1 w44 = false := by
  decide +kernel

theorem s45 : optimized 5 0 w45 = false := by
  decide +kernel

theorem s46 : optimized 5 0 w46 = false := by
  decide +kernel

theorem s47 : optimized 5 0 w47 = false := by
  decide +kernel

theorem s48 : optimized 5 0 w48 = false := by
  decide +kernel

theorem s49 : optimized 5 0 w49 = false := by
  decide +kernel

theorem s50 : optimized 5 0 w50 = false := by
  decide +kernel

theorem s51 : optimized 5 0 w51 = false := by
  decide +kernel

theorem s52 : optimized 5 1 w52 = false := by
  decide +kernel

theorem s53 : optimized 5 0 w53 = false := by
  decide +kernel

theorem s54 : optimized 5 0 w54 = false := by
  decide +kernel

theorem s55 : optimized 5 0 w55 = false := by
  decide +kernel

theorem s56 : optimized 5 0 w56 = false := by
  decide +kernel

theorem s57 : optimized 5 1 w57 = false := by
  decide +kernel

theorem s58 : optimized 5 0 w58 = false := by
  decide +kernel

theorem s59 : optimized 5 0 w59 = false := by
  decide +kernel

theorem s60 : optimized 5 0 w60 = false := by
  decide +kernel

theorem s61 : optimized 5 0 w61 = false := by
  decide +kernel

theorem s62 : optimized 5 0 w62 = false := by
  decide +kernel

theorem s63 : optimized 5 0 w63 = false := by
  decide +kernel

theorem s64 : optimized 6 0 w64 = false := by
  decide +kernel

theorem s65 : optimized 6 1 w65 = false := by
  decide +kernel

theorem s66 : optimized 6 0 w66 = false := by
  decide +kernel

theorem s67 : optimized 6 0 w67 = false := by
  decide +kernel

theorem s68 : optimized 6 0 w68 = false := by
  decide +kernel

theorem s69 : optimized 6 0 w69 = false := by
  decide +kernel

theorem s70 : optimized 6 0 w70 = false := by
  decide +kernel

theorem s71 : optimized 6 0 w71 = false := by
  decide +kernel

theorem s72 : optimized 6 0 w72 = false := by
  decide +kernel

theorem s73 : optimized 6 0 w73 = false := by
  decide +kernel

theorem s74 : optimized 6 0 w74 = false := by
  decide +kernel

theorem s75 : optimized 6 0 w75 = false := by
  decide +kernel

theorem s76 : optimized 6 0 w76 = false := by
  decide +kernel

theorem s77 : optimized 6 0 w77 = false := by
  decide +kernel

theorem s78 : optimized 6 0 w78 = false := by
  decide +kernel

theorem s79 : optimized 6 0 w79 = false := by
  decide +kernel

theorem s80 : optimized 6 0 w80 = false := by
  decide +kernel

theorem s81 : optimized 6 0 w81 = false := by
  decide +kernel

theorem s82 : optimized 6 1 w82 = false := by
  decide +kernel

theorem s83 : optimized 6 0 w83 = false := by
  decide +kernel

theorem s84 : optimized 6 0 w84 = false := by
  decide +kernel

theorem s85 : optimized 6 0 w85 = false := by
  decide +kernel

theorem s86 : optimized 6 1 w86 = false := by
  decide +kernel

theorem s87 : optimized 6 0 w87 = false := by
  decide +kernel

theorem s88 : optimized 6 0 w88 = false := by
  decide +kernel

theorem s89 : optimized 6 0 w89 = false := by
  decide +kernel

theorem s90 : optimized 6 1 w90 = false := by
  decide +kernel

theorem s91 : optimized 6 0 w91 = false := by
  decide +kernel

theorem s92 : optimized 6 0 w92 = false := by
  decide +kernel

theorem s93 : optimized 6 0 w93 = false := by
  decide +kernel

theorem s94 : optimized 6 1 w94 = false := by
  decide +kernel

theorem s95 : optimized 6 0 w95 = false := by
  decide +kernel

theorem s96 : optimized 6 0 w96 = false := by
  decide +kernel

theorem s97 : optimized 6 1 w97 = false := by
  decide +kernel

theorem s98 : optimized 6 0 w98 = false := by
  decide +kernel

theorem s99 : optimized 6 0 w99 = false := by
  decide +kernel

theorem s100 : optimized 6 0 w100 = false := by
  decide +kernel

theorem s101 : optimized 6 0 w101 = false := by
  decide +kernel

theorem s102 : optimized 6 0 w102 = false := by
  decide +kernel

theorem s103 : optimized 6 0 w103 = false := by
  decide +kernel

theorem s104 : optimized 6 0 w104 = false := by
  decide +kernel

theorem s105 : optimized 6 0 w105 = false := by
  decide +kernel

theorem s106 : optimized 6 0 w106 = false := by
  decide +kernel

theorem s107 : optimized 6 0 w107 = false := by
  decide +kernel

theorem s108 : optimized 6 0 w108 = false := by
  decide +kernel

theorem s109 : optimized 6 0 w109 = false := by
  decide +kernel

theorem s110 : optimized 6 0 w110 = false := by
  decide +kernel

theorem s111 : optimized 6 0 w111 = false := by
  decide +kernel

theorem s112 : optimized 6 0 w112 = false := by
  decide +kernel

theorem s113 : optimized 6 1 w113 = false := by
  decide +kernel

theorem s114 : optimized 6 0 w114 = false := by
  decide +kernel

theorem s115 : optimized 6 0 w115 = false := by
  decide +kernel

theorem s116 : optimized 6 0 w116 = false := by
  decide +kernel

theorem s117 : optimized 6 0 w117 = false := by
  decide +kernel

theorem s118 : optimized 6 1 w118 = false := by
  decide +kernel

theorem s119 : optimized 6 0 w119 = false := by
  decide +kernel

theorem s120 : optimized 6 0 w120 = false := by
  decide +kernel

theorem s121 : optimized 6 0 w121 = false := by
  decide +kernel

theorem s122 : optimized 6 0 w122 = false := by
  decide +kernel

theorem s123 : optimized 6 1 w123 = false := by
  decide +kernel

theorem s124 : optimized 6 0 w124 = false := by
  decide +kernel

theorem s125 : optimized 6 0 w125 = false := by
  decide +kernel

theorem s126 : optimized 6 0 w126 = false := by
  decide +kernel

theorem s127 : optimized 6 0 w127 = false := by
  decide +kernel

theorem s128 : optimized 6 1 w128 = false := by
  decide +kernel

theorem s129 : optimized 6 0 w129 = false := by
  decide +kernel

theorem s130 : optimized 6 0 w130 = false := by
  decide +kernel

theorem s131 : optimized 6 0 w131 = false := by
  decide +kernel

theorem s132 : optimized 6 1 w132 = false := by
  decide +kernel

theorem s133 : optimized 6 0 w133 = false := by
  decide +kernel

theorem s134 : optimized 6 0 w134 = false := by
  decide +kernel

theorem s135 : optimized 6 0 w135 = false := by
  decide +kernel

theorem s136 : optimized 6 1 w136 = false := by
  decide +kernel

theorem s137 : optimized 6 0 w137 = false := by
  decide +kernel

theorem s138 : optimized 6 0 w138 = false := by
  decide +kernel

theorem s139 : optimized 6 0 w139 = false := by
  decide +kernel

theorem s140 : optimized 6 1 w140 = false := by
  decide +kernel

theorem s141 : optimized 6 0 w141 = false := by
  decide +kernel

theorem s142 : optimized 6 0 w142 = false := by
  decide +kernel

theorem s143 : optimized 6 0 w143 = false := by
  decide +kernel

theorem s144 : optimized 6 1 w144 = false := by
  decide +kernel

theorem s145 : optimized 6 0 w145 = false := by
  decide +kernel

theorem s146 : optimized 6 0 w146 = false := by
  decide +kernel

theorem s147 : optimized 6 0 w147 = false := by
  decide +kernel

theorem s148 : optimized 6 1 w148 = false := by
  decide +kernel

theorem s149 : optimized 6 0 w149 = false := by
  decide +kernel

theorem s150 : optimized 6 0 w150 = false := by
  decide +kernel

theorem s151 : optimized 6 0 w151 = false := by
  decide +kernel

theorem s152 : optimized 6 0 w152 = false := by
  decide +kernel

theorem s153 : optimized 6 0 w153 = false := by
  decide +kernel

theorem s154 : optimized 6 0 w154 = false := by
  decide +kernel

theorem s155 : optimized 6 0 w155 = false := by
  decide +kernel

theorem s156 : optimized 6 0 w156 = false := by
  decide +kernel

theorem s157 : optimized 6 0 w157 = false := by
  decide +kernel

theorem s158 : optimized 6 0 w158 = false := by
  decide +kernel

theorem s159 : optimized 6 0 w159 = false := by
  decide +kernel

theorem s160 : optimized 6 0 w160 = false := by
  decide +kernel

theorem s161 : optimized 6 0 w161 = false := by
  decide +kernel

theorem s162 : optimized 6 0 w162 = false := by
  decide +kernel

theorem s163 : optimized 6 0 w163 = false := by
  decide +kernel

theorem s164 : optimized 6 0 w164 = false := by
  decide +kernel

theorem s165 : optimized 6 0 w165 = false := by
  decide +kernel

theorem s166 : optimized 6 1 w166 = false := by
  decide +kernel

theorem s167 : optimized 6 0 w167 = false := by
  decide +kernel

theorem s168 : optimized 6 0 w168 = false := by
  decide +kernel

theorem s169 : optimized 6 0 w169 = false := by
  decide +kernel

theorem s170 : optimized 6 1 w170 = false := by
  decide +kernel

theorem s171 : optimized 6 0 w171 = false := by
  decide +kernel

theorem s172 : optimized 6 0 w172 = false := by
  decide +kernel

theorem s173 : optimized 6 0 w173 = false := by
  decide +kernel

theorem s174 : optimized 6 1 w174 = false := by
  decide +kernel

theorem s175 : optimized 6 0 w175 = false := by
  decide +kernel

theorem s176 : optimized 6 0 w176 = false := by
  decide +kernel

theorem s177 : optimized 6 0 w177 = false := by
  decide +kernel

theorem s178 : optimized 6 0 w178 = false := by
  decide +kernel

theorem s179 : optimized 6 0 w179 = false := by
  decide +kernel

theorem s180 : optimized 6 0 w180 = false := by
  decide +kernel

theorem s181 : optimized 6 0 w181 = false := by
  decide +kernel

theorem s182 : optimized 6 0 w182 = false := by
  decide +kernel

theorem s183 : optimized 6 0 w183 = false := by
  decide +kernel

theorem s184 : optimized 6 0 w184 = false := by
  decide +kernel

theorem s185 : optimized 6 0 w185 = false := by
  decide +kernel

theorem s186 : optimized 6 0 w186 = false := by
  decide +kernel

theorem s187 : optimized 6 0 w187 = false := by
  decide +kernel

theorem s188 : optimized 6 0 w188 = false := by
  decide +kernel

theorem s189 : optimized 6 0 w189 = false := by
  decide +kernel

theorem s190 : optimized 6 0 w190 = false := by
  decide +kernel

theorem s191 : optimized 6 0 w191 = false := by
  decide +kernel

theorem s192 : optimized 6 0 w192 = false := by
  decide +kernel

theorem s193 : optimized 6 0 w193 = false := by
  decide +kernel

theorem s194 : optimized 6 0 w194 = false := by
  decide +kernel

theorem s195 : optimized 6 0 w195 = false := by
  decide +kernel

theorem s196 : optimized 6 0 w196 = false := by
  decide +kernel

theorem s197 : optimized 6 0 w197 = false := by
  decide +kernel

theorem s198 : optimized 6 0 w198 = false := by
  decide +kernel

theorem s199 : optimized 6 0 w199 = false := by
  decide +kernel

theorem s200 : optimized 6 1 w200 = false := by
  decide +kernel

theorem s201 : optimized 6 0 w201 = false := by
  decide +kernel

theorem s202 : optimized 6 0 w202 = false := by
  decide +kernel

theorem s203 : optimized 6 0 w203 = false := by
  decide +kernel

theorem s204 : optimized 6 1 w204 = false := by
  decide +kernel

theorem s205 : optimized 6 0 w205 = false := by
  decide +kernel

theorem s206 : optimized 6 0 w206 = false := by
  decide +kernel

theorem s207 : optimized 6 0 w207 = false := by
  decide +kernel

theorem s208 : optimized 6 0 w208 = false := by
  decide +kernel

theorem s209 : optimized 6 1 w209 = false := by
  decide +kernel

theorem s210 : optimized 6 0 w210 = false := by
  decide +kernel

theorem s211 : optimized 6 0 w211 = false := by
  decide +kernel

theorem s212 : optimized 6 0 w212 = false := by
  decide +kernel

theorem s213 : optimized 6 0 w213 = false := by
  decide +kernel

theorem s214 : optimized 6 0 w214 = false := by
  decide +kernel

theorem s215 : optimized 6 0 w215 = false := by
  decide +kernel

theorem s216 : optimized 6 0 w216 = false := by
  decide +kernel

theorem s217 : optimized 6 0 w217 = false := by
  decide +kernel

theorem s218 : optimized 6 0 w218 = false := by
  decide +kernel

theorem s219 : optimized 6 0 w219 = false := by
  decide +kernel

theorem s220 : optimized 6 0 w220 = false := by
  decide +kernel

theorem s221 : optimized 6 0 w221 = false := by
  decide +kernel

theorem s222 : optimized 6 0 w222 = false := by
  decide +kernel

theorem s223 : optimized 6 0 w223 = false := by
  decide +kernel

theorem s224 : optimized 6 0 w224 = false := by
  decide +kernel

theorem s225 : optimized 6 0 w225 = false := by
  decide +kernel

theorem s226 : optimized 6 0 w226 = false := by
  decide +kernel

theorem s227 : optimized 6 0 w227 = false := by
  decide +kernel

theorem s228 : optimized 6 0 w228 = false := by
  decide +kernel

theorem s229 : optimized 6 0 w229 = false := by
  decide +kernel

theorem s230 : optimized 6 0 w230 = false := by
  decide +kernel

theorem s231 : optimized 6 0 w231 = false := by
  decide +kernel

theorem s232 : optimized 6 0 w232 = false := by
  decide +kernel

theorem s233 : optimized 6 0 w233 = false := by
  decide +kernel

theorem s234 : optimized 6 0 w234 = false := by
  decide +kernel

theorem s235 : optimized 6 0 w235 = false := by
  decide +kernel

theorem s236 : optimized 6 1 w236 = false := by
  decide +kernel

theorem s237 : optimized 6 0 w237 = false := by
  decide +kernel

theorem s238 : optimized 6 0 w238 = false := by
  decide +kernel

theorem s239 : optimized 6 0 w239 = false := by
  decide +kernel

theorem s240 : optimized 6 0 w240 = false := by
  decide +kernel

theorem s241 : optimized 6 0 w241 = false := by
  decide +kernel

theorem s242 : optimized 6 0 w242 = false := by
  decide +kernel

theorem s243 : optimized 6 0 w243 = false := by
  decide +kernel

theorem s244 : optimized 6 0 w244 = false := by
  decide +kernel

theorem s245 : optimized 6 0 w245 = false := by
  decide +kernel

theorem s246 : optimized 6 0 w246 = false := by
  decide +kernel

theorem s247 : optimized 6 0 w247 = false := by
  decide +kernel

theorem s248 : optimized 6 0 w248 = false := by
  decide +kernel

theorem s249 : optimized 6 0 w249 = false := by
  decide +kernel

theorem s250 : optimized 6 0 w250 = false := by
  decide +kernel

theorem s251 : optimized 6 0 w251 = false := by
  decide +kernel

theorem s252 : optimized 6 0 w252 = false := by
  decide +kernel

theorem s253 : optimized 6 0 w253 = false := by
  decide +kernel

theorem s254 : optimized 6 1 w254 = false := by
  decide +kernel

theorem s255 : optimized 6 0 w255 = false := by
  decide +kernel

theorem s256 : optimized 6 0 w256 = false := by
  decide +kernel

theorem s257 : optimized 6 0 w257 = false := by
  decide +kernel

theorem s258 : optimized 6 0 w258 = false := by
  decide +kernel

theorem s259 : optimized 6 0 w259 = false := by
  decide +kernel

theorem s260 : optimized 6 0 w260 = false := by
  decide +kernel

theorem s261 : optimized 6 0 w261 = false := by
  decide +kernel

theorem s262 : optimized 6 0 w262 = false := by
  decide +kernel

theorem s263 : optimized 6 0 w263 = false := by
  decide +kernel

theorem s264 : optimized 6 0 w264 = false := by
  decide +kernel

theorem s265 : optimized 6 0 w265 = false := by
  decide +kernel

theorem s266 : optimized 6 0 w266 = false := by
  decide +kernel

theorem s267 : optimized 6 0 w267 = false := by
  decide +kernel

theorem s268 : optimized 6 0 w268 = false := by
  decide +kernel

theorem s269 : optimized 6 0 w269 = false := by
  decide +kernel

theorem s270 : optimized 6 0 w270 = false := by
  decide +kernel

theorem s271 : optimized 6 0 w271 = false := by
  decide +kernel

theorem s272 : optimized 6 0 w272 = false := by
  decide +kernel

theorem s273 : optimized 6 1 w273 = false := by
  decide +kernel

theorem s274 : optimized 6 0 w274 = false := by
  decide +kernel

theorem s275 : optimized 6 0 w275 = false := by
  decide +kernel

theorem s276 : optimized 6 0 w276 = false := by
  decide +kernel

theorem s277 : optimized 6 1 w277 = false := by
  decide +kernel

theorem s278 : optimized 6 0 w278 = false := by
  decide +kernel

theorem s279 : optimized 6 0 w279 = false := by
  decide +kernel

theorem s280 : optimized 6 0 w280 = false := by
  decide +kernel

theorem s281 : optimized 6 0 w281 = false := by
  decide +kernel

theorem s282 : optimized 6 0 w282 = false := by
  decide +kernel

theorem s283 : optimized 6 0 w283 = false := by
  decide +kernel

theorem s284 : optimized 6 0 w284 = false := by
  decide +kernel

theorem s285 : optimized 6 0 w285 = false := by
  decide +kernel

theorem s286 : optimized 6 0 w286 = false := by
  decide +kernel

theorem s287 : optimized 6 0 w287 = false := by
  decide +kernel

theorem s288 : optimized 6 0 w288 = false := by
  decide +kernel

theorem s289 : optimized 6 0 w289 = false := by
  decide +kernel

theorem s290 : optimized 6 0 w290 = false := by
  decide +kernel

theorem s291 : optimized 6 0 w291 = false := by
  decide +kernel

theorem s292 : optimized 6 0 w292 = false := by
  decide +kernel

theorem s293 : optimized 6 0 w293 = false := by
  decide +kernel

theorem s294 : optimized 6 0 w294 = false := by
  decide +kernel

theorem s295 : optimized 6 0 w295 = false := by
  decide +kernel

theorem s296 : optimized 6 0 w296 = false := by
  decide +kernel

theorem s297 : optimized 6 1 w297 = false := by
  decide +kernel

theorem s298 : optimized 6 0 w298 = false := by
  decide +kernel

theorem s299 : optimized 6 0 w299 = false := by
  decide +kernel

theorem s300 : optimized 6 0 w300 = false := by
  decide +kernel

theorem s301 : optimized 6 0 w301 = false := by
  decide +kernel

theorem s302 : optimized 6 1 w302 = false := by
  decide +kernel

theorem s303 : optimized 6 0 w303 = false := by
  decide +kernel

theorem s304 : optimized 6 0 w304 = false := by
  decide +kernel

theorem s305 : optimized 6 0 w305 = false := by
  decide +kernel

theorem s306 : optimized 6 0 w306 = false := by
  decide +kernel

theorem s307 : optimized 6 0 w307 = false := by
  decide +kernel

theorem s308 : optimized 6 0 w308 = false := by
  decide +kernel

theorem s309 : optimized 6 0 w309 = false := by
  decide +kernel

theorem s310 : optimized 6 0 w310 = false := by
  decide +kernel

theorem s311 : optimized 6 0 w311 = false := by
  decide +kernel

theorem s312 : optimized 6 0 w312 = false := by
  decide +kernel

theorem s313 : optimized 6 0 w313 = false := by
  decide +kernel

theorem s314 : optimized 6 1 w314 = false := by
  decide +kernel

theorem s315 : optimized 6 0 w315 = false := by
  decide +kernel

theorem s316 : optimized 6 0 w316 = false := by
  decide +kernel

theorem s317 : optimized 6 1 w317 = false := by
  decide +kernel

theorem s318 : optimized 6 0 w318 = false := by
  decide +kernel

theorem s319 : optimized 6 0 w319 = false := by
  decide +kernel

theorem s320 : optimized 6 0 w320 = false := by
  decide +kernel

theorem s321 : optimized 6 0 w321 = false := by
  decide +kernel

theorem s322 : optimized 6 0 w322 = false := by
  decide +kernel

theorem s323 : optimized 6 0 w323 = false := by
  decide +kernel

theorem s324 : optimized 6 0 w324 = false := by
  decide +kernel

theorem s325 : optimized 6 0 w325 = false := by
  decide +kernel

theorem s326 : optimized 6 1 w326 = false := by
  decide +kernel

theorem s327 : optimized 6 0 w327 = false := by
  decide +kernel

theorem s328 : optimized 6 0 w328 = false := by
  decide +kernel

theorem s329 : optimized 6 0 w329 = false := by
  decide +kernel

theorem s330 : optimized 6 1 w330 = false := by
  decide +kernel

theorem s331 : optimized 6 0 w331 = false := by
  decide +kernel

theorem s332 : optimized 6 0 w332 = false := by
  decide +kernel

theorem s333 : optimized 6 0 w333 = false := by
  decide +kernel

theorem s334 : optimized 6 1 w334 = false := by
  decide +kernel

theorem s335 : optimized 6 0 w335 = false := by
  decide +kernel

theorem s336 : optimized 6 0 w336 = false := by
  decide +kernel

theorem s337 : optimized 6 0 w337 = false := by
  decide +kernel

theorem s338 : optimized 6 1 w338 = false := by
  decide +kernel

theorem s339 : optimized 6 0 w339 = false := by
  decide +kernel

theorem s340 : optimized 6 0 w340 = false := by
  decide +kernel

theorem s341 : optimized 6 0 w341 = false := by
  decide +kernel

theorem s342 : optimized 6 0 w342 = false := by
  decide +kernel

theorem s343 : optimized 6 0 w343 = false := by
  decide +kernel

theorem s344 : optimized 6 0 w344 = false := by
  decide +kernel

theorem s345 : optimized 6 0 w345 = false := by
  decide +kernel

theorem s346 : optimized 6 0 w346 = false := by
  decide +kernel

theorem s347 : optimized 6 0 w347 = false := by
  decide +kernel

theorem s348 : optimized 6 0 w348 = false := by
  decide +kernel

theorem s349 : optimized 6 1 w349 = false := by
  decide +kernel

theorem s350 : optimized 6 0 w350 = false := by
  decide +kernel

theorem s351 : optimized 6 0 w351 = false := by
  decide +kernel

theorem s352 : optimized 6 0 w352 = false := by
  decide +kernel

theorem s353 : optimized 6 1 w353 = false := by
  decide +kernel

theorem s354 : optimized 6 0 w354 = false := by
  decide +kernel

theorem s355 : optimized 6 0 w355 = false := by
  decide +kernel

theorem s356 : optimized 6 1 w356 = false := by
  decide +kernel

theorem s357 : optimized 6 0 w357 = false := by
  decide +kernel

theorem s358 : optimized 6 0 w358 = false := by
  decide +kernel

theorem s359 : optimized 6 1 w359 = false := by
  decide +kernel

theorem s360 : optimized 6 0 w360 = false := by
  decide +kernel

theorem s361 : optimized 6 0 w361 = false := by
  decide +kernel

theorem s362 : optimized 6 1 w362 = false := by
  decide +kernel

theorem s363 : optimized 6 0 w363 = false := by
  decide +kernel

theorem s364 : optimized 6 0 w364 = false := by
  decide +kernel

theorem s365 : optimized 6 1 w365 = false := by
  decide +kernel

theorem s366 : optimized 6 0 w366 = false := by
  decide +kernel

theorem s367 : optimized 6 0 w367 = false := by
  decide +kernel

theorem s368 : optimized 6 0 w368 = false := by
  decide +kernel

theorem s369 : optimized 6 0 w369 = false := by
  decide +kernel

theorem s370 : optimized 6 0 w370 = false := by
  decide +kernel

theorem s371 : optimized 6 0 w371 = false := by
  decide +kernel

theorem s372 : optimized 6 1 w372 = false := by
  decide +kernel

theorem s373 : optimized 6 0 w373 = false := by
  decide +kernel

theorem s374 : optimized 6 0 w374 = false := by
  decide +kernel

theorem s375 : optimized 6 0 w375 = false := by
  decide +kernel

theorem s376 : optimized 6 1 w376 = false := by
  decide +kernel

theorem s377 : optimized 6 0 w377 = false := by
  decide +kernel

theorem s378 : optimized 6 0 w378 = false := by
  decide +kernel

theorem s379 : optimized 6 0 w379 = false := by
  decide +kernel

theorem s380 : optimized 6 0 w380 = false := by
  decide +kernel

theorem s381 : optimized 6 1 w381 = false := by
  decide +kernel

theorem s382 : optimized 6 0 w382 = false := by
  decide +kernel

theorem s383 : optimized 6 0 w383 = false := by
  decide +kernel

theorem s384 : optimized 6 0 w384 = false := by
  decide +kernel

theorem s385 : optimized 6 0 w385 = false := by
  decide +kernel

theorem s386 : optimized 6 0 w386 = false := by
  decide +kernel

theorem s387 : optimized 6 0 w387 = false := by
  decide +kernel

theorem s388 : optimized 6 0 w388 = false := by
  decide +kernel

theorem s389 : optimized 6 0 w389 = false := by
  decide +kernel

theorem s390 : optimized 6 0 w390 = false := by
  decide +kernel

theorem s391 : optimized 6 0 w391 = false := by
  decide +kernel

theorem s392 : optimized 6 0 w392 = false := by
  decide +kernel

theorem s393 : optimized 6 0 w393 = false := by
  decide +kernel

theorem s394 : optimized 6 0 w394 = false := by
  decide +kernel

theorem s395 : optimized 6 0 w395 = false := by
  decide +kernel

theorem s396 : optimized 6 0 w396 = false := by
  decide +kernel

theorem s397 : optimized 6 0 w397 = false := by
  decide +kernel

theorem s398 : optimized 6 0 w398 = false := by
  decide +kernel

theorem s399 : optimized 6 0 w399 = false := by
  decide +kernel

theorem s400 : optimized 6 0 w400 = false := by
  decide +kernel

theorem s401 : optimized 6 0 w401 = false := by
  decide +kernel

theorem s402 : optimized 6 0 w402 = false := by
  decide +kernel

theorem s403 : optimized 6 1 w403 = false := by
  decide +kernel

theorem s404 : optimized 6 0 w404 = false := by
  decide +kernel

theorem s405 : optimized 6 0 w405 = false := by
  decide +kernel

theorem s406 : optimized 6 0 w406 = false := by
  decide +kernel

theorem s407 : optimized 6 0 w407 = false := by
  decide +kernel

theorem s408 : optimized 6 1 w408 = false := by
  decide +kernel

theorem s409 : optimized 6 0 w409 = false := by
  decide +kernel

theorem s410 : optimized 6 0 w410 = false := by
  decide +kernel

theorem s411 : optimized 6 0 w411 = false := by
  decide +kernel

theorem s412 : optimized 6 0 w412 = false := by
  decide +kernel

theorem s413 : optimized 6 0 w413 = false := by
  decide +kernel

theorem s414 : optimized 6 0 w414 = false := by
  decide +kernel

theorem s415 : optimized 6 0 w415 = false := by
  decide +kernel

theorem s416 : optimized 6 0 w416 = false := by
  decide +kernel

theorem s417 : optimized 6 0 w417 = false := by
  decide +kernel

theorem s418 : optimized 6 0 w418 = false := by
  decide +kernel

theorem s419 : optimized 6 0 w419 = false := by
  decide +kernel

theorem s420 : optimized 6 0 w420 = false := by
  decide +kernel

theorem s421 : optimized 6 1 w421 = false := by
  decide +kernel

theorem s422 : optimized 6 0 w422 = false := by
  decide +kernel

theorem s423 : optimized 6 0 w423 = false := by
  decide +kernel

theorem s424 : optimized 6 0 w424 = false := by
  decide +kernel

theorem s425 : optimized 6 0 w425 = false := by
  decide +kernel

theorem s426 : optimized 6 1 w426 = false := by
  decide +kernel

theorem s427 : optimized 6 0 w427 = false := by
  decide +kernel

theorem s428 : optimized 6 0 w428 = false := by
  decide +kernel

theorem s429 : optimized 6 0 w429 = false := by
  decide +kernel

theorem s430 : optimized 6 0 w430 = false := by
  decide +kernel

theorem s431 : optimized 6 0 w431 = false := by
  decide +kernel

theorem s432 : optimized 6 0 w432 = false := by
  decide +kernel

theorem s433 : optimized 6 0 w433 = false := by
  decide +kernel

theorem s434 : optimized 6 0 w434 = false := by
  decide +kernel

theorem s435 : optimized 6 0 w435 = false := by
  decide +kernel

theorem s436 : optimized 6 0 w436 = false := by
  decide +kernel

theorem s437 : optimized 6 1 w437 = false := by
  decide +kernel

theorem s438 : optimized 6 0 w438 = false := by
  decide +kernel

theorem s439 : optimized 6 0 w439 = false := by
  decide +kernel

theorem s440 : optimized 6 0 w440 = false := by
  decide +kernel

theorem s441 : optimized 6 1 w441 = false := by
  decide +kernel

theorem s442 : optimized 6 0 w442 = false := by
  decide +kernel

theorem s443 : optimized 6 0 w443 = false := by
  decide +kernel

theorem s444 : optimized 6 0 w444 = false := by
  decide +kernel

theorem s445 : optimized 6 1 w445 = false := by
  decide +kernel

theorem s446 : optimized 6 0 w446 = false := by
  decide +kernel

theorem s447 : optimized 6 0 w447 = false := by
  decide +kernel

theorem s448 : optimized 6 0 w448 = false := by
  decide +kernel

theorem s449 : optimized 6 0 w449 = false := by
  decide +kernel

theorem s450 : optimized 6 0 w450 = false := by
  decide +kernel

theorem s451 : optimized 6 0 w451 = false := by
  decide +kernel

theorem s452 : optimized 6 0 w452 = false := by
  decide +kernel

theorem s453 : optimized 6 0 w453 = false := by
  decide +kernel

theorem s454 : optimized 6 0 w454 = false := by
  decide +kernel

theorem s455 : optimized 6 0 w455 = false := by
  decide +kernel

theorem s456 : optimized 6 0 w456 = false := by
  decide +kernel

theorem s457 : optimized 6 0 w457 = false := by
  decide +kernel

theorem s458 : optimized 6 0 w458 = false := by
  decide +kernel

theorem s459 : optimized 6 0 w459 = false := by
  decide +kernel

theorem s460 : optimized 6 0 w460 = false := by
  decide +kernel

theorem s461 : optimized 6 0 w461 = false := by
  decide +kernel

theorem s462 : optimized 6 0 w462 = false := by
  decide +kernel

theorem s463 : optimized 6 0 w463 = false := by
  decide +kernel

theorem s464 : optimized 6 0 w464 = false := by
  decide +kernel

theorem s465 : optimized 6 0 w465 = false := by
  decide +kernel

theorem s466 : optimized 6 0 w466 = false := by
  decide +kernel

theorem s467 : optimized 6 0 w467 = false := by
  decide +kernel

theorem s468 : optimized 6 0 w468 = false := by
  decide +kernel

theorem s469 : optimized 6 0 w469 = false := by
  decide +kernel

theorem s470 : optimized 6 0 w470 = false := by
  decide +kernel

theorem s471 : optimized 6 0 w471 = false := by
  decide +kernel

theorem s472 : optimized 6 0 w472 = false := by
  decide +kernel

theorem s473 : optimized 6 0 w473 = false := by
  decide +kernel

theorem s474 : optimized 6 0 w474 = false := by
  decide +kernel

theorem s475 : optimized 6 0 w475 = false := by
  decide +kernel

theorem s476 : optimized 6 0 w476 = false := by
  decide +kernel

theorem s477 : optimized 6 0 w477 = false := by
  decide +kernel

theorem s478 : optimized 6 0 w478 = false := by
  decide +kernel

theorem s479 : optimized 6 1 w479 = false := by
  decide +kernel

theorem s480 : optimized 6 0 w480 = false := by
  decide +kernel

theorem s481 : optimized 6 0 w481 = false := by
  decide +kernel

theorem s482 : optimized 6 0 w482 = false := by
  decide +kernel

theorem s483 : optimized 6 1 w483 = false := by
  decide +kernel

theorem s484 : optimized 6 0 w484 = false := by
  decide +kernel

theorem s485 : optimized 6 0 w485 = false := by
  decide +kernel

theorem s486 : optimized 6 0 w486 = false := by
  decide +kernel

theorem s487 : optimized 6 0 w487 = false := by
  decide +kernel

theorem s488 : optimized 6 0 w488 = false := by
  decide +kernel

theorem s489 : optimized 6 0 w489 = false := by
  decide +kernel

theorem s490 : optimized 6 0 w490 = false := by
  decide +kernel

theorem s491 : optimized 6 0 w491 = false := by
  decide +kernel

theorem s492 : optimized 6 0 w492 = false := by
  decide +kernel

theorem s493 : optimized 6 0 w493 = false := by
  decide +kernel

theorem s494 : optimized 6 0 w494 = false := by
  decide +kernel

theorem s495 : optimized 6 0 w495 = false := by
  decide +kernel

theorem s496 : optimized 6 0 w496 = false := by
  decide +kernel

theorem s497 : optimized 6 0 w497 = false := by
  decide +kernel

theorem s498 : optimized 6 1 w498 = false := by
  decide +kernel

theorem s499 : optimized 6 0 w499 = false := by
  decide +kernel

theorem s500 : optimized 6 0 w500 = false := by
  decide +kernel

theorem s501 : optimized 6 1 w501 = false := by
  decide +kernel

theorem s502 : optimized 6 0 w502 = false := by
  decide +kernel

theorem s503 : optimized 6 0 w503 = false := by
  decide +kernel

theorem s504 : optimized 6 0 w504 = false := by
  decide +kernel

theorem s505 : optimized 6 0 w505 = false := by
  decide +kernel

theorem s506 : optimized 6 0 w506 = false := by
  decide +kernel

theorem s507 : optimized 6 0 w507 = false := by
  decide +kernel

theorem s508 : optimized 6 1 w508 = false := by
  decide +kernel

theorem s509 : optimized 6 0 w509 = false := by
  decide +kernel

theorem s510 : optimized 6 0 w510 = false := by
  decide +kernel

theorem s511 : optimized 6 0 w511 = false := by
  decide +kernel

theorem s512 : optimized 6 0 w512 = false := by
  decide +kernel

theorem s513 : optimized 6 0 w513 = false := by
  decide +kernel

theorem s514 : optimized 6 0 w514 = false := by
  decide +kernel

theorem s515 : optimized 6 0 w515 = false := by
  decide +kernel

theorem s516 : optimized 6 0 w516 = false := by
  decide +kernel

theorem s517 : optimized 6 0 w517 = false := by
  decide +kernel

theorem s518 : optimized 6 0 w518 = false := by
  decide +kernel

theorem s519 : optimized 6 0 w519 = false := by
  decide +kernel

theorem s520 : optimized 6 0 w520 = false := by
  decide +kernel

theorem s521 : optimized 6 0 w521 = false := by
  decide +kernel

theorem s522 : optimized 6 0 w522 = false := by
  decide +kernel

theorem s523 : optimized 6 0 w523 = false := by
  decide +kernel

theorem s524 : optimized 6 0 w524 = false := by
  decide +kernel

theorem s525 : optimized 6 0 w525 = false := by
  decide +kernel

theorem s526 : optimized 6 0 w526 = false := by
  decide +kernel

theorem s527 : optimized 6 0 w527 = false := by
  decide +kernel

theorem s528 : optimized 6 0 w528 = false := by
  decide +kernel

theorem s529 : optimized 6 0 w529 = false := by
  decide +kernel

theorem s530 : optimized 6 0 w530 = false := by
  decide +kernel

theorem s531 : optimized 6 0 w531 = false := by
  decide +kernel

theorem s532 : optimized 6 0 w532 = false := by
  decide +kernel

theorem s533 : optimized 6 0 w533 = false := by
  decide +kernel

theorem s534 : optimized 6 1 w534 = false := by
  decide +kernel

theorem s535 : optimized 6 0 w535 = false := by
  decide +kernel

theorem s536 : optimized 6 0 w536 = false := by
  decide +kernel

theorem s537 : optimized 6 1 w537 = false := by
  decide +kernel

theorem s538 : optimized 6 0 w538 = false := by
  decide +kernel

theorem s539 : optimized 6 0 w539 = false := by
  decide +kernel

theorem s540 : optimized 6 1 w540 = false := by
  decide +kernel

theorem s541 : optimized 6 0 w541 = false := by
  decide +kernel

theorem s542 : optimized 6 0 w542 = false := by
  decide +kernel

theorem s543 : optimized 6 0 w543 = false := by
  decide +kernel

theorem s544 : optimized 6 1 w544 = false := by
  decide +kernel

theorem s545 : optimized 6 0 w545 = false := by
  decide +kernel

theorem s546 : optimized 6 0 w546 = false := by
  decide +kernel

theorem s547 : optimized 6 0 w547 = false := by
  decide +kernel

theorem s548 : optimized 6 0 w548 = false := by
  decide +kernel

theorem s549 : optimized 6 0 w549 = false := by
  decide +kernel

theorem s550 : optimized 6 0 w550 = false := by
  decide +kernel

theorem s551 : optimized 6 0 w551 = false := by
  decide +kernel

theorem s552 : optimized 6 0 w552 = false := by
  decide +kernel

theorem s553 : optimized 6 0 w553 = false := by
  decide +kernel

theorem s554 : optimized 6 0 w554 = false := by
  decide +kernel

theorem s555 : optimized 6 0 w555 = false := by
  decide +kernel

theorem s556 : optimized 6 0 w556 = false := by
  decide +kernel

theorem s557 : optimized 6 0 w557 = false := by
  decide +kernel

theorem s558 : optimized 6 0 w558 = false := by
  decide +kernel

theorem s559 : optimized 6 0 w559 = false := by
  decide +kernel

theorem s560 : optimized 6 0 w560 = false := by
  decide +kernel

theorem s561 : optimized 6 0 w561 = false := by
  decide +kernel

theorem s562 : optimized 6 1 w562 = false := by
  decide +kernel

theorem s563 : optimized 6 0 w563 = false := by
  decide +kernel

theorem s564 : optimized 6 0 w564 = false := by
  decide +kernel

theorem s565 : optimized 6 0 w565 = false := by
  decide +kernel

theorem s566 : optimized 6 0 w566 = false := by
  decide +kernel

theorem s567 : optimized 6 0 w567 = false := by
  decide +kernel

theorem s568 : optimized 6 0 w568 = false := by
  decide +kernel

theorem s569 : optimized 6 0 w569 = false := by
  decide +kernel

theorem s570 : optimized 6 0 w570 = false := by
  decide +kernel

theorem s571 : optimized 6 0 w571 = false := by
  decide +kernel

theorem s572 : optimized 6 0 w572 = false := by
  decide +kernel

theorem s573 : optimized 6 0 w573 = false := by
  decide +kernel

theorem s574 : optimized 6 0 w574 = false := by
  decide +kernel

theorem s575 : optimized 6 0 w575 = false := by
  decide +kernel

theorem s576 : optimized 6 0 w576 = false := by
  decide +kernel

theorem s577 : optimized 6 0 w577 = false := by
  decide +kernel

theorem s578 : optimized 6 0 w578 = false := by
  decide +kernel

theorem s579 : optimized 6 0 w579 = false := by
  decide +kernel

theorem s580 : optimized 6 0 w580 = false := by
  decide +kernel

theorem s581 : optimized 6 0 w581 = false := by
  decide +kernel

theorem s582 : optimized 6 0 w582 = false := by
  decide +kernel

theorem s583 : optimized 6 0 w583 = false := by
  decide +kernel

theorem s584 : optimized 6 0 w584 = false := by
  decide +kernel

theorem s585 : optimized 6 0 w585 = false := by
  decide +kernel

theorem s586 : optimized 6 1 w586 = false := by
  decide +kernel

theorem s587 : optimized 6 0 w587 = false := by
  decide +kernel

theorem s588 : optimized 6 0 w588 = false := by
  decide +kernel

theorem s589 : optimized 6 0 w589 = false := by
  decide +kernel

theorem s590 : optimized 6 1 w590 = false := by
  decide +kernel

theorem s591 : optimized 6 0 w591 = false := by
  decide +kernel

theorem s592 : optimized 6 0 w592 = false := by
  decide +kernel

theorem s593 : optimized 6 0 w593 = false := by
  decide +kernel

theorem s594 : optimized 6 0 w594 = false := by
  decide +kernel

theorem s595 : optimized 6 0 w595 = false := by
  decide +kernel

theorem s596 : optimized 6 0 w596 = false := by
  decide +kernel

theorem s597 : optimized 6 0 w597 = false := by
  decide +kernel

theorem s598 : optimized 6 0 w598 = false := by
  decide +kernel

theorem s599 : optimized 6 1 w599 = false := by
  decide +kernel

theorem s600 : optimized 6 0 w600 = false := by
  decide +kernel

theorem s601 : optimized 6 0 w601 = false := by
  decide +kernel

theorem s602 : optimized 6 0 w602 = false := by
  decide +kernel

theorem s603 : optimized 6 1 w603 = false := by
  decide +kernel

theorem s604 : optimized 6 1 w604 = false := by
  decide +kernel

theorem s605 : optimized 6 0 w605 = false := by
  decide +kernel

theorem s606 : optimized 6 0 w606 = false := by
  decide +kernel

theorem s607 : optimized 6 0 w607 = false := by
  decide +kernel

theorem s608 : optimized 6 0 w608 = false := by
  decide +kernel

theorem s609 : optimized 6 0 w609 = false := by
  decide +kernel

theorem s610 : optimized 6 0 w610 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s611 : optimized 6 2 w611 = false :=
  opt_false_of_P (tbl := [(5, 0, w0), (5, 0, w1), (5, 0, w2), (5, 0, w3), (5, 0, w4), (5, 0, w5), (5, 0, w6), (5, 0, w7), (5, 0, w8), (5, 0, w9), (5, 0, w10), (5, 0, w11), (5, 0, w12), (5, 0, w13), (5, 0, w14), (5, 0, w15), (5, 0, w16), (5, 0, w17), (5, 0, w18), (5, 0, w19), (5, 0, w20), (5, 0, w21), (5, 0, w22), (5, 0, w23), (5, 0, w24), (5, 0, w25), (5, 0, w26), (5, 0, w27), (5, 0, w28), (5, 0, w29), (5, 0, w30), (5, 0, w31), (5, 0, w32), (5, 0, w33), (5, 0, w34), (5, 0, w35), (5, 0, w36), (5, 0, w37), (5, 0, w38), (5, 0, w39)])
    (tbl_cons s0 (tbl_cons s1 (tbl_cons s2 (tbl_cons s3 (tbl_cons s4 (tbl_cons s5 (tbl_cons s6 (tbl_cons s7 (tbl_cons s8 (tbl_cons s9 (tbl_cons s10 (tbl_cons s11 (tbl_cons s12 (tbl_cons s13 (tbl_cons s14 (tbl_cons s15 (tbl_cons s16 (tbl_cons s17 (tbl_cons s18 (tbl_cons s19 (tbl_cons s20 (tbl_cons s21 (tbl_cons s22 (tbl_cons s23 (tbl_cons s24 (tbl_cons s25 (tbl_cons s26 (tbl_cons s27 (tbl_cons s28 (tbl_cons s29 (tbl_cons s30 (tbl_cons s31 (tbl_cons s32 (tbl_cons s33 (tbl_cons s34 (tbl_cons s35 (tbl_cons s36 (tbl_cons s37 (tbl_cons s38 (tbl_cons s39 tbl_nil))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

theorem s612 : optimized 6 1 w612 = false := by
  decide +kernel

theorem s613 : optimized 6 1 w613 = false := by
  decide +kernel

theorem s614 : optimized 6 0 w614 = false := by
  decide +kernel

theorem s615 : optimized 6 0 w615 = false := by
  decide +kernel

theorem s616 : optimized 6 1 w616 = false := by
  decide +kernel

theorem s617 : optimized 6 0 w617 = false := by
  decide +kernel

theorem s618 : optimized 6 0 w618 = false := by
  decide +kernel

theorem s619 : optimized 6 0 w619 = false := by
  decide +kernel

theorem s620 : optimized 6 0 w620 = false := by
  decide +kernel

theorem s621 : optimized 6 0 w621 = false := by
  decide +kernel

theorem s622 : optimized 6 0 w622 = false := by
  decide +kernel

theorem s623 : optimized 6 1 w623 = false := by
  decide +kernel

theorem s624 : optimized 6 0 w624 = false := by
  decide +kernel

theorem s625 : optimized 6 0 w625 = false := by
  decide +kernel

theorem s626 : optimized 6 0 w626 = false := by
  decide +kernel

theorem s627 : optimized 6 0 w627 = false := by
  decide +kernel

theorem s628 : optimized 6 0 w628 = false := by
  decide +kernel

theorem s629 : optimized 6 0 w629 = false := by
  decide +kernel

theorem s630 : optimized 6 0 w630 = false := by
  decide +kernel

theorem s631 : optimized 6 0 w631 = false := by
  decide +kernel

theorem s632 : optimized 6 0 w632 = false := by
  decide +kernel

theorem s633 : optimized 6 0 w633 = false := by
  decide +kernel

theorem s634 : optimized 6 0 w634 = false := by
  decide +kernel

theorem s635 : optimized 6 0 w635 = false := by
  decide +kernel

theorem s636 : optimized 6 0 w636 = false := by
  decide +kernel

theorem s637 : optimized 6 0 w637 = false := by
  decide +kernel

theorem s638 : optimized 6 0 w638 = false := by
  decide +kernel

theorem s639 : optimized 6 0 w639 = false := by
  decide +kernel

theorem s640 : optimized 6 0 w640 = false := by
  decide +kernel

theorem s641 : optimized 6 0 w641 = false := by
  decide +kernel

theorem s642 : optimized 6 0 w642 = false := by
  decide +kernel

theorem s643 : optimized 6 0 w643 = false := by
  decide +kernel

theorem s644 : optimized 6 0 w644 = false := by
  decide +kernel

theorem s645 : optimized 6 0 w645 = false := by
  decide +kernel

theorem s646 : optimized 6 0 w646 = false := by
  decide +kernel

theorem s647 : optimized 6 0 w647 = false := by
  decide +kernel

theorem s648 : optimized 6 0 w648 = false := by
  decide +kernel

theorem s649 : optimized 6 0 w649 = false := by
  decide +kernel

theorem s650 : optimized 6 0 w650 = false := by
  decide +kernel

theorem s651 : optimized 6 0 w651 = false := by
  decide +kernel

theorem s652 : optimized 6 0 w652 = false := by
  decide +kernel

theorem s653 : optimized 6 0 w653 = false := by
  decide +kernel

theorem s654 : optimized 6 0 w654 = false := by
  decide +kernel

theorem s655 : optimized 6 0 w655 = false := by
  decide +kernel

theorem s656 : optimized 6 1 w656 = false := by
  decide +kernel

theorem s657 : optimized 6 0 w657 = false := by
  decide +kernel

theorem s658 : optimized 6 0 w658 = false := by
  decide +kernel

theorem s659 : optimized 6 1 w659 = false := by
  decide +kernel

theorem s660 : optimized 6 0 w660 = false := by
  decide +kernel

theorem s661 : optimized 6 0 w661 = false := by
  decide +kernel

theorem s662 : optimized 6 0 w662 = false := by
  decide +kernel

theorem s663 : optimized 6 0 w663 = false := by
  decide +kernel

theorem s664 : optimized 6 0 w664 = false := by
  decide +kernel

theorem s665 : optimized 6 0 w665 = false := by
  decide +kernel

theorem s666 : optimized 6 0 w666 = false := by
  decide +kernel

theorem s667 : optimized 6 0 w667 = false := by
  decide +kernel

theorem s668 : optimized 6 0 w668 = false := by
  decide +kernel

theorem s669 : optimized 6 1 w669 = false := by
  decide +kernel

theorem s670 : optimized 6 0 w670 = false := by
  decide +kernel

theorem s671 : optimized 6 0 w671 = false := by
  decide +kernel

theorem s672 : optimized 6 0 w672 = false := by
  decide +kernel

theorem s673 : optimized 6 0 w673 = false := by
  decide +kernel

theorem s674 : optimized 6 0 w674 = false := by
  decide +kernel

theorem s675 : optimized 6 0 w675 = false := by
  decide +kernel

theorem s676 : optimized 6 0 w676 = false := by
  decide +kernel

theorem s677 : optimized 6 0 w677 = false := by
  decide +kernel

theorem s678 : optimized 6 0 w678 = false := by
  decide +kernel

theorem s679 : optimized 6 0 w679 = false := by
  decide +kernel

theorem s680 : optimized 6 0 w680 = false := by
  decide +kernel

theorem s681 : optimized 6 0 w681 = false := by
  decide +kernel

theorem s682 : optimized 6 0 w682 = false := by
  decide +kernel

theorem s683 : optimized 6 0 w683 = false := by
  decide +kernel

theorem s684 : optimized 6 0 w684 = false := by
  decide +kernel

theorem s685 : optimized 6 0 w685 = false := by
  decide +kernel

theorem s686 : optimized 6 0 w686 = false := by
  decide +kernel

theorem s687 : optimized 6 0 w687 = false := by
  decide +kernel

theorem s688 : optimized 6 0 w688 = false := by
  decide +kernel

theorem s689 : optimized 6 0 w689 = false := by
  decide +kernel

theorem s690 : optimized 6 0 w690 = false := by
  decide +kernel

theorem s691 : optimized 6 0 w691 = false := by
  decide +kernel

theorem s692 : optimized 6 0 w692 = false := by
  decide +kernel

theorem s693 : optimized 6 0 w693 = false := by
  decide +kernel

theorem s694 : optimized 6 0 w694 = false := by
  decide +kernel

theorem s695 : optimized 6 0 w695 = false := by
  decide +kernel

theorem s696 : optimized 6 0 w696 = false := by
  decide +kernel

theorem s697 : optimized 6 0 w697 = false := by
  decide +kernel

theorem s698 : optimized 6 0 w698 = false := by
  decide +kernel

theorem s699 : optimized 6 0 w699 = false := by
  decide +kernel

theorem s700 : optimized 6 0 w700 = false := by
  decide +kernel

theorem s701 : optimized 6 0 w701 = false := by
  decide +kernel

theorem s702 : optimized 6 0 w702 = false := by
  decide +kernel

theorem s703 : optimized 6 0 w703 = false := by
  decide +kernel

theorem s704 : optimized 6 0 w704 = false := by
  decide +kernel

theorem s705 : optimized 6 0 w705 = false := by
  decide +kernel

theorem s706 : optimized 6 0 w706 = false := by
  decide +kernel

theorem s707 : optimized 6 0 w707 = false := by
  decide +kernel

theorem s708 : optimized 6 0 w708 = false := by
  decide +kernel

theorem s709 : optimized 6 0 w709 = false := by
  decide +kernel

theorem s710 : optimized 6 0 w710 = false := by
  decide +kernel

theorem s711 : optimized 6 1 w711 = false := by
  decide +kernel

theorem s712 : optimized 6 0 w712 = false := by
  decide +kernel

theorem s713 : optimized 6 0 w713 = false := by
  decide +kernel

theorem s714 : optimized 6 0 w714 = false := by
  decide +kernel

theorem s715 : optimized 6 0 w715 = false := by
  decide +kernel

theorem s716 : optimized 6 0 w716 = false := by
  decide +kernel

theorem s717 : optimized 6 0 w717 = false := by
  decide +kernel

theorem s718 : optimized 6 0 w718 = false := by
  decide +kernel

theorem s719 : optimized 6 0 w719 = false := by
  decide +kernel

theorem s720 : optimized 6 1 w720 = false := by
  decide +kernel

theorem s721 : optimized 6 0 w721 = false := by
  decide +kernel

theorem s722 : optimized 6 0 w722 = false := by
  decide +kernel

theorem s723 : optimized 6 0 w723 = false := by
  decide +kernel

theorem s724 : optimized 6 0 w724 = false := by
  decide +kernel

theorem s725 : optimized 6 0 w725 = false := by
  decide +kernel

theorem s726 : optimized 6 0 w726 = false := by
  decide +kernel

theorem s727 : optimized 6 0 w727 = false := by
  decide +kernel

theorem s728 : optimized 6 0 w728 = false := by
  decide +kernel

theorem s729 : optimized 6 0 w729 = false := by
  decide +kernel

theorem s730 : optimized 6 0 w730 = false := by
  decide +kernel

theorem s731 : optimized 6 0 w731 = false := by
  decide +kernel

theorem s732 : optimized 6 0 w732 = false := by
  decide +kernel

theorem s733 : optimized 6 0 w733 = false := by
  decide +kernel

theorem s734 : optimized 6 0 w734 = false := by
  decide +kernel

theorem s735 : optimized 6 0 w735 = false := by
  decide +kernel

theorem s736 : optimized 6 0 w736 = false := by
  decide +kernel

theorem s737 : optimized 6 0 w737 = false := by
  decide +kernel

theorem s738 : optimized 6 0 w738 = false := by
  decide +kernel

theorem s739 : optimized 6 0 w739 = false := by
  decide +kernel

theorem s740 : optimized 6 0 w740 = false := by
  decide +kernel

theorem s741 : optimized 6 0 w741 = false := by
  decide +kernel

theorem s742 : optimized 6 0 w742 = false := by
  decide +kernel

theorem s743 : optimized 6 0 w743 = false := by
  decide +kernel

theorem s744 : optimized 6 0 w744 = false := by
  decide +kernel

theorem s745 : optimized 6 0 w745 = false := by
  decide +kernel

theorem s746 : optimized 6 0 w746 = false := by
  decide +kernel

theorem s747 : optimized 6 0 w747 = false := by
  decide +kernel

theorem s748 : optimized 6 0 w748 = false := by
  decide +kernel

theorem s749 : optimized 6 0 w749 = false := by
  decide +kernel

theorem s750 : optimized 6 0 w750 = false := by
  decide +kernel

theorem s751 : optimized 6 0 w751 = false := by
  decide +kernel

theorem s752 : optimized 6 0 w752 = false := by
  decide +kernel

theorem s753 : optimized 6 0 w753 = false := by
  decide +kernel

theorem s754 : optimized 6 0 w754 = false := by
  decide +kernel

theorem s755 : optimized 6 0 w755 = false := by
  decide +kernel

theorem s756 : optimized 6 1 w756 = false := by
  decide +kernel

theorem s757 : optimized 6 0 w757 = false := by
  decide +kernel

theorem s758 : optimized 6 0 w758 = false := by
  decide +kernel

theorem s759 : optimized 6 0 w759 = false := by
  decide +kernel

theorem s760 : optimized 6 0 w760 = false := by
  decide +kernel

theorem s761 : optimized 6 0 w761 = false := by
  decide +kernel

theorem s762 : optimized 6 0 w762 = false := by
  decide +kernel

theorem s763 : optimized 6 0 w763 = false := by
  decide +kernel

theorem s764 : optimized 6 0 w764 = false := by
  decide +kernel

theorem s765 : optimized 6 0 w765 = false := by
  decide +kernel

theorem s766 : optimized 6 0 w766 = false := by
  decide +kernel

theorem s767 : optimized 6 0 w767 = false := by
  decide +kernel

theorem s768 : optimized 6 0 w768 = false := by
  decide +kernel

theorem s769 : optimized 6 0 w769 = false := by
  decide +kernel

theorem s770 : optimized 6 0 w770 = false := by
  decide +kernel

theorem s771 : optimized 6 0 w771 = false := by
  decide +kernel

theorem s772 : optimized 6 0 w772 = false := by
  decide +kernel

theorem s773 : optimized 6 0 w773 = false := by
  decide +kernel

theorem s774 : optimized 6 0 w774 = false := by
  decide +kernel

theorem s775 : optimized 6 0 w775 = false := by
  decide +kernel

theorem s776 : optimized 6 0 w776 = false := by
  decide +kernel

theorem s777 : optimized 6 0 w777 = false := by
  decide +kernel

theorem s778 : optimized 6 0 w778 = false := by
  decide +kernel

theorem s779 : optimized 6 0 w779 = false := by
  decide +kernel

theorem s780 : optimized 6 0 w780 = false := by
  decide +kernel

theorem s781 : optimized 6 0 w781 = false := by
  decide +kernel

theorem s782 : optimized 6 0 w782 = false := by
  decide +kernel

theorem s783 : optimized 6 0 w783 = false := by
  decide +kernel

theorem s784 : optimized 6 0 w784 = false := by
  decide +kernel

theorem s785 : optimized 6 0 w785 = false := by
  decide +kernel

theorem s786 : optimized 6 0 w786 = false := by
  decide +kernel

theorem s787 : optimized 6 1 w787 = false := by
  decide +kernel

theorem s788 : optimized 6 0 w788 = false := by
  decide +kernel

theorem s789 : optimized 6 0 w789 = false := by
  decide +kernel

theorem s790 : optimized 6 1 w790 = false := by
  decide +kernel

theorem s791 : optimized 6 0 w791 = false := by
  decide +kernel

theorem s792 : optimized 6 0 w792 = false := by
  decide +kernel

theorem s793 : optimized 6 0 w793 = false := by
  decide +kernel

theorem s794 : optimized 6 1 w794 = false := by
  decide +kernel

theorem s795 : optimized 6 0 w795 = false := by
  decide +kernel

theorem s796 : optimized 6 0 w796 = false := by
  decide +kernel

theorem s797 : optimized 6 0 w797 = false := by
  decide +kernel

theorem s798 : optimized 6 1 w798 = false := by
  decide +kernel

theorem s799 : optimized 6 0 w799 = false := by
  decide +kernel

theorem s800 : optimized 6 0 w800 = false := by
  decide +kernel

theorem s801 : optimized 6 0 w801 = false := by
  decide +kernel

theorem s802 : optimized 6 0 w802 = false := by
  decide +kernel

theorem s803 : optimized 6 0 w803 = false := by
  decide +kernel

theorem s804 : optimized 6 0 w804 = false := by
  decide +kernel

theorem s805 : optimized 6 0 w805 = false := by
  decide +kernel

theorem s806 : optimized 6 0 w806 = false := by
  decide +kernel

theorem s807 : optimized 6 1 w807 = false := by
  decide +kernel

theorem s808 : optimized 6 0 w808 = false := by
  decide +kernel

theorem s809 : optimized 6 0 w809 = false := by
  decide +kernel

theorem s810 : optimized 6 0 w810 = false := by
  decide +kernel

theorem s811 : optimized 6 1 w811 = false := by
  decide +kernel

theorem s812 : optimized 6 0 w812 = false := by
  decide +kernel

theorem s813 : optimized 6 0 w813 = false := by
  decide +kernel

theorem s814 : optimized 6 0 w814 = false := by
  decide +kernel

theorem s815 : optimized 6 1 w815 = false := by
  decide +kernel

theorem s816 : optimized 6 0 w816 = false := by
  decide +kernel

theorem s817 : optimized 6 0 w817 = false := by
  decide +kernel

theorem s818 : optimized 6 0 w818 = false := by
  decide +kernel

theorem s819 : optimized 6 1 w819 = false := by
  decide +kernel

theorem s820 : optimized 6 0 w820 = false := by
  decide +kernel

theorem s821 : optimized 6 0 w821 = false := by
  decide +kernel

theorem s822 : optimized 6 0 w822 = false := by
  decide +kernel

theorem s823 : optimized 6 0 w823 = false := by
  decide +kernel

theorem s824 : optimized 6 1 w824 = false := by
  decide +kernel

theorem s825 : optimized 6 0 w825 = false := by
  decide +kernel

theorem s826 : optimized 6 0 w826 = false := by
  decide +kernel

theorem s827 : optimized 6 0 w827 = false := by
  decide +kernel

theorem s828 : optimized 6 0 w828 = false := by
  decide +kernel

theorem s829 : optimized 6 0 w829 = false := by
  decide +kernel

theorem s830 : optimized 6 0 w830 = false := by
  decide +kernel

theorem s831 : optimized 6 0 w831 = false := by
  decide +kernel

theorem s832 : optimized 6 0 w832 = false := by
  decide +kernel

theorem s833 : optimized 6 0 w833 = false := by
  decide +kernel

theorem s834 : optimized 6 0 w834 = false := by
  decide +kernel

theorem s835 : optimized 6 0 w835 = false := by
  decide +kernel

theorem s836 : optimized 6 0 w836 = false := by
  decide +kernel

theorem s837 : optimized 6 0 w837 = false := by
  decide +kernel

theorem s838 : optimized 6 0 w838 = false := by
  decide +kernel

theorem s839 : optimized 6 0 w839 = false := by
  decide +kernel

theorem s840 : optimized 6 0 w840 = false := by
  decide +kernel

theorem s841 : optimized 6 0 w841 = false := by
  decide +kernel

theorem s842 : optimized 6 0 w842 = false := by
  decide +kernel

theorem s843 : optimized 6 0 w843 = false := by
  decide +kernel

theorem s844 : optimized 6 0 w844 = false := by
  decide +kernel

theorem s845 : optimized 6 0 w845 = false := by
  decide +kernel

theorem s846 : optimized 6 0 w846 = false := by
  decide +kernel

theorem s847 : optimized 6 0 w847 = false := by
  decide +kernel

theorem s848 : optimized 6 0 w848 = false := by
  decide +kernel

theorem s849 : optimized 6 0 w849 = false := by
  decide +kernel

theorem s850 : optimized 6 0 w850 = false := by
  decide +kernel

theorem s851 : optimized 6 0 w851 = false := by
  decide +kernel

theorem s852 : optimized 6 0 w852 = false := by
  decide +kernel

theorem s853 : optimized 6 0 w853 = false := by
  decide +kernel

theorem s854 : optimized 6 0 w854 = false := by
  decide +kernel

theorem s855 : optimized 6 0 w855 = false := by
  decide +kernel

theorem s856 : optimized 6 0 w856 = false := by
  decide +kernel

theorem s857 : optimized 6 0 w857 = false := by
  decide +kernel

theorem s858 : optimized 6 0 w858 = false := by
  decide +kernel

theorem s859 : optimized 6 0 w859 = false := by
  decide +kernel

theorem s860 : optimized 6 0 w860 = false := by
  decide +kernel

theorem s861 : optimized 6 0 w861 = false := by
  decide +kernel

theorem s862 : optimized 6 0 w862 = false := by
  decide +kernel

theorem s863 : optimized 6 0 w863 = false := by
  decide +kernel

theorem s864 : optimized 6 0 w864 = false := by
  decide +kernel

theorem s865 : optimized 6 1 w865 = false := by
  decide +kernel

theorem s866 : optimized 6 0 w866 = false := by
  decide +kernel

theorem s867 : optimized 6 0 w867 = false := by
  decide +kernel

theorem s868 : optimized 6 0 w868 = false := by
  decide +kernel

theorem s869 : optimized 6 1 w869 = false := by
  decide +kernel

theorem s870 : optimized 6 0 w870 = false := by
  decide +kernel

theorem s871 : optimized 6 0 w871 = false := by
  decide +kernel

theorem s872 : optimized 6 1 w872 = false := by
  decide +kernel

theorem s873 : optimized 6 0 w873 = false := by
  decide +kernel

theorem s874 : optimized 6 0 w874 = false := by
  decide +kernel

theorem s875 : optimized 6 0 w875 = false := by
  decide +kernel

theorem s876 : optimized 6 0 w876 = false := by
  decide +kernel

theorem s877 : optimized 6 0 w877 = false := by
  decide +kernel

theorem s878 : optimized 6 0 w878 = false := by
  decide +kernel

theorem s879 : optimized 6 0 w879 = false := by
  decide +kernel

theorem s880 : optimized 6 0 w880 = false := by
  decide +kernel

theorem s881 : optimized 6 0 w881 = false := by
  decide +kernel

theorem s882 : optimized 6 0 w882 = false := by
  decide +kernel

theorem s883 : optimized 6 0 w883 = false := by
  decide +kernel

theorem s884 : optimized 6 0 w884 = false := by
  decide +kernel

theorem s885 : optimized 6 0 w885 = false := by
  decide +kernel

theorem s886 : optimized 6 0 w886 = false := by
  decide +kernel

theorem s887 : optimized 6 0 w887 = false := by
  decide +kernel

theorem s888 : optimized 6 0 w888 = false := by
  decide +kernel

theorem s889 : optimized 6 0 w889 = false := by
  decide +kernel

theorem s890 : optimized 6 0 w890 = false := by
  decide +kernel

theorem s891 : optimized 6 0 w891 = false := by
  decide +kernel

theorem s892 : optimized 6 0 w892 = false := by
  decide +kernel

theorem s893 : optimized 6 0 w893 = false := by
  decide +kernel

theorem s894 : optimized 6 0 w894 = false := by
  decide +kernel

theorem s895 : optimized 6 0 w895 = false := by
  decide +kernel

theorem s896 : optimized 6 0 w896 = false := by
  decide +kernel

theorem s897 : optimized 6 0 w897 = false := by
  decide +kernel

theorem s898 : optimized 6 0 w898 = false := by
  decide +kernel

theorem s899 : optimized 6 0 w899 = false := by
  decide +kernel

theorem s900 : optimized 6 0 w900 = false := by
  decide +kernel

theorem s901 : optimized 6 0 w901 = false := by
  decide +kernel

theorem s902 : optimized 6 0 w902 = false := by
  decide +kernel

theorem s903 : optimized 6 0 w903 = false := by
  decide +kernel

theorem s904 : optimized 6 0 w904 = false := by
  decide +kernel

theorem s905 : optimized 6 0 w905 = false := by
  decide +kernel

theorem s906 : optimized 6 0 w906 = false := by
  decide +kernel

theorem s907 : optimized 6 0 w907 = false := by
  decide +kernel

theorem s908 : optimized 6 0 w908 = false := by
  decide +kernel

theorem s909 : optimized 6 0 w909 = false := by
  decide +kernel

theorem s910 : optimized 6 0 w910 = false := by
  decide +kernel

theorem s911 : optimized 6 0 w911 = false := by
  decide +kernel

theorem s912 : optimized 6 0 w912 = false := by
  decide +kernel

theorem s913 : optimized 6 0 w913 = false := by
  decide +kernel

theorem s914 : optimized 6 0 w914 = false := by
  decide +kernel

theorem s915 : optimized 6 1 w915 = false := by
  decide +kernel

theorem s916 : optimized 6 0 w916 = false := by
  decide +kernel

theorem s917 : optimized 6 0 w917 = false := by
  decide +kernel

theorem s918 : optimized 6 0 w918 = false := by
  decide +kernel

theorem s919 : optimized 6 1 w919 = false := by
  decide +kernel

theorem s920 : optimized 6 0 w920 = false := by
  decide +kernel

theorem s921 : optimized 6 0 w921 = false := by
  decide +kernel

theorem s922 : optimized 6 0 w922 = false := by
  decide +kernel

theorem s923 : optimized 6 0 w923 = false := by
  decide +kernel

theorem s924 : optimized 6 1 w924 = false := by
  decide +kernel

theorem s925 : optimized 6 0 w925 = false := by
  decide +kernel

theorem s926 : optimized 6 0 w926 = false := by
  decide +kernel

theorem s927 : optimized 6 0 w927 = false := by
  decide +kernel

theorem s928 : optimized 6 0 w928 = false := by
  decide +kernel

theorem s929 : optimized 6 0 w929 = false := by
  decide +kernel

theorem s930 : optimized 6 0 w930 = false := by
  decide +kernel

theorem s931 : optimized 6 0 w931 = false := by
  decide +kernel

theorem s932 : optimized 6 0 w932 = false := by
  decide +kernel

theorem s933 : optimized 6 0 w933 = false := by
  decide +kernel

theorem s934 : optimized 6 0 w934 = false := by
  decide +kernel

theorem s935 : optimized 6 0 w935 = false := by
  decide +kernel

theorem s936 : optimized 6 0 w936 = false := by
  decide +kernel

theorem s937 : optimized 6 0 w937 = false := by
  decide +kernel

theorem s938 : optimized 6 0 w938 = false := by
  decide +kernel

theorem s939 : optimized 6 0 w939 = false := by
  decide +kernel

theorem s940 : optimized 6 0 w940 = false := by
  decide +kernel

theorem s941 : optimized 6 0 w941 = false := by
  decide +kernel

theorem s942 : optimized 6 0 w942 = false := by
  decide +kernel

theorem s943 : optimized 6 0 w943 = false := by
  decide +kernel

theorem s944 : optimized 6 0 w944 = false := by
  decide +kernel

theorem s945 : optimized 6 0 w945 = false := by
  decide +kernel

theorem s946 : optimized 6 0 w946 = false := by
  decide +kernel

theorem s947 : optimized 6 0 w947 = false := by
  decide +kernel

theorem s948 : optimized 6 0 w948 = false := by
  decide +kernel

theorem s949 : optimized 6 0 w949 = false := by
  decide +kernel

theorem s950 : optimized 6 0 w950 = false := by
  decide +kernel

theorem s951 : optimized 6 1 w951 = false := by
  decide +kernel

theorem s952 : optimized 6 0 w952 = false := by
  decide +kernel

theorem s953 : optimized 6 0 w953 = false := by
  decide +kernel

theorem s954 : optimized 6 1 w954 = false := by
  decide +kernel

theorem s955 : optimized 6 0 w955 = false := by
  decide +kernel

theorem s956 : optimized 6 0 w956 = false := by
  decide +kernel

theorem s957 : optimized 6 0 w957 = false := by
  decide +kernel

theorem s958 : optimized 6 0 w958 = false := by
  decide +kernel

theorem s959 : optimized 6 0 w959 = false := by
  decide +kernel

theorem s960 : optimized 6 0 w960 = false := by
  decide +kernel

theorem s961 : optimized 6 0 w961 = false := by
  decide +kernel

theorem s962 : optimized 6 0 w962 = false := by
  decide +kernel

theorem s963 : optimized 6 0 w963 = false := by
  decide +kernel

theorem s964 : optimized 6 0 w964 = false := by
  decide +kernel

theorem s965 : optimized 6 0 w965 = false := by
  decide +kernel

theorem s966 : optimized 6 0 w966 = false := by
  decide +kernel

theorem s967 : optimized 6 0 w967 = false := by
  decide +kernel

theorem s968 : optimized 6 0 w968 = false := by
  decide +kernel

theorem s969 : optimized 6 1 w969 = false := by
  decide +kernel

theorem s970 : optimized 6 0 w970 = false := by
  decide +kernel

theorem s971 : optimized 6 0 w971 = false := by
  decide +kernel

theorem s972 : optimized 6 0 w972 = false := by
  decide +kernel

theorem s973 : optimized 6 1 w973 = false := by
  decide +kernel

theorem s974 : optimized 6 0 w974 = false := by
  decide +kernel

theorem s975 : optimized 6 0 w975 = false := by
  decide +kernel

theorem s976 : optimized 6 1 w976 = false := by
  decide +kernel

theorem s977 : optimized 6 0 w977 = false := by
  decide +kernel

theorem s978 : optimized 6 0 w978 = false := by
  decide +kernel

theorem s979 : optimized 6 0 w979 = false := by
  decide +kernel

theorem s980 : optimized 6 0 w980 = false := by
  decide +kernel

theorem s981 : optimized 6 0 w981 = false := by
  decide +kernel

theorem s982 : optimized 6 0 w982 = false := by
  decide +kernel

theorem s983 : optimized 6 0 w983 = false := by
  decide +kernel

theorem s984 : optimized 6 0 w984 = false := by
  decide +kernel

theorem s985 : optimized 6 0 w985 = false := by
  decide +kernel

theorem s986 : optimized 6 1 w986 = false := by
  decide +kernel

theorem s987 : optimized 6 0 w987 = false := by
  decide +kernel

theorem s988 : optimized 6 0 w988 = false := by
  decide +kernel

theorem s989 : optimized 6 1 w989 = false := by
  decide +kernel

theorem s990 : optimized 6 0 w990 = false := by
  decide +kernel

theorem s991 : optimized 6 0 w991 = false := by
  decide +kernel

theorem s992 : optimized 6 0 w992 = false := by
  decide +kernel

theorem s993 : optimized 6 0 w993 = false := by
  decide +kernel

theorem s994 : optimized 6 0 w994 = false := by
  decide +kernel

theorem s995 : optimized 6 0 w995 = false := by
  decide +kernel

theorem s996 : optimized 6 0 w996 = false := by
  decide +kernel

theorem s997 : optimized 6 1 w997 = false := by
  decide +kernel

theorem s998 : optimized 6 0 w998 = false := by
  decide +kernel

theorem s999 : optimized 6 0 w999 = false := by
  decide +kernel

theorem s1000 : optimized 6 1 w1000 = false := by
  decide +kernel

theorem s1001 : optimized 6 0 w1001 = false := by
  decide +kernel

theorem s1002 : optimized 6 0 w1002 = false := by
  decide +kernel

theorem s1003 : optimized 6 0 w1003 = false := by
  decide +kernel

theorem s1004 : optimized 6 1 w1004 = false := by
  decide +kernel

theorem s1005 : optimized 6 0 w1005 = false := by
  decide +kernel

theorem s1006 : optimized 6 0 w1006 = false := by
  decide +kernel

theorem s1007 : optimized 6 0 w1007 = false := by
  decide +kernel

theorem s1008 : optimized 6 1 w1008 = false := by
  decide +kernel

theorem s1009 : optimized 6 0 w1009 = false := by
  decide +kernel

theorem s1010 : optimized 6 0 w1010 = false := by
  decide +kernel

theorem s1011 : optimized 6 0 w1011 = false := by
  decide +kernel

theorem s1012 : optimized 6 0 w1012 = false := by
  decide +kernel

theorem s1013 : optimized 6 0 w1013 = false := by
  decide +kernel

theorem s1014 : optimized 6 0 w1014 = false := by
  decide +kernel

theorem s1015 : optimized 6 0 w1015 = false := by
  decide +kernel

theorem s1016 : optimized 6 0 w1016 = false := by
  decide +kernel

theorem s1017 : optimized 6 0 w1017 = false := by
  decide +kernel

theorem s1018 : optimized 6 0 w1018 = false := by
  decide +kernel

theorem s1019 : optimized 6 0 w1019 = false := by
  decide +kernel

theorem s1020 : optimized 6 0 w1020 = false := by
  decide +kernel

theorem s1021 : optimized 6 0 w1021 = false := by
  decide +kernel

theorem s1022 : optimized 6 0 w1022 = false := by
  decide +kernel

theorem s1023 : optimized 6 0 w1023 = false := by
  decide +kernel

theorem s1024 : optimized 6 0 w1024 = false := by
  decide +kernel

theorem s1025 : optimized 6 0 w1025 = false := by
  decide +kernel

theorem s1026 : optimized 6 0 w1026 = false := by
  decide +kernel

theorem s1027 : optimized 6 1 w1027 = false := by
  decide +kernel

theorem s1028 : optimized 6 0 w1028 = false := by
  decide +kernel

theorem s1029 : optimized 6 0 w1029 = false := by
  decide +kernel

theorem s1030 : optimized 6 0 w1030 = false := by
  decide +kernel

theorem s1031 : optimized 6 1 w1031 = false := by
  decide +kernel

theorem s1032 : optimized 6 0 w1032 = false := by
  decide +kernel

theorem s1033 : optimized 6 0 w1033 = false := by
  decide +kernel

theorem s1034 : optimized 6 1 w1034 = false := by
  decide +kernel

theorem s1035 : optimized 6 0 w1035 = false := by
  decide +kernel

theorem s1036 : optimized 6 0 w1036 = false := by
  decide +kernel

theorem s1037 : optimized 6 0 w1037 = false := by
  decide +kernel

theorem s1038 : optimized 6 0 w1038 = false := by
  decide +kernel

theorem s1039 : optimized 6 0 w1039 = false := by
  decide +kernel

theorem s1040 : optimized 6 0 w1040 = false := by
  decide +kernel

theorem s1041 : optimized 6 0 w1041 = false := by
  decide +kernel

theorem s1042 : optimized 6 0 w1042 = false := by
  decide +kernel

theorem s1043 : optimized 6 0 w1043 = false := by
  decide +kernel

theorem s1044 : optimized 6 0 w1044 = false := by
  decide +kernel

theorem s1045 : optimized 6 0 w1045 = false := by
  decide +kernel

theorem s1046 : optimized 6 0 w1046 = false := by
  decide +kernel

theorem s1047 : optimized 6 0 w1047 = false := by
  decide +kernel

theorem s1048 : optimized 6 0 w1048 = false := by
  decide +kernel

theorem s1049 : optimized 6 0 w1049 = false := by
  decide +kernel

theorem s1050 : optimized 6 0 w1050 = false := by
  decide +kernel

theorem s1051 : optimized 6 0 w1051 = false := by
  decide +kernel

theorem s1052 : optimized 6 0 w1052 = false := by
  decide +kernel

theorem s1053 : optimized 6 0 w1053 = false := by
  decide +kernel

theorem s1054 : optimized 6 0 w1054 = false := by
  decide +kernel

theorem s1055 : optimized 6 0 w1055 = false := by
  decide +kernel

theorem s1056 : optimized 6 0 w1056 = false := by
  decide +kernel

theorem s1057 : optimized 6 0 w1057 = false := by
  decide +kernel

theorem s1058 : optimized 6 0 w1058 = false := by
  decide +kernel

theorem s1059 : optimized 6 0 w1059 = false := by
  decide +kernel

theorem s1060 : optimized 6 0 w1060 = false := by
  decide +kernel

theorem s1061 : optimized 6 0 w1061 = false := by
  decide +kernel

theorem s1062 : optimized 6 0 w1062 = false := by
  decide +kernel

theorem s1063 : optimized 6 0 w1063 = false := by
  decide +kernel

theorem s1064 : optimized 6 0 w1064 = false := by
  decide +kernel

theorem s1065 : optimized 6 0 w1065 = false := by
  decide +kernel

theorem s1066 : optimized 6 1 w1066 = false := by
  decide +kernel

theorem s1067 : optimized 6 0 w1067 = false := by
  decide +kernel

theorem s1068 : optimized 6 0 w1068 = false := by
  decide +kernel

theorem s1069 : optimized 6 1 w1069 = false := by
  decide +kernel

theorem s1070 : optimized 6 0 w1070 = false := by
  decide +kernel

theorem s1071 : optimized 6 0 w1071 = false := by
  decide +kernel

theorem s1072 : optimized 6 0 w1072 = false := by
  decide +kernel

theorem s1073 : optimized 6 1 w1073 = false := by
  decide +kernel

theorem s1074 : optimized 6 0 w1074 = false := by
  decide +kernel

theorem s1075 : optimized 6 0 w1075 = false := by
  decide +kernel

theorem s1076 : optimized 6 0 w1076 = false := by
  decide +kernel

theorem s1077 : optimized 6 1 w1077 = false := by
  decide +kernel

theorem s1078 : optimized 6 0 w1078 = false := by
  decide +kernel

theorem s1079 : optimized 6 0 w1079 = false := by
  decide +kernel

theorem s1080 : optimized 6 1 w1080 = false := by
  decide +kernel

theorem s1081 : optimized 6 0 w1081 = false := by
  decide +kernel

theorem s1082 : optimized 6 0 w1082 = false := by
  decide +kernel

theorem s1083 : optimized 6 0 w1083 = false := by
  decide +kernel

theorem s1084 : optimized 6 0 w1084 = false := by
  decide +kernel

theorem s1085 : optimized 6 0 w1085 = false := by
  decide +kernel

theorem s1086 : optimized 6 0 w1086 = false := by
  decide +kernel

theorem s1087 : optimized 6 0 w1087 = false := by
  decide +kernel

theorem s1088 : optimized 6 0 w1088 = false := by
  decide +kernel

theorem s1089 : optimized 6 0 w1089 = false := by
  decide +kernel

theorem s1090 : optimized 6 0 w1090 = false := by
  decide +kernel

theorem s1091 : optimized 6 0 w1091 = false := by
  decide +kernel

theorem s1092 : optimized 6 0 w1092 = false := by
  decide +kernel

theorem s1093 : optimized 6 1 w1093 = false := by
  decide +kernel

theorem s1094 : optimized 6 0 w1094 = false := by
  decide +kernel

theorem s1095 : optimized 6 0 w1095 = false := by
  decide +kernel

theorem s1096 : optimized 6 1 w1096 = false := by
  decide +kernel

theorem s1097 : optimized 6 0 w1097 = false := by
  decide +kernel

theorem s1098 : optimized 6 0 w1098 = false := by
  decide +kernel

theorem s1099 : optimized 6 0 w1099 = false := by
  decide +kernel

theorem s1100 : optimized 6 0 w1100 = false := by
  decide +kernel

theorem s1101 : optimized 6 0 w1101 = false := by
  decide +kernel

theorem s1102 : optimized 6 0 w1102 = false := by
  decide +kernel

theorem s1103 : optimized 6 0 w1103 = false := by
  decide +kernel

theorem s1104 : optimized 6 0 w1104 = false := by
  decide +kernel

theorem s1105 : optimized 6 0 w1105 = false := by
  decide +kernel

theorem s1106 : optimized 6 0 w1106 = false := by
  decide +kernel

theorem s1107 : optimized 6 0 w1107 = false := by
  decide +kernel

theorem s1108 : optimized 6 0 w1108 = false := by
  decide +kernel

theorem s1109 : optimized 6 0 w1109 = false := by
  decide +kernel

theorem s1110 : optimized 6 0 w1110 = false := by
  decide +kernel

theorem s1111 : optimized 6 0 w1111 = false := by
  decide +kernel

theorem s1112 : optimized 6 0 w1112 = false := by
  decide +kernel

theorem s1113 : optimized 6 0 w1113 = false := by
  decide +kernel

theorem s1114 : optimized 6 0 w1114 = false := by
  decide +kernel

theorem s1115 : optimized 6 0 w1115 = false := by
  decide +kernel

theorem s1116 : optimized 6 0 w1116 = false := by
  decide +kernel

theorem s1117 : optimized 6 0 w1117 = false := by
  decide +kernel

theorem s1118 : optimized 6 0 w1118 = false := by
  decide +kernel

theorem s1119 : optimized 6 0 w1119 = false := by
  decide +kernel

theorem s1120 : optimized 6 1 w1120 = false := by
  decide +kernel

theorem s1121 : optimized 6 0 w1121 = false := by
  decide +kernel

theorem s1122 : optimized 6 0 w1122 = false := by
  decide +kernel

theorem s1123 : optimized 6 1 w1123 = false := by
  decide +kernel

theorem s1124 : optimized 6 0 w1124 = false := by
  decide +kernel

theorem s1125 : optimized 6 0 w1125 = false := by
  decide +kernel

theorem s1126 : optimized 6 0 w1126 = false := by
  decide +kernel

theorem s1127 : optimized 6 0 w1127 = false := by
  decide +kernel

theorem s1128 : optimized 6 1 w1128 = false := by
  decide +kernel

theorem s1129 : optimized 6 0 w1129 = false := by
  decide +kernel

theorem s1130 : optimized 6 0 w1130 = false := by
  decide +kernel

theorem s1131 : optimized 6 0 w1131 = false := by
  decide +kernel

theorem s1132 : optimized 6 0 w1132 = false := by
  decide +kernel

theorem s1133 : optimized 6 0 w1133 = false := by
  decide +kernel

theorem s1134 : optimized 6 0 w1134 = false := by
  decide +kernel

theorem s1135 : optimized 6 0 w1135 = false := by
  decide +kernel

theorem s1136 : optimized 6 0 w1136 = false := by
  decide +kernel

theorem s1137 : optimized 6 0 w1137 = false := by
  decide +kernel

theorem s1138 : optimized 6 0 w1138 = false := by
  decide +kernel

theorem s1139 : optimized 6 0 w1139 = false := by
  decide +kernel

theorem s1140 : optimized 6 0 w1140 = false := by
  decide +kernel

theorem s1141 : optimized 6 0 w1141 = false := by
  decide +kernel

theorem s1142 : optimized 6 0 w1142 = false := by
  decide +kernel

theorem s1143 : optimized 6 0 w1143 = false := by
  decide +kernel

theorem s1144 : optimized 6 0 w1144 = false := by
  decide +kernel

theorem s1145 : optimized 6 1 w1145 = false := by
  decide +kernel

theorem s1146 : optimized 6 0 w1146 = false := by
  decide +kernel

theorem s1147 : optimized 6 0 w1147 = false := by
  decide +kernel

theorem s1148 : optimized 6 0 w1148 = false := by
  decide +kernel

theorem s1149 : optimized 6 1 w1149 = false := by
  decide +kernel

theorem s1150 : optimized 6 0 w1150 = false := by
  decide +kernel

theorem s1151 : optimized 6 0 w1151 = false := by
  decide +kernel

theorem s1152 : optimized 6 0 w1152 = false := by
  decide +kernel

theorem s1153 : optimized 6 0 w1153 = false := by
  decide +kernel

theorem s1154 : optimized 6 0 w1154 = false := by
  decide +kernel

theorem s1155 : optimized 6 0 w1155 = false := by
  decide +kernel

theorem s1156 : optimized 6 0 w1156 = false := by
  decide +kernel

theorem s1157 : optimized 6 0 w1157 = false := by
  decide +kernel

theorem s1158 : optimized 6 0 w1158 = false := by
  decide +kernel

theorem s1159 : optimized 6 0 w1159 = false := by
  decide +kernel

theorem s1160 : optimized 6 0 w1160 = false := by
  decide +kernel

theorem s1161 : optimized 6 0 w1161 = false := by
  decide +kernel

theorem s1162 : optimized 6 1 w1162 = false := by
  decide +kernel

theorem s1163 : optimized 6 0 w1163 = false := by
  decide +kernel

theorem s1164 : optimized 6 0 w1164 = false := by
  decide +kernel

theorem s1165 : optimized 6 0 w1165 = false := by
  decide +kernel

theorem s1166 : optimized 6 0 w1166 = false := by
  decide +kernel

theorem s1167 : optimized 6 0 w1167 = false := by
  decide +kernel

theorem s1168 : optimized 6 0 w1168 = false := by
  decide +kernel

theorem s1169 : optimized 6 0 w1169 = false := by
  decide +kernel

theorem s1170 : optimized 6 0 w1170 = false := by
  decide +kernel

theorem s1171 : optimized 6 0 w1171 = false := by
  decide +kernel

theorem s1172 : optimized 6 0 w1172 = false := by
  decide +kernel

theorem s1173 : optimized 6 0 w1173 = false := by
  decide +kernel

theorem s1174 : optimized 6 0 w1174 = false := by
  decide +kernel

theorem s1175 : optimized 6 0 w1175 = false := by
  decide +kernel

theorem s1176 : optimized 6 0 w1176 = false := by
  decide +kernel

theorem s1177 : optimized 6 0 w1177 = false := by
  decide +kernel

theorem s1178 : optimized 6 0 w1178 = false := by
  decide +kernel

theorem s1179 : optimized 6 0 w1179 = false := by
  decide +kernel

theorem s1180 : optimized 6 0 w1180 = false := by
  decide +kernel

theorem s1181 : optimized 6 0 w1181 = false := by
  decide +kernel

theorem s1182 : optimized 6 0 w1182 = false := by
  decide +kernel

theorem s1183 : optimized 6 0 w1183 = false := by
  decide +kernel

theorem s1184 : optimized 6 0 w1184 = false := by
  decide +kernel

theorem s1185 : optimized 6 0 w1185 = false := by
  decide +kernel

theorem s1186 : optimized 6 0 w1186 = false := by
  decide +kernel

theorem s1187 : optimized 6 0 w1187 = false := by
  decide +kernel

theorem s1188 : optimized 6 0 w1188 = false := by
  decide +kernel

theorem s1189 : optimized 6 0 w1189 = false := by
  decide +kernel

theorem s1190 : optimized 6 0 w1190 = false := by
  decide +kernel

theorem s1191 : optimized 6 0 w1191 = false := by
  decide +kernel

theorem s1192 : optimized 6 0 w1192 = false := by
  decide +kernel

theorem s1193 : optimized 6 0 w1193 = false := by
  decide +kernel

theorem s1194 : optimized 6 0 w1194 = false := by
  decide +kernel

theorem s1195 : optimized 6 1 w1195 = false := by
  decide +kernel

theorem s1196 : optimized 6 0 w1196 = false := by
  decide +kernel

theorem s1197 : optimized 6 0 w1197 = false := by
  decide +kernel

theorem s1198 : optimized 6 0 w1198 = false := by
  decide +kernel

theorem s1199 : optimized 6 0 w1199 = false := by
  decide +kernel

theorem s1200 : optimized 6 0 w1200 = false := by
  decide +kernel

theorem s1201 : optimized 6 0 w1201 = false := by
  decide +kernel

theorem s1202 : optimized 6 1 w1202 = false := by
  decide +kernel

theorem s1203 : optimized 6 0 w1203 = false := by
  decide +kernel

theorem s1204 : optimized 6 0 w1204 = false := by
  decide +kernel

theorem s1205 : optimized 6 0 w1205 = false := by
  decide +kernel

theorem s1206 : optimized 6 0 w1206 = false := by
  decide +kernel

theorem s1207 : optimized 6 0 w1207 = false := by
  decide +kernel

theorem s1208 : optimized 6 0 w1208 = false := by
  decide +kernel

theorem s1209 : optimized 6 0 w1209 = false := by
  decide +kernel

theorem s1210 : optimized 6 0 w1210 = false := by
  decide +kernel

theorem s1211 : optimized 6 0 w1211 = false := by
  decide +kernel

theorem s1212 : optimized 6 0 w1212 = false := by
  decide +kernel

theorem s1213 : optimized 6 0 w1213 = false := by
  decide +kernel

theorem s1214 : optimized 6 0 w1214 = false := by
  decide +kernel

theorem s1215 : optimized 6 0 w1215 = false := by
  decide +kernel

theorem s1216 : optimized 6 0 w1216 = false := by
  decide +kernel

theorem s1217 : optimized 6 0 w1217 = false := by
  decide +kernel

theorem s1218 : optimized 6 0 w1218 = false := by
  decide +kernel

theorem s1219 : optimized 6 0 w1219 = false := by
  decide +kernel

theorem s1220 : optimized 6 0 w1220 = false := by
  decide +kernel

theorem s1221 : optimized 6 0 w1221 = false := by
  decide +kernel

theorem s1222 : optimized 6 0 w1222 = false := by
  decide +kernel

theorem s1223 : optimized 6 0 w1223 = false := by
  decide +kernel

theorem s1224 : optimized 6 0 w1224 = false := by
  decide +kernel

theorem s1225 : optimized 6 1 w1225 = false := by
  decide +kernel

theorem s1226 : optimized 6 0 w1226 = false := by
  decide +kernel

theorem s1227 : optimized 6 0 w1227 = false := by
  decide +kernel

theorem s1228 : optimized 6 0 w1228 = false := by
  decide +kernel

theorem s1229 : optimized 6 0 w1229 = false := by
  decide +kernel

theorem s1230 : optimized 6 0 w1230 = false := by
  decide +kernel

theorem s1231 : optimized 6 0 w1231 = false := by
  decide +kernel

theorem s1232 : optimized 6 0 w1232 = false := by
  decide +kernel

theorem s1233 : optimized 6 0 w1233 = false := by
  decide +kernel

theorem s1234 : optimized 6 0 w1234 = false := by
  decide +kernel

theorem s1235 : optimized 6 0 w1235 = false := by
  decide +kernel

theorem s1236 : optimized 6 0 w1236 = false := by
  decide +kernel

theorem s1237 : optimized 6 0 w1237 = false := by
  decide +kernel

theorem s1238 : optimized 6 0 w1238 = false := by
  decide +kernel

theorem s1239 : optimized 6 0 w1239 = false := by
  decide +kernel

theorem s1240 : optimized 6 0 w1240 = false := by
  decide +kernel

theorem s1241 : optimized 6 0 w1241 = false := by
  decide +kernel

theorem s1242 : optimized 6 0 w1242 = false := by
  decide +kernel

theorem s1243 : optimized 6 0 w1243 = false := by
  decide +kernel

theorem s1244 : optimized 6 0 w1244 = false := by
  decide +kernel

theorem s1245 : optimized 6 0 w1245 = false := by
  decide +kernel

theorem s1246 : optimized 6 0 w1246 = false := by
  decide +kernel

theorem s1247 : optimized 6 0 w1247 = false := by
  decide +kernel

theorem s1248 : optimized 6 0 w1248 = false := by
  decide +kernel

theorem s1249 : optimized 6 0 w1249 = false := by
  decide +kernel

theorem s1250 : optimized 6 0 w1250 = false := by
  decide +kernel

theorem s1251 : optimized 6 0 w1251 = false := by
  decide +kernel

theorem s1252 : optimized 6 0 w1252 = false := by
  decide +kernel

theorem s1253 : optimized 6 0 w1253 = false := by
  decide +kernel

theorem s1254 : optimized 6 0 w1254 = false := by
  decide +kernel

theorem s1255 : optimized 6 0 w1255 = false := by
  decide +kernel

theorem s1256 : optimized 6 1 w1256 = false := by
  decide +kernel

theorem s1257 : optimized 6 0 w1257 = false := by
  decide +kernel

theorem s1258 : optimized 6 0 w1258 = false := by
  decide +kernel

theorem s1259 : optimized 6 1 w1259 = false := by
  decide +kernel

theorem s1260 : optimized 6 0 w1260 = false := by
  decide +kernel

theorem s1261 : optimized 6 0 w1261 = false := by
  decide +kernel

theorem s1262 : optimized 6 0 w1262 = false := by
  decide +kernel

theorem s1263 : optimized 6 0 w1263 = false := by
  decide +kernel

theorem s1264 : optimized 6 0 w1264 = false := by
  decide +kernel

theorem s1265 : optimized 6 0 w1265 = false := by
  decide +kernel

theorem s1266 : optimized 6 0 w1266 = false := by
  decide +kernel

theorem s1267 : optimized 6 0 w1267 = false := by
  decide +kernel

theorem s1268 : optimized 6 0 w1268 = false := by
  decide +kernel

theorem s1269 : optimized 6 0 w1269 = false := by
  decide +kernel

theorem s1270 : optimized 6 0 w1270 = false := by
  decide +kernel

theorem s1271 : optimized 6 1 w1271 = false := by
  decide +kernel

theorem s1272 : optimized 6 0 w1272 = false := by
  decide +kernel

theorem s1273 : optimized 6 0 w1273 = false := by
  decide +kernel

theorem s1274 : optimized 6 0 w1274 = false := by
  decide +kernel

theorem s1275 : optimized 6 1 w1275 = false := by
  decide +kernel

theorem s1276 : optimized 6 0 w1276 = false := by
  decide +kernel

theorem s1277 : optimized 6 0 w1277 = false := by
  decide +kernel

theorem s1278 : optimized 6 1 w1278 = false := by
  decide +kernel

theorem s1279 : optimized 6 0 w1279 = false := by
  decide +kernel

theorem s1280 : optimized 6 0 w1280 = false := by
  decide +kernel

theorem s1281 : optimized 6 0 w1281 = false := by
  decide +kernel

theorem s1282 : optimized 6 0 w1282 = false := by
  decide +kernel

theorem s1283 : optimized 6 0 w1283 = false := by
  decide +kernel

theorem s1284 : optimized 6 0 w1284 = false := by
  decide +kernel

theorem s1285 : optimized 6 0 w1285 = false := by
  decide +kernel

theorem s1286 : optimized 6 0 w1286 = false := by
  decide +kernel

theorem s1287 : optimized 6 0 w1287 = false := by
  decide +kernel

theorem s1288 : optimized 6 0 w1288 = false := by
  decide +kernel

theorem s1289 : optimized 6 0 w1289 = false := by
  decide +kernel

theorem s1290 : optimized 6 0 w1290 = false := by
  decide +kernel

theorem s1291 : optimized 6 0 w1291 = false := by
  decide +kernel

theorem s1292 : optimized 6 0 w1292 = false := by
  decide +kernel

theorem s1293 : optimized 6 0 w1293 = false := by
  decide +kernel

theorem s1294 : optimized 6 0 w1294 = false := by
  decide +kernel

theorem s1295 : optimized 6 0 w1295 = false := by
  decide +kernel

theorem s1296 : optimized 6 0 w1296 = false := by
  decide +kernel

theorem s1297 : optimized 6 0 w1297 = false := by
  decide +kernel

theorem s1298 : optimized 6 0 w1298 = false := by
  decide +kernel

theorem s1299 : optimized 6 0 w1299 = false := by
  decide +kernel

theorem s1300 : optimized 6 1 w1300 = false := by
  decide +kernel

theorem s1301 : optimized 6 0 w1301 = false := by
  decide +kernel

theorem s1302 : optimized 6 0 w1302 = false := by
  decide +kernel

theorem s1303 : optimized 6 0 w1303 = false := by
  decide +kernel

theorem s1304 : optimized 6 0 w1304 = false := by
  decide +kernel

theorem s1305 : optimized 6 0 w1305 = false := by
  decide +kernel

theorem s1306 : optimized 6 0 w1306 = false := by
  decide +kernel

theorem s1307 : optimized 6 0 w1307 = false := by
  decide +kernel

theorem s1308 : optimized 6 0 w1308 = false := by
  decide +kernel

theorem s1309 : optimized 6 0 w1309 = false := by
  decide +kernel

theorem s1310 : optimized 6 0 w1310 = false := by
  decide +kernel

theorem s1311 : optimized 6 0 w1311 = false := by
  decide +kernel

theorem s1312 : optimized 6 0 w1312 = false := by
  decide +kernel

theorem s1313 : optimized 6 0 w1313 = false := by
  decide +kernel

theorem s1314 : optimized 6 0 w1314 = false := by
  decide +kernel

theorem s1315 : optimized 6 0 w1315 = false := by
  decide +kernel

theorem s1316 : optimized 6 0 w1316 = false := by
  decide +kernel

theorem s1317 : optimized 6 0 w1317 = false := by
  decide +kernel

theorem s1318 : optimized 6 0 w1318 = false := by
  decide +kernel

theorem s1319 : optimized 6 0 w1319 = false := by
  decide +kernel

theorem s1320 : optimized 6 0 w1320 = false := by
  decide +kernel

theorem s1321 : optimized 6 0 w1321 = false := by
  decide +kernel

theorem s1322 : optimized 6 0 w1322 = false := by
  decide +kernel

theorem s1323 : optimized 6 1 w1323 = false := by
  decide +kernel

theorem s1324 : optimized 6 0 w1324 = false := by
  decide +kernel

theorem s1325 : optimized 6 0 w1325 = false := by
  decide +kernel

theorem s1326 : optimized 6 0 w1326 = false := by
  decide +kernel

theorem s1327 : optimized 6 0 w1327 = false := by
  decide +kernel

theorem s1328 : optimized 6 0 w1328 = false := by
  decide +kernel

theorem s1329 : optimized 6 0 w1329 = false := by
  decide +kernel

theorem s1330 : optimized 6 0 w1330 = false := by
  decide +kernel

theorem s1331 : optimized 6 0 w1331 = false := by
  decide +kernel

theorem s1332 : optimized 6 0 w1332 = false := by
  decide +kernel

theorem s1333 : optimized 6 0 w1333 = false := by
  decide +kernel

theorem s1334 : optimized 6 0 w1334 = false := by
  decide +kernel

theorem s1335 : optimized 6 0 w1335 = false := by
  decide +kernel

theorem s1336 : optimized 6 0 w1336 = false := by
  decide +kernel

theorem s1337 : optimized 6 0 w1337 = false := by
  decide +kernel

theorem s1338 : optimized 6 0 w1338 = false := by
  decide +kernel

theorem s1339 : optimized 6 1 w1339 = false := by
  decide +kernel

theorem s1340 : optimized 6 0 w1340 = false := by
  decide +kernel

theorem s1341 : optimized 6 0 w1341 = false := by
  decide +kernel

theorem s1342 : optimized 6 0 w1342 = false := by
  decide +kernel

theorem s1343 : optimized 6 1 w1343 = false := by
  decide +kernel

theorem s1344 : optimized 6 0 w1344 = false := by
  decide +kernel

theorem s1345 : optimized 6 0 w1345 = false := by
  decide +kernel

theorem s1346 : optimized 6 0 w1346 = false := by
  decide +kernel

theorem s1347 : optimized 6 0 w1347 = false := by
  decide +kernel

theorem s1348 : optimized 6 1 w1348 = false := by
  decide +kernel

theorem s1349 : optimized 6 0 w1349 = false := by
  decide +kernel

theorem s1350 : optimized 6 0 w1350 = false := by
  decide +kernel

theorem s1351 : optimized 6 0 w1351 = false := by
  decide +kernel

theorem s1352 : optimized 6 0 w1352 = false := by
  decide +kernel

theorem s1353 : optimized 6 0 w1353 = false := by
  decide +kernel

theorem s1354 : optimized 6 0 w1354 = false := by
  decide +kernel

theorem s1355 : optimized 6 0 w1355 = false := by
  decide +kernel

theorem s1356 : optimized 6 0 w1356 = false := by
  decide +kernel

theorem s1357 : optimized 6 0 w1357 = false := by
  decide +kernel

theorem s1358 : optimized 6 0 w1358 = false := by
  decide +kernel

theorem s1359 : optimized 6 0 w1359 = false := by
  decide +kernel

theorem s1360 : optimized 6 0 w1360 = false := by
  decide +kernel

theorem s1361 : optimized 6 0 w1361 = false := by
  decide +kernel

theorem s1362 : optimized 6 1 w1362 = false := by
  decide +kernel

theorem s1363 : optimized 6 0 w1363 = false := by
  decide +kernel

theorem s1364 : optimized 6 0 w1364 = false := by
  decide +kernel

theorem s1365 : optimized 6 1 w1365 = false := by
  decide +kernel

theorem s1366 : optimized 6 0 w1366 = false := by
  decide +kernel

theorem s1367 : optimized 6 0 w1367 = false := by
  decide +kernel

theorem s1368 : optimized 6 0 w1368 = false := by
  decide +kernel

theorem s1369 : optimized 6 1 w1369 = false := by
  decide +kernel

theorem s1370 : optimized 6 0 w1370 = false := by
  decide +kernel

theorem s1371 : optimized 6 0 w1371 = false := by
  decide +kernel

theorem s1372 : optimized 6 0 w1372 = false := by
  decide +kernel

theorem s1373 : optimized 6 1 w1373 = false := by
  decide +kernel

theorem s1374 : optimized 6 0 w1374 = false := by
  decide +kernel

theorem s1375 : optimized 6 0 w1375 = false := by
  decide +kernel

theorem s1376 : optimized 6 1 w1376 = false := by
  decide +kernel

theorem s1377 : optimized 6 0 w1377 = false := by
  decide +kernel

theorem s1378 : optimized 6 0 w1378 = false := by
  decide +kernel

theorem s1379 : optimized 6 0 w1379 = false := by
  decide +kernel

theorem s1380 : optimized 6 0 w1380 = false := by
  decide +kernel

theorem s1381 : optimized 6 0 w1381 = false := by
  decide +kernel

theorem s1382 : optimized 6 0 w1382 = false := by
  decide +kernel

theorem s1383 : optimized 6 0 w1383 = false := by
  decide +kernel

theorem s1384 : optimized 6 0 w1384 = false := by
  decide +kernel

theorem s1385 : optimized 6 0 w1385 = false := by
  decide +kernel

theorem s1386 : optimized 6 0 w1386 = false := by
  decide +kernel

theorem s1387 : optimized 6 0 w1387 = false := by
  decide +kernel

theorem s1388 : optimized 6 0 w1388 = false := by
  decide +kernel

theorem s1389 : optimized 6 0 w1389 = false := by
  decide +kernel

theorem s1390 : optimized 6 1 w1390 = false := by
  decide +kernel

theorem s1391 : optimized 6 0 w1391 = false := by
  decide +kernel

theorem s1392 : optimized 6 0 w1392 = false := by
  decide +kernel

theorem s1393 : optimized 6 1 w1393 = false := by
  decide +kernel

theorem s1394 : optimized 6 0 w1394 = false := by
  decide +kernel

theorem s1395 : optimized 6 0 w1395 = false := by
  decide +kernel

theorem s1396 : optimized 6 0 w1396 = false := by
  decide +kernel

theorem s1397 : optimized 6 0 w1397 = false := by
  decide +kernel

theorem s1398 : optimized 6 0 w1398 = false := by
  decide +kernel

theorem s1399 : optimized 6 0 w1399 = false := by
  decide +kernel

theorem s1400 : optimized 6 1 w1400 = false := by
  decide +kernel

theorem s1401 : optimized 6 0 w1401 = false := by
  decide +kernel

theorem s1402 : optimized 6 0 w1402 = false := by
  decide +kernel

theorem s1403 : optimized 6 0 w1403 = false := by
  decide +kernel

theorem s1404 : optimized 6 0 w1404 = false := by
  decide +kernel

theorem s1405 : optimized 6 1 w1405 = false := by
  decide +kernel

theorem s1406 : optimized 6 0 w1406 = false := by
  decide +kernel

theorem s1407 : optimized 6 0 w1407 = false := by
  decide +kernel

theorem s1408 : optimized 6 1 w1408 = false := by
  decide +kernel

theorem s1409 : optimized 6 0 w1409 = false := by
  decide +kernel

theorem s1410 : optimized 6 0 w1410 = false := by
  decide +kernel

theorem s1411 : optimized 6 1 w1411 = false := by
  decide +kernel

theorem s1412 : optimized 6 0 w1412 = false := by
  decide +kernel

theorem s1413 : optimized 6 0 w1413 = false := by
  decide +kernel

theorem s1414 : optimized 6 1 w1414 = false := by
  decide +kernel

theorem s1415 : optimized 6 0 w1415 = false := by
  decide +kernel

theorem s1416 : optimized 6 0 w1416 = false := by
  decide +kernel

theorem s1417 : optimized 6 0 w1417 = false := by
  decide +kernel

theorem s1418 : optimized 6 0 w1418 = false := by
  decide +kernel

theorem s1419 : optimized 6 0 w1419 = false := by
  decide +kernel

theorem s1420 : optimized 6 0 w1420 = false := by
  decide +kernel

theorem s1421 : optimized 6 0 w1421 = false := by
  decide +kernel

theorem s1422 : optimized 6 0 w1422 = false := by
  decide +kernel

theorem s1423 : optimized 6 0 w1423 = false := by
  decide +kernel

theorem s1424 : optimized 6 0 w1424 = false := by
  decide +kernel

theorem s1425 : optimized 6 0 w1425 = false := by
  decide +kernel

theorem s1426 : optimized 6 0 w1426 = false := by
  decide +kernel

theorem s1427 : optimized 6 0 w1427 = false := by
  decide +kernel

theorem s1428 : optimized 6 0 w1428 = false := by
  decide +kernel

theorem s1429 : optimized 6 0 w1429 = false := by
  decide +kernel

theorem s1430 : optimized 6 0 w1430 = false := by
  decide +kernel

theorem s1431 : optimized 6 0 w1431 = false := by
  decide +kernel

theorem s1432 : optimized 6 0 w1432 = false := by
  decide +kernel

theorem s1433 : optimized 6 0 w1433 = false := by
  decide +kernel

theorem s1434 : optimized 6 0 w1434 = false := by
  decide +kernel

theorem s1435 : optimized 6 0 w1435 = false := by
  decide +kernel

theorem s1436 : optimized 6 0 w1436 = false := by
  decide +kernel

theorem s1437 : optimized 6 0 w1437 = false := by
  decide +kernel

theorem s1438 : optimized 6 0 w1438 = false := by
  decide +kernel

theorem s1439 : optimized 6 0 w1439 = false := by
  decide +kernel

theorem s1440 : optimized 6 0 w1440 = false := by
  decide +kernel

theorem s1441 : optimized 6 0 w1441 = false := by
  decide +kernel

theorem s1442 : optimized 6 0 w1442 = false := by
  decide +kernel

theorem s1443 : optimized 6 1 w1443 = false := by
  decide +kernel

theorem s1444 : optimized 6 0 w1444 = false := by
  decide +kernel

theorem s1445 : optimized 6 0 w1445 = false := by
  decide +kernel

theorem s1446 : optimized 6 1 w1446 = false := by
  decide +kernel

theorem s1447 : optimized 6 0 w1447 = false := by
  decide +kernel

theorem s1448 : optimized 6 0 w1448 = false := by
  decide +kernel

theorem s1449 : optimized 6 1 w1449 = false := by
  decide +kernel

theorem s1450 : optimized 6 0 w1450 = false := by
  decide +kernel

theorem s1451 : optimized 6 0 w1451 = false := by
  decide +kernel

theorem s1452 : optimized 6 1 w1452 = false := by
  decide +kernel

theorem s1453 : optimized 6 0 w1453 = false := by
  decide +kernel

theorem s1454 : optimized 6 0 w1454 = false := by
  decide +kernel

theorem s1455 : optimized 6 0 w1455 = false := by
  decide +kernel

theorem s1456 : optimized 6 0 w1456 = false := by
  decide +kernel

theorem s1457 : optimized 6 0 w1457 = false := by
  decide +kernel

theorem s1458 : optimized 6 0 w1458 = false := by
  decide +kernel

theorem s1459 : optimized 6 0 w1459 = false := by
  decide +kernel

theorem s1460 : optimized 6 0 w1460 = false := by
  decide +kernel

theorem s1461 : optimized 6 0 w1461 = false := by
  decide +kernel

theorem s1462 : optimized 6 1 w1462 = false := by
  decide +kernel

theorem s1463 : optimized 6 0 w1463 = false := by
  decide +kernel

theorem s1464 : optimized 6 0 w1464 = false := by
  decide +kernel

theorem s1465 : optimized 6 1 w1465 = false := by
  decide +kernel

theorem s1466 : optimized 6 0 w1466 = false := by
  decide +kernel

theorem s1467 : optimized 6 0 w1467 = false := by
  decide +kernel

theorem s1468 : optimized 6 0 w1468 = false := by
  decide +kernel

theorem s1469 : optimized 6 0 w1469 = false := by
  decide +kernel

theorem s1470 : optimized 6 1 w1470 = false := by
  decide +kernel

theorem s1471 : optimized 6 0 w1471 = false := by
  decide +kernel

theorem s1472 : optimized 6 0 w1472 = false := by
  decide +kernel

theorem s1473 : optimized 6 0 w1473 = false := by
  decide +kernel

theorem s1474 : optimized 6 0 w1474 = false := by
  decide +kernel

theorem s1475 : optimized 6 0 w1475 = false := by
  decide +kernel

theorem s1476 : optimized 6 0 w1476 = false := by
  decide +kernel

theorem s1477 : optimized 6 0 w1477 = false := by
  decide +kernel

theorem s1478 : optimized 6 0 w1478 = false := by
  decide +kernel

theorem s1479 : optimized 6 0 w1479 = false := by
  decide +kernel

theorem s1480 : optimized 6 0 w1480 = false := by
  decide +kernel

theorem s1481 : optimized 6 0 w1481 = false := by
  decide +kernel

theorem s1482 : optimized 6 0 w1482 = false := by
  decide +kernel

theorem s1483 : optimized 6 0 w1483 = false := by
  decide +kernel

theorem s1484 : optimized 6 0 w1484 = false := by
  decide +kernel

theorem s1485 : optimized 6 0 w1485 = false := by
  decide +kernel

theorem s1486 : optimized 6 0 w1486 = false := by
  decide +kernel

theorem s1487 : optimized 6 0 w1487 = false := by
  decide +kernel

theorem s1488 : optimized 6 0 w1488 = false := by
  decide +kernel

theorem s1489 : optimized 6 0 w1489 = false := by
  decide +kernel

theorem s1490 : optimized 6 0 w1490 = false := by
  decide +kernel

theorem s1491 : optimized 6 0 w1491 = false := by
  decide +kernel

theorem s1492 : optimized 6 0 w1492 = false := by
  decide +kernel

theorem s1493 : optimized 6 0 w1493 = false := by
  decide +kernel

theorem s1494 : optimized 6 0 w1494 = false := by
  decide +kernel

theorem s1495 : optimized 6 0 w1495 = false := by
  decide +kernel

theorem s1496 : optimized 6 0 w1496 = false := by
  decide +kernel

theorem s1497 : optimized 6 0 w1497 = false := by
  decide +kernel

theorem s1498 : optimized 6 0 w1498 = false := by
  decide +kernel

theorem s1499 : optimized 6 0 w1499 = false := by
  decide +kernel

theorem s1500 : optimized 6 1 w1500 = false := by
  decide +kernel

theorem s1501 : optimized 6 0 w1501 = false := by
  decide +kernel

theorem s1502 : optimized 6 0 w1502 = false := by
  decide +kernel

theorem s1503 : optimized 6 0 w1503 = false := by
  decide +kernel

theorem s1504 : optimized 6 0 w1504 = false := by
  decide +kernel

theorem s1505 : optimized 6 0 w1505 = false := by
  decide +kernel

theorem s1506 : optimized 6 0 w1506 = false := by
  decide +kernel

theorem s1507 : optimized 6 0 w1507 = false := by
  decide +kernel

theorem s1508 : optimized 6 0 w1508 = false := by
  decide +kernel

theorem s1509 : optimized 6 0 w1509 = false := by
  decide +kernel

theorem s1510 : optimized 6 0 w1510 = false := by
  decide +kernel

theorem s1511 : optimized 6 0 w1511 = false := by
  decide +kernel

theorem s1512 : optimized 6 0 w1512 = false := by
  decide +kernel

theorem s1513 : optimized 6 0 w1513 = false := by
  decide +kernel

theorem s1514 : optimized 6 0 w1514 = false := by
  decide +kernel

theorem s1515 : optimized 6 0 w1515 = false := by
  decide +kernel

theorem s1516 : optimized 6 0 w1516 = false := by
  decide +kernel

theorem s1517 : optimized 6 0 w1517 = false := by
  decide +kernel

theorem s1518 : optimized 6 0 w1518 = false := by
  decide +kernel

theorem s1519 : optimized 6 0 w1519 = false := by
  decide +kernel

theorem s1520 : optimized 6 0 w1520 = false := by
  decide +kernel

theorem s1521 : optimized 6 0 w1521 = false := by
  decide +kernel

theorem s1522 : optimized 6 0 w1522 = false := by
  decide +kernel

theorem s1523 : optimized 6 0 w1523 = false := by
  decide +kernel

theorem s1524 : optimized 6 1 w1524 = false := by
  decide +kernel

theorem s1525 : optimized 6 0 w1525 = false := by
  decide +kernel

theorem s1526 : optimized 6 0 w1526 = false := by
  decide +kernel

theorem s1527 : optimized 6 1 w1527 = false := by
  decide +kernel

theorem s1528 : optimized 6 0 w1528 = false := by
  decide +kernel

theorem s1529 : optimized 6 0 w1529 = false := by
  decide +kernel

theorem s1530 : optimized 6 0 w1530 = false := by
  decide +kernel

theorem s1531 : optimized 6 0 w1531 = false := by
  decide +kernel

theorem s1532 : optimized 6 0 w1532 = false := by
  decide +kernel

theorem s1533 : optimized 6 1 w1533 = false := by
  decide +kernel

theorem s1534 : optimized 6 0 w1534 = false := by
  decide +kernel

theorem s1535 : optimized 6 0 w1535 = false := by
  decide +kernel

theorem s1536 : optimized 6 0 w1536 = false := by
  decide +kernel

theorem s1537 : optimized 6 1 w1537 = false := by
  decide +kernel

theorem s1538 : optimized 6 0 w1538 = false := by
  decide +kernel

theorem s1539 : optimized 6 0 w1539 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1540 : optimized 6 1 w51 = false :=
  opt_false_of_P (tbl := [(5, 0, w40), (5, 0, w41), (5, 0, w42), (5, 0, w43), (5, 1, w44), (5, 0, w45), (5, 0, w46), (5, 0, w47), (5, 0, w48), (5, 0, w49), (5, 0, w50), (5, 0, w51), (5, 1, w52), (5, 0, w53), (5, 0, w54), (5, 0, w55), (5, 0, w56), (5, 1, w57), (5, 0, w58), (5, 0, w59), (5, 0, w60), (5, 0, w61), (5, 0, w62), (5, 0, w63)])
    (tbl_cons s40 (tbl_cons s41 (tbl_cons s42 (tbl_cons s43 (tbl_cons s44 (tbl_cons s45 (tbl_cons s46 (tbl_cons s47 (tbl_cons s48 (tbl_cons s49 (tbl_cons s50 (tbl_cons s51 (tbl_cons s52 (tbl_cons s53 (tbl_cons s54 (tbl_cons s55 (tbl_cons s56 (tbl_cons s57 (tbl_cons s58 (tbl_cons s59 (tbl_cons s60 (tbl_cons s61 (tbl_cons s62 (tbl_cons s63 tbl_nil))))))))))))))))))))))))
    (by decide +kernel)

theorem s1541 : optimized 6 0 w1540 = false := by
  decide +kernel

theorem s1542 : optimized 6 0 w1541 = false := by
  decide +kernel

theorem s1543 : optimized 6 0 w1542 = false := by
  decide +kernel

theorem s1544 : optimized 6 0 w1543 = false := by
  decide +kernel

theorem s1545 : optimized 6 1 w1544 = false := by
  decide +kernel

theorem s1546 : optimized 6 0 w1545 = false := by
  decide +kernel

theorem s1547 : optimized 6 0 w1546 = false := by
  decide +kernel

theorem s1548 : optimized 6 1 w1547 = false := by
  decide +kernel

theorem s1549 : optimized 6 0 w1548 = false := by
  decide +kernel

theorem s1550 : optimized 6 0 w1549 = false := by
  decide +kernel

theorem s1551 : optimized 6 0 w1550 = false := by
  decide +kernel

theorem s1552 : optimized 6 0 w1551 = false := by
  decide +kernel

theorem s1553 : optimized 6 0 w1552 = false := by
  decide +kernel

theorem s1554 : optimized 6 0 w1553 = false := by
  decide +kernel

theorem s1555 : optimized 6 0 w1554 = false := by
  decide +kernel

theorem s1556 : optimized 6 0 w1555 = false := by
  decide +kernel

theorem s1557 : optimized 6 0 w1556 = false := by
  decide +kernel

theorem s1558 : optimized 6 0 w1557 = false := by
  decide +kernel

theorem s1559 : optimized 6 0 w1558 = false := by
  decide +kernel

theorem s1560 : optimized 6 0 w1559 = false := by
  decide +kernel

theorem s1561 : optimized 6 0 w1560 = false := by
  decide +kernel

theorem s1562 : optimized 6 0 w1561 = false := by
  decide +kernel

theorem s1563 : optimized 6 0 w1562 = false := by
  decide +kernel

theorem s1564 : optimized 6 0 w1563 = false := by
  decide +kernel

theorem s1565 : optimized 6 0 w1564 = false := by
  decide +kernel

theorem s1566 : optimized 6 1 w1565 = false := by
  decide +kernel

theorem s1567 : optimized 6 0 w1566 = false := by
  decide +kernel

theorem s1568 : optimized 6 0 w1567 = false := by
  decide +kernel

theorem s1569 : optimized 6 0 w1568 = false := by
  decide +kernel

theorem s1570 : optimized 6 0 w1569 = false := by
  decide +kernel

theorem s1571 : optimized 6 0 w1570 = false := by
  decide +kernel

theorem s1572 : optimized 6 0 w1571 = false := by
  decide +kernel

theorem s1573 : optimized 6 0 w1572 = false := by
  decide +kernel

theorem s1574 : optimized 6 1 w1573 = false := by
  decide +kernel

theorem s1575 : optimized 6 0 w1574 = false := by
  decide +kernel

theorem s1576 : optimized 6 0 w1575 = false := by
  decide +kernel

theorem s1577 : optimized 6 0 w1576 = false := by
  decide +kernel

theorem s1578 : optimized 6 1 w1577 = false := by
  decide +kernel

theorem s1579 : optimized 6 0 w1578 = false := by
  decide +kernel

theorem s1580 : optimized 6 0 w1579 = false := by
  decide +kernel

theorem s1581 : optimized 6 0 w1580 = false := by
  decide +kernel

theorem s1582 : optimized 6 0 w1581 = false := by
  decide +kernel

theorem s1583 : optimized 6 0 w1582 = false := by
  decide +kernel

theorem s1584 : optimized 6 0 w1583 = false := by
  decide +kernel

theorem s1585 : optimized 6 0 w1584 = false := by
  decide +kernel

theorem s1586 : optimized 6 0 w1585 = false := by
  decide +kernel

theorem s1587 : optimized 6 0 w1586 = false := by
  decide +kernel

theorem s1588 : optimized 6 0 w1587 = false := by
  decide +kernel

theorem s1589 : optimized 6 0 w1588 = false := by
  decide +kernel

theorem s1590 : optimized 6 0 w1589 = false := by
  decide +kernel

theorem s1591 : optimized 6 0 w1590 = false := by
  decide +kernel

theorem s1592 : optimized 6 0 w1591 = false := by
  decide +kernel

theorem s1593 : optimized 6 0 w1592 = false := by
  decide +kernel

theorem s1594 : optimized 6 0 w1593 = false := by
  decide +kernel

theorem s1595 : optimized 6 0 w1594 = false := by
  decide +kernel

theorem s1596 : optimized 6 0 w1595 = false := by
  decide +kernel

theorem s1597 : optimized 6 0 w1596 = false := by
  decide +kernel

theorem s1598 : optimized 6 0 w1597 = false := by
  decide +kernel

theorem s1599 : optimized 6 0 w1598 = false := by
  decide +kernel

theorem s1600 : optimized 6 0 w1599 = false := by
  decide +kernel

theorem s1601 : optimized 6 0 w1600 = false := by
  decide +kernel

theorem s1602 : optimized 6 0 w1601 = false := by
  decide +kernel

theorem s1603 : optimized 6 0 w1602 = false := by
  decide +kernel

theorem s1604 : optimized 6 0 w1603 = false := by
  decide +kernel

theorem s1605 : optimized 6 0 w1604 = false := by
  decide +kernel

theorem s1606 : optimized 6 1 w1605 = false := by
  decide +kernel

theorem s1607 : optimized 6 0 w1606 = false := by
  decide +kernel

theorem s1608 : optimized 6 0 w1607 = false := by
  decide +kernel

theorem s1609 : optimized 6 1 w1608 = false := by
  decide +kernel

theorem s1610 : optimized 6 0 w1609 = false := by
  decide +kernel

theorem s1611 : optimized 6 0 w1610 = false := by
  decide +kernel

theorem s1612 : optimized 6 1 w1611 = false := by
  decide +kernel

theorem s1613 : optimized 6 0 w1612 = false := by
  decide +kernel

theorem s1614 : optimized 6 0 w1613 = false := by
  decide +kernel

theorem s1615 : optimized 6 0 w1614 = false := by
  decide +kernel

theorem s1616 : optimized 6 0 w1615 = false := by
  decide +kernel

theorem s1617 : optimized 6 0 w1616 = false := by
  decide +kernel

theorem s1618 : optimized 6 0 w1617 = false := by
  decide +kernel

theorem s1619 : optimized 6 0 w1618 = false := by
  decide +kernel

theorem s1620 : optimized 6 0 w1619 = false := by
  decide +kernel

theorem s1621 : optimized 6 0 w1620 = false := by
  decide +kernel

theorem s1622 : optimized 6 0 w1621 = false := by
  decide +kernel

theorem s1623 : optimized 6 0 w1622 = false := by
  decide +kernel

theorem s1624 : optimized 6 1 w1623 = false := by
  decide +kernel

theorem s1625 : optimized 6 0 w1624 = false := by
  decide +kernel

theorem s1626 : optimized 6 0 w1625 = false := by
  decide +kernel

theorem s1627 : optimized 6 0 w1626 = false := by
  decide +kernel

theorem s1628 : optimized 6 0 w1627 = false := by
  decide +kernel

theorem s1629 : optimized 6 0 w1628 = false := by
  decide +kernel

theorem s1630 : optimized 6 1 w1629 = false := by
  decide +kernel

theorem s1631 : optimized 6 0 w1630 = false := by
  decide +kernel

theorem s1632 : optimized 6 0 w1631 = false := by
  decide +kernel

theorem s1633 : optimized 6 0 w1632 = false := by
  decide +kernel

theorem s1634 : optimized 6 1 w1633 = false := by
  decide +kernel

theorem s1635 : optimized 6 0 w1634 = false := by
  decide +kernel

theorem s1636 : optimized 6 0 w1635 = false := by
  decide +kernel

theorem s1637 : optimized 6 0 w1636 = false := by
  decide +kernel

theorem s1638 : optimized 6 0 w1637 = false := by
  decide +kernel

theorem s1639 : optimized 6 0 w1638 = false := by
  decide +kernel

theorem s1640 : optimized 6 0 w1639 = false := by
  decide +kernel

theorem s1641 : optimized 6 0 w1640 = false := by
  decide +kernel

theorem s1642 : optimized 6 0 w1641 = false := by
  decide +kernel

theorem s1643 : optimized 6 0 w1642 = false := by
  decide +kernel

theorem s1644 : optimized 6 0 w1643 = false := by
  decide +kernel

theorem s1645 : optimized 6 0 w1644 = false := by
  decide +kernel

theorem s1646 : optimized 6 0 w1645 = false := by
  decide +kernel

theorem s1647 : optimized 6 0 w1646 = false := by
  decide +kernel

theorem s1648 : optimized 6 0 w1647 = false := by
  decide +kernel

theorem s1649 : optimized 6 0 w1648 = false := by
  decide +kernel

theorem s1650 : optimized 6 0 w1649 = false := by
  decide +kernel

theorem s1651 : optimized 6 0 w1650 = false := by
  decide +kernel

theorem s1652 : optimized 6 0 w1651 = false := by
  decide +kernel

theorem s1653 : optimized 6 0 w1652 = false := by
  decide +kernel

theorem s1654 : optimized 6 0 w1653 = false := by
  decide +kernel

theorem s1655 : optimized 6 0 w1654 = false := by
  decide +kernel

theorem s1656 : optimized 6 0 w1655 = false := by
  decide +kernel

theorem s1657 : optimized 6 1 w1656 = false := by
  decide +kernel

theorem s1658 : optimized 6 0 w1657 = false := by
  decide +kernel

theorem s1659 : optimized 6 0 w1658 = false := by
  decide +kernel

theorem s1660 : optimized 6 1 w1659 = false := by
  decide +kernel

theorem s1661 : optimized 6 0 w1660 = false := by
  decide +kernel

theorem s1662 : optimized 6 0 w1661 = false := by
  decide +kernel

theorem s1663 : optimized 6 1 w1662 = false := by
  decide +kernel

theorem s1664 : optimized 6 0 w1663 = false := by
  decide +kernel

theorem s1665 : optimized 6 0 w1664 = false := by
  decide +kernel

theorem s1666 : optimized 6 0 w1665 = false := by
  decide +kernel

theorem s1667 : optimized 6 0 w1666 = false := by
  decide +kernel

theorem s1668 : optimized 6 0 w1667 = false := by
  decide +kernel

theorem s1669 : optimized 6 1 w1668 = false := by
  decide +kernel

theorem s1670 : optimized 6 0 w1669 = false := by
  decide +kernel

theorem s1671 : optimized 6 0 w1670 = false := by
  decide +kernel

theorem s1672 : optimized 6 0 w1671 = false := by
  decide +kernel

theorem s1673 : optimized 6 0 w1672 = false := by
  decide +kernel

theorem s1674 : optimized 6 0 w1673 = false := by
  decide +kernel

theorem s1675 : optimized 6 0 w1674 = false := by
  decide +kernel

theorem s1676 : optimized 6 1 w1675 = false := by
  decide +kernel

theorem s1677 : optimized 6 0 w1676 = false := by
  decide +kernel

theorem s1678 : optimized 6 0 w1677 = false := by
  decide +kernel

theorem s1679 : optimized 6 0 w1678 = false := by
  decide +kernel

theorem s1680 : optimized 6 0 w1679 = false := by
  decide +kernel

theorem s1681 : optimized 6 0 w1680 = false := by
  decide +kernel

theorem s1682 : optimized 6 0 w1681 = false := by
  decide +kernel

theorem s1683 : optimized 6 0 w1682 = false := by
  decide +kernel

theorem s1684 : optimized 6 0 w1683 = false := by
  decide +kernel

theorem s1685 : optimized 6 0 w1684 = false := by
  decide +kernel

theorem s1686 : optimized 6 0 w1685 = false := by
  decide +kernel

theorem s1687 : optimized 6 0 w1686 = false := by
  decide +kernel

theorem s1688 : optimized 6 0 w1687 = false := by
  decide +kernel

theorem s1689 : optimized 6 0 w1688 = false := by
  decide +kernel

theorem s1690 : optimized 6 0 w1689 = false := by
  decide +kernel

theorem s1691 : optimized 6 0 w1690 = false := by
  decide +kernel

theorem s1692 : optimized 6 0 w1691 = false := by
  decide +kernel

theorem s1693 : optimized 6 0 w1692 = false := by
  decide +kernel

theorem s1694 : optimized 6 0 w1693 = false := by
  decide +kernel

theorem s1695 : optimized 6 0 w1694 = false := by
  decide +kernel

theorem s1696 : optimized 6 0 w1695 = false := by
  decide +kernel

theorem s1697 : optimized 6 0 w1696 = false := by
  decide +kernel

theorem s1698 : optimized 6 0 w1697 = false := by
  decide +kernel

theorem s1699 : optimized 6 0 w1698 = false := by
  decide +kernel

theorem s1700 : optimized 6 0 w1699 = false := by
  decide +kernel

theorem s1701 : optimized 6 0 w1700 = false := by
  decide +kernel

theorem s1702 : optimized 6 0 w1701 = false := by
  decide +kernel

theorem s1703 : optimized 6 0 w1702 = false := by
  decide +kernel

theorem s1704 : optimized 6 0 w1703 = false := by
  decide +kernel

theorem s1705 : optimized 6 0 w1704 = false := by
  decide +kernel

theorem s1706 : optimized 6 0 w1705 = false := by
  decide +kernel

theorem s1707 : optimized 6 0 w1706 = false := by
  decide +kernel

theorem s1708 : optimized 6 0 w1707 = false := by
  decide +kernel

theorem s1709 : optimized 6 0 w1708 = false := by
  decide +kernel

theorem s1710 : optimized 6 0 w1709 = false := by
  decide +kernel

theorem s1711 : optimized 6 0 w1710 = false := by
  decide +kernel

theorem s1712 : optimized 6 1 w1711 = false := by
  decide +kernel

theorem s1713 : optimized 6 0 w1712 = false := by
  decide +kernel

theorem s1714 : optimized 6 0 w1713 = false := by
  decide +kernel

theorem s1715 : optimized 6 0 w1714 = false := by
  decide +kernel

theorem s1716 : optimized 6 0 w1715 = false := by
  decide +kernel

theorem s1717 : optimized 6 0 w1716 = false := by
  decide +kernel

theorem s1718 : optimized 6 0 w1717 = false := by
  decide +kernel

theorem s1719 : optimized 6 0 w1718 = false := by
  decide +kernel

theorem s1720 : optimized 6 0 w1719 = false := by
  decide +kernel

theorem s1721 : optimized 6 0 w1720 = false := by
  decide +kernel

theorem s1722 : optimized 6 0 w1721 = false := by
  decide +kernel

theorem s1723 : optimized 6 0 w1722 = false := by
  decide +kernel

theorem s1724 : optimized 6 0 w1723 = false := by
  decide +kernel

theorem s1725 : optimized 6 0 w1724 = false := by
  decide +kernel

theorem s1726 : optimized 6 0 w1725 = false := by
  decide +kernel

theorem s1727 : optimized 6 0 w1726 = false := by
  decide +kernel

theorem s1728 : optimized 6 0 w1727 = false := by
  decide +kernel

theorem s1729 : optimized 6 0 w1728 = false := by
  decide +kernel

theorem s1730 : optimized 6 0 w1729 = false := by
  decide +kernel

theorem s1731 : optimized 6 0 w1730 = false := by
  decide +kernel

theorem s1732 : optimized 6 0 w1731 = false := by
  decide +kernel

theorem s1733 : optimized 6 0 w1732 = false := by
  decide +kernel

theorem s1734 : optimized 6 1 w1733 = false := by
  decide +kernel

theorem s1735 : optimized 6 0 w1734 = false := by
  decide +kernel

theorem s1736 : optimized 6 0 w1735 = false := by
  decide +kernel

theorem s1737 : optimized 6 0 w1736 = false := by
  decide +kernel

theorem s1738 : optimized 6 0 w1737 = false := by
  decide +kernel

theorem s1739 : optimized 6 0 w1738 = false := by
  decide +kernel

theorem s1740 : optimized 6 0 w1739 = false := by
  decide +kernel

theorem s1741 : optimized 6 0 w1740 = false := by
  decide +kernel

theorem s1742 : optimized 6 0 w1741 = false := by
  decide +kernel

theorem s1743 : optimized 6 0 w1742 = false := by
  decide +kernel

theorem s1744 : optimized 6 0 w1743 = false := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1745 : optimized 7 1 w64 = false :=
  opt_false_of_P (tbl := [(6, 0, w64), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w68), (6, 0, w69), (6, 0, w70), (6, 0, w71), (6, 0, w72), (6, 0, w73), (6, 0, w74), (6, 0, w75), (6, 0, w76), (6, 0, w77), (6, 0, w78), (6, 0, w79), (6, 0, w80), (6, 0, w81), (6, 1, w82), (6, 0, w83), (6, 0, w84), (6, 0, w85), (6, 1, w86), (6, 0, w87), (6, 0, w88), (6, 0, w89), (6, 1, w90), (6, 0, w91), (6, 0, w92), (6, 0, w93), (6, 1, w94), (6, 0, w95), (6, 0, w96), (6, 1, w97), (6, 0, w98), (6, 0, w99), (6, 0, w100), (6, 0, w101), (6, 0, w102), (6, 0, w103), (6, 0, w104), (6, 0, w105)])
    (tbl_cons s64 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s68 (tbl_cons s69 (tbl_cons s70 (tbl_cons s71 (tbl_cons s72 (tbl_cons s73 (tbl_cons s74 (tbl_cons s75 (tbl_cons s76 (tbl_cons s77 (tbl_cons s78 (tbl_cons s79 (tbl_cons s80 (tbl_cons s81 (tbl_cons s82 (tbl_cons s83 (tbl_cons s84 (tbl_cons s85 (tbl_cons s86 (tbl_cons s87 (tbl_cons s88 (tbl_cons s89 (tbl_cons s90 (tbl_cons s91 (tbl_cons s92 (tbl_cons s93 (tbl_cons s94 (tbl_cons s95 (tbl_cons s96 (tbl_cons s97 (tbl_cons s98 (tbl_cons s99 (tbl_cons s100 (tbl_cons s101 (tbl_cons s102 (tbl_cons s103 (tbl_cons s104 (tbl_cons s105 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1746 : optimized 7 1 w108 = false :=
  opt_false_of_P (tbl := [(6, 1, w97), (6, 0, w98), (6, 0, w99), (6, 0, w106), (6, 0, w107), (6, 1, w65), (6, 0, w66), (6, 0, w108), (6, 0, w67), (6, 0, w76), (6, 0, w109), (6, 0, w110), (6, 0, w111), (6, 0, w112), (6, 1, w113), (6, 0, w114), (6, 0, w115), (6, 0, w116), (6, 0, w117), (6, 1, w118), (6, 0, w119), (6, 0, w120), (6, 0, w74), (6, 0, w69), (6, 0, w121), (6, 0, w122), (6, 1, w123), (6, 0, w124), (6, 0, w125), (6, 0, w126), (6, 0, w127), (6, 1, w128), (6, 0, w129), (6, 0, w130), (6, 0, w131), (6, 1, w132), (6, 0, w133), (6, 0, w134), (6, 0, w135), (6, 1, w136), (6, 0, w137), (6, 0, w138), (6, 0, w139), (6, 1, w140), (6, 0, w141), (6, 0, w142), (6, 0, w143), (6, 1, w144), (6, 0, w145), (6, 0, w146), (6, 0, w147), (6, 1, w148), (6, 0, w149), (6, 0, w150), (6, 0, w151), (6, 0, w152), (6, 0, w153)])
    (tbl_cons s97 (tbl_cons s98 (tbl_cons s99 (tbl_cons s106 (tbl_cons s107 (tbl_cons s65 (tbl_cons s66 (tbl_cons s108 (tbl_cons s67 (tbl_cons s76 (tbl_cons s109 (tbl_cons s110 (tbl_cons s111 (tbl_cons s112 (tbl_cons s113 (tbl_cons s114 (tbl_cons s115 (tbl_cons s116 (tbl_cons s117 (tbl_cons s118 (tbl_cons s119 (tbl_cons s120 (tbl_cons s74 (tbl_cons s69 (tbl_cons s121 (tbl_cons s122 (tbl_cons s123 (tbl_cons s124 (tbl_cons s125 (tbl_cons s126 (tbl_cons s127 (tbl_cons s128 (tbl_cons s129 (tbl_cons s130 (tbl_cons s131 (tbl_cons s132 (tbl_cons s133 (tbl_cons s134 (tbl_cons s135 (tbl_cons s136 (tbl_cons s137 (tbl_cons s138 (tbl_cons s139 (tbl_cons s140 (tbl_cons s141 (tbl_cons s142 (tbl_cons s143 (tbl_cons s144 (tbl_cons s145 (tbl_cons s146 (tbl_cons s147 (tbl_cons s148 (tbl_cons s149 (tbl_cons s150 (tbl_cons s151 (tbl_cons s152 (tbl_cons s153 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1747 : optimized 7 1 w69 = false :=
  opt_false_of_P (tbl := [(6, 0, w69), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w68), (6, 0, w64), (6, 0, w154), (6, 0, w155), (6, 0, w156), (6, 0, w157), (6, 0, w106), (6, 0, w108), (6, 0, w74), (6, 0, w158), (6, 0, w159), (6, 0, w160), (6, 0, w161), (6, 0, w162), (6, 0, w163), (6, 0, w164), (6, 0, w165), (6, 1, w166), (6, 0, w167), (6, 0, w168), (6, 0, w169), (6, 1, w170), (6, 0, w171), (6, 0, w172), (6, 0, w173), (6, 1, w174), (6, 0, w175), (6, 0, w176), (6, 0, w177), (6, 0, w178), (6, 0, w179), (6, 0, w180), (6, 0, w181), (6, 0, w182), (6, 0, w183), (6, 0, w184)])
    (tbl_cons s69 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s68 (tbl_cons s64 (tbl_cons s154 (tbl_cons s155 (tbl_cons s156 (tbl_cons s157 (tbl_cons s106 (tbl_cons s108 (tbl_cons s74 (tbl_cons s158 (tbl_cons s159 (tbl_cons s160 (tbl_cons s161 (tbl_cons s162 (tbl_cons s163 (tbl_cons s164 (tbl_cons s165 (tbl_cons s166 (tbl_cons s167 (tbl_cons s168 (tbl_cons s169 (tbl_cons s170 (tbl_cons s171 (tbl_cons s172 (tbl_cons s173 (tbl_cons s174 (tbl_cons s175 (tbl_cons s176 (tbl_cons s177 (tbl_cons s178 (tbl_cons s179 (tbl_cons s180 (tbl_cons s181 (tbl_cons s182 (tbl_cons s183 (tbl_cons s184 tbl_nil))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1748 : optimized 7 1 w76 = false :=
  opt_false_of_P (tbl := [(6, 0, w67), (6, 0, w108), (6, 0, w107), (6, 1, w65), (6, 0, w66), (6, 0, w76), (6, 0, w75), (6, 1, w174), (6, 0, w175), (6, 0, w176), (6, 0, w185), (6, 0, w186), (6, 0, w187), (6, 0, w188), (6, 0, w189), (6, 0, w190), (6, 0, w74), (6, 0, w64), (6, 0, w191), (6, 0, w192), (6, 0, w193), (6, 0, w194), (6, 0, w195), (6, 0, w196), (6, 0, w197), (6, 0, w198), (6, 0, w199), (6, 1, w200), (6, 0, w201), (6, 0, w202), (6, 0, w203), (6, 1, w204), (6, 0, w205), (6, 0, w206), (6, 0, w207), (6, 0, w208), (6, 1, w209), (6, 0, w210), (6, 0, w211), (6, 0, w212), (6, 0, w213), (6, 0, w214), (6, 0, w215)])
    (tbl_cons s67 (tbl_cons s108 (tbl_cons s107 (tbl_cons s65 (tbl_cons s66 (tbl_cons s76 (tbl_cons s75 (tbl_cons s174 (tbl_cons s175 (tbl_cons s176 (tbl_cons s185 (tbl_cons s186 (tbl_cons s187 (tbl_cons s188 (tbl_cons s189 (tbl_cons s190 (tbl_cons s74 (tbl_cons s64 (tbl_cons s191 (tbl_cons s192 (tbl_cons s193 (tbl_cons s194 (tbl_cons s195 (tbl_cons s196 (tbl_cons s197 (tbl_cons s198 (tbl_cons s199 (tbl_cons s200 (tbl_cons s201 (tbl_cons s202 (tbl_cons s203 (tbl_cons s204 (tbl_cons s205 (tbl_cons s206 (tbl_cons s207 (tbl_cons s208 (tbl_cons s209 (tbl_cons s210 (tbl_cons s211 (tbl_cons s212 (tbl_cons s213 (tbl_cons s214 (tbl_cons s215 tbl_nil)))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1749 : optimized 7 1 w216 = false :=
  opt_false_of_P (tbl := [(6, 0, w216), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w217), (6, 0, w218), (6, 0, w219), (6, 0, w220), (6, 0, w221), (6, 0, w222), (6, 0, w77), (6, 0, w223), (6, 0, w158), (6, 0, w224), (6, 0, w225), (6, 0, w226), (6, 0, w227), (6, 0, w228), (6, 0, w229), (6, 0, w230), (6, 0, w231), (6, 0, w232), (6, 0, w233), (6, 0, w234), (6, 0, w235), (6, 1, w236), (6, 0, w237), (6, 0, w238), (6, 0, w239), (6, 0, w240), (6, 0, w241), (6, 0, w242), (6, 0, w243), (6, 0, w244), (6, 0, w245), (6, 0, w246)])
    (tbl_cons s216 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s217 (tbl_cons s218 (tbl_cons s219 (tbl_cons s220 (tbl_cons s221 (tbl_cons s222 (tbl_cons s77 (tbl_cons s223 (tbl_cons s158 (tbl_cons s224 (tbl_cons s225 (tbl_cons s226 (tbl_cons s227 (tbl_cons s228 (tbl_cons s229 (tbl_cons s230 (tbl_cons s231 (tbl_cons s232 (tbl_cons s233 (tbl_cons s234 (tbl_cons s235 (tbl_cons s236 (tbl_cons s237 (tbl_cons s238 (tbl_cons s239 (tbl_cons s240 (tbl_cons s241 (tbl_cons s242 (tbl_cons s243 (tbl_cons s244 (tbl_cons s245 (tbl_cons s246 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1750 : optimized 7 1 w251 = false :=
  opt_false_of_P (tbl := [(6, 0, w247), (6, 0, w248), (6, 0, w109), (6, 0, w177), (6, 1, w236), (6, 0, w237), (6, 0, w238), (6, 0, w249), (6, 0, w250), (6, 1, w65), (6, 0, w66), (6, 0, w251), (6, 0, w67), (6, 0, w227), (6, 0, w252), (6, 0, w253), (6, 1, w254), (6, 0, w255), (6, 0, w256), (6, 0, w257), (6, 0, w258), (6, 0, w259), (6, 0, w260), (6, 0, w261), (6, 0, w131), (6, 0, w193), (6, 0, w262), (6, 0, w263), (6, 0, w264), (6, 0, w265), (6, 0, w266), (6, 0, w225), (6, 0, w218), (6, 0, w267), (6, 0, w268), (6, 0, w269), (6, 0, w270), (6, 0, w271), (6, 0, w272), (6, 1, w273), (6, 0, w274), (6, 0, w275), (6, 0, w276), (6, 1, w277), (6, 0, w278), (6, 0, w279), (6, 0, w280)])
    (tbl_cons s247 (tbl_cons s248 (tbl_cons s109 (tbl_cons s177 (tbl_cons s236 (tbl_cons s237 (tbl_cons s238 (tbl_cons s249 (tbl_cons s250 (tbl_cons s65 (tbl_cons s66 (tbl_cons s251 (tbl_cons s67 (tbl_cons s227 (tbl_cons s252 (tbl_cons s253 (tbl_cons s254 (tbl_cons s255 (tbl_cons s256 (tbl_cons s257 (tbl_cons s258 (tbl_cons s259 (tbl_cons s260 (tbl_cons s261 (tbl_cons s131 (tbl_cons s193 (tbl_cons s262 (tbl_cons s263 (tbl_cons s264 (tbl_cons s265 (tbl_cons s266 (tbl_cons s225 (tbl_cons s218 (tbl_cons s267 (tbl_cons s268 (tbl_cons s269 (tbl_cons s270 (tbl_cons s271 (tbl_cons s272 (tbl_cons s273 (tbl_cons s274 (tbl_cons s275 (tbl_cons s276 (tbl_cons s277 (tbl_cons s278 (tbl_cons s279 (tbl_cons s280 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1751 : optimized 7 1 w218 = false :=
  opt_false_of_P (tbl := [(6, 0, w218), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w217), (6, 0, w216), (6, 0, w281), (6, 0, w282), (6, 0, w283), (6, 0, w284), (6, 0, w79), (6, 0, w285), (6, 0, w160), (6, 0, w286), (6, 0, w249), (6, 0, w251), (6, 0, w225), (6, 0, w287), (6, 0, w288), (6, 0, w289), (6, 0, w290), (6, 0, w291), (6, 0, w292), (6, 0, w293), (6, 0, w294), (6, 0, w295), (6, 0, w296), (6, 0, w110), (6, 0, w178), (6, 1, w297), (6, 0, w298), (6, 0, w299), (6, 0, w300), (6, 0, w301), (6, 1, w302), (6, 0, w303), (6, 0, w304), (6, 0, w305), (6, 0, w306), (6, 0, w307), (6, 0, w308), (6, 0, w309), (6, 0, w310)])
    (tbl_cons s218 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s217 (tbl_cons s216 (tbl_cons s281 (tbl_cons s282 (tbl_cons s283 (tbl_cons s284 (tbl_cons s79 (tbl_cons s285 (tbl_cons s160 (tbl_cons s286 (tbl_cons s249 (tbl_cons s251 (tbl_cons s225 (tbl_cons s287 (tbl_cons s288 (tbl_cons s289 (tbl_cons s290 (tbl_cons s291 (tbl_cons s292 (tbl_cons s293 (tbl_cons s294 (tbl_cons s295 (tbl_cons s296 (tbl_cons s110 (tbl_cons s178 (tbl_cons s297 (tbl_cons s298 (tbl_cons s299 (tbl_cons s300 (tbl_cons s301 (tbl_cons s302 (tbl_cons s303 (tbl_cons s304 (tbl_cons s305 (tbl_cons s306 (tbl_cons s307 (tbl_cons s308 (tbl_cons s309 (tbl_cons s310 tbl_nil)))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1752 : optimized 7 1 w227 = false :=
  opt_false_of_P (tbl := [(6, 0, w67), (6, 0, w251), (6, 0, w250), (6, 1, w65), (6, 0, w66), (6, 0, w227), (6, 0, w226), (6, 1, w297), (6, 0, w298), (6, 0, w299), (6, 0, w311), (6, 0, w312), (6, 0, w313), (6, 1, w314), (6, 0, w315), (6, 0, w316), (6, 1, w317), (6, 0, w318), (6, 0, w319), (6, 0, w320), (6, 0, w191), (6, 0, w321), (6, 0, w322), (6, 0, w135), (6, 0, w323), (6, 0, w324), (6, 0, w225), (6, 0, w216), (6, 0, w325), (6, 1, w326), (6, 0, w327), (6, 0, w328), (6, 0, w329), (6, 1, w330), (6, 0, w331), (6, 0, w332), (6, 0, w333), (6, 1, w334), (6, 0, w335), (6, 0, w336), (6, 0, w337), (6, 1, w338), (6, 0, w339), (6, 0, w340), (6, 0, w341), (6, 0, w342), (6, 0, w343), (6, 0, w344)])
    (tbl_cons s67 (tbl_cons s251 (tbl_cons s250 (tbl_cons s65 (tbl_cons s66 (tbl_cons s227 (tbl_cons s226 (tbl_cons s297 (tbl_cons s298 (tbl_cons s299 (tbl_cons s311 (tbl_cons s312 (tbl_cons s313 (tbl_cons s314 (tbl_cons s315 (tbl_cons s316 (tbl_cons s317 (tbl_cons s318 (tbl_cons s319 (tbl_cons s320 (tbl_cons s191 (tbl_cons s321 (tbl_cons s322 (tbl_cons s135 (tbl_cons s323 (tbl_cons s324 (tbl_cons s225 (tbl_cons s216 (tbl_cons s325 (tbl_cons s326 (tbl_cons s327 (tbl_cons s328 (tbl_cons s329 (tbl_cons s330 (tbl_cons s331 (tbl_cons s332 (tbl_cons s333 (tbl_cons s334 (tbl_cons s335 (tbl_cons s336 (tbl_cons s337 (tbl_cons s338 (tbl_cons s339 (tbl_cons s340 (tbl_cons s341 (tbl_cons s342 (tbl_cons s343 (tbl_cons s344 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1753 : optimized 7 1 w345 = false :=
  opt_false_of_P (tbl := [(6, 0, w345), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w346), (6, 0, w347), (6, 0, w348), (6, 1, w349), (6, 0, w350), (6, 0, w351), (6, 0, w352), (6, 1, w353), (6, 0, w354), (6, 0, w355), (6, 0, w81), (6, 1, w356), (6, 0, w357), (6, 0, w358), (6, 0, w162), (6, 1, w359), (6, 0, w360), (6, 0, w361), (6, 0, w228), (6, 1, w362), (6, 0, w363), (6, 0, w364), (6, 0, w287), (6, 1, w365), (6, 0, w366), (6, 0, w367), (6, 0, w368), (6, 0, w369), (6, 0, w370), (6, 0, w371), (6, 1, w372), (6, 0, w373), (6, 0, w374), (6, 0, w375), (6, 1, w376), (6, 0, w377), (6, 0, w378), (6, 0, w379), (6, 0, w380), (6, 1, w381), (6, 0, w382), (6, 0, w383), (6, 0, w384), (6, 0, w385), (6, 0, w386), (6, 0, w387), (6, 0, w388), (6, 0, w389), (6, 0, w390), (6, 0, w391), (6, 0, w392), (6, 0, w393), (6, 0, w394), (6, 0, w395)])
    (tbl_cons s345 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s346 (tbl_cons s347 (tbl_cons s348 (tbl_cons s349 (tbl_cons s350 (tbl_cons s351 (tbl_cons s352 (tbl_cons s353 (tbl_cons s354 (tbl_cons s355 (tbl_cons s81 (tbl_cons s356 (tbl_cons s357 (tbl_cons s358 (tbl_cons s162 (tbl_cons s359 (tbl_cons s360 (tbl_cons s361 (tbl_cons s228 (tbl_cons s362 (tbl_cons s363 (tbl_cons s364 (tbl_cons s287 (tbl_cons s365 (tbl_cons s366 (tbl_cons s367 (tbl_cons s368 (tbl_cons s369 (tbl_cons s370 (tbl_cons s371 (tbl_cons s372 (tbl_cons s373 (tbl_cons s374 (tbl_cons s375 (tbl_cons s376 (tbl_cons s377 (tbl_cons s378 (tbl_cons s379 (tbl_cons s380 (tbl_cons s381 (tbl_cons s382 (tbl_cons s383 (tbl_cons s384 (tbl_cons s385 (tbl_cons s386 (tbl_cons s387 (tbl_cons s388 (tbl_cons s389 (tbl_cons s390 (tbl_cons s391 (tbl_cons s392 (tbl_cons s393 (tbl_cons s394 (tbl_cons s395 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1754 : optimized 7 1 w400 = false :=
  opt_false_of_P (tbl := [(6, 1, w381), (6, 0, w382), (6, 0, w383), (6, 0, w396), (6, 0, w397), (6, 0, w398), (6, 0, w399), (6, 1, w65), (6, 0, w66), (6, 0, w400), (6, 0, w67), (6, 0, w370), (6, 0, w401), (6, 0, w402), (6, 1, w403), (6, 0, w404), (6, 0, w405), (6, 0, w406), (6, 0, w407), (6, 1, w408), (6, 0, w409), (6, 0, w410), (6, 0, w411), (6, 0, w412), (6, 0, w413), (6, 0, w414), (6, 0, w415), (6, 0, w139), (6, 0, w197), (6, 0, w416), (6, 0, w417), (6, 0, w268), (6, 0, w329), (6, 0, w418), (6, 0, w419), (6, 0, w420), (6, 0, w368), (6, 0, w347), (6, 1, w421), (6, 0, w422), (6, 0, w423), (6, 0, w424), (6, 0, w425), (6, 1, w426), (6, 0, w427), (6, 0, w428)])
    (tbl_cons s381 (tbl_cons s382 (tbl_cons s383 (tbl_cons s396 (tbl_cons s397 (tbl_cons s398 (tbl_cons s399 (tbl_cons s65 (tbl_cons s66 (tbl_cons s400 (tbl_cons s67 (tbl_cons s370 (tbl_cons s401 (tbl_cons s402 (tbl_cons s403 (tbl_cons s404 (tbl_cons s405 (tbl_cons s406 (tbl_cons s407 (tbl_cons s408 (tbl_cons s409 (tbl_cons s410 (tbl_cons s411 (tbl_cons s412 (tbl_cons s413 (tbl_cons s414 (tbl_cons s415 (tbl_cons s139 (tbl_cons s197 (tbl_cons s416 (tbl_cons s417 (tbl_cons s268 (tbl_cons s329 (tbl_cons s418 (tbl_cons s419 (tbl_cons s420 (tbl_cons s368 (tbl_cons s347 (tbl_cons s421 (tbl_cons s422 (tbl_cons s423 (tbl_cons s424 (tbl_cons s425 (tbl_cons s426 (tbl_cons s427 (tbl_cons s428 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1755 : optimized 7 1 w347 = false :=
  opt_false_of_P (tbl := [(6, 0, w347), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w346), (6, 0, w345), (6, 0, w429), (6, 0, w430), (6, 0, w431), (6, 0, w432), (6, 0, w85), (6, 0, w433), (6, 0, w164), (6, 0, w434), (6, 0, w230), (6, 0, w435), (6, 0, w289), (6, 0, w436), (6, 0, w396), (6, 0, w400), (6, 0, w368), (6, 1, w437), (6, 0, w438), (6, 0, w439), (6, 0, w440), (6, 1, w441), (6, 0, w442), (6, 0, w443), (6, 0, w444), (6, 1, w445), (6, 0, w446), (6, 0, w447), (6, 0, w448), (6, 0, w449), (6, 0, w450), (6, 0, w451), (6, 0, w452), (6, 0, w453), (6, 0, w454), (6, 0, w455), (6, 0, w456), (6, 0, w457), (6, 0, w458), (6, 0, w459)])
    (tbl_cons s347 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s346 (tbl_cons s345 (tbl_cons s429 (tbl_cons s430 (tbl_cons s431 (tbl_cons s432 (tbl_cons s85 (tbl_cons s433 (tbl_cons s164 (tbl_cons s434 (tbl_cons s230 (tbl_cons s435 (tbl_cons s289 (tbl_cons s436 (tbl_cons s396 (tbl_cons s400 (tbl_cons s368 (tbl_cons s437 (tbl_cons s438 (tbl_cons s439 (tbl_cons s440 (tbl_cons s441 (tbl_cons s442 (tbl_cons s443 (tbl_cons s444 (tbl_cons s445 (tbl_cons s446 (tbl_cons s447 (tbl_cons s448 (tbl_cons s449 (tbl_cons s450 (tbl_cons s451 (tbl_cons s452 (tbl_cons s453 (tbl_cons s454 (tbl_cons s455 (tbl_cons s456 (tbl_cons s457 (tbl_cons s458 (tbl_cons s459 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1756 : optimized 7 1 w370 = false :=
  opt_false_of_P (tbl := [(6, 0, w460), (6, 0, w461), (6, 0, w67), (6, 0, w400), (6, 0, w397), (6, 1, w65), (6, 0, w66), (6, 0, w370), (6, 0, w369), (6, 1, w445), (6, 0, w446), (6, 0, w447), (6, 0, w462), (6, 0, w463), (6, 0, w464), (6, 0, w465), (6, 0, w466), (6, 0, w467), (6, 0, w468), (6, 0, w469), (6, 0, w195), (6, 0, w470), (6, 0, w471), (6, 0, w143), (6, 0, w472), (6, 0, w473), (6, 0, w474), (6, 0, w475), (6, 0, w325), (6, 0, w476), (6, 0, w477), (6, 0, w269), (6, 0, w368), (6, 0, w345), (6, 0, w478), (6, 1, w479), (6, 0, w480), (6, 0, w481), (6, 0, w482), (6, 1, w483), (6, 0, w484), (6, 0, w485), (6, 0, w486), (6, 0, w487)])
    (tbl_cons s460 (tbl_cons s461 (tbl_cons s67 (tbl_cons s400 (tbl_cons s397 (tbl_cons s65 (tbl_cons s66 (tbl_cons s370 (tbl_cons s369 (tbl_cons s445 (tbl_cons s446 (tbl_cons s447 (tbl_cons s462 (tbl_cons s463 (tbl_cons s464 (tbl_cons s465 (tbl_cons s466 (tbl_cons s467 (tbl_cons s468 (tbl_cons s469 (tbl_cons s195 (tbl_cons s470 (tbl_cons s471 (tbl_cons s143 (tbl_cons s472 (tbl_cons s473 (tbl_cons s474 (tbl_cons s475 (tbl_cons s325 (tbl_cons s476 (tbl_cons s477 (tbl_cons s269 (tbl_cons s368 (tbl_cons s345 (tbl_cons s478 (tbl_cons s479 (tbl_cons s480 (tbl_cons s481 (tbl_cons s482 (tbl_cons s483 (tbl_cons s484 (tbl_cons s485 (tbl_cons s486 (tbl_cons s487 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1757 : optimized 7 1 w488 = false :=
  opt_false_of_P (tbl := [(6, 0, w488), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w489), (6, 0, w490), (6, 0, w491), (6, 0, w492), (6, 0, w493), (6, 0, w70), (6, 0, w494), (6, 0, w154), (6, 0, w495), (6, 0, w219), (6, 0, w496), (6, 0, w281), (6, 0, w497), (6, 0, w348), (6, 1, w498), (6, 0, w499), (6, 0, w500), (6, 0, w429), (6, 1, w501), (6, 0, w502), (6, 0, w503), (6, 0, w504), (6, 0, w505), (6, 0, w506), (6, 0, w507), (6, 1, w508), (6, 0, w509), (6, 0, w510), (6, 0, w247), (6, 0, w295), (6, 0, w379), (6, 0, w460), (6, 0, w511), (6, 0, w512), (6, 0, w513), (6, 0, w514), (6, 0, w515), (6, 0, w516), (6, 0, w517), (6, 0, w518), (6, 0, w519), (6, 0, w520), (6, 0, w521), (6, 0, w522)])
    (tbl_cons s488 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s489 (tbl_cons s490 (tbl_cons s491 (tbl_cons s492 (tbl_cons s493 (tbl_cons s70 (tbl_cons s494 (tbl_cons s154 (tbl_cons s495 (tbl_cons s219 (tbl_cons s496 (tbl_cons s281 (tbl_cons s497 (tbl_cons s348 (tbl_cons s498 (tbl_cons s499 (tbl_cons s500 (tbl_cons s429 (tbl_cons s501 (tbl_cons s502 (tbl_cons s503 (tbl_cons s504 (tbl_cons s505 (tbl_cons s506 (tbl_cons s507 (tbl_cons s508 (tbl_cons s509 (tbl_cons s510 (tbl_cons s247 (tbl_cons s295 (tbl_cons s379 (tbl_cons s460 (tbl_cons s511 (tbl_cons s512 (tbl_cons s513 (tbl_cons s514 (tbl_cons s515 (tbl_cons s516 (tbl_cons s517 (tbl_cons s518 (tbl_cons s519 (tbl_cons s520 (tbl_cons s521 (tbl_cons s522 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1758 : optimized 7 1 w525 = false :=
  opt_false_of_P (tbl := [(6, 1, w508), (6, 0, w509), (6, 0, w510), (6, 0, w523), (6, 0, w524), (6, 1, w65), (6, 0, w66), (6, 0, w525), (6, 0, w67), (6, 0, w493), (6, 0, w526), (6, 0, w527), (6, 0, w491), (6, 0, w490), (6, 0, w528), (6, 0, w529), (6, 0, w530), (6, 0, w116), (6, 0, w531), (6, 0, w190), (6, 0, w532), (6, 0, w258), (6, 0, w533), (6, 0, w320), (6, 1, w534), (6, 0, w535), (6, 0, w536), (6, 0, w406), (6, 1, w537), (6, 0, w538), (6, 0, w539), (6, 0, w467), (6, 1, w540), (6, 0, w541), (6, 0, w542), (6, 0, w543), (6, 1, w544), (6, 0, w545), (6, 0, w546), (6, 0, w547), (6, 0, w548), (6, 0, w549), (6, 0, w550), (6, 0, w551)])
    (tbl_cons s508 (tbl_cons s509 (tbl_cons s510 (tbl_cons s523 (tbl_cons s524 (tbl_cons s65 (tbl_cons s66 (tbl_cons s525 (tbl_cons s67 (tbl_cons s493 (tbl_cons s526 (tbl_cons s527 (tbl_cons s491 (tbl_cons s490 (tbl_cons s528 (tbl_cons s529 (tbl_cons s530 (tbl_cons s116 (tbl_cons s531 (tbl_cons s190 (tbl_cons s532 (tbl_cons s258 (tbl_cons s533 (tbl_cons s320 (tbl_cons s534 (tbl_cons s535 (tbl_cons s536 (tbl_cons s406 (tbl_cons s537 (tbl_cons s538 (tbl_cons s539 (tbl_cons s467 (tbl_cons s540 (tbl_cons s541 (tbl_cons s542 (tbl_cons s543 (tbl_cons s544 (tbl_cons s545 (tbl_cons s546 (tbl_cons s547 (tbl_cons s548 (tbl_cons s549 (tbl_cons s550 (tbl_cons s551 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1759 : optimized 7 1 w490 = false :=
  opt_false_of_P (tbl := [(6, 0, w490), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w489), (6, 0, w488), (6, 0, w523), (6, 0, w525), (6, 0, w491), (6, 0, w72), (6, 0, w552), (6, 0, w156), (6, 0, w553), (6, 0, w221), (6, 0, w554), (6, 0, w283), (6, 0, w555), (6, 0, w352), (6, 0, w556), (6, 0, w431), (6, 0, w557), (6, 0, w558), (6, 0, w559), (6, 0, w560), (6, 0, w561), (6, 1, w562), (6, 0, w563), (6, 0, w564), (6, 0, w565), (6, 0, w566), (6, 0, w567), (6, 0, w568), (6, 0, w569), (6, 0, w570), (6, 0, w571), (6, 0, w572), (6, 0, w573), (6, 0, w574), (6, 0, w575), (6, 0, w576)])
    (tbl_cons s490 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s489 (tbl_cons s488 (tbl_cons s523 (tbl_cons s525 (tbl_cons s491 (tbl_cons s72 (tbl_cons s552 (tbl_cons s156 (tbl_cons s553 (tbl_cons s221 (tbl_cons s554 (tbl_cons s283 (tbl_cons s555 (tbl_cons s352 (tbl_cons s556 (tbl_cons s431 (tbl_cons s557 (tbl_cons s558 (tbl_cons s559 (tbl_cons s560 (tbl_cons s561 (tbl_cons s562 (tbl_cons s563 (tbl_cons s564 (tbl_cons s565 (tbl_cons s566 (tbl_cons s567 (tbl_cons s568 (tbl_cons s569 (tbl_cons s570 (tbl_cons s571 (tbl_cons s572 (tbl_cons s573 (tbl_cons s574 (tbl_cons s575 (tbl_cons s576 tbl_nil))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1760 : optimized 7 1 w493 = false :=
  opt_false_of_P (tbl := [(6, 0, w67), (6, 0, w525), (6, 0, w524), (6, 1, w65), (6, 0, w66), (6, 0, w493), (6, 0, w492), (6, 1, w562), (6, 0, w563), (6, 0, w564), (6, 0, w248), (6, 0, w296), (6, 0, w380), (6, 0, w461), (6, 0, w577), (6, 0, w578), (6, 0, w491), (6, 0, w488), (6, 0, w187), (6, 0, w579), (6, 0, w117), (6, 0, w580), (6, 0, w313), (6, 0, w581), (6, 0, w259), (6, 0, w582), (6, 0, w464), (6, 0, w583), (6, 0, w407), (6, 0, w584), (6, 0, w585), (6, 1, w586), (6, 0, w587), (6, 0, w588), (6, 0, w589), (6, 1, w590), (6, 0, w591), (6, 0, w592), (6, 0, w593), (6, 0, w594), (6, 0, w595), (6, 0, w596), (6, 0, w597), (6, 0, w598)])
    (tbl_cons s67 (tbl_cons s525 (tbl_cons s524 (tbl_cons s65 (tbl_cons s66 (tbl_cons s493 (tbl_cons s492 (tbl_cons s562 (tbl_cons s563 (tbl_cons s564 (tbl_cons s248 (tbl_cons s296 (tbl_cons s380 (tbl_cons s461 (tbl_cons s577 (tbl_cons s578 (tbl_cons s491 (tbl_cons s488 (tbl_cons s187 (tbl_cons s579 (tbl_cons s117 (tbl_cons s580 (tbl_cons s313 (tbl_cons s581 (tbl_cons s259 (tbl_cons s582 (tbl_cons s464 (tbl_cons s583 (tbl_cons s407 (tbl_cons s584 (tbl_cons s585 (tbl_cons s586 (tbl_cons s587 (tbl_cons s588 (tbl_cons s589 (tbl_cons s590 (tbl_cons s591 (tbl_cons s592 (tbl_cons s593 (tbl_cons s594 (tbl_cons s595 (tbl_cons s596 (tbl_cons s597 (tbl_cons s598 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1761 : optimized 7 2 w599 = false :=
  opt_false_of_P (tbl := [(6, 1, w599), (6, 0, w600), (6, 0, w601), (6, 0, w602), (6, 1, w603), (6, 1, w604), (6, 0, w605), (6, 0, w606), (6, 0, w607), (6, 0, w608), (6, 0, w609), (6, 0, w610), (6, 2, w611), (6, 1, w612), (6, 1, w613), (6, 0, w614), (6, 1, w166), (6, 0, w615), (6, 1, w616), (6, 0, w617), (6, 0, w618), (6, 0, w619), (6, 0, w620), (6, 0, w621), (6, 0, w622), (6, 1, w623), (6, 0, w624), (6, 1, w437), (6, 0, w625), (6, 0, w626), (6, 0, w511), (6, 0, w526), (6, 0, w565), (6, 0, w577), (6, 0, w100), (6, 0, w111), (6, 0, w179), (6, 0, w185), (6, 0, w239), (6, 0, w252), (6, 0, w300), (6, 0, w311), (6, 0, w384), (6, 0, w398), (6, 0, w448), (6, 0, w462), (6, 0, w627), (6, 0, w628), (6, 0, w629), (6, 0, w630), (6, 0, w631), (6, 0, w632), (6, 0, w633), (6, 0, w634), (6, 0, w635), (6, 0, w636), (6, 0, w637), (6, 0, w638), (6, 0, w639), (6, 0, w640), (6, 0, w641), (6, 0, w642), (6, 0, w643), (6, 0, w644), (6, 0, w645), (6, 0, w646), (6, 0, w647), (6, 0, w648), (6, 0, w649), (6, 0, w650)])
    (tbl_cons s599 (tbl_cons s600 (tbl_cons s601 (tbl_cons s602 (tbl_cons s603 (tbl_cons s604 (tbl_cons s605 (tbl_cons s606 (tbl_cons s607 (tbl_cons s608 (tbl_cons s609 (tbl_cons s610 (tbl_cons s611 (tbl_cons s612 (tbl_cons s613 (tbl_cons s614 (tbl_cons s166 (tbl_cons s615 (tbl_cons s616 (tbl_cons s617 (tbl_cons s618 (tbl_cons s619 (tbl_cons s620 (tbl_cons s621 (tbl_cons s622 (tbl_cons s623 (tbl_cons s624 (tbl_cons s437 (tbl_cons s625 (tbl_cons s626 (tbl_cons s511 (tbl_cons s526 (tbl_cons s565 (tbl_cons s577 (tbl_cons s100 (tbl_cons s111 (tbl_cons s179 (tbl_cons s185 (tbl_cons s239 (tbl_cons s252 (tbl_cons s300 (tbl_cons s311 (tbl_cons s384 (tbl_cons s398 (tbl_cons s448 (tbl_cons s462 (tbl_cons s627 (tbl_cons s628 (tbl_cons s629 (tbl_cons s630 (tbl_cons s631 (tbl_cons s632 (tbl_cons s633 (tbl_cons s634 (tbl_cons s635 (tbl_cons s636 (tbl_cons s637 (tbl_cons s638 (tbl_cons s639 (tbl_cons s640 (tbl_cons s641 (tbl_cons s642 (tbl_cons s643 (tbl_cons s644 (tbl_cons s645 (tbl_cons s646 (tbl_cons s647 (tbl_cons s648 (tbl_cons s649 (tbl_cons s650 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1762 : optimized 7 1 w651 = false :=
  opt_false_of_P (tbl := [(6, 0, w651), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w652), (6, 0, w653), (6, 0, w504), (6, 0, w654), (6, 0, w558), (6, 0, w655), (6, 0, w89), (6, 1, w656), (6, 0, w657), (6, 0, w658), (6, 0, w168), (6, 1, w659), (6, 0, w660), (6, 0, w661), (6, 0, w232), (6, 0, w662), (6, 0, w291), (6, 0, w663), (6, 0, w371), (6, 0, w664), (6, 0, w439), (6, 0, w665), (6, 1, w599), (6, 0, w600), (6, 0, w666), (6, 0, w602), (6, 0, w667), (6, 0, w668), (6, 1, w669), (6, 0, w670), (6, 0, w671), (6, 1, w603), (6, 0, w605), (6, 0, w672), (6, 0, w673), (6, 0, w674), (6, 0, w675), (6, 0, w676), (6, 0, w677), (6, 0, w678), (6, 0, w679), (6, 0, w680), (6, 0, w681), (6, 0, w682), (6, 0, w683), (6, 0, w684), (6, 0, w685), (6, 0, w686), (6, 0, w687)])
    (tbl_cons s651 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s652 (tbl_cons s653 (tbl_cons s504 (tbl_cons s654 (tbl_cons s558 (tbl_cons s655 (tbl_cons s89 (tbl_cons s656 (tbl_cons s657 (tbl_cons s658 (tbl_cons s168 (tbl_cons s659 (tbl_cons s660 (tbl_cons s661 (tbl_cons s232 (tbl_cons s662 (tbl_cons s291 (tbl_cons s663 (tbl_cons s371 (tbl_cons s664 (tbl_cons s439 (tbl_cons s665 (tbl_cons s599 (tbl_cons s600 (tbl_cons s666 (tbl_cons s602 (tbl_cons s667 (tbl_cons s668 (tbl_cons s669 (tbl_cons s670 (tbl_cons s671 (tbl_cons s603 (tbl_cons s605 (tbl_cons s672 (tbl_cons s673 (tbl_cons s674 (tbl_cons s675 (tbl_cons s676 (tbl_cons s677 (tbl_cons s678 (tbl_cons s679 (tbl_cons s680 (tbl_cons s681 (tbl_cons s682 (tbl_cons s683 (tbl_cons s684 (tbl_cons s685 (tbl_cons s686 (tbl_cons s687 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1763 : optimized 7 1 w690 = false :=
  opt_false_of_P (tbl := [(6, 0, w253), (6, 0, w301), (6, 1, w669), (6, 0, w670), (6, 0, w671), (6, 0, w688), (6, 0, w689), (6, 1, w65), (6, 0, w66), (6, 0, w690), (6, 0, w67), (6, 0, w668), (6, 0, w691), (6, 0, w543), (6, 0, w589), (6, 0, w692), (6, 0, w693), (6, 0, w694), (6, 0, w695), (6, 0, w147), (6, 0, w203), (6, 0, w696), (6, 0, w697), (6, 0, w276), (6, 0, w337), (6, 0, w698), (6, 0, w699), (6, 0, w700), (6, 0, w701), (6, 0, w424), (6, 0, w482), (6, 0, w702), (6, 0, w666), (6, 1, w604), (6, 0, w653)])
    (tbl_cons s253 (tbl_cons s301 (tbl_cons s669 (tbl_cons s670 (tbl_cons s671 (tbl_cons s688 (tbl_cons s689 (tbl_cons s65 (tbl_cons s66 (tbl_cons s690 (tbl_cons s67 (tbl_cons s668 (tbl_cons s691 (tbl_cons s543 (tbl_cons s589 (tbl_cons s692 (tbl_cons s693 (tbl_cons s694 (tbl_cons s695 (tbl_cons s147 (tbl_cons s203 (tbl_cons s696 (tbl_cons s697 (tbl_cons s276 (tbl_cons s337 (tbl_cons s698 (tbl_cons s699 (tbl_cons s700 (tbl_cons s701 (tbl_cons s424 (tbl_cons s482 (tbl_cons s702 (tbl_cons s666 (tbl_cons s604 (tbl_cons s653 tbl_nil)))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1764 : optimized 7 2 w604 = false :=
  opt_false_of_P (tbl := [(6, 1, w604), (6, 0, w703), (6, 0, w704), (6, 0, w705), (6, 1, w603), (6, 1, w599), (6, 0, w605), (6, 0, w706), (6, 0, w707), (6, 0, w708), (6, 0, w709), (6, 0, w710), (6, 1, w711), (6, 0, w712), (6, 1, w170), (6, 0, w713), (6, 0, w714), (6, 0, w715), (6, 0, w716), (6, 0, w717), (6, 0, w718), (6, 0, w719), (6, 1, w720), (6, 0, w721), (6, 1, w441), (6, 0, w722), (6, 0, w723), (6, 0, w512), (6, 0, w527), (6, 0, w566), (6, 0, w578), (6, 0, w101), (6, 0, w112), (6, 0, w180), (6, 0, w186), (6, 0, w240), (6, 1, w254), (6, 0, w255), (6, 1, w302), (6, 0, w303), (6, 0, w312), (6, 0, w385), (6, 0, w399), (6, 0, w449), (6, 0, w463), (6, 0, w724), (6, 0, w725), (6, 0, w726), (6, 0, w727), (6, 0, w728), (6, 0, w729), (6, 0, w730), (6, 0, w731), (6, 0, w732), (6, 0, w733), (6, 0, w734), (6, 0, w735), (6, 0, w736), (6, 0, w737), (6, 0, w738), (6, 0, w739), (6, 0, w740), (6, 0, w741), (6, 0, w742), (6, 0, w743), (6, 0, w744), (6, 0, w745), (6, 0, w746), (6, 0, w747)])
    (tbl_cons s604 (tbl_cons s703 (tbl_cons s704 (tbl_cons s705 (tbl_cons s603 (tbl_cons s599 (tbl_cons s605 (tbl_cons s706 (tbl_cons s707 (tbl_cons s708 (tbl_cons s709 (tbl_cons s710 (tbl_cons s711 (tbl_cons s712 (tbl_cons s170 (tbl_cons s713 (tbl_cons s714 (tbl_cons s715 (tbl_cons s716 (tbl_cons s717 (tbl_cons s718 (tbl_cons s719 (tbl_cons s720 (tbl_cons s721 (tbl_cons s441 (tbl_cons s722 (tbl_cons s723 (tbl_cons s512 (tbl_cons s527 (tbl_cons s566 (tbl_cons s578 (tbl_cons s101 (tbl_cons s112 (tbl_cons s180 (tbl_cons s186 (tbl_cons s240 (tbl_cons s254 (tbl_cons s255 (tbl_cons s302 (tbl_cons s303 (tbl_cons s312 (tbl_cons s385 (tbl_cons s399 (tbl_cons s449 (tbl_cons s463 (tbl_cons s724 (tbl_cons s725 (tbl_cons s726 (tbl_cons s727 (tbl_cons s728 (tbl_cons s729 (tbl_cons s730 (tbl_cons s731 (tbl_cons s732 (tbl_cons s733 (tbl_cons s734 (tbl_cons s735 (tbl_cons s736 (tbl_cons s737 (tbl_cons s738 (tbl_cons s739 (tbl_cons s740 (tbl_cons s741 (tbl_cons s742 (tbl_cons s743 (tbl_cons s744 (tbl_cons s745 (tbl_cons s746 (tbl_cons s747 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1765 : optimized 7 1 w653 = false :=
  opt_false_of_P (tbl := [(6, 0, w653), (6, 1, w65), (6, 0, w66), (6, 0, w67), (6, 0, w652), (6, 0, w651), (6, 0, w506), (6, 0, w748), (6, 0, w560), (6, 0, w749), (6, 0, w93), (6, 0, w750), (6, 0, w172), (6, 0, w751), (6, 0, w234), (6, 0, w752), (6, 0, w293), (6, 0, w753), (6, 0, w375), (6, 0, w754), (6, 0, w443), (6, 0, w755), (6, 0, w705), (6, 0, w688), (6, 0, w690), (6, 1, w604), (6, 0, w703), (6, 0, w666), (6, 0, w256), (6, 0, w304), (6, 1, w603), (6, 0, w605), (6, 1, w756), (6, 0, w757), (6, 0, w758), (6, 0, w759), (6, 0, w760), (6, 0, w761), (6, 0, w762), (6, 0, w763), (6, 0, w764), (6, 0, w765), (6, 0, w766), (6, 0, w767), (6, 0, w768), (6, 0, w769), (6, 0, w770), (6, 0, w771), (6, 0, w772), (6, 0, w773), (6, 0, w774)])
    (tbl_cons s653 (tbl_cons s65 (tbl_cons s66 (tbl_cons s67 (tbl_cons s652 (tbl_cons s651 (tbl_cons s506 (tbl_cons s748 (tbl_cons s560 (tbl_cons s749 (tbl_cons s93 (tbl_cons s750 (tbl_cons s172 (tbl_cons s751 (tbl_cons s234 (tbl_cons s752 (tbl_cons s293 (tbl_cons s753 (tbl_cons s375 (tbl_cons s754 (tbl_cons s443 (tbl_cons s755 (tbl_cons s705 (tbl_cons s688 (tbl_cons s690 (tbl_cons s604 (tbl_cons s703 (tbl_cons s666 (tbl_cons s256 (tbl_cons s304 (tbl_cons s603 (tbl_cons s605 (tbl_cons s756 (tbl_cons s757 (tbl_cons s758 (tbl_cons s759 (tbl_cons s760 (tbl_cons s761 (tbl_cons s762 (tbl_cons s763 (tbl_cons s764 (tbl_cons s765 (tbl_cons s766 (tbl_cons s767 (tbl_cons s768 (tbl_cons s769 (tbl_cons s770 (tbl_cons s771 (tbl_cons s772 (tbl_cons s773 (tbl_cons s774 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1766 : optimized 7 1 w668 = false :=
  opt_false_of_P (tbl := [(6, 0, w67), (6, 0, w690), (6, 0, w689), (6, 1, w65), (6, 0, w66), (6, 0, w668), (6, 0, w667), (6, 1, w756), (6, 0, w757), (6, 0, w758), (6, 0, w585), (6, 0, w775), (6, 0, w776), (6, 0, w547), (6, 0, w199), (6, 0, w777), (6, 0, w778), (6, 0, w151), (6, 0, w779), (6, 0, w780), (6, 0, w333), (6, 0, w781), (6, 0, w782), (6, 0, w280), (6, 0, w478), (6, 0, w783), (6, 0, w425), (6, 0, w784), (6, 0, w666), (6, 1, w599), (6, 0, w651), (6, 0, w785), (6, 0, w786)])
    (tbl_cons s67 (tbl_cons s690 (tbl_cons s689 (tbl_cons s65 (tbl_cons s66 (tbl_cons s668 (tbl_cons s667 (tbl_cons s756 (tbl_cons s757 (tbl_cons s758 (tbl_cons s585 (tbl_cons s775 (tbl_cons s776 (tbl_cons s547 (tbl_cons s199 (tbl_cons s777 (tbl_cons s778 (tbl_cons s151 (tbl_cons s779 (tbl_cons s780 (tbl_cons s333 (tbl_cons s781 (tbl_cons s782 (tbl_cons s280 (tbl_cons s478 (tbl_cons s783 (tbl_cons s425 (tbl_cons s784 (tbl_cons s666 (tbl_cons s599 (tbl_cons s651 (tbl_cons s785 (tbl_cons s786 tbl_nil)))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1767 : optimized 7 1 w801 = false :=
  opt_false_of_P (tbl := [(6, 0, w77), (6, 1, w787), (6, 0, w788), (6, 0, w789), (6, 0, w191), (6, 1, w790), (6, 0, w791), (6, 0, w792), (6, 0, w793), (6, 1, w794), (6, 0, w795), (6, 0, w796), (6, 0, w797), (6, 1, w798), (6, 0, w799), (6, 0, w800), (6, 0, w801), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w802), (6, 0, w803), (6, 0, w225), (6, 0, w804), (6, 0, w805), (6, 0, w806), (6, 1, w807), (6, 0, w808), (6, 0, w809), (6, 0, w810), (6, 1, w811), (6, 0, w812), (6, 0, w813), (6, 0, w814), (6, 1, w815), (6, 0, w816), (6, 0, w817), (6, 0, w818), (6, 1, w819), (6, 0, w820), (6, 0, w821), (6, 0, w241), (6, 0, w305), (6, 0, w639), (6, 0, w736), (6, 0, w822), (6, 0, w823), (6, 1, w824), (6, 0, w825), (6, 0, w826), (6, 0, w827), (6, 0, w828), (6, 0, w829), (6, 0, w830), (6, 0, w831), (6, 0, w832)])
    (tbl_cons s77 (tbl_cons s787 (tbl_cons s788 (tbl_cons s789 (tbl_cons s191 (tbl_cons s790 (tbl_cons s791 (tbl_cons s792 (tbl_cons s793 (tbl_cons s794 (tbl_cons s795 (tbl_cons s796 (tbl_cons s797 (tbl_cons s798 (tbl_cons s799 (tbl_cons s800 (tbl_cons s801 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s802 (tbl_cons s803 (tbl_cons s225 (tbl_cons s804 (tbl_cons s805 (tbl_cons s806 (tbl_cons s807 (tbl_cons s808 (tbl_cons s809 (tbl_cons s810 (tbl_cons s811 (tbl_cons s812 (tbl_cons s813 (tbl_cons s814 (tbl_cons s815 (tbl_cons s816 (tbl_cons s817 (tbl_cons s818 (tbl_cons s819 (tbl_cons s820 (tbl_cons s821 (tbl_cons s241 (tbl_cons s305 (tbl_cons s639 (tbl_cons s736 (tbl_cons s822 (tbl_cons s823 (tbl_cons s824 (tbl_cons s825 (tbl_cons s826 (tbl_cons s827 (tbl_cons s828 (tbl_cons s829 (tbl_cons s830 (tbl_cons s831 (tbl_cons s832 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1768 : optimized 7 1 w843 = false :=
  opt_false_of_P (tbl := [(6, 0, w640), (6, 0, w737), (6, 0, w833), (6, 0, w131), (6, 0, w160), (6, 0, w834), (6, 0, w835), (6, 0, w836), (6, 0, w837), (6, 0, w838), (6, 1, w824), (6, 0, w825), (6, 0, w826), (6, 0, w839), (6, 0, w840), (6, 0, w841), (6, 0, w842), (6, 1, w65), (6, 0, w74), (6, 0, w843), (6, 0, w67), (6, 0, w805), (6, 0, w225), (6, 0, w803), (6, 0, w844), (6, 0, w845), (6, 0, w846), (6, 0, w847), (6, 0, w848), (6, 0, w849), (6, 0, w850), (6, 0, w851), (6, 0, w852), (6, 0, w853)])
    (tbl_cons s640 (tbl_cons s737 (tbl_cons s833 (tbl_cons s131 (tbl_cons s160 (tbl_cons s834 (tbl_cons s835 (tbl_cons s836 (tbl_cons s837 (tbl_cons s838 (tbl_cons s824 (tbl_cons s825 (tbl_cons s826 (tbl_cons s839 (tbl_cons s840 (tbl_cons s841 (tbl_cons s842 (tbl_cons s65 (tbl_cons s74 (tbl_cons s843 (tbl_cons s67 (tbl_cons s805 (tbl_cons s225 (tbl_cons s803 (tbl_cons s844 (tbl_cons s845 (tbl_cons s846 (tbl_cons s847 (tbl_cons s848 (tbl_cons s849 (tbl_cons s850 (tbl_cons s851 (tbl_cons s852 (tbl_cons s853 tbl_nil))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1769 : optimized 7 1 w803 = false :=
  opt_false_of_P (tbl := [(6, 0, w79), (6, 0, w854), (6, 0, w855), (6, 0, w193), (6, 0, w242), (6, 0, w306), (6, 0, w641), (6, 0, w738), (6, 0, w856), (6, 0, w857), (6, 0, w858), (6, 0, w859), (6, 0, w803), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w802), (6, 0, w801), (6, 0, w839), (6, 0, w843), (6, 0, w225), (6, 0, w860), (6, 0, w861), (6, 0, w862), (6, 0, w863), (6, 0, w864), (6, 1, w865), (6, 0, w866), (6, 0, w867), (6, 0, w868), (6, 1, w869), (6, 0, w870), (6, 0, w871), (6, 1, w872), (6, 0, w873), (6, 0, w874), (6, 0, w875), (6, 0, w876), (6, 0, w877), (6, 0, w878), (6, 0, w879), (6, 0, w880)])
    (tbl_cons s79 (tbl_cons s854 (tbl_cons s855 (tbl_cons s193 (tbl_cons s242 (tbl_cons s306 (tbl_cons s641 (tbl_cons s738 (tbl_cons s856 (tbl_cons s857 (tbl_cons s858 (tbl_cons s859 (tbl_cons s803 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s802 (tbl_cons s801 (tbl_cons s839 (tbl_cons s843 (tbl_cons s225 (tbl_cons s860 (tbl_cons s861 (tbl_cons s862 (tbl_cons s863 (tbl_cons s864 (tbl_cons s865 (tbl_cons s866 (tbl_cons s867 (tbl_cons s868 (tbl_cons s869 (tbl_cons s870 (tbl_cons s871 (tbl_cons s872 (tbl_cons s873 (tbl_cons s874 (tbl_cons s875 (tbl_cons s876 (tbl_cons s877 (tbl_cons s878 (tbl_cons s879 (tbl_cons s880 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1770 : optimized 7 1 w805 = false :=
  opt_false_of_P (tbl := [(6, 0, w158), (6, 0, w881), (6, 0, w882), (6, 0, w135), (6, 0, w642), (6, 0, w739), (6, 0, w883), (6, 0, w884), (6, 0, w885), (6, 0, w886), (6, 0, w887), (6, 0, w888), (6, 0, w67), (6, 0, w843), (6, 0, w840), (6, 1, w65), (6, 0, w74), (6, 0, w805), (6, 0, w804), (6, 1, w872), (6, 0, w873), (6, 0, w874), (6, 0, w889), (6, 0, w890), (6, 0, w225), (6, 0, w801), (6, 0, w891), (6, 0, w892), (6, 0, w893), (6, 0, w894), (6, 0, w895), (6, 0, w896), (6, 0, w897), (6, 0, w898), (6, 0, w899), (6, 0, w900)])
    (tbl_cons s158 (tbl_cons s881 (tbl_cons s882 (tbl_cons s135 (tbl_cons s642 (tbl_cons s739 (tbl_cons s883 (tbl_cons s884 (tbl_cons s885 (tbl_cons s886 (tbl_cons s887 (tbl_cons s888 (tbl_cons s67 (tbl_cons s843 (tbl_cons s840 (tbl_cons s65 (tbl_cons s74 (tbl_cons s805 (tbl_cons s804 (tbl_cons s872 (tbl_cons s873 (tbl_cons s874 (tbl_cons s889 (tbl_cons s890 (tbl_cons s225 (tbl_cons s801 (tbl_cons s891 (tbl_cons s892 (tbl_cons s893 (tbl_cons s894 (tbl_cons s895 (tbl_cons s896 (tbl_cons s897 (tbl_cons s898 (tbl_cons s899 (tbl_cons s900 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1771 : optimized 7 1 w907 = false :=
  opt_false_of_P (tbl := [(6, 0, w81), (6, 0, w901), (6, 0, w195), (6, 0, w902), (6, 0, w903), (6, 0, w904), (6, 0, w905), (6, 0, w906), (6, 0, w907), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w908), (6, 0, w909), (6, 0, w806), (6, 0, w910), (6, 0, w860), (6, 0, w911), (6, 0, w368), (6, 0, w912), (6, 0, w913), (6, 0, w914), (6, 1, w915), (6, 0, w916), (6, 0, w917), (6, 0, w918), (6, 1, w919), (6, 0, w920), (6, 0, w921), (6, 0, w388), (6, 0, w452), (6, 0, w643), (6, 0, w740), (6, 0, w922), (6, 0, w923), (6, 1, w924), (6, 0, w925), (6, 0, w926), (6, 0, w927), (6, 0, w928), (6, 0, w929), (6, 0, w930)])
    (tbl_cons s81 (tbl_cons s901 (tbl_cons s195 (tbl_cons s902 (tbl_cons s903 (tbl_cons s904 (tbl_cons s905 (tbl_cons s906 (tbl_cons s907 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s908 (tbl_cons s909 (tbl_cons s806 (tbl_cons s910 (tbl_cons s860 (tbl_cons s911 (tbl_cons s368 (tbl_cons s912 (tbl_cons s913 (tbl_cons s914 (tbl_cons s915 (tbl_cons s916 (tbl_cons s917 (tbl_cons s918 (tbl_cons s919 (tbl_cons s920 (tbl_cons s921 (tbl_cons s388 (tbl_cons s452 (tbl_cons s643 (tbl_cons s740 (tbl_cons s922 (tbl_cons s923 (tbl_cons s924 (tbl_cons s925 (tbl_cons s926 (tbl_cons s927 (tbl_cons s928 (tbl_cons s929 (tbl_cons s930 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1772 : optimized 7 1 w943 = false :=
  opt_false_of_P (tbl := [(6, 0, w121), (6, 0, w207), (6, 0, w411), (6, 0, w472), (6, 0, w644), (6, 0, w741), (6, 0, w931), (6, 0, w139), (6, 0, w164), (6, 0, w932), (6, 0, w933), (6, 0, w934), (6, 0, w935), (6, 0, w936), (6, 0, w937), (6, 0, w938), (6, 1, w924), (6, 0, w925), (6, 0, w926), (6, 0, w939), (6, 0, w940), (6, 0, w941), (6, 0, w942), (6, 1, w65), (6, 0, w74), (6, 0, w943), (6, 0, w67), (6, 0, w913), (6, 0, w944), (6, 0, w945), (6, 0, w946), (6, 0, w847), (6, 0, w893), (6, 0, w947), (6, 0, w948), (6, 0, w949), (6, 0, w368), (6, 0, w909), (6, 0, w950), (6, 1, w951), (6, 0, w952), (6, 0, w953), (6, 1, w954), (6, 0, w955), (6, 0, w956), (6, 0, w957)])
    (tbl_cons s121 (tbl_cons s207 (tbl_cons s411 (tbl_cons s472 (tbl_cons s644 (tbl_cons s741 (tbl_cons s931 (tbl_cons s139 (tbl_cons s164 (tbl_cons s932 (tbl_cons s933 (tbl_cons s934 (tbl_cons s935 (tbl_cons s936 (tbl_cons s937 (tbl_cons s938 (tbl_cons s924 (tbl_cons s925 (tbl_cons s926 (tbl_cons s939 (tbl_cons s940 (tbl_cons s941 (tbl_cons s942 (tbl_cons s65 (tbl_cons s74 (tbl_cons s943 (tbl_cons s67 (tbl_cons s913 (tbl_cons s944 (tbl_cons s945 (tbl_cons s946 (tbl_cons s847 (tbl_cons s893 (tbl_cons s947 (tbl_cons s948 (tbl_cons s949 (tbl_cons s368 (tbl_cons s909 (tbl_cons s950 (tbl_cons s951 (tbl_cons s952 (tbl_cons s953 (tbl_cons s954 (tbl_cons s955 (tbl_cons s956 (tbl_cons s957 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1773 : optimized 7 1 w909 = false :=
  opt_false_of_P (tbl := [(6, 0, w85), (6, 0, w958), (6, 0, w959), (6, 0, w197), (6, 0, w122), (6, 0, w208), (6, 0, w389), (6, 0, w453), (6, 0, w645), (6, 0, w742), (6, 0, w960), (6, 0, w961), (6, 0, w962), (6, 0, w963), (6, 0, w964), (6, 0, w965), (6, 0, w909), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w908), (6, 0, w907), (6, 0, w810), (6, 0, w966), (6, 0, w862), (6, 0, w967), (6, 0, w939), (6, 0, w943), (6, 0, w368), (6, 0, w968), (6, 1, w969), (6, 0, w970), (6, 0, w971), (6, 0, w972), (6, 1, w973), (6, 0, w974), (6, 0, w975), (6, 1, w976), (6, 0, w977), (6, 0, w978), (6, 0, w979), (6, 0, w980), (6, 0, w981), (6, 0, w982)])
    (tbl_cons s85 (tbl_cons s958 (tbl_cons s959 (tbl_cons s197 (tbl_cons s122 (tbl_cons s208 (tbl_cons s389 (tbl_cons s453 (tbl_cons s645 (tbl_cons s742 (tbl_cons s960 (tbl_cons s961 (tbl_cons s962 (tbl_cons s963 (tbl_cons s964 (tbl_cons s965 (tbl_cons s909 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s908 (tbl_cons s907 (tbl_cons s810 (tbl_cons s966 (tbl_cons s862 (tbl_cons s967 (tbl_cons s939 (tbl_cons s943 (tbl_cons s368 (tbl_cons s968 (tbl_cons s969 (tbl_cons s970 (tbl_cons s971 (tbl_cons s972 (tbl_cons s973 (tbl_cons s974 (tbl_cons s975 (tbl_cons s976 (tbl_cons s977 (tbl_cons s978 (tbl_cons s979 (tbl_cons s980 (tbl_cons s981 (tbl_cons s982 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1774 : optimized 7 1 w913 = false :=
  opt_false_of_P (tbl := [(6, 0, w162), (6, 0, w983), (6, 0, w984), (6, 0, w143), (6, 0, w412), (6, 0, w473), (6, 0, w646), (6, 0, w743), (6, 0, w985), (6, 1, w986), (6, 0, w987), (6, 0, w988), (6, 1, w989), (6, 0, w990), (6, 0, w991), (6, 0, w992), (6, 0, w993), (6, 0, w994), (6, 0, w67), (6, 0, w943), (6, 0, w940), (6, 1, w65), (6, 0, w74), (6, 0, w913), (6, 0, w912), (6, 1, w976), (6, 0, w977), (6, 0, w978), (6, 0, w995), (6, 0, w996), (6, 0, w891), (6, 1, w997), (6, 0, w998), (6, 0, w999), (6, 0, w848), (6, 1, w1000), (6, 0, w1001), (6, 0, w1002), (6, 0, w368), (6, 0, w907), (6, 0, w1003), (6, 1, w1004), (6, 0, w1005), (6, 0, w1006), (6, 0, w1007), (6, 1, w1008), (6, 0, w1009), (6, 0, w1010), (6, 0, w1011), (6, 0, w1012), (6, 0, w1013), (6, 0, w1014)])
    (tbl_cons s162 (tbl_cons s983 (tbl_cons s984 (tbl_cons s143 (tbl_cons s412 (tbl_cons s473 (tbl_cons s646 (tbl_cons s743 (tbl_cons s985 (tbl_cons s986 (tbl_cons s987 (tbl_cons s988 (tbl_cons s989 (tbl_cons s990 (tbl_cons s991 (tbl_cons s992 (tbl_cons s993 (tbl_cons s994 (tbl_cons s67 (tbl_cons s943 (tbl_cons s940 (tbl_cons s65 (tbl_cons s74 (tbl_cons s913 (tbl_cons s912 (tbl_cons s976 (tbl_cons s977 (tbl_cons s978 (tbl_cons s995 (tbl_cons s996 (tbl_cons s891 (tbl_cons s997 (tbl_cons s998 (tbl_cons s999 (tbl_cons s848 (tbl_cons s1000 (tbl_cons s1001 (tbl_cons s1002 (tbl_cons s368 (tbl_cons s907 (tbl_cons s1003 (tbl_cons s1004 (tbl_cons s1005 (tbl_cons s1006 (tbl_cons s1007 (tbl_cons s1008 (tbl_cons s1009 (tbl_cons s1010 (tbl_cons s1011 (tbl_cons s1012 (tbl_cons s1013 (tbl_cons s1014 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1775 : optimized 7 1 w1017 = false :=
  opt_false_of_P (tbl := [(6, 0, w70), (6, 0, w1015), (6, 0, w1016), (6, 0, w187), (6, 0, w513), (6, 0, w567), (6, 0, w627), (6, 0, w724), (6, 0, w1017), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1018), (6, 0, w1019), (6, 0, w74), (6, 0, w1020), (6, 0, w1021), (6, 0, w793), (6, 0, w1022), (6, 0, w856), (6, 0, w1023), (6, 0, w903), (6, 0, w1024), (6, 0, w960), (6, 0, w1025), (6, 0, w1026), (6, 1, w1027), (6, 0, w1028), (6, 0, w1029), (6, 0, w1030), (6, 1, w1031), (6, 0, w1032), (6, 0, w1033), (6, 1, w1034), (6, 0, w1035), (6, 0, w1036), (6, 0, w1037), (6, 0, w1038), (6, 0, w822), (6, 0, w883), (6, 0, w1039), (6, 0, w1040), (6, 0, w1041), (6, 0, w1042)])
    (tbl_cons s70 (tbl_cons s1015 (tbl_cons s1016 (tbl_cons s187 (tbl_cons s513 (tbl_cons s567 (tbl_cons s627 (tbl_cons s724 (tbl_cons s1017 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1018 (tbl_cons s1019 (tbl_cons s74 (tbl_cons s1020 (tbl_cons s1021 (tbl_cons s793 (tbl_cons s1022 (tbl_cons s856 (tbl_cons s1023 (tbl_cons s903 (tbl_cons s1024 (tbl_cons s960 (tbl_cons s1025 (tbl_cons s1026 (tbl_cons s1027 (tbl_cons s1028 (tbl_cons s1029 (tbl_cons s1030 (tbl_cons s1031 (tbl_cons s1032 (tbl_cons s1033 (tbl_cons s1034 (tbl_cons s1035 (tbl_cons s1036 (tbl_cons s1037 (tbl_cons s1038 (tbl_cons s822 (tbl_cons s883 (tbl_cons s1039 (tbl_cons s1040 (tbl_cons s1041 (tbl_cons s1042 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1776 : optimized 7 1 w1047 = false :=
  opt_false_of_P (tbl := [(6, 0, w1043), (6, 0, w116), (6, 0, w156), (6, 0, w1044), (6, 0, w628), (6, 0, w725), (6, 1, w1034), (6, 0, w1035), (6, 0, w1036), (6, 0, w1045), (6, 0, w1046), (6, 1, w65), (6, 0, w491), (6, 0, w1047), (6, 0, w67), (6, 0, w1021), (6, 0, w1048), (6, 0, w1049), (6, 0, w74), (6, 0, w1019), (6, 0, w1050), (6, 0, w1051), (6, 0, w1052), (6, 0, w836), (6, 0, w1053), (6, 0, w888), (6, 0, w1054), (6, 0, w936), (6, 0, w1055), (6, 0, w992), (6, 0, w1056), (6, 0, w1057), (6, 0, w1058), (6, 0, w1059), (6, 0, w1060), (6, 0, w1061)])
    (tbl_cons s1043 (tbl_cons s116 (tbl_cons s156 (tbl_cons s1044 (tbl_cons s628 (tbl_cons s725 (tbl_cons s1034 (tbl_cons s1035 (tbl_cons s1036 (tbl_cons s1045 (tbl_cons s1046 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1047 (tbl_cons s67 (tbl_cons s1021 (tbl_cons s1048 (tbl_cons s1049 (tbl_cons s74 (tbl_cons s1019 (tbl_cons s1050 (tbl_cons s1051 (tbl_cons s1052 (tbl_cons s836 (tbl_cons s1053 (tbl_cons s888 (tbl_cons s1054 (tbl_cons s936 (tbl_cons s1055 (tbl_cons s992 (tbl_cons s1056 (tbl_cons s1057 (tbl_cons s1058 (tbl_cons s1059 (tbl_cons s1060 (tbl_cons s1061 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1777 : optimized 7 1 w1021 = false :=
  opt_false_of_P (tbl := [(6, 0, w72), (6, 0, w1062), (6, 0, w1063), (6, 0, w190), (6, 0, w514), (6, 0, w568), (6, 0, w630), (6, 0, w727), (6, 0, w67), (6, 0, w1046), (6, 0, w1047), (6, 0, w1021), (6, 1, w65), (6, 0, w491), (6, 0, w74), (6, 0, w1020), (6, 0, w1017), (6, 0, w797), (6, 0, w1064), (6, 0, w859), (6, 0, w1065), (6, 0, w905), (6, 1, w1066), (6, 0, w1067), (6, 0, w1068), (6, 0, w963), (6, 1, w1069), (6, 0, w1070), (6, 0, w1071), (6, 0, w1072), (6, 1, w1073), (6, 0, w1074), (6, 0, w1075), (6, 0, w1076), (6, 1, w1077), (6, 0, w1078), (6, 0, w1079), (6, 1, w1080), (6, 0, w1081), (6, 0, w1082), (6, 0, w1083), (6, 0, w1084), (6, 0, w1085), (6, 0, w1086), (6, 0, w1087), (6, 0, w1088)])
    (tbl_cons s72 (tbl_cons s1062 (tbl_cons s1063 (tbl_cons s190 (tbl_cons s514 (tbl_cons s568 (tbl_cons s630 (tbl_cons s727 (tbl_cons s67 (tbl_cons s1046 (tbl_cons s1047 (tbl_cons s1021 (tbl_cons s65 (tbl_cons s491 (tbl_cons s74 (tbl_cons s1020 (tbl_cons s1017 (tbl_cons s797 (tbl_cons s1064 (tbl_cons s859 (tbl_cons s1065 (tbl_cons s905 (tbl_cons s1066 (tbl_cons s1067 (tbl_cons s1068 (tbl_cons s963 (tbl_cons s1069 (tbl_cons s1070 (tbl_cons s1071 (tbl_cons s1072 (tbl_cons s1073 (tbl_cons s1074 (tbl_cons s1075 (tbl_cons s1076 (tbl_cons s1077 (tbl_cons s1078 (tbl_cons s1079 (tbl_cons s1080 (tbl_cons s1081 (tbl_cons s1082 (tbl_cons s1083 (tbl_cons s1084 (tbl_cons s1085 (tbl_cons s1086 (tbl_cons s1087 (tbl_cons s1088 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1778 : optimized 7 1 w1019 = false :=
  opt_false_of_P (tbl := [(6, 0, w154), (6, 0, w1089), (6, 0, w117), (6, 0, w1090), (6, 0, w1019), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1018), (6, 0, w1017), (6, 0, w1045), (6, 0, w1047), (6, 0, w74), (6, 0, w885), (6, 0, w1091), (6, 0, w837), (6, 0, w1092), (6, 0, w985), (6, 1, w1093), (6, 0, w1094), (6, 0, w1095), (6, 0, w937), (6, 1, w1096), (6, 0, w1097), (6, 0, w1098), (6, 0, w1099), (6, 0, w1100), (6, 0, w1101), (6, 0, w1102), (6, 0, w629), (6, 0, w726), (6, 1, w1080), (6, 0, w1081), (6, 0, w1082), (6, 0, w1103), (6, 0, w1104), (6, 0, w823), (6, 0, w884), (6, 0, w1105), (6, 0, w1106), (6, 0, w1107), (6, 0, w1108)])
    (tbl_cons s154 (tbl_cons s1089 (tbl_cons s117 (tbl_cons s1090 (tbl_cons s1019 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1018 (tbl_cons s1017 (tbl_cons s1045 (tbl_cons s1047 (tbl_cons s74 (tbl_cons s885 (tbl_cons s1091 (tbl_cons s837 (tbl_cons s1092 (tbl_cons s985 (tbl_cons s1093 (tbl_cons s1094 (tbl_cons s1095 (tbl_cons s937 (tbl_cons s1096 (tbl_cons s1097 (tbl_cons s1098 (tbl_cons s1099 (tbl_cons s1100 (tbl_cons s1101 (tbl_cons s1102 (tbl_cons s629 (tbl_cons s726 (tbl_cons s1080 (tbl_cons s1081 (tbl_cons s1082 (tbl_cons s1103 (tbl_cons s1104 (tbl_cons s823 (tbl_cons s884 (tbl_cons s1105 (tbl_cons s1106 (tbl_cons s1107 (tbl_cons s1108 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1779 : optimized 7 1 w1113 = false :=
  opt_false_of_P (tbl := [(6, 0, w89), (6, 0, w1109), (6, 0, w1110), (6, 0, w199), (6, 0, w676), (6, 0, w763), (6, 0, w1026), (6, 0, w1111), (6, 0, w1072), (6, 0, w1112), (6, 0, w1113), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w1114), (6, 0, w1115), (6, 0, w814), (6, 0, w1116), (6, 0, w864), (6, 0, w1117), (6, 0, w914), (6, 0, w1118), (6, 0, w968), (6, 0, w1119), (6, 0, w666), (6, 1, w1120), (6, 0, w1121), (6, 0, w1122), (6, 1, w1123), (6, 0, w1124), (6, 0, w1125), (6, 0, w1126), (6, 0, w1127)])
    (tbl_cons s89 (tbl_cons s1109 (tbl_cons s1110 (tbl_cons s199 (tbl_cons s676 (tbl_cons s763 (tbl_cons s1026 (tbl_cons s1111 (tbl_cons s1072 (tbl_cons s1112 (tbl_cons s1113 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s1114 (tbl_cons s1115 (tbl_cons s814 (tbl_cons s1116 (tbl_cons s864 (tbl_cons s1117 (tbl_cons s914 (tbl_cons s1118 (tbl_cons s968 (tbl_cons s1119 (tbl_cons s666 (tbl_cons s1120 (tbl_cons s1121 (tbl_cons s1122 (tbl_cons s1123 (tbl_cons s1124 (tbl_cons s1125 (tbl_cons s1126 (tbl_cons s1127 tbl_nil)))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1780 : optimized 7 2 w1145 = false :=
  opt_false_of_P (tbl := [(6, 0, w519), (6, 0, w548), (6, 0, w573), (6, 0, w595), (6, 0, w102), (6, 1, w123), (6, 0, w124), (6, 0, w181), (6, 1, w209), (6, 0, w210), (6, 0, w243), (6, 0, w263), (6, 0, w307), (6, 0, w323), (6, 0, w390), (6, 0, w413), (6, 0, w454), (6, 0, w474), (6, 1, w1128), (6, 0, w1129), (6, 0, w1130), (6, 1, w170), (6, 0, w1131), (6, 0, w1132), (6, 0, w1039), (6, 0, w1050), (6, 0, w1105), (6, 0, w1085), (6, 0, w1133), (6, 0, w1134), (6, 0, w1135), (6, 0, w1136), (6, 0, w1137), (6, 0, w1138), (6, 0, w1139), (6, 0, w1140), (6, 0, w1141), (6, 0, w1142), (6, 0, w1143), (6, 0, w1144), (6, 0, w827), (6, 0, w841), (6, 0, w875), (6, 0, w889), (6, 0, w927), (6, 0, w941), (6, 0, w979), (6, 0, w995), (6, 1, w1145), (6, 0, w1146), (6, 0, w1147), (6, 0, w1148), (6, 1, w1120), (6, 1, w1149), (6, 0, w1150), (6, 0, w1151), (6, 0, w1152), (6, 0, w1153), (6, 0, w1154), (6, 0, w1155), (6, 0, w1156), (6, 0, w1157), (6, 0, w1158), (6, 0, w1159), (6, 1, w951), (6, 0, w1160), (6, 0, w1161), (6, 1, w1162), (6, 0, w1163)])
    (tbl_cons s519 (tbl_cons s548 (tbl_cons s573 (tbl_cons s595 (tbl_cons s102 (tbl_cons s123 (tbl_cons s124 (tbl_cons s181 (tbl_cons s209 (tbl_cons s210 (tbl_cons s243 (tbl_cons s263 (tbl_cons s307 (tbl_cons s323 (tbl_cons s390 (tbl_cons s413 (tbl_cons s454 (tbl_cons s474 (tbl_cons s1128 (tbl_cons s1129 (tbl_cons s1130 (tbl_cons s170 (tbl_cons s1131 (tbl_cons s1132 (tbl_cons s1039 (tbl_cons s1050 (tbl_cons s1105 (tbl_cons s1085 (tbl_cons s1133 (tbl_cons s1134 (tbl_cons s1135 (tbl_cons s1136 (tbl_cons s1137 (tbl_cons s1138 (tbl_cons s1139 (tbl_cons s1140 (tbl_cons s1141 (tbl_cons s1142 (tbl_cons s1143 (tbl_cons s1144 (tbl_cons s827 (tbl_cons s841 (tbl_cons s875 (tbl_cons s889 (tbl_cons s927 (tbl_cons s941 (tbl_cons s979 (tbl_cons s995 (tbl_cons s1145 (tbl_cons s1146 (tbl_cons s1147 (tbl_cons s1148 (tbl_cons s1120 (tbl_cons s1149 (tbl_cons s1150 (tbl_cons s1151 (tbl_cons s1152 (tbl_cons s1153 (tbl_cons s1154 (tbl_cons s1155 (tbl_cons s1156 (tbl_cons s1157 (tbl_cons s1158 (tbl_cons s1159 (tbl_cons s951 (tbl_cons s1160 (tbl_cons s1161 (tbl_cons s1162 (tbl_cons s1163 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1781 : optimized 7 1 w1174 = false :=
  opt_false_of_P (tbl := [(6, 0, w125), (6, 0, w211), (6, 0, w677), (6, 0, w693), (6, 0, w764), (6, 0, w779), (6, 0, w1164), (6, 0, w147), (6, 0, w172), (6, 0, w1165), (6, 0, w1166), (6, 0, w1167), (6, 0, w1168), (6, 0, w1169), (6, 0, w1170), (6, 0, w1057), (6, 0, w1101), (6, 0, w1171), (6, 1, w1123), (6, 0, w1124), (6, 0, w1125), (6, 0, w1147), (6, 0, w1172), (6, 1, w1149), (6, 0, w1150), (6, 0, w1173), (6, 1, w65), (6, 0, w74), (6, 0, w1174), (6, 0, w67), (6, 0, w1122), (6, 0, w1175), (6, 0, w1176), (6, 0, w1177), (6, 0, w1178), (6, 0, w1179), (6, 0, w851), (6, 0, w897), (6, 0, w1180), (6, 0, w1181), (6, 0, w1182), (6, 0, w1183), (6, 0, w1184), (6, 0, w1185), (6, 0, w952), (6, 0, w1007), (6, 0, w1186), (6, 0, w666), (6, 1, w1145), (6, 0, w1148), (6, 0, w1115)])
    (tbl_cons s125 (tbl_cons s211 (tbl_cons s677 (tbl_cons s693 (tbl_cons s764 (tbl_cons s779 (tbl_cons s1164 (tbl_cons s147 (tbl_cons s172 (tbl_cons s1165 (tbl_cons s1166 (tbl_cons s1167 (tbl_cons s1168 (tbl_cons s1169 (tbl_cons s1170 (tbl_cons s1057 (tbl_cons s1101 (tbl_cons s1171 (tbl_cons s1123 (tbl_cons s1124 (tbl_cons s1125 (tbl_cons s1147 (tbl_cons s1172 (tbl_cons s1149 (tbl_cons s1150 (tbl_cons s1173 (tbl_cons s65 (tbl_cons s74 (tbl_cons s1174 (tbl_cons s67 (tbl_cons s1122 (tbl_cons s1175 (tbl_cons s1176 (tbl_cons s1177 (tbl_cons s1178 (tbl_cons s1179 (tbl_cons s851 (tbl_cons s897 (tbl_cons s1180 (tbl_cons s1181 (tbl_cons s1182 (tbl_cons s1183 (tbl_cons s1184 (tbl_cons s1185 (tbl_cons s952 (tbl_cons s1007 (tbl_cons s1186 (tbl_cons s666 (tbl_cons s1145 (tbl_cons s1148 (tbl_cons s1115 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1782 : optimized 7 1 w1115 = false :=
  opt_false_of_P (tbl := [(6, 0, w93), (6, 0, w1187), (6, 0, w1188), (6, 0, w203), (6, 0, w126), (6, 0, w212), (6, 0, w678), (6, 0, w765), (6, 0, w1030), (6, 0, w1189), (6, 0, w1076), (6, 0, w1190), (6, 0, w1115), (6, 1, w65), (6, 0, w74), (6, 0, w67), (6, 0, w1114), (6, 0, w1113), (6, 0, w818), (6, 0, w1191), (6, 0, w868), (6, 0, w1192), (6, 0, w918), (6, 0, w1193), (6, 0, w972), (6, 0, w1194), (6, 1, w1145), (6, 0, w1172), (6, 0, w1174), (6, 0, w666), (6, 1, w1195), (6, 0, w1196), (6, 0, w1197), (6, 0, w1198), (6, 0, w1199)])
    (tbl_cons s93 (tbl_cons s1187 (tbl_cons s1188 (tbl_cons s203 (tbl_cons s126 (tbl_cons s212 (tbl_cons s678 (tbl_cons s765 (tbl_cons s1030 (tbl_cons s1189 (tbl_cons s1076 (tbl_cons s1190 (tbl_cons s1115 (tbl_cons s65 (tbl_cons s74 (tbl_cons s67 (tbl_cons s1114 (tbl_cons s1113 (tbl_cons s818 (tbl_cons s1191 (tbl_cons s868 (tbl_cons s1192 (tbl_cons s918 (tbl_cons s1193 (tbl_cons s972 (tbl_cons s1194 (tbl_cons s1145 (tbl_cons s1172 (tbl_cons s1174 (tbl_cons s666 (tbl_cons s1195 (tbl_cons s1196 (tbl_cons s1197 (tbl_cons s1198 (tbl_cons s1199 tbl_nil)))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1783 : optimized 7 2 w1120 = false :=
  opt_false_of_P (tbl := [(6, 0, w520), (6, 0, w549), (6, 0, w574), (6, 0, w596), (6, 0, w103), (6, 0, w127), (6, 0, w182), (6, 0, w213), (6, 1, w166), (6, 0, w1200), (6, 0, w1201), (6, 1, w1202), (6, 0, w1203), (6, 0, w1204), (6, 0, w244), (6, 0, w264), (6, 0, w308), (6, 0, w324), (6, 0, w391), (6, 0, w414), (6, 0, w455), (6, 0, w475), (6, 0, w1040), (6, 0, w1051), (6, 0, w1106), (6, 0, w1086), (6, 0, w1205), (6, 0, w1206), (6, 0, w1207), (6, 0, w1208), (6, 0, w1209), (6, 0, w1210), (6, 0, w1211), (6, 0, w1212), (6, 0, w1213), (6, 0, w1214), (6, 0, w1215), (6, 0, w1216), (6, 0, w1217), (6, 1, w1145), (6, 1, w1149), (6, 0, w1150), (6, 1, w1120), (6, 0, w1218), (6, 0, w1219), (6, 0, w828), (6, 0, w842), (6, 0, w876), (6, 0, w890), (6, 0, w928), (6, 0, w942), (6, 0, w980), (6, 0, w996), (6, 0, w1220), (6, 0, w1221), (6, 0, w1222), (6, 0, w1223), (6, 0, w1224), (6, 1, w1225), (6, 0, w1226), (6, 1, w954), (6, 0, w1227), (6, 0, w1228), (6, 0, w1229), (6, 0, w1230), (6, 0, w1231), (6, 0, w1232)])
    (tbl_cons s520 (tbl_cons s549 (tbl_cons s574 (tbl_cons s596 (tbl_cons s103 (tbl_cons s127 (tbl_cons s182 (tbl_cons s213 (tbl_cons s166 (tbl_cons s1200 (tbl_cons s1201 (tbl_cons s1202 (tbl_cons s1203 (tbl_cons s1204 (tbl_cons s244 (tbl_cons s264 (tbl_cons s308 (tbl_cons s324 (tbl_cons s391 (tbl_cons s414 (tbl_cons s455 (tbl_cons s475 (tbl_cons s1040 (tbl_cons s1051 (tbl_cons s1106 (tbl_cons s1086 (tbl_cons s1205 (tbl_cons s1206 (tbl_cons s1207 (tbl_cons s1208 (tbl_cons s1209 (tbl_cons s1210 (tbl_cons s1211 (tbl_cons s1212 (tbl_cons s1213 (tbl_cons s1214 (tbl_cons s1215 (tbl_cons s1216 (tbl_cons s1217 (tbl_cons s1145 (tbl_cons s1149 (tbl_cons s1150 (tbl_cons s1120 (tbl_cons s1218 (tbl_cons s1219 (tbl_cons s828 (tbl_cons s842 (tbl_cons s876 (tbl_cons s890 (tbl_cons s928 (tbl_cons s942 (tbl_cons s980 (tbl_cons s996 (tbl_cons s1220 (tbl_cons s1221 (tbl_cons s1222 (tbl_cons s1223 (tbl_cons s1224 (tbl_cons s1225 (tbl_cons s1226 (tbl_cons s954 (tbl_cons s1227 (tbl_cons s1228 (tbl_cons s1229 (tbl_cons s1230 (tbl_cons s1231 (tbl_cons s1232 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1784 : optimized 7 1 w1122 = false :=
  opt_false_of_P (tbl := [(6, 0, w168), (6, 0, w1233), (6, 0, w1234), (6, 0, w151), (6, 0, w679), (6, 0, w694), (6, 0, w766), (6, 0, w780), (6, 0, w1099), (6, 0, w1235), (6, 0, w1236), (6, 0, w1059), (6, 0, w1237), (6, 0, w1238), (6, 0, w1239), (6, 0, w1240), (6, 0, w67), (6, 0, w1174), (6, 0, w1173), (6, 1, w65), (6, 0, w74), (6, 0, w1122), (6, 0, w1121), (6, 1, w1149), (6, 0, w1150), (6, 1, w1195), (6, 0, w1196), (6, 0, w1197), (6, 0, w1219), (6, 0, w895), (6, 0, w1241), (6, 0, w852), (6, 0, w1242), (6, 0, w1003), (6, 0, w1243), (6, 0, w955), (6, 0, w1244), (6, 1, w1120), (6, 0, w666), (6, 0, w1217), (6, 0, w1113), (6, 0, w1245), (6, 0, w1246), (6, 0, w1247), (6, 0, w1248), (6, 0, w1249), (6, 0, w1250), (6, 0, w1251), (6, 0, w1252)])
    (tbl_cons s168 (tbl_cons s1233 (tbl_cons s1234 (tbl_cons s151 (tbl_cons s679 (tbl_cons s694 (tbl_cons s766 (tbl_cons s780 (tbl_cons s1099 (tbl_cons s1235 (tbl_cons s1236 (tbl_cons s1059 (tbl_cons s1237 (tbl_cons s1238 (tbl_cons s1239 (tbl_cons s1240 (tbl_cons s67 (tbl_cons s1174 (tbl_cons s1173 (tbl_cons s65 (tbl_cons s74 (tbl_cons s1122 (tbl_cons s1121 (tbl_cons s1149 (tbl_cons s1150 (tbl_cons s1195 (tbl_cons s1196 (tbl_cons s1197 (tbl_cons s1219 (tbl_cons s895 (tbl_cons s1241 (tbl_cons s852 (tbl_cons s1242 (tbl_cons s1003 (tbl_cons s1243 (tbl_cons s955 (tbl_cons s1244 (tbl_cons s1120 (tbl_cons s666 (tbl_cons s1217 (tbl_cons s1113 (tbl_cons s1245 (tbl_cons s1246 (tbl_cons s1247 (tbl_cons s1248 (tbl_cons s1249 (tbl_cons s1250 (tbl_cons s1251 (tbl_cons s1252 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1785 : optimized 7 1 w1265 = false :=
  opt_false_of_P (tbl := [(6, 0, w228), (6, 0, w1253), (6, 0, w1254), (6, 0, w325), (6, 0, w647), (6, 0, w744), (6, 0, w1255), (6, 1, w1256), (6, 0, w1257), (6, 0, w1258), (6, 1, w1259), (6, 0, w1260), (6, 0, w1261), (6, 0, w1262), (6, 0, w806), (6, 0, w1263), (6, 0, w1264), (6, 0, w891), (6, 0, w1151), (6, 0, w1229), (6, 0, w1265), (6, 1, w65), (6, 0, w225), (6, 0, w67), (6, 0, w1266), (6, 0, w1267), (6, 0, w368), (6, 0, w1268), (6, 0, w1269), (6, 0, w1270), (6, 1, w1271), (6, 0, w1272), (6, 0, w1273), (6, 0, w1274), (6, 1, w1275), (6, 0, w1276), (6, 0, w1277), (6, 1, w1278), (6, 0, w1279), (6, 0, w1280), (6, 0, w1281), (6, 0, w1282)])
    (tbl_cons s228 (tbl_cons s1253 (tbl_cons s1254 (tbl_cons s325 (tbl_cons s647 (tbl_cons s744 (tbl_cons s1255 (tbl_cons s1256 (tbl_cons s1257 (tbl_cons s1258 (tbl_cons s1259 (tbl_cons s1260 (tbl_cons s1261 (tbl_cons s1262 (tbl_cons s806 (tbl_cons s1263 (tbl_cons s1264 (tbl_cons s891 (tbl_cons s1151 (tbl_cons s1229 (tbl_cons s1265 (tbl_cons s65 (tbl_cons s225 (tbl_cons s67 (tbl_cons s1266 (tbl_cons s1267 (tbl_cons s368 (tbl_cons s1268 (tbl_cons s1269 (tbl_cons s1270 (tbl_cons s1271 (tbl_cons s1272 (tbl_cons s1273 (tbl_cons s1274 (tbl_cons s1275 (tbl_cons s1276 (tbl_cons s1277 (tbl_cons s1278 (tbl_cons s1279 (tbl_cons s1280 (tbl_cons s1281 (tbl_cons s1282 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1786 : optimized 7 1 w1297 = false :=
  opt_false_of_P (tbl := [(6, 0, w265), (6, 0, w341), (6, 0, w392), (6, 0, w456), (6, 0, w1283), (6, 0, w268), (6, 0, w289), (6, 0, w1284), (6, 0, w648), (6, 0, w745), (6, 0, w1285), (6, 0, w1286), (6, 0, w1287), (6, 0, w1288), (6, 0, w1289), (6, 0, w1290), (6, 0, w1291), (6, 0, w1292), (6, 0, w829), (6, 0, w877), (6, 0, w944), (6, 0, w1011), (6, 0, w1293), (6, 0, w847), (6, 0, w862), (6, 0, w1294), (6, 0, w1152), (6, 0, w1230), (6, 1, w1278), (6, 0, w1279), (6, 0, w1280), (6, 0, w1295), (6, 0, w1296), (6, 1, w65), (6, 0, w225), (6, 0, w1297), (6, 0, w67), (6, 0, w1269), (6, 0, w1298), (6, 0, w1299), (6, 0, w368), (6, 0, w1267), (6, 1, w1300), (6, 0, w1301), (6, 0, w1302), (6, 0, w1303), (6, 0, w1304), (6, 0, w1305), (6, 0, w1306), (6, 0, w1307), (6, 0, w1308)])
    (tbl_cons s265 (tbl_cons s341 (tbl_cons s392 (tbl_cons s456 (tbl_cons s1283 (tbl_cons s268 (tbl_cons s289 (tbl_cons s1284 (tbl_cons s648 (tbl_cons s745 (tbl_cons s1285 (tbl_cons s1286 (tbl_cons s1287 (tbl_cons s1288 (tbl_cons s1289 (tbl_cons s1290 (tbl_cons s1291 (tbl_cons s1292 (tbl_cons s829 (tbl_cons s877 (tbl_cons s944 (tbl_cons s1011 (tbl_cons s1293 (tbl_cons s847 (tbl_cons s862 (tbl_cons s1294 (tbl_cons s1152 (tbl_cons s1230 (tbl_cons s1278 (tbl_cons s1279 (tbl_cons s1280 (tbl_cons s1295 (tbl_cons s1296 (tbl_cons s65 (tbl_cons s225 (tbl_cons s1297 (tbl_cons s67 (tbl_cons s1269 (tbl_cons s1298 (tbl_cons s1299 (tbl_cons s368 (tbl_cons s1267 (tbl_cons s1300 (tbl_cons s1301 (tbl_cons s1302 (tbl_cons s1303 (tbl_cons s1304 (tbl_cons s1305 (tbl_cons s1306 (tbl_cons s1307 (tbl_cons s1308 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1787 : optimized 7 1 w1267 = false :=
  opt_false_of_P (tbl := [(6, 0, w230), (6, 0, w1309), (6, 0, w329), (6, 0, w1310), (6, 0, w1311), (6, 0, w1312), (6, 0, w1313), (6, 0, w1314), (6, 0, w810), (6, 0, w1315), (6, 0, w893), (6, 0, w1316), (6, 0, w1267), (6, 1, w65), (6, 0, w225), (6, 0, w67), (6, 0, w1266), (6, 0, w1265), (6, 0, w1295), (6, 0, w1297), (6, 0, w368), (6, 0, w1317), (6, 0, w1318), (6, 0, w1319), (6, 0, w1320), (6, 0, w266), (6, 0, w342), (6, 0, w649), (6, 0, w746), (6, 0, w1321), (6, 0, w1322), (6, 0, w830), (6, 0, w878), (6, 0, w1153), (6, 0, w1231), (6, 1, w1323), (6, 0, w1324), (6, 0, w1325), (6, 0, w1326), (6, 0, w1327), (6, 0, w1328), (6, 0, w1329)])
    (tbl_cons s230 (tbl_cons s1309 (tbl_cons s329 (tbl_cons s1310 (tbl_cons s1311 (tbl_cons s1312 (tbl_cons s1313 (tbl_cons s1314 (tbl_cons s810 (tbl_cons s1315 (tbl_cons s893 (tbl_cons s1316 (tbl_cons s1267 (tbl_cons s65 (tbl_cons s225 (tbl_cons s67 (tbl_cons s1266 (tbl_cons s1265 (tbl_cons s1295 (tbl_cons s1297 (tbl_cons s368 (tbl_cons s1317 (tbl_cons s1318 (tbl_cons s1319 (tbl_cons s1320 (tbl_cons s266 (tbl_cons s342 (tbl_cons s649 (tbl_cons s746 (tbl_cons s1321 (tbl_cons s1322 (tbl_cons s830 (tbl_cons s878 (tbl_cons s1153 (tbl_cons s1231 (tbl_cons s1323 (tbl_cons s1324 (tbl_cons s1325 (tbl_cons s1326 (tbl_cons s1327 (tbl_cons s1328 (tbl_cons s1329 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1788 : optimized 7 1 w1269 = false :=
  opt_false_of_P (tbl := [(6, 0, w287), (6, 0, w1330), (6, 0, w269), (6, 0, w1331), (6, 0, w1332), (6, 0, w1333), (6, 0, w1334), (6, 0, w1335), (6, 0, w860), (6, 0, w1336), (6, 0, w848), (6, 0, w1337), (6, 0, w67), (6, 0, w1296), (6, 0, w1297), (6, 0, w1269), (6, 1, w65), (6, 0, w225), (6, 0, w368), (6, 0, w1268), (6, 0, w1265), (6, 0, w1338), (6, 1, w1339), (6, 0, w1340), (6, 0, w1341), (6, 0, w1342), (6, 1, w1343), (6, 0, w1344), (6, 0, w1345), (6, 0, w393), (6, 0, w457), (6, 0, w650), (6, 0, w747), (6, 0, w1346), (6, 0, w1347), (6, 0, w945), (6, 0, w1012), (6, 0, w1154), (6, 0, w1232), (6, 1, w1323), (6, 0, w1324), (6, 0, w1325), (6, 1, w1348), (6, 0, w1349), (6, 0, w1350), (6, 0, w1351), (6, 0, w1352)])
    (tbl_cons s287 (tbl_cons s1330 (tbl_cons s269 (tbl_cons s1331 (tbl_cons s1332 (tbl_cons s1333 (tbl_cons s1334 (tbl_cons s1335 (tbl_cons s860 (tbl_cons s1336 (tbl_cons s848 (tbl_cons s1337 (tbl_cons s67 (tbl_cons s1296 (tbl_cons s1297 (tbl_cons s1269 (tbl_cons s65 (tbl_cons s225 (tbl_cons s368 (tbl_cons s1268 (tbl_cons s1265 (tbl_cons s1338 (tbl_cons s1339 (tbl_cons s1340 (tbl_cons s1341 (tbl_cons s1342 (tbl_cons s1343 (tbl_cons s1344 (tbl_cons s1345 (tbl_cons s393 (tbl_cons s457 (tbl_cons s650 (tbl_cons s747 (tbl_cons s1346 (tbl_cons s1347 (tbl_cons s945 (tbl_cons s1012 (tbl_cons s1154 (tbl_cons s1232 (tbl_cons s1323 (tbl_cons s1324 (tbl_cons s1325 (tbl_cons s1348 (tbl_cons s1349 (tbl_cons s1350 (tbl_cons s1351 (tbl_cons s1352 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1789 : optimized 7 1 w1355 = false :=
  opt_false_of_P (tbl := [(6, 0, w219), (6, 0, w1353), (6, 0, w313), (6, 0, w1354), (6, 0, w1355), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1356), (6, 0, w1357), (6, 0, w793), (6, 0, w1358), (6, 0, w885), (6, 0, w1359), (6, 0, w225), (6, 0, w1360), (6, 0, w1361), (6, 0, w1255), (6, 1, w1362), (6, 0, w1363), (6, 0, w1364), (6, 0, w1311), (6, 1, w1365), (6, 0, w1366), (6, 0, w1367), (6, 0, w1368), (6, 1, w1369), (6, 0, w1370), (6, 0, w1371), (6, 0, w1372), (6, 1, w1373), (6, 0, w1374), (6, 0, w1375), (6, 0, w631), (6, 0, w728), (6, 1, w1376), (6, 0, w1377), (6, 0, w1378), (6, 0, w1133), (6, 0, w1209), (6, 0, w1379), (6, 0, w1380)])
    (tbl_cons s219 (tbl_cons s1353 (tbl_cons s313 (tbl_cons s1354 (tbl_cons s1355 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1356 (tbl_cons s1357 (tbl_cons s793 (tbl_cons s1358 (tbl_cons s885 (tbl_cons s1359 (tbl_cons s225 (tbl_cons s1360 (tbl_cons s1361 (tbl_cons s1255 (tbl_cons s1362 (tbl_cons s1363 (tbl_cons s1364 (tbl_cons s1311 (tbl_cons s1365 (tbl_cons s1366 (tbl_cons s1367 (tbl_cons s1368 (tbl_cons s1369 (tbl_cons s1370 (tbl_cons s1371 (tbl_cons s1372 (tbl_cons s1373 (tbl_cons s1374 (tbl_cons s1375 (tbl_cons s631 (tbl_cons s728 (tbl_cons s1376 (tbl_cons s1377 (tbl_cons s1378 (tbl_cons s1133 (tbl_cons s1209 (tbl_cons s1379 (tbl_cons s1380 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1790 : optimized 7 1 w1389 = false :=
  opt_false_of_P (tbl := [(6, 0, w515), (6, 0, w569), (6, 0, w632), (6, 0, w729), (6, 0, w1381), (6, 0, w258), (6, 0, w283), (6, 0, w1382), (6, 0, w1048), (6, 0, w1103), (6, 1, w1376), (6, 0, w1377), (6, 0, w1378), (6, 0, w1383), (6, 0, w1384), (6, 0, w1385), (6, 0, w1386), (6, 0, w1387), (6, 0, w1388), (6, 1, w65), (6, 0, w491), (6, 0, w1389), (6, 0, w67), (6, 0, w1361), (6, 0, w1134), (6, 0, w1210), (6, 1, w1390), (6, 0, w1391), (6, 0, w1392), (6, 0, w836), (6, 0, w859), (6, 1, w1393), (6, 0, w1394), (6, 0, w1395), (6, 0, w1285), (6, 0, w1321), (6, 0, w225), (6, 0, w1357), (6, 0, w1396), (6, 0, w1397), (6, 0, w1398), (6, 0, w1290), (6, 0, w1334), (6, 0, w1399), (6, 1, w1400), (6, 0, w1401), (6, 0, w1402), (6, 0, w1403), (6, 0, w1404), (6, 1, w1405), (6, 0, w1406), (6, 0, w1407)])
    (tbl_cons s515 (tbl_cons s569 (tbl_cons s632 (tbl_cons s729 (tbl_cons s1381 (tbl_cons s258 (tbl_cons s283 (tbl_cons s1382 (tbl_cons s1048 (tbl_cons s1103 (tbl_cons s1376 (tbl_cons s1377 (tbl_cons s1378 (tbl_cons s1383 (tbl_cons s1384 (tbl_cons s1385 (tbl_cons s1386 (tbl_cons s1387 (tbl_cons s1388 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1389 (tbl_cons s67 (tbl_cons s1361 (tbl_cons s1134 (tbl_cons s1210 (tbl_cons s1390 (tbl_cons s1391 (tbl_cons s1392 (tbl_cons s836 (tbl_cons s859 (tbl_cons s1393 (tbl_cons s1394 (tbl_cons s1395 (tbl_cons s1285 (tbl_cons s1321 (tbl_cons s225 (tbl_cons s1357 (tbl_cons s1396 (tbl_cons s1397 (tbl_cons s1398 (tbl_cons s1290 (tbl_cons s1334 (tbl_cons s1399 (tbl_cons s1400 (tbl_cons s1401 (tbl_cons s1402 (tbl_cons s1403 (tbl_cons s1404 (tbl_cons s1405 (tbl_cons s1406 (tbl_cons s1407 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1791 : optimized 7 1 w1361 = false :=
  opt_false_of_P (tbl := [(6, 0, w221), (6, 1, w1408), (6, 0, w1409), (6, 0, w1410), (6, 1, w1411), (6, 0, w1412), (6, 0, w1413), (6, 0, w320), (6, 0, w634), (6, 0, w731), (6, 0, w67), (6, 0, w1389), (6, 0, w1384), (6, 1, w65), (6, 0, w491), (6, 0, w1361), (6, 0, w1360), (6, 1, w1414), (6, 0, w1415), (6, 0, w1416), (6, 0, w797), (6, 0, w1417), (6, 0, w1418), (6, 0, w888), (6, 0, w1136), (6, 0, w1212), (6, 0, w225), (6, 0, w1355), (6, 0, w1262), (6, 0, w1419), (6, 0, w1313), (6, 0, w1420), (6, 0, w1421), (6, 0, w1422), (6, 0, w1423), (6, 0, w1424), (6, 0, w1286), (6, 0, w1322), (6, 0, w1425), (6, 0, w1426)])
    (tbl_cons s221 (tbl_cons s1408 (tbl_cons s1409 (tbl_cons s1410 (tbl_cons s1411 (tbl_cons s1412 (tbl_cons s1413 (tbl_cons s320 (tbl_cons s634 (tbl_cons s731 (tbl_cons s67 (tbl_cons s1389 (tbl_cons s1384 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1361 (tbl_cons s1360 (tbl_cons s1414 (tbl_cons s1415 (tbl_cons s1416 (tbl_cons s797 (tbl_cons s1417 (tbl_cons s1418 (tbl_cons s888 (tbl_cons s1136 (tbl_cons s1212 (tbl_cons s225 (tbl_cons s1355 (tbl_cons s1262 (tbl_cons s1419 (tbl_cons s1313 (tbl_cons s1420 (tbl_cons s1421 (tbl_cons s1422 (tbl_cons s1423 (tbl_cons s1424 (tbl_cons s1286 (tbl_cons s1322 (tbl_cons s1425 (tbl_cons s1426 tbl_nil))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1792 : optimized 7 1 w1357 = false :=
  opt_false_of_P (tbl := [(6, 0, w281), (6, 0, w1427), (6, 0, w1428), (6, 0, w259), (6, 0, w516), (6, 0, w570), (6, 0, w633), (6, 0, w730), (6, 0, w1357), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1356), (6, 0, w1355), (6, 0, w856), (6, 0, w1429), (6, 0, w837), (6, 0, w1430), (6, 0, w1383), (6, 0, w1389), (6, 0, w225), (6, 0, w1332), (6, 0, w1431), (6, 0, w1291), (6, 0, w1432), (6, 0, w1433), (6, 0, w1434), (6, 0, w1435), (6, 0, w1436), (6, 0, w1049), (6, 0, w1104), (6, 1, w1414), (6, 0, w1415), (6, 0, w1416), (6, 0, w1437), (6, 0, w1438), (6, 0, w1439), (6, 0, w1440), (6, 0, w1135), (6, 0, w1211), (6, 0, w1441), (6, 0, w1442)])
    (tbl_cons s281 (tbl_cons s1427 (tbl_cons s1428 (tbl_cons s259 (tbl_cons s516 (tbl_cons s570 (tbl_cons s633 (tbl_cons s730 (tbl_cons s1357 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1356 (tbl_cons s1355 (tbl_cons s856 (tbl_cons s1429 (tbl_cons s837 (tbl_cons s1430 (tbl_cons s1383 (tbl_cons s1389 (tbl_cons s225 (tbl_cons s1332 (tbl_cons s1431 (tbl_cons s1291 (tbl_cons s1432 (tbl_cons s1433 (tbl_cons s1434 (tbl_cons s1435 (tbl_cons s1436 (tbl_cons s1049 (tbl_cons s1104 (tbl_cons s1414 (tbl_cons s1415 (tbl_cons s1416 (tbl_cons s1437 (tbl_cons s1438 (tbl_cons s1439 (tbl_cons s1440 (tbl_cons s1135 (tbl_cons s1211 (tbl_cons s1441 (tbl_cons s1442 tbl_nil))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1793 : optimized 7 1 w1459 = false :=
  opt_false_of_P (tbl := [(6, 0, w232), (6, 1, w1443), (6, 0, w1444), (6, 0, w1445), (6, 1, w1446), (6, 0, w1447), (6, 0, w1448), (6, 0, w333), (6, 0, w680), (6, 0, w767), (6, 0, w1368), (6, 1, w1449), (6, 0, w1450), (6, 0, w1451), (6, 1, w1452), (6, 0, w1453), (6, 0, w1454), (6, 0, w1421), (6, 0, w1455), (6, 0, w1456), (6, 0, w814), (6, 0, w1457), (6, 0, w1458), (6, 0, w895), (6, 0, w1175), (6, 0, w1245), (6, 0, w1459), (6, 1, w65), (6, 0, w225), (6, 0, w67), (6, 0, w1460), (6, 0, w1461), (6, 0, w1270), (6, 1, w1462), (6, 0, w1463), (6, 0, w1464), (6, 0, w1317), (6, 1, w1465), (6, 0, w1466), (6, 0, w1467), (6, 0, w666), (6, 0, w1468), (6, 0, w1469), (6, 0, w1298), (6, 0, w1326), (6, 1, w1470), (6, 0, w1471), (6, 0, w1472), (6, 0, w1473), (6, 0, w1474)])
    (tbl_cons s232 (tbl_cons s1443 (tbl_cons s1444 (tbl_cons s1445 (tbl_cons s1446 (tbl_cons s1447 (tbl_cons s1448 (tbl_cons s333 (tbl_cons s680 (tbl_cons s767 (tbl_cons s1368 (tbl_cons s1449 (tbl_cons s1450 (tbl_cons s1451 (tbl_cons s1452 (tbl_cons s1453 (tbl_cons s1454 (tbl_cons s1421 (tbl_cons s1455 (tbl_cons s1456 (tbl_cons s814 (tbl_cons s1457 (tbl_cons s1458 (tbl_cons s895 (tbl_cons s1175 (tbl_cons s1245 (tbl_cons s1459 (tbl_cons s65 (tbl_cons s225 (tbl_cons s67 (tbl_cons s1460 (tbl_cons s1461 (tbl_cons s1270 (tbl_cons s1462 (tbl_cons s1463 (tbl_cons s1464 (tbl_cons s1317 (tbl_cons s1465 (tbl_cons s1466 (tbl_cons s1467 (tbl_cons s666 (tbl_cons s1468 (tbl_cons s1469 (tbl_cons s1298 (tbl_cons s1326 (tbl_cons s1470 (tbl_cons s1471 (tbl_cons s1472 (tbl_cons s1473 (tbl_cons s1474 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1794 : optimized 7 1 w1485 = false :=
  opt_false_of_P (tbl := [(6, 0, w681), (6, 0, w768), (6, 0, w1475), (6, 0, w276), (6, 0, w293), (6, 0, w1476), (6, 0, w1477), (6, 0, w1478), (6, 0, w1479), (6, 0, w1403), (6, 0, w1435), (6, 0, w1480), (6, 0, w1176), (6, 0, w1246), (6, 0, w1481), (6, 0, w851), (6, 0, w868), (6, 0, w1482), (6, 1, w1470), (6, 0, w1471), (6, 0, w1472), (6, 0, w1483), (6, 0, w1484), (6, 1, w65), (6, 0, w225), (6, 0, w1485), (6, 0, w67), (6, 0, w1469), (6, 0, w1486), (6, 0, w1487), (6, 0, w1488), (6, 0, w1306), (6, 0, w1342), (6, 0, w1489), (6, 0, w666), (6, 0, w1461)])
    (tbl_cons s681 (tbl_cons s768 (tbl_cons s1475 (tbl_cons s276 (tbl_cons s293 (tbl_cons s1476 (tbl_cons s1477 (tbl_cons s1478 (tbl_cons s1479 (tbl_cons s1403 (tbl_cons s1435 (tbl_cons s1480 (tbl_cons s1176 (tbl_cons s1246 (tbl_cons s1481 (tbl_cons s851 (tbl_cons s868 (tbl_cons s1482 (tbl_cons s1470 (tbl_cons s1471 (tbl_cons s1472 (tbl_cons s1483 (tbl_cons s1484 (tbl_cons s65 (tbl_cons s225 (tbl_cons s1485 (tbl_cons s67 (tbl_cons s1469 (tbl_cons s1486 (tbl_cons s1487 (tbl_cons s1488 (tbl_cons s1306 (tbl_cons s1342 (tbl_cons s1489 (tbl_cons s666 (tbl_cons s1461 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1795 : optimized 7 1 w1461 = false :=
  opt_false_of_P (tbl := [(6, 0, w234), (6, 0, w1490), (6, 0, w337), (6, 0, w1491), (6, 0, w1372), (6, 0, w1492), (6, 0, w1423), (6, 0, w1493), (6, 0, w818), (6, 0, w1494), (6, 0, w897), (6, 0, w1495), (6, 0, w1461), (6, 1, w65), (6, 0, w225), (6, 0, w67), (6, 0, w1460), (6, 0, w1459), (6, 0, w1274), (6, 0, w1496), (6, 0, w1319), (6, 0, w1497), (6, 0, w1483), (6, 0, w1485), (6, 0, w666), (6, 0, w682), (6, 0, w769), (6, 0, w1498), (6, 0, w1499), (6, 0, w1177), (6, 0, w1247), (6, 1, w1500), (6, 0, w1501), (6, 0, w1502), (6, 0, w1503), (6, 0, w1504)])
    (tbl_cons s234 (tbl_cons s1490 (tbl_cons s337 (tbl_cons s1491 (tbl_cons s1372 (tbl_cons s1492 (tbl_cons s1423 (tbl_cons s1493 (tbl_cons s818 (tbl_cons s1494 (tbl_cons s897 (tbl_cons s1495 (tbl_cons s1461 (tbl_cons s65 (tbl_cons s225 (tbl_cons s67 (tbl_cons s1460 (tbl_cons s1459 (tbl_cons s1274 (tbl_cons s1496 (tbl_cons s1319 (tbl_cons s1497 (tbl_cons s1483 (tbl_cons s1485 (tbl_cons s666 (tbl_cons s682 (tbl_cons s769 (tbl_cons s1498 (tbl_cons s1499 (tbl_cons s1177 (tbl_cons s1247 (tbl_cons s1500 (tbl_cons s1501 (tbl_cons s1502 (tbl_cons s1503 (tbl_cons s1504 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1796 : optimized 7 1 w1469 = false :=
  opt_false_of_P (tbl := [(6, 0, w291), (6, 0, w1505), (6, 0, w1506), (6, 0, w280), (6, 0, w683), (6, 0, w770), (6, 0, w1433), (6, 0, w1507), (6, 0, w1404), (6, 0, w1508), (6, 0, w864), (6, 0, w1509), (6, 0, w852), (6, 0, w1510), (6, 0, w67), (6, 0, w1484), (6, 0, w1485), (6, 0, w1469), (6, 1, w65), (6, 0, w225), (6, 0, w1338), (6, 0, w1511), (6, 0, w1308), (6, 0, w1512), (6, 0, w666), (6, 0, w1468), (6, 0, w1459), (6, 0, w1513), (6, 0, w1514), (6, 0, w1178), (6, 0, w1248), (6, 0, w1299), (6, 0, w1327), (6, 1, w1500), (6, 0, w1501), (6, 0, w1502), (6, 0, w1515), (6, 0, w1516)])
    (tbl_cons s291 (tbl_cons s1505 (tbl_cons s1506 (tbl_cons s280 (tbl_cons s683 (tbl_cons s770 (tbl_cons s1433 (tbl_cons s1507 (tbl_cons s1404 (tbl_cons s1508 (tbl_cons s864 (tbl_cons s1509 (tbl_cons s852 (tbl_cons s1510 (tbl_cons s67 (tbl_cons s1484 (tbl_cons s1485 (tbl_cons s1469 (tbl_cons s65 (tbl_cons s225 (tbl_cons s1338 (tbl_cons s1511 (tbl_cons s1308 (tbl_cons s1512 (tbl_cons s666 (tbl_cons s1468 (tbl_cons s1459 (tbl_cons s1513 (tbl_cons s1514 (tbl_cons s1178 (tbl_cons s1248 (tbl_cons s1299 (tbl_cons s1327 (tbl_cons s1500 (tbl_cons s1501 (tbl_cons s1502 (tbl_cons s1515 (tbl_cons s1516 tbl_nil))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1797 : optimized 7 1 w1519 = false :=
  opt_false_of_P (tbl := [(6, 0, w348), (6, 0, w1517), (6, 0, w464), (6, 0, w1518), (6, 0, w1519), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1520), (6, 0, w1521), (6, 0, w903), (6, 0, w1522), (6, 0, w985), (6, 0, w1523), (6, 0, w1255), (6, 1, w1524), (6, 0, w1525), (6, 0, w1526), (6, 0, w1332), (6, 1, w1527), (6, 0, w1528), (6, 0, w1529), (6, 0, w368), (6, 0, w1530), (6, 0, w1531), (6, 0, w1532), (6, 1, w1533), (6, 0, w1534), (6, 0, w1535), (6, 0, w1536), (6, 1, w1537), (6, 0, w1538), (6, 0, w1539), (6, 0, w517), (6, 0, w571), (6, 0, w386), (6, 0, w450), (6, 0, w635), (6, 0, w732), (6, 1, w51), (6, 0, w1540), (6, 0, w1541), (6, 0, w933), (6, 0, w993), (6, 0, w1137), (6, 0, w1213), (6, 0, w1542), (6, 0, w1543)])
    (tbl_cons s348 (tbl_cons s1517 (tbl_cons s464 (tbl_cons s1518 (tbl_cons s1519 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1520 (tbl_cons s1521 (tbl_cons s903 (tbl_cons s1522 (tbl_cons s985 (tbl_cons s1523 (tbl_cons s1255 (tbl_cons s1524 (tbl_cons s1525 (tbl_cons s1526 (tbl_cons s1332 (tbl_cons s1527 (tbl_cons s1528 (tbl_cons s1529 (tbl_cons s368 (tbl_cons s1530 (tbl_cons s1531 (tbl_cons s1532 (tbl_cons s1533 (tbl_cons s1534 (tbl_cons s1535 (tbl_cons s1536 (tbl_cons s1537 (tbl_cons s1538 (tbl_cons s1539 (tbl_cons s517 (tbl_cons s571 (tbl_cons s386 (tbl_cons s450 (tbl_cons s635 (tbl_cons s732 (tbl_cons s1540 (tbl_cons s1541 (tbl_cons s1542 (tbl_cons s933 (tbl_cons s993 (tbl_cons s1137 (tbl_cons s1213 (tbl_cons s1543 (tbl_cons s1544 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1798 : optimized 7 1 w1552 = false :=
  opt_false_of_P (tbl := [(6, 0, w528), (6, 0, w593), (6, 0, w401), (6, 0, w468), (6, 0, w636), (6, 0, w733), (6, 1, w1544), (6, 0, w1545), (6, 0, w1546), (6, 0, w406), (6, 0, w431), (6, 1, w1547), (6, 0, w1548), (6, 0, w1549), (6, 0, w1037), (6, 0, w1083), (6, 0, w1385), (6, 0, w1437), (6, 1, w51), (6, 0, w1540), (6, 0, w1541), (6, 0, w1550), (6, 0, w1551), (6, 1, w65), (6, 0, w491), (6, 0, w1552), (6, 0, w67), (6, 0, w1531), (6, 0, w922), (6, 0, w964), (6, 0, w1138), (6, 0, w1214), (6, 0, w1553), (6, 0, w936), (6, 0, w963), (6, 0, w1554), (6, 0, w1287), (6, 0, w1346), (6, 0, w1555), (6, 0, w1290), (6, 0, w1313), (6, 0, w1556), (6, 0, w1557), (6, 0, w1558), (6, 0, w368), (6, 0, w1521), (6, 0, w1559), (6, 0, w1560), (6, 0, w1561), (6, 0, w1562)])
    (tbl_cons s528 (tbl_cons s593 (tbl_cons s401 (tbl_cons s468 (tbl_cons s636 (tbl_cons s733 (tbl_cons s1545 (tbl_cons s1546 (tbl_cons s1547 (tbl_cons s406 (tbl_cons s431 (tbl_cons s1548 (tbl_cons s1549 (tbl_cons s1550 (tbl_cons s1037 (tbl_cons s1083 (tbl_cons s1385 (tbl_cons s1437 (tbl_cons s1540 (tbl_cons s1541 (tbl_cons s1542 (tbl_cons s1551 (tbl_cons s1552 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1553 (tbl_cons s67 (tbl_cons s1531 (tbl_cons s922 (tbl_cons s964 (tbl_cons s1138 (tbl_cons s1214 (tbl_cons s1554 (tbl_cons s936 (tbl_cons s963 (tbl_cons s1555 (tbl_cons s1287 (tbl_cons s1346 (tbl_cons s1556 (tbl_cons s1290 (tbl_cons s1313 (tbl_cons s1557 (tbl_cons s1558 (tbl_cons s1559 (tbl_cons s368 (tbl_cons s1521 (tbl_cons s1560 (tbl_cons s1561 (tbl_cons s1562 (tbl_cons s1563 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1799 : optimized 7 1 w1531 = false :=
  opt_false_of_P (tbl := [(6, 0, w518), (6, 0, w572), (6, 0, w352), (6, 0, w1563), (6, 0, w1564), (6, 0, w467), (6, 0, w402), (6, 0, w469), (6, 0, w638), (6, 0, w735), (6, 0, w67), (6, 0, w1552), (6, 0, w1551), (6, 1, w65), (6, 0, w491), (6, 0, w1531), (6, 0, w1530), (6, 1, w1565), (6, 0, w1566), (6, 0, w1567), (6, 0, w905), (6, 0, w1568), (6, 0, w1569), (6, 0, w992), (6, 0, w923), (6, 0, w965), (6, 0, w1140), (6, 0, w1216), (6, 0, w1262), (6, 0, w1570), (6, 0, w1571), (6, 0, w1334), (6, 0, w1288), (6, 0, w1347), (6, 0, w368), (6, 0, w1519), (6, 0, w1572), (6, 1, w1573), (6, 0, w1574), (6, 0, w1575), (6, 0, w1576), (6, 1, w1577), (6, 0, w1578), (6, 0, w1579), (6, 0, w1580), (6, 0, w1581)])
    (tbl_cons s518 (tbl_cons s572 (tbl_cons s352 (tbl_cons s1564 (tbl_cons s1565 (tbl_cons s467 (tbl_cons s402 (tbl_cons s469 (tbl_cons s638 (tbl_cons s735 (tbl_cons s67 (tbl_cons s1553 (tbl_cons s1552 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1531 (tbl_cons s1530 (tbl_cons s1566 (tbl_cons s1567 (tbl_cons s1568 (tbl_cons s905 (tbl_cons s1569 (tbl_cons s1570 (tbl_cons s992 (tbl_cons s923 (tbl_cons s965 (tbl_cons s1140 (tbl_cons s1216 (tbl_cons s1262 (tbl_cons s1571 (tbl_cons s1572 (tbl_cons s1334 (tbl_cons s1288 (tbl_cons s1347 (tbl_cons s368 (tbl_cons s1519 (tbl_cons s1573 (tbl_cons s1574 (tbl_cons s1575 (tbl_cons s1576 (tbl_cons s1577 (tbl_cons s1578 (tbl_cons s1579 (tbl_cons s1580 (tbl_cons s1581 (tbl_cons s1582 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1800 : optimized 7 1 w1521 = false :=
  opt_false_of_P (tbl := [(6, 0, w429), (6, 0, w1582), (6, 0, w1583), (6, 0, w407), (6, 0, w529), (6, 0, w594), (6, 0, w387), (6, 0, w451), (6, 0, w637), (6, 0, w734), (6, 0, w1521), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1520), (6, 0, w1519), (6, 0, w960), (6, 0, w1584), (6, 0, w937), (6, 0, w1585), (6, 0, w1311), (6, 0, w1586), (6, 0, w1291), (6, 0, w1587), (6, 0, w1550), (6, 0, w1552), (6, 0, w368), (6, 0, w1588), (6, 0, w1589), (6, 0, w1590), (6, 0, w1591), (6, 0, w1038), (6, 0, w1084), (6, 0, w1386), (6, 0, w1438), (6, 1, w1565), (6, 0, w1566), (6, 0, w1567), (6, 0, w934), (6, 0, w994), (6, 0, w1139), (6, 0, w1215), (6, 0, w1592), (6, 0, w1593)])
    (tbl_cons s429 (tbl_cons s1583 (tbl_cons s1584 (tbl_cons s407 (tbl_cons s529 (tbl_cons s594 (tbl_cons s387 (tbl_cons s451 (tbl_cons s637 (tbl_cons s734 (tbl_cons s1521 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1520 (tbl_cons s1519 (tbl_cons s960 (tbl_cons s1585 (tbl_cons s937 (tbl_cons s1586 (tbl_cons s1311 (tbl_cons s1587 (tbl_cons s1291 (tbl_cons s1588 (tbl_cons s1551 (tbl_cons s1553 (tbl_cons s368 (tbl_cons s1589 (tbl_cons s1590 (tbl_cons s1591 (tbl_cons s1592 (tbl_cons s1038 (tbl_cons s1084 (tbl_cons s1386 (tbl_cons s1438 (tbl_cons s1566 (tbl_cons s1567 (tbl_cons s1568 (tbl_cons s934 (tbl_cons s994 (tbl_cons s1139 (tbl_cons s1215 (tbl_cons s1593 (tbl_cons s1594 tbl_nil))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1801 : optimized 7 1 w1602 = false :=
  opt_false_of_P (tbl := [(6, 0, w371), (6, 0, w1594), (6, 0, w1595), (6, 0, w478), (6, 0, w684), (6, 0, w771), (6, 0, w1532), (6, 0, w1596), (6, 0, w1597), (6, 0, w1572), (6, 0, w914), (6, 0, w1598), (6, 0, w1599), (6, 0, w1003), (6, 0, w1181), (6, 0, w1249), (6, 0, w1270), (6, 0, w1600), (6, 0, w1601), (6, 0, w1338), (6, 0, w1602), (6, 1, w65), (6, 0, w368), (6, 0, w67), (6, 0, w1603), (6, 0, w1604), (6, 0, w666), (6, 1, w1605), (6, 0, w1606), (6, 0, w1607), (6, 1, w1608), (6, 0, w1609), (6, 0, w1610)])
    (tbl_cons s371 (tbl_cons s1595 (tbl_cons s1596 (tbl_cons s478 (tbl_cons s684 (tbl_cons s771 (tbl_cons s1532 (tbl_cons s1597 (tbl_cons s1598 (tbl_cons s1573 (tbl_cons s914 (tbl_cons s1599 (tbl_cons s1600 (tbl_cons s1003 (tbl_cons s1181 (tbl_cons s1249 (tbl_cons s1270 (tbl_cons s1601 (tbl_cons s1602 (tbl_cons s1338 (tbl_cons s1603 (tbl_cons s65 (tbl_cons s368 (tbl_cons s67 (tbl_cons s1604 (tbl_cons s1605 (tbl_cons s666 (tbl_cons s1606 (tbl_cons s1607 (tbl_cons s1608 (tbl_cons s1609 (tbl_cons s1610 (tbl_cons s1611 tbl_nil)))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1802 : optimized 7 2 w1629 = false :=
  opt_false_of_P (tbl := [(6, 0, w521), (6, 0, w550), (6, 0, w575), (6, 0, w597), (6, 0, w104), (6, 0, w152), (6, 0, w183), (6, 0, w214), (6, 0, w245), (6, 0, w271), (6, 0, w309), (6, 0, w343), (6, 0, w394), (6, 0, w419), (6, 0, w458), (6, 0, w486), (6, 1, w1611), (6, 0, w1612), (6, 0, w1613), (6, 1, w441), (6, 0, w1614), (6, 0, w1615), (6, 0, w1041), (6, 0, w1060), (6, 0, w1107), (6, 0, w1087), (6, 0, w1379), (6, 0, w1396), (6, 0, w1441), (6, 0, w1425), (6, 0, w1542), (6, 0, w1557), (6, 0, w1592), (6, 0, w1580), (6, 0, w1616), (6, 0, w1617), (6, 0, w1618), (6, 0, w1619), (6, 0, w831), (6, 0, w844), (6, 0, w879), (6, 0, w899), (6, 0, w929), (6, 0, w948), (6, 0, w981), (6, 0, w1013), (6, 0, w1620), (6, 1, w951), (6, 0, w1621), (6, 0, w1622), (6, 1, w1623), (6, 0, w1624), (6, 0, w1281), (6, 1, w1300), (6, 0, w1301), (6, 0, w1328), (6, 1, w1348), (6, 0, w1349), (6, 0, w1625), (6, 0, w1626), (6, 0, w1627), (6, 0, w1628), (6, 1, w1629), (6, 0, w1630), (6, 0, w1631), (6, 0, w1632), (6, 1, w1605), (6, 1, w1633), (6, 0, w1634)])
    (tbl_cons s521 (tbl_cons s550 (tbl_cons s575 (tbl_cons s597 (tbl_cons s104 (tbl_cons s152 (tbl_cons s183 (tbl_cons s214 (tbl_cons s245 (tbl_cons s271 (tbl_cons s309 (tbl_cons s343 (tbl_cons s394 (tbl_cons s419 (tbl_cons s458 (tbl_cons s486 (tbl_cons s1612 (tbl_cons s1613 (tbl_cons s1614 (tbl_cons s441 (tbl_cons s1615 (tbl_cons s1616 (tbl_cons s1041 (tbl_cons s1060 (tbl_cons s1107 (tbl_cons s1087 (tbl_cons s1379 (tbl_cons s1396 (tbl_cons s1441 (tbl_cons s1425 (tbl_cons s1543 (tbl_cons s1558 (tbl_cons s1593 (tbl_cons s1581 (tbl_cons s1617 (tbl_cons s1618 (tbl_cons s1619 (tbl_cons s1620 (tbl_cons s831 (tbl_cons s844 (tbl_cons s879 (tbl_cons s899 (tbl_cons s929 (tbl_cons s948 (tbl_cons s981 (tbl_cons s1013 (tbl_cons s1621 (tbl_cons s951 (tbl_cons s1622 (tbl_cons s1623 (tbl_cons s1624 (tbl_cons s1625 (tbl_cons s1281 (tbl_cons s1300 (tbl_cons s1301 (tbl_cons s1328 (tbl_cons s1348 (tbl_cons s1349 (tbl_cons s1626 (tbl_cons s1627 (tbl_cons s1628 (tbl_cons s1629 (tbl_cons s1630 (tbl_cons s1631 (tbl_cons s1632 (tbl_cons s1633 (tbl_cons s1606 (tbl_cons s1634 (tbl_cons s1635 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1803 : optimized 7 1 w1649 = false :=
  opt_false_of_P (tbl := [(6, 0, w685), (6, 0, w699), (6, 0, w772), (6, 0, w785), (6, 0, w1635), (6, 0, w424), (6, 0, w443), (6, 0, w1636), (6, 0, w1637), (6, 0, w1638), (6, 0, w1639), (6, 0, w1640), (6, 0, w1641), (6, 0, w1560), (6, 0, w1590), (6, 0, w1642), (6, 0, w1126), (6, 0, w1182), (6, 0, w1198), (6, 0, w1250), (6, 0, w1643), (6, 0, w952), (6, 0, w972), (6, 0, w1644), (6, 0, w1302), (6, 0, w1350), (6, 0, w1473), (6, 0, w1486), (6, 0, w1503), (6, 0, w1515), (6, 0, w1645), (6, 0, w1306), (6, 0, w1319), (6, 0, w1646), (6, 1, w1608), (6, 0, w1609), (6, 0, w1610), (6, 0, w1631), (6, 0, w1647), (6, 1, w1633), (6, 0, w1634), (6, 0, w1648), (6, 1, w65), (6, 0, w368), (6, 0, w1649), (6, 0, w67), (6, 0, w1607), (6, 0, w666), (6, 1, w1629), (6, 0, w1632), (6, 0, w1604)])
    (tbl_cons s685 (tbl_cons s699 (tbl_cons s772 (tbl_cons s785 (tbl_cons s1636 (tbl_cons s424 (tbl_cons s443 (tbl_cons s1637 (tbl_cons s1638 (tbl_cons s1639 (tbl_cons s1640 (tbl_cons s1641 (tbl_cons s1642 (tbl_cons s1561 (tbl_cons s1591 (tbl_cons s1643 (tbl_cons s1126 (tbl_cons s1182 (tbl_cons s1198 (tbl_cons s1250 (tbl_cons s1644 (tbl_cons s952 (tbl_cons s972 (tbl_cons s1645 (tbl_cons s1302 (tbl_cons s1350 (tbl_cons s1473 (tbl_cons s1486 (tbl_cons s1503 (tbl_cons s1515 (tbl_cons s1646 (tbl_cons s1306 (tbl_cons s1319 (tbl_cons s1647 (tbl_cons s1609 (tbl_cons s1610 (tbl_cons s1611 (tbl_cons s1632 (tbl_cons s1648 (tbl_cons s1634 (tbl_cons s1635 (tbl_cons s1649 (tbl_cons s65 (tbl_cons s368 (tbl_cons s1650 (tbl_cons s67 (tbl_cons s1608 (tbl_cons s666 (tbl_cons s1630 (tbl_cons s1633 (tbl_cons s1605 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1804 : optimized 7 1 w1604 = false :=
  opt_false_of_P (tbl := [(6, 0, w375), (6, 0, w1650), (6, 0, w482), (6, 0, w1651), (6, 0, w1536), (6, 0, w1652), (6, 0, w1576), (6, 0, w1653), (6, 0, w918), (6, 0, w1654), (6, 0, w1007), (6, 0, w1655), (6, 0, w1274), (6, 1, w1656), (6, 0, w1657), (6, 0, w1658), (6, 0, w1342), (6, 1, w1659), (6, 0, w1660), (6, 0, w1661), (6, 0, w1604), (6, 1, w65), (6, 0, w368), (6, 0, w67), (6, 0, w1603), (6, 0, w1602), (6, 1, w1629), (6, 0, w1647), (6, 0, w1649), (6, 0, w666), (6, 0, w686), (6, 0, w773), (6, 0, w1183), (6, 0, w1251), (6, 0, w1303), (6, 0, w1351), (6, 1, w1662), (6, 0, w1663), (6, 0, w1664)])
    (tbl_cons s375 (tbl_cons s1651 (tbl_cons s482 (tbl_cons s1652 (tbl_cons s1536 (tbl_cons s1653 (tbl_cons s1577 (tbl_cons s1654 (tbl_cons s918 (tbl_cons s1655 (tbl_cons s1007 (tbl_cons s1656 (tbl_cons s1274 (tbl_cons s1657 (tbl_cons s1658 (tbl_cons s1659 (tbl_cons s1342 (tbl_cons s1660 (tbl_cons s1661 (tbl_cons s1662 (tbl_cons s1605 (tbl_cons s65 (tbl_cons s368 (tbl_cons s67 (tbl_cons s1604 (tbl_cons s1603 (tbl_cons s1630 (tbl_cons s1648 (tbl_cons s1650 (tbl_cons s666 (tbl_cons s686 (tbl_cons s773 (tbl_cons s1183 (tbl_cons s1251 (tbl_cons s1303 (tbl_cons s1351 (tbl_cons s1663 (tbl_cons s1664 (tbl_cons s1665 tbl_nil)))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1805 : optimized 7 2 w1605 = false :=
  opt_false_of_P (tbl := [(6, 1, w437), (6, 0, w1665), (6, 0, w1666), (6, 0, w1667), (6, 1, w1668), (6, 0, w1669), (6, 0, w1670), (6, 0, w1671), (6, 0, w1672), (6, 0, w1673), (6, 0, w1674), (6, 1, w1675), (6, 0, w1676), (6, 1, w954), (6, 0, w1677), (6, 0, w1678), (6, 0, w1679), (6, 0, w1680), (6, 0, w1681), (6, 0, w1682), (6, 0, w1683), (6, 1, w1633), (6, 1, w1629), (6, 0, w1634), (6, 1, w1605), (6, 0, w1684), (6, 0, w1685), (6, 0, w522), (6, 0, w551), (6, 0, w576), (6, 0, w598), (6, 0, w105), (6, 0, w153), (6, 0, w184), (6, 0, w215), (6, 0, w246), (6, 0, w272), (6, 0, w310), (6, 0, w344), (6, 0, w395), (6, 0, w420), (6, 0, w459), (6, 0, w487), (6, 0, w1042), (6, 0, w1061), (6, 0, w1108), (6, 0, w1088), (6, 0, w1380), (6, 0, w1397), (6, 0, w1442), (6, 0, w1426), (6, 0, w1543), (6, 0, w1558), (6, 0, w1593), (6, 0, w1581), (6, 0, w832), (6, 0, w845), (6, 0, w880), (6, 0, w900), (6, 0, w930), (6, 0, w949), (6, 0, w982), (6, 0, w1014), (6, 0, w1282), (6, 0, w1304), (6, 0, w1329), (6, 0, w1352)])
    (tbl_cons s437 (tbl_cons s1666 (tbl_cons s1667 (tbl_cons s1668 (tbl_cons s1669 (tbl_cons s1670 (tbl_cons s1671 (tbl_cons s1672 (tbl_cons s1673 (tbl_cons s1674 (tbl_cons s1675 (tbl_cons s1676 (tbl_cons s1677 (tbl_cons s954 (tbl_cons s1678 (tbl_cons s1679 (tbl_cons s1680 (tbl_cons s1681 (tbl_cons s1682 (tbl_cons s1683 (tbl_cons s1684 (tbl_cons s1634 (tbl_cons s1630 (tbl_cons s1635 (tbl_cons s1606 (tbl_cons s1685 (tbl_cons s1686 (tbl_cons s522 (tbl_cons s551 (tbl_cons s576 (tbl_cons s598 (tbl_cons s105 (tbl_cons s153 (tbl_cons s184 (tbl_cons s215 (tbl_cons s246 (tbl_cons s272 (tbl_cons s310 (tbl_cons s344 (tbl_cons s395 (tbl_cons s420 (tbl_cons s459 (tbl_cons s487 (tbl_cons s1042 (tbl_cons s1061 (tbl_cons s1108 (tbl_cons s1088 (tbl_cons s1380 (tbl_cons s1397 (tbl_cons s1442 (tbl_cons s1426 (tbl_cons s1544 (tbl_cons s1559 (tbl_cons s1594 (tbl_cons s1582 (tbl_cons s832 (tbl_cons s845 (tbl_cons s880 (tbl_cons s900 (tbl_cons s930 (tbl_cons s949 (tbl_cons s982 (tbl_cons s1014 (tbl_cons s1282 (tbl_cons s1304 (tbl_cons s1329 (tbl_cons s1352 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1806 : optimized 7 1 w1607 = false :=
  opt_false_of_P (tbl := [(6, 0, w439), (6, 0, w1686), (6, 0, w425), (6, 0, w1687), (6, 0, w1588), (6, 0, w1688), (6, 0, w1561), (6, 0, w1689), (6, 0, w968), (6, 0, w1690), (6, 0, w955), (6, 0, w1691), (6, 0, w1317), (6, 0, w1692), (6, 0, w1308), (6, 0, w1693), (6, 0, w67), (6, 0, w1648), (6, 0, w1649), (6, 0, w1607), (6, 1, w65), (6, 0, w368), (6, 1, w1605), (6, 0, w1684), (6, 0, w666), (6, 0, w1683), (6, 0, w1606), (6, 0, w1602), (6, 0, w687), (6, 0, w700), (6, 0, w774), (6, 0, w786), (6, 0, w1694), (6, 0, w1695), (6, 0, w1696), (6, 0, w1697), (6, 0, w1127), (6, 0, w1184), (6, 0, w1199), (6, 0, w1252), (6, 0, w1474), (6, 0, w1487), (6, 0, w1504), (6, 0, w1516), (6, 1, w1633), (6, 0, w1634), (6, 1, w1662), (6, 0, w1663), (6, 0, w1664)])
    (tbl_cons s439 (tbl_cons s1687 (tbl_cons s425 (tbl_cons s1688 (tbl_cons s1589 (tbl_cons s1689 (tbl_cons s1562 (tbl_cons s1690 (tbl_cons s968 (tbl_cons s1691 (tbl_cons s955 (tbl_cons s1692 (tbl_cons s1317 (tbl_cons s1693 (tbl_cons s1308 (tbl_cons s1694 (tbl_cons s67 (tbl_cons s1649 (tbl_cons s1650 (tbl_cons s1608 (tbl_cons s65 (tbl_cons s368 (tbl_cons s1606 (tbl_cons s1685 (tbl_cons s666 (tbl_cons s1684 (tbl_cons s1607 (tbl_cons s1603 (tbl_cons s687 (tbl_cons s700 (tbl_cons s774 (tbl_cons s786 (tbl_cons s1695 (tbl_cons s1696 (tbl_cons s1697 (tbl_cons s1698 (tbl_cons s1127 (tbl_cons s1184 (tbl_cons s1199 (tbl_cons s1252 (tbl_cons s1474 (tbl_cons s1487 (tbl_cons s1504 (tbl_cons s1516 (tbl_cons s1634 (tbl_cons s1635 (tbl_cons s1663 (tbl_cons s1664 (tbl_cons s1665 tbl_nil)))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1807 : optimized 7 1 w1700 = false :=
  opt_false_of_P (tbl := [(6, 0, w504), (6, 0, w1698), (6, 0, w585), (6, 0, w1699), (6, 0, w1700), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1701), (6, 0, w1702), (6, 0, w1026), (6, 0, w1703), (6, 0, w1099), (6, 0, w1704), (6, 0, w1368), (6, 0, w1705), (6, 0, w1433), (6, 0, w1706), (6, 0, w1532), (6, 0, w1707), (6, 0, w1588), (6, 0, w1708), (6, 0, w666), (6, 0, w1709), (6, 0, w1710), (6, 0, w672), (6, 0, w759), (6, 1, w1711), (6, 0, w1712), (6, 0, w1713), (6, 0, w1166), (6, 0, w1237), (6, 0, w1455), (6, 0, w1498), (6, 0, w1637), (6, 0, w1694)])
    (tbl_cons s504 (tbl_cons s1699 (tbl_cons s585 (tbl_cons s1700 (tbl_cons s1701 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1702 (tbl_cons s1703 (tbl_cons s1026 (tbl_cons s1704 (tbl_cons s1099 (tbl_cons s1705 (tbl_cons s1368 (tbl_cons s1706 (tbl_cons s1433 (tbl_cons s1707 (tbl_cons s1532 (tbl_cons s1708 (tbl_cons s1589 (tbl_cons s1709 (tbl_cons s666 (tbl_cons s1710 (tbl_cons s1711 (tbl_cons s672 (tbl_cons s759 (tbl_cons s1712 (tbl_cons s1713 (tbl_cons s1714 (tbl_cons s1166 (tbl_cons s1237 (tbl_cons s1455 (tbl_cons s1498 (tbl_cons s1638 (tbl_cons s1695 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1808 : optimized 7 1 w1718 = false :=
  opt_false_of_P (tbl := [(6, 0, w673), (6, 0, w760), (6, 0, w1714), (6, 0, w543), (6, 0, w560), (6, 0, w1715), (6, 0, w1387), (6, 0, w1439), (6, 1, w1711), (6, 0, w1712), (6, 0, w1713), (6, 0, w1716), (6, 0, w1717), (6, 1, w65), (6, 0, w491), (6, 0, w1718), (6, 0, w67), (6, 0, w1710), (6, 0, w1167), (6, 0, w1238), (6, 0, w1719), (6, 0, w1057), (6, 0, w1076), (6, 0, w1720), (6, 0, w1477), (6, 0, w1513), (6, 0, w1721), (6, 0, w1403), (6, 0, w1423), (6, 0, w1722), (6, 0, w1638), (6, 0, w1695), (6, 0, w1723), (6, 0, w1560), (6, 0, w1576), (6, 0, w1724), (6, 0, w666), (6, 0, w1702)])
    (tbl_cons s673 (tbl_cons s760 (tbl_cons s1715 (tbl_cons s543 (tbl_cons s560 (tbl_cons s1716 (tbl_cons s1387 (tbl_cons s1439 (tbl_cons s1712 (tbl_cons s1713 (tbl_cons s1714 (tbl_cons s1717 (tbl_cons s1718 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1719 (tbl_cons s67 (tbl_cons s1711 (tbl_cons s1167 (tbl_cons s1238 (tbl_cons s1720 (tbl_cons s1057 (tbl_cons s1076 (tbl_cons s1721 (tbl_cons s1477 (tbl_cons s1513 (tbl_cons s1722 (tbl_cons s1403 (tbl_cons s1423 (tbl_cons s1723 (tbl_cons s1639 (tbl_cons s1696 (tbl_cons s1724 (tbl_cons s1561 (tbl_cons s1577 (tbl_cons s1725 (tbl_cons s666 (tbl_cons s1703 tbl_nil))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1809 : optimized 7 1 w1702 = false :=
  opt_false_of_P (tbl := [(6, 0, w506), (6, 0, w1725), (6, 0, w1726), (6, 0, w589), (6, 0, w674), (6, 0, w761), (6, 0, w1702), (6, 1, w65), (6, 0, w491), (6, 0, w67), (6, 0, w1701), (6, 0, w1700), (6, 0, w1030), (6, 0, w1727), (6, 0, w1101), (6, 0, w1728), (6, 0, w1372), (6, 0, w1729), (6, 0, w1435), (6, 0, w1730), (6, 0, w1536), (6, 0, w1731), (6, 0, w1590), (6, 0, w1732), (6, 0, w1716), (6, 0, w1718), (6, 0, w666), (6, 0, w1388), (6, 0, w1440), (6, 1, w1733), (6, 0, w1734), (6, 0, w1735), (6, 0, w1168), (6, 0, w1239), (6, 0, w1456), (6, 0, w1499), (6, 0, w1639), (6, 0, w1696)])
    (tbl_cons s506 (tbl_cons s1726 (tbl_cons s1727 (tbl_cons s589 (tbl_cons s674 (tbl_cons s761 (tbl_cons s1703 (tbl_cons s65 (tbl_cons s491 (tbl_cons s67 (tbl_cons s1702 (tbl_cons s1701 (tbl_cons s1030 (tbl_cons s1728 (tbl_cons s1101 (tbl_cons s1729 (tbl_cons s1372 (tbl_cons s1730 (tbl_cons s1435 (tbl_cons s1731 (tbl_cons s1536 (tbl_cons s1732 (tbl_cons s1591 (tbl_cons s1733 (tbl_cons s1717 (tbl_cons s1719 (tbl_cons s666 (tbl_cons s1388 (tbl_cons s1440 (tbl_cons s1734 (tbl_cons s1735 (tbl_cons s1736 (tbl_cons s1168 (tbl_cons s1239 (tbl_cons s1456 (tbl_cons s1499 (tbl_cons s1640 (tbl_cons s1697 tbl_nil))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1810 : optimized 7 1 w1710 = false :=
  opt_false_of_P (tbl := [(6, 0, w558), (6, 0, w1736), (6, 0, w1737), (6, 0, w547), (6, 0, w675), (6, 0, w762), (6, 0, w67), (6, 0, w1718), (6, 0, w1717), (6, 1, w65), (6, 0, w491), (6, 0, w1710), (6, 0, w1709), (6, 1, w1733), (6, 0, w1734), (6, 0, w1735), (6, 0, w1072), (6, 0, w1738), (6, 0, w1739), (6, 0, w1059), (6, 0, w1169), (6, 0, w1240), (6, 0, w1421), (6, 0, w1740), (6, 0, w1741), (6, 0, w1404), (6, 0, w1478), (6, 0, w1514), (6, 0, w1572), (6, 0, w1742), (6, 0, w1743), (6, 0, w1561), (6, 0, w1640), (6, 0, w1697), (6, 0, w666), (6, 0, w1700)])
    (tbl_cons s558 (tbl_cons s1737 (tbl_cons s1738 (tbl_cons s547 (tbl_cons s675 (tbl_cons s762 (tbl_cons s67 (tbl_cons s1719 (tbl_cons s1718 (tbl_cons s65 (tbl_cons s491 (tbl_cons s1711 (tbl_cons s1710 (tbl_cons s1734 (tbl_cons s1735 (tbl_cons s1736 (tbl_cons s1072 (tbl_cons s1739 (tbl_cons s1740 (tbl_cons s1059 (tbl_cons s1169 (tbl_cons s1240 (tbl_cons s1421 (tbl_cons s1741 (tbl_cons s1742 (tbl_cons s1404 (tbl_cons s1478 (tbl_cons s1514 (tbl_cons s1573 (tbl_cons s1743 (tbl_cons s1744 (tbl_cons s1562 (tbl_cons s1641 (tbl_cons s1698 (tbl_cons s666 (tbl_cons s1701 tbl_nil))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem s1811 : optimized 8 3 w1744 = false :=
  opt_false_of_P (tbl := [(7, 1, w64), (7, 1, w108), (7, 1, w69), (7, 1, w76), (7, 1, w216), (7, 1, w251), (7, 1, w218), (7, 1, w227), (7, 1, w345), (7, 1, w400), (7, 1, w347), (7, 1, w370), (7, 1, w488), (7, 1, w525), (7, 1, w490), (7, 1, w493), (7, 2, w599), (7, 1, w651), (7, 1, w690), (7, 2, w604), (7, 1, w653), (7, 1, w668), (7, 1, w801), (7, 1, w843), (7, 1, w803), (7, 1, w805), (7, 1, w907), (7, 1, w943), (7, 1, w909), (7, 1, w913), (7, 1, w1017), (7, 1, w1047), (7, 1, w1021), (7, 1, w1019), (7, 1, w1113), (7, 2, w1145), (7, 1, w1174), (7, 1, w1115), (7, 2, w1120), (7, 1, w1122), (7, 1, w1265), (7, 1, w1297), (7, 1, w1267), (7, 1, w1269), (7, 1, w1355), (7, 1, w1389), (7, 1, w1361), (7, 1, w1357), (7, 1, w1459), (7, 1, w1485), (7, 1, w1461), (7, 1, w1469), (7, 1, w1519), (7, 1, w1552), (7, 1, w1531), (7, 1, w1521), (7, 1, w1602), (7, 2, w1629), (7, 1, w1649), (7, 1, w1604), (7, 2, w1605), (7, 1, w1607), (7, 1, w1700), (7, 1, w1718), (7, 1, w1702), (7, 1, w1710)])
    (tbl_cons s1745 (tbl_cons s1746 (tbl_cons s1747 (tbl_cons s1748 (tbl_cons s1749 (tbl_cons s1750 (tbl_cons s1751 (tbl_cons s1752 (tbl_cons s1753 (tbl_cons s1754 (tbl_cons s1755 (tbl_cons s1756 (tbl_cons s1757 (tbl_cons s1758 (tbl_cons s1759 (tbl_cons s1760 (tbl_cons s1761 (tbl_cons s1762 (tbl_cons s1763 (tbl_cons s1764 (tbl_cons s1765 (tbl_cons s1766 (tbl_cons s1767 (tbl_cons s1768 (tbl_cons s1769 (tbl_cons s1770 (tbl_cons s1771 (tbl_cons s1772 (tbl_cons s1773 (tbl_cons s1774 (tbl_cons s1775 (tbl_cons s1776 (tbl_cons s1777 (tbl_cons s1778 (tbl_cons s1779 (tbl_cons s1780 (tbl_cons s1781 (tbl_cons s1782 (tbl_cons s1783 (tbl_cons s1784 (tbl_cons s1785 (tbl_cons s1786 (tbl_cons s1787 (tbl_cons s1788 (tbl_cons s1789 (tbl_cons s1790 (tbl_cons s1791 (tbl_cons s1792 (tbl_cons s1793 (tbl_cons s1794 (tbl_cons s1795 (tbl_cons s1796 (tbl_cons s1797 (tbl_cons s1798 (tbl_cons s1799 (tbl_cons s1800 (tbl_cons s1801 (tbl_cons s1802 (tbl_cons s1803 (tbl_cons s1804 (tbl_cons s1805 (tbl_cons s1806 (tbl_cons s1807 (tbl_cons s1808 (tbl_cons s1809 (tbl_cons s1810 tbl_nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel)

def rows : List W := w1744

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [9, 14]⟩], 15⟩

set_option maxRecDepth 8000 in
theorem reject : search 8 rows = false := by
  have hcut : ∀ ws ∈ rows.sublists, ws = rows ∨
      (decide (ws.length ≤ 8+1) && (cuts ws == -1)) = false := by decide +kernel
  have key : ∀ ws ∈ rows.sublists,
      (decide (ws.length ≤ 8+1) && (cuts ws == -1) && optimized 8 (8+1-ws.length) ws) = false := by
    intro ws hws
    rcases hcut ws hws with h | h
    · subst h
      have e : (8+1-rows.length) = 3 := by decide
      rw [e]
      exact (Bool.and_eq_false_iff.2 (Or.inr s1811))
    · rw [h, Bool.false_and]
  unfold search
  exact List.any_eq_false.2 (fun ws hws => by simp only [key ws hws, Bool.false_eq_true, not_false_eq_true])

set_option maxRecDepth 8000 in
theorem solve (s : ℕ) (hs : HasCircuitSize 6 (targetFun (4008372960 * 2 ^ 32 + 4008241856)) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetFun (4008372960 * 2 ^ 32 + 4008241856) x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search (4008372960 * 2 ^ 32 + 4008241856) rows rfl (by decide) reject
      (by decide +kernel) C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, by decide⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_16465

theorem PEqualNP.Outside.L_meta_16465 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008241856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_16465.solve

