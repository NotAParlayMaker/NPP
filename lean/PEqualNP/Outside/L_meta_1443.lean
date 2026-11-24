import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1443_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (fresh : Finset α → α → Prop) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops fresh goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, fresh available z ∧ build ops fresh goal k (insert z available)

def live (ops : α → α → Finset α) (fresh : Finset α → α → Prop) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops fresh goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, fresh s z ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops fresh goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {fresh : Finset α → α → Prop}
    (hanti : ∀ {s t : Finset α} {z : α}, s ⊆ t → fresh t z → fresh s z)
    {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops fresh goal k available) : ∃ s ⊆ available, live ops fresh goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hfr, tail⟩
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
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz, hanti hs hfr,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {fresh : Finset α → α → Prop}
    {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops fresh goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, _, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {fresh : Finset α → α → Prop}
    {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops fresh goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, _, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {fresh : Finset α → α → Prop}
    {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops fresh goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, fresh s z ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops fresh goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hfr, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hfr, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 512
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

def freshW (av : Finset W) (z : W) : Prop := ¬ holds av z

theorem freshW_anti {s t : Finset W} {z : W} (hst : s ⊆ t) (h : freshW t z) : freshW s z := by
  intro hs
  apply h
  rcases hs with h0 | h1 | ⟨a, ha, he⟩
  · exact .inl h0
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨a, hst ha, he⟩)

def isFreshB (a b : W) (r : List W) (w : W) : Bool :=
  w != 0 && w != ~~~0 && w != a && w != ~~~a && w != b && w != ~~~b &&
    r.all fun u => w != u && w != ~~~u

theorem isFreshB_of_freshW {ws r : List W} {a b w : W}
    (hp : ws.Perm (a :: b :: r)) (h : freshW ws.toFinset w) : isFreshB a b r w = true := by
  have hmem : ∀ u, u ∈ ws ↔ u = a ∨ u = b ∨ u ∈ r := by
    intro u; simp [hp.mem_iff]
  have h0 : w ≠ 0 := fun e => h (.inl e)
  have h1 : w ≠ ~~~0 := fun e => h (.inr (.inl e))
  have hne : ∀ u ∈ ws, w ≠ u ∧ w ≠ ~~~u := by
    intro u hu
    constructor <;> intro e <;> exact h (.inr (.inr ⟨u, List.mem_toFinset.mpr hu, by simp [e]⟩))
  have ha := hne a ((hmem a).mpr (.inl rfl))
  have hb := hne b ((hmem b).mpr (.inr (.inl rfl)))
  simp only [isFreshB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨h0, h1⟩, ha.1⟩, ha.2⟩, hb.1⟩, hb.2⟩, ?_⟩
  intro u hu
  exact hne u ((hmem u).mpr (.inr (.inr hu)))

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

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256 + i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256 + i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps freshW g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
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
  let sa := sep a
  let sb := sep b
  (ops a b).any fun w =>
    isFreshB a b r w &&
    let v := sep w ||| base
    (((v == -1) && next extra (w :: r)) ||
     ((extra != 0) && (((v ||| sa == -1) && next (extra - 1) (w :: a :: r)) ||
                        ((v ||| sb == -1) && next (extra - 1) (w :: b :: r)))) ||
     ((extra ≥ 2) && (v ||| sa ||| sb == -1) && next (extra - 2) (w :: a :: b :: r)))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hfr : isFreshB a b r z = true)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp only [hfr, Bool.true_and]
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
    (room : extra + ws.length = n + 1) (h : live basicOps freshW g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hfr, hout, needed, hs, tail⟩
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
        have hl : live basicOps freshW g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop
          (isFreshB_of_freshW perm hfr) hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cuts ws == -1) && optimized n (n + 1 - ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps freshW g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress (fresh := freshW) (fun hst hfr => freshW_anti hst hfr) h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps freshW g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n + 1 - ws.length + ws.length = n + 1) hl']⟩

open PEqualNP.CircuitLowerBounds

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, freshW av w ∧ holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hfr, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, hfr, holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z := by
    by_cases hhold : holds av w
    · exact .inl (hz.elim (fun e => e ▸ hhold) (fun e => e ▸ holds_not hhold))
    · exact .inr ⟨a, ha, b, hb, h, w, hw, hhold, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps, ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps, ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps, ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      BitVec.getElem_zero, bit0, Bool.not_false] <;> rfl

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
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
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
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps freshW t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
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
        rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, hfr, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, hfr, run⟩⟩

theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search n ins = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps freshW t a ins.toFinset) : build basicOps freshW t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht n ins nd (lift low run)
  exact Bool.noConfusion (rejection.symm.trans found)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search (m - 2) ins = false)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds, p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have b := bound_from_search T (m - 2) ins nd row width rejection gs o hg he
    obtain ⟨ds, p, ok, size, ev⟩ := upper
    exact ⟨ds, p, ok, by omega, ev⟩
  · refine ⟨gs, o, ?_, le_rfl, he⟩
    intro g hm
    obtain ⟨hop, cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g, hm, eq⟩).elim)), cap⟩


def ins_feeafcc0 : List W := [0x0000fff000fff000fff000ffffff000ffffffffffff000fff000fff000fff00000000aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa0aa, 0xffffffffff000000ffffff000ffffff000fff000ffffff000000ffffffffffff000020c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c20c, 0xffffffffffffffff000000000fffffffff000000ffffffffffff000000ffffff0000430430430430430430430430430430430430430430430430430430430430, 0x0000fffffffffffffffffffff000000000000000ffffffffffffffffff00000000008c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c08c0, 0x0000ffffffffffffffffffffffffffffffffffff0000000000000000000000000000f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00f00]

theorem nd_feeafcc0 : ins_feeafcc0.Nodup := by decide +kernel

theorem spec_feeafcc0 : ∀ j : Fin 512, Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if (ins_feeafcc0.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeafcc0 : search 4 ins_feeafcc0 = false := by decide +kernel

def gates_feeafcc0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [9, 7]⟩]

theorem upper_feeafcc0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeafcc0, 10, ?_, rfl, ?_⟩
  · simp [gates_feeafcc0]
  · decide +kernel


def ins_eeeaeaea : List W := [0xfffffffff001fffff800fffffc007ffffffffff800fffffffffff001ffffffff0000000000000000000000000000000000000000000000000000000000000000, 0x0000007ffffe003fffff001fffff800ffe003fffff001ffc007ffffe003ff8000000000921242484909212424849092124248490921242484909212424849092, 0x0000007fffffffc00000001ffffffff000003fffffffe000007fffffffc00000000000524a4949292524a4949292524a4949292524a4949292524a4949292524, 0x0000007fffffffffffffffe00000000000003fffffffffffff80000000000000000000638c718e31c638c718e31c638c718e31c638c718e31c638c718e31c638, 0x0000007fffffffffffffffffffffffffffffc0000000000000000000000000000000007c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0]

theorem nd_eeeaeaea : ins_eeeaeaea.Nodup := by decide +kernel

theorem spec_eeeaeaea : ∀ j : Fin 512, Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if (ins_eeeaeaea.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaeaea : search 2 ins_eeeaeaea = false := by decide +kernel

def gates_eeeaeaea : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 4]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 0]⟩]

theorem upper_eeeaeaea : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_eeeaeaea, 8, ?_, rfl, ?_⟩
  · simp [gates_eeeaeaea]
  · decide +kernel


def ins_eeeaeee8 : List W := [0xfffffffff001fffff800fffffc007ffffffffff800fffffc007ffffe003fffff0000000020040080100200400801002004008010020040080100200400801002, 0xfffffffffffe003fffff001fffff800ffe003fffff001fffff800fffffc007ff0000000841082104208410821042084108210420841082104208410821042084, 0x0000007fffffffc00000001ffffffff000003fffffffe00000000ffffffff800000000528a514a294528a514a294528a514a294528a514a294528a514a294528, 0x0000007fffffffffffffffe00000000000003ffffffffffffffff00000000000000000630c618c318630c618c318630c618c318630c618c318630c618c318630, 0x0000007fffffffffffffffffffffffffffffc0000000000000000000000000000000007c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0]

theorem nd_eeeaeee8 : ins_eeeaeee8.Nodup := by decide +kernel

theorem spec_eeeaeee8 : ∀ j : Fin 512, Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if (ins_eeeaeee8.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeaeee8 : search 4 ins_eeeaeee8 = false := by decide +kernel

def gates_eeeaeee8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [9, 5]⟩]

theorem upper_eeeaeee8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_eeeaeee8, 10, ?_, rfl, ?_⟩
  · simp [gates_eeeaeee8]
  · decide +kernel


def ins_eeeeeee0 : List W := [0xfffffffff001fffff800fffffc007ffffe003fffff001fffff800fffffc007ff00000000a0140280500a0140280500a0140280500a0140280500a0140280500a, 0x0000007ffffe003fffff001fffff800fffffc007ffffe003fffff001fffff80000000000c0180300600c0180300600c0180300600c0180300600c0180300600c, 0xffffffffffffffc00000001ffffffff000000007fffffffc00000001ffffffff000000550aa1542a8550aa1542a8550aa1542a8550aa1542a8550aa1542a8550, 0x0000007fffffffffffffffe00000000000000007fffffffffffffffe00000000000000660cc198330660cc198330660cc198330660cc198330660cc198330660, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_eeeeeee0 : ins_eeeeeee0.Nodup := by decide +kernel

theorem spec_eeeeeee0 : ∀ j : Fin 512, Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if (ins_eeeeeee0.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_eeeeeee0 : search 2 ins_eeeeeee0 = false := by decide +kernel

def gates_eeeeeee0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [7, 5]⟩]

theorem upper_eeeeeee0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_eeeeeee0, 8, ?_, rfl, ?_⟩
  · simp [gates_eeeeeee0]
  · decide +kernel


def ins_fee8eee8 : List W := [0xfffffffff001ffc007ff001fffff800ffffffff800fffffc007ffffe003fffff0000000821042084108210420841082104208410821042084108210420841082, 0xfffffffffffe000007ffffe003fffff001ffffffff001fffff800fffffc007ff0000001042084108210420841082104208410821042084108210420841082104, 0x0000007ffffffffff800000003fffffffe003fffffffe00000000ffffffff8000000002284508a1142284508a1142284508a1142284508a1142284508a114228, 0x0000007ffffffffffffffffffc00000000003ffffffffffffffff000000000000000004308610c2184308610c2184308610c2184308610c2184308610c218430, 0x0000007fffffffffffffffffffffffffffffc0000000000000000000000000000000007c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0f81f03e07c0]

theorem nd_fee8eee8 : ins_fee8eee8.Nodup := by decide +kernel

theorem spec_fee8eee8 : ∀ j : Fin 512, Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if (ins_fee8eee8.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_fee8eee8 : search 6 ins_fee8eee8 = false := by decide +kernel

def gates_fee8eee8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [6, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [11, 10]⟩]

theorem upper_fee8eee8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_fee8eee8, 12, ?_, rfl, ?_⟩
  · simp [gates_fee8eee8]
  · decide +kernel


def ins_feeaeaaa : List W := [0xfffffffff001ffc007ff001fffff800fffffffffff001fffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0x0000007ffffe000007ffffe003fffff001ffc007ffffe003ff800ffe003ff80000000012a2544a89512a2544a89512a2544a89512a2544a89512a2544a89512a, 0x0000007ffffffffff800000003fffffffe000007fffffffc00000fffffc0000000000024c4989312624c4989312624c4989312624c4989312624c4989312624c, 0x0000007ffffffffffffffffffc00000000000007fffffffffffff000000000000000004708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_feeaeaaa : ins_feeaeaaa.Nodup := by decide +kernel

theorem spec_feeaeaaa : ∀ j : Fin 512, Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if (ins_feeaeaaa.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeaeaaa : search 6 ins_feeaeaaa = false := by decide +kernel

def gates_feeaeaaa : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [1, 2]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [11, 7]⟩]

theorem upper_feeaeaaa : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeaeaaa, 12, ?_, rfl, ?_⟩
  · simp [gates_feeaeaaa]
  · decide +kernel


def ins_feeaeae8 : List W := [0xfffffffff001ffc007ff001fffff800fffffffffff001ffffffffffe003fffff0000000020040080100200400801002004008010020040080100200400801002, 0xfffffffffffe000007ffffe003fffff001ffc007ffffe003ff800fffffc007ff0000001242484909212424849092124248490921242484909212424849092124, 0x0000007ffffffffff800000003fffffffe000007fffffffc00000ffffffff8000000002484909212424849092124248490921242484909212424849092124248, 0x0000007ffffffffffffffffffc00000000000007fffffffffffff000000000000000004708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_feeaeae8 : ins_feeaeae8.Nodup := by decide +kernel

theorem spec_feeaeae8 : ∀ j : Fin 512, Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if (ins_feeaeae8.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeaeae8 : search 7 ins_feeaeae8 = false := by decide +kernel

def gates_feeaeae8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [1, 2]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.or, [8, 6]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [11, 6]⟩, ⟨.or, [12, 10]⟩]

theorem upper_feeaeae8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeaeae8, 13, ?_, rfl, ?_⟩
  · simp [gates_feeaeae8]
  · decide +kernel


def ins_feeaece8 : List W := [0xfffffffff001ffc007ff001fffff800fffffffffff001fffff800ffe003fffff0000000220440881102204408811022044088110220440881102204408811022, 0xfffffffffffe000007ffffe003fffff001ffc007ffffe003ffffffffffc007ff0000001042084108210420841082104208410821042084108210420841082104, 0x0000007ffffffffff800000003fffffffe000007fffffffc00000ffffffff8000000002484909212424849092124248490921242484909212424849092124248, 0x0000007ffffffffffffffffffc00000000000007fffffffffffff000000000000000004708e11c2384708e11c2384708e11c2384708e11c2384708e11c238470, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_feeaece8 : ins_feeaece8.Nodup := by decide +kernel

theorem spec_feeaece8 : ∀ j : Fin 512, Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if (ins_feeaece8.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeaece8 : search 6 ins_feeaece8 = false := by decide +kernel

def gates_feeaece8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.and, [5, 2]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [10, 9]⟩, ⟨.or, [11, 6]⟩]

theorem upper_feeaece8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeaece8, 12, ?_, rfl, ?_⟩
  · simp [gates_feeaece8]
  · decide +kernel


def ins_feeaeee0 : List W := [0xfffffffff001ffc007ff001fffff800fffffffffff001fffff800fffffc007ff00000000a0140280500a0140280500a0140280500a0140280500a0140280500a, 0x0000007ffffe000007ffffe003fffff001ffc007ffffe003fffff001fffff80000000010c2184308610c2184308610c2184308610c2184308610c2184308610c, 0xfffffffffffffffff800000003fffffffe000007fffffffc00000001ffffffff0000002504a0941282504a0941282504a0941282504a0941282504a094128250, 0x0000007ffffffffffffffffffc00000000000007fffffffffffffffe000000000000004608c1182304608c1182304608c1182304608c1182304608c118230460, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_feeaeee0 : ins_feeaeee0.Nodup := by decide +kernel

theorem spec_feeaeee0 : ∀ j : Fin 512, Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if (ins_feeaeee0.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeaeee0 : search 5 ins_feeaeee0 = false := by decide +kernel

def gates_feeaeee0 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [10, 8]⟩]

theorem upper_feeaeee0 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeaeee0, 11, ?_, rfl, ?_⟩
  · simp [gates_feeaeee0]
  · decide +kernel


def ins_feeafcc8 : List W := [0xfffffffff001ffc007ff001fffff800fffffffffff001ffc007ff001ffc007ff0000000520a4148290520a4148290520a4148290520a4148290520a414829052, 0xfffffffffffe000007ffffe003fffff001ffc007ffffe000007fffffffffffff0000001042084108210420841082104208410821042084108210420841082104, 0x0000007ffffffffff800000003fffffffe000007ffffffffff800001fffff8000000002184308610c2184308610c2184308610c2184308610c2184308610c218, 0x0000007ffffffffffffffffffc00000000000007fffffffffffffffe000000000000004608c1182304608c1182304608c1182304608c1182304608c118230460, 0x0000007ffffffffffffffffffffffffffffffff8000000000000000000000000000000780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e03c0780]

theorem nd_feeafcc8 : ins_feeafcc8.Nodup := by decide +kernel

theorem spec_feeafcc8 : ∀ j : Fin 512, Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if (ins_feeafcc8.getD i.val 0)[j.val] then 2 ^ (i : ℕ) else 0) = goal[j.val] := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_feeafcc8 : search 5 ins_feeafcc8 = false := by decide +kernel

def gates_feeafcc8 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [0, 2]⟩, ⟨.and, [5, 1]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 7]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [10, 9]⟩]

theorem upper_feeafcc8 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨gates_feeafcc8, 11, ?_, rfl, ?_⟩
  · simp [gates_feeafcc8]
  · decide +kernel


end PEqualNP.Outside.L_meta_1443_aux

open PEqualNP.Outside.L_meta_1443_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1443 : ∀ T ∈ ({0xfeeafcc0, 0xeeeaeaea, 0xeeeaeee8, 0xeeeeeee0, 0xfee8eee8, 0xfeeaeaaa, 0xfeeaeae8, 0xfeeaece8, 0xfeeaeee0, 0xfeeafcc8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xfeeafcc0 6 ins_feeafcc0 nd_feeafcc0 spec_feeafcc0 rfl reject_feeafcc0 upper_feeafcc0 gs o hg he
  · exact replace 0xeeeaeaea 4 ins_eeeaeaea nd_eeeaeaea spec_eeeaeaea rfl reject_eeeaeaea upper_eeeaeaea gs o hg he
  · exact replace 0xeeeaeee8 6 ins_eeeaeee8 nd_eeeaeee8 spec_eeeaeee8 rfl reject_eeeaeee8 upper_eeeaeee8 gs o hg he
  · exact replace 0xeeeeeee0 4 ins_eeeeeee0 nd_eeeeeee0 spec_eeeeeee0 rfl reject_eeeeeee0 upper_eeeeeee0 gs o hg he
  · exact replace 0xfee8eee8 8 ins_fee8eee8 nd_fee8eee8 spec_fee8eee8 rfl reject_fee8eee8 upper_fee8eee8 gs o hg he
  · exact replace 0xfeeaeaaa 8 ins_feeaeaaa nd_feeaeaaa spec_feeaeaaa rfl reject_feeaeaaa upper_feeaeaaa gs o hg he
  · exact replace 0xfeeaeae8 9 ins_feeaeae8 nd_feeaeae8 spec_feeaeae8 rfl reject_feeaeae8 upper_feeaeae8 gs o hg he
  · exact replace 0xfeeaece8 8 ins_feeaece8 nd_feeaece8 spec_feeaece8 rfl reject_feeaece8 upper_feeaece8 gs o hg he
  · exact replace 0xfeeaeee0 7 ins_feeaeee0 nd_feeaeee0 spec_feeaeee0 rfl reject_feeaeee0 upper_feeaeee0 gs o hg he
  · exact replace 0xfeeafcc8 7 ins_feeafcc8 nd_feeafcc8 spec_feeafcc8 rfl reject_feeafcc8 upper_feeafcc8 gs o hg he
