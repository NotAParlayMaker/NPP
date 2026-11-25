import PEqualNP.Defs

-- The witness has 12 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 10 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12110_aux
namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
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

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[2,6]⟩, ⟨.and,[3,4]⟩, ⟨.and,[5,7]⟩, ⟨.or,[0,1]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,11]⟩, ⟨.or,[3,4]⟩, ⟨.or,[9,8]⟩, ⟨.and,[10,14]⟩, ⟨.or,[12,15]⟩, ⟨.and,[13,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfee8e800fe808000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
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
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfee8e800fe808000 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfee8e800fe808000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def ew0 : Word := 0xaa00

def ew1 : Word := 0xcc00

def ew2 : Word := 0xf000

def ew3 : Word := 0x888888

def ew4 : Word := 0x909090

def ew5 : Word := 0x8088888

def ew6 : Word := 0x8880888

def ew7 : Word := 0x8888888

def ew8 : Word := 0x9009900

def ew9 : Word := 0x9990000

def ew10 : Word := 0xa00a000

def ew11 : Word := 0xc00c000

def ew12 : Word := 0xf000000

def ew13 : Word := 0x10109090

def ew14 : Word := 0x10901090

def ew15 : Word := 0x10909090

def ew16 : Word := 0x11009900

def ew17 : Word := 0x11990000

def ew18 : Word := 0x19001900

def ew19 : Word := 0x19009900

def ew20 : Word := 0x19190000

def ew21 : Word := 0x19990000

def ew22 : Word := 0x22008800

def ew23 : Word := 0x3000c000

def ew24 : Word := 0x33000000

def ew25 : Word := 0x44008800

def ew26 : Word := 0x5000a000

def ew27 : Word := 0x55000000

def ew28 : Word := 0x80008000

def ew29 : Word := 0x80800000

def ew30 : Word := 0x80808080

def ew31 : Word := 0x82008200

def ew32 : Word := 0x82828282

def ew33 : Word := 0x84008400

def ew34 : Word := 0x84848484

def ew35 : Word := 0x88000000

def ew36 : Word := 0x88008800

def ew37 : Word := 0x88880000

def ew38 : Word := 0x88888888

def ew39 : Word := 0x90000000

def ew40 : Word := 0x90009000

def ew41 : Word := 0x90900000

def ew42 : Word := 0x90909090

def ew43 : Word := 0x99000000

def ew44 : Word := 0x99009900

def ew45 : Word := 0x99990000

def ew46 : Word := 0xa000a000

def ew47 : Word := 0xa0a0a0a0

def ew48 : Word := 0xa5000000

def ew49 : Word := 0xa500a500

def ew50 : Word := 0xa5a50000

def ew51 : Word := 0xaa00aa00

def ew52 : Word := 0xaaaa0000

def ew53 : Word := 0xaaaaaaaa

def ew54 : Word := 0xc000c000

def ew55 : Word := 0xc0c0c0c0

def ew56 : Word := 0xc3000000

def ew57 : Word := 0xc300c300

def ew58 : Word := 0xc3c30000

def ew59 : Word := 0xcc00cc00

def ew60 : Word := 0xcccc0000

def ew61 : Word := 0xcccccccc

def ew62 : Word := 0xee00ee00

def ew63 : Word := 0xf000f000

def ew64 : Word := 0xf0f00000

def ew65 : Word := 0xf0f0f0f0

def ew66 : Word := 0xfa00fa00

def ew67 : Word := 0xfc00fc00

def ew68 : Word := 0xff000000

def ew69 : Word := 0xff00ff00

def ew70 : Word := 0xffff0000

def ew71 : Word := 0x880000008800

def ew72 : Word := 0x888800008888

def ew73 : Word := 0x888888880000

def ew74 : Word := 0xa0000000a000

def ew75 : Word := 0xa0a00000a0a0

def ew76 : Word := 0xa0a0a0a00000

def ew77 : Word := 0xaa0000000000

def ew78 : Word := 0xaa000000aa00

def ew79 : Word := 0xaa00aa000000

def ew80 : Word := 0xaaaa00000000

def ew81 : Word := 0xaaaa0000aaaa

def ew82 : Word := 0xcc000000cc00

def ew83 : Word := 0xcccc0000cccc

def ew84 : Word := 0xf0000000f000

def ew85 : Word := 0xf0f00000f0f0

def ew86 : Word := 0xff0000000000

def ew87 : Word := 0xff000000ff00

def ew88 : Word := 0xffff00000000

def ew89 : Word := 0x88008800880088

def ew90 : Word := 0x88008888008800

def ew91 : Word := 0xa000a000a000a0

def ew92 : Word := 0xa000a0a000a000

def ew93 : Word := 0xaa000000aa0000

def ew94 : Word := 0xaa0000aa000000

def ew95 : Word := 0xaa00aa00000000

def ew96 : Word := 0xaa00aa00aa00aa

def ew97 : Word := 0xcc00cc00cc00cc

def ew98 : Word := 0xf000f000f000f0

def ew99 : Word := 0xff000000ff0000

def ew100 : Word := 0xff00ff00000000

def ew101 : Word := 0x808080808080808

def ew102 : Word := 0x808808008088080

def ew103 : Word := 0x880088008800880

def ew104 : Word := 0xa000a000a000a00

def ew105 : Word := 0xa00a0000a00a000

def ew106 : Word := 0xa0a00000a0a0000

def ew107 : Word := 0xa0a0a0a00000000

def ew108 : Word := 0xa0a0a0a0a0a0a0a

def ew109 : Word := 0xa0aa0a000000000

def ew110 : Word := 0xaa000000aa00000

def ew111 : Word := 0xaa00aa000000000

def ew112 : Word := 0xc0c0c0c00000000

def ew113 : Word := 0xc0c0c0c0c0c0c0c

def ew114 : Word := 0xf000f0000000000

def ew115 : Word := 0xf000f000f000f00

def ew116 : Word := 0xf0f000000000000

def ew117 : Word := 0xf0f00000f0f0000

def ew118 : Word := 0xf0f0f0f00000000

def ew119 : Word := 0x2020202020202020

def ew120 : Word := 0x2020808020208080

def ew121 : Word := 0x2080208020802080

def ew122 : Word := 0x2200220022002200

def ew123 : Word := 0x2200880022008800

def ew124 : Word := 0x2222000022220000

def ew125 : Word := 0x2222222200000000

def ew126 : Word := 0x2222222222222222

def ew127 : Word := 0x2222888800000000

def ew128 : Word := 0x2288000022880000

def ew129 : Word := 0x2288228800000000

def ew130 : Word := 0x3030303030303030

def ew131 : Word := 0x3300330033003300

def ew132 : Word := 0x3333000033330000

def ew133 : Word := 0x3333333300000000

def ew134 : Word := 0x4444444444444444

def ew135 : Word := 0x5050505050505050

def ew136 : Word := 0x5500550055005500

def ew137 : Word := 0x5555000055550000

def ew138 : Word := 0x5555555500000000

def ew139 : Word := 0x8008800880088008

def ew140 : Word := 0x8020802080208020

def ew141 : Word := 0x8080080880800808

def ew142 : Word := 0x8080202080802020

def ew143 : Word := 0x8080808080808080

def ew144 : Word := 0x8800220088002200

def ew145 : Word := 0x8800880000880088

def ew146 : Word := 0x8800880088008800

def ew147 : Word := 0x8822000088220000

def ew148 : Word := 0x8822882200000000

def ew149 : Word := 0x8888000000008888

def ew150 : Word := 0x8888000088880000

def ew151 : Word := 0x8888222200000000

def ew152 : Word := 0x8888888800000000

def ew153 : Word := 0x8888888888888888

def ew154 : Word := 0xa0000a00a0000a00

def ew155 : Word := 0xa000a00000a000a0

def ew156 : Word := 0xa000a000a000a000

def ew157 : Word := 0xa00a0000a00a0000

def ew158 : Word := 0xa00aa00a00000000

def ew159 : Word := 0xa0a000000000a0a0

def ew160 : Word := 0xa0a00000a0a00000

def ew161 : Word := 0xa0a00a0a00000000

def ew162 : Word := 0xa0a0a0a000000000

def ew163 : Word := 0xa0a0a0a0a0a0a0a0

def ew164 : Word := 0xaa0000000000aa00

def ew165 : Word := 0xaa00000000aa0000

def ew166 : Word := 0xaa000000aa000000

def ew167 : Word := 0xaa00aa0000000000

def ew168 : Word := 0xaa00aa00aa00aa00

def ew169 : Word := 0xaaaa000000000000

def ew170 : Word := 0xaaaa0000aaaa0000

def ew171 : Word := 0xaaaaaaaa00000000

def ew172 : Word := 0xaaaaaaaaaaaaaaaa

def ew173 : Word := 0xc0c0c0c0c0c0c0c0

def ew174 : Word := 0xcc00cc00cc00cc00

def ew175 : Word := 0xcccc0000cccc0000

def ew176 : Word := 0xcccccccc00000000

def ew177 : Word := 0xcccccccccccccccc

def ew178 : Word := 0xf000f000f000f000

def ew179 : Word := 0xf0f00000f0f00000

def ew180 : Word := 0xf0f0f0f000000000

def ew181 : Word := 0xf0f0f0f0f0f0f0f0

def ew182 : Word := 0xff000000ff000000

def ew183 : Word := 0xff00ff0000000000

def ew184 : Word := 0xff00ff00ff00ff00

def ew185 : Word := 0xffff000000000000

def ew186 : Word := 0xffff0000ffff0000

def ew187 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0xf2c,
  0xf1c,
  0x171c,
  0xf30,
  0x1b2c,
  0x174c,
  0x1924,
  0xf34,
  0x1750,
  0x1c30,
  0x1c60,
  0x1b4c,
  0x100e,
  0xf38,
  0xf0c,
  0xf20
]

def labelsBlock1 : Array Nat := #[
  0x1960,
  0x170c,
  0xf10,
  0x1710,
  0x1b60,
  0x1a60,
  0x1b0c,
  0x1012,
  0x1c50,
  0x1a28,
  0x1016,
  0x1c20,
  0xf24,
  0x1c10,
  0x2b2c,
  0x101a
]

def labelsBlock2 : Array Nat := #[
  0x1920,
  0x1944,
  0x1b20,
  0x1a20,
  0xf28,
  0x1904,
  0x1740,
  0xf00,
  0x1032,
  0x1b40,
  0x1c40,
  0x1900,
  0x1042,
  0x1754,
  0xf14,
  0xf04
]

def labelsBlock3 : Array Nat := #[
  0x1700,
  0x1c00,
  0x1714,
  0x2d34,
  0x2b24,
  0x334c,
  0x1096,
  0x2d24,
  0x2b0c,
  0x109a,
  0x1758,
  0x10aa,
  0x1a00,
  0x1934,
  0x1b00,
  0xf18
]

def labelsBlock4 : Array Nat := #[
  0x2ba4,
  0x330c,
  0x109e,
  0x1a38,
  0x1a48,
  0x1718,
  0x2da4,
  0x10ae,
  0x2b28,
  0x10a2,
  0x10b2,
  0x1704,
  0x2b04,
  0x101e,
  0x1022,
  0x102a
]

def labelsBlock5 : Array Nat := #[
  0x103a,
  0x103e,
  0x102e,
  0x2b8c,
  0x338c,
  0x10b6,
  0x2d04,
  0x2b20,
  0x1930,
  0x1a30,
  0x1d,
  0x25,
  0x9,
  0x15,
  0x49,
  0x41
]

def labelsBlock6 : Array Nat := #[
  0x81,
  0x79,
  0x1056,
  0x10ba,
  0xf08,
  0x2b00,
  0x2b08,
  0x2e20,
  0x2d20,
  0x3304,
  0x21,
  0x29,
  0x2d,
  0x31,
  0x4d,
  0x51
]

def labelsBlock7 : Array Nat := #[
  0x55,
  0x65,
  0x69,
  0x85,
  0x89,
  0x99,
  0x1b24,
  0x1d34,
  0x1d24,
  0x1e38,
  0x1e28,
  0x100a,
  0x1006,
  0x1002,
  0x107a,
  0x1066
]

def labelsBlock8 : Array Nat := #[
  0x106e,
  0x1072,
  0x106a,
  0x1076,
  0x105e,
  0x107e,
  0x105a,
  0x1082,
  0x1036,
  0x1052,
  0x108a,
  0x1046,
  0x1092,
  0x2e38,
  0x2ba8,
  0x10a6
]

def labelsBlock9 : Array Nat := #[
  0x1708,
  0x2e00,
  0x2d00,
  0x104a,
  0x3300,
  0x3308,
  0x1940,
  0x3504,
  0x5,
  0x11,
  0xd,
  0x19,
  0x3d,
  0x39,
  0x45,
  0x5d
]

def labelsBlock10 : Array Nat := #[
  0x61,
  0x75,
  0x71,
  0x7d,
  0x91,
  0x95,
  0xa1,
  0xa5,
  0x35,
  0x59,
  0x6d,
  0x8d,
  0x9d,
  0xa9,
  0x192c,
  0x1a2c
]

def labelsBlock11 : Array Nat := #[
  0x1b28,
  0x1c34,
  0x1d30,
  0x1c38,
  0x1e30,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9
]

def labelsBlock12 : Array Nat := #[
  0xdd,
  0x1086,
  0x108e,
  0x104e,
  0x10be,
  0x1,
  0xad,
  0xe1,
  0x1026,
  0xe5,
  0x1a40,
  0x1062,
  0xe9,
  0x3600,
  0x3500,
  0xed
]

def labelsGet (i : Nat) : Nat :=
  if i < 96 then
    if i < 48 then
      if i < 16 then
        labelsBlock0.getD (i-0) 3
      else
        if i < 32 then
          labelsBlock1.getD (i-16) 3
        else
          labelsBlock2.getD (i-32) 3
    else
      if i < 64 then
        labelsBlock3.getD (i-48) 3
      else
        if i < 80 then
          labelsBlock4.getD (i-64) 3
        else
          labelsBlock5.getD (i-80) 3
  else
    if i < 144 then
      if i < 112 then
        labelsBlock6.getD (i-96) 3
      else
        if i < 128 then
          labelsBlock7.getD (i-112) 3
        else
          labelsBlock8.getD (i-128) 3
    else
      if i < 176 then
        if i < 160 then
          labelsBlock9.getD (i-144) 3
        else
          labelsBlock10.getD (i-160) 3
      else
        if i < 192 then
          labelsBlock11.getD (i-176) 3
        else
          labelsBlock12.getD (i-192) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 8)) % 256)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (8*q)) % 256)

def viewsBlock0 : Array View := #[
  ⟨0xf00f000,⟨12,by decide⟩,0xe008000,[ew10,ew11,ew12],3,decodeHints 0xc50d07033d585903⟩,
  ⟨0x3300cc00,⟨10,by decide⟩,0x32008000,[ew22,ew23,ew24],3,decodeHints 0x0⟩,
  ⟨0x5500aa00,⟨9,by decide⟩,0x54008000,[ew25,ew26,ew27],3,decodeHints 0x0⟩,
  ⟨0x88888888,⟨3,by decide⟩,0x88808000,[ew30,ew36,ew37],3,decodeHints 0x0⟩,
  ⟨0x90909090,⟨4,by decide⟩,0x90808000,[ew30,ew40,ew41],3,decodeHints 0x0⟩,
  ⟨0x99009900,⟨8,by decide⟩,0x98008000,[ew36,ew40,ew43],3,decodeHints 0x0⟩,
  ⟨0x99990000,⟨16,by decide⟩,0x98800000,[ew37,ew41,ew43],3,decodeHints 0x0⟩,
  ⟨0xa500a500,⟨8,by decide⟩,0xa4008000,[ew33,ew46,ew48],3,decodeHints 0x0⟩,
  ⟨0xc300c300,⟨8,by decide⟩,0xc2008000,[ew31,ew54,ew56],3,decodeHints 0x0⟩,
  ⟨0xaa000000aa00,⟨9,by decide⟩,0xa80000008000,[ew71,ew74,ew77],3,decodeHints 0x0⟩,
  ⟨0x99999999,⟨0,by decide⟩,0x98808000,[ew38,ew42,ew44,ew45],6,decodeHints 0xc603000f01120e2702131130163e3127⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xaa808000,[ew38,ew47,ew51,ew52],4,decodeHints 0xc07001c012e0e2f0232114b2525252f⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xfe008000,[ew51,ew59,ew63,ew68],5,decodeHints 0xc70d070300241c0f062023201b20230f⟩,
  ⟨0xaaaa0000aaaa,⟨1,by decide⟩,0xa80000008000,[ew72,ew75,ew78,ew80],4,decodeHints 0xc807001c012e0e2f1e34371c384c562f⟩,
  ⟨0xa5a5a5a5,⟨0,by decide⟩,0xa4808000,[ew34,ew47,ew49,ew50],6,decodeHints 0x0⟩,
  ⟨0xc3c3c3c3,⟨0,by decide⟩,0xc2808000,[ew32,ew55,ew57,ew58],6,decodeHints 0x0⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew52,ew60,ew64,ew68],5,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa0000,⟨17,by decide⟩,0xa800aa800000,[ew73,ew76,ew79,ew80],5,decodeHints 0x0⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xe80000008000,[ew78,ew82,ew84,ew86],6,decodeHints 0x0⟩,
  ⟨0xaa00aa00aa00aa,⟨1,by decide⟩,0xa8000000800000,[ew89,ew91,ew93,ew95],4,decodeHints 0x0⟩,
  ⟨0xaa00aaaa00aa00,⟨9,by decide⟩,0xa80000aa008000,[ew90,ew92,ew94,ew95],5,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa0808000a000000,[ew101,ew104,ew106,ew107],4,decodeHints 0x0⟩,
  ⟨0xa0aa0a00a0aa0a0,⟨5,by decide⟩,0xa08a0000a008000,[ew102,ew105,ew106,ew109],5,decodeHints 0x0⟩,
  ⟨0xaa00aa00aa00aa0,⟨5,by decide⟩,0xaa008000a800000,[ew103,ew104,ew110,ew111],5,decodeHints 0x0⟩,
  ⟨0xf0f0f0f00000000,⟨32,by decide⟩,0xe08080000000000,[ew107,ew112,ew114,ew116],6,decodeHints 0x0⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2220200022000000,[ew119,ew122,ew124,ew125],4,decodeHints 0x0⟩,
  ⟨0x2222888822228888,⟨3,by decide⟩,0x2220880022008000,[ew120,ew123,ew124,ew127],5,decodeHints 0x0⟩,
  ⟨0x2288228822882288,⟨3,by decide⟩,0x2288200022800000,[ew121,ew122,ew128,ew129],5,decodeHints 0x0⟩,
  ⟨0x8822882288228822,⟨1,by decide⟩,0x8820880088008000,[ew140,ew146,ew147,ew148],5,decodeHints 0x0⟩,
  ⟨0x8888222288882222,⟨1,by decide⟩,0x8888200088800000,[ew142,ew144,ew150,ew151],5,decodeHints 0x0⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8888880088808000,[ew143,ew146,ew150,ew152],4,decodeHints 0x0⟩,
  ⟨0xa00aa00aa00aa00a,⟨1,by decide⟩,0xa008a000a0008000,[ew139,ew156,ew157,ew158],5,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xa0a00a0aa0a00a0a,⟨1,by decide⟩,0xa0a00800a0800000,[ew141,ew154,ew160,ew161],5,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa0a0a000a0808000,[ew143,ew156,ew160,ew162],4,decodeHints 0x0⟩,
  ⟨0xaa00aa0000aa00aa,⟨1,by decide⟩,0xaa00a80000800000,[ew145,ew155,ew165,ew167],5,decodeHints 0x0⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xaa00a800aa008000,[ew146,ew156,ew166,ew167],4,decodeHints 0x0⟩,
  ⟨0xaaaa00000000aaaa,⟨1,by decide⟩,0xaaa8000000008000,[ew149,ew159,ew164,ew169],5,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe808000,[ew53,ew61,ew65,ew69,ew70],7,decodeHints 0xc90d070300241c0f013f2e120e642f270245321311904b30252b3c2b312b3c27⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xe80000008000,[ew81,ew83,ew85,ew87,ew88],7,decodeHints 0x930d070300241c0f013f2e120e642f271e4834573768670f38664c6556929127⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0808000e000000,[ew108,ew113,ew115,ew117,ew118],7,decodeHints 0xcb1015102196ca9606202320252b3c2b1e48345738664c6541956994252b3c2b⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaaa8a800aa808000,[ew153,ew163,ew168,ew170,ew171],7,decodeHints 0xcc07001c012e0e2f0232114b2525252f1e34371c384c562f4169974b2525252f⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00e800fe008000,[ew168,ew174,ew178,ew182,ew183],7,decodeHints 0x930d070300241c0f062023201b20230f1e4834573768670f062023201b20230f⟩,
  ⟨0xff00ff00ff00ff,⟨0,by decide⟩,0xe8000000800000,[ew96,ew97,ew98,ew99,ew100],7,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3220200032000000,[ew126,ew130,ew131,ew132,ew133],7,decodeHints 0x0⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5440400054000000,[ew134,ew135,ew136,ew137,ew138],7,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xccc8c800cc808000,[ew153,ew173,ew174,ew175,ew176],7,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf0e0e000f0808000,[ew163,ew173,ew178,ew179,ew180],7,decodeHints 0x0⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfee80000fe800000,[ew170,ew175,ew179,ew182,ew185],7,decodeHints 0x0⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8e800fe808000,[ew172,ew177,ew181,ew184,ew186,ew187],10,decodeHints 0xcf0d070300241c0f013f2e120e642f270245321311904b30252b3c2b312b3c271e4834573768670f38664c65569291274195699497cecd30252b3c2b312b3c27⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      viewsBlock3[(i-48)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew10,ew11,ew12],localHints 4 0x59583d43030d071510 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew21,ew38,ew42,ew44],decodeHints 0xe0e0105121201080f0f0014161604011111020013130203⟩,
  ⟨10,4,[ew28,ew38,ew42,ew44,ew45],decodeHints 0x16160402111102042a2a18051313020929290b082626051498021f02010100000303⟩,
  ⟨10,4,[ew18,ew38,ew42,ew44,ew45],localHints 4 0x110e1309122604020b010a0500140803 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨10,3,[ew19,ew38,ew42,ew45],decodeHints 0x11110200131302030f0f0014161604010e0e010512120108⟩,
  ⟨10,4,[ew29,ew38,ew42,ew44,ew45],decodeHints 0x161604011b1b09000e0e010b22220403121201180f0f0014020299011a0105000803⟩,
  ⟨10,4,[ew20,ew38,ew42,ew44,ew45],localHints 4 0x110e1312180f04020b010a0500140803 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨10,3,[ew30,ew36,ew40,ew45],decodeHints 0x313109023e3e040201010c293030020400000c2603031726⟩,
  ⟨10,4,[ew30,ew36,ew42,ew44,ew45],decodeHints 0x1d1d0402021b02042a2a185a220204020101140a17141313020408181a08000003031708⟩,
  ⟨10,3,[ew30,ew37,ew41,ew44],decodeHints 0x31311b013e3e220102020c222727010b0f1b0c0f0f22170f⟩,
  ⟨10,4,[ew30,ew37,ew42,ew44,ew45],decodeHints 0x1d1d09011b1b095b012a010b020229010b01140a171403091f031212010b0f0f03081703⟩,
  ⟨10,4,[ew30,ew38,ew40,ew44,ew45],decodeHints 0x161604021b02090201010222020929290b5a140a0c1411110204050b1a0500000c050303⟩,
  ⟨10,4,[ew30,ew38,ew41,ew44,ew45],decodeHints 0x1616040102022a0118012222045b01290118140a0c1400041f000e0e010b00050c000f0f⟩,
  ⟨10,5,[ew30,ew38,ew42,ew44,ew45],localHints 5 0x161b6d2a6c226b09296a189b1f025d049a1a015c0b0a00170c1403 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨10,4,[ew14,ew38,ew42,ew44,ew45],localHints 4 0x160e1309290f0204180b010500081403 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨10,3,[ew15,ew38,ew44,ew45],decodeHints 0x161604011313020312120108111102000e0e01050f0f0014⟩
]

def nodesBlock1 : Array Node := #[
  ⟨10,4,[ew35,ew38,ew42,ew44,ew45],decodeHints 0x1d1d0901111102000e0e010513130203121201080f0f000a04020b019c0017001403⟩,
  ⟨10,4,[ew17,ew38,ew42,ew44,ew45],localHints 4 0x160e2204120f0a02180b0105000803 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨10,3,[ew36,ew37,ew42,ew43],decodeHints 0x31311d00131d0c1330301300121d0c122727120512131a12⟩,
  ⟨10,4,[ew36,ew37,ew42,ew44,ew45],decodeHints 0x1d1d095e1b1b09002a000005131308181a082600050003091f0312120f0f000503081a03⟩,
  ⟨10,4,[ew36,ew38,ew40,ew42,ew45],decodeHints 0x111102041d1d09020000131302092626055a08180c08161604020b05170501010c0b0303⟩,
  ⟨10,4,[ew36,ew38,ew42,ew43,ew45],decodeHints 0x1d1d11110200002a18001313025e08180c080026000a01021f01010b0c010e0e01051212⟩,
  ⟨10,5,[ew36,ew38,ew42,ew44,ew45],localHints 5 0x1d70112a6f136e09266a0a9e1f045f0218019d17005c051a0c0803 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨10,4,[ew13,ew38,ew42,ew44,ew45],localHints 4 0x16110522121826090402010b00140308 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨10,4,[ew16,ew38,ew42,ew44,ew45],localHints 4 0x161113290f0a0904020100050308 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨10,4,[ew37,ew38,ew41,ew42,ew44],decodeHints 0xe0e010b1d1d09011b1b121201180f0f005b03090c03161604010400170002020c042222⟩,
  ⟨10,4,[ew37,ew38,ew42,ew43,ew44],decodeHints 0x1d1d0e0e01051b1b09001212015e03090c030f0f000a02011a0102040c02111102001313⟩,
  ⟨10,5,[ew37,ew38,ew42,ew44,ew45],localHints 5 0x1d721b710e126e180f6b0a0902a01a0b5f019f17055d001f080c03 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨10,4,[ew6,ew38,ew42,ew44,ew45],localHints 4 0x1611042a120f02090b1801050a000803 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨10,3,[ew7,ew42,ew44,ew45],decodeHints 0x16160401111102000e0e010513130203121201080f0f0014⟩,
  ⟨10,4,[ew38,ew39,ew42,ew44,ew45],decodeHints 0x16160401111102000e0e0105090218010a0013130203121201080f0f001403a10c03⟩,
  ⟨10,4,[ew9,ew38,ew42,ew44,ew45],localHints 4 0x1d1b0e09120f14020b0105000803 0xdda4cca2bb430a109941882766545432321010⟩
]

def nodesBlock2 : Array Node := #[
  ⟨10,3,[ew38,ew40,ew41,ew43],decodeHints 0x111617110e16170e0e111a0e3e3e16033030110327270e08⟩,
  ⟨10,4,[ew38,ew40,ew41,ew44,ew45],decodeHints 0x161604601111050b1a0500041f000e0e00051a002222040329030308032605030f0f0008⟩,
  ⟨10,4,[ew38,ew40,ew42,ew43,ew45],decodeHints 0x161611110260050b170501021f01010b17010e0e1313020303290b032603031412120108⟩,
  ⟨10,5,[ew38,ew40,ew42,ew44,ew45],localHints 5 0x1674117304a31f610100130209291a0b6f2617056c14a20c035c08 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨10,4,[ew5,ew38,ew42,ew44,ew45],localHints 4 0x161b0e0b13082604090201180a000503 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨10,4,[ew8,ew38,ew42,ew44,ew45],localHints 4 0x1d112a130f1404020100050308 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨10,4,[ew38,ew41,ew42,ew43,ew44],decodeHints 0x16160e0e01600004170002011a0102041702111112120108222204030f0f001413130203⟩,
  ⟨10,5,[ew38,ew41,ew42,ew44,ew45],localHints 5 0x16750e730b02a51a61051f220471120118170f006d14a40c085d03 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨10,4,[ew3,ew38,ew42,ew44,ew45],localHints 4 0x1d110e0522291409020418010b000a03 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨10,4,[ew4,ew38,ew42,ew44,ew45],localHints 4 0x161b2a1312080204010b000314 0xcc546b654a4399618847011065654343221010⟩,
  ⟨10,5,[ew38,ew42,ew43,ew44,ew45],localHints 5 0x40b11750e7405a717611f1302721a12017008a60c5f0f03000a14 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨10,6,[ew38,ew42,ew44,ew45],localHints 5 0x16ad11ac040eab0b051f1302aa091a1201a91808170f0c0300a80a14 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨12,4,[ew36,ew51,ew59,ew63,ew68],localHints 4 0x1b0923201910151a0406000a070d 0xddc4bb943237aa493238876545432321100⟩,
  ⟨12,4,[ew51,ew59,ew62,ew63,ew68],localHints 4 0x1b09761c15061924000a10070d1a 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨12,4,[ew46,ew51,ew59,ew63,ew68],localHints 4 0x1b092320190a4d1077060007150d 0xddc4bb941221aa496872126545433212100⟩,
  ⟨12,4,[ew51,ew59,ew63,ew66,ew68],localHints 4 0x78090a231c061910000d4d030715 0x8787d8c8b5aa78011099508787645432210⟩
]

def nodesBlock3 : Array Node := #[
  ⟨12,4,[ew0,ew51,ew59,ew63,ew68],localHints 4 0x1b23091c20191006000a07150d 0xcca7bb7a994186743462126554343212100⟩,
  ⟨12,4,[ew27,ew51,ew59,ew63,ew68],decodeHints 0x78063d067606ae061c1c001520060d2424000a0303071519060a000a0015071507100d⟩,
  ⟨12,4,[ew51,ew54,ew59,ew63,ew68],localHints 4 0x1b0923150a4e7900072006190d10 0xddc3bb23a98737366554432011001100110⟩,
  ⟨12,4,[ew51,ew59,ew63,ew67,ew68],localHints 4 0x7a090a154e2006190d2400030710 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨12,4,[ew1,ew51,ew59,ew63,ew68],localHints 4 0x1b23152009241906000a070d10 0xcc85ba5434a995877400110654343221010⟩,
  ⟨12,4,[ew24,ew51,ew59,ew63,ew68],decodeHints 0x7a1943192319071c1c000ab019af19242400100303071006060a000a001507100d100d⟩,
  ⟨12,4,[ew2,ew51,ew59,ew63,ew68],localHints 4 0x1b0a2320190309060007150d10 0xcb5aa852332995801107730654432321010⟩,
  ⟨12,4,[ew12,ew51,ew59,ew63,ew68],decodeHints 0x1b0900b409b3091c1c0015b209b109242400100303071006060a0015071507100d100d⟩,
  ⟨12,5,[ew51,ew59,ew63,ew68],decodeHints 0xc000091bbf0a061b7d0a09097d000606be071923bd1506237c1519197c0706064e15001c4e070a1cbc070000bb150a15ba0d0620b91019207b1006067b0d19194d1000244d0d0a24b80d0000b7100a101a1007031a0d1503b60d0707b5101510⟩,
  ⟨37,7,[ew53,ew61,ew65,ew69,ew70],localHints 5 0x25110e0532062e2d211c5145022c193f01283a442400500a030d074f1510 0x6371d6563d657186362d8223c86b1c86a3182318669bb622bb621ad66ab580e3985b1985a3180f18659b760eb760dad65ab59851498cd498d08984c18123282df282e31811ef62dae6114e611ad62d4a38109390c939108380c010065110251106310020⟩,
  ⟨40,7,[ew153,ew163,ew168,ew170,ew171],decodeHints 0x8c0235418c541e418b5435358b021e028a011e388a53353889531e1e8901350188010625c3210225c2210606880102015200333762461e37c146333352001e00870002118705061186050202860006068505010e8500210e840001018405212152071e347f4033347e401e1e5207330783070232832d0632822d020282070606812d012e8107212e80070101802d21216240001c7f07461c7e07000062404640⟩,
  ⟨48,10,[ew172,ew177,ew181,ew184,ew186,ew187],localHints 6 0x41c454385335258f3746110e630534403332062e2d211c55488e1e368d450239193f013b3a442400420a4a03490d07471510 0x593b314af5f1c2fb2c5935d358f5ee3adb2eaad5d758fb0f48f7eb39c4eba9c7df48f4cf58a8692685e996886158a5ca48a4e72647e79644d348a7df3a43e624a72694a3cf3a471c5835e30a28636a25d75838434834e009d7e069d4d34837df39d3de08371e6833cf39d71c24129b08321b68328a2412015845d91d85591585d75845444844d41cd45414d4d348445138d3d01c43101443cf38d30c24028b1c420b14428a2402000800c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 32 then
    if i < 16 then
      nodesBlock0[(i-0)]?
    else
      nodesBlock1[(i-16)]?
  else
    if i < 48 then
      nodesBlock2[(i-32)]?
    else
      nodesBlock3[(i-48)]?

def fastViews : QFast.Table View := ⟨49,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨60,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap2 : Array Nat := #[8,0,0,9,10,0,0,11,12,0,0,13,14,0,0,15,40,0,0,41,42,0,0,43,44,0,0,45,46,0,0,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,16,19,20,23,0,0,0,0,0,0,0,0,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,8,11,12,15,0,0,0,0,0,0,0,0,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,4,7,12,15,0,0,0,0,0,0,0,0,20,23,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,3,7,11,15,0,0,0,0,0,0,0,0,19,23,27,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,1,3,5,7,9,11,13,15,0,0,0,0,0,0,0,0,49,51,53,55,57,59,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,8,9,14,15,0,0,0,0,0,0,0,0,24,25,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,8,10,13,15,0,0,0,0,0,0,0,0,24,26,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,9,11,13,15,0,0,0,0,0,0,0,0,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,10,11,14,15,0,0,0,0,0,0,0,0,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,63,0,61,0,59,0,57,0,47,0,45,0,43,0,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,0,29,0,27,0,25,0,15,0,13,0,11,0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,9,11,13,15,0,0,0,0,0,0,0,0,41,43,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,0,0,0,0,0,0,1,3,5,7,17,19,21,23,0,0,0,0,0,0,0,0,41,43,45,47,57,59,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,63,0,61,0,31,0,29,0,55,0,53,0,23,0,21,0,47,0,45,0,15,0,13,0,39,0,37,0,7,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,63,61,55,53,31,29,23,21,0,0,0,0,0,0,0,0,43,41,35,33,11,9,3,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,63,61,47,45,31,29,15,13,0,0,0,0,0,0,0,0,51,49,35,33,19,17,3,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,63,0,59,0,31,0,27,0,55,0,51,0,23,0,19,0,47,0,43,0,15,0,11,0,39,0,35,0,7,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,63,59,55,51,31,27,23,19,0,0,0,0,0,0,0,0,45,41,37,33,13,9,5,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,0,0,0,0,0,0,63,59,47,43,31,27,15,11,0,0,0,0,0,0,0,0,53,49,37,33,21,17,5,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,61,57,55,51,29,25,23,19,0,0,0,0,0,0,0,0,45,41,39,35,13,9,7,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,0,0,0,0,0,0,0,61,57,47,43,29,25,15,11,0,0,0,0,0,0,0,0,53,49,39,35,21,17,7,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,1,0,5,0,33,0,37,0,9,0,13,0,41,0,45,0,17,0,21,0,49,0,53,0,25,0,29,0,57,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,0,0,0,0,0,0,0,59,57,55,53,27,25,23,21,0,0,0,0,0,0,0,0,43,41,39,37,11,9,7,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap26 : Array Nat := #[0,0,0,0,0,0,0,0,59,57,47,45,27,25,15,13,0,0,0,0,0,0,0,0,51,49,39,37,19,17,7,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap27 : Array Nat := #[0,1,0,3,0,33,0,35,0,9,0,11,0,41,0,43,0,17,0,19,0,49,0,51,0,25,0,27,0,57,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap28 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,37,39,9,11,13,15,0,0,0,0,0,0,0,0,49,51,53,55,25,27,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,1,0,3,0,5,0,7,0,17,0,19,0,21,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,35,0,37,0,39,0,49,0,51,0,53,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,33,35,37,39,17,19,21,23,0,0,0,0,0,0,0,0,41,43,45,47,25,27,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap32 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,16,18,20,22,0,0,0,0,24,26,28,30,0,0,0,0,32,34,36,38,0,0,0,0,40,42,44,46,0,0,0,0,48,50,52,54,0,0,0,0,56,58,60,62,0,0,0,0]
def aliasMap33 : Array Nat := #[32,0,0,33,34,0,0,35,40,0,0,41,42,0,0,43,48,0,0,49,50,0,0,51,56,0,0,57,58,0,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,16,17,20,21,0,0,0,0,24,25,28,29,0,0,0,0,32,33,36,37,0,0,0,0,40,41,44,45,0,0,0,0,48,49,52,53,0,0,0,0,56,57,60,61,0,0,0,0]
def aliasMap35 : Array Nat := #[0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap36 : Array Nat := #[0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,0,0,1,6,0,0,7,8,0,0,9,14,0,0,15,16,0,0,17,22,0,0,23,24,0,0,25,30,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,0,0,2,5,0,0,7,8,0,0,10,13,0,0,15,16,0,0,18,21,0,0,23,24,0,0,26,29,0,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap12)
  | 2 => some (0, aliasMap11)
  | 3 => some (0, aliasMap6)
  | 4 => some (0, aliasMap5)
  | 5 => some (0, aliasMap4)
  | 6 => some (0, aliasMap3)
  | 7 => some (0, aliasMap10)
  | 8 => some (0, aliasMap9)
  | 9 => some (0, aliasMap14)
  | 14 => some (10, aliasMap38)
  | 15 => some (10, aliasMap37)
  | 16 => some (12, aliasMap36)
  | 17 => some (12, aliasMap30)
  | 18 => some (10, aliasMap2)
  | 19 => some (13, aliasMap29)
  | 20 => some (12, aliasMap28)
  | 21 => some (11, aliasMap27)
  | 22 => some (12, aliasMap26)
  | 23 => some (12, aliasMap25)
  | 24 => some (10, aliasMap33)
  | 25 => some (11, aliasMap24)
  | 26 => some (12, aliasMap23)
  | 27 => some (12, aliasMap22)
  | 28 => some (12, aliasMap21)
  | 29 => some (12, aliasMap20)
  | 30 => some (11, aliasMap19)
  | 31 => some (12, aliasMap18)
  | 32 => some (12, aliasMap17)
  | 33 => some (11, aliasMap16)
  | 34 => some (12, aliasMap15)
  | 35 => some (13, aliasMap13)
  | 36 => some (12, aliasMap8)
  | 42 => some (38, aliasMap35)
  | 43 => some (39, aliasMap34)
  | 44 => some (39, aliasMap32)
  | 45 => some (40, aliasMap31)
  | 46 => some (40, aliasMap7)
  | 47 => some (41, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_8 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 8 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_24 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 24 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_40 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 40 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 1 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 8 8 blockRoots_0 blockRoots_8

theorem joinRoots_0_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 8 8 blockRoots_16 blockRoots_24

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 8 8 blockRoots_32 blockRoots_40

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 joinRoots_0_0 joinRoots_0_16

theorem joinRoots_1_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 17 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 1 joinRoots_0_32 blockRoots_48

theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 49 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 17 joinRoots_1_0 joinRoots_1_32

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 49 = true := joinRoots_2_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_6 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 6 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_18 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 18 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_30 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 30 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_42 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 42 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_54 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 54 6 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 6 6 blockNodes_0 blockNodes_6

theorem joinNodes_0_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 12 6 6 blockNodes_12 blockNodes_18

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 6 6 blockNodes_24 blockNodes_30

theorem joinNodes_0_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 36 6 6 blockNodes_36 blockNodes_42

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 6 6 blockNodes_48 blockNodes_54

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 joinNodes_0_0 joinNodes_0_12

theorem joinNodes_1_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 joinNodes_0_24 joinNodes_0_36

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_1_0 joinNodes_1_24

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 60 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 12 joinNodes_2_0 joinNodes_0_48

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 60 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfee8e800fe808000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfee8e800fe808000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 48) = true := by decide +kernel
  cases ev : QFast.get fastViews 48 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12110_aux

open PEqualNP.Outside.L_meta_12110_aux in
theorem PEqualNP.Outside.L_meta_12110 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
