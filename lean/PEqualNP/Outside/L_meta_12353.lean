import PEqualNP.Defs

-- The witness has ten binary gates. Any circuit with a NOT and fewer gates
-- would have at most eight binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12353_aux
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


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or,[0,1]⟩,⟨.or,[6,2]⟩,⟨.or,[3,4]⟩,
  ⟨.and,[7,8]⟩,⟨.and,[0,1]⟩,⟨.and,[10,2]⟩,⟨.and,[3,4]⟩,⟨.or,[11,12]⟩,
  ⟨.or,[13,5]⟩,⟨.and,[9,14]⟩],15⟩

theorem size : witness.size = 10 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfefefe00fe808000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfefefe00fe808000 : W) 8 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 8 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfefefe00fe808000 : BitVec 64) 8 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew3 : Word := 0xaa0000

def ew4 : Word := 0xcc0000

def ew5 : Word := 0xf00000

def ew6 : Word := 0xa00a000

def ew7 : Word := 0xaa00000

def ew8 : Word := 0xc00c000

def ew9 : Word := 0xcc00000

def ew10 : Word := 0xf000000

def ew11 : Word := 0x22008800

def ew12 : Word := 0x22880000

def ew13 : Word := 0x2a2a2a2a

def ew14 : Word := 0x3000c000

def ew15 : Word := 0x30c00000

def ew16 : Word := 0x33000000

def ew17 : Word := 0x44008800

def ew18 : Word := 0x44880000

def ew19 : Word := 0x4c4c4c4c

def ew20 : Word := 0x5000a000

def ew21 : Word := 0x50a00000

def ew22 : Word := 0x55000000

def ew23 : Word := 0x70707070

def ew24 : Word := 0x80808080

def ew25 : Word := 0x82008200

def ew26 : Word := 0x82820000

def ew27 : Word := 0x82828282

def ew28 : Word := 0x84008400

def ew29 : Word := 0x84840000

def ew30 : Word := 0x84848484

def ew31 : Word := 0x88008800

def ew32 : Word := 0x88880000

def ew33 : Word := 0x88888888

def ew34 : Word := 0x90009000

def ew35 : Word := 0x90900000

def ew36 : Word := 0x90909090

def ew37 : Word := 0x99000000

def ew38 : Word := 0x99009900

def ew39 : Word := 0x99990000

def ew40 : Word := 0xa000a000

def ew41 : Word := 0xa0a00000

def ew42 : Word := 0xa0a0a0a0

def ew43 : Word := 0xa5000000

def ew44 : Word := 0xa500a500

def ew45 : Word := 0xa5a50000

def ew46 : Word := 0xaa00aa00

def ew47 : Word := 0xaaaa0000

def ew48 : Word := 0xaaaaaaaa

def ew49 : Word := 0xc000c000

def ew50 : Word := 0xc0c00000

def ew51 : Word := 0xc0c0c0c0

def ew52 : Word := 0xc3000000

def ew53 : Word := 0xc300c300

def ew54 : Word := 0xc3c30000

def ew55 : Word := 0xcc00cc00

def ew56 : Word := 0xcccc0000

def ew57 : Word := 0xcccccccc

def ew58 : Word := 0xee00ee00

def ew59 : Word := 0xeeee0000

def ew60 : Word := 0xf000f000

def ew61 : Word := 0xf0f00000

def ew62 : Word := 0xf0f0f0f0

def ew63 : Word := 0xfa00fa00

def ew64 : Word := 0xfafa0000

def ew65 : Word := 0xfc00fc00

def ew66 : Word := 0xfcfc0000

def ew67 : Word := 0xff000000

def ew68 : Word := 0xff00ff00

def ew69 : Word := 0xffff0000

def ew70 : Word := 0xaaaaaaaaaaaaaaaa

def ew71 : Word := 0xcccccccccccccccc

def ew72 : Word := 0xf0f0f0f0f0f0f0f0

def ew73 : Word := 0xff00ff00ff00ff00

def ew74 : Word := 0xffff0000ffff0000

def ew75 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x1960,
  0xf1c,
  0x171c,
  0x1a60,
  0x1924,
  0x1944,
  0xf2c,
  0x1c60,
  0xf34,
  0xf38,
  0x174c,
  0x1754,
  0x1758,
  0x1a28,
  0x1a48,
  0xf28
]

def labelsBlock1 : Array Nat := #[
  0xf24,
  0xf30,
  0x1748,
  0x1744,
  0x1750,
  0x1c30,
  0x1c50,
  0x1904,
  0x1920,
  0x1940,
  0xf20,
  0x1a20,
  0x1a40,
  0x1c20,
  0x1c40,
  0x104a
]

def labelsBlock2 : Array Nat := #[
  0x105e,
  0x1b2c,
  0x1062,
  0xf0c,
  0x1b4c,
  0x170c,
  0xf14,
  0xf18,
  0x1714,
  0x1718,
  0x104e,
  0x1740,
  0x1d34,
  0x1e38,
  0x1022,
  0x1b60
]

def labelsBlock3 : Array Nat := #[
  0x1d54,
  0x1e58,
  0x101e,
  0x101a,
  0xf00,
  0xf04,
  0xf08,
  0x1056,
  0x1d60,
  0x1e60,
  0x1900,
  0x1704,
  0x1708,
  0x1a08,
  0xf10,
  0x1710
]

def labelsBlock4 : Array Nat := #[
  0x1026,
  0x102a,
  0x1032,
  0x1036,
  0x103e,
  0x1042,
  0x1934,
  0x1954,
  0x192c,
  0x194c,
  0x1a2c,
  0x1a4c,
  0x1a00,
  0x1a38,
  0x1a58,
  0x1c38
]

def labelsBlock5 : Array Nat := #[
  0x1c58,
  0x1c34,
  0x1c54,
  0x1b0c,
  0x41005e,
  0x410062,
  0x42005e,
  0x420062,
  0x42105e,
  0x421062,
  0x1700,
  0x102e,
  0x103a,
  0x1046,
  0x1052,
  0x1c00
]

def labelsBlock6 : Array Nat := #[
  0x1930,
  0x1a30,
  0x1950,
  0x1a50,
  0x1928,
  0x1c28,
  0x1948,
  0x1c48,
  0x1a24,
  0x1c24,
  0x1a44,
  0x1c44,
  0x1c10,
  0x1b20,
  0x1b40,
  0x1d14
]

def labelsBlock7 : Array Nat := #[
  0x1d20,
  0x1d40,
  0x1e18,
  0x1e20,
  0x1e40,
  0x41004a,
  0x410056,
  0xbd,
  0x3100,
  0x2900,
  0x2920,
  0x1b24,
  0x1d24,
  0x1e28,
  0x1012,
  0x100a
]

def labelsBlock8 : Array Nat := #[
  0x1002,
  0x1b44,
  0x1d44,
  0x1e48,
  0x1016,
  0x100e,
  0x1006,
  0x40104e,
  0x105a,
  0x410052,
  0x3200,
  0x2a00,
  0x2a20,
  0x1b28,
  0x1d30,
  0x1e30
]

def labelsBlock9 : Array Nat := #[
  0x55,
  0x59,
  0x5d,
  0x61,
  0x65,
  0x69,
  0x6d,
  0x71,
  0x75,
  0x79,
  0x7d,
  0x81,
  0x1b48,
  0x1d50,
  0x1e50,
  0x89
]

def labelsBlock10 : Array Nat := #[
  0x8d,
  0x91,
  0x95,
  0x99,
  0x9d,
  0xa1,
  0xa5,
  0xa9,
  0xad,
  0xb1,
  0xb5,
  0x71004a,
  0xc1,
  0x70104e,
  0xc9,
  0x41005a
]

def labelsBlock11 : Array Nat := #[
  0x610056,
  0xd1,
  0x41004e,
  0xc5,
  0xcd,
  0xd5,
  0x1,
  0x5,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25
]

def labelsBlock12 : Array Nat := #[
  0x29,
  0x2d,
  0x31,
  0x35,
  0x39,
  0x3d,
  0x41,
  0x45,
  0x1b00,
  0x49,
  0x1d00,
  0x4d,
  0x1e00,
  0x51,
  0x85,
  0xb9
]

def labelsBlock13 : Array Nat := #[
  0xd9,
  0x3400,
  0x3104,
  0x2c00,
  0x2904,
  0x2c20,
  0x2924,
  0x1066
]

def labelsGet (i : Nat) : Nat :=
  if i < 112 then
    if i < 48 then
      if i < 16 then
        labelsBlock0.getD (i-0) 3
      else
        if i < 32 then
          labelsBlock1.getD (i-16) 3
        else
          labelsBlock2.getD (i-32) 3
    else
      if i < 80 then
        if i < 64 then
          labelsBlock3.getD (i-48) 3
        else
          labelsBlock4.getD (i-64) 3
      else
        if i < 96 then
          labelsBlock5.getD (i-80) 3
        else
          labelsBlock6.getD (i-96) 3
  else
    if i < 160 then
      if i < 128 then
        labelsBlock7.getD (i-112) 3
      else
        if i < 144 then
          labelsBlock8.getD (i-128) 3
        else
          labelsBlock9.getD (i-144) 3
    else
      if i < 192 then
        if i < 176 then
          labelsBlock10.getD (i-160) 3
        else
          labelsBlock11.getD (i-176) 3
      else
        if i < 208 then
          labelsBlock12.getD (i-192) 3
        else
          labelsBlock13.getD (i-208) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 8)) % 256)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (8*q)) % 256)

def viewsBlock0 : Array View := #[
  ⟨0xf00f000,⟨12,by decide⟩,0xe008000,[ew6,ew8,ew10],3,decodeHints 0xb609081146606111⟩,
  ⟨0xff00000,⟨20,by decide⟩,0xe800000,[ew7,ew9,ew10],3,decodeHints 0xb70c0b1447626314⟩,
  ⟨0x3300cc00,⟨10,by decide⟩,0x32008000,[ew11,ew14,ew16],3,decodeHints 0xb809060f4864650f⟩,
  ⟨0x33cc0000,⟨18,by decide⟩,0x32800000,[ew12,ew15,ew16],3,decodeHints 0xb90c0a1249666712⟩,
  ⟨0x5500aa00,⟨9,by decide⟩,0x54008000,[ew17,ew20,ew22],3,decodeHints 0xba0806104a686910⟩,
  ⟨0x55aa0000,⟨17,by decide⟩,0x54800000,[ew18,ew21,ew22],3,decodeHints 0xbb0b0a134b6a6b13⟩,
  ⟨0x82828282,⟨1,by decide⟩,0x82808000,[ew24,ew25,ew26],3,decodeHints 0xbc100135023b1735⟩,
  ⟨0x84848484,⟨2,by decide⟩,0x84808000,[ew24,ew28,ew29],3,decodeHints 0xbd0f0136023c3d36⟩,
  ⟨0x88888888,⟨3,by decide⟩,0x88808000,[ew24,ew31,ew32],3,decodeHints 0xbe06012302255323⟩,
  ⟨0x90909090,⟨4,by decide⟩,0x90808000,[ew24,ew34,ew35],3,decodeHints 0xbf11013e023f6c3e⟩,
  ⟨0x99009900,⟨8,by decide⟩,0x98008000,[ew31,ew34,ew37],3,decodeHints 0xc011061a216d1d1a⟩,
  ⟨0x99990000,⟨16,by decide⟩,0x98800000,[ew32,ew35,ew37],3,decodeHints 0xc1140a2b246e1e2b⟩,
  ⟨0xa0a0a0a0,⟨5,by decide⟩,0xa0808000,[ew24,ew40,ew41],3,decodeHints 0xc208012602286f26⟩,
  ⟨0xa500a500,⟨8,by decide⟩,0xa4008000,[ew28,ew40,ew43],3,decodeHints 0xc3080f1a0d1b701a⟩,
  ⟨0xa5a50000,⟨16,by decide⟩,0xa4800000,[ew29,ew41,ew43],3,decodeHints 0xc40b122b0e1c712b⟩,
  ⟨0xc0c0c0c0,⟨6,by decide⟩,0xc0808000,[ew24,ew49,ew50],3,decodeHints 0xc509012702297227⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xc300c300,⟨8,by decide⟩,0xc2008000,[ew25,ew49,ew52],3,decodeHints 0xc609101a0418731a⟩,
  ⟨0xc3c30000,⟨16,by decide⟩,0xc2800000,[ew26,ew50,ew52],3,decodeHints 0xc70c132b0519742b⟩,
  ⟨0x99999999,⟨0,by decide⟩,0x98808000,[ew33,ew36,ew38,ew39],5,decodeHints 0xc911061a013e2334023f255a53c85f34⟩,
  ⟨0xa5a5a5a5,⟨0,by decide⟩,0xa4808000,[ew30,ew42,ew44,ew45],5,decodeHints 0xcb080f1a0126363402283c5a3d4cca34⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xaa808000,[ew33,ew42,ew46,ew47],4,decodeHints 0x2e080610012623350228253b17171735⟩,
  ⟨0xc3c3c3c3,⟨0,by decide⟩,0xc2808000,[ew27,ew51,ew53,ew54],5,decodeHints 0xcd09101a0127353402293b5a173acc34⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xcc808000,[ew33,ew51,ew55,ew56],4,decodeHints 0x2e09060f012723360229253c3d3d3d36⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xfe008000,[ew46,ew55,ew60,ew67],5,decodeHints 0xce090811060f101a04181b181d181b1a⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew47,ew56,ew61,ew67],5,decodeHints 0xcf0c0b140a12132b05191c191e191c2b⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe808000,[ew48,ew57,ew62,ew68,ew69],7,decodeHints 0xd0090811060f101a0127263e233635340229283f253c3b5a173a4c3a5f3a4c34⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfefefe00fe808000,[ew70,ew71,ew72,ew73,ew74,ew75],8,decodeHints 0xd7090811060f101a0127263e233635340229283f253c3b5a173a4c3a5f3a4c34d67a8c7ad57a8c1ad4798b79d3798b34d2788a78d1788a5a173a4c3a5f3a4c34⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 16 then
    viewsBlock0[(i-0)]?
  else
    viewsBlock1[(i-16)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew6,ew8,ew10],localHints 4 0x6160464d1109080300 0x258168155262367057066353024314322010⟩,
  ⟨1,3,[ew7,ew9,ew10],localHints 4 0x6362474e140c0b0300 0x258168155262367057066353024314322010⟩,
  ⟨2,3,[ew11,ew14,ew16],localHints 4 0x6564484f0f09060700 0x258168155262367057066353024314322010⟩,
  ⟨3,3,[ew12,ew15,ew16],localHints 4 0x67664950120c0a0700 0x258168155262367057066353024314322010⟩,
  ⟨4,3,[ew17,ew20,ew22],localHints 4 0x69684a511008060703 0x258168155262367057066353024314322010⟩,
  ⟨5,3,[ew18,ew21,ew22],localHints 4 0x6b6a4b52130b0a0703 0x258168155262367057066353024314322010⟩,
  ⟨6,3,[ew24,ew25,ew26],localHints 4 0x173b02043510010513 0x258168155262367057066353024314322010⟩,
  ⟨7,3,[ew24,ew28,ew29],localHints 4 0x3d3c020d360f010e12 0x258168155262367057066353024314322010⟩,
  ⟨8,3,[ew24,ew31,ew32],localHints 4 0x53250221230601240a 0x258168155262367057066353024314322010⟩,
  ⟨9,3,[ew24,ew34,ew35],localHints 4 0x6c3f02153e11011614 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew31,ew34,ew37],localHints 4 0x1d6d21151a1106072f 0x258168155262367057066353024314322010⟩,
  ⟨11,3,[ew32,ew35,ew37],localHints 4 0x1e6e24162b140a072f 0x258168155262367057066353024314322010⟩,
  ⟨12,3,[ew24,ew40,ew41],localHints 4 0x6f28022c260801300b 0x258168155262367057066353024314322010⟩,
  ⟨13,3,[ew28,ew40,ew43],localHints 4 0x701b0d2c1a080f3803 0x258168155262367057066353024314322010⟩,
  ⟨14,3,[ew29,ew41,ew43],localHints 4 0x711c0e302b0b123803 0x258168155262367057066353024314322010⟩,
  ⟨15,3,[ew24,ew49,ew50],localHints 4 0x7229022d270901310c 0x258168155262367057066353024314322010⟩
]

def nodesBlock1 : Array Node := #[
  ⟨16,3,[ew25,ew49,ew52],localHints 4 0x7318042d1a09103900 0x258168155262367057066353024314322010⟩,
  ⟨17,3,[ew26,ew50,ew52],localHints 4 0x741905312b0c133900 0x258168155262367057066353024314322010⟩,
  ⟨18,5,[ew33,ew36,ew38,ew39],localHints 5 0x534125212340240a3f02153e0116141a11062e072f 0x9a2349b9749ba319a16878d727b6327b56b78e237b51078dd078d087b5cd1116c1194c1196b1114411909110e911108118e610065110251106310020⟩,
  ⟨19,5,[ew30,ew42,ew44,ew45],localHints 5 0x3d433c0d36420e1228022c2601300b1a080f323803 0x9a2349b9749ba319a16878d727b6327b56b78e237b51078dd078d087b5cd1116c1194c1196b1114411909110e911108118e610065110251106310020⟩,
  ⟨21,5,[ew27,ew51,ew53,ew54],localHints 5 0x17453b043544051329022d2701310c1a0910333900 0x9a2349b9749ba319a16878d727b6327b56b78e237b51078dd078d087b5cd1116c1194c1196b1114411909110e911108118e610065110251106310020⟩,
  ⟨23,4,[ew31,ew46,ew55,ew60,ew67],localHints 4 0x1d151b180d000341210406070809 0xddc4bb943237aa493238876545432321100⟩,
  ⟨23,4,[ew46,ew55,ew58,ew60,ew67],localHints 4 0x1d157b1003040d0f060700080941 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨23,4,[ew40,ew46,ew55,ew60,ew67],localHints 4 0x1d151b180d0743002c0406080309 0xddc4bb941221aa496872126545433212100⟩,
  ⟨23,4,[ew46,ew55,ew60,ew63,ew67],localHints 4 0x7c15071b10040d00060943110803 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨23,4,[ew0,ew46,ew55,ew60,ew67],localHints 4 0x1d1b1510180d00040607080309 0xcca7bb7a994186743462126554343212100⟩,
  ⟨23,4,[ew22,ew46,ew55,ew60,ew67],decodeHints 0x7c0446047b044804101006031804090f0f0607111108030d0407060706030803080009⟩,
  ⟨23,4,[ew46,ew49,ew55,ew60,ew67],localHints 4 0x1d151b0307452d060818040d0900 0xddc3bb23a98737366554432011001100110⟩,
  ⟨23,4,[ew46,ew55,ew60,ew65,ew67],localHints 4 0x7d1507034518040d090f06110800 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨23,4,[ew1,ew46,ew55,ew60,ew67],localHints 4 0x1d1b0318150f0d040607080900 0xcc85ba5434a995877400110654343221010⟩,
  ⟨23,4,[ew16,ew46,ew55,ew60,ew67],decodeHints 0x7d0d4d0d1b0d08101006078d0d4a0d0f0f060011110800040407060706030800090009⟩,
  ⟨23,4,[ew2,ew46,ew55,ew60,ew67],localHints 4 0x1d071b180d1115040608030900 0xcb5aa852332995801107730654432321010⟩
]

def nodesBlock2 : Array Node := #[
  ⟨23,4,[ew10,ew46,ew55,ew60,ew67],decodeHints 0x1d15068f154f15101006038e1551150f0f060011110800040407060308030800090009⟩,
  ⟨23,5,[ew46,ew55,ew60,ew67],decodeHints 0x9b06151d9a07041d800715158006040499080d1b9803041b7f030d0d7f080404450306104508071097080606960307039509041894000d187e0004047e090d0d4300060f4309070f930906069200070041000811410903119109080890000300⟩,
  ⟨24,4,[ew32,ew47,ew56,ew61,ew67],localHints 4 0x1e161c190e00035b24050a070b0c 0xddc4bb943237aa493238876545432321100⟩,
  ⟨24,4,[ew47,ew56,ew59,ew61,ew67],localHints 4 0x1e16811303050e120a07000b0c5b 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨24,4,[ew41,ew47,ew56,ew61,ew67],localHints 4 0x1e161c190e075c0030050a0b030c 0xddc4bb941221aa496872126545433212100⟩,
  ⟨24,4,[ew47,ew56,ew61,ew64,ew67],localHints 4 0x8216071c13050e000a0c5c140b03 0x8787d8c8b5aa78011099508787645432210⟩,
  ⟨24,4,[ew3,ew47,ew56,ew61,ew67],localHints 4 0x1e1c1613190e00050a070b030c 0xcca7bb7a994186743462126554343212100⟩,
  ⟨24,4,[ew22,ew47,ew56,ew61,ew67],decodeHints 0x820547058105490513130a0319050c12120a0714140b030e05070a070a030b030b000c⟩,
  ⟨24,4,[ew47,ew50,ew56,ew61,ew67],localHints 4 0x1e161c03075d310a0b19050e0c00 0xddc3bb23a98737366554432011001100110⟩,
  ⟨24,4,[ew47,ew56,ew61,ew66,ew67],localHints 4 0x831607035d19050e0c120a140b00 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨24,4,[ew4,ew47,ew56,ew61,ew67],localHints 4 0x1e1c031916120e050a070b0c00 0xcc85ba5434a995877400110654343221010⟩,
  ⟨24,4,[ew16,ew47,ew56,ew61,ew67],decodeHints 0x830e4e0e1c0e0b13130a079c0e4b0e12120a0014140b000505070a070a030b000c000c⟩,
  ⟨24,4,[ew5,ew47,ew56,ew61,ew67],localHints 4 0x1e071c190e1416050a0b030c00 0xcb5aa852332995801107730654432321010⟩,
  ⟨24,4,[ew10,ew47,ew56,ew61,ew67],decodeHints 0x1e160a9e16501613130a039d16521612120a0014140b000505070a030b030b000c000c⟩,
  ⟨24,5,[ew47,ew56,ew61,ew67],decodeHints 0xaa0a161ea907051e86071616860a0505a80b0e1ca703051c85030e0e850b05055d030a135d0b0713a60b0a0aa5030703a40c0519a3000e1984000505840c0e0e5c000a125c0c0712a20c0a0aa10007005b000b145b0c0314a00c0b0b9f000300⟩,
  ⟨25,5,[ew24,ew48,ew57,ew62,ew68,ew69],decodeHints 0x17170401021d0204011e0105021b0204011c0105030776030218020d0119010e00078700000375000204020401050105060608080909⟩
]

def nodesBlock3 : Array Node := #[
  ⟨25,5,[ew23,ew48,ew57,ew62,ew68,ew69],decodeHints 0x171704012525020423230105021b0204011c0105101006030218020d0119010e0f0f06000003ab00150215021601160107061f0308081f000909⟩,
  ⟨25,6,[ew33,ew48,ew57,ew62,ew68,ew69],localHints 5 0x1725230a1b1c7688180d190e875e2202550420015405ac2a06770703081f0009 0xc77d50fa9ce6418787b8ef72103b9dc674eae9d8ce294f8408ed92107b9cb6308ad118c5a94439f252e0e72148f84036b86107dacb63034a858c5d28139e652c8e70942110444208427c21173a3083dce5b18d529ac62d4a49ce829507398a51086220c4200820⟩,
  ⟨25,5,[ew19,ew48,ew57,ew62,ew68,ew69],decodeHints 0x17170401021d0204011e01052828020426260105101008070218020d0119010e0007ad00111108000d020d020e010e011f07060603082a000909⟩,
  ⟨25,6,[ew42,ew48,ew57,ew62,ew68,ew69],localHints 5 0x171d1e28260b76af180d190e755e22025704200156050706ae0877032a1f0009 0xc77d50fa9ce6418f8412ef26107b9cb6312aea58c5a9468734ee6a10339da66ccad998cd2944c90c931b062248f84036b86107dacb63034a858c5d2811846948c63098d321246304817c21173a3083dce5b18d529ac62d4a18d024a0e630884118c52106300820⟩,
  ⟨25,5,[ew13,ew48,ew57,ew62,ew68,ew69],decodeHints 0x17170401021d0204011e0105021b0204011c01050307b0032929020d2727010e0f0f09071111090304020402050105011f0706062a0308080009⟩,
  ⟨25,6,[ew48,ew51,ew57,ew62,ew68,ew69],localHints 5 0x171d1e1b1c22590420580506370829020d27010c0eb207758903b11f097700 0xcbfa8ff52f763d987bd17ea1efc5ef563114e218cad2987bcb7d95efc5ef5630b4d158cad2859164844a52c3df9bdf2f7e2f7ab196a52cc6569494a6344e5288cb113e0b7416f789ce5b1a25344c62d4a02402408461010001c0228846100a000c022084310020⟩,
  ⟨25,7,[ew48,ew57,ew62,ew68,ew69],localHints 6 0x1725230a2804260b05371088b52902220d2701200c0e2a0f06b4071f115e0908b30300 0x3d07623da5223da75d3d05104ca5214df7614df5144ca75d3df4203ca6a03ca4103df69a4c351e4db75e4db5144c375d3db41c3c369c3c34103db69a6412986432185c328a5812014c45154ce4954ce5144c44923ce4113c43513c44103ce34d30028b30420b14428a2402001c00c61c40461440c3080040⟩
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

def fastViews : QFast.Table View := ⟨27,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨55,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_8 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 8 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_24 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 24 3 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 8 8 blockRoots_0 blockRoots_8

theorem joinRoots_0_16 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 16 11 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 16 8 3 blockRoots_16 blockRoots_24

theorem joinRoots_1_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 27 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 16 11 joinRoots_0_0 joinRoots_0_16

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 27 = true := joinRoots_1_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_5 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 5 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_10 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 10 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_15 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 15 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_20 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 20 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_25 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 25 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_30 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 30 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_35 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 35 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_40 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 40 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_45 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 45 5 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_50 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 50 5 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 10 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 5 5 blockNodes_0 blockNodes_5

theorem joinNodes_0_10 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 10 10 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 10 5 5 blockNodes_10 blockNodes_15

theorem joinNodes_0_20 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 20 10 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 20 5 5 blockNodes_20 blockNodes_25

theorem joinNodes_0_30 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 30 10 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 30 5 5 blockNodes_30 blockNodes_35

theorem joinNodes_0_40 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 40 10 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 40 5 5 blockNodes_40 blockNodes_45

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 20 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 10 10 joinNodes_0_0 joinNodes_0_10

theorem joinNodes_1_20 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 20 20 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 20 10 10 joinNodes_0_20 joinNodes_0_30

theorem joinNodes_1_40 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 40 15 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 40 10 5 joinNodes_0_40 blockNodes_50

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 40 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 20 20 joinNodes_1_0 joinNodes_1_20

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 55 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 40 15 joinNodes_2_0 joinNodes_1_40

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 55 = true := joinNodes_3_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfefefe00fe808000 : Word) && vk v == 8 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfefefe00fe808000 : BitVec 64) 8 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 26) = true := by decide +kernel
  cases ev : QFast.get fastViews 26 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12353_aux

open PEqualNP.Outside.L_meta_12353_aux in
theorem PEqualNP.Outside.L_meta_12353 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
