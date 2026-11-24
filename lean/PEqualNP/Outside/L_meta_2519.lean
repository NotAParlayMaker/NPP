import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2519

inductive Plan {α : Type} [DecidableEq α] (zero target : α)
    (combine : Bool → Bool → α → α → α) : ℕ → Finset α → Prop
  | done : Plan zero target combine 0 {target}
  | gate {k : ℕ} {rest : Finset α} {a b : α} (p q : Bool)
      (ha : a ≠ zero) (hb : b ≠ zero) (hab : a ≠ b)
      (allowed : p = q ∨ k < 5)
      (fresh : combine p q a b ∉ insert a (insert b rest))
      (tail : Plan zero target combine k (insert (combine p q a b) rest)) :
      Plan zero target combine (k + 1) (insert a (insert b rest))

lemma Plan.proper {α : Type} [DecidableEq α] {z t : α} {op} {k S}
    (h : Plan z t op k S) (ht : t ≠ z) : z ∉ S := by
  induction h with
  | done => simpa [eq_comm] using ht
  | gate _ _ ha hb _ _ _ _ ih =>
    exact fun hz => (Finset.mem_insert.mp hz).elim (Ne.symm ha)
      (fun hu => (Finset.mem_insert.mp hu).elim (Ne.symm hb)
        (fun hr => ih (Finset.mem_insert_of_mem hr)))

-- Each new signal is either available without a gate or obtained from two distinct signals.
def Available {α : Type} [DecidableEq α] (zero : α) (op : Bool → Bool → α → α → α)
    (S : Finset α) (k : Nat) (c : α) : Prop :=
  c = zero ∨ c ∈ S ∨ ∃ p q a b, a ∈ S ∧ b ∈ S ∧
    a ≠ zero ∧ b ≠ zero ∧ a ≠ b ∧ (p = q ∨ k < 5) ∧ c = op p q a b

lemma Plan.pull {α : Type} [DecidableEq α] {z t : α} {op} {k S T c}
    (h : Plan z t op k T) (ht : t ≠ z) (hsub : T ⊆ insert c S)
    (avail : Available z op S k c) :
    ∃ r ≤ k + 1, ∃ U ⊆ S, Plan z t op r U := by
  by_cases same : T ⊆ S
  · exact ⟨k, by omega, T, same, h⟩
  have hc : c ∈ T ∧ c ∉ S := by
    by_contra! bad
    apply same
    intro w hw
    rcases Finset.mem_insert.mp (hsub hw) with rfl | hmem
    · exact bad hw
    · exact hmem
  have proper := h.proper ht
  rcases avail with rfl | hm | ⟨p,q,a,b,ha,hb,haz,hbz,hab,allow,rfl⟩
  · exact (proper hc.1).elim
  · exact (hc.2 hm).elim
  · let R := T.erase (op p q a b)
    have hR : R ⊆ S := by
      intro w hw
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hw
      exact (Finset.mem_insert.mp (hsub hm)).resolve_left hne
    have hin : insert a (insert b R) ⊆ S :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hb, hR⟩⟩
    have hf : op p q a b ∉ insert a (insert b R) := fun hm => hc.2 (hin hm)
    have ht' : Plan z t op k (insert (op p q a b) R) := by rwa [Finset.insert_erase hc.1]
    exact ⟨k+1, le_rfl, _, hin, .gate p q haz hbz hab allow hf ht'⟩

lemma Plan.pull_free {α : Type} [DecidableEq α] {z t : α} {op} {k S T c}
    (h : Plan z t op k T) (ht : t ≠ z) (hsub : T ⊆ insert c S)
    (avail : c = z ∨ c ∈ S) : T ⊆ S := by
  intro w hw
  rcases Finset.mem_insert.mp (hsub hw) with rfl | hm
  · exact avail.elim (fun e => (h.proper ht (e ▸ hw)).elim) id
  · exact hm

lemma Plan.card_le {α : Type} [DecidableEq α] {z t : α} {op} {k S}
    (h : Plan z t op k S) : S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @gate k rest a b p q _ _ _ _ hf _ ih =>
    rw [Finset.card_insert_of_notMem (fun h => hf (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem h)))] at ih
    have ha := Finset.card_insert_le a (insert b rest)
    have hb := Finset.card_insert_le b rest
    omega

def zeroWire {α : Type} : α → Bool := fun _ => false

def phase {α : Type} (p : Bool) (a : α → Bool) : α → Bool :=
  fun x => xor p (a x)

def normalize {α : Type} (d : α) (a : α → Bool) : α → Bool := phase (a d) a

def joinWires {α : Type} (d : α) (p q : Bool) (a b : α → Bool) : α → Bool :=
  normalize d (fun x => phase p a x && phase q b x)

lemma normalize_phase {α : Type} (d : α) (p : Bool) (a : α → Bool) :
    normalize d (phase p a) = normalize d a := by
  funext x
  unfold normalize phase
  cases p <;> cases h : a d <;> cases hx : a x <;> rfl

lemma normalize_at {α : Type} (d : α) (a : α → Bool) : normalize d a d = false := by
  unfold normalize phase
  cases a d <;> rfl

lemma normalize_fixed {α : Type} {d : α} {a : α → Bool} (h : a d = false) :
    normalize d a = a := by
  funext x
  simp [normalize, phase, h]

lemma phase_normalize {α : Type} (d : α) (a : α → Bool) :
    phase (a d) (normalize d a) = a := by
  funext x
  unfold normalize phase
  cases a d <;> cases a x <;> rfl

lemma normalize_const {α : Type} (d : α) (b : Bool) :
    normalize d (fun _ => b) = zeroWire := by
  funext x
  cases b <;> rfl

lemma join_left_zero {α : Type} (d : α) (p q : Bool) (a : α → Bool) (ha : a d = false) :
    joinWires d p q zeroWire a = zeroWire ∨ joinWires d p q zeroWire a = a := by
  cases p
  · left
    simpa [joinWires, phase, zeroWire] using normalize_const d false
  · right
    change normalize d (phase q a) = a
    exact (normalize_phase d q a).trans (normalize_fixed ha)

lemma join_swap {α : Type} (d : α) (p q : Bool) (a b : α → Bool) :
    joinWires d p q a b = joinWires d q p b a := by
  unfold joinWires
  congr 1
  funext x
  exact Bool.and_comm _ _

lemma join_self {α : Type} (d : α) (p q : Bool) (a : α → Bool) (ha : a d = false) :
    joinWires d p q a a = zeroWire ∨ joinWires d p q a a = a := by
  cases p <;> cases q
  · right
    simpa [joinWires, phase] using normalize_fixed ha
  · left
    simpa [joinWires, phase] using normalize_const d false
  · left
    simpa [joinWires, phase] using normalize_const d false
  · right
    have he : (fun x => phase true a x && phase true a x) = phase true a := by
      funext x; simp
    unfold joinWires
    rw [he, normalize_phase, normalize_fixed ha]

lemma join_available {α : Type} [DecidableEq (α → Bool)] (d : α) (p q : Bool)
    (a b : α → Bool) (S : Finset (α → Bool)) (ha : a ∈ S) (hb : b ∈ S)
    (hda : a d = false) (hdb : b d = false) {k : Nat}
    (allow : a ≠ zeroWire → b ≠ zeroWire → p = q ∨ k < 5) :
    Available zeroWire (joinWires d) S k (joinWires d p q a b) := by
  unfold Available
  by_cases haz : a = zeroWire
  · subst a
    rcases join_left_zero d p q b hdb with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl (e.symm ▸ hb))
  by_cases hbz : b = zeroWire
  · subst b
    rw [join_swap]
    rcases join_left_zero d q p a hda with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl (e.symm ▸ ha))
  by_cases hab : a = b
  · subst b
    rcases join_self d p q a hda with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl (e.symm ▸ ha))
  exact Or.inr (Or.inr ⟨p,q,a,b,ha,hb,haz,hbz,hab,allow haz hbz,rfl⟩)

lemma Plan.separates {α : Type} [DecidableEq (α → Bool)] {d : α} {target : α → Bool}
    {k S} (h : Plan zeroWire target (joinWires d) k S) (x y : α)
    (same : ∀ w ∈ S, w x = w y) : target x = target y := by
  induction h with
  | done => exact same _ (Finset.mem_singleton_self _)
  | @gate k rest a b p q _ _ _ _ _ _ ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hm
    · have ha := same a (Finset.mem_insert_self ..)
      have hb := same b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
      simp only [joinWires, normalize, phase, ha, hb]
    · exact same w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))



def precompose {α β : Type} (emb : β → α) (w : α → Bool) : β → Bool := w ∘ emb

lemma precompose_join {α β : Type} (emb : β → α) (d : α) (e : β) (he : emb e = d)
    (p q : Bool) (u v : α → Bool) :
    precompose emb (joinWires d p q u v) =
      joinWires e p q (precompose emb u) (precompose emb v) := by
  funext x
  simp [precompose, joinWires, normalize, phase, he]

lemma Plan.restrict {α β : Type} [DecidableEq (α → Bool)] [DecidableEq (β → Bool)]
    {d : α} {target : α → Bool} {k S} (h : Plan zeroWire target (joinWires d) k S)
    (emb : β → α) (e : β) (he : emb e = d) (ht : precompose emb target ≠ zeroWire)
    (fixed : ∀ w ∈ S, w d = false) :
    ∃ r ≤ k, ∃ T ⊆ S.image (precompose emb),
      Plan zeroWire (precompose emb target) (joinWires e) r T ∧
      ((∃ w ∈ S, precompose emb w = zeroWire) → r < k) := by
  induction h with
  | done =>
    refine ⟨0, le_rfl, {precompose emb target}, by simp, .done, ?_⟩
    rintro ⟨w, hw, hz⟩
    rw [Finset.mem_singleton.mp hw] at hz
    exact (ht hz).elim
  | @gate k rest a b p q haz hbz hab allowed hf tail ih =>
    let S := insert a (insert b rest)
    let c := joinWires d p q a b
    let f := precompose emb
    have hnorm (w : α → Bool) (hw : w ∈ insert c rest) : w d = false := by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact normalize_at d _
      · exact fixed _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    obtain ⟨r, hr, U, hU, plan, saves⟩ := ih hnorm
    have hsub : U ⊆ insert (f c) (S.image f) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hU hw)
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv)))
    have eq : f c = joinWires e p q (f a) (f b) := precompose_join emb d e he p q a b
    have ha : f a ∈ S.image f := Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
    have hb : f b ∈ S.image f := Finset.mem_image_of_mem _
      (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have hfa : f a e = false := by
      change a (emb e) = false
      rw [he]
      exact fixed _ (Finset.mem_insert_self ..)
    have hfb : f b e = false := by
      change b (emb e) = false
      rw [he]
      exact fixed _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    by_cases free : f c = zeroWire ∨ f c ∈ S.image f
    · exact ⟨r, by omega, U, plan.pull_free ht hsub free, plan, fun _ => by omega⟩
    have hna : f a ≠ zeroWire := by
      intro za
      rw [eq, za] at free
      exact free ((join_left_zero e p q (f b) hfb).elim Or.inl
        (fun h => Or.inr (h.symm ▸ hb)))
    have hnb : f b ≠ zeroWire := by
      intro zb
      rw [eq, zb, join_swap] at free
      exact free ((join_left_zero e q p (f a) hfa).elim Or.inl
        (fun h => Or.inr (h.symm ▸ ha)))
    have hav : Available zeroWire (joinWires e) (S.image f) r (f c) := by
      rw [eq]
      exact join_available e p q (f a) (f b) _ ha hb hfa hfb
        (fun _ _ => allowed.imp_right (fun h => hr.trans_lt h))
    obtain ⟨r', hr', V, hV, plan'⟩ := plan.pull ht hsub hav
    refine ⟨r', by omega, V, hV, plan', ?_⟩
    rintro ⟨w, hw, hz⟩
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact (hna hz).elim
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact (hnb hz).elim
    have less := saves ⟨w, Finset.mem_insert_of_mem hw, hz⟩
    omega


lemma normalize_not {α : Type} (d : α) (a : α → Bool) :
    normalize d (fun x => !a x) = normalize d a := by
  have e : phase true a = fun x => !a x := by
    funext x
    simp [phase]
  rw [← e, normalize_phase]

lemma normalize_and {α : Type} (d : α) (a b : α → Bool) :
    normalize d (fun x => a x && b x) =
      joinWires d (a d) (b d) (normalize d a) (normalize d b) := by
  unfold joinWires
  rw [phase_normalize, phase_normalize]

lemma normalize_or {α : Type} (d : α) (a b : α → Bool) :
    normalize d (fun x => a x || b x) =
      joinWires d (!(a d)) (!(b d)) (normalize d a) (normalize d b) := by
  have flip (s : α → Bool) : phase (!s d) (normalize d s) = fun x => !s x := by
    funext x
    unfold phase normalize
    cases h : s d <;> cases h' : s x <;> simp [phase, h']
  unfold joinWires
  rw [flip, flip]
  have eq : (fun x => !a x && !b x) = fun x => !(a x || b x) := by
    funext x
    cases a x <;> cases b x <;> rfl
  rw [eq, normalize_not]

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireValue {α : Type} (w : List (α → Bool)) (g : Gate) : α → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => w.getD i zeroWire x)

def evalStep {α : Type} (w : List (α → Bool)) (g : Gate) : List (α → Bool) :=
  w ++ [wireValue w g]

lemma eval_fold {α : Type} (gs : List Gate) (w : List (α → Bool)) (x : α) :
    (gs.foldl evalStep w).map (fun z => z x) = gs.foldl wireStep (w.map (fun z => z x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    simp only [evalStep, wireValue, wireStep, List.map_append, List.map_singleton]
    have h (j : Nat) : (w.map (fun z => z x)).getD j false = w.getD j zeroWire x :=
      List.getD_map (l := w) (d := zeroWire) (n := j) (fun z => z x)
    simp only [h]

lemma fold_keeps (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
    (gs.foldl wireStep w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [wireStep]; omega)]
    exact List.getD_append _ _ _ _ hj

def binaryGate (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

def signals {α : Type} [DecidableEq (α → Bool)] (d : α) (w : List (α → Bool)) :
    Finset (α → Bool) := insert zeroWire (w.map (normalize d)).toFinset

lemma signals_read {α : Type} [DecidableEq (α → Bool)] (d : α) (w : List (α → Bool)) (j : Nat) :
    normalize d (w.getD j zeroWire) ∈ signals d w := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨_, List.getElem_mem hj, rfl⟩))
  · rw [List.getD_eq_default _ _ (by omega), show normalize d zeroWire = zeroWire from
      normalize_const d false]
    exact Finset.mem_insert_self ..

def AnchorGood {α : Type} (d : α) (w : List (α → Bool)) : Prop :=
  ∀ a ∈ w, a d = true → ∀ x, a x = true

lemma AnchorGood.getD {α : Type} {d : α} {w : List (α → Bool)}
    (h : AnchorGood d w) (i : Nat) (hi : w.getD i zeroWire d = true) (x : α) :
    w.getD i zeroWire x = true := by
  by_cases lt : i < w.length
  · rw [List.getD_eq_getElem _ _ lt] at hi ⊢
    exact h _ (List.getElem_mem lt) hi x
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    contradiction

lemma AnchorGood.nonzero {α : Type} {d : α} {w : List (α → Bool)}
    (h : AnchorGood d w) (i : Nat) (hi : normalize d (w.getD i zeroWire) ≠ zeroWire) :
    w.getD i zeroWire d = false := by
  by_contra! hn
  have ht : w.getD i zeroWire d = true := Bool.eq_true_of_not_eq_false hn
  have c : w.getD i zeroWire = fun _ => true := funext (h.getD i ht)
  exact hi (c ▸ normalize_const d true)

lemma anchor_step {α : Type} (d : α) (w : List (α → Bool)) (g : Gate)
    (h : AnchorGood d w) (legal : g.op = .and ∨ g.op = .or) : AnchorGood d (evalStep w g) := by
  intro a ha hv x
  have hm : a ∈ w ∨ a = wireValue w g := by simpa [evalStep] using ha
  rcases hm with hm | rfl
  · exact h _ hm hv x
  rcases legal with ho | ho
  · simp only [wireValue, ho, GateOp.eval, List.all_eq_true] at hv ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h.getD i (hv _ (List.mem_map_of_mem hi)) x
  · simp only [wireValue, ho, GateOp.eval, List.any_eq_true] at hv ⊢
    obtain ⟨b, hb, hb'⟩ := hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map_of_mem hi, h.getD i hb' x⟩

lemma binary_basis (g : Gate) (legal : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hg : binaryGate g = true) : g.op = .and ∨ g.op = .or := by
  rcases legal with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [binaryGate, h] at hg

lemma gate_available {α : Type} [DecidableEq (α → Bool)] (d : α) (w : List (α → Bool)) (g : Gate)
    (legal : FanInTwo (⟨[g], 0⟩ : Circuit)) (k : Nat)
    (mode : binaryGate g = true → k < 5 ∨ AnchorGood d w) :
    Available zeroWire (joinWires d) (signals d w) k (normalize d (wireValue w g)) ∧
    (binaryGate g = false →
      normalize d (wireValue w g) = zeroWire ∨ normalize d (wireValue w g) ∈ signals d w) := by
  obtain ⟨ops, arity⟩ := legal g List.mem_cons_self
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
  change ins.length ≤ 2 at arity
  have eqPhase (m : k < 5 ∨ AnchorGood d w) (i j : Nat)
      (hi : normalize d (w.getD i zeroWire) ≠ zeroWire)
      (hj : normalize d (w.getD j zeroWire) ≠ zeroWire) :
      w.getD i zeroWire d = w.getD j zeroWire d ∨ k < 5 := by
    rcases m with h | h
    · exact Or.inr h
    · exact Or.inl ((h.nonzero i hi).trans (h.nonzero j hj).symm)
  have binaryAnd (i j : Nat) (m : k < 5 ∨ AnchorGood d w) :
      Available zeroWire (joinWires d) (signals d w) k
        (normalize d (fun x => w.getD i zeroWire x && w.getD j zeroWire x)) := by
    rw [normalize_and]
    exact join_available _ _ _ _ _ _ (signals_read d w i) (signals_read d w j)
      (normalize_at d _) (normalize_at d _) (eqPhase m i j)
  have binaryOr (i j : Nat) (m : k < 5 ∨ AnchorGood d w) :
      Available zeroWire (joinWires d) (signals d w) k
        (normalize d (fun x => w.getD i zeroWire x || w.getD j zeroWire x)) := by
    rw [normalize_or]
    exact join_available _ _ _ _ _ _ (signals_read d w i) (signals_read d w j)
      (normalize_at d _) (normalize_at d _)
      (fun hi hj => (eqPhase m i j hi hj).imp_left (congrArg Bool.not))
  have freeNot (i : Nat) : normalize d (fun x => !w.getD i zeroWire x) ∈ signals d w := by
    rw [normalize_not]
    exact signals_read d w i
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ins⟩⟩⟩
  · rcases ops with rfl | rfl | rfl
    · exact ⟨Or.inl (normalize_const d true), by simp [binaryGate]⟩
    · exact ⟨Or.inl (normalize_const d false), by simp [binaryGate]⟩
    · exact ⟨Or.inl (normalize_const d true), fun _ => Or.inl (normalize_const d true)⟩
  · rcases ops with rfl | rfl | rfl
    · refine ⟨Or.inr (Or.inl ?_), by simp [binaryGate]⟩
      change normalize d (fun x => w.getD i zeroWire x && true) ∈ signals d w
      simpa only [Bool.and_true] using signals_read d w i
    · refine ⟨Or.inr (Or.inl ?_), by simp [binaryGate]⟩
      change normalize d (fun x => w.getD i zeroWire x || false) ∈ signals d w
      simpa only [Bool.or_false] using signals_read d w i
    · exact ⟨Or.inr (Or.inl (freeNot i)), fun _ => Or.inr (freeNot i)⟩
  · rcases ops with rfl | rfl | rfl
    · refine ⟨?_, by simp [binaryGate]⟩
      change Available zeroWire (joinWires d) (signals d w) _
        (normalize d (fun x => w.getD i zeroWire x && (w.getD j zeroWire x && true)))
      simpa only [Bool.and_true] using binaryAnd i j (mode rfl)
    · refine ⟨?_, by simp [binaryGate]⟩
      change Available zeroWire (joinWires d) (signals d w) _
        (normalize d (fun x => w.getD i zeroWire x || (w.getD j zeroWire x || false)))
      simpa only [Bool.or_false] using binaryOr i j (mode rfl)
    · exact ⟨Or.inr (Or.inl (freeNot i)), fun _ => Or.inr (freeNot i)⟩
  · simp at arity

def Late (gs : List Gate) : Prop :=
  ∀ pre g post, gs = pre ++ g :: post → 5 < post.countP binaryGate → binaryGate g = true

lemma plan_of_gates {α : Type} [DecidableEq (α → Bool)] (d : α) (gs : List Gate) (o : Nat)
    (fan : FanInTwo (⟨gs, o⟩ : Circuit)) (late : Late gs) (w : List (α → Bool))
    (anchor : 5 < gs.countP binaryGate → AnchorGood d w) (target : α → Bool)
    (eq : normalize d ((gs.foldl evalStep w).getD o zeroWire) = target)
    (nonzero : target ≠ zeroWire) :
    ∃ k ≤ gs.countP binaryGate, ∃ S ⊆ signals d w, Plan zeroWire target (joinWires d) k S := by
  induction gs generalizing w with
  | nil =>
    refine ⟨0, by simp, {target}, Finset.singleton_subset_iff.mpr ?_, .done⟩
    exact eq ▸ signals_read d w o
  | cons g gs ih =>
    have legal := fan g List.mem_cons_self
    have tail : FanInTwo (⟨gs, o⟩ : Circuit) := fun h hh => fan h (List.mem_cons_of_mem _ hh)
    have ht : Late gs := by
      intro pre h post e hn
      apply late (g :: pre) h post _ hn
      exact congrArg (g :: ·) e
    have nextAnchor (hn : 5 < gs.countP binaryGate) : AnchorGood d (evalStep w g) := by
      have gb : binaryGate g = true := late [] g gs rfl hn
      apply anchor_step d w g
      · apply anchor
        simp [List.countP_cons, gb]
        omega
      · exact binary_basis g legal.1 gb
    obtain ⟨k, hk, S, hS, plan⟩ := ih tail ht (evalStep w g) nextAnchor eq
    let c := normalize d (wireValue w g)
    have sub : S ⊆ insert c (signals d w) := by
      intro v hv
      have hm := hS hv
      simpa [signals, evalStep, c, Finset.insert_comm] using hm
    have mode (gb : binaryGate g = true) : k < 5 ∨ AnchorGood d w := by
      by_cases small : k < 5
      · exact Or.inl small
      · right
        apply anchor
        simp [List.countP_cons, gb]
        omega
    obtain ⟨has, free⟩ := gate_available d w g (fun h hh => by
      have : h = g := List.mem_singleton.mp hh
      exact this.symm ▸ legal) k mode
    cases h : binaryGate g with
    | false =>
      exact ⟨k, by simpa [List.countP_cons, h] using hk, S,
        plan.pull_free nonzero sub (free h), plan⟩
    | true =>
      obtain ⟨r, hr, U, hU, plan'⟩ := plan.pull nonzero sub has
      refine ⟨r, ?_, U, hU, plan'⟩
      simp only [List.countP_cons, h, if_true]
      omega

lemma count_two_false {α : Type} (p : α → Bool) (gs : List α) (i j : Nat)
    (hi : i < gs.length) (hj : j < gs.length) (ne : i ≠ j)
    (pi : p gs[i] = false) (pj : p gs[j] = false) : gs.countP p + 2 ≤ gs.length := by
  let pred := fun x : α => !p x
  let two : Finset (Fin gs.length) := {⟨i,hi⟩, ⟨j,hj⟩}
  have sub : two ⊆ Finset.univ.filter (fun x : Fin gs.length => pred (gs.get x) = true) := by
    intro x hx
    simp only [two, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [pred, List.get_eq_getElem, pi, pj]
  have ct : two.card = 2 := by simp [two, Fin.ext_iff, ne]
  have all := List.countP_ofFn gs.get pred
  rw [List.ofFn_get] at all
  have pair_count := Finset.card_le_card sub
  rw [ct, ←all] at pair_count
  have add : gs.countP p + gs.countP pred = gs.length := (gs.length_eq_countP_add_countP p).symm
  omega


def graph9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 1 && x 5) ||
  (x 2 && x 6) || (x 3 && x 5) || (x 4 && x 6) || (x 6 && x 3)

def coordinate {n : Nat} (i : Fin n) (x : Fin n → Bool) : Bool := x i

def inputWires (n : Nat) : List ((Fin n → Bool) → Bool) := List.ofFn coordinate

def firstOr (x : Fin 9 → Bool) : Bool := x 0 || x 2

def seed : List ((Fin 9 → Bool) → Bool) := inputWires 9 ++ [firstOr]

def reset (i : Fin 9) (x : Fin 9 → Bool) : Fin 9 → Bool := Function.update x i false

def graph8 := precompose (reset 0) graph9

def graph7 := precompose (reset 4) graph8

def liftSeven (x : Fin 7 → Bool) : Fin 9 → Bool :=
  (0 : Fin 9).insertNth false ((3 : Fin 8).insertNth false x)

lemma seed_map (x : Fin 9 → Bool) : seed.map (fun a => a x) = List.ofFn x ++ [firstOr x] := by
  simp [seed, inputWires, coordinate, List.map_ofFn]

lemma seed_anchor : ∀ a ∈ seed, a zeroWire = false := by
  intro a ha
  have h : a ∈ inputWires 9 ∨ a = firstOr := by simpa [seed] using ha
  rcases h with h | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    rfl
  · rfl

lemma root_signals : signals (zeroWire : Fin 9 → Bool) seed = insert zeroWire seed.toFinset := by
  unfold signals
  have h : seed.map (normalize (zeroWire : Fin 9 → Bool)) = seed.map id :=
    List.map_congr_left fun a ha => normalize_fixed (seed_anchor a ha)
  rw [h, List.map_id]

lemma norm_image_false {α β : Type} [DecidableEq (α → Bool)] [DecidableEq (β → Bool)]
    (emb : β → α) {a : α} {b : β} (he : emb b = a) {S T : Finset (α → Bool)}
    (fixed : ∀ w ∈ S, w a = false) {U : Finset (β → Bool)} (hSU : T ⊆ S)
    (hU : U ⊆ T.image (precompose emb)) : ∀ v ∈ U, v b = false := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hU hv)
  change w (emb b) = false
  rw [he]
  exact fixed w (hSU hw)

lemma precompose_reset_self (i : Fin 9) : precompose (reset i) (coordinate i) = zeroWire := by
  funext x
  simp [precompose, reset, coordinate, zeroWire]

lemma precompose_reset_ne {i j : Fin 9} (ne : j ≠ i) :
    precompose (reset i) (coordinate j) = coordinate j := by
  funext x
  exact Function.update_of_ne ne _ _

lemma reset_anchor (i : Fin 9) : reset i zeroWire = zeroWire := by
  exact Function.update_eq_self i zeroWire

lemma retained0 (x : Fin 9 → Bool) : firstOr (reset 0 x) = x 2 := by
  simp [firstOr, reset, Function.update_of_ne (show (2 : Fin 9) ≠ 0 by decide)]

lemma uses_zero {k : Nat} {S : Finset ((Fin 9 → Bool) → Bool)}
    (plan : Plan zeroWire graph9 (joinWires zeroWire) k S)
    (hS : S ⊆ insert zeroWire seed.toFinset) : coordinate (0 : Fin 9) ∈ S := by
  let x : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 4)
  let y := Function.update x (0 : Fin 9) true
  have ne : graph9 x ≠ graph9 y := by decide
  by_contra hn
  apply ne
  apply plan.separates
  intro a ha
  rcases Finset.mem_insert.mp (hS ha) with rfl | hm
  · rfl
  have h : a ∈ inputWires 9 ∨ a = firstOr := by
    simpa [seed] using List.mem_toFinset.mp hm
  rcases h with h | rfl
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    have hi : i ≠ 0 := by
      rintro rfl
      exact hn ha
    exact (Function.update_of_ne hi true x).symm
  · change (x 0 || x 2) = (y 0 || y 2)
    decide

lemma uses_four {k : Nat} {S : Finset ((Fin 9 → Bool) → Bool)}
    (plan : Plan zeroWire graph8 (joinWires zeroWire) k S)
    (hS : S ⊆ insert zeroWire (inputWires 9).toFinset) : coordinate (4 : Fin 9) ∈ S := by
  let x : Fin 9 → Bool := fun i => decide (i = 3)
  let y := Function.update x (4 : Fin 9) true
  have ne : graph8 x ≠ graph8 y := by decide
  by_contra hn
  apply ne
  apply plan.separates
  intro a ha
  rcases Finset.mem_insert.mp (hS ha) with rfl | hm
  · rfl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hm)
  have hi : i ≠ 4 := by
    rintro rfl
    exact hn ha
  exact (Function.update_of_ne hi true x).symm

lemma graph_to_theta {k : Nat} {S : Finset ((Fin 9 → Bool) → Bool)}
    (plan : Plan zeroWire graph9 (joinWires zeroWire) k S)
    (hS : S ⊆ insert zeroWire seed.toFinset) :
    ∃ r, r + 2 ≤ k ∧ ∃ U ⊆ (inputWires 7).toFinset,
      Plan zeroWire theta (joinWires zeroWire) r U := by
  have nonzero8 : graph8 ≠ zeroWire := by
    intro h
    have eq := congrFun h (fun _ => true)
    exact (by decide : graph8 (fun _ => true) ≠ false) eq
  have nonzero7 : graph7 ≠ zeroWire := by
    intro h
    have eq := congrFun h (fun _ => true)
    exact (by decide : graph7 (fun _ => true) ≠ false) eq
  have fixed (a : (Fin 9 → Bool) → Bool) (ha : a ∈ insert zeroWire seed.toFinset) :
      a zeroWire = false := by
    rcases Finset.mem_insert.mp ha with rfl | h
    · rfl
    · exact seed_anchor _ (List.mem_toFinset.mp h)
  obtain ⟨k1, hk1, U1, hU1, p1, save1⟩ := plan.restrict (reset 0) zeroWire
    (reset_anchor 0) nonzero8 (fun v hv => fixed v (hS hv))
  have drop1 := save1 ⟨coordinate 0, uses_zero plan hS, precompose_reset_self 0⟩
  have retained1 : U1 ⊆ insert zeroWire (inputWires 9).toFinset := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hU1 hw)
    rcases Finset.mem_insert.mp (hS hv) with rfl | hv
    · exact Finset.mem_insert_self ..
    have hm : v ∈ inputWires 9 ∨ v = firstOr := by
      simpa [seed] using List.mem_toFinset.mp hv
    rcases hm with hm | rfl
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      by_cases hi : i = 0
      · rw [hi, precompose_reset_self]
        exact Finset.mem_insert_self ..
      · rw [precompose_reset_ne hi]
        exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩))
    · have e : precompose (reset 0) firstOr = coordinate 2 := funext retained0
      rw [e]
      exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨2,rfl⟩))
  have fixed1 := norm_image_false (reset 0) (reset_anchor 0) fixed hS hU1
  obtain ⟨k2, hk2, U2, hU2, p2, save2⟩ := p1.restrict (reset 4) zeroWire
    (reset_anchor 4) nonzero7 fixed1
  have drop2 := save2 ⟨coordinate 4, uses_four p1 retained1, precompose_reset_self 4⟩
  have fixed2 := norm_image_false (reset 4) (reset_anchor 4) fixed1 (fun _ h => h) hU2
  have atZero : liftSeven zeroWire = zeroWire := by decide
  have formula : precompose liftSeven graph7 = theta := by
    funext x
    exact (by decide +kernel : ∀ x : Fin 7 → Bool, precompose liftSeven graph7 x = theta x) x
  have nt : precompose liftSeven graph7 ≠ zeroWire := by
    rw [formula]
    intro h
    exact (by decide : theta (fun _ => true) ≠ false) (congrFun h (fun _ => true))
  obtain ⟨r, hr, U, hU, p, _⟩ := p2.restrict liftSeven zeroWire atZero nt fixed2
  have pinImage (i : Fin 9) : precompose liftSeven (precompose (reset 4) (coordinate i)) =
      if i = 0 ∨ i = 4 then zeroWire else coordinate (![0,0,1,2,0,3,4,5,6] i) := by
    funext x
    exact (by decide +kernel : ∀ (i : Fin 9) (x : Fin 7 → Bool),
      precompose liftSeven (precompose (reset 4) (coordinate i)) x =
        (if i = 0 ∨ i = 4 then zeroWire else coordinate (![0,0,1,2,0,3,4,5,6] i)) x) i x
  refine ⟨r, by omega, U, ?_, formula ▸ p⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hU ha)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hU2 hb)
  rcases Finset.mem_insert.mp (retained1 hc) with rfl | hm
  · exact (p.proper nt ha).elim
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hm)
  rw [pinImage] at ha ⊢
  by_cases hi : i = 0 ∨ i = 4
  · rw [if_pos hi] at ha
    exact (p.proper nt ha).elim
  · rw [if_neg hi]
    exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨_,rfl⟩)

lemma tail_late {g : Gate} {gs : List Gate} {o : Nat} (len : (g :: gs).length ≤ 15)
    (fan : FanInTwo (⟨g :: gs, o⟩ : Circuit)) (i j : Fin (g :: gs).length)
    (ord : i.val < j.val) (l : 8 ≤ i.val)
    (nj : ((g :: gs).get j).op = .not)
    (all : ∀ t : Fin (g :: gs).length, ((g :: gs).get t).op = .not → t = i ∨ t = j) :
    Late gs := by
  intro pre h post eq bound
  have size' : (g :: gs).length = pre.length + post.length + 2 := by simp [eq]; omega
  have place : pre.length + 1 < (g :: gs).length := by omega
  let t : Fin (g :: gs).length := ⟨pre.length + 1, place⟩
  have atGate : (g :: gs).get t = h := by
    change (g :: gs)[pre.length+1] = h
    rw [List.getElem_cons_succ]
    exact List.getElem_of_append eq rfl
  rcases (fan h (atGate ▸ List.get_mem (g :: gs) t)).1 with hop | hop | hop
  · simp [binaryGate, hop]
  · simp [binaryGate, hop]
  have ht : ((g :: gs).get t).op = .not := atGate.symm ▸ hop
  have base := List.countP_le_length (p := binaryGate) (l := post)
  have iv := i.isLt
  have jv := j.isLt
  rcases all t ht with ti | tj
  · have it : pre.length + 1 = i.val := congrArg Fin.val ti
    have pj : pre.length + 2 ≤ j.val := by omega
    have q : j.val - (pre.length+2) < post.length := by omega
    have hpost : post[j.val - (pre.length+2)].op = .not := by
      have he : (g :: gs).get j = post[j.val - (pre.length+2)] := by
        change ((g :: gs)[j.val]) = _
        have splitAt : g :: gs = (g :: (pre ++ [h])) ++ post := by simp [eq]
        rw [List.getElem_of_eq splitAt j.isLt, List.getElem_append_right (by simp; omega)]
        simp only [List.length_cons, List.length_append]
        congr 1
      exact he ▸ nj
    have short : post.countP binaryGate ≠ post.length := by
      intro same
      have hh := List.countP_eq_length.mp same _ (List.getElem_mem q)
      simp [binaryGate, hpost] at hh
    omega
  · have jt : pre.length + 1 = j.val := congrArg Fin.val tj
    omega

lemma after_first {g : Gate} {gs : List Gate} {o : Nat}
    (first : ∀ x : Fin 9 → Bool, ((Circuit.mk (g :: gs) o).wires (List.ofFn x)).getD 9 false = firstOr x)
    (computes : circuitFun 9 (⟨g :: gs, o⟩ : Circuit) = graph9) :
    normalize (zeroWire : Fin 9 → Bool) ((gs.foldl evalStep seed).getD o zeroWire) = graph9 := by
  apply Eq.trans _ (normalize_fixed (by decide : graph9 zeroWire = false))
  congr 1
  funext x
  have head (x : Fin 9 → Bool) : wireStep (List.ofFn x) g = List.ofFn x ++ [firstOr x] := by
    have a := first x
    change (gs.foldl wireStep (wireStep (List.ofFn x) g)).getD 9 false = firstOr x at a
    rw [fold_keeps _ _ _ (by simp [wireStep])] at a
    have j : (List.ofFn x).length = 9 := by simp
    have value : (wireStep (List.ofFn x) g).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
      unfold wireStep
      rw [List.getD_append_right _ _ _ _ (by omega), j]
      rfl
    rw [value] at a
    unfold wireStep
    rw [a]
  have hv : (((gs.foldl evalStep seed).getD o zeroWire) x) =
      ((gs.foldl evalStep seed).map (fun z => z x)).getD o false :=
    (List.getD_map (l := gs.foldl evalStep seed) (d := zeroWire) (n := o) (fun z => z x)).symm
  rw [hv, eval_fold, seed_map, ← head]
  exact congrFun computes x

lemma possible_theta (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 15)
    (nots : ∃ i j : Fin C.gates.length, i < j ∧ 8 ≤ i.val ∧ (C.gates.get i).op = .not ∧
      (C.gates.get j).op = .not ∧ ∀ t : Fin C.gates.length, (C.gates.get t).op = .not → t = i ∨ t = j)
    (first : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = firstOr x)
    (computes : circuitFun 9 C = graph9) :
    ∃ r ≤ 10, ∃ U ⊆ (inputWires 7).toFinset, Plan zeroWire theta (joinWires zeroWire) r U := by
  obtain ⟨i,j,ord,late,ni,nj,all⟩ := nots
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil => exact Fin.elim0 i
  | cons g gs =>
    have len : (g :: gs).length ≤ 15 := small
    have ht := tail_late len fan i j ord late nj all
    have ti : i.val - 1 < gs.length := by have := i.isLt; change i.val < gs.length + 1 at this; omega
    have tj : j.val - 1 < gs.length := by
      have low : i.val < j.val := ord
      have := j.isLt
      change j.val < gs.length + 1 at this
      omega
    have shift (a : Fin (g :: gs).length) (h : a.val - 1 < gs.length) (p : 1 ≤ a.val) :
        (g :: gs).get a = gs[a.val - 1] := by
      obtain ⟨av, avh⟩ := a
      cases av with
      | zero => simp at p
      | succ v => rfl
    change ((g :: gs).get i).op = .not at ni
    change ((g :: gs).get j).op = .not at nj
    have hi : binaryGate gs[i.val - 1] = false := by
      rw [← shift i ti (by omega)]
      rw [binaryGate, ni]
    have hj : binaryGate gs[j.val - 1] = false := by
      have low : i.val < j.val := ord
      rw [← shift j tj (by omega)]
      rw [binaryGate, nj]
    have lt : i.val < j.val := ord
    have ct := count_two_false binaryGate gs _ _ ti tj (by omega) hi hj
    have not0 : graph9 ≠ zeroWire := by
      intro h
      exact (by decide : graph9 (fun _ => true) ≠ false) (congrFun h (fun _ => true))
    obtain ⟨k, hk, S, hS, p⟩ := plan_of_gates zeroWire gs o
      (fun a ha => fan a (List.mem_cons_of_mem _ ha)) ht seed
      (fun _ a ha h => by rw [seed_anchor a ha] at h; contradiction)
      graph9 (after_first first computes) not0
    rw [root_signals] at hS
    obtain ⟨r, hr, U, hU, p'⟩ := graph_to_theta p hS
    have lg : gs.length + 1 ≤ 15 := len
    exact ⟨r, by omega, U, hU, p'⟩


lemma Plan.map {α β : Type} [DecidableEq α] [DecidableEq β] {zero target : α} {op} {k S}
    (plan : Plan zero target op k S) (f : α → β) (injective : Function.Injective f)
    (op' : Bool → Bool → β → β → β) (hom : ∀ p q a b, f (op p q a b) = op' p q (f a) (f b)) :
    Plan (f zero) (f target) op' k (S.image f) := by
  induction plan with
  | done => simpa using (Plan.done : Plan (f zero) (f target) op' 0 {f target})
  | @gate k rest a b p q ha hb hab allowed hf tail ih =>
    rw [Finset.image_insert, Finset.image_insert]
    have fr : op' p q (f a) (f b) ∉ insert (f a) (insert (f b) (rest.image f)) := by
      rw [← Finset.image_insert, ← Finset.image_insert, ← hom]
      intro m
      obtain ⟨x, hx, ex⟩ := Finset.mem_image.mp m
      exact hf (injective ex ▸ hx)
    apply Plan.gate p q (fun e => ha (injective e)) (fun e => hb (injective e))
      (fun e => hab (injective e)) allowed fr
    rwa [Finset.image_insert, hom] at ih

lemma uses_all_theta {k : Nat} {S : Finset ((Fin 7 → Bool) → Bool)}
    (p : Plan zeroWire theta (joinWires zeroWire) k S) (sub : S ⊆ (inputWires 7).toFinset) :
    S = (inputWires 7).toFinset := by
  refine Finset.Subset.antisymm sub ?_
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp ha)
  let j : Fin 7 := ![1,0,1,5,0,1,2] i
  let x : Fin 7 → Bool := fun u => decide (u = j)
  let y := Function.update x i true
  have hdiff : theta x ≠ theta y := by
    revert i
    decide +kernel
  by_contra hn
  apply hdiff
  apply p.separates
  intro w hw
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp (sub hw))
  have ne : l ≠ i := fun e => hn (e ▸ hw)
  exact (Function.update_of_ne ne true x).symm

def packBits (n : Nat) (f : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListBE (List.ofFn f)).reverse.cast List.length_ofFn

lemma pack_bit {n : Nat} (f : Fin n → Bool) (i : Nat) (h : i < n) :
    (packBits n f).toNat.testBit i = f ⟨i,h⟩ := by
  change (packBits n f).getLsbD i = _
  rw [packBits, BitVec.getLsbD_cast, BitVec.getLsbD_reverse, BitVec.getMsbD_ofBoolListBE]
  simp [h]

def half : Nat := 248
def rows : Nat := 0xffffffff7efdfbeffb7dfcf7b3dee7eb5dbafbb757a7ab553edda7cfe5ca5cbad9a747faffebf7af5ebdf2efcbb72e5cb9f8deeaff0cecabeafb69faabb61722a1411881a206a08a40307211500d1034422a1411881a206a08a40307211500d1034422a1411881a206a08a403900e82222a1411881a206a08a4038d1a346ca7b29ec85a28e881a206b58ed63a58a543b89ee27b08ec23ca7b29ee8da68fc85a28ee0ca48ba89a607881a206a08a403a58a5433ab5e3532a5c316af169de2eb49b62e14992ab1615a2ab41322a1411e0ca48ba08a403a08a403000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000850a142850a142850a1424a7129c4a7129c4a7129c4a7129c4a7129cc26b09ac26b09ac26b09ac26b09ac26b09a68d068d68d068d68d068d68d068d850a142c26b09ac04a08a800a0023584d6125805413894e253084c214a7129c68d068d485028c60c0489289060508102042080401850a1421a35a3412258304a7129cc26b09a42610980a31214822b0120221010c04a08a800a0020000000

def rowValue (i : Nat) : Nat := (rows >>> (7*i)) &&& 127

def row (i : Nat) : Fin 7 → Bool := fun j => (rowValue i).testBit j.val

def rowIndex (x : Fin 128) : Nat := ([0, 15, 4, 248, 52, 23, 300, 304, 14, 38, 8, 256, 22, 42, 312, 316, 12, 260, 10, 264, 20, 268, 314, 424, 24, 272, 28, 276, 32, 280, 320, 428, 13, 25, 250, 324, 21, 33, 306, 328, 261, 273, 266, 432, 269, 281, 426, 436, 36, 275, 258, 434, 40, 283, 318, 438, 274, 440, 278, 444, 282, 448, 430, 452, 5, 9, 44, 292, 301, 313, 352, 456, 249, 257, 293, 460, 305, 317, 457, 464, 251, 267, 295, 468, 307, 427, 459, 472, 325, 433, 337, 476, 329, 437, 480, 484, 11, 29, 294, 336, 315, 321, 458, 481, 265, 277, 469, 477, 425, 429, 473, 485, 259, 279, 462, 479, 319, 431, 466, 487, 435, 445, 478, 488, 439, 453, 486, 492] : List Nat).getD x.val 0

lemma rowIndex_spec : ∀ x : Fin 128, rowIndex x < 2 * half ∧ rowValue (rowIndex x) = x.val := by
  decide +kernel

lemma row_surjective (x : Fin 7 → Bool) : ∃ i < 2 * half, row i = x := by
  let m : Fin 128 := ⟨(packBits 7 x).toNat, (packBits 7 x).isLt⟩
  obtain ⟨bound, eq⟩ := rowIndex_spec m
  refine ⟨rowIndex m, bound, ?_⟩
  funext j
  change (rowValue (rowIndex m)).testBit j.val = x j
  rw [eq]
  exact pack_bit x j.val j.isLt

def code (a : (Fin 7 → Bool) → Bool) : Nat := (packBits (2 * half) (fun i => a (row i.val))).toNat

def lowMask : Nat := 2^half - 1
def allMask : Nat := 2^(2 * half) - 1
def outCode : Nat := lowMask <<< half

def flipCode (p : Bool) (a : Nat) : Nat := if p then a ^^^ allMask else a

def blendCode (p q : Bool) (a b : Nat) : Nat :=
  let c := flipCode p a &&& flipCode q b
  flipCode (c.testBit 0) c

lemma code_bit (a : (Fin 7 → Bool) → Bool) (i : Nat) (h : i < 2 * half) :
    (code a).testBit i = a (row i) := pack_bit _ i h

lemma code_injective : Function.Injective code := by
  intro a b h
  funext x
  obtain ⟨i, hi, rfl⟩ := row_surjective x
  rw [← code_bit a i hi, ← code_bit b i hi, h]

lemma code_high (a : (Fin 7 → Bool) → Bool) (i : Nat) (h : 2 * half ≤ i) :
    (code a).testBit i = false :=
  Nat.testBit_lt_two_pow ((packBits _ _).isLt.trans_le (Nat.pow_le_pow_right (by decide) h))

lemma code_phase (p : Bool) (a : (Fin 7 → Bool) → Bool) :
    code (phase p a) = flipCode p (code a) := by
  cases p
  · have h : phase false a = a := by funext x; simp [phase]
    rw [h]; rfl
  · apply Nat.eq_of_testBit_eq
    intro i
    change (code (phase true a)).testBit i = (code a ^^^ allMask).testBit i
    rw [Nat.testBit_xor]
    by_cases h : i < 2 * half
    · simp only [code_bit _ i h, allMask, Nat.testBit_two_pow_sub_one, h, decide_true, phase]
      exact Bool.xor_comm _ _
    · simp [code_high _ i (by omega), allMask, Nat.testBit_two_pow_sub_one, h]

lemma code_and (a b : (Fin 7 → Bool) → Bool) :
    code (fun x => a x && b x) = code a &&& code b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases h : i < 2 * half
  · simp only [code_bit _ i h]
  · simp [code_high _ i (by omega)]

lemma row_zero : row 0 = (zeroWire : Fin 7 → Bool) := by
  funext j
  exact (by decide : ∀ j : Fin 7, row 0 j = false) j

lemma code_join (p q : Bool) (a b : (Fin 7 → Bool) → Bool) :
    code (joinWires (zeroWire : Fin 7 → Bool) p q a b) = blendCode p q (code a) (code b) := by
  unfold joinWires normalize blendCode
  rw [code_phase]
  have h := code_bit (fun x => phase p a x && phase q b x) 0 (by decide)
  rw [row_zero, code_and, code_phase, code_phase] at h
  simp only at h ⊢
  rw [←h, code_and, code_phase, code_phase]

lemma code_zero : code (zeroWire : (Fin 7 → Bool) → Bool) = 0 := by decide +kernel
lemma code_theta : code theta = outCode := by decide +kernel

def rawCodes : List Nat := [0xf0ff0f0f0fff00f0ff0f00f0f00f0f000f0ffff00f0fff0ff00f0f00f00000000000000000000000000fffff00000ffff000000f0fff0ff00f0f00f00000, 0xff75766332ffffbb76602406024060286020510a2aa53132022ee777666322000000000000000000000555555555533330510a2aa53132020cc555444100, 0xffbab99331ffff77b9901809018090149010a205155a3231011ddbbb999311000000000000000000000aaaaaaaaaa33330a205155a3231010ccaaa888200, 0xffd5d99cc8ffffeed9908109081090829080540a8aa5c4c8088bbddd999c880000000000000000000005555555555cccc0540a8aa5c4c808033555111400, 0xffeae66cc4ffffdde6604206042060416040a805455ac8c404477eee666c44000000000000000000000aaaaaaaaaacccc0a805455ac8c404033aaa222800, 0xffffffffff50505555055aa055aa0555055f555ff555555555f00050050555000000000000000000fff00000555550000f555aa000000000f00050050550, 0xffffffffffa0a0aaaa0aa550aa550aaa0aafaaaffaaaaaaaaaf000a00a0aaa000000000000000000fff00000aaaaa0000faaa55000000000f000a00a0aa0]

lemma codes_match : ((inputWires 7).toFinset.image code) = rawCodes.toFinset := by
  have e : (inputWires 7).toFinset.image code = ((inputWires 7).map code).toFinset := by
    ext x
    simp [List.mem_map]
  rw [e]
  have h : (inputWires 7).map code = [0xffbab99331ffff77b9901809018090149010a205155a3231011ddbbb999311000000000000000000000aaaaaaaaaa33330a205155a3231010ccaaa888200, 0xffffffffff50505555055aa055aa0555055f555ff555555555f00050050555000000000000000000fff00000555550000f555aa000000000f00050050550, 0xf0ff0f0f0fff00f0ff0f00f0f00f0f000f0ffff00f0fff0ff00f0f00f00000000000000000000000000fffff00000ffff000000f0fff0ff00f0f00f00000, 0xff75766332ffffbb76602406024060286020510a2aa53132022ee777666322000000000000000000000555555555533330510a2aa53132020cc555444100, 0xffd5d99cc8ffffeed9908109081090829080540a8aa5c4c8088bbddd999c880000000000000000000005555555555cccc0540a8aa5c4c808033555111400, 0xffeae66cc4ffffdde6604206042060416040a805455ac8c404477eee666c44000000000000000000000aaaaaaaaaacccc0a805455ac8c404033aaa222800, 0xffffffffffa0a0aaaa0aa550aa550aaa0aafaaaffaaaaaaaaaf000a00a0aaa000000000000000000fff00000aaaaa0000faaa55000000000f000a00a0aa0] := by decide +kernel
  rw [h]
  decide

lemma plan_codes {k : Nat} {S : Finset ((Fin 7 → Bool) → Bool)}
    (p : Plan zeroWire theta (joinWires (zeroWire : Fin 7 → Bool)) k S)
    (sub : S ⊆ (inputWires 7).toFinset) : Plan 0 outCode blendCode k rawCodes.toFinset := by
  have h := p.map code code_injective blendCode code_join
  rw [code_zero, code_theta, uses_all_theta p sub, codes_match] at h
  exact h


def vertexPerm (g : Fin 4) : Fin 7 → Fin 7 :=
  (![![0,1,2,3,4,5,6], ![3,6,2,0,5,4,1], ![5,1,2,4,3,0,6], ![4,6,2,5,0,3,1]] :
    Fin 4 → Fin 7 → Fin 7) g

def permuteInput (g : Fin 4) (x : Fin 7 → Bool) : Fin 7 → Bool := x ∘ vertexPerm g

def laneMask (d : Nat) : Nat := if d = 1 then allMask / 3 else allMask / 5

def swapColumns (d a : Nat) : Nat := ((a &&& laneMask d) <<< d) ||| ((a >>> d) &&& laneMask d)

def column (d i : Nat) : Nat := if i % (2*d) < d then i+d else i-d

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma mask_at (d i : Nat) (hd : d = 1 ∨ d = 2) :
    (laneMask d).testBit i = decide (i < 2*half ∧ i % (2*d) < d) := by
  by_cases h : i < 2*half
  · rcases hd with rfl | rfl
    · exact (by decide +kernel : ∀ n : Fin (2*half),
        (laneMask 1).testBit n.val = decide (n.val < 2*half ∧ n.val % (2*1) < 1)) ⟨i,h⟩
    · exact (by decide +kernel : ∀ n : Fin (2*half),
        (laneMask 2).testBit n.val = decide (n.val < 2*half ∧ n.val % (2*2) < 2)) ⟨i,h⟩
  · have small : allMask < 2^(2*half) := Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    have bound : laneMask d < 2^(2*half) := by
      unfold laneMask
      split <;> exact (Nat.div_le_self ..).trans_lt small
    have hi := bound.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h))
    simp [Nat.testBit_lt_two_pow hi, h]

lemma column_lt {d i : Nat} (hd : d = 1 ∨ d = 2) (hi : i < 2*half) :
    column d i < 2*half := by
  rcases hd with rfl | rfl <;> unfold column <;> dsimp [half] at * <;> split <;> omega

lemma swap_bit_below (d a i : Nat) (hd : d = 1 ∨ d = 2) (hi : i < 2*half) :
    (swapColumns d a).testBit i = a.testBit (column d i) := by
  simp only [swapColumns, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, mask_at _ _ hd, column, hi, true_and]
  by_cases lower : i % (2*d) < d
  · by_cases hz : d ≤ i
    · have none : ¬ (i-d < 2*half ∧ (i-d) % (2*d) < d) := by
        rcases hd with rfl | rfl <;> dsimp [half] at * <;> omega
      simp [lower, hz, none, Nat.add_comm]
    · simp [lower, hz, Nat.add_comm]
  · have ge : d ≤ i := by rcases hd with rfl | rfl <;> dsimp [half] at * <;> omega
    have lane : i-d < 2*half ∧ (i-d) % (2*d) < d := by
      rcases hd with rfl | rfl <;> dsimp [half] at * <;> omega
    simp [lower, ge, lane]

lemma swap_bit_above (d a i : Nat) (hd : d = 1 ∨ d = 2) (hi : 2*half ≤ i) :
    (swapColumns d a).testBit i = false := by
  have zero : ¬ (i-d < 2*half ∧ (i-d) % (2*d) < d) := by
    rcases hd with rfl | rfl <;> dsimp [half] at * <;> omega
  simp [swapColumns, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, mask_at _ _ hd, zero, not_lt_of_ge hi]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma code_swap (d : Nat) (hd : d = 1 ∨ d = 2) (a : (Fin 7 → Bool) → Bool) :
    swapColumns d (code a) = code (precompose (permuteInput (Fin.ofNat 4 d)) a) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 2*half
  · rw [swap_bit_below _ _ _ hd hi, code_bit _ _ (column_lt hd hi), code_bit _ _ hi]
    congr 1
    funext j
    change row (column d i) j = row i (vertexPerm (Fin.ofNat 4 d) j)
    rcases hd with rfl | rfl
    · exact (by decide +kernel : ∀ v : Fin (2*half), ∀ u : Fin 7,
        row (column 1 v.val) u = row v.val (vertexPerm 1 u)) ⟨i,hi⟩ j
    · exact (by decide +kernel : ∀ v : Fin (2*half), ∀ u : Fin 7,
        row (column 2 v.val) u = row v.val (vertexPerm 2 u)) ⟨i,hi⟩ j
  · rw [swap_bit_above _ _ _ hd (by omega), code_high _ _ (by omega)]

def rotateCode (g : Fin 4) (a : Nat) : Nat :=
  (![a, swapColumns 1 a, swapColumns 2 a, swapColumns 2 (swapColumns 1 a)] : Fin 4 → Nat) g

lemma code_rotate (g : Fin 4) (a : (Fin 7 → Bool) → Bool) :
    rotateCode g (code a) = code (precompose (permuteInput g) a) := by
  fin_cases g
  · change code a = code (precompose (permuteInput 0) a)
    apply congrArg code
    funext x
    have h : permuteInput 0 x = x := by
      funext i
      exact congrArg x ((by decide : ∀ j : Fin 7, vertexPerm 0 j = j) i)
    exact (congrArg a h).symm
  · exact code_swap 1 (Or.inl rfl) a
  · exact code_swap 2 (Or.inr rfl) a
  · change swapColumns 2 (swapColumns 1 (code a)) = _
    rw [code_swap 1 (Or.inl rfl), code_swap 2 (Or.inr rfl)]
    apply congrArg code
    funext x
    change a (permuteInput 1 (permuteInput 2 x)) = a (permuteInput 3 x)
    apply congrArg a
    funext i
    have e : vertexPerm 2 (vertexPerm 1 i) = vertexPerm 3 i :=
      (by decide : ∀ j : Fin 7, vertexPerm 2 (vertexPerm 1 j) = vertexPerm 3 j) i
    exact congrArg x e

lemma permute_twice (g : Fin 4) (x : Fin 7 → Bool) : permuteInput g (permuteInput g x) = x := by
  funext i
  exact congrArg x ((by decide : ∀ (g : Fin 4) (i : Fin 7),
    vertexPerm g (vertexPerm g i) = i) g i)

lemma rotate_zero (g : Fin 4) : rotateCode g 0 = 0 := by
  rw [← code_zero, code_rotate]
  rfl

lemma rotate_target (g : Fin 4) : rotateCode g outCode = outCode := by
  rw [← code_theta, code_rotate]
  congr 1
  funext x
  exact (by decide +kernel : ∀ (g : Fin 4) (x : Fin 7 → Bool),
    theta (permuteInput g x) = theta x) g x

def IsCode (a : Nat) : Prop := ∃ f : (Fin 7 → Bool) → Bool, code f = a

lemma rotate_inj {g : Fin 4} {a b : Nat} (ha : IsCode a) (hb : IsCode b)
    (eq : rotateCode g a = rotateCode g b) : a = b := by
  rcases ha with ⟨f,rfl⟩
  rcases hb with ⟨h,rfl⟩
  rw [code_rotate, code_rotate] at eq
  have e := code_injective eq
  apply congrArg code
  funext x
  have hh := congrFun e (permuteInput g x)
  simpa [precompose, permute_twice] using hh

lemma blend_isCode {a b : Nat} (ha : IsCode a) (hb : IsCode b) (p q : Bool) :
    IsCode (blendCode p q a b) := by
  obtain ⟨f,rfl⟩ := ha
  obtain ⟨h,rfl⟩ := hb
  exact ⟨_, code_join p q f h⟩

lemma rotated_isCode (g : Fin 4) {a : Nat} (ha : IsCode a) : IsCode (rotateCode g a) := by
  obtain ⟨f,rfl⟩ := ha
  exact ⟨_, (code_rotate g f).symm⟩

lemma rotate_blend (g : Fin 4) (p q : Bool) {a b : Nat} (ha : IsCode a) (hb : IsCode b) :
    rotateCode g (blendCode p q a b) = blendCode p q (rotateCode g a) (rotateCode g b) := by
  obtain ⟨f,rfl⟩ := ha
  obtain ⟨h,rfl⟩ := hb
  have commute := precompose_join (permuteInput g) zeroWire zeroWire
    (rfl : permuteInput g zeroWire = zeroWire) p q f h
  rw [← code_join, code_rotate, commute, code_join, ← code_rotate, ← code_rotate]

lemma Plan.rotate {k S} (p : Plan 0 outCode blendCode k S) (g : Fin 4)
    (proper : ∀ a ∈ S, IsCode a) : Plan 0 outCode blendCode k (S.image (rotateCode g)) := by
  induction p with
  | done => simpa [rotate_target] using (Plan.done : Plan 0 outCode blendCode 0 {outCode})
  | @gate k rest a b p q ha hb hab al fr tail ih =>
    have ac := proper _ (Finset.mem_insert_self ..)
    have bc := proper _ (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have cc := blend_isCode ac bc p q
    have zc : IsCode 0 := ⟨zeroWire, code_zero⟩
    have fresh : blendCode p q (rotateCode g a) (rotateCode g b) ∉
        (insert a (insert b rest)).image (rotateCode g) := by
      rw [← rotate_blend g p q ac bc]
      intro hc
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp hc
      exact fr ((rotate_inj (proper x hx) cc e) ▸ hx)
    have htail := ih (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact cc
      · exact proper x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
    rw [Finset.image_insert, rotate_blend g p q ac bc] at htail
    rw [Finset.image_insert, Finset.image_insert] at fresh ⊢
    exact Plan.gate p q (fun e => ha (rotate_inj ac zc (e.trans (rotate_zero g).symm)))
      (fun e => hb (rotate_inj bc zc (e.trans (rotate_zero g).symm)))
      (fun e => hab (rotate_inj ac bc e)) al fresh htail

lemma raw_isCode : ∀ a ∈ rawCodes, IsCode a := by
  intro a ha
  have h : a ∈ ((inputWires 7).toFinset.image code) := by
    rw [codes_match]
    exact List.mem_toFinset.mpr ha
  obtain ⟨f, _, h⟩ := Finset.mem_image.mp h
  exact ⟨f,h⟩


def pairDiff (a : Nat) : Nat := (a ^^^ (a >>> half)) &&& lowMask

def covered : List Nat → Nat
  | [] => 0
  | a :: rest => pairDiff a ||| covered rest

lemma covered_bit (i : Nat) (l : List Nat) :
    (covered l).testBit i = true ↔ ∃ w ∈ l, (pairDiff w).testBit i = true := by
  induction l with
  | nil => simp [covered]
  | cons w l ih =>
    simp only [covered, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨v,hv,h⟩)
      · exact ⟨w, Or.inl rfl, h⟩
      · exact ⟨v, Or.inr hv, h⟩
    · rintro ⟨v, rfl | hv, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨v,hv,h⟩

lemma flip_code_agree (p : Bool) (a i j : Nat) (hi : i < 2 * half) (hj : j < 2 * half)
    (h : a.testBit i = a.testBit j) : (flipCode p a).testBit i = (flipCode p a).testBit j := by
  cases p
  · exact h
  · simp [flipCode, Nat.testBit_xor, allMask, Nat.testBit_two_pow_sub_one, hi, hj, h]

lemma Plan.agree_code {k S} (plan : Plan 0 outCode blendCode k S) (i j : Nat)
    (hi : i < 2 * half) (hj : j < 2 * half)
    (h : ∀ a ∈ S, a.testBit i = a.testBit j) : outCode.testBit i = outCode.testBit j := by
  induction plan with
  | done => exact h _ (Finset.mem_singleton_self _)
  | @gate k rest a b p q _ _ _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | r
    · apply flip_code_agree _ _ i j hi hj
      simp only [Nat.testBit_and]
      rw [flip_code_agree p a i j hi hj (h a (Finset.mem_insert_self ..)),
        flip_code_agree q b i j hi hj
          (h b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)))]
    · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem r))

lemma Plan.covers {k} {l : List Nat} (p : Plan 0 outCode blendCode k l.toFinset) :
    covered l = lowMask := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < half
  · have need : outCode.testBit i ≠ outCode.testBit (half + i) := by
      simp [outCode, lowMask, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi,
        Nat.not_le_of_lt hi]
    have left := covered_bit i l
    have hw : (covered l).testBit i = true := by
      apply left.mpr
      by_contra! bad
      apply need
      apply p.agree_code i (half+i) (by omega) (by omega)
      intro v hv
      have hn := bad v (List.mem_toFinset.mp hv)
      have c : ((v.testBit i) ^^ (v.testBit (half+i))) = false := by
        have simpMask := hn
        simpa [pairDiff, lowMask, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hi] using simpMask
      cases h0 : v.testBit i <;> cases h1 : v.testBit (half+i) <;> simp_all
    simp [hw, lowMask, Nat.testBit_two_pow_sub_one, hi]
  · have hh : (covered l).testBit i = false := by
      rw [← Bool.not_eq_true, covered_bit]
      simp [pairDiff, lowMask, Nat.testBit_and, Nat.testBit_two_pow_sub_one, hi]
    simp [hh, lowMask, Nat.testBit_two_pow_sub_one, hi]

lemma blend_swap (p q : Bool) (a b : Nat) : blendCode p q a b = blendCode q p b a := by
  unfold blendCode
  rw [Nat.and_comm]

def retain (b : Bool) (a : Nat) (r : List Nat) : List Nat := if b then a :: r else r

def placeSorted (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: placeSorted a l

lemma place_perm (a : Nat) (l : List Nat) : (placeSorted a l).Perm (a :: l) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [placeSorted]
    split
    · rfl
    · exact (ih.cons b).trans (List.Perm.swap a b l)

def sortedState (l : List Nat) (a b c : Nat) (ka kb : Bool) : List Nat :=
  let v := if kb then placeSorted b l else l
  let w := if ka then placeSorted a v else v
  placeSorted c w

lemma sorted_state_perm (l : List Nat) (a b c : Nat) (ka kb : Bool) :
    (sortedState l a b c ka kb).Perm (c :: retain ka a (retain kb b l)) := by
  have h := place_perm c
  cases ka <;> cases kb <;> simp only [sortedState, retain, Bool.false_eq_true, ite_false, ite_true]
  · exact h _
  · exact (h _).trans ((place_perm b l).cons c)
  · exact (h _).trans ((place_perm a l).cons c)
  · exact (h _).trans (((place_perm a _).trans ((place_perm b l).cons a)).cons c)

def makeState (l : List Nat) (a b : Nat) (p q ka kb : Bool) : List Nat :=
  sortedState ((l.erase a).erase b) a b (blendCode p q a b) ka kb

def gateTag (i j : Nat) (p q ka kb : Bool) : Nat :=
  i*256 + j*16 + p.toNat*4 + q.toNat*8 + ka.toNat + kb.toNat*2

def applyTag (l : List Nat) (tag : Nat) : List Nat :=
  let a := l.getD (tag / 256) 0
  let b := l.getD (tag / 16 % 16) 0
  makeState l a b (tag.testBit 2) (tag.testBit 3) (tag.testBit 0) (tag.testBit 1)

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
lemma tag_bits (i j : Fin 16) (p q ka kb : Bool) :
    let t := gateTag i.val j.val p q ka kb
    t / 256 = i.val ∧ t / 16 % 16 = j.val ∧
      t.testBit 2 = p ∧ t.testBit 3 = q ∧ t.testBit 0 = ka ∧ t.testBit 1 = kb := by
  revert i j p q ka kb
  decide +kernel

lemma tag_applies {l : List Nat} {a b : Nat} (ma : a ∈ l) (mb : b ∈ l) (small : l.length ≤ 15)
    (p q ka kb : Bool) :
    applyTag l (gateTag (l.idxOf a) (l.idxOf b) p q ka kb) = makeState l a b p q ka kb := by
  have ai : l.idxOf a < l.length := List.idxOf_lt_length_iff.mpr ma
  have bi : l.idxOf b < l.length := List.idxOf_lt_length_iff.mpr mb
  obtain ⟨ad, bd, pd, qd, kad, kbd⟩ := tag_bits ⟨l.idxOf a, by omega⟩ ⟨l.idxOf b, by omega⟩ p q ka kb
  have aa : l.getD (l.idxOf a) 0 = a := by
    rw [List.getD_eq_getElem _ _ ai, List.getElem_idxOf]
  have bb : l.getD (l.idxOf b) 0 = b := by
    rw [List.getD_eq_getElem _ _ bi, List.getElem_idxOf]
  change makeState l (l.getD (gateTag (l.idxOf a) (l.idxOf b) p q ka kb /256) 0)
    (l.getD (gateTag (l.idxOf a) (l.idxOf b) p q ka kb / 16 % 16) 0) _ _ _ _ = _
  rw [ad, bd, pd, qd, kad, kbd, aa, bb]

def allBools : List Bool := [false,true]

def legalNext (k : Nat) (l : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  l.any fun a => l.any fun b =>
    a < b &&
    let rest := (l.erase a).erase b
    let cov := covered rest
    allBools.any fun p => allBools.any fun q =>
      (k < 5 || p == q) &&
      let c := blendCode p q a b
      c != 0 && !l.contains c &&
      let mask := pairDiff c ||| cov
      allBools.any fun ka => allBools.any fun kb =>
        ka.toNat + kb.toNat ≤ k+2-l.length &&
        (mask ||| (if ka then pairDiff a else 0) ||| (if kb then pairDiff b else 0)) == lowMask &&
        f (gateTag (l.idxOf a) (l.idxOf b) p q ka kb) (sortedState rest a b c ka kb)

lemma finset_erase_eq {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [nd.mem_erase_iff]

lemma retain_set {R : Finset Nat} {a b : Nat} {l : List Nat}
    (nd : l.Nodup) (ne : a ≠ b) (e : l.toFinset = insert a (insert b R))
    (ka kb : Bool) (hka : ka = true ↔ a ∈ R) (hkb : kb = true ↔ b ∈ R) :
    (retain ka a (retain kb b ((l.erase a).erase b))).toFinset = R := by
  have er := finset_erase_eq nd a
  rw [e] at er
  have er' := finset_erase_eq (nd.erase a) b
  rw [er] at er'
  ext x
  have m : x ∈ ((l.erase a).erase b) ↔ x ∈ R ∧ x ≠ a ∧ x ≠ b := by
    rw [← List.mem_toFinset, er']
    simp only [Finset.mem_erase, Finset.mem_insert]
    tauto
  have retain_mem (k : Bool) (n : Nat) (s : List Nat) :
      x ∈ retain k n s ↔ (k = true ∧ x = n) ∨ x ∈ s := by
    cases k <;> simp [retain]
  rw [List.mem_toFinset, retain_mem, retain_mem, m, hka, hkb]
  by_cases xa : x = a
  · subst x; simp [ne]
  by_cases xb : x = b
  · subst x; simp [Ne.symm ne]
  simp [xa, xb]

lemma make_state_toFinset {R : Finset Nat} {l : List Nat} {a b : Nat} {p q : Bool}
    (nd : l.Nodup) (ne : a ≠ b) (e : l.toFinset = insert a (insert b R))
    (ka kb : Bool) (hka : ka = true ↔ a ∈ R) (hkb : kb = true ↔ b ∈ R) :
    (makeState l a b p q ka kb).toFinset = insert (blendCode p q a b) R := by
  have hk := retain_set nd ne e ka kb hka hkb
  ext v
  rw [List.mem_toFinset, makeState, (sorted_state_perm ..).mem_iff, List.mem_cons,
    ← List.mem_toFinset, hk, Finset.mem_insert]

lemma coverage_keep (l : List Nat) (a b c : Nat) (ka kb : Bool) :
    covered (sortedState l a b c ka kb) =
      pairDiff c ||| covered l ||| (if ka then pairDiff a else 0) |||
      (if kb then pairDiff b else 0) := by
  have h : covered (sortedState l a b c ka kb) =
      covered (c :: retain ka a (retain kb b l)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    simp only [covered_bit, (sorted_state_perm ..).mem_iff]
  rw [h]
  cases ka <;> cases kb <;> simp [retain, covered, Nat.or_assoc, Nat.or_comm, Nat.or_left_comm]

lemma legal_next_hit {k : Nat} {R : Finset Nat} {l : List Nat} {a b : Nat} {p q : Bool}
    (nd : l.Nodup) (hab : a < b) (e : l.toFinset = insert a (insert b R))
    (allowed : p = q ∨ k < 5) (fresh : blendCode p q a b ∉ l.toFinset)
    (tail : Plan 0 outCode blendCode k (insert (blendCode p q a b) R))
    (small : l.length ≤ 15) (valid : ∀ a ∈ l, IsCode a)
    (f : Nat → List Nat → Bool)
    (hf : ∀ tag l', applyTag l tag = l' → (∀ v ∈ l', IsCode v) →
      Plan 0 outCode blendCode k l'.toFinset → f tag l' = true) :
    legalNext k l f = true := by
  have ne := Nat.ne_of_lt hab
  have ma : a ∈ l := List.mem_toFinset.mp (e ▸ Finset.mem_insert_self ..)
  have mb : b ∈ l := List.mem_toFinset.mp (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have not0 : outCode ≠ 0 := by decide
  have hc0 : blendCode p q a b ≠ 0 := by
    intro h
    exact tail.proper not0 (h ▸ Finset.mem_insert_self ..)
  have hcf : blendCode p q a b ∉ l := fun em => fresh (List.mem_toFinset.mpr em)
  let ka := decide (a ∈ R)
  let kb := decide (b ∈ R)
  have kaSpec : ka = true ↔ a ∈ R := by simp [ka, kb]
  have kbSpec : kb = true ↔ b ∈ R := by simp [ka, kb]
  let c := blendCode p q a b
  let rest := (l.erase a).erase b
  let l' := makeState l a b p q ka kb
  have eq' : l'.toFinset = insert c R := make_state_toFinset nd ne e ka kb kaSpec kbSpec
  have t' : Plan 0 outCode blendCode k l'.toFinset := eq'.symm ▸ tail
  let tag := gateTag (l.idxOf a) (l.idxOf b) p q ka kb
  have encoded : applyTag l tag = l' := tag_applies ma mb small p q ka kb
  have validChild : ∀ v ∈ l', IsCode v := by
    intro v hv
    have hm : v ∈ insert c R := eq' ▸ List.mem_toFinset.mpr hv
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact blend_isCode (valid a ma) (valid b mb) p q
    · exact valid v (List.mem_toFinset.mp (e.symm ▸
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)))
  have good := hf tag l' encoded validChild t' 
  have sig := t'.covers
  change covered (sortedState rest a b c ka kb) = _ at sig
  rw [coverage_keep] at sig
  have adj : ka.toNat + kb.toNat ≤ k+2-l.length := by
    have gap : l.length ≤ k + (2 - (ka.toNat + kb.toNat)) := by
      have hcard := tail.card_le
      have fc : c ∉ R := fun hr => fresh (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr))
      rw [Finset.card_insert_of_notMem fc] at hcard
      have card := List.toFinset_card_of_nodup nd
      rw [e] at card
      cases hka : ka <;> cases hkb : kb
      · simp only [Bool.toNat_false, Nat.add_zero]
        have h1 := Finset.card_insert_le a (insert b R)
        have h2 := Finset.card_insert_le b R
        omega
      · have hMem : b ∈ R := kbSpec.mp hkb
        rw [Finset.insert_eq_of_mem hMem] at card
        have h1 := Finset.card_insert_le a R
        simp only [Bool.toNat_false, Bool.toNat_true, Nat.zero_add]
        omega
      · have hMem : a ∈ R := kaSpec.mp hka
        rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hMem)] at card
        have h1 := Finset.card_insert_le b R
        simp only [Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
        omega
      · have ha := kaSpec.mp hka
        have hb := kbSpec.mp hkb
        rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha), Finset.insert_eq_of_mem hb] at card
        simp only [Bool.toNat_true]
        omega
    have n : ka.toNat + kb.toNat ≤ 2 := by cases ka <;> cases kb <;> decide
    omega
  unfold legalNext
  apply List.any_eq_true.mpr ⟨a, ma, ?_⟩
  apply List.any_eq_true.mpr ⟨b, mb, ?_⟩
  simp only [hab, decide_true, Bool.true_and]
  apply List.any_eq_true.mpr ⟨p, by cases p <;> simp [allBools], ?_⟩
  apply List.any_eq_true.mpr ⟨q, by cases q <;> simp [allBools], ?_⟩
  have hs : (decide (k < 5) || (p == q)) = true := by
    simpa [Bool.or_eq_true, or_comm] using allowed
  have hc : (blendCode p q a b != 0) = true := bne_iff_ne.mpr hc0
  simp only [hs, hc, Bool.true_and, List.contains_eq_mem, hcf, decide_false, Bool.not_false]
  apply List.any_eq_true.mpr ⟨ka, by cases ka <;> simp [allBools], ?_⟩
  apply List.any_eq_true.mpr ⟨kb, by cases kb <;> simp [allBools], ?_⟩
  change (decide (ka.toNat+kb.toNat ≤ k+2-l.length) &&
    (pairDiff c ||| covered rest ||| (if ka then pairDiff a else 0) |||
      (if kb then pairDiff b else 0)) == lowMask && f tag l') = true
  simp [adj, sig, good]


-- A row records its predecessor and gate, and the indices of its surviving successors.
-- Packed blocks store thirty-two fixed-width entries each.
def parentTable : Nat → Nat × Array Nat
  | 4 => (23, #[
    0xde08abbb115727096e4e01dc7203b8640b6fc896da912db1429b6184f6c1026d5104da9409b52807674896cea01d99a07b3340b627096c4e01d86207b0c40b5b0096b0015d60429a6f4534800968f812d1e825a351144681a8800000
  ])
  | 5 => (26, #[
    0xa600f429901d0a0857427116d0994d7425f16d095c17425106d087857421b15d085c57421712d084c17420036107f05841f4061072c4f41cb01d07008f41be14d06fc4f41bf01d06ec4f41bb01d06708f419512d06380f410301d03b00f40ec02d0224174000000,
    0x17341745cb353172090c5c506d17141745c501d1680d745a203d1670d8459446116480f458e03d14511744f706d13741b445305d11440f444c05d113407444035d11080f443301d10a80743e505d0f900b43da02d0f4807437506d0dd417436a01d0d8807434901d,
    0x1c3893470514d1c089346fc5611be85346f913d1be40746da14d1b545346c904d1ab15846ac34119d493467056119a018466406d199017466306d197417465523d19181b464605d18b80f462006118701b461c05d18615845e905d179cd845d423d17409845d0241,
    0x24440f491301d242857486e14d20f117483e15d20e51747bd35d1ee84f47b735d1ed08f47b035d1ec80f47883611de093477914d1dd118476e15d1da457476615d1d984b476105d1cc44f473101d1cb41b472824d1ca45347244611c844f472101d1c5417471503d,
    0x3eec4b4fae12d3e984b4f5612d3d484b4f4212d3cc84b4e3846138c4074dfe14d34fc174d3805d33b0934cc405d33140f4cc402d3314074cbe02d32fc074c5103d3148074b6913d2cf01b4b3006d2cc00b4a9802d2a580b4a7404d29d00b4a5f03d29700b49ad06d,
    0x4af45b52bd15d4ae45b52b915d4ab09852a516d4a945752a512d48345b520d15d48104b51f113d47cc4b51ea13d47344f516913d45944b515513d452c4b511d15d4330d850c05614300d0509a15d42684b509026141b0d0506c1214051174ffd16d3fb04b4fba15d,
    0x4e50d3539503d4db117536845d4d90d3534514d4d101353402614cd457533115d4cb857532e12d4ca417531413d4c104b53022614bf44f52fd01d4be45352f804d4bd89852ec16d4ba44f52e901d4b801352d404d4b305852c816d4b205752c513d4b140752c0121,
    0x5a7c07567c23d59ec4b567b01d59dc53567513d59dc07565a12d59584b565701d57fc4b55f116d56708f557a12d554c0b554503d550c13554203d550c0b553e03d54fc0b551c12d54604b551501d52981b547a03d51385753d713d4e84d7539c23d4e60d7539b13d,
    0x60cc0b583201d60a80fd80914d602c0757fb01d5ed45357b713d5edc0757ae15d5e9c5757a513d5e8050d79f15d5e7c4b579b05d5e640f579b02d5e680757900435e480fd77d15d5df44f577d01d5d708f574823d5ce80f56af01d5a884f56a312d5a8c07569d13d,
    0x63a85358e804d63885758db15d63644f58d4143634c5758d312d633c1758cd03d633c0b58ce01d631010d8c603f63045758c113d63040758bb01d624c4f589301d621853588713d621c07587b13d61dc4f586215d60fc5b583d13d60dc5b583712d60cc1b583103d,
    0x72f0585cb416172c0985cac1617260185c943617240185c8d1617210185c7805d71d0139c7403e71d00b9c7401e71c0185c3615d70c4d75c2f05d6928575a4a12d6914175a3856167508f59a814d66a04f598d01d661117597316d65804b594913d65144f58e824d,
    0x780c075de81617780185dbe15d76e44f5db715d76dc4b5db305d76c40f5d7513d75984b5d5c0617480db5d1c23d74644f5d1a12d7450db5d1603d740cd85cfb36173acd39ceb13f73a00fdce73517360585cd43617340585cc415d7300539cc013e73004b9cc001f,
    0x7ffc1b5f8b05d7dd81b5efb13d7bec075ef713d7b2c4f5ec701d7b0c4f5ec301d7a90935ea404d7a2054de8515d79fc4f5e7b13d79dc4b5e5415379544fde5215d792c575e4a12d79144fde3f12d78dc4b5e1805378680fde1505d784c175e0e05d783c075e0701d,
    0x93980764dd03d93001764c003d930407648b01d90f0d7635c45d8c085762e916d8b741b62bf16d8a7457628d15d88345b61ff16d865857618e15d85dc57617216d853117610d16d8384d760d316d81e417606905d815857605106d80e097603606d80cc1b600c45d,
    0x253226193ec0764ef01d
  ])
  | 6 => (26, #[
    0x1941b406405d019413406603d01701f405c05d017413405e03d015c1b405603d01001c403c67d00d09f403516d00d057403514d00d84f403401d00cd1c402d14d009097402716d00984f402401d007093401423d005007400c07d00380f400f02d00104b4000000,
    0x3641780d702d03301f40cc03d032418c0c805f03041f40c104d03000f40c102d02d55b40b445d02d4d740b625d02cd1c40ad35d02815c409045102481c408c171023c1c408825d02205f408816d02101c408007d020013408202d01f014407c03101e014406a02d,
    0x60417417d27105d007417045105c49c416d27105b05c416817d05a05b416814d056093415516d05584f415401d05444f414347104f4d7413237104b8d0412d25104605f411815d046453411801d04405f411116d044057411001d04304b40f857103e01840d8063,
    0x7fc4f41ff12d07fc0741e815d07a45341ea13d07a00741da26f0724d741c017106ec9741bb24d06ec0b41ad25106a09741a916d069d14c1a416306905381a017d06845341a213d068007419824d06645f419916d06604f419014d064c1b419202d06055b418225d,
    0x9205b824027d09045b424014d08f897c23427d08d85b423414d08d04f422c17d08b01b422c04d08b40f422e02d089c1bc22017108801c4218571086498421116d084453421213d084007420c15e083053820c13e08304b820c01f08205c420001d07f11c41fe14d,
    0xc180f42fc07d0bf80f42ed56d0bb11742ed35d0bad1c42e535d0b411442cc1710b2c9742c817d0b205b42c813d0b149442bc0110ac44b42a807d0aa01742a904d0a801f42a106d0a8017429d14d0a5c0b429301e0a2018c28056d09d453425826d09309f424c16d,
    0xe305f438c16d0e200c437f12d0de04b437805d0dd04b437405d0dc04b436c12d0da04b436106d0d7013835f01e0d601f435904d0d680f435107d0d441b435003d0d055b434045d0d0897433f4710ca11443241710c805f432016d0c8453431a3410c384b430506d,
    0x10745b441d14d10784f441a36110241b440805d10141843fc12d0fe04b43f906d0fd04b43f406d0fc04b43ec12d0f7007c3d805d0f641343da03d0f401f43cc01f0f141f43c404d0ee81f43ba04d0ee00f43b403f0ea55b43a935d0ea89743a135d0e51144390171,
    0x12a05744a814d12ac07449c571127018449514d12405c448c16d123057448506d121413448006111f014447845f11e0d8847834211e013847012d11b04b446c06d11a04b446807d11904b446012d11301b444106d110013443606d10d813443403d10815c4420061,
    0x14004f450303d13f01c44f846d13e0df44f835d13e08f44f813d13ec0f44f045d13a0df44e826d13a09744e824d13a04b44eb02d13719c44d835d1340d344c814d132c0744c026d13005f44c015d13005344c013d130c0744b825d12c09344a823d12a05f44a816d,
    0x1ae80f46b056d1ab04b46a906d1aa41346aa03d1a701f469d04d1a780f468317d15a05b456814d15a04f456812d1590dc456013d15605f455816d15005b454014d15004f454012d14e05f453814d14e04b451867d146c17451046d1440d3451024d144053450c371,
    0x1c401c47084511c20dc47080711c10dc47040711c181b46fb06f1bd01f46f406d1bc0d8c6f205f1bcc1786f105d1bcc0786e546d1b949346e00711b615c46d80711b511446d43711b40dc46d03611b401c46c706f1b0c5346c007d1b001b46bc12d1ae01746b904d,
    0x1d211c474b06d1d0118c74024e1d0c1bc74305f1d0c0cc73f3411cf00c473807d1cd0d8c73435f1cd81bc73605f1cd010c73107d1cc00f472807d1ca80b472a01d1c90d8c72435f1c949bc72525f1c9448872403e1c841f472103d1c800b471916d1c5d1b471524d,
    0x1ff09387fc1531ff853c7fe13f1ff01bc7f817d1fe05b47f725d1fd05f47f416d1fd04f47f015d1fc01f47f006d1f515b47c85711f211847bd24d1ee11b47a06711e811747a00711e701b479c05d1e501b477406d1d80d747586711d409c474e17d1d385b474f01d,
    0x21b05b486845321a093886815e21a053886813e21a04b886801f21905c48601712170dc485706f20f453482c35d20b0974828571209c97482424d20900b481016120441c48084532020938808163202053880a13f202418c804471201114480325d20005b47fc463,
    0x24f057493d14d24d05f493415d24d453490d14124215c48f017d23cc5b48f114d23ac1048e514123811748d424d23485348cc45e2334d3c8ce24f233853c8cc04f23211c48c047122a45f489017122401c488c461221093487c34d21f093487d14d21d11c4870471,
    0x28b05f4a2d14d28b84f4a1826d28211c4a04561281c1049fe57127f89049eb04127859c49e127127415f49d315d27315b89ce25f273c57c9cc05f26f45b49bc15d26f84f499624126315b498d35d26215c497e05125e450495b05125545049534712534d7493d16d,
    0x2bb11b4aee24d2bb8534ae047d2b84d34ae224d2b88534adc46d2b70d34add24d2b78534adf04d2b505c4ace5712b0007caa845d2aa4d74aaa25d2a48934a8b16d2a0c144a7b341297c144a533412924d74a3c25d28f0934a3c02d28e4944a3716d28d4534a3613d,
    0x2de05b4b7807d2de0134b7803d2de40b4b5c05d2d74134b5e03d2d7c0b4b5807d2d64134b5a03d2d680b4b5507d2d50134b5403d2d5c0b4b5007d2d44134b5203d2d480b4b4d35d2d20134b4a02d2cf81c4b3856d2ce01c4b080632c111b4afc1432be11b4af934d,
    0x2f30974bce01d2f28dc4bbc27d2ef45b4bbd15d2ef0534bbf13d2ef4074bb425d2eb0934bad17d2eb45b4bad15d2ebc4f4bad01d2e909f4ba416d2e90534ba613d2e90074ba04712e70534b9425d2e505f4b9416d2e50534b9613d2e50074b8c24d2e108f4b8401d,
    0x30641f4c1406f305014cc1206d3048134c1003d30201f4c0803d301c18cc0405f3010178c0006d3000134c0003d2fe41f4bfb02d2fc01c4bec67d2fb0174be80712f915b4be447d2f94d34be624d2f98534be404d2f785b4bdc14d2f704f4bde01d2f649c4bd413d,
    0x323c0f4c7845d31e4d74c7a25d31cc5b4c7114d31c84f4c5c45131781c4c5857d3164534c5b13d31684b4c5713d3140504c4f25d31305b4c4c14d31304f4c492513110974c4234130f4974c3905d30e40f4c2c051309018cc2405f3090178c2004d30800f4c2102d,
    0x33405b4cd014d33484f4cd001d3320934cc816d3320074cc023d3300074cb816d32e41f4cb804d32e00f4cb506f32d01b8cb503f32d00f8cb403d32d40bccb402e32d00b4cac56232b0138c9805d32680f4c9507d3250134c9703d32401f4c9203d32341f4c8c04d,
    0x3468074d1527134404f4d1201d3420974d0a01d3418dc4d050713404574cf916d33e0534cfb13d33e4074cf457133c0974ce824d33a45f4ce916d33a4574ceb13d33a4074ce507133809f4ce016d3380574ce014d33884f4ce001d3360534cd801d3340974cd017d,
    0x35fc1c4d7b13d35d0504d7017d35c0534d7013d35b1184d6d25135a0974d663413524184d40063350017cd4005e34f0134d3c03d34f40b4d3407d34c418cd3005f34b01c4d2867d34a0174d2417134901c4d2224d347c1c4d1827d34685b4d1a15d3460534d1813d,
    0x3774534dde13d3770074dd424d37545b4dd401d37308f4dcc01d37101b4dc603d371c0b4dc005e37080b8dc001f370c078dc301d36e014cdb007d36b41f4da404d36900f4da502d366d1c4d9535d36405f4d9114d36484f4d8316d3604534d8313d36084b4d7c171,
    0x3900584e3c15d38f4534e3e13d38e4534e3637138c4534e2e02d38784b4e0817138201c4e0514d37f09b4dfc15d37f4534dfe13d37f0074df856137d0934df307137b09f4ded16d37b0574ded14d37b84f4dec01d37ad1c4de514d3790074ddc25d37705f4ddf16d,
    0x3d7d184f581613d3cdc4f200513c5c0b4f0c05d3c34134f0f02d3bb89b4ee816d3b941b4ee603d3b744f4ed405d3b54134ed603d3aec5f4eaa07d3aa4134eaa03d3a34534e8807d3a280f4e8024d39e44f4e7407d39d0174e7504d39a84b4e4415d3914534e4613d,
    0x42205f508906d422013508903d42280b508737142040f508202d41e053507807d41e41b507903d41e80b507013d41904b504e02d40f15c503f01d40d80b903701e40419c5008471400057500114d40084f4f9c15d3e74534f9e13d3dbc974f6017d3d84534f6213d,
    0x43d44f90f116d43c00750ec07d43b01b50ec04d43580750d007d43401350d103d43201f50c906d43201350c457d43111750c535d42f11c50b867d42c11f50b034d42c49350a817d42ac1b50ab05d42a01350a903d42a80b50a517142840f509815d42404b509005d,
    0x45f013517d03d45a55b516a25d45ac17515401d454114514c171452c8f514817d45205b514914d4508d0513423d44c08f513114d44b08f512c15d44a08f512914d44904b511513e44445b511015d444007510916d441093910017d440057510001d43e05f50f816d,
    0x48484b521002d4800d751f823d47e05351f015d47a01c51e057147745b51de13d47700751da36147405c51cc16d47305751cd14d47245351c636146e08f51b423d46d45b51b023d46c05b51ac23d46b05f51a812d466453519801d46405f518517d461453517c07d,
    0x4bc04f52e83414ba05452e44514b904b52d114d4b400752cc01d4b115b52c017d4b045352c001d4aac5f52a123d4a705f529c15d4a7007529116d4a4007524126d49048f524002d48e48f523126d48c48f522067d488857521d3714840df521126d484497521024d,
    0x4fd4d753f01714f809753e024d4f800b53dd2514f645b53da13d4f600753b935d4e4118538624d4df853537001f4db19c536c45d4d911c534045d4ca49c53281714c949c53223714c50dc530801f4c111c53041714c011c530215d4bd45bd2f515f4bc05f52f016d,
    0x53e84f54f801d5374d754cc17153209354c817d53204f54c525152e08f54b424d52d84f54b024d52b09354ac13d52a04f54a156d528897549013d51f8dc547637151d01c546413e5134d7544c05d50f050d43a24d5088d0541e341503c5b540f13d5018d05403471,
    0x562057557c15d55f84f557925155d0d8957434255c453556e37155b44f556024d557093555824d55605f555413d55005b554013d54e01b553a02d54a01c5520571548018551d16d547453551c01d54605c551126154311b950c45e5430d8950c352543057950024d,
    0x592807561c17d58745b561c01d57609b55d824d57688f55d802d5758dc55c827d57289b55ca23d57019f55c115d56e15f55b846d56e89355b804d56d09c55a824d56a44b55a036d56809f55a025d56809355a112d56800b559835d565054559024d56404f558c671,
    0x5a705856944535a509bd69425f5a588cd6941635a411c56904515a4897568c16d5a2118d68a26f5a2897d68a2335a2054d68913f5a149056852315a005f568016d59f09bd67c25f59f48cd67817d59e05b567813d59d01f567406d59d00f564e24d592c5b564815d,
    0x5c505c57104615c015f570056d5c00d3570114d5c001356f516f5bb19c56ec3415ba11c56e92715b905b56e414d5b8114d6e026f5b8097d6e015e5b805396e013e5b804b96e001f5b705c56c614d5ad09756b405d5ac0dc56a813d5a909356a702d5a808c569c26d,
    0x5f6c5b57da12d5f449457c92515ec49457a92515e6097579824d5e608f579802d5e5494579116d5e4453579001d5e205f578914d5e2007577e02d5dc017576845d5d7013575914d5d5117975534f5d5093d75514f5d5013d74915f5d0053573c4715cc85f5715271,
    0x61e84f587801d61d093587517d61d45b587413d61d407586127161001c583046d60c093582856e60a050d82447d6094d3582424d609453582145d608853582304d606517d81127160401c58085716010dc580001d5ff04b97fc01f5fb89757ed05d5f909357dd05d,
    0x63589758cc47163219f58c407163011f58c124d63085358be27162e40f58b017d62c41b58b105d62c01358b103d62c80b58a815d62805358a106d62801758a202d62605f589b06d626013589903d62680b5897371624013589103d61f053587825d61e45b587914d,
    0x64545b591413d644053591107d64441b591103d64480b590a14d640c57590314d640c4f58f406163d40f58f014d63c01b58ef35363b018d8ef03f63b00f98ee03d63a01f58e903d63a80b58e013d63841f58e106d63800b58da07d63641b58d804d63515f58d535d,
    0x6598dc595827d65645b595814d65604f595901d65309f594c16d653057594d14d65384f594c01d65211c594514d64f097593c17d64f05b593c14d64f04f593c01d64d057592023d647097591f16d647453591e13d646097591916d646453591a13d645093591517d,
    0x66945b59a2363668494d9a223f66745f599f13d667407599823d66508f599716d664058d99012e66444b598c07166219f598637166105c598224d65f49c597856d65e11f597934d65e893597914d65e013597216d65c053597313d65c807596d27165a053596b13d,
    0x67b45b59ec01d67a11459e927167915f59e716d67985359e701d6788dc59e017167605059d425d67505f59d416d673c9359cf23d673c0b59cb25d67209359cb02d66e49459b823d66d09359b235366c498d9b223f66c48f99b023d66b85f59ac13d66b80759a424d,
    0x69a058da6a15f69905c5a6106d6980175a6302d6950975a5025d69445b5a4c24d69345f5a4d16d6920935a4917d69245b5a4414d69101f5a4406d68d84f5a3401d68b45f5a2217d688c4f5a1807d68640f5a1a02d68208f59fd56d67f11759fd05d67ed1c59ec17d,
    0x6a68dc5a981716a54535a934616a309b5a8d17d6a30575a8d14d6a384f5a8c01d6a10975a8417d6a185b5a7d16d69f0575a7d14d69f84f5a7c01d69ed14da7815e69e0539a7b13f69e04f9a7b13d69e04b9a7801f69ec079a7b01d69dd1c5a7015d69c4535a68453,
    0x6b208f5ac74716b105c5ac40716b019f5ab914d6ac09b5ab015d6ac4535ab213d6ac0075aac16e6abc53daac14e6ab8535aaf13f6ab04f9aaf13d6ab04b9aac01f6abc079aaf01d6aa05c5aa427d6a9c5b5aa415d6a94535aa613d6a90075aa34716a849c5a9d14d,
    0x6c1c075b0016d6c04535b0213d6c00075afc4536bf0579afc14e6bfc4fdafc13e6bfc4f5afc12e6bf007daff01e6bfc075af81616bc8dc5af01716ba81f5ae805d6bac0b5ae725d6b9c935ae702d6b8c975ae324d6b8c0b5ad12516b408f5acc25d6b2494dac923e,
    0x6d509f5b5425d6d50935b5512d6d500b5b4c35d6d10935b4413d6cf0575b3724d6cdc0b5b2c0716c915c5b274616c90585b240616c819f5b1d16d6c70575b1c01d6c68d85b181716c505b5b1415d6c50075b1214d6c4c4f5b1301d6c34535b0b13d6c2c075b0713d,
    0x7004535c0001d6fac5f5be316d6f80075bd327d6f00975bb726d6eac9b5ba824d6e9098dba326d6e8c8f5b9c16d6e70535b9c13d6e6c5b5b9814d6e6c4f5b9b12d6e60075b901636e4c53db7f26d6df0935b7c02d6dd0935b704716dc01c5b6c67d6db4575b5436d,
    0x72f0505cb815172a45b5ca815d72a0075c7316d71b1185c6024d7164d35c5515d713114dc4c15e71304f9c4c12e713007dc4817171119c5c4445d70b0975c2f24d70a84f5c2801d7090075c1c56d70684f5c1725d705c0b5c1316d7044535c1301d701c975c0017d,
    0x76d0535dac25d76b05b5dac14d76b0075da415d766d1c5d9535d761c5b5d8713d761c075d7114d75c84f5d6d14d75b04f5d6503d75980b5d5c45d7574d75d5e25d7504535d4001d74f0535d3c01d74d04f5d3601d74805c5d1c07173f8975cfc05d73a0935cd4141,
    0x77e19f5dfa25d77c15b5df047d77c4d35df024d77c4535df004d77a09f5dea16d77a0535de813d77a8075de527177804f5dd825d7768075dd6371774058ddd015e77209f5dc916d7720535dc813d7724075dc226d76f09f5dbc16d76f0535dbe13d76f0075db8471,
    0x7a104f5e8035f79f0135e7d03d79f80b5e7705f79b4d75e5b16d796c4f5e5b01d79505c5e4815d7900535e3c04d78d1175e3625d78d4175e3116d78c4535e3001d78a0075e244517888535e2212d788c075e0814d78204f5e0901d78045f5e0313d7804075dfc071,
    0x7ec018dfb00627ec0185fb005e7df4535f7e13d7df0075f3914d7cd0575f3514d7cd0075ee025d7b80935ee023d7b800b5ed514d7b405c5ec826d7b20575eca13d7b20075ec514d7af0175ebd04d7afc0b5eb417d7ab85f5ea807d7a6857de9014d7a389bde8414d,
    0x7f611c5fda15d7f5117dfd73637f50d89fd43617f50d39fd01717f30dc5fcf15d7f344f5fc846e7f21179fc81637f20589fc81617f20579fc03717f0c575fc213d7f0c4b5fbc45e7ef058dfbc15e7ee0dc5fbb05d7ee40f5fbb02d7ee8075fb41717ec11b9fb045e,
    0x82511c60911718230dc607627181880b605067181309c6048471812c07604301d80cd1c602e37180a897602627180411c600e37180285b600637180049c5fff3717fe11c5fec47d7fa11b9fe834f7fa093dfeb14f7fa013dfe44717f811c5fdc4717f705c5fdd16d,
    0x849017612404d84900f611c67184611c611b13d846c4b611b01d845c4f611313d844c07610d271842c4f610313d840c0760f815e83e053a0f813e83e04ba0f801f83b89760e706d8368dc60b747182c84f60ab47182905760a613d82900760a017182749c6098171,
    0x84f85f613e16d84f857613e13d84f807613b16d84ec4f613434f84dc57e13415e84dc57613413e84d84be13412e84dc4b613023d84c45f613116d84c457613114d84c407612f16d84a0d3e12b05f84a017a12b05d84a00fa12802e84a007a12412d84901f612406d,
    0x866c17618e363863498e18816d86045b618014d85d85b617414d85d04f616c06d85b013616d03d85b80b616347185801c615746385405f615015d854053615013d854007614f16d852114e14a15f852057a14a15d851c5b614315f850057a14315d85004fa13c24d,
    0x892053624a13d892007624427d89145b624414d89104f624501d89009f624216d890053624013d890807622914d88904fa220171886013a1f913d879017a1e113d876c53e1d813e87519c61d457186e01c61b346186985761a316d868c57619f15d867c4b619b06d,
    0x8a701c629817d8a6c1b629805d8a6013629903d8a680b62940518a4057628a06d8a2013628903d8a280b62846718a0057627817d89e41b627805d89e013627903d89e80b627015d89a117e26806289405f624c26d893057624d14d89384f624c01d89209f624816d,
    0x8bb05f62ec06d8ba41be2e806e8ba41b62e80438b9c1f62e503d8b980b62dc17d8b741b62dc03d8b6857e2d406d8b501362d602d8b305f62ce06d8b300f62cc02d8b209be2c507d8b101362c503d8b011762c135d8b089762a867d8aac1762a034d8a849362a214d,
    0x8d404f635001d8d2057633426d8cc09b633015d8cc453633213d8cb09f632d16d8cb053632c13d8ca09f632816d8ca453632813d8c905f632506d8c9013632503d8c980b631f16d8c645f630306d8bf05b62fb05f8be017a2fb05d8bd01362f503d8bd80b62f307d,
    0x8e40df638c27d8e305b638c13d8e2c5be38816e8e2c5b638416d8e184f638401d8e001c637c67d8df4d7637456d8dd11f637434d8dd893637614d8dd013636827d8da45b636915d8da053636813d8d98d4636025d8d609f635816d8d6053635813d8d4097635016d,
    0x8fc04f63ec17d8fb01b63ec04d8fb40f63e626d8f789b63d445d8f54d763d405d8f445b63d213d8f400763c84518f115f63c614d8f1c4f63b136d8eb09b63a935f8ea0d7a3a935d8e905363a413d8e9807639c27d8e705b639816e8e604ce39517d8e5c4f639501d,
    0x91301c644a25d91105c643d27190e09f643a16d90e053643813d90d494643025d90c807642816290709f641c16d907057641c14d905097641417d905053641401d90415c640c15d8ff89f63f826d8fe05763f914d8fd09f63f416d8fd05363f027d8fc85b63f214d,
    0x92a09f64aa16d92a05364a427d92945b64a414d92805f64a306d928013649617d92305f648d14d923007648401d9200df648316d920853646826d919897e46014d91804f646101d91789b645827d91605b645516f91505ba45516d915050e45217d91404f645201d,
    0x940057a50215d940050e4fc14d93f04f64fc01d93e01c64f467d93d85764f017193b15b64ec47d93b0d364ec24d93b45364ec04d93909f64e616d93905364e015193709764de01d93509f64d516d93505364d015193309764c015192f05764b046d92b09b64ac15d,
    0x95d453657613d95d007657114d95909f656416d959057656514d959007655c05d957413655e03d95409f655016d95309f654d16d95209f654a16d95105f654406d94f11b653535d94d897653405d94a007652445194905c652057d94309b650a16d94109b650215f,
    0x9a844f662056d98709f661914d98684f661801d984057661114d98400765f447197dc1c65f067d97805765d847d9750dc65c826d97284f65b514d96d84f65b401d96c8d865a415d96945365a401d968058659805d966413659a03d96205c657927195d09f657416d,
    0x9cc007e73101e9cc407672c12d9cb01f672d06d9cb017672d04d9cb80f67201719c801c671c27d9c505f671702d9c4017a71301e9c0453670213d9c000766fc01d9bb19f66ee15d9ba19f66ea25d9b919f66e435d9b819f66e305d9b5158a6d40539b119f66c405d,
    0x9de11c677427d9d405c674d14d9d1017674403d9d1407673c04d9cf00f673d02d9cc00fe73003e9cc00f673002e
  ])
  | 7 => (24, #[
    0x804f00802f00412f00412e00412d00507f00407300406f00406300705f00405300604f00404300503f004033000570000564001170000164000160000154000150000144000140000134000130000124000060000054000020000014000000,
    0x1167201156f01127201017200c17300c16f00c16e00d07f00c07e00c07d00c07300d03f00e03e00e03d00c02f00e02e00f02d00957f00857300856f00856300845e00b45200935e00a35200825e00925200b17f00b16f00b14300807f008063,
    0x2056f02056302125202317f02316f02314302005201c24e01c24d01d17f01c17301c16f01c16301d13f01c01e01856f01856301935e01a35201b16f01b13f01805201423e01423d01416f01416301614f01414301401f01401e01401d01067e,
    0x3016303007202c26f02c26e02d17f02c17302f15f02e14f02c14e02d14d02c13f02c01e02856f02856302925202b16f02805202427302425e02425d02616f02716e02716d02416302513f02713e02613d02401f02401e02401d02157f020573,
    0x3967203b47203a37203817203807203427f03427e03427d03416f03416e03516d03715f03415e03415d03614f03414e03514d03513f03413e03613d03401f03401e03401d03367e03167203156f03347303347203347103345e032372031272,
    0x5406305503f05012d04d57f04c57304c56f04c56304c45e04f45204d35e04e35204f17f04f16f04f14304f13f04d12304c02f04c01204823d04814d04406f04406304604f04404304017204007304007204007103c67e03c67d03d15e03c05e,
    0x6816d06808d06807d06805d06804d06712e06606f06706e06706d06406306503f06703e06603d06012d05d57f05c57305c56f05c56305f45205d25e05d25205f17f05f16f05f14305e13305f12f05c01205823d05815d05507f05407305406f,
    0x7817d07808d07806d07805d07804d07412f07507f07407e07407d07407307705f07405e07405d07604f07404e07504d07503f07403e07603d07012d06d57f06c57306c56f06c56306e35206d25206f17f06f16f06f14306c04f06c01206823d,
    0x8e02e08e02d08823d08818d08807d08806d08805d08804d08406f08406e08506d08705f08405e08405d08604f08404e08504d08503f08403e08603d08012d07f67e07d67207d56f07f47207d45e07e37207d27207c15207c05207f01e07823d,
    0x9436009435409435009434409427009426409426009425409425009424409424009423409417009416409416009415409415009414409414009413409413009412409012d08d67208d56f08f47208e37208d35e08d25208c17208c05208d02f,
    0xbc16d0bc15d0bc14d0bc13d09c17f09c17309c16f09c16309c14f09c14309c13f09c13309c12f09c12309817f09817309816f09816309814f09b14309813f09a13309812f099123094570094564094470094464094460094454094370094364,
    0xf445d0f438d0f437d0f436d0f423d0f413d0f603d0ec38d0ec27d0ec26d0ec25d0ec24d0ec12d0e85810e425d0e412d0dc36d0dc28d0dc27d0dc25d0dc24d0dc12d0d435d0d412d0cc34d0cc12d0c417d0c416d0c415d0c414d0c413d0bc18d,
    0x12808112458d12447d12446d12434d12424d12414d12604d12038112008111c24d11e04d11806111456d11414d11604d11048111008110c36d10d03d10808110447d10438d10436d10435d10423d10413d10503d1000610fc46d0ff03d0f8061,
    0x15005215005115003215003114c16114816114447314546f14445214524e14707f14706f14405314405214405114703314018114008113c78d13d06d13828113808113435d13705d13008112c67d12c58d12c45d12c35d12c25d12c15d12f05d,
    0x16018115c17d15c08d15c05d15d04d15e03d15f02d15857315856f15835e15a17f15a16f15814315807f15807e15807d15b04f15804e15804d15803e15902f15a02e15a02d15a01e15416115414115047315346f15045215307f15306f150053,
    0x18016d18014e18013e18001f17e36117c05117824d17525117406117023d16c57116c18116857216856e16847316847216846316846216924e16807316807216807116b06f16b05f16b03316417d16508d16405d16504d16603d16702d160561,
    0x19045319034e19024e19017319017219017119016e19014e19307319307219307118c27d18d14d18b45118806118425d18418d18417d18514d18613d18056318035e18027318325f18025e18025d18024f18017f18017e18017d18016f18016e,
    0x1a518d1a517d1a416d1a41611a514d1a613d1a401d1a05711a108119c47319c45319c45219c45119c24e19c17219c15e19e07319e07219e07119828d19817d19815d19914d19a13d19456119748119408119057e19056e190473190463190462,
    0x1ce13d1cc01d1c85811c80811c428d1c517d1c516d1c415d1c514d1c613d1c401d1bc56f1bc5631be3521b826d1b517f1b41731b416f1b41631b715f1b614f1b401f1b05611b23611b12511ac24d1ad16d1ac1611ac01d1a956d1a85611a425d,
    0x1f401d1f05811f12811f20811ee16d1ed14d1e87811e567e1e56721e457e1e45731e45721e45711e41721e026d1dd17f1dc1731dc16f1dc1631df15f1dd13f1d85611d81611d423d1d616d1d41611d401d1d05811d05711d23811cc16d1cd14d,
    0x21514d21401d21058121018121208120c28d20f17d20f16d20c15d20d14d20e13d20c01d20456f20456320525220026d1fc2731fd17f1fc1731fe16f1fc1631fe14f1fc13f1fc01f1f85811f46811f428d1f617d1f716d1f415d1f514d1f613d,
    0x22c45d22d35f22f35e22d35d22e25f22d25e22e25d22f15f22c05f22b48122767e22567222756f22747322747222747122637222527222067d22135d21d57f21c57321f45e21d35f21e35e21d35d21c25e21f15f21858121818121716d21415d,
    0x24806024805424b04424418d24416d24415d24414d24413d24408d24406d24405d24604d24058124008123c78d23d56d23f16d23c06d23567223747223637223417223068d23057d23045d23135d23225d22c56f22c56e22d56d22c45f22f45e,
    0x24d02f24c02e24d02d24857024856424846024845424837024a36424836024a35424835024a344248270249264248260249254248250249244248240249234248170248164248160248154248150248144248140248134248130248124248070,
    0x25157f25057325045e25345225035e25235225025e25125225317f25017325016325314f25314325313f25213325312f25112324d17324c16f24c16e24d07f24c07e24d07d24d07324d04f24c04e24d04d24f04324d03f24c03e24c03d24d033,
    0x25c26025d25425c25025d24425c24025d23425c17025c16425c16025c15425c15025c14425c14025c13425c13025c12425c07025d06425d06325c06025c05f25e04425817d25815d25813d25907d25906d25905d25b04d25408d25405d25603d,
    0x26716f26416326714f26714326713f26613326712f26512326407f26406326017326016f26016e26007f26007e26007d26007326003f26003e26003d25c57025c56425c47025c46425c37025e36425c36025e35425c35025e34425c27025d264,
    0x27525427525027524427417027416427416027415427415027414427414027413427413027412427407027406427406327406027505e27018d27204d27203d26c02f26f02e26f02d26908d26456f26456326745226535e266352265252264173,
    0x2a412d2a402d2a006129c34d29c12d29c02d28867228856328825e28815e28516328018128017127d56327d27227d25e27d25227c17227d15e27c15227c07327c06e27c05327c05227817327816f27816e274570274564276270275264274260,
    0x2cc38d2cc36d2cc35d2ce23d2cc13d2c86712c90612c446d2c503d2c01812c00812bc38d2bc27d2bc26d2bc25d2be24d2bc12d2bc02d2ba5812b425d2b412d2b00612ac36d2ac28d2ae27d2ac25d2ae24d2ac12d2af02d2a80612a435d2a427d,
    0x30408130026d30114d2fc5812fb5812f825d2fa18d2f81812f817d2fb16d2f914d2fa13d2f801d2f45812f024d2f018d2f01812ec5812e823d2e818d2e81812e801d2e45812e456d2dc78d2dc16d2da4812d81812d80812d436d2d503d2cc47d,
    0x32c17d32d14d32c01d32927132808132427d32516d32415d32514d32613d32058131c24d31d18d31c18131c01d31b48131428d31117f31315f31214f31013f30c78130827d30818d30818130916d30815d30914d30a13d30801d307481304171,
    0x36004036003436003036002436002035c34d35c12d35417235068d34c25e34d15e34968134807134457334457234457134406334406234406134067d33828d33416f33715f33614f33513f33401f33078133056d33238133127132d18d32c181,
    0x37315f37015e37015d37015337001f37001e37001d36c23d36812e36812d36806f36806336a03f368033364563366352360570360564360460360454361270362264360260362254361250362244360240362234361070360064360060360054,
    0x38001f38001e38001d37c23d37b57f37857337856f37856337934f37825e37925237b17f37b16f37b14337a13337b12f37805237434d37425d37418d37517d37416d37401d37024e37117f37017e37017d37017337016f37016e37116d370163,
    0x39024039223439005039004438c23d38a67e38967238956f38b47238945e38a37238935e38925238815238b12f38807238434d38427d38418d38416d38515d38401d38117f38017e38017d38017338315f38015e38015d38214f38014e38114d,
    0x3b525d3b424d3b402d3b15813ad25d3ac24d3a436d3a428d3a527d3a525d3a424d3a402d39c35d39c24d39527f39427339426f39426339424f39424339423f394233390570390564390460390454391270390264390260390254391250390244,
    0x3ed2533ed2523ed2513ee2333ec1523ec13e3ec12e3e824d3e016d3dc06f3de04f3d81813d80813d478d3d416d3d01813cc58d3cd47d3cc46d3cc34d3cd24d3ce14d3cc04d3c93813c81813c524d3c614d3c01613bc14d3b438d3b527d3b426d,
    0x40045340237340237240237140035f40024e40017340016e40014e3fc27d3fd14d3fb4613f92513f456d3f425d3f418d3f517d3f514d3f401d3f23613f12513ec57f3ec56f3ec47f3ec4533ec4523ed36f3ee3433ee3423ee3413ee27f3ee26f,
    0x41c57341c56f41c56341c47f41e35241c05241826d41427341517f41417341416f41416341414e41413f41401e41056d41056140c56140c18140828d40917d40815d40914d40801d40456140748140528140056e400473400472400463400462,
    0x44716d44348143c67e43d67243f47343f47243f47143e37243c07243867d43935d43557f43457343445e43535f43535e43535d43715f43405e43058142c28d42f17d42f16d42c15d42d14d42e13d42c01d42858142928142716d42514d41d57f,
    0x46517f46417346513f46401e46024d45f57f45c57345c56f45c56345d35e45e35245e24f45f16f45f14345f13f45c05245835d45824d45818d45817d45816d45801d45424d45057345056345125244c35d44c12d44858144808144478d44456d,
    0x47d25247c24e47c24d47c17247d15e47c07247835d47828d47817d47a14d47801d47416f47416e47516d47513f47613e47613d47401f47401e47401d47024d46d67e46d67246d56f46d27246d25e46c15246d13e46d13d46c07246835d46827d,
    0x49e58149825d49036d49028d49227d49025d49224d49002d48827f48827348826f48826348824f48824348457048456448447048446448446048445448427048426448426048425448425048424448424048523448405048404448024d47d672,
    0x4d414d4d413e4d401f4d07814cc16d4c907f4c806f4c903f4c41814c40814c078d4c116d4be4814bc1814b836d4b913d4b41814b047d4b038d4b036d4b035d4b223d4b113d4b003d4ac1614a813d4a038d4a027d4a026d4a025d4a224d4a002d,
    0x4e52734e52724e52714e426f4e425f4e41734e41724e41714e416e4e027d4e114d4df4514de3614d825d4d818d4da17d4da13d4d801d4d45634d437f4d436f4d43434d42734d424f4d417f4d417e4d417d4d416f4d416e4d416d4d414f4d414e,
    0x4fc01f4fc01e4fc01d4f85614f81614f45714f63814f04734f04534f04524f04514f12734f12724f12714f025f4f01724f015e4ec28d4ec17d4ec15d4ed14d4ee13d4ec01d4e85614eb4814ea3814e457e4e456e4e44734e44634e44624e4453,
    0x52127152007251c67d51957f51857351925e51b15f51805e51458151638151016d51015d51114d51213d50c58150e38150828d50917d50816d50815d50914d50a13d50901d50026d50101d4fc2734fd17f4fc1734fc16f4fc1634fe14f4fc13e,
    0x54012d54307d54304d53c58153c08153878d53956d53b16d53167253017253007252c68d52c57d52e25d52c05d52867e52856f52856e52956d52a25f52925e52a25d52b15f52805f52905e52905d52528152067e52167252156f521273521272,
    0x54c14e54c14d54f06f54f06e54f06d54c06354d02f54f02e54e02d54d02354856354925254457054456454746054445454417054516454416054515454415054514454413054512454407054406454406054405454404054036d54327d54324d,
    0x55846055845455837055a36455836055a35455827055926455826055925455824055817055816455816055815455815055814455805055b04455445d55438d55437d55436d55423d55618d55517d55516d55501d55025d55317d55213d54c173,
    0x56057356056f56056356045e56345256317f56017356316f56016356314f56314356005255f46355c27355f24f55c24e55c24d55d17f55c17e55d17d55f17355d16f55c16e55d16d55c16355d13f55c13e55c13d558570558564558470558464,
    0x57016457016357016057015457015057014e57007057106456c36d56c28d56c27d56c18d56c15d56f14d56c01d56917f56817e56817d56817356a14f56814e56914d56913f56813e56a13d56801f56801e56801d56425d56618d56617d56157f,
    0x57925157923e57817257915e57815257807257756357427357725f57425e57425d57616f57416e57516d570570570564570470573464572460573454573453570370572364570360572354570270571264570260571254572240572234570170,
    0x58427358426f58426358057058056458046058045458027058026458026058025458025058024458024058123458005058004457c28157c27157c25d57967e57967257956f57956357b47257945e57b45257a36357a352579273579253579252,
    0x5a847d5a838d5a836d5a835d5ab23d5a913d5a803d5a41615a013d59838d59b27d59826d59825d59b24d59802d59456359426e59725f59425e59725d59724f59424e59724d59423e59412f59402f59702e59702d58c26d58c25d58456358427f,
    0x5da13d5d801d5d45615d74815d056e5d04735d04725d04635d04625d04535d01735d01725d01715d016e5d115f5cc27d5cd14d5c416d5c006f5c103f5bc2815bc1815bc0815b878d5b916d5b74815b42815b41815b036d5b113d5af5815ac181,
    0x60057360135f60335e60135d60025e60315f60005e5fc5815fe3815f916d5f914d5f45815f028d5f117d5f116d5f015d5f114d5f213d5f001d5e826d5e517f5e41735e416f5e41635e715f5e401e5e05615df5715df4815d828d5db17d5d914d,
    0x62805262425d62424d62418d62416d62415d62401d62114d61c57361f45261e35261d25261f16f61825d61812d61808d61806d61805d61804d61458161408161078d61056d61316d60867e60967260a37260927260807260467d60535d60357f,
    0x63457063456463446063445463437063636463436063635463435063634463427063626f63426063525463524463417063416463416063415463415063414463405063704463025d62d14d62957f62957362b45262a35262a27f62926362b16f,
    0x65001f65001e65001d64856f64856364847f64847e64a35264925264817364b16f64805264426d64418d64415d64414d64401d63f57f63c57363f45263d36f63d25263f17f63c17363c16363c05263826f63826e63917f63817363914f638143,
    0x66858166456366447366445e66435e66425e66057366026365956365b47265a37265935e65826e65925265817265915e65807265428d65416d65415d65414d65401d65026f65315f65015e65015d65214f65014e65114d65013f65013e65213d,
    0x6a018169c15d69467d69458d69445d69435d69425d69405d69018168c58d68c47d68c46d68c34d68c24d68c14d68c04d68838168048168018167c13d67447d67438d67436d67435d67423d67403d66c38d66c27d66c26d66c25d66c24d66c02d,
    0x6bc01d6b867e6b856f6b84736b84726b84716b845e6b815e6bb14f6b814e6ba14d6bb13f6b813e6bb13d6bb12f6b812e6bb12d6b801f6bb01e6bb01d6b74816b74716b05816b018d6af07f6af05f6ae04f6ad03f6a80816a478d6a426d6a0281,
    0x6d44816d428d6d401d6d016f6d315f6d014f6d013e6d001f6d001e6d001d6cc7816cc56d6ce3816cc1816cb4816c92816c81716c44816c427d6c516d6c415d6c514d6c401d6c16716c05816c23816bc5816bc27d6bd16d6bc15d6bd14d6be13d,
    0x6f81726f81716f427d6f516d6f514d6f613d6f401d6f34816f34716f12816ec3816ec28d6e917f6eb15f6e813f6e801e6e47816e74716e41816e03816e027d6e218d6e01816e116d6e015d6e114d6e213d6e001d6dd2816dc1816db4816db471,
    0x70914d70913f70813e70a13d70801f70801e70801d70457070456470416070415e70415470415070414e70414070413e70613470413070412e70512470402070401f70401470078170056d7001816fe3716fd2816fa56e6fb4636fb4626f8173,
    0x72168172017172007171c67271c57371c57271c57171d26371d26271d26171c06371867d71028d71316d71114d71213d71001d70c57e70c57270c56e70c16e70c15e70c14e70c13e70c12e70c01f70816f70816e70916d70815e70a14f70814e,
    0x73816073915473815073914473807073b06f73438d73427d73426d73425d73424d73412d73407d73406d73405d73404d73348173308172e37272d27272c17372c17272c17172c07372c07272c07172868d72457e72645e72635e72415e72405e,
    0x74006e74006d74006374004f74004e74004d74304374203f74003e74103d74003374002f74002e74202d74102373c56373f45273e35273d25273f17f73857073856473846073845473836073b35473835073b34473827073a26473825073a244,
    0x74c56474c46074c45474c37074c26074d25474c25074d24474c17074c16474c15074c14474c05074f04474847d74838d74836d74835d74823d74918d74916d74915d74901d74428d74417d74415d74514d74613d74017f74017e74017d74006f,
    0x75c25d75c17d75c16d75c14d75c01d75828d75917d75815d75914d75757f75557375745275635275717f75417375405275027f75027e75027d75216f75016e75216d75016375214f75014e75014d75314375213f75013e75013d75213374c570,
    0x76805276427f76427e76427d76516f76416e76516d76416376514f76414e76414d76714376057076056476047076046476037076236476035076234476026076225f76124476017076016476015076014476005076304475c38d75c27d75c26d,
    0x77816377457077456477446077445477437077636477435077634477426077525477425077524477417077416e77405077704477067d77058d77025d77318d77314d77313d77301d76c28d76e17d76c15d76856376b45276937f769252768173,
    0x78b45478837078a36478926478826078817078816478807078906478438d78427d78416d78415d78414d78401d78028d78317d77f57f77f57377c46e77e35277d25277f17f77c17377c05277827f77827e77827d77825377816f77816e77816d,
    0x7a036e7a236279857079856479847079846479846079b45479837079836479827079826479826079925479807079906479427d79156379347279145e79345279237279127279125e79125279007278c26f78c26e78c26d78847078b464788460,
    0x7ec28d7ed14d7e917f7ea14f7e814e7e914d7e813f7e801e7e47817e34817dc28d7d917f7db15f7da14f7d801e7d47817cc18d7cb07f7cb05f7ca04f7c802f7c40817c078d7c026d7bc2817bc1817b815d7ac1817a813d7a056e7a05627a0472,
    0x82817282807282478d82426d82415d82514d82613d82401d82067d81c56e81c56d81c17281878d81816d81b02d81638181608181068d80e45e80e35e80c25e80c05e80968180927180807180467d7fc28d7f816f7fb15f7f913f7f801e7f5281,
    0x85808185428d85514d85015f85214f85014e85114d85113f85001e84818d84b02d84717e84417284505e84701e84002f84302e84302d83c02083f01e83c01483808183407383317083016483007083006483006382c67d82856e82b47282a372,
    0x858181
  ])
  | 8 => (19, #[
    0x80de101902031840600e0be101502029840500c09e101102021840400a07e100d020198057000ac8045c000b200160002a80054000a20014000268004c0009200060000a800080000a00000,
    0x86a810d4021a204280084e8109c0213204260084a810940212204240084681060020ba04170082c81058020aa041500828810500209a041300825e104b82096840800a0fe101d0203984070,
    0x10280204d040980812410100201fc483a08070100c82018c40280804f10080200c040178468008ce81160022ba0457008ac811200223a04470088c811180222a04380086e810dc021b204360,
    0x168a420e0051ba08370146c820d8049af0a354146a420d4051a208280124e8209c0493208260104bc249504929092501248820900491a08180162fe205d040b80b16f102c82054040a20b143,
    0x1a0fe301f8603e8c074180e630100681f8e03e1c07a340d060180c02f1c05c3c0b460120868010ce8216004abf8857410ae6215c042b78856410ac6212005a3a08470168c821180422f0b454,
    0x202a04051080a010134202604049080380c68018ce830e0061ba0c370186c830d8061aa0c280184e8309c061320c260184a83094061220c240184683060060ba0c173182e0305bc60b70c080,
    0x282a05853ca0a214143280405007ca00f1401d2802841a00833f1167422ce4415c08ab79056420500449d0893910270224c840980892a11250224884060080ba10172202e04059080b010154,
    0x302c860540c0a2181403627e604d0c03018054300a451a00a33a15480288e8511c0a23214460288a854a00a13a14270284c850980a12a142502848850900a11f1423d282e0505bca0b214163,
    0x3a2fe705d0e0b99c170382de70590e0b19e1403a27e704d0e0101c01e3802861a00c33a1857030ade61590c2b199380346e860dc0d1b219360326bc68d50d1a91835032300605d0c0b81b16f,
    0x424a48094100c02317f402e8805c118b7a0164402a08051118a1a0060400a880148e3401c6743870070dd0e1b81c364386c070d50e1401c274384e070990e1301c254384a070938e1269c180,
    0x4e2e0985bd38b72716d482c89058d38a02513f4e27c984f5289a240204803e90079200ea401440d00819d102c02157f40ae8815cd02b82056f40ac88158d014021274404e084991013021254,
    0x50500a49d1413829264504c0a495149292824050300a05d140b82b16f502c8a0181402a2805248d00919d121c024374486e090d9121a82434448500909d12139a4270484c890981212f2425d,
    0x586e8b0dc161b22c280584e8b09c16137ac26e58300b45fd60ba2c173582c0bc57d60aa2c1505c29eb053968a6ac14458280b04fd609a2c0205803cb005143402867450ae0a15bd42b228563,
    0x648c0cd1799a2a30380646e8c8dc999b832364606c0c0a01893a31272604e0c0981892a31170602c8c058d804030074600e4b1a01633a2c58058ae8b15c162b22c480588e8b11c162322c380,
    0x6e2bed0579a0aeb7154682a0d853da0a73514d68288d0501a89fb413e6c27ad44d1a0103401f6803cd0075a00a3068066cfcc59d18b393057062adec1591824033474668e6cd1c99a38b0470,
    0x768e8ed1c9c23038380746e8e8dc9c1b838180702e8e05c9c0b838080700e8e01c9a3403467468ae0d1591a24034474686e0d0d91a1403427f684fcd09f5a0b83416f682dcd45b5a0b234160,
    0x10c60200ba4017280101001d20039c0072800e2f1a01e33f3c67d7a2c0f4579e0aa3c060780bcf0151c3403967472ce4e15c1c2b238480
  ])
  | 9 => (13, #[
    0x5702b245c02c81600aa054028814009a04c024806002a0080028000
  ])
  | _ => (1, #[])

def offsetTable : Nat → Nat × Array Nat
  | 5 => (7, #[
    0x0,
    0x101c3060c18305080808000000000000000000000000000000000000,
    0x1a3460b162c58b162c58b162c58b162c58b162c58b162c58b1624488,
    0x224489122448912244891224489120408102040810203c78e1c3870e,
    0x22448912244891224489122448912244891224489122448912244891,
    0x22448912244891224489122448912244891224489122448912244891,
    0x3264c993264c983060c183060b162c58b162c54a952a54a94264c991,
    0x3264c993264c993264c993264c993264c993264c993264c993264c99,
    0x4489122448909f3a74e9d366cd9b366cd993264c993264c993264c99,
    0x50993264c91224489122444891224489122448912244891224489122,
    0x72e5cb972e5cb972e5bb566c58b162c58b162c57ad56ad5ab56ad5a9,
    0xa13e7cf9f3e7cf9f3a74e992a4c98f1e3c78b0e0c183060c17ef5db9,
    0xb972e5cb972e5cb35ab56a952a54a94a952a54a952a542850a142850,
    0xbd7af5db972e5cb972e5cb972e5cb972e5cb972e5cb972e5cb972e5c,
    0xbd7af5e
  ])
  | 6 => (11, #[
    0x0,
    0xc0180300600801002004008010020040080100200400801002004008010018020040080100200400000000,
    0x100200400801002004008010020040080100200400801002004008010020040080100200400801002004006,
    0x400800f81f03e07c0f81f03e07c0f01c0340600a81402203c0780f01e03c0780d0180300580901002004008,
    0x780e81d0390720dc1b03606a0cc190310620c4188310620c4188310620c41882d0580a41382504a09411021,
    0x8c1182304608c1182304608c1182304608c1182304608c1182304608c1182304608c10c218430861001e83c,
    0xa61482804e09a1302584a0941282404808e1182304608c1182304608c1182304608c1182304608c11823046,
    0xbc1782f05e0ba1702d0580ae1582a8540a81502a0540a81502a0540a81502a0540a81502a0540a81502a054,
    0xdc1b83706e0dc1b83706d0d81ac350680cc198330640c8188308600be1782f05e0bc1782f05e0bc1782f05e,
    0xe21c43806f0de1bc3786f0dc1b83706e0dc1b83706e0dc1b83706e0dc1b83706e0dc1b83706e0dc1b83706e,
    0x1001fc3f87f0fe1fc3f07e0fc1f43e07b0f61ec3d87b0f41e43c0770ee1dc3b0750ea1d0398720e21c438871,
    0x144288510a11402784e09c1382704c09612623c4608b114228448891122244488610a2144108110020040080,
    0x1742e85c0b716c2d4598b21602c0570ae15a2b0550aa1542a8550aa1502a0538a614828c518a314628c518a2,
    0x1ca388710e11c03786e8db1b43606b0d41a4340680d019e33c678ce19832c650c9192324638c41822f85d8ba,
    0x23c46c8d11622a4488810e21c4388710e21c42c8510720c410811001fe3ec7c8f71ee3d8798f21de3b0750e7,
    0x2604c0981302604c0981302604c0981302604c09812d2564a49312424848c91923246488911222424808f91f,
    0x27c4f89f13d2784f09e13c2784f09e13c2784f09c93826c4d49a93526a4d49a1322604c0981302604c098130,
    0x284508a0941282504a094027e4fc9f93f27e4fc9f93f27e4fc9f93e27c4f89f13e27c4f89f13e27c4f89f13e,
    0x290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a414628a510a2143,
    0x294528a514a294528a514a294528a514a294528a514a292524a4949290520a4148290520a4148290520a4148,
    0x29c538a614c298530a614c294528a514a294528a514a294528a514a294528a514a294528a514a294528a514a,
    0x2b0560ac1582b0560ac1582b0560ac1582b0560ac1582b0560ac1582b0560ac1552a4540a714e29c538a714e,
    0x2cc598b31662ca590b21642c8590b21642c8590b01602b8570ae1582b0560ac1582b0560ac1582b0560ac158,
    0x2d85acb596b2d65acb596b2d65acb596b2d65acb596b2d45a4b49692d25a0b41682d05a0b41682d05a0b4167,
    0x2ec5d8bb1752ea5d4ba9752ea5d4b99712e25c4b89712e25c4b796f2da5b4b696d2da5b4b616c2d85b0b616c,
    0x314628c5189310620c418831061cc31822fe5fcbd97b2ee5dcbb9772ee5dcbb9772ec5d8bb1762ec5d8bb176,
    0x328650ca194328650ca194322644c8991320640c819031e638c718d31a634c698d31a634c618c318630c598a,
    0x336668cd19a334668cd19a33065ccb99732e65ccb99732e65ccb99732e65ccb994328650ca194328650ca194,
    0x3506a0d41a83506a0d41a83506a0d41a83506a0d41a834c690d11a033e678cf19e33c678cf19e33a674ce99d,
    0x3506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a83506a0d41a8,
    0x3646c8d91b23646c8d91b23606c0d79ae35c6b0d59aa3546a8d49a83506a0d41a83506a0d41a83506a0d41a8,
    0x37c6f8df1bd3786f0de1bc3786f0de1bc3786ecdd9ba3746e0db1b53686ccd91b23646c8d91b23646c8d91b2,
    0x39872ce59ca390720e41c838e71ce39c738c718e31c638c718e31c5388710e21c3384704e01c037e6fcdf9bf,
    0x3aa754ea9d53aa754ea9d53aa754ea1d43a674ce91d03a0740e81d03a0740e79cf39e734e69cc398730e61cc,
    0x3c4788f11e23c077cef1de3b876ced1da3b2760ec1d83b0760ec1d83b0760ec1d83ae75ceb9d73ac754ea9d5,
    0x3d87acf51e83d0798f31e63cc790f21e33c4788f11e23c4788f11e23c4788f11e23c4788f11e23c4788f11e2,
    0x3ee7d8fa9f53ea7d0f99f33e67c8f91f13e27c4f89f13e07c0f81f03e07c0f81f03e07c0f81f03dc7b4f61ec,
    0x4328590aa144208390720c41682d04a0840e80d00a003fc7ecfd9fb3f47e8fb9f73ee7dcfb9f73ee7dcfb9f7,
    0x49292524a4648a90d20a4148290520a414808fd1e23b4748d91aa324608b91722e45a8ad142254468850e21b,
    0x4b09612c2584b09612c2574ae95d2b2564ac9592b2564ac9592b2564ac95929a5149e9312524a49492524a49,
    0x4ce999332664cc999332664ca98d31a614c09812fa5f4bc9712da5b4b09612c2584b09612c2584b09612c258,
    0x4d89b13626c4d89b13626c4d89b13626c4d89b13626c4d89b13626c4d69ad3526a4d49a93526a4d099d33a67,
    0x510a1d43a8750ea1d43a86508a094027d4fa9e93ca764e69cd39a724e49c93926f4dc9b53626c4d89b13626c,
    0x526a4949291522a4548a91522a4548a91520a414828f51ca3946a8d51aa2d4528a512a2544a89512a2544288,
    0x542a7d4e29c538a714e29c532a614aa95528a514a294528a514a294528a514a294528a514a294528a514a294,
    0x586b0d61ac3586b0d61ac3586b0d61ac3584b055fabd576ae15aab255eabd562a954ca99532a554aa9552aa2,
    0x5a4b45682cf59cb3965aca592b2564ac9590b1d63ac658cb1562ac558ab1562ac558ab1562ac558ab1562ac4,
    0x600bfd7fafe5fcbf97f2fe5fcbf97f2fc5f4be57caf85f0bdd792ee5d6bad73ae45c2b756e2d95acb596b2d5,
    0x648c8d91322644c8990b20640c819031c638c658c318628c458730a610c1582304608c1182304608c0980b01,
    0x6d4da5b43686ced89af35b6b6d5daa35169ad31a4b4668ad11a1b43686cfd9db37668cc59732b656ca192b25,
    0x6f4de9bd3796f2de5bc3776eedd1b8b716e2dc1b7b6f6dedbdb7b6f6dedb9b736e6dcdb9b636a6d4da9b536a,
    0x758eb1d5bab756ea1d23a2740e79ccb9772ae55c9b92720e39c638a710e0dc0b806fedf9bf37e6fadf1bdb7a,
    0x782f05e0bc1782f05e0bc1782f01e03bd776ee5dbbb776aed1da3b2764ec9d8bb075eeb9d63ac758eb1d63ac,
    0x782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1,
    0x782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1,
    0x782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1782f05e0bc1,
    0x7a8f45e63ca794f29e53ca794f29e53c9792f21e3bc778ef11e1bc2782f05e0bc1782f05e0bc1782f05e0bc1,
    0x7feff9ff3fe7f8fddfabf57e2fc1f7bee7dcfb9f5be67c8f81efbde7baf75eebdd7b2f61ebbd67aaf55ea3d4,
    0x86b0d619c338670ca18c3085f0be17c2f85f0be1742e85b0b616c2d8570a61241f83504e0740b80f01a02c03,
    0x89d13a2744d89111e23c4688d11a2344688d1162244187d0f21d43886f0da1b43586b0d61ac3586b0d61ac35,
    0x90720a40c819031fe3f47c8f71de3a4728e51ba35c698d11a233c678cf19631c618bb16a2c4558a514227c4e,
    0x9632be574ad95b2b2554aa95129a52ca594b29251c9d93b2764ec9d93b2764d49992b24a4949191b22a43c84,
    0x9692d259cb39672ce59cb39672ce59cb39672ce594b29652c658cb19632c658cb19632c658cb19632c658cb1,
    0x97b2f65ecbc9772ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4b996f2da5b4b696d2d65a4b4,
    0x99f33a674ce99d332664cc999326644c798f31e63cc798930e614c198330660cc198330660cc097f2fe5fcbf,
    0x9b736e6dcd99b13626c4d79ad35a6b4d59ab3566acd59ab3566acd59ab3566acd59a534a694d29a534a694d2,
    0x9c9386704df9bf37e6fcdf9bf37e6fcde9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766e4dc9b736e6dcdb,
    0x9d93b2764ec9d93b2764ec9d93b2764ec9d93b2764ec9d93b274ce99d33a674ce99d339a72ce59c9392724e4,
    0x9ed3da7b4f59eb3d67a4f39e73ce79cf29e53ca794f29e53ca794f29e53ca784f09e13c277cef9dd3b676ced,
    0xa0d41a83505a0b41281d03a0540a81502a0540a805009ff3f27e4fc9f93f27e4f99f13e27c4f89ed3da7b4f6,
    0xa2945289512a2544a89511a2143e87d0fa1f43a86d0ca1742e85d0ba1742e85d0ba1742e85d0ba1742283d06,
    0xa3746e8dd1ba3746e8dd1ba3746e8dd1ba3746e8dd1ba3746e8dd1ba3746e8dd1ba3746e8d51aa2f45e8a514,
    0xa4347a8ed1da3b4768ed1da3b4768ed1da3b4768ed1ca3746e8dd1ba3746e8dd1ba3746e8dd1ba3746e8dd1b,
    0xa6f4ce99d30a5f4be9752ea5b4b696d2da5b4b294525a4b49692d25a4b49692d25a4b49692d25a4b48690d21,
    0x1516a2543a8750ea1541a81502a053ea7d4ea9d537
  ])
  | 7 => (13, #[
    0x1800b405a02d01600ac04e027011808c03e01f00f807c03e01d00e006c02a014009804801800b005002400e0070010004000000,
    0x3c81d80e807403781b40d806b033818c0be05f02d815c0ae053029814c09804b024812008c045022811408604001e80e406e034,
    0x52828c14009d04d025c12e09704a825012008f047823c11e08e0460230114088042821410a084042020010007c03d81ec0f607b,
    0x72838c1c40e207103781bc0de06f03741ba0dd06e836c1b60d906c834c1a40cc065031417c0ba05d02d41680af05782bc15e0a7,
    0x9e04e827013809b04d026612e09704a4252127091047c23e11a08b845c224111086043021210708284082040fa07883bc1da0ea,
    0xbc05e02ee1770b805bc2da16c0b505a82d01660b205802bc15c0ad05642b01570ab85502a81510a7053428a13f09f84f427a13c,
    0xd806b83581ab0d5069c34e1a40d1067c33e19c0ce066c3361940c9864431e18f0c606283101840c1860430017f0bf05f82f617b,
    0xf507a03cc1e50f207843c21de0ee87683b41d70eb07583a61d30e9874039e1ce0e7071c38c1c40e2070c3821bf0dd86e43701b3,
    0x114089043e21c10d086042e21610b084c426213108084042020d106883441420a104882040c2030fe07e83f21f70fb87d03e41ed,
    0x134898c4c426113009684b425a12c095c4ac25512a894c4a424c1258928492248123890448023e11d08e046c23311788bc45822a,
    0x14a8a545282931498a3451828b1458a1c50e2871438a1450a27f13f89e84f227913c89e44f227913b89d44ea26f13709b84da26b,
    0x15f8af05722b615a8ad05622b11578ab45582ab1550aa45502a71538a945462a31518a885442a11508a8053c29c14d8a68532297,
    0x1700b7c5bc2dd16e0b6c5b42d716b0b545aa2d41698b485a42d11680b3c59c2cd1660b2c5942c91640b1c58c2c31610b045822c1,
    0x1988cc065c3221908c8063631918c0c5062230e1870c3861a30a1830c045fe2fd17c8bd05e62f21760ba85d22e81738b985ca2e1,
    0x1c68e307143891c48e2070e3821c00df06f03741b70db06d03631b08d746ae3541aa0d406943471a30d0867a33b19d0cd4664331,
    0x1df8ee876a3b11d80ebc75e3ae1d68eb47583ab1d48e9474a3a41d10e847403a01d00e7c7383981ca8e507243911c80e3c71c38e,
    0x21690b0852427211105c8284122089044820410207903881a40b203901480a4051ff0fe87e83f31f90fb47d43e51ef8f507a03ca,
    0x23291888c245c22d91648ae45522a114c8a2450224911c88a442221110888244021f90f487843b21d90e887243621a10cc864432,
    0x2461228912488243921890a48424192048fe47e23e11f08f647a23a91d48e047023811bc8dc46e23711b48da46c23511a48d2468,
    0x262130c9844c2261130097e4bc25d12e89744b2252928c9444a224e927493849c24e127093849b24d9268930495248923c91e48e,
    0x2841418a0a50228013fc9fc4fb27b93d09e64ef27793b49da4eb273138c9bc4dd26c13609b04d726b13449a04cf266932c9904c7,
    0x2a61518a8853b29a94d4a6852e294149ca4c5242911488a4051f28f9474a3a51d28e145ca2e51628b1454a2a514287942ca16509,
    0x2d21678b3a59a2cb9650b2258d2c4160cafc5792b995c0adc56e2b615a4ad25692b495a4ad25672b29590ac65622ae155caa254f,
    0x2f29788bc45e02ef1770bac5d62e89740b9e5ce2e6172cb945c92e19708b825c02dd16e4b665b22d896c0b545a92d4169cb4a5a5,
    0x32098e8c7263231898bcc5c62b3141888c4261f30c985cc2c6143091830c126073029808bfa5fa2fd17dcbe65f02f817b4bd05e5,
    0x3561a9cd4a6a43519a70d326933479a34d186853419a00cfe67d33e19d8cd866c334199ccc866132e9960ca664e324991cc8a643,
    0x37e1becdf26f23779bb8dd86ea3751ba0dc26dd36d9b64dac6d13671b38d966c73629b0cd826c035e9adcd686b23589abcd5a6ac,
    0x3af9d74eb87593a99d44e9e74e3a39d14e8474139f9cf8e6e72e3971ca4e4a72038d9c6ce3071838c1c58e2870c3851c20e0a6ff,
    0x3e31f0cf7c7b93da1ec0f5c7ae3d71eb4f507a13cd1e64f2478f3c49e1cf0a7843c11e04efe77a3ba1dc0ed876a3b49d9cecc765,
    0x435a1990c285c42b214509884742220fd07483541820ad04c82140e205101c8094032004ff87f63f81facfcc7e13ec1f4cf9a7c9,
    0x45622b11588ac453229914a8a044f226d13689b44ca26513289944ca26513289944c225d12c892446a22510888143e21dd0e8870,
    0x45d22e91728b745b22d916c8b645b22d916a8b545aa2d11668b3459a2cd1668b3459a2cd1668b345722b515a8ad456a2b11588ac,
    0x47423891c28e046fa3791ba8dd46ea3751ba8dc46d23691b48d646923411968cb465a32d1928c9464a32118c8c446123011808bb,
    0x492a48924291e48da46d23691a48d246122e91448a2445216909483a41920c90148023e91f28f847ba3d91ea8f347923b11d68e9,
    0x4b325992cc9654b2a5792ba95b4aca5652ac9544a9253529894a4a5251528293e49da4e126c933499a4c125e92c49624a5250925,
    0x4d626a53509a74d2a6913449a04cca65d32a9934c726353169894c226012fa97a4bba5d52ea9724b925bd2de96c4b625b12d2969,
    0x4ee27693b09d74ea27493a29cf4e6272538e9c64e2a7113889bf4dfa6f937c9ba4dd26e93729b74db26d936a9af4d7a6bd35c9ad,
    0x51628b1452a265122879438a1c50da86d436a1650aa849420a0b5042819408a0250027ed3f29f44f7a7b93da9e84f2a7913c29df,
    0x528a9454a2a50526292d494a49524292148ea46522a911488a4252028f947ca3d51e28e546ea3551a28cd462a31518a8c145ca2c,
    0x53ba9dd4eaa73539a9cd4e4a6d53529954c6a62530a9854c2a6152fa9754b8a5c52da96d4b4a5952ca9654b0a5652aa9514a6a53,
    0x5542a9d548aa45522a89540a9e54f2a7953ca9e54caa65530a97549aa49524a915482a3d51aa8a543aa19508a8053e29f14f4a79,
    0x56eab695b4ada56cab655aead656a2b515a4ad05672b29590ac8561ab0157cabd55daae9572ab3558aabd55caad555aaad554aaa,
    0x590ac7d634b1858aac4d61cb0b5852c2160eb075822c11608b01580abf95fcafe57eabed5f2af55772bad5d4ae8570ab7d5bcadd,
    0x5b02d7d6beb5d5ae2d6d6b2b595acad4d6a4b505a82d2d690b465a2acf9678b3a59cacdd66ab2f5972cb5656b29593ac9964ab25,
    0x5c8ae39716b8a5c4ae25712b895c42e1d70cb855c0adf16f6b7a5bcade16eeb765baadd16e2b705b52da16d0b675b2ad916c4b61,
    0x6013009800bfb5fbafd57debe45f12f897c2be05efaf797b8bdb5ed2f697a8bd05e62f1177ebbc5dcaed5756ba85d22e6d732b95,
    0x61cb0e5872c3661a30c9862c3061730b584cc266133091842c1f60e306d834c1860bb05982ac1560a304d81ec0d606302d816c03,
    0x63c31e18f0c78639b1cd8e4c7263631a58d2c6763331918c6c62630b1818bcc5a62bb1518a2c506283129890c4362130f587ac3b,
    0x66ab33d992cc4661b309984cc06603301980cbf65f32f1976cb3659b2b1958ca5651b27992ec90647321990ac8264031f98fac7a,
    0x69bb4b9a56d2768f346da36d1768b344da1ad0b684b421a0ed02680b4019fecf967c33dd9eccf0677b3a59d0ce6672b3819bacda,
    0x6d0b66db36d966cab64db24d916c83629b12d876c0b5fdafcd7d6bb35d5ae8d6f6b635a5accd616adb555a9ed496a234fda7ed39,
    0x70db865c2ee16707382dc0ae02700b7fdbf0df66f837a5bccde46edb761ba8dcb6e4371db86dbc6dcb6d9b64da96d3b699b48da3,
    0x74039d1ce4e70737b9a1ccce6072db961ca6e4d723b905c76e3b71c38e1c6ae3571938c9c64e2f717b8b1c58e2c714b899c48e22,
    0x7843c19e08f0077fbbe1de0ee97733b89daeed47683b1dd86ec2760bb01d7eeb9755baa1d44e9f74f3a6dd34e97748ba41d10e87,
    0x7b83db9edaf6a7b43da1ed0f687b43d9dec2f607afbd79eb0f577ab3d39e8ef4379fbcf5e70f377983cb1e4cf217903c75e36f14,
    0x819c0b604f02180dc04a0190077fe3fddfe2fea7f23f7dfb2fd07e4bf21f84fba7dc3ec5f4af9f7cc3e45f1af817bebdddeeaf75,
    0x84bc25a12d094849424612108f847c23211508884041f60f307983c41de0ef07783941b60cf06182ec15e0a304c823c11207d039,
    0x85a42ce1670b1858c2c21610af857c2be15b0ad85642ae1550a9853c2961490a3851c27a13d09d84ec27613b09b84cc266131097,
    0x872c38a1bf0dd86dc36a1b10d886943421a10ce867432e1910c6862430e1830be85ec2f21790ba85cc2e61730b985cc2e61730b9,
    0x894449a24b11f88ec45e22d11588a444a22310e886c41e20d10487f43f61f90fb87ac3d21e70f3879c3ca1e10ee87643ae1cf0e7,
    0x8b1c58e2c51618afc57e2bf15d8aec5662af1558a9454229f14d8a5c52e28913d89ec4ea27113389944c226113089844b625b12a,
    0x8d0468233f19e8cf467633b1978cb46523251908c7462630f1868c045f62f717a8bc45da2e51728b7c5ba2dd16b8b545aa2cf166,
    0x8e8474239f1cd8e6472a3931c78e3471a38b1c48e1c70a37f1be8dec6f236f1b78db46d23651b18d846ba35b1ac8d4c69e3491a1,
    0x91dc8e2469230914c86642720e905c81a4032008fdc7d63eb1f08f6c7a23cf1e18f047823bd1de8ee47723b91dc8edc76a3b31d5,
    0x93849c24df26f936c9b64d7269934c99a4c926293049764bb25b92dc95a4ab254929c9464a1250927c93a491246922490647f23d,
    0x9524a7253329894b4a56527292948ca4251d28e946ca3651b28d9464a2a511283941ca0a4fb27b93d49e24ef27693a49ce4e5272,
    0x9a44d1a67f33c99accce65f32d996cc9e62d311987cc166032f29764b9e5b72d59684b0e57b2b795acac255f2ac9554aa65532a6,
    0x9cc4e5a72b3939c9ce4e7233909c84e3671738b9c5ce2670f3869c24e0e70337f9becde66f13759b9cdc66dd3679af4d5e6ab34e,
    0x9f4cf8e7c53e19f04f6e7ad3d39e84f367953c59dfcee67673ad9d64eae7573a99d44e9674139f9cece7273939b9cdce6a735399,
    0xa22d10287b43aa1b50c685d42ea15509e849424a105076835414a09504281d40ca03d01680b4009fecfda7e73f29f94fb67d73ea,
    0xa56d2b294d4a5a51d27693749aa4cd24e92548ca45d22a90b482a3fd1f28ef471a35d1968bf45ca2dd16a8b545aa2b5152899449,
    0xa8fd466a2750da83d412a07503a8154069f54f3a78d3be9d34e7a7253869b34d6a6953369954c9a62d30a97f4bea5d52d69654af,
    0xac25602afd576aba55c2adb56aab3d58eabd55baac555eaad555aa9552ea93547aa35506a8153fa9cd4e2a65530a97d4aaa4f524,
    0xaf957bebdb5eaaf1d78abb95daaec575eba35ceae6d732b915c5ae256feb795b7ad8d6aeb4b59face5672b37599ac95642b1b586,
    0xb39d9c6cd7669b34599ecc3661b2e5962ca964eb24590ac79638b1ad8cec5962ab145896c4361ab0c5856c23607b00d7fabf55f5,
    0xb665b22d8b6c4b625b12d896bfb5f5af6d796bcb5ddad6d6b6b5b595ac6d556a8b515a82d33697b48da2ed0f684b3d59e6cf1678,
    0xb85dc2ae11708b83dc16e0b705b82dc12e09704b825c12e09704b825c0ee07703b81dbfadf36f3b76dba2dbd6d9b685b3ed9f6cc,
    0xb9e5ceae6d732b985cbae5972ab955ca6e47721b8edc66e2f716b8adc52e29714b8a5c52e27711b88dc46e2170fb86dc36e1b70b,
    0xbce5e66f2d793bc9de46f1d78ebc75e36f15789bc3de12f0177ebbbddcaedd762bae5d6eeb7758babdd5ae9f74aba55d22e8d73f,
    0x2f4379e
  ])
  | 8 => (13, #[
    0xe7072036e1b50d2067831818a0bc05d82dc16c0ac855c29e13a09684742080ef070834816a0a004982080e606402580dc054000,
    0x15e0ae055a2ab1508a7c5322971468a2c50a28313e89f04e627213489984c025e12c09584a025012108d441820a0fb87c43c21df,
    0x1d30e9073c39b1ca8e146fc3781b88d7c6b034219e0cd864231a18b0c4061830617e8be05de2ea1730b845b82d71698b3858a2c0,
    0x25b12c494e4a124e926890c48423b11c48d846422f116089e44d22190fc85a425210107082240b1fd0fcc7d83d61e90f307863ac,
    0x3509a30cbc6553229900c4860f2f09760ba25b92d215e8ae25682b11580ab054e295149ca3251328013e09e44ea26f937099e4ca,
    0x3ec9f3cf987c93e31f08f7a7b63d61e8cf367943c39df8eec76c3af9d58e9a74539b9cb8e4871c3899c34dfe6e83719b48d8c6bf,
    0x47623691a68c246022d513a873438a1c10d0865428212d07683941c20d504281b40b203d0128054009ffcffc7f03f69f94fbc7dc,
    0x4fb27c13ce9e14e727313949c84dd26c935a9a64ce26553209894c1a6012ea9724b5a5a12ba9594a9254528891b48c24191fe8ef,
    0x5812bf15d8aea56aab4d596ac955c2ac9560a9e54e2a5551ea8c54029ed4cea6152ba941498a4a51f28e944aa1f50ca8494169f9,
    0x60e3041814bf85f8afa97a6bd05e52f0d75abaa5d42e69728b905c52e19702b785b92db96d8b625b02d6d6b2b4f5a7ad0562eb15,
    0x71ab84dbf4dc96dfb6bdb4ed8e6bab529a80d3668eb4159b6cd1663330197ccb66563221908c75637b16d8a6c4d62330ed872c33,
    0x7bf3de9eecf6d7b5bda5eb6f577a83d25e86f34798bcbde5af1f789bc29dfeef6775bb75da8ec475ebabdd2ae8e74239fdcd6e3d,
    0x85842b61470a184b425210f07e83e41aa0c9053828c0fa07103780f4051fd2fe87f33f51f9cfcc7dd3ed1f5afa77d2be75f30f83,
    0x8d4c66632518e8c545e22e51698b045762b114289d44ce25912688f442a20f103877c3b21cb0df86dc36219d0ca860c2fa1750b4,
    0xa07cfea79b3c39dece8a71b3609ab4d4266f32297bcbb65cf2d295bca2a50127c936499e4ab24e91c48d246722a90ac7aa36f1af,
    0xae0d6b6b4d5a4acfd61ab0557fabed5bead7569ab2d542a8d53ca98d48aa3750da8253da9e34dca65d27a92d47ea34d0fe86b42d,
    0xb775ba6dc76ceb665b0ad5b685b2ad952c8d61cb0d581ec035ffaf55792bc15deae85726b8f5c5
  ])
  | 9 => (11, #[
    0x23fc377eeed1b43205bea7526a0538a6049f8fd1621a815000
  ])
  | 10 => (6, #[
    0xa80
  ])
  | _ => (1, #[])

def childTable : Nat → Nat × Array Nat
  | 5 => (19, #[
    0x54038c40b1701e3612c64038b40f148162412c422988057100962112c3825880570f0a61914c1c03814070a0161002c1203854130681e1412c20258304b042280a03c1209814170422804350,
    0xac03978532d0965a13c6a2b958131502e5103c9c03944131702e4a01c620b938132500e4615c8a298f8171e8264105c72099184b1d00e3c03c82058f80f228964201c7a078e40b1601e3512c,
    0x3e22a78454ea259a8072f09e7102cdc039440f3b0967201cda039744f348165203cca258944b2e89e4d01cb227924072d89e5502ca40797c4f2801e6112cb84994c932812e5e13c
  ])
  | 6 => (23, #[
    0x800c00c45b01e0ae02c16c0700b80a01b01f89e03b01c06a2b80744f00b00e03423c0642980bc4f01580e02713c0460380745b00c89601c23c0322580581b00a82e01603c0260380440f00601e00802c00c0380140700303600505c,
    0xec2b81c44f03080e07615c0e22781ac4b0388b606f15c0d62581b4d70358b606705c0c207819c1703083605e14c0b627815c4b02780e05e15c0b62b814c4b0138b605715c0a625813c1701183604914c08e27810c070241b0044160,
    0x14c0d82980705101609e01c1420b82700b04d82e09603c1360b82680b04b02e09601c11c0382480704883608d05c1120b82141b04501e08a01c10c0782180704103608105c1040382040703e01e07901c0200b81d85303789606701c,
    0x19c05832c0706300e0c305c17a0d82380f04901e0bb05c16c0d828c1704f02e0cf05c1988b82cc170568360cb06c18c0783141b06180e0bd01c1760382d80706182e0bd03c1700b82d4070581ae0ae03c1560b82980f05582e0ab01c,
    0x2220b80181b0879b00045602104784140f0808360f505c2084c04009007e82e0f102c1dc0383ecd487a1210d403d1a625a3c41b07682e0e901c1ce0b83841306c0180e435c1c40783701806e1b00d84601aa0983441706b01e0d203c,
    0x2680584640f09e82e12802c23a078500d70a692601304c290ac0040d80a203014006c2780b84ec1b09a82e12906c2624780240f0041b010426025c0d84a81709301e00c23c0186c04801808e03611805c228ac04244800282e10d06c,
    0x2c22983c40707680e16116c2ba2583b8070b10a60f201c2ba2983a4070ad03615905c2b40980180f0ac82600503c2a60b8551170aa2b01503400806c00a0d401c1a813103c2480585201b08b01611404c28a0d84840f08201614106c,
    0x33a0d8660930ca8a60f601c0500986411806880e18d13c3120383500f0c282e18103c250058418070bf12610201c0700985e4570b089e15a01c2f22983f4070bb1260fa01c0400985c15806a80e16e14c2d22785940706801e020360,
    0x3782c0444070e21261c114c0800986f1180dd0a61b513c3642586a4070dd0ae1b515c35c2586345b0d90ae1ae12c3520b86241b0cc0ae17e14c2160586545b0c80b617015c1b00585b45b0d28b616915c3420d8594170d289e1a101c,
    0x39a0d8448070f90a61f214c3de2b87b4d70f282e1e914c3d88b87a8570f2a2e0e602c2e0ac0384070b98ae0dc04c3c0698764530e80261e135c3ba2787784f0ea11e1db35c3a84787300f0e81ae1ce03c21c038540170e20b01c8360,
    0x4480d88700b10881e20501c4400d88700b10780e20804c4220788200b00883621906c41a05881c0710c01601004c42c0580401310802620c02c4160788100b10080e20106c3fa0787ec070ed0ae1f615c3aa2b8784d70ef8ae1d305c,
    0x47c0389201712281e24002c47a0388e80b11c02623701c46a0784ec0709b00e22503c4460588c40f11700e21f01c43a0588440f10500e00e01c2400784740f08c81e00802c25c0384a8071148ae22913c4480788800b10d80e01104c,
    0x2ac05810c0712c8b625a14c0560380ec0712a02e20201c4a20b89341711581622903c4620788b00b10a80e25701c4ae0b89401700802614404c2860384f0131268ae24c24c4680b88e01712580e24a02c4920789201312402e24403c,
    0x516258a245b14209628412c5042589f84b1410ae27f12c4f62b89d84f13d8ae27a12c4ec2b89d84b1388b626c12c4e42589b84b1358b626712c4d62589a84b13389626612c4c60389840f1302300105604bc0388e01712e80e23405c,
    0x582278af44b15d8b62b712c576258ae44f15b8962b712c5622b8a844f14e8962a435c5586c0aa1171542b02a43405322d8a885714f096298260520258a504b14a1a029012051c258a284b1418ae27e15c4e62589b84b1470ae28c45c,
    0x5fa2d8be45717a8b62f115c5c2258bb0981748b62e515c5c2258b744f16c1262d116c59a2d8b044f15f8962c916c5ba2d8b645716a0962d412c5a2278b344f16889e2cf12c594278b208f1638962c513c58a2d8b144f1608b62bd12c,
    0x6064b8c085b1808ae30026c6844c0cf44f19c80e33514c6600980b09319713002c3506502d8c385718011e2f013c64a278c840718e02603c24c07c6c0c60130121260263606282c0c405b1860ae30323c5e8278c244f18280e300120,
    0x53c258da4531b202604424c6c04c0110d81ae8a635913c6ac258d34071ae8ae35915c6a4258c945b1ab0ae35212c69a0b8c841b19a8b633005c638098d204f1a10b631615c688258ca0db1881ae33d16c6122b8ce81718303634412c,
    0x7022d8e2c5b1bf0a637c34c6f40b8dbc131b69261485607262d8e4c4f1c61a638514c6f8098e34d71c489e38823c704278e10d71c189e37803c6f8698de40f14d09637434c6e2298db0131ba22e37045c5586c0db0d31b20302a212c,
    0x78e058ec80f0118263c105c752058e98071e081e3bf04c774078edc0b1d901e3af02c0460985608f5d48363a505c742038ea04b1d20963a101c73c078e781b1cd03639905c734038e680f0a402e38d35c70c2b8dd4d71b90ae39615c,
    0x7e6038fbc531f489e3e701c7c42d8f84571d080e3e212c7bc258f6c071eb89e15c03d7ae258f444f1e88b62ed13c5d2278b944f1708963cf16c796258f344f1e611e3ca12c794258560131de03602005c7720d8ec4171e202e3b406c,
    0x7ba2590205b1ea0a640406c7b0058fb05b1ea09e02415c8022d8fa4571ef09641005c7c80d8f600b20980e40113c04e298fe4571f10963a901c81c27902c4b20380e40113c7fe03809c530b001ebf915c7c2258e94071fc11e3f712c,
    0x87a0790ec0b21b00e18a01c8600850b80f9910173ef13c77e0380c8530188a642915c84a279084070199b002301c3080986040f20e8ae41a12c82c0390745720e11e41916c8304790581720b01e2fd13c5f0498bd44f17889e40d16c,
    0x8d60380bc4f19412631113c61a278c309321411e42423c8420791945323189e45f01c8984990c01322d0a645713c89625910c0722d0ae45113c87a03915c5722889e44712c8760391305099309718e01d8962b911c4b21b00e44305c,
    0x92e27923c4b24380e05e14c9222792040702f0b616c03d92e2d92444f24589647f01c8c02a4c284b8b500ec8f16c9162591e80724383648103c8fe0591e8070b68a616601c8ec07d1701498301702713c8e22991bc0718a12632c24c,
    0x7720392d05720409e3ec14c7680392c01720201e3e402c7780992b4572010963b101c9502b8fd04f1d600e4a405c7f8058fc00f25b89e4b301c95c298fe84b1fc89e3c101c95c2992ac4f25380e17803d94627927c4f24d0a649a15c,
    0x9ce25937c0727b0ae4ed13c9b20393cc5727689e4e312c9ae0393a05099f0971a601d9ce2b938c4b26900e4df05c9b207935c0b26900e1a201c9980853280f99d0174c515c9822792f4071a01264bb01c33e0392b45720689e3ea12c,
    0x9822d92f41b28c80e51515ca288b94484b2898b650c12ca182592d0571e200e02414c9600b90400b01002650913ca0a2780fc4f2800a80441609f00a0100182628a64c023c97a0794009327f0a64f804c9d627933c0727b0a64f313c,
    0x9da2d92445729211e51f02ca002d93a0570220964e415c9182d9380572440b649715c07e2d923c5726e02e48406c9b20d92041726a02e47c06c9a20b91e41b24382e03b06ca402994704f27c0364cc05c0800393241b23a82e4c615c,
    0xa6c2594b4072148ae53212c84a2d94d85729909652d05c8420d94a1170241b0528560a142d94185728c81e51423c6922791c85b25c02e46c06ca20479264571e909639d01ca400993f85b27e8ae04914c9ea2b81745b2780ae49416c,
    0xaf02c15d0982b80b056f05cad207959c0b2b180e56c060ad06c1590182b08b055c060ab00b95105b01403655404daa007b5300b6a400ec5c05da880c00a1582a10ae53f15ca760b95085329f89653b01ca842b94f4d729d82e05f360,
    0xad20396ccd82d1a2e05c35cb5e69b6b0d76d589f5a823eb4807d68cd402e2b059f15cb322795cc4b2b380e59c160b306c1650582c80ae57c26c0582d9630536c409ed8412db0003d180576be0b002c560af62b95d84f2b989656301c,
    0xa960397208f2e309e58712ca9e039130d72e289e5c212cb720396b4572c412655004c8cc2d96f0db2dd01e58302caa60990c0d72da8a657f13ca8e0396c4532cf89e57b12cade0396d85b0188b65b7360060ac16c4572cc89e57612c,
    0xbda279774072f689e5e712cbd62b979c4b2f182e5dd03c078ac00e15802389e5d913c6c0498aa84b2eb0965d301cba00c16d8532da1b059713cabe03964c4f2ad80e5cc34cb780996b8532c789e55701cb986d97208f2e089e58b14c,
    0xc1e0598280722182e618052c2c07cd380bb0882e43d06cc1e0b981c0721d83660a05cc0e0390d81b3018365ff05cc060397fc072948a65fb13cbf04997dc072fa02604914cbf02c17d0180122b0020560be42997ac4b2f180e5f215c,
    0x6aa278d444b31b0ae62612cb982a18c84f31789660a01c8962b98e054b1a89f1b101dc642b98a84b3178ae62a12cc0e03911c5b31289f5c815235a03b8885b30f09e62312cc3e2586e4530d500e61505c85a0d97d0182de02861103c,
    0xc70699860132d70a665424cca0098124530241b064913cc642598440722d0ae5af3526be47a6e00f6fc0b064913cc5e25983c0722b8ae64c1526b425c6d8077248ae62a12c8a22d99145b3208ae63d13cc8e27990c4f31f89635e14c,
    0xd008b99fc1b01582e5200300800814744801c02e67b05ccec0799ec0733d82e67601ccec0d99ac5733313067313ccde0399ac4f2f90ae5ed16cbd26b94d08f2f38b653212cbc60b94b40f2ee83666713ccc603997c4f32d80e64c24c,
    0xd642d9ab4d735622e6a913cd522d9a985735109e6a712cd4a6b9a8c4b3518b669d03cd2e059a380734e82e69102cd14039a741734c82e4d906cd2e0b9a440b34380e69615cd220d9a381734501668701cd184b9a281b34383668305c,
    0xda62d9b344f35b89669701cd9a2b9ac84b34880e6cd15cd922b93b45b0178ae044140a482400f0573638966c113cd8a279b145b3618966c316cd7c279adc4b34700e6be15cd64259a280735f0ae6ba15cd6e2b9ac84b34380e6b715c,
    0xd5e259a0c0733f80e6e612cdc86b80c85736489e6ba12cd32039b344f35f09669d01c9ec2b81785b3710ae6e045c0bc2b99504c0241a0650030da6259b745736d0966d601cdbc299b785736c89e6d916cdaa079b541b36889e6ab12c,
    0x4be0b89701b38280e70402c48a0b89101b38300e70402c4800b9c1c0738201623f05c4780d9c0c1b37f01e6fb01ce06039bf80737c81e6e805cdee039bd80b37a81e6f404cde80b9bc00f37680e6eb01cdd4059ba40f3740266e214c,
    0x70b13ce144c0981143782286ec450
  ])
  | 7 => (26, #[
    0x164130054070014158005067c013494004c27c01245b004415c010453003e13c00e007003747000c453002c14000b097002b16c00a05f002613c009453002001c00704c001c24c006048001823c005007001007c00380f000c05c002c0b000904c001004000412c,
    0x2c05c00af07000211c00a825c02905f00a016c02200b009c07000e11c009807c025013009202c023cd0008c05002200c00204500214500084050005114008306e02080b007d06c01e017007504c01c80f006c07c01a017006504c01880f005f06c01701f005a03c,
    0x3e01700f407c03c00f00e104c03780b00ed06203a017809401e02400f80e507c03841300dc03c03640b00d556c03411700cd35c03289700bb17c00e017000f15c031d1c00c135c002c5700a814002300b002001c02f15c008402c00500700b845002d81c000c470,
    0x4705f011916c045057011001c04304b010867c00415f0108570041018001067002700b003801c03bc0f00ee12c03b41700ec14c01500700ea02c03a01300fd06c01501c00f603c03d01700e702c039413010006203f417409a03e02600780fb02c03e80f00f904c,
    0x5c114016d27001011c016927005905c003047005805f015c16c056053015516e051457815424c05445b014e13c053057014801c05144f014347004f4d7003f15c04c093002514c04e8dc003c47004d8d00131250009114010c01e04b05f012815c049453012001c,
    0x2901340a301d06c05f01ad14c06a84f01a401c068093019d17c06645b019413c062407015913d064053018f06c06301f018a02c06240f018556c060897018045c05f417017317c05c4df004315c0104d7017b47005e49c003315c00c4d7017401c04d08f002613c,
    0x7a84f01e401c07889b81dd35c011c5701d817001111c01d725c074c9301cf02c07205f01bc16c00d04b01b417c071c5741c416d068c4b41a013d06400780a804d072494003527007109701c116c067453019a13c06300701bf45206e05881b414d058093415f13e,
    0x8a84f022401c08309f01d825c011057002817c088057421c14d08604f421412d084007820745206e05b416424d02c013420c17000a19c016824c00c453020801c04e08f003e13c08111c020214c07fc4f01fb12c07dc0700ac12c002c0b01e313c07c05701ed14c,
    0x80857827827c09d45b027014c09704f024d01c09b89781fe26e07488c826827c09985b026014c09704f024a01c07e4d7825817c09501b025004c09340f024a02c091c1b81f705e073c0c824017008f01c023867c01215f023857008d498004867008c45b022d14c,
    0x4001b42940620a4017429056c05b093004114c0a3453002b16c02d04f000e03c09bc4f024701c09f057028815d0a1053427813d09a04b425801e0a209b028015c09d453026613c09500701d414000dd14028427c0a005b027014c09804f025001c09f05b421c142,
    0xb149400584500b040b001825c0b0004008514000105702bd12c0af44b02b807c0ad01702b104c0ab01f02a906c0a901702a114c08d09b004916c0a5158029f02c0a780f029d04c0a7017010516c04105f001106c00401f029b01d0a680b429903d0a6013410105d,
    0xc184f030612c0c041b02fe03c0bf01702f807c0bd80f02f405c0af40402f156c0bb11702e935c0b7c5f006315c00f897003805c0b9d1c02e135c01cc5702d4140009453002001c0b1093005914c0b711400604700b605c00704700b5c9702d017c0b305b02c813c,
    0xcf80f033907c0cd41b033003c0c1808032d56c0ca117032625c0c7c5f007715c0104d7003805c0c8d1c006715c00c4d7002613c008007030823c01684f001401c0c711400744700c605c00644700c505f031016c0c345302d425c007097030a340016114000415c,
    0x1e11c037c17c0de05b037702c00b0970374030023cd0000415c0dcc53036c07c0d901b035c03c0d600b037312c0da01f036006c0db04b036805c0d904b036005c0d704b035812c0d504b034c07c0d201b035106c0ce413033603c0d3013434b01d0d101f034104c,
    0xeb41303a603c0f100783c005c0ef41303ba03c0ed01f03a804c0e880f03b001e0eb41f03a804c0e700f03a607c0e8813039c03c0e600f83730300e555b039135c0e3897038717c01ac57004445c00e01700c74700e24d7007b15c005007038445001a11c0380170,
    0xfc09f005c17c011057003801c0fc8d8005e67000c453003e13c00e00703ed06c0fa01703e612c0f941800af0700f805b03dc07c0f501303cc03c0f200b03e012c0f641b03d005c0f704b03d906c0f504b03d006c0f304b03c812c0f101f03b004c0e680b03b405c,
    0x10800b043812c10c01b042805c10d04b043006c10b04b042807c10904b042012c107017041904c10480f041c06c105013040e03c10641b041404c10200f041206c103813040803c0f8014023c07010119f007c57c10115c040006001f19c03fd16c0fe45303f613c,
    0x11c19f006c57c11c15c046c060112c07006c670010453003801c11a453005f16c11905c043f01c01719c046016c117057045002c01309f045906c115413044e13c114018009c07011301400b607011211784443611100d0443c04d10e05f043406c10b013042403c,
    0x1350df04d026c13309704c824c13104b04c302c12f19c04b824012e0d704b423012d0d304b014c12bc0704a815012a09b04a417c128057049c14c12604f049701c124050049025c12304c048c24c122048048823c12105f048016c11f057047814c11dc070438060,
    0x2d407052417c148053051c12c0f981b00ac01c0d500c0518560112c1b051867c145c17051046c1430d3050824c141053044704c110c1f050037010fc1b04fc13c13ec0f04f407013c0d404f046c13b0df04e835c13908f04e013c137c0f04d834013611704d4260,
    0x14d04b045806c14c04b045407c14b04b052812c001057052412c0fb41b052012c0fa01b051c12c001057055416c154053054c13c15204b045007c027007054437015004f053c17c14e05b037704c02300702c102c021007053416c14c053052c13c14a04b044f07c,
    0xb5417048412c0c441302d203c12004b031504c0b380f047812c0c301302ca03c11f057047c15c11d40f002535c008017055412c11801b055012c11701f054c12c15204b000415c15104b054012c001057053c12c0df017053812c0de017000415c001057000415c,
    0x13504b04d012c13204b04c412c13305704cc15c13040f004135c00e017031904c019413003135c01641304b412c00501702da03c01c80f04b012c12b80b006203c12a04b04a412c12704b049812c12805704a015c12580b003e25c00e017005a03c12304b048812c,
    0x14604b057856c14580b057412c11901f038005c03100b057106c15b413056a03c01e017005c07c13f04b04f804c15901f056104c15780f04f412c01a017005f06c15601704f012c13b04b04e412c13804b04e815c13a057055b17c137013004445c00e017007504c,
    0x17051b05bd24c16bc1f05a217c024c1305b807008211c008404016d15c05b007016500c017447016b11405a837002411c05a43701680d8059c070166c1b859714c16401f058c06c16204b046c07c10041b023f01c161017058104c15f80f007d06c01b01f057906c,
    0x17ec1f05d4030025c1305fc07008911c008c04017e11405f437017c01c05e505c02511c05ec37017a01c05e606c02200c05e306e17701f05d806c175d1485d436217481785d106e173c1745cc06d17281b05c905c171c0745c402d165c8f459414d0010040004010,
    0x18f00f063402c18380706543621940d7864e06e192817864404218608f464107c18f00f063002c18e01f063602c18c807061103c18b0d8862835e18949b862125e187448461803d18541f061103c18300b000401018285f060916c0d500400a845c181d1b060124c,
    0x1a419c067006c18680b061804c19e41b064c02c18940f00ec4701a309c066906c19200b062103c1a285f068616c1a0c07066707c197c13061f02c19f11c067b06c196013064103c18e80b061701c19d118867024d19bc1b866b05e199c0c866334019700c065807c,
    0x20c1b824436003a0dc00806701ac19c06ac45c1aa01c01f43601a901b06a005c07311c069d06c1a701b053401014b408053001002d810052a030001004069806c1a601b0524010148004051e03002bc10069435c19f017065404c18b80b00ee15c194013062a02c,
    0x16300f86e817c1b905b06e025c1b504f05c402c1b8c9706dc17c1b605b06d413c171c0b06d015c1b301f06c806c022053001c130001004001812000100406c456c00100406c067c02615f06c05701af11806af05c02619c009c0401ae49300eb04c1ad11b017c670,
    0x17300b07284521c909347201621c7053471a13e1c541886a405e18280745dc01e172807059003e1c411c070c4501a801705d201c1c2c97070416c1b905306d813c1b200705cf02c1c011886fc24d1be05486f614e1bc84f86ec06e1a2414860901d17600785c901c,
    0x175c0b01cc05c1d015c072416c1bf057059402c1cfc97073824c1cd00b073017c1be05b00b012c1bd45f071c17c1c2c57470816d1b8c4b46e013d1b4007871a17c1bc85b059704c1cc058072d0701a141805d101c02c05c070825c1c105b06e814c1b704f06cc01c,
    0x1dc057476c14d1da04f476412d1d8007872016d1aa017868d06216700f875c17017980700a46701d605c00d04701d50dc075306e150408002c140001004074d17c02a117074d14c1c711705dc04c14f00405d804c14e004074835c1d1097072817c1c4057070c16c,
    0x15500407a517c154004054d02015280c054704000100407a01701e701c029c4701e611806ac05c1e005c079424c1e40d3078c24c1e2453077817007d01300c84701e111c077416003019c07804701d5c1c077c16c1d709f075825c17a00b00a417c1de114877424d,
    0x1f7c5b07d914c044407005a13c11e00407d704001611407d114004451407cc45c013054000502002e11407c824c09101307c614c1f011747bd34e1ee89387b614e1ec01385f801e16b00f87ac47003319c05f002c02805b07a847017940700a067002081787a514c,
    0x48514080b4702014d700cb15c124408059a02c20045b07fc15c1fe453012101c01c84f07f417c1fc05707ed14c048007006213c021057017505c123408011001c1fa45001104501f915c04890201c94d7058e02c12000406fd35c16480b048401011f40807e017c,
    0x20b84f014801c01d453006514c12d808011001c20a890011045016980b020805c032897082456c2084d7081e37016880b081c57016701304b00102068140060450205450012045016a80b009202c12a40804a40101280040499020127004081305001c114080d140,
    0x12f0040855670214d1c0851270030c5700c135c21315f084b15c2124d707ae26c1eb11b017c05c03389700cc45c21115b484225e210117883f15e20f4d7883805e1e189b878446e1d088c87401411a441885b603e16d00785b002c05d00704ba03020d45b083015c,
    0x69c07007815c00d49c087c17c21e453087613c069007006815c02305700cd35c21c09b086c15c21a453086201c02f45b04d603013400404cd02002f15c086c47013180c0868560219c100074450132004086257021789001484500304d7077445c216c100064450,
    0x13cc1004ec0101cf05004e8010031d1408a705022605000b015001e11408952501ce48c04e203013940808a33402240140734030069d14089d35c034c5704db04002a050089825c225093089002c22305f00c412c22349405e202c03149c088b16c221453088213c,
    0x23100785b802c082007005407023011708bd35c22e89701e405c03ec5708b424c1e589788b624c1eac5f05ec04c08901700d045c00d05408b316c1d611705e804c028c5f08af05001a11404fe03022acd001a445017d01305f004c13d00400a716c13d80c009602c,
    0x1d288c86b804e1a5414860003e16f00788fc46c23e89308f614c23b0d308d404c1ef0df079135e23c11f08ed34c23a89308e614c23401300b856c23811b08dc34c23649308d614c234c1307b307c140c1008cc17023219f00d457c23295c00d667017f00b022401c,
    0x23f89708f315c23801707c316c244018882515d1b1417460603e170007890c46c2400d308f824c23945308dc04c1ed45f074414000dd1409081421f305b478a15e24111b090134c23d45308e824c23601307b825c21c49400bc570210118882014d1f2893878e25e,
    0x24fc0b000905c24e01f093504c24c80f092e02c003017092935c1e6c5b06bc07c0a7c5700d556c015014092404c24880b009807c24601b051801024781c00f847024615b091407007911c06b406c14400407c517c143004050902014180c0054070243117090535c,
    0x25b40b029c05c02b057095805c252413093a03c25a01f094404c24c00f096507c255413092c03c25881f095204c25000f095f07c253813093f03c24dc0b096805c259413096203c257c0b001007c25601f095504c25480f094e02c003017094907c251013094003c,
    0x27509309d117c27345b09c915c271c4f09c101c26f05809bc27c26e05b09b414c26c84f09ac01c03405709a847026905309a0140268097099c17c26605b099414c26484f098c01c26204c098824c261048098423c260007097c05025f05b097807c25d013097003c,
    0x28e19f0a3405c28c01c0a2c45028b15b0a2847c2894d30a2224c2878530a1804c28585b0a1014c28304f0a0a01c0328570a0527028004f09fe34027f09709fa01c27d8dc00c115c27c49409f027c27b45b09e915c27905309e313c27740709d924027609709d5230,
    0x2a3017464002e1850138a8804c2a100f0a8102c29f41f0a6003c29040b0a7806e29d014863d02e1840138a7206c29b8130a6803c29901f0a6003c290c0b0a5f0622960178a5405d18c007860c04e29401b0a4c04c29200f0a4507c290c0b0a4103c28f01c0a38560,
    0x1e1140ac325c2af05b0ab814c2ad04f099c17c2630070ab12500191140aac25c2aa8d000704502a949709fa01c2a84170a9d03c2a605b0a7414c29784b0a3c01c2a441b0a7903c29600b0a8d06c29500f0a9805028f01c0a7d04c29900f0a4502c2a50188a9005e,
    0x2bd4d70af225c2b8c5f00fb15c01255b003805c2b00500aef16c2ba4530ae613c2b1097007815c00a05f002001c2ab04c0ab024c0194530aa41202aa08f007213c0050070ae04502b781c00f84702b615f0ad514c2b4c4f0ace12c28ac5b0a1b01c2b2c4f0ac4140,
    0x2c48130b0b03c2c0c0b0b2005c2c780f0a7302c294413001007c2c641f0b1404c2c4c0f0a6f02c0024170b0c07c2c280f0a6902c293413000c05c2c141f0b0004c2bfc0f0a4b02c002417061701c026017060e01c025013061103c0240130ad925008f81c0af845c,
    0x2d80480b6023c2d70070b590602d605b0b5507c2d40130b4c03c25cc0b029d05c2d241b8b4406d2d040f8b3c03d2ce00f0b3502e2cc00b4b2c02c2a80134a9e01d2ca1584b2404d19401b462826d02d0570b1805c2c34130b0603c2c841b0b1504c2bf00f0b1f06c,
    0x2ed4570bb313c2eb407061c04c2ea41c0ba41601938070ba427c2e805b0b9c15c2e60530b9613c2e40070b2405c1c411c065007c1928070b8c14c2e20070b841402e10970b8017c2df05b0b7814c2dd84f0b7001c19100b0b6c1301860130b6c24c2da05b0b6401c,
    0x305c1c0c1236018940f0c1027c30385b0c0a15c3010530c0013c2ff8070bf927018a01f062103c2fd04f0bf201c2fb8d00bec25c2fa8070be63702f841c0bdd15c2f645b0bd414c2f4c4f0bcd01c0334570bc85702f14900bc425c2f048c0bc024c2ef45f0bb916c,
    0x30c00b0a7903c2968070c4806c29580b0c5506030b01c0c3803c29f4130a6602c3140188c4c05e312017465801e18e00f8c4404c31000f0c3d02c30e01f0a6202c29800f0c3506230c017863602e18d0078c2c07030a1580c2867c3090170c2017030701c0c1a24c,
    0x1315f0c8017031fc1c00f847031ec4f0c7414001a1140c7017c31b0530c6813c2df05b0b7001c2b0097065f02c3191180c6125001d1140c5c25c3168d000604502fa8070aa425c2d080b0b3404c31541f0c3503c30b0070b3c14c2cc84b0a7504c29740b0c4c06c,
    0x32d41f0c4404c30fc0f0a8702c0024170cb004c32b00f0ca902c329d1c023f0703284d700fb15c32705f0c9914c32584f0c7425c19800b006815c00ac5b002001c31749000bc570318093007514c31608f006213c0050070c9316c3234530c8b13c32184b08d301c,
    0x338007010406033701b0cda03c3360170cd702c3354130cbd16c04105f0cd005d33380b4ccc04d33280f8cc801e331c074cc503d330c070cc103c32f014869e03e1a7007869b04e1a640b8cba03c32e0170cb702c32d4130cb807c31080f0a8904c2a080b000c05c,
    0x3545f0d3856034d04c0d3424c34cc1c0d2c16019bc070d2c27c34a45b0d2415c3484530d1e13c3460070d1747019ac070d1114c3430070d081403420970d0417c340c5b0cfd14c33e84f0cf401c199c0b0cf013019c0170cf024c33b45b0ce801c3390480ce423c,
    0x2d20130cdc06c2d580f0b5405c25ec0b097904c35784b0d5c14c31480f0c5005c2a5c0b0a9504c31380b0c4c04c2a4c070a9103c31280f0c4805c2a3c0b0a8d04c042158010007004219f0d5817035501c0d5114c3534940d4c26c3520570d4514c35084f0d3c01c,
    0x3154170b4612c2d10530a9b02c2a6413010001c01419f0d8815c3614530d8213c35f09f006c17c01245b003801c35f058067b01c01b19c0d7815c35d4530d7213c34a45b0d1801c2b609f0d6d14c01f45b0d6a37001f19c0d6514c35880b0d6004c0410180b4a02c,
    0x1cc0b006203c36380b0ce407c2d80130aa405c26140f0ce007c2fa80b0b5c04c27ec07098103c36384b001405c003897000b15c2ca80b0b2804c2c90130b5b03c2d6417097f02c25f413010401c30b80f0c2c05c2a884b0aa014c28fc0b0a3d04c04001f0c5703c,
    0x341d5b0bb535c272897068004c00a15f002005c003c57000845c36a01f0da603c369017006702c0194130da026c36740b0cf007c2db80f0b6c04c2ab0170da024c33b41b0b6a03c2da0170ce807c2d980b0b6404c36744f000b15c0024d70d9807c3650170d9104c,
    0x34201f0bc303c2b001709d404c34101f0c7005c2ee80f0abf02c274413068a12c34041b0bbc05c2df80f09cf02c267413068414c33f41f0c6c04c2ec00f0ab702c2724170cf807c31a80f0bb405c2ae41309c502c33d01f0bae02c2dc01309c103c263c070dad14c,
    0x2ff80b0b9004c286c0709dd03c36fc5f0c0a25c2e711709e935c01255b003805c00415f000b15c34541f0bf905c27d40b078104c1c480f068c14c34441f0bf403c2e30130acb02c0304170d0c07c2fc80b0b8804c36e81f0db504c36c80f007b02c01a0170dae02c,
    0x3b84b0dc805c3714130dc203c03ec0b006c07c36fc0b0c1003c2e90170ad807c27c0130d2906c30380f0ba005c28ac0b09ed04c35e01f0c0403c2e70170ad502c2790130d7507c30000f0b9804c2b4c0b09e905c35c01f0c0805c2e500f0acc04c27840b0d1807c,
    0x3214130bd003c26c40b00c905c37789b0d3d07c2f30130a0b01c26b40f08d202c37605b0d3907c31980f0c6405c02f01b0dd506c37480f0dd005c01dc0b007504c37300f0d3507c317417098b02c2624130dcd13c003c57000d35c30540f0ba905c2b740b023f01c,
    0x3794130de302c03e80f007c07c35901f0c7a03c2f70170a0102c2694130bdd35c00455b000f15c37784f0d4d06c26f41300ba03c32480f0bd805c285c0b09b904c03501f0d4407c32280f0a0d02c26d41300cc05c35241f0c8c03c2f54130a1102c0344170d4107c,
    0x37fd1806a404c37e05806a301c01719c0df737006911c012001c04811c00fd56c37c014029067003f55c00fc56030a80f0c2805c28ec0b0a3904c04201b0c2602c3090130a3701c28d40f0def02c35a01f0c8005c2f900f0a0404c31f40f0be105c08f8070de805c,
    0x3890570e2114c38784f01e401c01b05f006c67007911c024701c01305800ea02c05f417014801c05211c0e1815c3854530e1213c079007007d16c01f19c01e4470383c970dfc16c37e05f0df401c073c0b00c412c03149c0e0817c3814530e0213c069007005f16c,
    0x430040e4412c39104b005056039080b0e4004c38f01886c203e1b0007829005d38f15c0e3b01c38e40f010067037c05b00fc06c38d80b4e3404d38cc074e3103d32f0174e0c140031d14009c15c38b15b06b202c38b19c06ae02c38ad1c06a804c38a11c01f701c,
    0x3aa05f0ea706c3a8c170e9c04c3a640f0e9602c3a445c0e8d03c3a2cd00e8815c3a188c0e8412c3a00170e7d15039f05f0e7906c39d0130e7103c39b80b020805c39acdc0e6503c39880b0e5c0303970530e5807c39541b0e5103c39380b017405c3920080e4813c,
    0x3be05f0ef401c3bc01f0eec06c3ba0130e440103b9c1b8ee605e3b98070ee007c3b70130ed903c3b501f0ed106c3b30130ec857c3b11170ec135c048017000e25c002c57082802c0448070ebc4703ae1580eb867c3ad11f0eb034c3ab4930bea14c27ec130eab350,
    0x3d04530ed401c3cf08f0f3815c3b40070f3423c3cc4530ecc01c3cb04b001405c3ca45f0f1516c3bf4530f1916c3c10570ef001c3ca44f4f2516c3c80570f1c01c3c645b0f0015c3bb0070f1424d3c405f0f0c15c3c20070f0417c3c005b0ee801c3bf44f4ef916c,
    0x11117004135c05ed1c012715c00c4d70f5d23004d8d00f6801c3d308f011613c3d911401284703d805c01244703d7c8f0f5817c3d505b0f5114c00b097001c25c3d38d001144503d208f0f4417c3cf45b0f3414c3cb0070f4823c3d045f0f3916c3cc4530f4423c,
    0x3ec08f0fad16c3b80070fa823c3e905b0edc01c3e808f0f9c17c3b60070f9812c0050170f8c15c3e24530f8001c3e54530f9415c3e40070f8c17c3e14530f7c01c3e245f0f8514c3de4070f8007c3df0130f7903c3d20480f7556c3dc8970f6f05c3d9c5f012b15c,
    0x3f745b0fda13c3f50070fd027c04785f004415c0104530fd236004719c011b16c00c4530fcc17004619c0fc816c3f10570fc114c3ee08f004c27c3ef4530fba36004e8dc000e03c002c0b0fb426c3ec05f0fa814c3e844f0f9801c3ed08f0fad16c3e90570f9d14c,
    0x4e04b102523c40849b101d23c3d7c53013412c406158101867c40585710113704034d4100c37c40249b100525c4000930ffe12c3fe00b0ff53403fd0d70ff02303fc08f0fec14c3a18070fe80403fa0570fb41503b98070fe40703f819f012c57c3f815c012c670,
    0x39d007102c23c3f005b0e7001c39b807001825c40a04b020805c39a807102423c3ef05f0e6401c398807001825c3970070f5815c396007102023c3d54530e5401c40708f0f5014c3940070e4e01c006097017405c392007001825c40c49b102d23c40a00b0fb817c,
    0x413c5f0ffc34c3a8c17004445c0104d70ff812c3a8417104923c3f305f0f6015c3a4007017812c41105f104015c40f007012514c04645b0e8e01c00c4d7103916c40e05f103401c045453011415c3fb84b0fec34c3a00170e7c01c40c08f0fc916c39e0070fc417c,
    0x56514015835041c114106c12c3fa048106914c41a057106401c04b45b012c17c418007105c16c40608f0eb801c41715b101612c41605f105514c414007012815c04745b104d14c40308f0eaa01c40208f0ea401c40008f0e9401c4014970e9e01c4010970e9a01c,
    0x41f44f101c12000704c001812042d49c10b01700a311c10ad27008b11c10aa37008a11c013634004c49010a437042445b10a001e42711c109817042511c109215c42345b908915e41d08f508417c42005b107c13c41d093015814c41e0d0107525041d054106c12c,
    0x41c09310d935c013494001812040c048102c12040a004001812043511810c035c42f05c013a34043489310ce14c07e0d310c801e43119c10c045c07e4dc01f836007711c10bc47042444f0180470409048002c14000604810b817c42e117108424c42044f1020120,
    0x443c5b110b13c43e117109824c4418d001ac450440d1c01de25c04f11710fd35c060c5710f817004f11c0ff634043d09710f024c43b00b10e817c05004b10e9250423093014127043945b10e213c43700701a914c053057108913c00dd1c01ad14c04c097107113c,
    0x42d093028d14c4494d7112445c44801701eb15c07a897111824c00d054111c14243605b50d026e433457911a24c425093100e3404020481004120050d14111634043d054014c4504448d010f125006a114100012043b0140ffa23042744f022b15c04f4d70035250,
    0x456093115613c454093114c24c45204f114413c44e004114156c44f897113c45c052017000f15c0034d7000b15c0024d707e802c044407113812c44e04f10d716c43589f101812044d8dc01e84704048d0113347044c8dc112c07042b093022d14c44a04f50b024d,
    0x2413118026c460093117e13c45f057117801c45784c004445c00f897014347045d4d7014f15c458093011514c45b48c013125045c05c014c47045b093116817c45904f002c25c458494011445045708f115817c45405b114c14c451007115c23c45585f114814c,
    0x46e80b11b804c46005411b407046509311b067c05415f11b057046b018119024c05419c11a916c46945311a001c46709f011817c011057003e13c46705c118424c04619c119824c466498016927046511b519045d4630d85188351461897518415d368414400b02c,
    0x5b49c11ec36147a0d051de24d477053519456d479453011d16c4788dc11dd13c04719c000e03c00301711d827c47505b11d213c47405311c801c47609311ce13c47305711d424c47409311cc17c47204f11c613c47105711bc01c47105b11c013c46e00711bc06c,
    0x47b45311e917c48d8dc1234270463453118916c47745b123024c48b44b1228250461457122836c48909f122025c487093121912c48500b12102404840d7120c15048208c120824c48104f120067047f01011fc15c47605811f815c47d84f11f024c01309f11f1250,
    0x7097125824c45a057125424c007097125024c45984f126c26c49a093126623c49800b11f017c05b04b125e37046605b016812c49609f125626c49488f116c14c04c04b124c56046545f119115c49319f124915c491118124457c49011b123e24c48f0d3123804c,
    0x4a0057127e01c05384f011c17c48c093122c24c04645b122824c489093121c24c488097122225c486093004445c00f897121413c49e05f127516c49c007120c24c04584f011415c48144f120424c49b093126824c47e05f001c25c49909311f417c49804f125c24c,
    0x4b105492c113e42004b471901d1bf01352bd2404ae48c12b417c4ac05b129813c4a300712ac26e4aa09792a523241f04b52a017c4a705b129813c4a501f129006c4a300f120013047f04c015116c46b45b124c24c492093128a24c47805f117015c05004b128716c,
    0x5904b13042304b085f12c116c4c009b12fc16005905c12d816c4ad05312a013c4a500712f84524bd09b92f025e4bb88c92e81624b084f90b814d42104b472404d1bc40752e44704b811412de25c4b605b12b014c4a704f129001c4b511892d226e4b389792ca232,
    0x704c132217c4c8853125813049504c12501304c7097131805c4be05f12e415c4b805b01d035c4c50dc130016c4b385712ac13c4bc05b12de15c4aa04f01d04704c404f130424c4bb85f12ec37c4b285b12c836c4aec8f12b914c4c3093130b02c4bf05f12c416c,
    0x4d089813401700788dc01e036005119c135c6704d60d0133c17007f0d813544704d449c134c16c4d2053132427c43e097109823c05805f13444524d009b933c25e4ce057533414d4cc04f532c12d4ca00793162324ba05b477404d4c905c016067005a490002c140,
    0x5705b138847042484b015c6704e1853126c1304e185f126813005b4901264130498008125d24000704c13812704df05c13744500a811c13784604dc1141354170078093137457c4dc15b136c34c4da453136404c4d6097134417007f09313502704d845b814515e,
    0x4ef00701aa13c04a05713ba01c04d09713ba02c42804b13b405c41e84b107834c48304c015b12c4ec117004c15000704c01704504eb013026c24c4ea45313a445d4e84d3939c24e4e6453939404e4dd15b535a25e4e4457815516e09b8dc026c36005519c138c14c,
    0x48849001781504fb49413e414005905401244504f8490130d23048704c13e92504f78d001ac4504f6450130a12048500812112404f909713e024c4f708f13d802c4f505f017812c4f549401792704f445b13cd14c4f200701ae13c04905700374704f105f13c114c,
    0x50815c01846705070dc141801c42a08f022a13c50504b541001e503897140c45c50241701ef15c07b4d7140424c500417138937c42984b022f15c06089700363504ffc5b13fa12c057c5f13f525004a11412301304fc49401a84500a3c57016316c48a4901224130,
    0x4db4d7936a15e51211f144534c510093143d14c50c013139e26c05c15b143945c50d853143434c50cc13143124c4e5c1b139526c37601400bc57050b51793ae14e4eb0d3936615e4d90d7931a1224c600c483846248d490142b47050a49c142407050819f018457c,
    0x49104c12401304ea85f123c13048e008145c070514897145045c50b017137717c4dd4df137316c4dc4db145a25c516117144b15c5124d7143905c4e9c5b13a536c51611b145424c5110d3143e14c50d01313a037c4e685f131c14000dd14145056d51305093b016d,
    0x52181b147104c51b80f148107c51f41b146b03c523053147b06c51e01f146602c51940f148825c52145b148114c51f84f147801c00a05f147424c51c45f146d16c51a04f146501c009457137b16c4de4db02a315c0a84d7018556c51715c124c13051849c01ec470,
    0x53645414d817c53541b14d105c53301314c903c53180b14c114053005714bd12052f05314ba07c52e41b14b405c52c80b14b103c52b01814ac17c52ac1b14a404c52840f149e02c089017149b370525013149103c06400c148c12c522c1b148807c51dc0f147404c,
    0x1b30d386cb04e54b01f152903c54980b152013c54741f151906c54500b128d02d54481f150d06c542013150457c5404d714fe25c069017000c45c002c5707d002c04400714f847053d15814f467c53c01c14ec47c53a49314e614c2dc0d3098f04c53889c14dd03c,
    0x28c57155f15c556c53155713c55401f154006c526007153806c54d01f154e05e55341b954b05d55201b553206c54c417152301d54800b46d034d554018154d03c52601c154814c55101b151d03c54680b154335254f018953b03e54d00f553203c4a504f529302e,
    0x568c5b159d14c56684f151001c00a05f159425c56445b158d14c56284f150c01c00a05f158424c56045f157d16c55e04f150901c009457157414c55c41f156d06c55a40f156602c008017156217c55845b148c0101b401700a845c55885306cc04c1b2c0700a445c,
    0x4ab44f15c914c57105015c425c57005f15bc16c56e05315b413c56c00712a424c56bc1015ac15c56a08f15a617c56545b158514c55d407159016c55f057156c01c56845b158015c55c007159817c56305b156801c56a08f159f17c562c5b157914c559c0715a425c,
    0x58b11f162934c589893162114c587013161a16c585053161313c583807022a15c58249c160414c580c4f15fe3700a345715f925057e09f15f516c57c05315ec13c57a407022d15c06848c15e41604aa44f15e427c57805b15dc15c57645315d613c57400715cc470,
    0x4ac44f52a224e1b940f46de02d59b45f166b13c599407166023c4a644f015934c59708f165b16c59605f151401c595c949654162594c4b965012d59344b129b13e4a609386d701d1b500b5648070591158164467c5908dc163c17058e893163527058c114163056c,
    0x59844b965c12d59344b152001e1b801356ad2505aa08f16092705a9093167d16c59604f151d01c5a88d4969d2625a688f969523d5a408f12b513d4a789386e903d1b680b568e17c5a204f168601c57f8dc168024c59f45b165b13c546407167a36259d494967223e,
    0x4511416d025c5b305f16c816c56e05315b413c52c00712b824c1f504b005b02c5b1c9316c323c5afc0b16a016c59504f15fc12c5aec9716b424c5acc0b16ac17c59d05b165413c58204b169816c59c05f165013c5a505f165013c5aa45b96a416d5a445b168015d,
    0x5c241716f717c06ac57004135c00f897170747005e49c01af15c00c4d716d01405c005f16fd16c5be00716d425c4af093011415c00984f002514c5bd11416f127006a11c16ec57c5bac5b16e614c5b8c07162a12c58944f16de3705b605c01ac47058e44f16d4140,
    0x5cf01f173806c5a180b166503c008017172d14c5ca84f172001c5cd84f173514c5cc007172d17c5c9c4f171d01c5ca85f172713c5c6807172007c5c740f171a02c5c585f166212c56a84c171423c4a744f015d35c4a844f016135c5bb49401434705c455b170c45c,
    0x5d909b176017c5d6053174f13c5d0007175514c5d184f173c01c5d9097175d16c5d4453174a13c5ce007176025c5d745b168e13c59b453152c01c00a05f175824c5d545f175116c5a204f152901c009457174c24c5d245f174516c59a04f152501c009457174014c,
    0x5edd1497b015d5eb05357ab13e5e904f57a313c5e704b579801e5e5c07579301c4ba093472004d5e3d1c177a14c5e2057178514c07105017804525df058977a15e4c884f90b824d1d3407471c04d5dd05c06ef01c5dc41b176c05c5dac0b0b7e03c267413071414c,
    0x4b344f180114c5ff8dc17f81704bd09317f514c5fcd1817ed2504bc09317ec26c5fa45f17e415c5f845317de13c5f600717d41405f509717d017c5f385b16ce13c5b245314b801c4bb0d712cb24c08305817c916c5f105717c114c5ef84f17b801c5df097020c27c,
    0x619494186426c618057185d14c61684f185401c08c45f185016d613c53984814d611853184313e60f04f583b13c60d04b583001e60bc07582b01c5ed11892c424d1be01358241706088d812d113c60809f181f16c606057181514c60484f180c01c602d1c1805270,
    0x61f457171613e5a904f569113c5a0c4b556201d552007953201c1c2013589125062308f178d260622097167e13c59f453154401c6218d8988525262088f988123d61f08f12da24e4b644f470602d1c140f587b47061d05c187007061b158186c67c06e05c186914c,
    0x5fd45318b607c62c01718af02c1cb053005d06c00380f000904c62ac9718a724c628c0b189016c5e304b16a013c59d053154001c627c97189b24c625c0b188416c5a7053167813c54f007188016c5a604f153801c62005b169414c59c04f153401c623857988815d,
    0x642c4f190701c072058190313c63fc0718f816c63d45318f213c63b00718c025c5f1057004c27c63a11498e415d63805358df13e63604f58d713c63404b58cc01e632c0758c701c4bf093473004d63005801d817004645b003114c62f8dc18b81704c00930118670,
    0x9005c194c67c06c15f194c570652d18194416065001801b067064f19f193916c64d057193001c64b09f011c17c010453003e13c64b8d819281704b744f011e67064905b192015c647007181514c60484f16ec27c646853191713c644c0718eb45008111c190d14c,
    0x65a0d71964230659093196013c5f585f17d516c5b445714bd01c657010195c15c5e305b16bb24c58205315fc13c557c0b149801c075c9701b817c656c93195702c627c97189016c5ab053155001c06e04b188d15c5d9c5816a913c553407195007064f1580243470,
    0x58104f149401c00b097199424c64345b178517c580c4f149101c0a3457178017c07509719a326c667093199802c63005f01d812c5de85b01d4470665093199047066301c198856066219f198515c660094198036c65f09f197825c65d093197112c65b00b1968240,
    0x60d05b19c816c67105319c013c66b007185026c08705701c827c66fc5b19b814c66dc4f19b312c66b00718cc07c60c01b18c816c60b05f073c25c1cdc0b19a8162669c53995405d64401b98fc05e63101718a006d60a01b16bc03d5ac00b555c04d4c204f978817c,
    0x627057584516c5b104f56b712d556007873c04d63705b184017c677c9b19d824c673c8f19c412c66dc0b18d817c60f05b19d4262656057591416e64005798d415c62905b583816c5b004f56b814d555007930f23e1cec0b59d326c673c8f19c012c66cc0b18d017c,
    0x8a457199814c63b01f185406c58380b15e903c08901719e425c675c9319d435c66ac0b19a805c63ac5b18e817c081c4b020415c678c9719df24c674c8f19c812c66fc0b18e416c61405f184c17c678c9b19d824c66e00b18e017c61205b021c12c64645b98a816d,
    0x9c57002625c0094d7002445c67ac97186416c57e05314ac01c08304b19a025c63ec5b161914c57d84f14a801c08c85f19eb27c61805b17c417c58504f15f014c529007002c25c66709318f517c61745b161313c528407022d15c63c45b185917c57bc4f149d01c,
    0x60405f17dc16c58a05315d413c53100719f717c65c08f17e956c57711714d105c0104d7003e25c00a95f002715c65b053191d06c5f641f16e202c57440f14d005c67cc5b19f017c67b007011613c045453196114c65808f17d156c5f415f14b405c4c444f131024c,
    0x74c93014012c68005f19fd14c67e00701aa13c04745b19f613c66009717ed16c5bb45f15e514c536407197c25c64945b17e817c5ba84f15e114c535007197825c60505b17e017c58904f15d814c532007197424c64845b17e517c5b9c4f15dd15c533407197b25c,
    0x66108f002a67c00a55f1a1e13c62f45b180517c5b645314e101c4c5c931a1b25c685c0b18b817c60205b16dc13c05e04b1a1316c6834531a0b01c06b84f011817c60005b17f417c58e04f15c814c537007003135c00a55b002715c681c97192817c5fc05b16f014c,
    0x69005c027c47006d19c1a3c67068e11702033700800d819952306570501a3425c68cc93194816c65105f024012c68b84f1a2d14c68a00701b316c06c05f1a2401c663097194316c65005f164a13c5924531a2116c662097193c17c59184f164514c53d0071a2056c,
    0x5384f012914c049453027f15c013d1401b716c00b05019a014066748c199803069ac5b002c1406991181a3915c08705c01d81406980931a5d34c69505c020114c696457021c47069009f01b417c6951149a5015d69304f5a4812d691007977c16d43e093475804d,
    0x69911f199014066305019881406a505c01f04706a401c1a8e25c6a34d71a8805c07cc5701f045c6a18931a6226e6970d79a8424c0778971a80140049114198123065f050197814065d48c1a7c14004a1141a78150053114196d12065a48c1a7516c69c0571a6c01c,
    0x6af8071ad114c6b384f1ac914c6b104f003115c6b040f1abe02c6ae1171ab535c6ac89701e405c00455b000f15c22a00b01a701c20500b012101c6ab41f1aa404c6a700f1aa807c6a80131a9a02c6ab4531aa801c6a90531aa001c00c4571a9c13c6a68071a6716c,
    0x6c1007013c15c6c011c1afc14c6be0501af825c6bd05b1af014c6bb00717f417c58e04f1aeb0406ba0571ae74706b84d701eb15c4fc09301a914c00ac5b002514c07a11c1adf16c6b6c4f1ad701c01315f081813c01880f1ad117c6b24531ac101c6b385f1ac414c,
    0x6d80131b5e3606cc89b1b5c27c6d685b1b5414c6d404f1b4e01c0778571b492706d104f1b423406d00971b3e01c6ce8dc1b341626cc0575b1825d6cb4941b2c27c6ca45b1b2414c6c804f1b1d01c0a8457016825c6c689b1b141606c509f1b1016c6c30531b0a13c,
    0x49057002817c00984f1bac01c44108f01ae13c6ea11401ec4706e98531ba212c6e7c071b7316c6dac4f140513c21604b006702c6e60531b9413c6e44071b8d17c6e2c4f1b8501c6e001c1b7c5606df19f1b7a25c6dd1141b7456c6dc11f1b6d34c6da0931b6514c,
    0x7cc5713f424c04a4531be316c6f7c4f1bdb01c01315f1bd417007c11c08ac12c01ac0b1bd017c6f304f1bc801c6f40571b8d14c00c4571bcc14c6e2c4f1bc804c6e140f1bc445c6f08971bbd05c6eac5f01ef15c01255b004135c6ee45b1bb514c6ec0071a8025c,
    0x7060571c1613c7040071c1817c6e6053003115c70585f1b9413c70401f1b9103c7038531c0713c6fe84b1beb01c7020531c0013c6fd0071c0e15e7020531bfc13c6fc4071c0626e7000531bfc13c6fb8071bf835e6fd0131bf103c6fb80b1beb05e090d1c1be535c,
    0x6cdc4f1b3313c6c6c4f1c5025c7130931c4823c71100b1c3816c08d04b005067c01245b004114c71045301b316c70f05c01b067070e494023526070e09b1c3415c70c84f1c2c01c01309f1c2914c04b45b012c6707090171c2104c707c0b006d06c00401f000e03c,
    0xc4d71b9d03c4d54531c6114c7170571c5914c71500701ea13c04b05f1b1514c6c44531ade13c6c34531ada13c04f4571b0b13c6c140f1ad602c6cb0531b2914c71409b1c3417c6c90531c4c26c0a84571c4826c70c85f1b2013c71105b1c2c07c6c740f1b3b14c,
    0x1e0c0b075412c1d4013023c0706e04531b7d14c6dec4f1c3c17c6f50571b4814c09004b1c6d14c71a84f1c6401c07c05701b017c6d7c531be015c6d645301dd15c6f70531b5313c6d5c4f1bd804c6d340f01ed14c6dc4531ba014c6e904f1b6913c012d5b004315c,
    0x7370dc1cdb15c73544f1caf12c724c071cd046d7331175cc81627310585cc016072f0575cb837072dc571cb213c72bc4b1c8e01c72a1175ca41627280575c9c370726c171c9503c724c0b1c8e01c72205c1c8446d7201175c7c06271e0185c7406071c0174034170,
    0x73704f5cc313c72e04b5c9c01e722c075c7701c5ed1175d104707408531cbf13c728c4b1c7301c06f19c1d0c47073e8531cdb13c72dc4b1c9b01c74211c1d0417074045b1cfc47073e8571cd513c72c84b1c9501c73d1179cf336273b0d85ce83607390d35ce0170,
    0x7134981d352707128d41d333707110141d2c470734c4f1c8701c73d8531ccf13c72ac4b1c8301c73c4531ccb13c729c4b1c7f01c74a11f1d1056c742c531d0715c731c4f1c7b01c06f11b1d2446d7480d39d1c24e746c539d1404e7430575cfc14d73a4531ce313e,
    0x75811c1d5f01c07ec4b1d5b01c0130581d5616c7548571d4a01c4b945310be13c753c4f1d574707548dc1d4e25c4b911c1d4a2700134941d4745075109f1d4316c74ec531d3713c74cc071d0815c75111c1d3e14c7508dc023526074f85b1d084707140541d3a370,
    0x76300701ed14c05445b1d8817005419c1d8527076005c01ec47075f11c1d7917075d0dc134024c078c4f003417075c80710be13c75c89c1a1814005ed141d6e01c04e0971d6e02c43204b1d5f05e756c1b9a1703275a15b10c612c75a19c10c212c75909c1d63470,
    0x76c0079d134524c9093475c04d76bc4f1dab01c07219c19c927076b89719c52706708dc1dab06c66b01c00341707690dc1da63704d5453135024c4d8093135c24c76811c01ff13c768d1c133c24c76784f1d8916c7614571d8114c75e4071d9b4707650571d9213c,
    0x77f0171df804c77d00f1df056c68f453023267c08c55f003747000d05c1df067068e4531dec47077ac4f1de712c778c07020214c777c4f1ddb13c775c07004c16077449c0230670773c4f1dcb13c771c0701b8670690097027c15c7700575dbc14d76e04f5db412d,
    0x791c4b1e0c01e748cd4979c16d1d900f5e4023c78f45f1e3916c78d4571e3114c78b4071e2b16c782004179717c1db117076004c7890d39e2305e7870175e1b05c78500f5e1002d7830075d17352641c1b979806d5e4c1b155f0324ca04f5e0812c78101f1e0006c,
    0x7a30575e8b15c7a104f5e6712e79204b5e4712c7840079d1f352642c5b97a416d5e8c5b16bb1324cc08f476803d7a00931e7e17c79e85b1e7615c79c84f1e6e01c79ac5b1e6713c790448133445c4cb0931e6034e797c579e5815d795c571e5013d79384b9e4812d,
    0x79ac4b9e5812d795c4b1e2b01d7870079e1b01c61405497b015d4ce093477004d7af05f1eb815c7ad0531eb013c7ab0071eab16c075c501ea44527a88579e9c15d7a68571e8413d79404b5e1401e5eb05b533424d1db0135e9716c7a084c1e4e12c5eac5f1e9315e,
    0x5ef85f1de535e5058d093f813d7b601b1ed404c7b440f1ece02c76c05f1a4414c5ee01f05740100310541de305e775c1b955f0322310109ecb4707b101c1ea214c7a4c4f1e5f12c788c071dec470749d141ec34627aac539e9c14d7a68531e9713e7a304f5e8b13c,
    0x22c80b477d03d7bc05b1ee814c7b804f1ed401c76f09f17c417c07609712881300508d41eed16c7ba0531edc13c7b44071db827c69309317c117c77a89b9dda25e5ae88c934913d44a490910a12d41204801792507b985b1ee014c7b704f1ece01c76d09f1a4824c,
    0x75019c1f1313c7c0c071f1614c7c3c4f1f0b12c7bfc071f1615c7c4c5b1f0f15c7c1c4b1f0b15c7c1c4b1f0306c7bfc171d2b45009005c00374707bc0571eed14c7b984f1ed801c77009b1a5025c5f245b1efa3627bd4989a6a23e61449493fe24e4d344f510e12d,
    0x7d005c079c15c0a70171f3c04d08e19f00374707cd15b00505607ce44f1ec84707b1d1c1f2407008e1581f3405d7c80189f3113c7cbc539f2813d7c61189f246707c815c1a5a14c088d181dca25c08649c0216370771c1b02100707c701c1d4057c081d141f1b460,
    0x1245f1f8427c7e005b1f7c14c7de84f1f7401c0110571f7027c7db45b1f6814c7d904f1f6101c0104571f5c27c7d685b1f5414c7d404f1f4e01c00f85700341707c705c138024c0a84531f400707d24531dd026c08c45b1f4413d7bd0575d2f4524df09347a004d,
    0x7e91179fa006176a0135c8456d1ec0d05f9c12c7e601b1f8405c7dc0131f5c03c7e00171f6d04c7d680f1f9406c7da0131f5403c7e441b1f7c04c7d400f1f8e06c7de8131f6403c7e705f1f8806c7dd0131f6103c7d380b1f9826c7e50571f9114c7e384f1f8801c,
    0x7ff01c1ffb35071cc171ff817c7fdc1b1ff005c7fb0131fe903c7f980b19a81407f80141fdf34066900c1fdc15c7f681b1fd404c7f440f1fce02c05f4171fc86707f18901fc415c7f04541fc017c7ef41b1fb805c7ed0131fb103c7eb80b1fa91407ea0570258060,
    0x80b09b9c8c25e66c448602907c809013202103c807117201935c80589701e405c00415f000b15c22800b01a401c21700b014801c20300b012001c37701400b84508041581fa706c721c1f1c8305c19f11c201067c803c17200834c801493200214c34611f0a1b04c,
    0x823013208903c82180b208307c66e00c19ac05081f05f207806c81400f203402c81d41ba07006d81b41b2068042725417a06707c81840f205e02c81605f205506c81400f203002c8138579c9216e66d848a04806c811013204202c80f05f203a06c80d00f203002c,
    0xe01720ab16c8294531f9c01082ac5b20a517c826c17207503c813c0b202e01c82501b207004c828c17a09c05d824c17208303e81f00f606d03c81600b603c01d828c1b1c9b05c07dc1f209c16c81e013205503c80e80b209b05e825017609305c726c1b99bf032,
    0x82c00720e917c83545320b501c83c09b20e317c83445320c113c82bc0720ec26c83a05720e514c83884f202801c01245f20dc27c83645b20d414c83404f202501c01045720cc27c83205b20c514c83004f202001c01105720bc17c82e41b20b404c82c40f20ae02c,
    0x849053212013c7f9407211e350846490211825c845058211427c84405b210c14c84204f1fcc01c0600572104140841097210016c83f04f20f801c60405f162814c83dc1020f415c83c08f20ed16c83745720cd14c82f40720d815c83245320b801c83905f20c414c,
    0x860407217c37c85e09f217416c85c04f203001c85bc5ba16816d859c5b1caf15e673c48a16016c85784f215801c85501c215056072a4d7215067c8534d7214845085215b214447c8500d3213e24c84e853213404c09a8d821312507284d7213027c84b45b212915c,
    0x86d05761ab15c86604f617e12e85e04b616712c80f007a1b936c72d4d701f937c86d09b219414c85d04f203a01c86c4d7a1ac35d86a4d71cb536e67448c61a414c86804f219e01c6708d0219827c86505b217013c80d007219016d86304c9cb215e86245f218713c,
    0x8774d721d805c87289b01ea25c01215f003f15c87545b21d213c8730071a7825c053057002817c00945313e824c06b45321c845007a11c21c457c87085321bf13c851c5b214212c7ebc07081012c01cc0b21b315c85bc4b202e01c86b85b219014c85a04f21bb15e,
    0x87b407222026c887057221914c85884f204801c01245f221427c88405b220c14c85704f204401c011057220827c88185b220214c87f04f204201c00f85721f817c87d01b21f004c87b40f215a02c00e01721eb16c879c4f20f112087a89b21e626c871d1421e045c,
    0x893058224c27c89205b224415c89005321be13c7ec007223c14088f097223817c88d053223001c60505b162413c88b15c222b04088a057222624c88805b221415c88204f21f801c884057220613c87d007221c16c88084f21f001c88989f221916c88305321fc13c,
    0x8a30509cd515e8a285f228413c8a0807227c07073489f1cce26c89e89722741706da893227127089b8d81cbe26c89b09f226a16c899053226013c84a8571fea01c675090225d2508968d0225825c89580702792508940585dac14d7530935cd056d4e70d0416c25c,
    0x8a5053216813c8ae05762a713e8a804f629113c879c4ba17812d859c4b205801e73689b01fe27c8ae09b229c14c85d04f205501c8ad8979cda26e67788ca2b014c8ab04f22a901c8a989b19d923067149422a027c8a705b217013c814007229916e8a505b629116c,
    0xe01722da14c88984c217e12c8b685f01ef15c00c4d722d417c8b445322cc01c69f097012815c00ac5b002613c8b149401704508b2007111023c06a84f22c437c8b0c5b22be14c84384b1fd301c51044f004c57c21904b007702c8adc57229913c85bc4b204f01c,
    0x8b9c0722f914c8bb84f22e001c8c211b230317c8bdc4f22eb12c8b7c07230426c8c0057228914c86284f206401c01245f22fc27c8be85b22f414c8a1c4f206201c00f85722f027c8bb45b22e814c86104f205d01c01045722e417c8b8c1b22dc04c8a040f218202c,
    0x8cd05322bc13c7f5807018215c8cc054232e3408cb097232a01c8c9494232427c8c845b231c14c89145721c313c7ed40723181508c549013341408c5097028416076f0509d3e15e4e184f87a501d8c4054230f0401db050230c15c8c2097230716c8bfc5322f313c,
    0x73e857020217c8e109b229c14c86504f207801c8e0857a37c15d8de857237414273e85ba37014c8db04f236801c8d901c236056073d857236067c8d785723581708d51141ce615c8d515b235047c8d30d3234824c8d1453234004c7a9054233e3608cf09f233a16c,
    0x8d4c5b234514c899c4f212712c7fbc07020445022904b007b02c8e0857229913c81d407237c16c8a5053219013c81c007238a15e8e1057637a15c8b684fa2a013d8a444f219812d829407607c01e81b407238c26c8dd05b228c14c86304f206801c63809f238a16c,
    0x8da01322a903c86780b003805c8ebc5b230b1408a9c4f208301c8eb11b19e0140672d14239345009005c23a935c8e989723a005c8e611b01f045c01295f004715c67a050020f4504fb093012514c8e7007111423c05384f23984508e505c1d0215c07c11c239057c,
    0x8f541323d203c34a41b0a2b02c8f305723c414c8ef04f23b401c8f205723c114c8ee84f23b001c8f309f23c816c8ac05321a413c823007004415c8f109f23c116c8dc05321a013c822407004115c8ef09f23ba16c8db05322ac13c821807003e15c8ed05f23b006c,
    0x87ac4ba1b412d86ac4b20ab01d827007a09301c90305c1b7114c8ce05722c114c84484f1fd801c06145f24092709018d8240427c90005b23fd14c8fe84f23f401c8d405723f114c08d09f02892508fb05823ec27c8fa05b23e415c8f845323dc01c85184f23d805c,
    0x90a057242514c908007241c27c04b05f004916c00f84f241c16004b19c23e816c8c8057224914c87109f214613c7ef007241805c905413241203c01f41b001007c002c0b238214c8adc4f21b312c826c07237c15c86b84f209401c8ebc53a38414d8de85322b813d,
    0x7fec07244836091211f2444370910094244026c90f84f232515c89345321c517c7f0407238a14c86ec4b20a301c01419f243914c90d84f243001c90b09f01b017c01245b004415c90b8d801b267090005b239027c8d4057226914c84b84f1ff401c05445b003114c,
    0x11c57004445c919057246114c91700701ea13c04b45b243f17c90f89b224535c8911171fb805c01255b004857c00fc57003e25c7e9c07225313c7e8c0701c847c8cf85722c424c84584f017114c91611c2457070914158245067c913057239317c89bc53213313c,
    0x7c945b067c01c91e09b236015c85484f201001c08e45b247856c8d7853227b13c853c4b200f01c01319f247427c8e5057227014c7ff007024012c06f09b247114c91b84f246801c07c05701b316c913c5f244c46c84a897212935c7fc01719e414001295f004956c,
    0x92180f248504c921017248301c92080b248103c920013248467c920017245b4509151142450160014158247d13c013058244a3604e444f1a04140050d14026f13c0130581dce26c91d494024127061a45b1dde26e4e344f644636008f41c236415c89f453215613c,
    0xa05f24b001c44d08f01ea13c24704f00fa03c92b05724a514c92784f249401c92a85324a313c92684b249301c92b19f24aa15c92919f24a225c92719f249835c92519f249305c04215c248c561922014891b04e24680f891902e246007891402c079007248702c,
    0x93a41b24e405c93841324de03c0a519f24d817093501c24d346093409f24cc06093305f24cb02c93280f24c904c932017248c06c92205b24c405d930c0764c202d93040f64c004d91e494023857051809301ed14c92f45324ba13c92d0071a9425c07c057002b16c,
    0x162004023f050946013251403c94440b0e3417c38c05b0cd807c33501b1f3c0423900178aa1062249007892003e94380b24fc04c93c0040cc807c94300fa50803d94100f250002d93f007a4f901d93d4070d6005e33301b4cc405d3300170aa106293c04b24ec07c,
    0x94b01c24d8560935158005407094d11c253113c934158253027c94a01c1f3026c7cbc5b1a3414009005423f116c7ca09b247c25e7ce09b9a3223293315824c856038e017029807094b05c252914c7c945b252701c94940f0e3c560949017252003c94740724c0560,
    0x2537470
  ])
  | 8 => (26, #[
    0xcd1bc03235f00c49bc03015f00bd18c02e35300b498c02c15300a48fc02814f00948cc024143008493c02013f007490c01c1330068d3c01812f0058d0c01412300441bc01005f003418c00c053002c13c00a03f00240bc00801f001c10c006033001408c004013,
    0x23c5b808b14202101f808006201f013807802e01d004807001101b004007412e01c04b406c12c01a41f806407201801b805c062016c178054052014813804c04201240f804403201015bc03c56300ecdbc03a45f00e45bc03825f00dd14c03636300d494c034163,
    0x3701f40d807c03501c80d305e03440f80ce03d03301740ca03c03201700c604e03100b80c202d03001340bf02c02f413008214e02004b806705201940c805e04201700880b957e02d15c80b056e02b15880a845d029d1440a135d0278d4409825d025494409317e,
    0x4808f011d17e04705b8119172046058811715e0458538111152044050810c01e042007410401c011004410067d03f59c40f956e03dd1c40f527103c8dc40f017103a01480e405102e91f40b827d02c8df40b017d021c13808502e03b05c80e816e03905b40e107e,
    0x58893816024d057093015917e05505c815016e053058814b15e05244f814401d0448548110132013004414157e05015b813d57204f158813935d04e117413745104d8d4413316e04c89f812f13e04b89381280510494488124121048048009805d04948f812423d,
    0x65453019001e063007418801c05ac93816835d0448508111132022c0b408805d015004418557e06015c817c56e05e158817745105d494417317e05c4df816f16e05b4db816b14205a48c416405105884c816013105704c013b45d04e497412f12e04b4d380a105d,
    0x7315b81cb57207215881c635107149441c316e07011f81bc05106dc5081b414106c050013b35d04e09740a805d06ed5881b827206dc9781b425d06c09701ae16e06b45f81ab16d06a05f41a716c06905f01a3172068058819e14e06744f819b13d066053419613c,
    0x84d1c420f470082d17420637108049c41fc16207e01c41f415207c05441cc47d070c53817c37d05bc4f814027d04cc4b80b007d023c0741f426e07c09b41ed17e07a05c81e715e07885381dc14d07645301d413e07400741a0152053050811813201700441cf57e,
    0x5005f40b807d02480b426827e09909f426027c09705b825816d09545b025315e093057424815c091853824014d08f453023913e08d04f423213c08b007822801d08900701fc26e07a05881b8252068c54815414204644c8064011088d9f421d67108655b8217472,
    0x8691b421915d08609b410007d03e41740f806d0a359f828c67d0a219f028735d0a1917428515d0a1097428005d07ad1441ea35107a49441e8151035014427d67109ed1c427637109c05c426c07109a4948265251098494022267d0824d741ce37d06111f417224e,
    0xb044882bc02e0ae0044128051025494401825d00201742b423c0ac05302ad07e0ab01b82a90720aa01882a705e0a981382a10520a8010829f4710a78dc429d2710a705c42980720a501c42900700a3558828c5610a2158022317d08889f422137d08811f421b35d,
    0xc784c831b12e0c500442e345d059014409e3510080d7400805d0c408f030c15c0c241f83040720c001b82fc0620bec1782f903e0a881482a00320bd04b02b00300bc55f82ec5720ba15b82e45620b811742df4510b64d742d63510b4c5f82cf16e0b2c5082c713e,
    0xdc017036c04c0dac4b436815d0d981b836507e0d8c1b436007d0d7c1b035c07c0d6c1c83580620d5813835503e0d4c0f435004d0d380f034d04c0a881082a10320d204b030c0400d155f83405720cf15b83385620cdd14433125d0cb494432b17e0c9c5b8323142,
    0xf281383c404d0f041303bd03e0ee00f43b603c0d601482fc0420aa00c83b012c0df01403ad57e0ea15c83a456e0e8158839e3510e6494439717e0e4c5b838f1420e201383840110cc09742db35d06f01440a745100a117400805d0e008f037c16c0de023037407c,
    0xff018042b67d10959c442156e107d1c441945d1058dc44112711030544408051101c0743ae47d0cf8df42f027d07e01c40f017100c05f401007d10008f03fc17c0fe02303f406c0fc01703ec04c0fa04b83e507e0f801f43dc07c0f601c83d705e0f401743cc05c,
    0x11e80b042a67d0e98df434647d0ba05f426c07103d49c403827d00401f447423c11c063046c07c11a01b046405c118013045c06e11601b445506c114c17844c05d112017044604e110013443d04c10e40f843403d10c80f03d80620d6c1483040420aa40c842c12c,
    0x132058c4c415f130054c4bc14f12e050c4b413f12c04cc4ac12f12a048c4a406f11ec1b847406310b017c4000530ec00fc3800330d200bc3100230bd007c2b401312904b047007012859c449d56e126d1c44963711244d7448d25112205c448405112040b847e02d,
    0x14f05b853816214d053853314214b04f852a13214904b852112211fc1f840706e0dac10851c56f146158c51446f144118c50c45f142114c50436f1400d8c4fc35f13e0d4c4f434f13c0d0c4ec26f13a098c4e425f138094c4dc24f136090c4d423f13408cc4cc16f,
    0x14b04b052814014a88f052825c0c5817031413c059007004c01014904b052013014848f052024c0ae41302b813c04a007004401015b05f856817215905b8560162157053855814215504f855013215304b854812212001f83e80620e2c1382bd02e15105f8540172,
    0xb0013009402c011008054412c16505f059016c163057058814c16104f054023c121423026d01c019004053c12c160063057c16c15e057057414c15c04f053823c10201f01f801c017004053412c14c054036805014cc8f053026c0e1c1b038413c06f0070054010,
    0x15904b05c425c17004b056013c10301f00f002c01700805bc25015704b05bc36c16e0a305b427c16c09705ac24c16a04b055813c0e301b00a402c01500805a424015504b05a435c16804b055013c0c7017009c02c013008059c23015304b059c34c16604b054813c,
    0x18211b060703c12c04b02a103018001805fc34012b04b02e106c17f11705f838c17d0df05f036c17b08f05e813c17980f04a812c0c841702ca04c0a800c05e027015b04b05e038c17709f05d826c17509705d024c17304b056813c12302300f402c01900805c8580,
    0x191053064204c13404b02a204018f120063808013304b02e908c0b380f063436c18c40f04c812c0aa40c062c08018a0d804c412c0bc02302d203c18a11f062438c1880db061c35c18608f061413c18440f04c012c0aa00c060c0601820d404b412c0b601b02c603c,
    0x1a0c1704f812c0d6014067c08019e11c04ec12c0d1c23032904c19e163067447c19c11b066c34c19a093066414c19881304e812c0c1010065c38019602004e412c0cf823032504c195093065204c13804b02fc040193018064845013504b033306c0c6413064856c,
    0x1ae02006b467014704b049c07c10ac23042106c1ad1e306b106c14604b03d80601ab0a006a808014104b049007c0e9c23039005c1a90d706a305c14004b035b0501a7020069856013f04b041906c0eb823039405c1a619f069458c1a4117068c35c1a2097068415c,
    0x14b80c052c01005115800a156c1ba49406e81601494080524010042158009856c1b955886e44721b851b86e057e1b751486dc4511b649346d835d1b5c1f86d616e1b4c1b86d217e1b345086cc0521b245046c80511b145006c40501b0c0c86c212204111406bc180,
    0xfa004871f4501c7058071814014dc10053401006315800a856c1c5d5887144721c4d1b871057e1c3d14870c4511c2c1f870836e1c1c1b870437e1c0cd087000521bfcd046fc0511becd006f80501bdc0c86f40311bc00c06db24d1b605741884501bb8d406ec160,
    0x1e1c0b05411301e0158077c1801de018053c01007416000b058c1de05f077408c1dc017076d04c1da80f076702c14e04807605721d715b875835d1d585f875216e1d3050874807e1d101f474007c1cfc13873804d1cd013073003d1cb40b872a02d1c980b072201d,
    0x2615b00485601f608f06dc01c15200807d45701f40600799070151004022858002e56307cc5711f215b47c44721f011c47bc4621ee11847b524d1ec01c87ac0711ea01c07a706e1e8c17879f0321c40df46e017d08911c079817c1e5423079005c1e3413078a03c,
    0x208c97881c25d206097081424e20405f880c17d20205f080416e20005b47fc16c1fe05347f413d1fc007879c06e1d3c1c871802d1bd00b86f002c1b001383680111fb8d807e80501f904c055401002855b00505601f909305500201f849407dc0601f6048054c010,
    0x218053485f072216c1c48570701e801787644711d4418870401e1b400f80bc47021409f084d14c15800803e8010212d140844060210050055c01002a15b0058560210097083c18c20e05f083514c20c84f081c56c1c300706f405c156008082c56220a0d74824272,
    0x1e901787884711d5418870801e1b500f80c847022c0a308ac17c22a05708a514c22884f07c001c15a008089c560226d200894080214058056401003116000b058c22415f488c56d22211c8884462220118487c45221e0d3487424d21c05c886c17121a05c086416d,
    0x24255b090456024048c04ac01024009708fd18c23e45f08f416c23c05808ed14c23a84f08e401c20a15b06c302c12a40c08e057023742008b017015b00400d058002e56308d847223511488d045123311408c824d23105c48c015d22f81c88ba07122d81c089067d,
    0x12e40c094117e24f05c893816e24d058893315e24b853892801e24405088f01521f808f86e802d1b200b86c402c042007410401c01244f801413200100449245602488d8091d25024604c090956c20588c06d905c12d408091824c24545b091016024300704b1030,
    0x24d05804c903025d160097008025b498095058c1b580b04c401025b0a3096917c25945b096015c257453095a13c255007093c16013040c094525012f004095157e25415b894d572253158894b4512528d4490935d242117487b16e21e89f894426c1b740706cc02c,
    0x26cc5789ad13e26604c88f31521fb09386ec02d051007405214e007050800401126a15809a41602688d0090b56c13500409a023c26785b099816026500704d2040264160098c5702628e0095158c21e89706e008c1b480b04cc01026105b098114c25f84f097801c,
    0x27a45309b416013881009e47802718d404dc01027859f49dd67127615f49d457227415c49cc5702728dc49c81712428df490817d23289788c845e21d89b887446e20a88c88281411ed01787590621b680f86d801e27109b04da04027045f89bc17226e05b89b4162,
    0x244850884825e1c700b46fc02e1be00b018c01d062007005b15e00905480040112871600a1637027656308c935c13b0040a186802850a30a1217c283c5b0a0815c2814530a0213c27f00709bc16013a81009f858027d4a009f2080278163087535c13900409ee16c,
    0x13ec140a4345020805004f4010293d5f8a4c56e292d5c8a485622918d44a45251242cd7490825d218c5b886047e207c50881c1412060500a4026c1c3c07070002c13cc14008815028f09c8a3917e28d05c8a3216e28b0588a2a14e28904f8a2001e26644c892024e,
    0x2a31600a88180293d6308c317c218117071008c1c101305040102a1c5b0a8015c29f4530a7801c28b058050305029d1600a7018029b8200a6b460293163086716c1c201304fc01029a0a30a6717c298c5b0a5c15c2964530a5613c2940070a3c26028d0580824250,
    0x2ae49c4a4c47d2780df495027d1d7014871304e1b840b8ab467c2ac4d7088317c1d9c5705080100200140aad57e2aa15c8aa745d2a84d78a9e35d2a64d70a9425d2a4c578a3745126d8d4493d25122705b488716e1e001b41d005d03105740bf15c00b054400c051,
    0x2aa1588a2f4512868dc49be35126309f493525123805f48d717e233c5f087f16e20bc5087d407d1ef01f87600621c501386e402e08a017422405c03405740cb15c00d054400d0512b6d200ab45601430040ad767d2b459c4acf56e2b2d1c8ac74712b0d1c0abe371,
    0x2cd59c4b334712cb8dc4b281712b599f4a4e37d27611f495017d2c91a30b2057c2c71170b1935c2c589708d318c1f001707b808c1e2c5705100102c415b8b0c56d2c255b0b0445e2c0d174afc45c2be4d78af735d2bc4d70aee25e2ba4974ae625c2b8c578adc05e,
    0x1db00bc76404f164004c58a03315e408c0c10632dc0630b6c16c2da0570b6414c2d804f0b5c08c2d601b0b5405c2d48130b4c5802d20200b446702b5d630acf56c224c63088f16c1f201f051c0102d11e30b4156c2cfc5b0b3806c2aa15805180102c915c0514010,
    0x2f80dbcbde3632f60d7cbd63532f40d3cbce3432f209bcbc52632f0097cbbd2532ee093cbb52432ec08fcbad2332ea05bcba41632e8057cb9c1532e6053cb941432e404fcb8c1332e204bcb841232e001bcb7c05f2de014cb770432a4118c88846f1e3007c78403f,
    0x222c5b876701d15c00441f805102b158803056e0020174c3917230d05b8c3016d30b41f8c2807d30941f0c210723074138c1804d3054130c1304230340f8c0803d30100f0c010322ff40b8bf802d2fd40b0b680221cc04b872015e2fc15bcbec5632fa117cbe4453,
    0x3280570c9c13c32641f0c9506c3244170c8f04c3040530c0016c3220230c8405c32080f0bfd04c2d8008072212c02005b0c7d57e31e15c8c7445d31cd144c6c35d31a8d44c6425d3184944c5f17e31605c8c54162314c538c4f142312c4f8c46132310c4b8c3d122,
    0x33c490ccec23f33a48ccce416f338058ccdc15f336054ccd414f334050cccc13f33204cccc412f330048ccbc06f32e418ccb506232c017ccac05e32a810cae0453236117c79002f1e2013c77001f1da00fc73401e1c900f858d02315f004c576033033014cca417c,
    0x35101f4d4007c34f01c8d3803e34d00f4d3003c32840c8c8402e3200138c1804d3054130c0a02d30180b0b6c0222d9810873812e1ca0538d2c56f34a158cd2446f348118cd1c36f3468d8cd1435f3448d4cd0c34f3428d0cd0426f340498ccfc25f33e494ccf424f,
    0x36615b8d94562364d144d8d35d3628d44d8525136005c8d7f16e35e0588d7714e35cc508d6f13e35a84c8d6712e3584488d5c07e3560188c7745d31949748db17e1e2c07473c04e1cb00b858401109b41440b457200e55f800805d35505c8d5016e35305b4d4807e,
    0x160004c0dc05336d0630db204c36c01b0dae03c36b0170d3e14c34f05b0c2313c3084570dab05e36a8138da903e36a00b8da702d36980f4da504d3690174da302c36880f0da104c36801703db0520f681083d90320f60088d9d08c34e0170c9d030307c0b0c0d04c,
    0x37c8dbcdf016f37b8d8cdec16337a8d7cde815f3798d4cde415337888fcde014f37788ccddc14337604fcdd41333748d3cdd012f3738d0cdcc12337201bcdc40633700188dbc05f36e417479704f1e540bc77603f1dd007c74203e1d00078597043165408c582033,
    0x38605b8e1416d367c178d9d03e35180f4d4405d35080f0d4005c329c148ca50323228138c8802e30a80b4c2804d309c0b0c2504c2dc8108b700221d1853874412e38415bce0c56338289bce0846f381d18ce05263380917ce0025f37fd14cdfd25337e493cdf5243,
    0x30b4130e49562391d1c4e45271390d174e4125d38fd144e3d25138e8dc4e3817138dcd74e3515d38c8d44e3015138b01c8e2806d3890148e2005138455b8dc905d3668df4d9817d31f91f4c7c27d1d2c13874902e0a501c429007003f59c404067d00401f4e1c172,
    0x3970974e5a35d3960574e1806d357c138d5d02e35480b4d5004d32b80b0cac04c30d8074c3403d1d78df475c17d3954588e2906e38501b4db906c35380f4d4c05d30c80b4c3004d1e6857879813e1de853877812e3940600e4c17036d01c0d4a03c3520170c2f02c,
    0x350040e5101e3940074e4d16d39301f4e2507e38905b8d5b05e3568538d5903e35604b8d5712d35580f4d5514d3550174cb703c32d84b0cb505c32d0530c3b02d30e84f4c3904d30e057429001c36f01f0cb203c32c0170b8302c2e04130e646713981588e5e45d,
    0x3310170c6406c310c0b0b8904c39c0d30e6c12c39a00b0dcc08c3580130cc006c30f40f0b8505c0aa0080e5417037201f0cbe03c32f0170b7f02c2df4130e5527c3950a30e2108c38805f0cbb04c32e84f0cb906c32e0570b7b03c2de8530b7905c2de05b029401c,
    0x3a404b0e8f02c3770230d7006c33ac130c4f03c2eb017074c13c0d60080e880603a10900dd808c33380f0ccc05c31b01b0c4b02c312413075816c3a10d70e8027c39f04b0e7802c3750230cca04c33201b0c4603c31101702fc02039d0180e702303740230d6603c,
    0xf60080eb658039605b0de807c34580f0cdc05c2f2413088b02c1d7063075212c3ac0970eac12c3790230d1004c33601b0c5403c2f101700ac02c0170080ea80603a90940de008c35d0170cee03c31d01b0c5302c2ec4130ea436c3a80a30e9e27c3a60970e9624c,
    0x2e4c0b0b9104c3b811b0edd03c37d4230d6b04c35a41b0b8f02c2e341703050303b60600ed40803b409c0e4007c34780f0ce405c31f4230c5f02c2f0413075612c3b40e30ecc27c3b209b0ec425c3b08930ebc12c3ae00b0e3c08c3460130ce006c31600f0bbc05c,
    0x35e4130d0106c2f540b0b9d05c0f640c0f0036039705b0e0007c33f0170be302c2ea41308da03c3c011f0efc38c3be0db0ef435c3bc88f0eec13c37f4230d8104c33e41b0bdd02c2e941700b503c01940c0ee86703b94180ee035037e4230d8c06c35b80f0d6c05c,
    0x3c815b02807800401e30f1c6703940600e1007c34b80f0d2c05c2fcc0b0bf104c3c71e30f1816c39805f0e4808c34a80f0d2805c2fbc0b0bed04c03f01b00d40603c59200f101803c30200e3407c3664230d7e03c3410170bdb02c2e84130f0836c3c140f0e3108c,
    0x2c1e300607803de09b0f7514c3dc1600f681402931630f6f5803da0970f6618c3d80600f5c17c3d6c5b0f5514c3d484f0f4c01c1e70170f485803d104c09e058c3d10930f4018c3cf0600f385803cd048095058c3cd08f0f3018c3cb0600f2801c3c959c0f24580,
    0x3ef05c0fbc28c3ee45f8fb715e3ec8538fac13e3e705c8f8026e3d80548f3c1423cb04c877c02d074007406016e00b05880040113ea1e00fa41602b5de30fa427c3e80630f9c1803e645b0f9415c3e44530f8e13c3e20070f874803e005c0f7c0803de0540e58050,
    0x40415b100e38040249c0ad678c1e880b100518c4000600ffc17c3fe4530ff401c3fc49c0fec0803fa4940e5c0501e980b00b878c01a1e00fe827c3f945b0fe015c3f74530fda13c1f10070fd45803f404c09d958c1ed4170fd024c3f34630fc81803f10070fc3480,
    0x2b389f4acc47d1f280f87c801e03619c103067c398018102d27040b0a307c401c1ec00b102816e409c57902214e40744f901801e40209b90001623fc09f8fc81423db0948f631523cb44c87d002d1eb00b87a802c08a007422401c01a45f80341720010045014780,
    0x41119f504067c4008d450001513e7d144f9d2513c901b4e6507238315f47ce03e1f3007828005d03855f80d857c00f15c800c0514145a0104c07040c158010078c0381e0104857241115c504057040f018903806140d018101335d4044574f2005d38419c4dc8672,
    0x41f00fd07912341e00cd07513f41d00bd07113341c008d06c01f24a450c9280431b7453c6dc04f043004d06834c41904b105d670418d1c506237141849c50601712b5c5f4ad627d2b54df4ad447d4171a3104867c37215f105a45d416097505735d415457505067e,
    0x25054400925d00205750bc56f42e158d0b546f42d117d0b146342c114d0ad26f42b0d7d0ab35342a898d0a536f429097d0a3363428894d09d24f4270d3d09b343426890d09423f42488cd08d06f423057d089153422018d08516f421017d081163420014d07d12f,
    0x43744b90dc12d43604b10d507e43501b90d107243401890cf04e43380f90c904243200c90c557243115890c34514308d44f3157e3cc15b8f2907e3ca01b8e6d07239b018899f45d2678d7499504e26500f86dd02e1b7007864704219180c85990221660048095251,
    0x44f014499c05d0718d4417745100a117402035d44e0d3113425c44c063112d17c44a05b112401c43200b112024d44745f911817d44505f111017244305b910816d44145b110016243fc5790f815d43d05710f015243b00790e801d43900702a001143808f1064010,
    0x43400b11a517e46805f519c17c46605c919715e464057518c15c462853918414d460453117c01e45e007517401c44445491001420aa004517023c44d05010ce01c45bd5f916857245915b91605624574d3915825d455494515317e453c5b914b14245184c914312e,
    0x39c014c9a103f26800bc64b033192808d1ec23c46e05810d401c47a99f51e567147855b91df47147651751d63714744d751cd25147205451c712e47001c516c47d4598df4f3007d09c05c420127100e09f403017d46f0d311b827c46d06311b016c46b45711a801c,
    0x486518d21845348549bd21435f4844d4d2102634834dbd20c25f4824d8d208253481493d20434f4804d0d20024347f08fd1fa23347d013d1f004347b45bd1ec15f46f458d1bc15345c44fd17012f44e44cd138123438007d0d801e41a004cf3506f3cd017ce71063,
    0x41e007017412c044448124c24048b08f112014041d007124c35c492093122834c451057107001c07104b011012041b007124527e49009c923c26e48e098923424e48c090922c23e48a08c91c617e45785390dc01e1f600b459c02148915bd22056348751bd21c45f,
    0x4a20e3128527c4a009b127d25c49e093127402c4900d311cc18c422007020012c046448127158048f08f108401c49b497126824c48e0d311c817c420007027012c046048126425048d08f107c01c4990db126028c49749f125925c495093125002c48c0d3114816c,
    0x4a9013121023c44405010aa01c4a84e0129c18048308f11d116c459863114d14c429007129924c4a5853120823c44005010a201c4a405811fc23c47e114115a16c450453114015c425007128c14c47e88f11f856c43c050109201c424013128936049108f108c01c,
    0x193c14864e04201240f804802e00140c80040224b406012cc0804b219c122423c47a86311e116c47805f10bc01c4b21e312c416c48808f119816042e00712c01804af558121423c47645b116c18c45405710ac01c4af16312b947c4ad11b12b034c4ab49312aa14c,
    0x4c915b932047e4c711493184514c54db93123424c38d0530a3404c189f930226e4bf49492f92514bd49412f22324bb05452e813d4b904b41944504b809312282304b701411f41204b705b11f02304b641f92d806e4b5c1792d604e39d41c8e740621f744f87dc12e,
    0x4d905c936016d4d7053532027d4c504f487804d08c11c135827c4d545312382304d4d18134d2504d10501234120052158013856c4d215b134425c4d0063133d17c4ce453133401c4c784f12f035c48c08c13323604cb49412e013048b048019c56004e55b132857e,
    0x47f04813b85604ed06013b126049104801d458005016313b028c4eb45f13a815c4e945313a001c4e284f12402304e7158139b4804e54a0135816048f0480238580050163139056d4e311c93884714e111893804614df114937a3724dd8dc53723704db0d7936824d,
    0x4d2050490805d4f909b131d14c4bf09312024504f809c93dd17e4f605c93d416e4f405893cc14d4f204f93c401d4d4097933024e4be09352f424c4bb0d7529013226900b464c011067853819514c052c57802415200705093c056c4ef15812e513c4b909311fe340,
    0x50ac5f142716c508057141d14c50684f141401c4f809813d816048491414105805034a0140058c4fc4d7132318c4c144f120c120502c5b140514c4f4058120a4504f9d14120412050055f93fc5724fe15b93f45624fc11f93ee3514fa01453c035d4da89f935f16e,
    0x51619f145535c4e2c57138317c486048145157e51315c944845d5114d7944135d50f4d7143b15e50d01753db4514f48d453b826d4e705b538716e4df89f8e7405108e057423315c075097403525100b054543058050bd1813f858c4d8c5b130024c485048142c28c,
    0x28d7400815d5250d7149012c523160148808052119c147458c4e4c5b139227c489048148478c52015b147f16c51f89b144c560488048147b480516158121c12051d19f547167151bd1c946b471519d1c146237151701c540037d4fe11f532b13e4c9893895007d,
    0x531c4f94c0051492448891405d071494413745100a117401825d52f0d714b824c52d06314b017c52b05b14a801c529093149001052815c949c562526d1454992513f355f8fc407e3d015b8e7c062245d17491525d243813890c02e16880c85a00120278d4409c151,
    0x54444f550d13c54201c54ea27d53a11f4f4007d3a0014420637108105c403237d00c05f550435c54009f14fd17e53e05c94f715e53d44f94f001d44085491001320bf00454ec24c52e85414eb57e53915c94e056e53715894d935d5358d454d224e533c5b94cb142,
    0x55705f155a14c55605b155401c55405b954c16d55245b154715e55144f954213d550057553e13c54f057153801e54d007553001c53e058911215244404c830401154b093150016054a59f552567154855b951f47154749c551b45d5464975516351545054551313e,
    0x525004cfd006f3d1017cee10633a1014c91a03f24600bc60b033182408d58424c55805c158167155fd14557d25155e893957824d55d093157237155c05c556f35d55b457556807154a19f54e237d53805f4fcc07d09ed1c427927100e91f403827d5590d7156028c,
    0x570158d5bc46f56e118d5b445f56c114d5ae36f56b09bd5aa36356a098d5a635f569097d5a2353568094d59e34f567093d59a343566090d59423f56448cd58c04f562010d58416f55d45b956416354b057d50d15e541054d4ee12f53b04fd4be13352f048d4a401f,
    0x57e09715d035c54505f020412c05304815f425057309315f436c57c0a315ee27c57a09715e624c57800b15c835c53205b013412c04484815dc27e57609c95d426e57409895cc24e572090957917e54445b94d114e4b808f924c23244804c87e402d16900855c456f,
    0x58d0e3163036c58b0d7162a23c58944f162003c5680971100130587058159424c5640d414d816c53184f14c415c58604f159125c56411b10f013058509c15dc24c5850e3161027c58309b160825c581893160002c5760d7157c18c09e04b015412057f96015d424c,
    0x183c14860d032014813805002e0018108004022597060165808059519c15c424c54a463152116c5951e3165116c57009314f8160593920164818056b093156c17c53846314ce13c5910db164113c56a097111013058f0601638360569093151916c53a863163847c,
    0x5aa0d096a42725a8093969c17e5a605f569417c5a405b968c16d5a205b168414e5a0053567c14c59e04f567401e4d209752f023d44844c882805d205c0b567078059b014158c13059b05b158824059a41f966406e598c17966103e3b901c8e880621fa85387e812e,
    0x5bb09796e81725b905c56e01705b705b56d44715ac88c93f014d4da0d3532837d4c104b487404d07611c16d827c5b545315d02405b4d1416ce3605b205015cc13004ed5b01145605b209716c418c5b085f16be13c5ae00715c82404c645316b45625ac0df96ac36e,
    0x5cb11c571467d5bb89b96ae2324c90df530012d232013423c4705ce0a3173417c5cc057172d14c5ca84f172401c57609017205605c7d20171a3805b605815d4130078160017c58c5c515f571056d5c311c97084625c111857004525bf49c96f92715bd49c16f026e,
    0x6584f011715e00905480141325dc158176f4505db8d8176d2505db05816a12305a8050159524056504c13c056c4ba84b12e834c5da15c17663805ce05c15dc130091160018558c5d811c975c4525d611457544505d449c974d2715d249c174425e5d005c573c15d,
    0x5e940717982605e405816a42505684d417a125056704c17a026c5e740715993504c684f131023c05a05417982725e545f97901725e305b97881625e1853978013d5df007977801d5dd007176c24e5b4097961c1424cb08f930c23d4c208f091c02d183004419d13e,
    0x7805741db15c0764d7002e35100b05457dc5805f68e0173d37c56b04c13f958c4d7897132718c4c584b17d416c5f405717cd14c5f284f178816056a4d417c45805f08e017bd2605b74db15a4130500163132b18c5ef0a317b917c5ed05b17b015c5eb45317aa13c,
    0x60149c980347160049c57ff4705ff49c17f807150091f540027d4c8c4b932134e27801f57f467c5c1c5f170537c5b5c5716d535c56c04c17f157e5fb15c97eb45d5fa49757e715e5f94d797e005d5e4d1457912515c88db572016d5c2c5b970936e3a201441e235d,
    0x608017981d05d60641717ec5625e2d1457892515da8df576817d5d7c5f975d37e5d5c5f175537c5c0c5b970136e5adc5096b52313ba41c4ee40510918d7424415d08fc57023d35c00d8d44034151605d2018152805fd15815b413060419f580d67160255b9807472,
    0x61415c15bc13061759c585a37161605c585407160459f53fa37d4fe05f49d807d6141a3184c57c612897184845c611017175b18c5d64e3172f15c5cb4d715b813061019f583c56e60e15b583556c60c897983045e60bd17582d25d60a897182845c609c57982535e,
    0x288cd0ca200431c3cd3c70c04f06400cd88836c621c9f188428c620c93188025c61f04b187b07c61e023187704c61d017187058061b020186867061015c181058c60255b171718c5c54e3171316c5c44db15c413061a1e3186556c618c5b186136c5fb15815c0130,
    0x630114d8bf25f62f05bd8ba25362e458d8b726f62d057d8b226362c454d8af24f62b053d8aa24362a450d8a412f628448d89f35f62701bd89b353626018d89736f625017d893363624014d88c03f5aec4fd6b802f578c4cd5e00234cdc8fd33401f494c8cd250013,
    0x59d09347f315e1fc11798d757263515898d23516344944f6656e3d955f8f4f07e3d301b8e930723a401888f735d23d09748e703e23900b870f04e1c300785ea03217a40885ab04216a00480a7451029054400b45d00205758cc56f632158d8c745f63111bd8c3463,
    0x643097190b17c642063190613c641453187c0101fcc0b07f005c022c9b008856c640d18990017263fc5398fc14d63e05318f706e63d01f98f306d63c01f58ef06c63b01f18eb07263a01898e603e63940b98e302d63800f58de02c63740f18da032636408967713e,
    0x64e013d9370435e08d0d6bc13f59f44f55e41334f3490d33812f4c70d3d31824f496048cf5406f3d4017ce990633a5014c8ec01f20d00bc83003f17c004c5b102316b80cc19923364c117192c38c64a0df192436c64808f191e18c64645f191516c64440718d803c,
    0x66504f599013c64944c990501d63800798dd01c620004568034d59ec9787f804d1fdc0b598c56f662158d98446f660118d97c45f65e114d97436f65c8d8d96c35f65a8d4d96426f658498d95c25f656494d95423f65405bd94c163652057d944153650053d93c143,
    0x67905c99e316e67705899db14e675c5099d00515a189395ea1324c7c4b931b13e49544888f505d23ac0745ec01105d49441363510080d7401825d673d1899c8272671c9399c024d66f09319b917e66d05f59b117c66bc5c99a916e66905b59a116c667058999913e,
    0x63a00b1a4117e68f05f5a3817c68d05c9a3214e68b0535a2914c68944f9a2013d68784f1a1801e6850075a1001c44444c91021420d60045a0c25c6828631a0617c66684f1922140639807167b24c05ac9b1a0157e67f15c99f856e67d15899f045d67bd1459eb17e,
    0x5b104fd6c124f5a5093568b13e57c04cd5ed2434d004bd33e34f498048d25e3433d7017cea005323f40bc8fa03f20f007c83b04f20201347ff01d17e80cc5f502316e004c5b704306a050da5c36c6960a31a5427c6940631a4c15c692c531a4401c66b093199c25c,
    0x63b00718840115a60d7568f24e203017480302d6b115bdac05636af11bdabb4636ad917dab34536abd149aa836f6a98d8daa035f6a78d4da9826f6a5498da9025f6a3494da8a23f6a188cda8016f69f058da7816269d057da7015369b053da6814d69901bda61063,
    0x67e05f569d13d5a48938f6407d3d64174e9c05120440f480602d09d8dc421127108349c003827d00c8df5ae75626b809c9adf25e6b60975ad425c6b485b9acc16d6b245b1a581626828539a0513e66d05359b114c669c4f59a213c64b850992913264200758f001e,
    0x20601345fe03317f408db382806cd09c1b3025c6b445b1a5717066e45319aa13c63d0071b2d67d6ca59c5b2556e6c85589b1f4716c65175b174516c48d89b0e3516c249c9b052526c04945afd2506be48f5af41716bc4575aec1516ba01c5abd35d6a04975a0247d,
    0x6d6097db573636d5094db5334f6d4093db4f3436d3090db4823f6d148cdb4004f6cf010db3315f6cc05bdad715d6b505b5a5f163697054da0f12f68304fd9bf12d66f04f593213364c448d90c01f63e00798880133dac1bcf6805f3a9c18cea4053240c0fc90002f,
    0x6230071b845626e009f9b7c2726de09b9b742626be05f9adc16d6b605f5a6817c67104f59c014d63f00796c824e57d090934835d4d108f926423221000b481c05d16f0085b7056f6db158db6b46f6da117db674636d9114db6335f6d809bdb5f3536d7098db5b36f,
    0x6c405b9b0417e6bf05f1ae416d6ab05b19cc13d672053590001e5a90d7482405d08304b1b7825c6ced601abf16c69d05f196e13c659453189401c6e309b1b8825c6dd0db1b0c17c69c063196814c658057189001c09d04b01a012069bc5f1a6c18c65584f195514c,
    0x65d84f195d14c6270071bd838c6f5c9f1bd026c6f30971bcb24c6f100b1b7c36c6c00631ab017c65c053195815c626007021012c068c481bc05626ef09b5bbb25e6ed0975bb325c6ebc939ba824d6e9c931ba023d6e704b9b9802e6e5c0b5b9302c6ce04b5b3417d,
    0x65345718b101c44444c1be01606d20971b443406a28631a8917c67c45b19da13c67645318a401c6f704f1b4526c6d11171a8737c6a18631a8517c6a10e319d723c67585319d515c6750db18a101c62800f16a925c5aa11b10f01306f609c1b8025c6ad45b1a8017c,
    0x5ac0d71c0c36c70244f1b5c26c6bb4631a9d17c677453194515c62e4071101130701d601c001806ff0d81b5825c6c6c5b1a9017c68006319ea13c65445318b401c5ab0d71bfc47c6fe0e31bf436c6fc0d71bef23c6fa44f1be403c6d509b1b1517c6a346319e514c,
    0x10089c2f58070b0a01c281807090201c206706dc0971b2c18c6c9c5b1b2417c66384f198d14c6330071c2078c70745b1b6c25c6c8c5f1b2018c68d058198a13c66245318c801c706d201c142807040601b6025c6bc05f1aa316c67e46319e213c65245318bc01c,
    0x7181189c5c4617161149c5417271405c5c4c17071205b5c4515e4fc093535c34d218013424847071009f1c3d14c6dd0941c380506d00501c3816c6cf0941c3707e70d01b9c3204e70c40f8eab0723aa018884715e21104b860204218040c805b05e01600b8007052,
    0x180004414913e045853801c14200504c9c945606d248c1b481404f015b1c93570723d201c8817071211f1b8014007916001cf58c7220a31c8717c7204531c7e13c71e0071c6415c6df0941c7456071cd201c401606de05002505800731631c6c56d71a11c9c64471,
    0x500563136a25c73645b1cd514c7280581b5d3407341601ccd2606d605013f858c7330a31cc917c73145b1cc015c72f4531cba13c72d0071ca81606d54d01cb12506d40501cb026c6d34d01cad17e72a05c9ca416e7280589c9f15e7260075be01525b3093934c23e,
    0x5008df53f827d29301f5d0867c7414d71c6715c717c5f1b64140740d5f9cfc57273e4d79cf735d73c4d71cec25d73ac579ce405d72a4945ca235172411b5c7416d718c5b9c5847e6e10504ea8051094057424b15c079d17403745100b0545ce05807378e01b60140,
    0x25e00b85c001203c05440ac56200415b800815d7520971d4412c7500231d3c06c74e0171d3404c74c1601d2c08074a19c1d1c58c71bc5b1c6c47c6dc0501d2878c74915b1d2316c74811b1cfc5606db0501d085606da0501d1c67d74659c5d1637174449c5d0c071,
    0x760c5b9d7c0517364d757d445d5f28939268121261017497e02d09c054413c56200e15b801815d75e0971d7424c75c0631d6c16c75a0571d6401c7584531d4401075715c9d5b4517558d45d51251753c5b900557e3fd01f8eac0622a1d174a7804e27b8d7498425d,
    0x76b050dda804f769c10dc3c23f6e248cd7e44635f304fd70c46f5b5093d6441334d504bd26c1233fe017cf7406f3c2014ceb106329f00fc98001f21300bc6a603318d004c5c5023077498dda025c7674531d7413076655f9d95572764d145d8e35176289f9d85262,
    0xc15b802035d78509b9e1026d78345f9e081727814539e0014276744f9d781327584075d4801177f15bddf856377d117ddf045377b0dbddea3637790d7dde23537770d3ddda34377509bddd226e773097ddc9253771490ddc016f76f058ddb815f76d054ddb014f,
    0xe55f802845d79309b1e4818c7910571e4014c78f0071e0025c7680501e3b57e78d15c9e3345178b4db9e29251789c5f9e201727870589e18051736d175cd714e703c50970f16e5b5c4f95fa132502497540712e4a644889ec05d27ac0746540110818d44178562,
    0x7a58539e9014d7a34531e8813e7a104f5e8213c79f0079e7801d79d0071a3415253e05091981320f60045e4c1507814531e7056e79b1589e6847e79911f5e623517974945e58172795c5b9e500516e3c5097d735d5f4c4f940825d2a10174a8301d09dd1441cb572,
    0x4d608f885002d7ae05c1e0d14c7b75589edb4717b58dc5ed135d7b309b5ec92517b105c5ec115d7af01c5e7237d78e11f5d9817d40101f4ffd05d0a749c427d67101019f403827d7ae0a31eb416c7ac0571eac14c7aa0071e0825c7a909b9ea315e7a70575e9815c,
    0x7c409f1f0c26c7c20971f0424c7c000b1ee037c7b20631dc815c0a704b01e81207bf1601dd514c7be1589ef44727bc1175eec35d7ba0975ea416279ac539e2f13e78504f5dd313c760c4b9d4f01d3de0175ee45727b80989ecd16e799c579e1014d71009796d824e,
    0x7bb09b170d14c7878571e1c24c05e053014c1407ce1201f341807b005f1db914c7664631d8a13c7cc04f1db515c76d0db11981307cb0d81ee826c7704531f2c47c7ca0e31f2436c7c80d71f1c23c7c600f1dbd15c761453013c13c04604c1f142707734531f1438c,
    0x7794531f7815c778c531de035c68d0541f745607bc09b1ded14c7dd19f1f7058c7db1171f6835c7d90971f6005c796c5b1deb14c07205701a01507d70601f5847078e4631e2514c7d61631f5447c7d411b1f4c34c7d20931f4414c7d00131e2215c53e0501f3c380,
    0x7e440f8f7c16e3c445c8f0d0722dd00b49f014e22504b885812d21504b06ab052196810863903203100b80bf02c01801b800c0620010089f8c0807e219c1dfd14c7e21e31f8426c7be09f1edc18c77e453027c16c07a0581f802807df0601ed017c79cc631e5415c,
    0x7ff0071ee02607fe19f5ff456e7fc11c9fec4717fa11c1fe445d7f80575fdf14e7f60535fd614c7f4c4f9fcc13d7f2c4f1fc712e7f004b5fbf12c7ee0079fb701d7ecc071ea41527ebd201fab4707e801c1fa45807e8063088b02c21704b1f9f07e7e6c179f9604e,
    0x813d1c204e38081249c204818051d1e3136e12c811d20204128080f05c20352507ba054014078c0471e0203848080d09f203116c80b057202914c809007138e13c80859c201c5808068e020112500a11e0022278c805160201027c80345b200815c801453200213c,
    0x821d20208347081e49c207c48081e0a3207401c4e384f137823c81c05ba06f15e81a053a06413d818007a05c01d816007204826e81009f9f341627050949c10152592050939423e4dd08f537023c18e004423913e08c84f011d17e00d05c80141328151e0205056c,
    0x5bd093129c13219600441e214e076453015016e00b058801c14282f1e020bb47082d06020ad2506045e316ec24c82c0e020ac27c82a86320a418082845b209c15c826453209613c824007208f4708234a0208a3708220601eee3507bb05416f113c05f1e30150780,
    0x6a019c573f13e5b7093536034d230c07486404d06919c20f427c83c45b20ed14c83a84f20e401c71a0571b9c280838d2020df4708364a020d23708350e020d028c5c345316fc24c83345fa0cb15e83104fa0c001d82905ca08826e7710535c131525c609396f824d,
    0x3ad418c9f402f26200fc89804f21a013465d02318f80cc5cb04308511be12078084715b211b470846060210e67c8435631d1c78c71145321163708444a020f52507bc8d401ce78c06b1e0210e56d842d18a10746184005ca0fc17183e05c1fe74527120535abc672,
    0x84e04be13412d84c448e12c01f84a007a12401382d097e0b125382309be04c35f8110dbe03a363806117e0174537fad149f3d2637ce8d4deff46373708fdc192336e7058db381436c205bda7816d5c7093d6e024d57f490d39834f49c8d0d00c05f3e101bcf14053,
    0x7140975c4c25c6e709c9b3825269f05f57d824e5b90d7564c242592850940c23e4a808c929d1322a200b486c05d1ab00846a8011094c57824815c06b45f81a417c00d05c802415285815be15c563856057e15415d854054e14c14f852053614413f85004f613e133,
    0x83549c608037d81f8dc5ff34527ea01f5fa70717bdd189ee74615ba093536434d21c013619416e86405b618d16c862057618614e860053617d14c85e44fa17413d85c84f216c01e85a007616401c84609ba11027e83f09f60f827c7fbd589f802627df0589c7025e,
    0x71b88f980847d5c4893939212d4040174ace07d22380b425467087419f215f4807be0581ea4150873d1c21cc28c872c5b21c514c87084f21bc01c84009f1c6815c7150971abc17c86e15f61b457186c15b61ac16d86a05761a414d86804f619c12d866007a0dc27d,
    0x87919f20a745180709b5f7e3517cd0544f0c0510a1097425d57e09515f003c57200d49461fd68087e05c21f407087415821634800971e0022378c87c19c61ec57287a15c61e4570878498a1dd26187649821d406286c8dca11d35d8430db605015d80319c9ff5252,
    0x88fd20223b08088559c21bb47088d8dc623127188b05ca22817188905c222007288701c62180708434575ffb45274705f581127d5c5093547637d2b501f489004d8851a321ec67c86d8e0200c57c07f494221057d883917620a35d881057620005d87f19fa1e867d,
    0x7d8cd8df422537c6458df0005372d04bdc7803f6f9448dbc40336e4c0c97a513f5c900bd621133580008d41423f4e8007d2a623349d004d0180432b7118c7c446f1f0013c22c0638990e3226027c89709b225825c895093225012c89301f224806c891017224004c,
    0x1f0007868704219980c861502217300480f415102d15c801157e00205762ac56f8aa158e2a445f8a8114e29c35f8a6cd4e29434f8a4cd0e28c26f8a2898e28424f8a0890e27c15f89e454e27414f89c450e26c06f89ac1ba0e436f824097e02416f7ff017dfb305e,
    0x8bc013a2ec04d8ba01322e70428b880fa2dc03d8b640f22d40328b400ba2cc02d8b280b22c50227ee05b9b981428b0158a2bf4518ae8d462b52518acc5f9fb716e6e5c508fa056e3e201b8eed0723af0188a6345d2940138a0f35d27f00f896525d25500b87c407e,
    0x3bc418cec005329500bca0001f22800fc69102319c004c5d203308d8d8e34447c8d00e3233c36c8ce0d7233423c8cc463232d16c8ca457232501c8b100f232028c8c705f231815c8c5453231213c894004230c17e8c205f630417c8c001ba2fc06d8be01b22f4062,
    0x8de117e3744538dc0dbe36c25f8da494e36424f8d8490e35c16f8d6058e35414f8d4050e34c04f8d2c10e0e826f825057e0663438000d7dfbd35e7db498df501537c18d4dc7c23f6f248cd72813f58104cd43846350604bd38c46f4e20d3d2b41233f601bcf8c05f,
    0x4e2c4b9279122259017495b01d186004420125104f158803056e00609763bc27e8ee09f63b427c8ec85ba3ac16d8ea85b23a41628e8853a39c14d8e605323971428e484fa38c13d8e204f23861328c480762cc01e8b280722540117f009b9ba02428e015be37c563,
    0x9020e3240427c90009b23fc25c8fe05f23f416c8fc05323ec01c8e189322d402c8fa0a323e517c8f805723dd14c8cd44c22d001c8f6d5fa3d55728f4d1463ce3518f2c5fa3c41728f00145fc627e7c70589cc445d72ec539bef1425ed4d757ab13e58a84c938f16e,
    0x906053e414143904013e40f04383b0d7e02815f80109bdfca26e7da8d4df241537c2498dc8023f6f348cdba6232609114d7ac13f5d8117d72c24f58c04cd3a412f49f048cfdc05f3e401bcef80533b1418ca5803f257007c8a402f1a380cc620013175408c241253,
    0x91c09f246d16e91a05b646516c918058a45d14e916053645414c914c50a3dd13e8e304f638813c8cf44ca31501d8b7007a2d901c8960045fcc26e6ea090a44c56f912158e44446f910118e43c36f90e8d8e43434f90c8d0e42c25f90a897a42524390805be41c163,
    0x8ff050239213c8b88072490562923d14648937e921494648017291f01460a856e826c5b9fd136e7d20589cc745d72fc539bf71426eb48c576317e5cbc4f960a132509497541f12e4ab4488a0d05d281c07466801109e8d4418057200e55f802035d91e09fa47427d,
    0x73008fdc6846f719053dbf12335cc04fd60c1334ea04bd2801233f801bcf9405f3bd418cec805328200fc96002f22a007c66e033187408c5d8013093058e4b867c92d16324b025c92bc6324ab14c929c4f24a301c9140d7239445c8b9017249c28c92685f249415c,
    0x8ce44ca31801d8bb007a2e801c8970045fd826e93e15be4f456393c117e4ec45393a0dbe4e63639380d3e4de343936097e4d5253934093e4cd24393205be4c416d930013e4bf043862050e1481428270d7e02c26f802057dfd615e7d38d4df212637c3054dce8463,
    0x6f4c509bb81416ec05017b735d5ecc4f962e132509097542312e4ac4488a6005d297c074688011084d14420f450072158803056e00a117651827e94509f651027c943094a50816e94105b650016c93f058a49414e916053645414c900050a3e013e8e704f639813c,
    0x96494e55838c95509f255016c953057254814c95100724fc26c91809723a424c8bd00b254028c94fc5f24b315091745323a213c8bc0071bb42506e7098253b57e94dd5ca53046d94b8d46529251949c5fa520172947014614f4527f711f9f6416271ac5b9c6714e,
    0x959058e56006f957418e21056387c15be0f035f80c057e00c26f7dc8d4df28153732053dc8623f6fe050dbd62335ee04fd73524f58d04cd61124350a8d3d3ac12f4ae8d0d2841233f9017cefc05329980fca1304f25a007c8ad02f1a580cc677043189004c5dd023,
    0x1019f403017d96509ba59026d96309b253f15e941057650015c92dc54a49a14e91a053646514c901050a3e513e8eb04f63aa13c8d044ca31c01d8bf007a2f801c8980045fe027e6ef094a58846f961d18e58045f95fd14e57836f95d8d8e57126395b097e56816f,
    0x19e80cc62902396f09f2554160942057246d14c8ec84f230001c7f809b01fc28c96e558a5b747196c51765af45196a8dc65a5271968497659d25196601c653847d8f689f61f156e82a8df60a135d8034575f563517c40544fa007d3e64174ecc0510a705c421d671,
    0x972494e5c406f970418e5bc15f9630576558153950053e51014d92ec50e49c13f91c04f64081338fa04be3b412d8d1448e32001f8c1007a26401382b0d7df5a35373308fdbfd2335ef093d63924350b0d3d2be3433e9017ced005329a013ca1403f25b00bc69b043,
    0x7ddd185f2d2613fa01b4f0106196405b653315e94505764c415c91d05363b813d8c2007a01026e7c50989c8825e6f6094973824e58509093b023e4a208c88b002d17800865f456f97c158e5ec46f97a118e5e445f978d14e5dc36f9760d8e5d426f974098e5cc25f,
    0x9670e324d516c9350d7241d15c9070db23c514c8f108f227901c89e00f119813095b45b24c815c90b453237213c89b007260856d981158660047197f0db65fa361965057651814d922c4fa47813d90ac4f23bc12d8c3007a2b301d89ac0720f446d80d09b5ff857d,
    0x96045b24e815c8d784f228c01c5d845325fa28c97e163257e17c95f11f24e616c9390d3248215c920093235a13c8d611b228a01c8a2013018014c055050261018097309f25c836096845b24d815c90845323da18c8f284f227c01c98304f25c928c97211f259d17c,
    0x8df84f22a801c08745b01e81609870a0261818097909f25e056096c45b253818c949057243d14c8db84f229c01c7f909b261415c978ca325e067c96bc5f25ac58c948c5b252025c90ec53243835c8dac4f236845c8a6c07229805c6f00981a3415097f09f25f8470,
    0x3b645c8ed507232a00f4a6c14e25c04b88dc13e22e04f48b413c1a7810867f05218b00880d103e03280f006806e003018800503298a020262467098209f24f815c913453238213c8ab00721f116c7fe0a31ff426c9891e3262026c9810a325b917c93d057244914c,
    0x975494265428c9744d8265117e993c57a64a14e991007661017280f09b9c0015258f05093b423e18b00441d413e04705b802c16200504ca64078097349425cc16051d1e3263c070971494263c18c9700d808da03c22f04f263b07e98dc17a63204e98b00b8fec16e,
    0x6a0c5b267517e99c853a66c14d99a453266413e998007661c27298605ca60356284509ba10426d7230979ab816d5f0093974035d58f85092c013229c00b48c405d1a700441e715e06b85b81a716c00b05880241529971e025e63609794941d1d78c996d202654170,
    0x9a3c57a68913e9a1007668027e90905360b826e7d70589c04252700c54976424e5d3093574824c4b044c867c011091853823d14c05645f8034172007050a6834709a04a025ff45097f494174424c0611e3015878099f8dc25ed25099f0a3267914c97ad58210826c,
    0x9ae1a325f01709ad91766b235d9ab09766a805d9a919fa61b451984494602016d7d78d44ed40510a145741ed57e00f15c802c1519a95a026a12709a701c2698560982494022278c07b1e0269867c9814982697470977494269428c97691c176114c5d4093269016e,
    0x9b201426d956e9b615b66d456c9b4d1c66d23719b449c66d01713c64188f180522d0cdf4b4247d2d045f4b4027d2cec138b3a03e2ce40b8b3801e03f59c40fc57100459f401057d9b31e326c816c9b1c0b26c603c9b141326c405c9b08e026be0809ae59c25f5250,
    0x1adc10c6b60331ad408c6b40139c319f26f12509c215b67074719c08dc66fc1719be01c66212527e14989d2537d74888f986447d618893948017d51f84b4b4007d2cf80b427d67108715c403857d00c59f66f478c9bc09b26ec15c9ba45326e613c9b800726dc67c,
    0x9c7498e71c1639c601be7140639c4018a70f35f9c3917e70d15f9c3097e6f74539bd8d4e6f52539bd054e6dc05f9b501766cc05374a48fdd2814f70848cdc2014361a493d86813f595490d6541335218d3d48412f4b28d0d2c81232d1c13cb4603f2d140bcb4401f,
    0x5228d3d48812f4b38d0d2cc123394418ce5005338b41bce2c05f3704174dc006d0a615be7280809c901ca70a45d9c209766d805d9a691b669826d989d1866252618748db61d016d7e28d85f8816140c01b4f1c0619c8c5be72226f9c84dbe72046f9c7d18e71e363,
    0x9cc80b673103d9cc013672f0439cb80ce72d0239cb004e7285639a7cdbe69e45f9a745be69c25f98ad14e62a36398a494e62816387dd1be1f635f87d49be1f415f7e3d18df8e3537e3498df8c15374b48fdd2c14f70948cdc2414361b493d86c13f596490d658133,
    0x41305b903916d40e05f503516c40d05f0e511723940588dc506d37101f4b4b15e2d28538b4913e2d204b86bf1521af85086bd1321af04886bb0521ae81086b90321ae00880e107e03801b80d906c03601f000d072003018a73704f9cd80fe73502f9cd007e73301d,
    0x9d44df675047d9d3d1c674e3719d349c674c1719d2417674806d9d1c07674602d9d140f674404d9c9558a7245619c415821d735d87591b61d515d87509b674305e9d0813a74103e9d000ba73f02d9cf80f673d04d9cf017673b02c9ce80f273904c9ce017104d17e,
    0x9d9453276113e9d700766a027e95c05b61f826e87709b61d826c70b0949c2815259705092d01321ae004425c16e09545b01ed17e00d05c802c1629d601c27185609d6063275702c9d580f275504c9d5017271467040f45b103c17c38441b0e1007c9d4c5f675227d,
    0x9e0060277c0809ded1c27500709c8158277828c9dd453274c0809c719c21f116c87809b277015e9db853a76814d
  ])
  | 9 => (24, #[
    0x3346f03235f03126f03015f02f46302e35302d26302c15302923f02814f02523302414302124f02013f01d24301c13301a34f01812f01634301412301106f01005f00d06300c05300b04f00a03f00902f00801f007043006033005023004013,
    0x9812d09412c09007f08d07e08807308407208006f07c06e07806307406207005f06f05e06805306405206004f05e04e05804305404205003f04d03e04803304403204056f03c56303b36f03a45f03916f03825f037453036363035253034163,
    0x11845f11445311037f10c37310836f10436310035f0fc3530f834f0f43430f027f0ec2730e826f0e42630e025f0dc2530d824f0d42430d023f0cc2330c817f0c41730c016f0bc1630b815f0b41530b014f0ac1430a813f0a41330a012f09c12e,
    0x17c13f17813317412f17012316c07f16807e16507316006f15c06315806215404f15004e14c03f14802f14402e0bb0430b20330a90230a001309c01209801109401014067f13c67313857f13457313056f12c56312847f12447312046f11c463,
    0x1ff4511f837f1f63731f036f1ee3631e835f1e535d1e23531de3511d834f1d63431d027f1cd2731c826f1c52631c025f1bc25d1b92531b52511b124f1ad2431a823f1a52331a017f19f17e19817319416f19316e18c16318814f184143183142,
    0x24402316615f16413f15e14f15c12f15a14e15812e0c71530c51330be1430bc12308705208503207604207402224067f23c67323857f23557e23057322c57222856f22456e22056321c56221847f21747321046f20f46320845f20445d203453,
    0x29c23329817f29417329017228c16f28816e28416d28007f27d07e27807d27407c27007326c07226a05f26803f26705e26503e26203d26005d25e03c25c05c25b05325903325604f25402f25204e25002e24e02d24c04d24b02c24904c246043,
    0xc90230c20330c00132e067f2dc6732da57f2d837f2d65732d43732d256f2d036f2ce5632cc3632c835f2c43532c247f2c027f2be4732bc2732ba46f2b826f2b64632b42632b234f2b025f2ae3432ac2532a824f2a42432a245f2a023f29e453,
    0x30a36330816330635f30415f3023533001532fe23f2fc14f2fa2332f81432f413f2f01332ee34f2ec12f2ea3432e81232e406f29906328c05328805228405123647d23427d22637d22417d16f04f16d02f16b04e16902e16203f16001f0cb043,
    0x4401135867f35467d35167334d67134856f34556e34056333e47f33c27f33b47333927333747133527133246f33026f32f46332d26332a45f32825f32745332525332124f31d24331a37f31817f31637331417331237131017130e36f30c16f,
    0x38c16f38917e38816e38517338416338117238016237d15f37c14f37b15e37a14e37515337414337115237014236c01f36801e36401d36001c35c0132e907f2e806f29d07329c0631d505f1d404f17103f17002f1170531160430cd0330cc023,
    0x3d46733d147f3d056f3cd5633cc4733c957f3c846f3c55733c44633c045f3bc4533b927f3b836f3b53633b42733b137f3b026f3ad3733ac2633a934f3a825f3a53433a42533a135f3a024f39d35339c24339823f39523e39423d39023c38d17f,
    0x3f923f3f814f3f52333f41433f124f3f013f3ef13e3ee24e3e92433e81333e405f3e00533dc0513c23433981233951223941213901202ed07f2ec06f2a10732a00631db04f1da03f1bc05d17502f17401f11b04311a0330d10230d00133d867f,
    0x43c56e43957343856343557243456243137f43046f42f46342e37342947f42836f42747342636342135f42045f41d35d41c45d41b45341a35341745141635141034f40d17f40c26f40926340817340527f40416f40316e40227e3fd2733fc163,
    0x46015f45f15e45d13e45a15345813345401f45001d44c0133ea45f3e823f39e45339c23337215237013231c07f2f006f2c50732a40631ae05f1ac03f17a04f17802f0ff0530fd0330d60430d402305401144867f44467344157f44056f43d57e,
    0x4b83734b656f4b436f4b25634b03634ac35f4a83534a647f4a427f4a24734a027349e46f49c26f49a46349826349634f49425f49234349025348c24f48a24e48824d48424c48017f47d17e47817347417247016f46c16e46816346416246213f,
    0x4c80514ad24348c13348a13248813148413041f45d41d25d3f234f3f012f3ef12e3ed34e3a23433a012332007f2f406f2c90732a80631e505d1b204f1b002f17e03f17c01f1030431010230da0330d80134c467f4c06734be57f4bc37f4ba573,
    0x51127350e46f50c26f50b46350926350645f50425f5034535012534ff4514fd2514f824f4f637f4f417f4f317e4f137e4ee3734ec1734ea36f4e816f4e716e4e536e4e23634e01634de23f4dc14f4da2334d81434d71424d52314d005f4cc053,
    0x3a74533a42333721423711322fb07f2f806f2af0732ac0631a704f1a403f18705f18402f18302d18005d0f60430f50330df0530dc02306401153c67f53867353457f53157e52c57352857252456f52056e51c56351856251647f51427f513473,
    0x57917e57716d57417d57316c57017c56f17356c16356b17256816256713f56414f56214e56113e55f13d55c14d55a13c55914c55614355513355001f54c01e54801d54401c5400134db35f4d824f4d724e4d435d4933534902433f745f3f423f,
    0xf90230e30430e00135bc67f5b86735b746f5b437f5b34635b03735af47f5ac36f5ab4735a83635a434f5a034359f56f59c27f59b56359827359756259427259357f59026f58f57358c26358825f58725e58425d58025c57f16f57c17f57a16e,
    0x5d316e5d047e5cf4735cc1635c805f5c40535c00515a52335881435871425841415801404df24f4dc13f49724349413341f35d41c25d3fb34f3f812f3ab3433a81232ff07f2fc06f2b30732b006320405d1aa03f1a902f18b04f18801f0fa033,
    0x7401161467f61067360f57f60c56f60b57e60856e6075736045636035726005625ff36f5fc27f5fa3635f92735f737f5f426f5f23735f12635ef35f5ec25f5ea3535e92535e63515e52515e023f5df46f5dc17f5db4635d81735d747f5d416f,
    0x62813e62413362001f61c01d6180135f834f5cc25f5b134358c25356815251035f4e024f4b935349824346414242445f3fc23f3c64533ac23338013232c07f30006f2d50732b406321405f1ec04f1cc03f18c02f13705311e04310d0330e4023,
    0x6a867f6a46736a057f69c57369856f69456369047f68c47368846f68446368037f67c37367836f67436367027f66c27366826f66426e66026d65c17f65917e65417365017264c15f64b15e64415364014f63e14e63814d63514c63014362c13f,
    0x60847d5fd23f5d414f5d314e5b523359014352037d51524f4e813f4e713e4bd24349c13343c27d42a34f40412f40312e3ca3433b012333106f30405f2d90632b805322407d21b04f1f203f1d102f19401f19301d13b0431220331110230e8013,
    0x71347370f47270b47170747070046f6fe45f6fb45d6f74536f037f6ee3736ea3716e736f6e23636dc35f6d827f6d52736d12716cc26f6c825f6c52536c116f6bc1636b81626b407f6b00736ac0716a346368a353681263668153664152660151,
    0x56b15250835f4ec24f4b13534a024347414242c45f40823f3ce4533b423338113232407f30806f2cd0732bc06320c05f1f404f1c403f19802f12f0531260431050330ec02308401173067f72f67d72967372567172056f71d56e71856371447f,
    0x77415c77315376c14f76a14e76414d76114c75c14375813f75513e75013d74e13c74913374401f74001e73c01d73801c7340136f457f6e046f6c437f6bc26f6b826e69757368e46367537366c2636501625f034f5d825f5a9343598253594252,
    0x2d00532c106323407d21203f1fb04f1c801f1a102f19e02d13203312b0431080130f10237c467f7c06737bc56f7b85637b447f7b04737ac36f7a83637a427f7a027e79c27d79827c79416f79016e78c16d78916c78416378015f77f15e77815d,
    0x7a52537a125279d25179925072e67d6fc35f6f935d6e446f6c815f6c026f69a35369346367815367126360a37d5f414f5dd23f5ac14359d23353047d50c13f4f524f4f224e4b41334a524343c17d43234f40c12f3d23433b812332805f30d06f,
    0x26c05123f04f23e03f23d02f23c01f13f04313e03313d02313c01381467f81167380d67180856f80456380047f7ff4737fb4717f445f7f037f7ee3737ea3717e436f7e017f7dc1737d81717d416f7d007f7cc0737c80717be3637b74537ac163,
    0x7c34637c23737c12637c017371b47f71a36f71927f71816f6a74736a63636a52736a416365345165235165125165015161123f61014f5b92335b814353924f53813f4c12434c013344634f44412f3d63433d412334107f34006f2dd0732dc063,
    0x2e005324304f24203f24102f24001f14304314203314102314001383867f83567e83467d83067c82f35f82e45f82d15f82c25f82b35d82a45d82915d82825d82745382635382525382415382005f81c05d81805380737f80646f80517f80426f,
    0x72d37d72c47d72346f72235f72126f72015f71f35d71e46d71d15d71c26d6ab4636aa3536a92636a815361523f61414f5bd2335bc14353d24f53c13f4c52434c413344a34f44812f3da3433d812335407d34906f34805f34505d34406d2e1063,
    0x85b17f85a27f85937f85847f85747385637385527385417385347185237185127185017184c07f84807384407284007183c07083856383556283456183056080b36f80a45f80916f80825f7c74537c63637c52537c416372f17d72e27d
  ])
  | 10 => (19, #[
    0x668dec8d7d8937b015f5e8c6b8d4d6931ac1535247ea053d2919a41434249e804fce9219c1333469e604bcb1a194123220de4017c68318c0531609e280fc48178801f0e086180cc281184013,
    0x202b7bc563766dee917dc8b7b825f6e8a6d8d8da929b4163
  ])
  | _ => (1, #[])

def nodeCount (r : Nat) : Nat := ([ 1, 1, 1, 1, 32, 451, 2382, 2529, 535, 17, 1 ] : List Nat).getD r 0

def readPacked (table : Nat × Array Nat) (i : Nat) : Nat :=
  (table.2[i / 32]?.getD 0 >>> ((i % 32) * table.1)) &&& (2^table.1 - 1)

def sortCodes : List Nat → List Nat
  | [] => []
  | x :: rest => placeSorted x (sortCodes rest)

lemma sort_perm (l : List Nat) : (sortCodes l).Perm l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact (place_perm a (sortCodes l)).trans (ih.cons a)

def rotateState (g : Fin 4) (l : List Nat) : List Nat := sortCodes (l.map (rotateCode g))

lemma rotate_state_image (g : Fin 4) (l : List Nat) :
    (rotateState g l).toFinset = l.toFinset.image (rotateCode g) := by
  ext x
  simp [rotateState, (sort_perm _).mem_iff, List.mem_map]

-- The layer parameter is the number of gates removed from the ten-gate budget.
def catalog : Nat → Nat → List Nat
  | 0, _ => rawCodes
  | d+1, i =>
    let parent := readPacked (parentTable (9-d)) i
    if parent = 0 then rawCodes
    else
      let step := parent-1
      let state := applyTag (catalog d (step / 16384)) (step % 4096)
      rotateState (Fin.ofNat 4 (step / 4096)) state

def links (r i : Nat) : List Nat :=
  let offsets := offsetTable r
  let base := readPacked offsets i
  let count := readPacked offsets (i+1) - base
  (List.range count).map fun j => readPacked (childTable r) (base+j)

def childMatches (k parent tag entry : Nat) (l : List Nat) : Bool :=
  entry % 4096 == tag &&
  let j := entry / 16384
  let g := Fin.ofNat 4 (entry / 4096)
  j < nodeCount k &&
    ((readPacked (parentTable k) j == 1+parent*16384+g.val*4096+tag) ||
      (catalog (10-k) j == rotateState g l))

def refutedBy (k parent tag : Nat) (refs : List Nat) (l : List Nat) : Bool :=
  refs.any fun e => childMatches k parent tag e l

def nodeChecks (r i : Nat) : Bool :=
  let l := catalog (10-r) i
  decide l.Nodup && !l.contains outCode &&
  match r with
  | 0 => true
  | k+1 => decide (k+2 < l.length) ||
      !legalNext k l (fun tag l' => !refutedBy k i tag (links (k+1) i) l')

lemma next_of_plan {k : Nat} {l : List Nat} (nd : l.Nodup) (small : l.length ≤ 15)
    (proper : ∀ a ∈ l, IsCode a)
    (p : Plan 0 outCode blendCode (k+1) l.toFinset) (f : Nat → List Nat → Bool)
    (hf : ∀ tag l', applyTag l tag = l' → (∀ v ∈ l', IsCode v) →
      Plan 0 outCode blendCode k l'.toFinset → f tag l' = true) :
    legalNext k l f = true := by
  generalize eq : l.toFinset = S at p
  cases p with
  | @gate k' rest a b p q ha hb ne al fr tail =>
    have fresh : blendCode p q a b ∉ l.toFinset := eq.symm ▸ fr
    rcases lt_or_gt_of_ne ne with lt | gt
    · exact legal_next_hit nd lt eq al fresh tail small proper f hf
    · rw [Finset.insert_comm] at eq
      rw [blend_swap] at fresh tail
      exact legal_next_hit nd gt eq (al.imp_left Eq.symm) fresh tail small proper f hf

lemma root_catalog : ∀ r : Fin 11, catalog (10-r.val) 0 = rawCodes ∧ 0 < nodeCount r.val := by
  decide +kernel

lemma catalog_link {k i tag entry : Nat} (hk : k < 10) {l : List Nat}
    (apply_eq : applyTag (catalog (10-(k+1)) i) tag = l)
    (match_eq : childMatches k i tag entry l = true) :
    let j := entry / 16384
    let g := Fin.ofNat 4 (entry / 4096)
    j < nodeCount k ∧ catalog (10-k) j = rotateState g l := by
  let j := entry / 16384
  let g : Fin 4 := Fin.ofNat 4 (entry / 4096)
  change (entry % 4096 == tag && (decide (j < nodeCount k) &&
    ((readPacked (parentTable k) j == 1+i*16384+g.val*4096+tag) ||
      (catalog (10-k) j == rotateState g l)))) = true at match_eq
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at match_eq
  rcases match_eq with ⟨low, idx, starts | agrees⟩
  · refine ⟨idx, ?_⟩
    have tag_bound : tag < 4096 := low ▸ Nat.mod_lt _ (by decide)
    have g_bound := g.isLt
    let key := 1+i*16384+g.val*4096+tag
    have depth : 10-k = (10-(k+1))+1 := by omega
    have level : 9-(10-(k+1)) = k := by omega
    have key_pos : key ≠ 0 := by dsimp [key]; omega
    have prev_index : (key-1)/16384 = i := by dsimp [key]; omega
    have same_tag : (key-1)%4096 = tag := by dsimp [key]; omega
    have same_perm : Fin.ofNat 4 ((key-1)/4096) = g := by
      apply Fin.ext
      change ((key-1)/4096)%4 = g.val
      dsimp [key]
      omega
    change catalog (10-k) j = rotateState g l
    conv_lhs => rw [depth, catalog, level, starts]
    change (if key = 0 then rawCodes else _) = _
    rw [if_neg key_pos]
    change rotateState (Fin.ofNat 4 ((key-1)/4096))
      (applyTag (catalog (10-(k+1)) ((key-1)/16384)) ((key-1)%4096)) = rotateState g l
    rw [prev_index, same_tag, same_perm, apply_eq]
  · exact ⟨idx, agrees⟩

lemma checked_node_sound (valid : ∀ r ≤ 10, ∀ i < nodeCount r, nodeChecks r i = true) :
    ∀ r ≤ 10, ∀ i < nodeCount r, (∀ v ∈ catalog (10-r) i, IsCode v) →
      ¬ Plan 0 outCode blendCode r (catalog (10-r) i).toFinset := by
  intro r
  induction r with
  | zero =>
    intro _ i hi _ plan
    have ck := valid 0 (by decide) i hi
    let l := catalog 10 i
    have hm : outCode ∉ l := by
      simp only [nodeChecks, Bool.and_eq_true] at ck
      simpa [l] using ck.1.2
    generalize e : l.toFinset = S at plan
    cases plan
    exact hm (List.mem_toFinset.mp (e.symm ▸ Finset.mem_singleton_self _))
  | succ k ih =>
    intro hr i hi initial p
    have chk := valid (k+1) hr i hi
    let l := catalog (10-(k+1)) i
    let bad := fun tag l' => !refutedBy k i tag (links (k+1) i) l'
    have split : ((decide l.Nodup && !l.contains outCode) &&
        (decide (k+2 < l.length) || !legalNext k l bad)) = true := chk
    simp only [Bool.and_eq_true] at split
    obtain ⟨⟨ob, _⟩, choices⟩ := split
    have nd : l.Nodup := of_decide_eq_true ob
    have card := p.card_le
    change l.toFinset.card ≤ k+2 at card
    rw [List.toFinset_card_of_nodup nd] at card
    have noBad : legalNext k l bad = false := by
      simpa [not_lt_of_ge card] using choices
    have yesBad : legalNext k l bad = true := next_of_plan nd (by omega) initial p bad (by
      intro tag l' applies proper p'
      by_contra hn
      have e : refutedBy k i tag (links (k+1) i) l' = true := by simpa [bad] using hn
      obtain ⟨entry, _, hj⟩ := List.any_eq_true.mp e
      obtain ⟨jb, eq⟩ := catalog_link (k := k) (by omega) applies hj
      let j := entry / 16384
      let g : Fin 4 := Fin.ofNat 4 (entry / 4096)
      change j < nodeCount k at jb
      change catalog (10-k) j = rotateState g l' at eq
      have transformed : Plan 0 outCode blendCode k (catalog (10-k) j).toFinset := by
        rw [eq, rotate_state_image]
        exact p'.rotate g (fun a ha => proper a (List.mem_toFinset.mp ha))
      have good (a : Nat) (ha : a ∈ catalog (10-k) j) : IsCode a := by
        rw [eq] at ha
        have hh := (sort_perm _).mem_iff.mp ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
        exact rotated_isCode g (proper _ hb)
      exact ih (by omega) j jb good transformed)
    simp [noBad] at yesBad

lemma theta_lower_of_checks (valid : ∀ r ≤ 10, ∀ i < nodeCount r, nodeChecks r i = true)
    {r : Nat} (hr : r ≤ 10) (p : Plan 0 outCode blendCode r rawCodes.toFinset) : False := by
  obtain ⟨eq, bound⟩ := root_catalog ⟨r, by omega⟩
  exact checked_node_sound valid r hr 0 bound (eq.symm ▸ raw_isCode) (eq.symm ▸ p)

def checkSpan (r : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => (decide (nodeCount r ≤ i) || nodeChecks r i) && checkSpan r n (i+1)

lemma checkSpan_ok {r n i : Nat} (h : checkSpan r n i = true)
    (j : Nat) (lo : i ≤ j) (hi : j < i+n) (limit : j < nodeCount r) : nodeChecks r j = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    simp only [checkSpan, Bool.and_eq_true] at h
    obtain ⟨head, tail⟩ := h
    rcases Nat.eq_or_lt_of_le lo with rfl | lt
    · simpa [not_le_of_gt limit] using head
    · exact ih tail (by omega) (by omega)



-- Every group checks sixteen small blocks independently.
def CheckedGroup (r group : Nat) : Prop :=
  ∀ b : Fin 16, checkSpan r 4 (group * 64 + b.val * 4) = true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer0Group0 : CheckedGroup 0 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer0 (group : Fin 1) : CheckedGroup 0 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer0Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer1Group0 : CheckedGroup 1 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer1 (group : Fin 1) : CheckedGroup 1 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer1Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer2Group0 : CheckedGroup 2 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer2 (group : Fin 1) : CheckedGroup 2 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer2Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer3Group0 : CheckedGroup 3 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer3 (group : Fin 1) : CheckedGroup 3 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer3Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer4Group0 : CheckedGroup 4 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer4 (group : Fin 1) : CheckedGroup 4 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer4Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group0 : CheckedGroup 5 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group1 : CheckedGroup 5 1 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group2 : CheckedGroup 5 2 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group3 : CheckedGroup 5 3 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group4 : CheckedGroup 5 4 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group5 : CheckedGroup 5 5 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group6 : CheckedGroup 5 6 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer5Group7 : CheckedGroup 5 7 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer5 (group : Fin 8) : CheckedGroup 5 group.val := by
  fin_cases group
  · exact layer5Group0
  · exact layer5Group1
  · exact layer5Group2
  · exact layer5Group3
  · exact layer5Group4
  · exact layer5Group5
  · exact layer5Group6
  · exact layer5Group7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group0 : CheckedGroup 6 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group1 : CheckedGroup 6 1 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group2 : CheckedGroup 6 2 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group3 : CheckedGroup 6 3 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group4 : CheckedGroup 6 4 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group5 : CheckedGroup 6 5 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group6 : CheckedGroup 6 6 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group7 : CheckedGroup 6 7 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group8 : CheckedGroup 6 8 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group9 : CheckedGroup 6 9 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group10 : CheckedGroup 6 10 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group11 : CheckedGroup 6 11 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group12 : CheckedGroup 6 12 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group13 : CheckedGroup 6 13 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group14 : CheckedGroup 6 14 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group15 : CheckedGroup 6 15 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group16 : CheckedGroup 6 16 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group17 : CheckedGroup 6 17 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group18 : CheckedGroup 6 18 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group19 : CheckedGroup 6 19 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group20 : CheckedGroup 6 20 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group21 : CheckedGroup 6 21 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group22 : CheckedGroup 6 22 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group23 : CheckedGroup 6 23 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group24 : CheckedGroup 6 24 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group25 : CheckedGroup 6 25 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group26 : CheckedGroup 6 26 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group27 : CheckedGroup 6 27 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group28 : CheckedGroup 6 28 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group29 : CheckedGroup 6 29 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group30 : CheckedGroup 6 30 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group31 : CheckedGroup 6 31 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group32 : CheckedGroup 6 32 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group33 : CheckedGroup 6 33 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group34 : CheckedGroup 6 34 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group35 : CheckedGroup 6 35 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group36 : CheckedGroup 6 36 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer6Group37 : CheckedGroup 6 37 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer6 (group : Fin 38) : CheckedGroup 6 group.val := by
  fin_cases group
  · exact layer6Group0
  · exact layer6Group1
  · exact layer6Group2
  · exact layer6Group3
  · exact layer6Group4
  · exact layer6Group5
  · exact layer6Group6
  · exact layer6Group7
  · exact layer6Group8
  · exact layer6Group9
  · exact layer6Group10
  · exact layer6Group11
  · exact layer6Group12
  · exact layer6Group13
  · exact layer6Group14
  · exact layer6Group15
  · exact layer6Group16
  · exact layer6Group17
  · exact layer6Group18
  · exact layer6Group19
  · exact layer6Group20
  · exact layer6Group21
  · exact layer6Group22
  · exact layer6Group23
  · exact layer6Group24
  · exact layer6Group25
  · exact layer6Group26
  · exact layer6Group27
  · exact layer6Group28
  · exact layer6Group29
  · exact layer6Group30
  · exact layer6Group31
  · exact layer6Group32
  · exact layer6Group33
  · exact layer6Group34
  · exact layer6Group35
  · exact layer6Group36
  · exact layer6Group37

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group0 : CheckedGroup 7 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group1 : CheckedGroup 7 1 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group2 : CheckedGroup 7 2 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group3 : CheckedGroup 7 3 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group4 : CheckedGroup 7 4 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group5 : CheckedGroup 7 5 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group6 : CheckedGroup 7 6 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group7 : CheckedGroup 7 7 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group8 : CheckedGroup 7 8 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group9 : CheckedGroup 7 9 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group10 : CheckedGroup 7 10 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group11 : CheckedGroup 7 11 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group12 : CheckedGroup 7 12 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group13 : CheckedGroup 7 13 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group14 : CheckedGroup 7 14 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group15 : CheckedGroup 7 15 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group16 : CheckedGroup 7 16 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group17 : CheckedGroup 7 17 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group18 : CheckedGroup 7 18 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group19 : CheckedGroup 7 19 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group20 : CheckedGroup 7 20 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group21 : CheckedGroup 7 21 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group22 : CheckedGroup 7 22 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group23 : CheckedGroup 7 23 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group24 : CheckedGroup 7 24 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group25 : CheckedGroup 7 25 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group26 : CheckedGroup 7 26 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group27 : CheckedGroup 7 27 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group28 : CheckedGroup 7 28 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group29 : CheckedGroup 7 29 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group30 : CheckedGroup 7 30 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group31 : CheckedGroup 7 31 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group32 : CheckedGroup 7 32 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group33 : CheckedGroup 7 33 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group34 : CheckedGroup 7 34 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group35 : CheckedGroup 7 35 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group36 : CheckedGroup 7 36 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group37 : CheckedGroup 7 37 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group38 : CheckedGroup 7 38 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer7Group39 : CheckedGroup 7 39 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer7 (group : Fin 40) : CheckedGroup 7 group.val := by
  fin_cases group
  · exact layer7Group0
  · exact layer7Group1
  · exact layer7Group2
  · exact layer7Group3
  · exact layer7Group4
  · exact layer7Group5
  · exact layer7Group6
  · exact layer7Group7
  · exact layer7Group8
  · exact layer7Group9
  · exact layer7Group10
  · exact layer7Group11
  · exact layer7Group12
  · exact layer7Group13
  · exact layer7Group14
  · exact layer7Group15
  · exact layer7Group16
  · exact layer7Group17
  · exact layer7Group18
  · exact layer7Group19
  · exact layer7Group20
  · exact layer7Group21
  · exact layer7Group22
  · exact layer7Group23
  · exact layer7Group24
  · exact layer7Group25
  · exact layer7Group26
  · exact layer7Group27
  · exact layer7Group28
  · exact layer7Group29
  · exact layer7Group30
  · exact layer7Group31
  · exact layer7Group32
  · exact layer7Group33
  · exact layer7Group34
  · exact layer7Group35
  · exact layer7Group36
  · exact layer7Group37
  · exact layer7Group38
  · exact layer7Group39

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group0 : CheckedGroup 8 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group1 : CheckedGroup 8 1 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group2 : CheckedGroup 8 2 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group3 : CheckedGroup 8 3 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group4 : CheckedGroup 8 4 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group5 : CheckedGroup 8 5 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group6 : CheckedGroup 8 6 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group7 : CheckedGroup 8 7 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer8Group8 : CheckedGroup 8 8 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer8 (group : Fin 9) : CheckedGroup 8 group.val := by
  fin_cases group
  · exact layer8Group0
  · exact layer8Group1
  · exact layer8Group2
  · exact layer8Group3
  · exact layer8Group4
  · exact layer8Group5
  · exact layer8Group6
  · exact layer8Group7
  · exact layer8Group8

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer9Group0 : CheckedGroup 9 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer9 (group : Fin 1) : CheckedGroup 9 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer9Group0

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma layer10Group0 : CheckedGroup 10 0 := by
  intro b
  fin_cases b <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma verifiedLayer10 (group : Fin 1) : CheckedGroup 10 group.val := by
  have h : group.val = 0 := by have := group.isLt; omega
  rw [h]
  exact layer10Group0

lemma verified_nodes (r : Nat) (verified : ∀ (g : Fin ((nodeCount r+63)/64)),
    CheckedGroup r g.val) : ∀ i < nodeCount r, nodeChecks r i = true := by
  intro i hi
  let group : Fin ((nodeCount r+63)/64) := ⟨i/64, by omega⟩
  let block : Fin 16 := ⟨i % 64 / 4, by omega⟩
  apply checkSpan_ok (verified group block) i _ _ hi
  · change (i/64)*64+(i % 64 / 4)*4 ≤ i
    omega
  · change i < (i/64)*64+(i % 64 / 4)*4+4
    omega

lemma all_nodes_checked : ∀ r ≤ 10, ∀ i < nodeCount r, nodeChecks r i = true := by
  intro r hr
  interval_cases r
  · exact verified_nodes 0 verifiedLayer0
  · exact verified_nodes 1 verifiedLayer1
  · exact verified_nodes 2 verifiedLayer2
  · exact verified_nodes 3 verifiedLayer3
  · exact verified_nodes 4 verifiedLayer4
  · exact verified_nodes 5 verifiedLayer5
  · exact verified_nodes 6 verifiedLayer6
  · exact verified_nodes 7 verifiedLayer7
  · exact verified_nodes 8 verifiedLayer8
  · exact verified_nodes 9 verifiedLayer9
  · exact verified_nodes 10 verifiedLayer10

end PEqualNP.Outside.L_meta_2519

theorem PEqualNP.Outside.L_meta_2519 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ (8 : ℕ) ≤ ↑x3 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  open PEqualNP.Outside.L_meta_2519 in
  intro C fan negs first eq
  by_contra h
  have small : C.size ≤ 15 := by omega
  obtain ⟨r, hr, S, hS, plan⟩ := possible_theta C fan small negs first eq
  exact theta_lower_of_checks all_nodes_checked hr (plan_codes plan hS)
