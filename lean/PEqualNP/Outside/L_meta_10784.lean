import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10784

open PEqualNP.CircuitLowerBounds

def wordsNat (ws : List ℕ) : ℕ :=
  ws.foldl (fun a w => (a <<< 64) ||| w) 0

def wordsBV (m : ℕ) (ws : List ℕ) : BitVec m :=
  BitVec.ofNat m (wordsNat ws)

namespace ThetaSigned

abbrev Wire (X : Type) := X → Bool
def inv {X : Type} (f : Wire X) : Wire X := fun x => !(f x)
def bit {X : Type} (b : Bool) : Wire X := fun _ => b
def bin {X : Type} (isOr : Bool) (a b : Wire X) : Wire X :=
  fun x => if isOr then a x || b x else a x && b x
def plus {X : Type} (P : Set (Wire X)) (f : Wire X) : Set (Wire X) :=
  {g | g ∈ P ∨ g = f ∨ g = inv f}
def Closed {X : Type} (P : Set (Wire X)) : Prop :=
  (∀ b, bit b ∈ P) ∧ ∀ f ∈ P, inv f ∈ P
theorem inv_inv {X : Type} (f : Wire X) : inv (inv f) = f := by funext x; simp [inv]
theorem plus_closed {X : Type} {P : Set (Wire X)} (hP : Closed P) (f : Wire X) : Closed (plus P f) := by
  refine ⟨fun b => Or.inl (hP.1 b), ?_⟩
  intro g hg
  rcases hg with hg | rfl | rfl
  · exact Or.inl (hP.2 _ hg)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (inv_inv _))

def Run {X : Type} (P : Set (Wire X)) (k : ℕ) (f : Wire X) : Prop :=
  ∀ Q : Set (Wire X) → ℕ → Wire X → Prop,
    (∀ {P k f}, f ∈ P → Q P k f) →
    (∀ {P k f a b} (isOr : Bool), a ∈ P → b ∈ P →
      Q (plus P (bin isOr a b)) k f → Q P (k + 1) f) →
    Q P k f

theorem Run.done {X : Type} {P : Set (Wire X)} {k : ℕ} {f : Wire X} (hf : f ∈ P) : Run P k f :=
  fun _ d _ => d hf

theorem Run.gate {X : Type} {P : Set (Wire X)} {k : ℕ} {f a b : Wire X} (isOr : Bool)
    (ha : a ∈ P) (hb : b ∈ P) (hr : Run (plus P (bin isOr a b)) k f) : Run P (k + 1) f :=
  fun Q d g => g isOr ha hb (hr Q d g)

theorem Run_pad {X : Type} {P : Set (Wire X)} {k : ℕ} {f : Wire X} (h : Run P k f) :
    Run P (k + 1) f :=
  h (fun P k f => Run P (k + 1) f) (fun hf => Run.done hf)
    (fun isOr ha hb ih => Run.gate isOr ha hb ih)

theorem Run_inv {X : Type} {P : Set (Wire X)} {k : ℕ} {f : Wire X} (h : Run P k f)
    (hc : Closed P) : Run P k (inv f) :=
  (h (fun P k f => Closed P → Run P k (inv f))
    (fun hf hc => Run.done (hc.2 _ hf))
    (fun isOr ha hb ih hc => Run.gate isOr ha hb (ih (plus_closed hc _)))) hc

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def isBinary (g : Gate) : Bool := match g.op with | .not => false | _ => true
def budget (gs : List Gate) : ℕ := gs.countP isBinary

theorem budget_lt_of_not (gs : List Gate) (g : Gate) (hg : g ∈ gs) (hn : g.op = GateOp.not) :
    budget gs < gs.length := by
  induction gs with
  | nil => simp at hg
  | cons a tl ih =>
    rcases List.mem_cons.mp hg with rfl | htl
    · have h0 : isBinary g = false := by dsimp only [isBinary]; rw [hn]
      have hle : List.countP isBinary tl ≤ tl.length := List.countP_le_length
      simp only [budget, List.countP_cons, h0, Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · have htl' : List.countP isBinary tl < tl.length := ih htl
      simp only [budget, List.countP_cons, List.length_cons]
      cases isBinary a <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] <;>
        omega

def readW {X : Type} (w : X → List Bool) (i : ℕ) : Wire X := fun x => (w x).getD i false
def observe {X : Type} (w : X → List Bool) (g : Gate) : Wire X :=
  fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
def emits {X : Type} (w : X → List Bool) (g : Gate) (x : X) := w x ++ [observe w g x]

theorem decode {X : Type} (w : X → List Bool) (g : Gate) (ok : Ok g) (P : Set (Wire X))
    (cp : Closed P) (hw : ∀ i, readW w i ∈ P) :
    (isBinary g = false ∧ observe w g ∈ P) ∨
    (isBinary g = true ∧ ∃ a ∈ P, ∃ b ∈ P, ∃ op, observe w g = bin op a b) := by
  rcases g with ⟨op, inputs⟩
  obtain ⟨allowed, short⟩ := ok
  rcases allowed with rfl | rfl | rfl
  · refine Or.inr ⟨rfl, ?_⟩
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, tl⟩⟩⟩
    · exact ⟨_, cp.1 true, _, cp.1 true, false, rfl⟩
    · refine ⟨_, hw a, _, cp.1 true, false, ?_⟩
      funext x; simp [bin, readW, observe, bit, GateOp.eval]
    · refine ⟨_, hw a, _, hw b, false, ?_⟩
      funext x; simp [bin, readW, observe, GateOp.eval]
    · change (a :: b :: d :: tl).length ≤ 2 at short; simp at short
  · refine Or.inr ⟨rfl, ?_⟩
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, tl⟩⟩⟩
    · exact ⟨_, cp.1 false, _, cp.1 false, true, rfl⟩
    · refine ⟨_, hw a, _, cp.1 false, true, ?_⟩
      funext x; simp [bin, readW, observe, bit, GateOp.eval]
    · refine ⟨_, hw a, _, hw b, true, ?_⟩
      funext x; simp [bin, readW, observe, GateOp.eval]
    · change (a :: b :: d :: tl).length ≤ 2 at short; simp at short
  · refine Or.inl ⟨rfl, ?_⟩
    cases inputs with
    | nil => exact cp.1 true
    | cons a tl => exact cp.2 _ (hw a)

theorem reads_after {X : Type} (w : X → List Bool) (g : Gate) (m : ℕ)
    (wm : ∀ x, (w x).length = m) (P : Set (Wire X)) (old : ∀ i, readW w i ∈ P)
    (fresh : observe w g ∈ P) : ∀ i, readW (emits w g) i ∈ P := by
  intro i
  by_cases e : i = m
  · have eq : readW (emits w g) i = observe w g := by
      funext x
      change (w x ++ [_]).getD i false = _
      rw [e, ← wm x, getD_snoc_eq]
    exact eq ▸ fresh
  · have eq : readW (emits w g) i = readW w i := by
      funext x
      change (w x ++ [_]).getD i false = _
      exact getD_snoc_ne _ _ _ _ (by rw [wm x]; exact e)
    exact eq ▸ old i

theorem compile {X : Type} (gs : List Gate) (out : ℕ) (ok : ∀ g ∈ gs, Ok g) :
    ∀ (w : X → List Bool) (m : ℕ), (∀ x, (w x).length = m) → ∀ P : Set (Wire X),
      Closed P → (∀ i, readW w i ∈ P) →
      Run P (budget gs) (fun x => (wiresFrom gs (w x)).getD out false) := by
  induction gs with
  | nil => intro w m wm P cp hw; exact Run.done (hw out)
  | cons g gs ih =>
    intro w m wm P cp hw
    have next := ih (fun g' hg => ok g' (List.mem_cons_of_mem _ hg)) (emits w g) (m + 1)
      (fun x => by simp [emits, wm])
    obtain one | two := decode w g (ok g (List.mem_cons_self ..)) P cp hw
    · rcases one with ⟨hn, v⟩
      simp only [budget, List.countP_cons, hn, Bool.false_eq_true, ite_false, Nat.add_zero]
      exact next P cp (reads_after w g m wm P hw v)
    · rcases two with ⟨hn, a, ha, b, hb, op, v⟩
      simp only [budget, List.countP_cons, hn, ite_true]
      apply Run.gate op ha hb
      exact next _ (plus_closed cp _) (reads_after w g m wm _ (fun i => Or.inl (hw i)) (Or.inr (Or.inl v)))

end ThetaSigned

namespace LiveSearch

section LiveOps

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
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
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

end LiveOps

section Projections

def kept {α β : Type} [DecidableEq β] (p : α → Option β) (s : Finset α) : Finset β :=
  s.biUnion (fun a => (p a).toFinset)
def zeros {α β : Type} (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert {α β : Type} [DecidableEq α] [DecidableEq β] (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

theorem zeros_some {α β : Type} {p : α → Option β} {a : α} {v : β} [DecidableEq α] (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]
theorem zeros_none {α β : Type} {p : α → Option β} {a : α} [DecidableEq α] (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]
theorem zeros_le {α β : Type} [DecidableEq α] (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le
theorem zeros_mono {α β : Type} (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)
theorem build_mono {β : Type} [DecidableEq β] {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a, hs ha, b, hs hb, hab, z, hz, ih (Finset.insert_subset_insert _ hs) tail⟩

def projects {α β : Type} (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {α β : Type} [DecidableEq α] {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r) + 1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {α β : Type} [DecidableEq α] {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hn, r, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {α β : Type} [DecidableEq α] [DecidableEq β] {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hn, r, rfl, tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha | hb | ⟨u, w, hA, hB, hw, hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert, hZ, hA, hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert, hA], w, by simp [kept_insert, hB],
              hw, v, hop, build_mono covers next⟩

def History {α : Type} [DecidableEq α] (ops : α → α → Finset α) (start s : Finset α) : Prop :=
  ∀ Q : Finset α → Prop,
    Q start →
    (∀ {t a b z}, Q t → a ∈ t → b ∈ t → z ∈ ops a b → Q (insert z t)) →
    Q s

theorem History.initial {α : Type} [DecidableEq α] {ops : α → α → Finset α} {start : Finset α} :
    History ops start start := fun _ q0 _ => q0

theorem History.gate {α : Type} [DecidableEq α] {ops : α → α → Finset α} {start s : Finset α}
    (old : History ops start s) {a b z : α} (ha : a ∈ s) (hb : b ∈ s) (hz : z ∈ ops a b) :
    History ops start (insert z s) := fun Q q0 qg => qg (old Q q0 qg) ha hb hz

theorem History.contains {α : Type} [DecidableEq α] {ops : α → α → Finset α} {start s : Finset α}
    (h : History ops start s) : start ⊆ s :=
  h (fun t => start ⊆ t) (Finset.Subset.refl _)
    (fun ih _ _ _ => ih.trans (Finset.subset_insert _ _))

theorem kept_mono {α β : Type} [DecidableEq β] (p : α → Option β) {s t : Finset α} (h : s ⊆ t) : kept p s ⊆ kept p t := by
  intro v hv
  obtain ⟨x, hx, px⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨x, h hx, px⟩

theorem kept_of {α β : Type} [DecidableEq β] {p : α → Option β} {s : Finset α} {a : α} {v : β}
    (ha : a ∈ s) (hp : p a = some v) : v ∈ kept p s :=
  Finset.mem_biUnion.mpr ⟨a, ha, by simp [hp]⟩

def price {α β : Type} [DecidableEq β] (p : α → Option β) (start s : Finset α) : ℕ := (kept p s \ kept p start).card

theorem History.compose {α β : Type} [DecidableEq α] [DecidableEq β] {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start s : Finset α} (h : History ops start s)
    {g : β} {k : ℕ} (tail : build ops' g k (kept p s)) :
    build ops' g (k + price p start s) (kept p start) := by
  refine (h (fun t => start ⊆ t ∧ ∀ {k}, build ops' g k (kept p t) → build ops' g (k + price p start t) (kept p start)) ?_ ?_).2 tail
  · exact ⟨Finset.Subset.refl _, fun tail => by simpa [price] using tail⟩
  · intro t a b z ⟨sub, ih⟩ ha hb hz
    constructor
    · exact sub.trans (Finset.subset_insert _ _)
    · intro k' tail'
      cases eq : p z with
      | none => simpa [price, kept_insert, eq] using ih (by simpa [kept_insert, eq] using tail')
      | some v =>
        have avail : kept p (insert z t) = insert v (kept p t) := by simp [kept_insert, eq]
        by_cases dup : v ∈ kept p t
        · rw [Finset.insert_eq_of_mem dup] at avail
          simpa [price, avail] using ih (avail ▸ tail')
        · have nv : v ∉ kept p start := fun hv => dup (kept_mono p sub hv)
          have cost : price p start (insert z t) = price p start t + 1 := by
            simp [price, avail, Finset.insert_sdiff_of_notMem, nv, dup]
          obtain ea | eb | ⟨u, w, eu, ew, ne, mem⟩ := proj a b z hz v eq
          · exact (dup (kept_of ha ea)).elim
          · exact (dup (kept_of hb eb)).elim
          · have t' : build ops' g (k' + 1) (kept p t) :=
              Or.inr ⟨u, kept_of ha eu, w, kept_of hb ew, ne, v, mem, avail ▸ tail'⟩
            simpa [cost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih t'

theorem face_budget {α β : Type} [DecidableEq α] [DecidableEq β] {ops : α → α → Finset α} {ops' : β → β → Finset β} {p : α → Option β}
    (proj : projects p ops ops') {start hist s : Finset α} {g : α} {g' : β} {k : ℕ}
    (past : History ops start hist) (pool : s ⊆ hist) (target : p g = some g')
    (run : live ops g k s) :
    build ops' g' (k - zeros p s + price p start hist) (kept p start) := by
  apply past.compose proj
  apply build_mono (kept_mono p pool)
  exact project_live target proj run _ (by omega)

end Projections

end LiveSearch

namespace Check

abbrev W (H : ℕ) := BitVec (2 * H)
def neg {H : ℕ} (x : W H) : W H := ~~~x
def both {H : ℕ} (x y : W H) : W H := x &&& y
def canon {H : ℕ} (x : W H) : W H := if x.getLsbD 0 then neg x else x
def ops {H : ℕ} (x y : W H) : List (W H) :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
abbrev basicOps (H : ℕ) (a b : W H) : Finset (W H) := (ops a b).toFinset
def sep (H : ℕ) (x : W H) : BitVec H := (x ^^^ (x >>> H)).setWidth H
def cuts (H : ℕ) (ws : List (W H)) : BitVec H := ws.foldr (fun w v => sep H w ||| v) 0
def rawGoal (H : ℕ) : W H := BitVec.allOnes (2 * H) <<< H
def goal (H : ℕ) : W H := canon (rawGoal H)

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
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
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
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def differs (H : ℕ) (i : Fin H) (w : W H) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (H + i.val)

theorem neg_differs {H : ℕ} (i : Fin H) (w : W H) : differs H i (neg w) ↔ differs H i w := by
  have lo : i.val < 2 * H := by omega
  have hi : H + i.val < 2 * H := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs {H : ℕ} (i : Fin H) (w : W H) : differs H i (canon w) ↔ differs H i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs {H : ℕ} (i : Fin H) (a b z : W H) (hz : z ∈ basicOps H a b)
    (hd : differs H i z) : differs H i a ∨ differs H i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (H + i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (H + i.val) := by simpa [differs] using h.2
  have lo : i.val < 2 * H := by omega
  have hi : H + i.val < 2 * H := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;>
    simp_all

theorem goal_differs {H : ℕ} (i : Fin H) : differs H i (goal H) := by
  rw [goal, canon_differs]
  unfold differs rawGoal
  have lo : i.val < H := i.isLt
  have hi : H + i.val < 2 * H := by omega
  simp [BitVec.getLsbD_shiftLeft, lo, hi]

theorem canon_canon {H : ℕ} (x : W H) : canon (canon x) = canon x := by
  unfold canon
  split
  · rename_i h
    by_cases h0 : 0 < 2 * H
    · simp [neg, h, h0]
    · have hz : 2 * H = 0 := by omega
      have hx : x.getLsbD 0 = false := by simp [hz]
      exact absurd h (by simp [hx])
  · rename_i h
    rfl

theorem canon_goal (H : ℕ) : canon (goal H) = goal H := canon_canon (rawGoal H)

theorem canon_zero (H : ℕ) : canon (0 : W H) = 0 := by simp [canon]

theorem goal_ne_zero {H : ℕ} (hH : 0 < H) : goal H ≠ 0 := by
  intro h
  have hd := goal_differs ⟨0, hH⟩
  rw [h] at hd
  simp [differs] at hd

theorem cuts_spec {H : ℕ} (ws : List (W H)) (i : Fin H) :
    (cuts H ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs H i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep H a ||| cuts H rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {H k : ℕ} {ws : List (W H)} (h : LiveSearch.live (basicOps H) (goal H) k ws.toFinset) :
    cuts H ws = BitVec.allOnes H := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := LiveSearch.live_separates (differs H ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap {H : ℕ} (a b : W H) : basicOps H a b = basicOps H b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

def keepChoices {H : ℕ} (a b : W H) (r : List (W H)) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {H : ℕ} {ws r : List (W H)} {a b : W H} {needed : Finset (W H)}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
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

theorem singleton_list {H : ℕ} {ws : List (W H)} (hn : ws.Nodup) (hs : ws.toFinset = {goal H}) :
    ws = [goal H] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem canon_neg {H : ℕ} (x : W H) : canon (~~~x) = canon x := by
  unfold canon neg
  by_cases h0 : 0 < 2 * H
  · cases hx : x.getLsbD 0
    · simp only [BitVec.getLsbD_not, h0, decide_true, Bool.true_and, BitVec.not_not, hx, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    · simp only [BitVec.getLsbD_not, h0, decide_true, Bool.true_and, BitVec.not_not, hx, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  · have hz : 2 * H = 0 := by omega
    have hnot : ~~~x = x := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      omega
    simp [hnot]

theorem sign {H : ℕ} (x : W H) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {H : ℕ} {x y a b : W H} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps H a b := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [basicOps, ops, both]

theorem same_both {H : ℕ} {x y : W H} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h | h <;> rcases sign y with j | j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W H => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl | rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self, canon_zero])

def represents {H : ℕ} (available : Finset (W H)) (w : List (W H)) : Prop :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

def possibleIn {H : ℕ} (w : List (W H)) (z : W H) : Bool :=
  z == 0 || z == BitVec.allOnes (2 * H) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

theorem not_zero_eq_allOnes (n : ℕ) : ~~~(0 : BitVec n) = BitVec.allOnes n := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp

theorem not_allOnes_eq_zero (n : ℕ) : ~~~(BitVec.allOnes n) = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp

theorem classify {H : ℕ} {available : Finset (W H)} {ws : List (W H)} (hw : represents available ws)
    {z : W H} (hz : possibleIn ws z = true) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps H a b := by
  simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, (h | h) | ⟨y, hy, hh⟩⟩)
  · subst z; left; exact canon_zero H
  · subst z; left; rw [← not_zero_eq_allOnes, canon_neg, canon_zero]
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W H) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps H a b := by
      have zeroOrFull (t : W H) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes (2 * H) := by
        rcases sign t with h' | h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr (h'.trans (not_zero_eq_allOnes (2 * H)))
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl | rfl
        · left; rw [show (0 : W H) &&& v = 0 from BitVec.zero_and, canon_zero]
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl | rfl
        · left; rw [show u &&& (0 : W H) = 0 from BitVec.and_zero, canon_zero]
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht | ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_, hu, _, hv, h, signed_both (sign u) (sign v)⟩)
    rcases hh with rfl | rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

def rawOps {H : ℕ} (a b : W H) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (H : ℕ) (x : W H) : sep H (canon x) = sep H x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W H) : (sep H v)[i] = true ↔ differs H ⟨i, hi⟩ v := by
    change (sep H v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i, hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (H extra : ℕ) (next : ℕ → List (W H) → Bool) (a b : W H) (r : List (W H)) : Bool :=
  let base := cuts H r
  let full := BitVec.allOnes H
  (rawOps a b).any fun w =>
    let v := sep H w ||| base
    ((v == full) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep H a == full) && next (extra - 1) (canon w :: a :: r)) ||
                       ((v ||| sep H b == full) && next (extra - 1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep H a ||| sep H b == full) && next (extra - 2) (canon w :: a :: b :: r))

def optimized (H : ℕ) : ℕ → ℕ → List (W H) → Bool
  | 0, _, ws => ws == [goal H]
  | k + 1, extra, ws => ws == [goal H] ||
    (pairs ws).any (fun (a, b, r) => dispatch H extra (optimized H k) a b r)

theorem dispatch_complete {H k extra : ℕ} {a b z : W H} {r kept : List (W H)}
    (next : ℕ → List (W H) → Bool)
    (hz : z ∈ basicOps H a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts H (z :: kept) = BitVec.allOnes H) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch H extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w, hw, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · simp only [cuts, List.foldr_cons, sep_canon] at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    left; left; refine ⟨hc, ?_⟩
    convert ht using 2; omega
  · simp only [cuts, List.foldr_cons, sep_canon] at hc
    simp only [List.length_cons] at he hn
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    left; right; refine ⟨by omega, .inl ⟨?_, ?_⟩⟩
    · simp only [cuts] at hc ⊢; convert hc using 1; ac_rfl
    · convert ht using 2; simp; omega
  · simp only [cuts, List.foldr_cons, sep_canon] at hc
    simp only [List.length_cons] at he hn
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
    left; right; refine ⟨by omega, .inr ⟨?_, ?_⟩⟩
    · simp only [cuts] at hc ⊢; convert hc using 1; ac_rfl
    · convert ht using 2; simp; omega
  · simp only [cuts, List.foldr_cons, sep_canon] at hc
    simp only [List.length_cons] at he hn
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    right; refine ⟨⟨by omega, ?_⟩, ?_⟩
    · simp only [cuts] at hc ⊢; convert hc using 1; ac_rfl
    · convert ht using 2; simp; omega

theorem optimized_complete (H n : ℕ) (ws : List (W H)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : LiveSearch.live (basicOps H) (goal H) n ws.toFinset) :
    optimized H n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases LiveSearch.first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W H} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps H a b) :
          dispatch H extra (optimized H k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : LiveSearch.live (basicOps H) (goal H) k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := LiveSearch.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized H k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check

namespace SignedCofactor

open ThetaSigned

def literals (n : Nat) : Set (Wire (Fin n → Bool)) :=
  {f | (∃ c, f = bit c) ∨ ∃ i : Fin n, f = (fun x => x i) ∨ f = inv (fun x => x i)}

theorem literals_closed (n : Nat) : Closed (literals n) := by
  constructor
  · exact fun b => Or.inl ⟨b, rfl⟩
  · intro f hf
    rcases hf with ⟨b, rfl⟩ | ⟨i, rfl | rfl⟩
    · exact Or.inl ⟨!b, rfl⟩
    · exact Or.inr ⟨i, Or.inr rfl⟩
    · exact Or.inr ⟨i, Or.inl (inv_inv _)⟩

def extFin {n : ℕ} (b : Bool) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else b

def allInputs : (n : ℕ) → List (Fin n → Bool)
  | 0 => [fun _ => false]
  | n + 1 => (allInputs n).flatMap fun x => [extFin false x, extFin true x]

theorem mem_allInputs {n : ℕ} (x : Fin n → Bool) : x ∈ allInputs n := by
  induction n with
  | zero =>
    have eq : x = fun _ => false := by
      funext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    simp [allInputs, eq]
  | succ n ih =>
    let x' : Fin n → Bool := fun i => x ⟨i.val, by omega⟩
    have hx' : x' ∈ allInputs n := ih x'
    have eq : extFin (x ⟨n, Nat.lt_succ_self n⟩) x' = x := by
      funext i
      by_cases hi : i.val < n
      · simp [extFin, hi, x']
      · have hval : i.val = n := by omega
        have hfin : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval
        simp [extFin, hfin]
    rw [allInputs, List.mem_flatMap]
    refine ⟨x', hx', ?_⟩
    cases hb : x ⟨n, Nat.lt_succ_self n⟩ <;> rw [hb] at eq <;> simp [← eq]

def isConst {n : ℕ} (w : Wire (Fin n → Bool)) (b : Bool) : Bool :=
  (allInputs n).all (fun x => w x == b)

def isVar {n : ℕ} (w : Wire (Fin n → Bool)) (i : Fin n) (b : Bool) : Bool :=
  (allInputs n).all (fun x => w x == (x i != b))

def isLiteral (n : ℕ) (w : Wire (Fin n → Bool)) : Bool :=
  isConst w false || isConst w true ||
  (List.finRange n).any (fun i => isVar w i false || isVar w i true)

theorem isLiteral_spec {n : ℕ} {w : Wire (Fin n → Bool)} (hw : isLiteral n w = true) :
    w ∈ literals n := by
  simp only [isLiteral, isConst, isVar, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, beq_iff_eq] at hw
  rcases hw with (h | h) | ⟨i, _, h | h⟩
  · exact Or.inl ⟨false, funext fun x => h x (mem_allInputs x)⟩
  · exact Or.inl ⟨true, funext fun x => h x (mem_allInputs x)⟩
  · exact Or.inr ⟨i, Or.inl (funext fun x => by simpa using h x (mem_allInputs x))⟩
  · exact Or.inr ⟨i, Or.inr (funext fun x => by simpa [inv] using h x (mem_allInputs x))⟩

end SignedCofactor

namespace Generic

open Check LiveSearch ThetaSigned

def wordBit {H : ℕ} (r : Fin (2 * H)) (w : W H) : Bool := w[r.val]

def representsPool {H : ℕ} {T : Type} (pick : Fin (2 * H) → T) (P : Set (Wire T)) (S : Finset (W H)) : Prop :=
  ∀ f ∈ P, ∃ w, (canon w = 0 ∨ canon w ∈ S) ∧ ∀ r, f (pick r) = wordBit r w

theorem singletonPossible {H : ℕ} {ws : List (W H)} {x : W H} (hx : x = 0 ∨ x ∈ ws) :
    possibleIn ws x ∧ possibleIn ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possibleIn]
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

theorem pairPossible {H : ℕ} {ws : List (W H)} {x y : W H}
    (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possibleIn ws (x &&& y) ∧ possibleIn ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws y from ⟨by simp [possibleIn], (singletonPossible hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possibleIn] using (show possibleIn ws 0 ∧ possibleIn ws x from ⟨by simp [possibleIn], (singletonPossible (.inr hx)).1⟩)
  · simp only [possibleIn, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem anyBuild {H : ℕ} (hH : 0 < H) {T : Type} (pick : Fin (2 * H) → T) {target : Wire T}
    (agrees : ∀ r, target (pick r) = wordBit r (goal H)) {P : Set (Wire T)} {k : ℕ} (h : Run P k target) :
    ∀ av, representsPool pick P av → build (basicOps H) (goal H) k av := by
  refine (h (fun P k f => (∀ r, f (pick r) = wordBit r (goal H)) →
      ∀ av, representsPool pick P av → build (basicOps H) (goal H) k av) ?_ ?_) agrees
  · intro P k f hf agrees' av rep
    obtain ⟨u, hu, huv⟩ := rep _ hf
    have eq : u = goal H := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact (huv ⟨i, hi⟩).symm.trans (agrees' ⟨i, hi⟩)
    rw [eq, canon_goal H] at hu
    have ing : goal H ∈ av := hu.resolve_left (goal_ne_zero hH)
    induction k with
    | zero => exact ing
    | succ k ih => exact Or.inl ih
  · intro P k f a b op ha hb ih agrees' av rep
    obtain ⟨u, ru, eu⟩ := rep _ ha
    obtain ⟨v, rv, ev⟩ := rep _ hb
    let z := if op then u ||| v else u &&& v
    have hbits (r) : ThetaSigned.bin op a b (pick r) = wordBit r z := by
      cases op <;> simp [z, ThetaSigned.bin, eu, ev, wordBit]
    have add {av' : Finset (W H)} (sub : av ⊆ av') (has : canon z = 0 ∨ canon z ∈ av') :
        representsPool pick (plus P (ThetaSigned.bin op a b)) av' := by
      rintro g (old | rfl | rfl)
      · obtain ⟨w, hw, e⟩ := rep g old
        exact ⟨w, hw.imp_right (fun h => sub h), e⟩
      · exact ⟨_, has, hbits⟩
      · refine ⟨~~~z, by simpa only [canon_neg] using has, ?_⟩
        intro r
        simp [ThetaSigned.inv, hbits, wordBit]
    have hws : represents av [u, v] := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> assumption
    have hz : possibleIn [u, v] z := by
      have hh := pairPossible (ws := [u, v]) (Or.inr (List.mem_cons_self ..) : u = 0 ∨ u ∈ [u, v])
        (Or.inr (by simp) : v = 0 ∨ v ∈ [u, v])
      cases op <;> first | exact hh.1 | exact hh.2
    rcases classify hws hz with hz | hz | ⟨a', ha', b', hb', ne, mem⟩
    · exact Or.inl (ih agrees' av (add (fun _ h => h) (Or.inl hz)))
    · exact Or.inl (ih agrees' av (add (fun _ h => h) (Or.inr hz)))
    · exact Or.inr ⟨a', ha', b', hb', ne, _, mem, ih agrees' _ (add (Finset.subset_insert ..) (Or.inr (Finset.mem_insert_self ..)))⟩

def columnPick {H n : ℕ} (cols : List (W H)) (r : Fin (2 * H)) (i : Fin n) : Bool :=
  wordBit r (cols.getD i.val 0)

def signals (H : ℕ) (cols : List (W H)) : List (W H) := cols.map canon

theorem columnGood {H n : ℕ} (cols : List (W H)) (len : cols.length = n) :
    representsPool (columnPick (n := n) cols) (SignedCofactor.literals n) (signals H cols).toFinset := by
  have present (i : Fin n) : canon (cols.getD i.val 0) ∈ (signals H cols).toFinset := by
    have h : i.val < cols.length := len ▸ i.isLt
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨_, by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem .., rfl⟩
  rintro f (⟨b, rfl⟩ | ⟨i, rfl | rfl⟩)
  · cases b
    · exact ⟨0, Or.inl (canon_zero H), by simp [ThetaSigned.bit, wordBit]⟩
    · exact ⟨BitVec.allOnes (2 * H), Or.inl (by rw [← not_zero_eq_allOnes, canon_neg, canon_zero]),
        by intro r; exact (BitVec.getElem_allOnes r.val r.isLt).symm⟩
  · exact ⟨_, Or.inr (present i), fun r => rfl⟩
  · refine ⟨~~~(cols.getD i.val 0), Or.inr ?_, ?_⟩
    · rw [canon_neg]; exact present i
    · intro r; simp [inv, columnPick, wordBit]

def critical (H : ℕ) (ws : List (W H)) (sites : List (Fin H)) : Bool :=
  ws.all fun a => sites.any fun i => ws.all fun b => (b.getLsbD i.val == b.getLsbD (H + i.val)) || b == a

theorem all_required {H : ℕ} {ws : List (W H)} {sites : List (Fin H)} {k : ℕ} {s : Finset (W H)}
    (crit : critical H ws sites = true)
    (hs : s ⊆ ws.toFinset) (hr : live (basicOps H) (goal H) k s) : s = ws.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  obtain ⟨i, _, all⟩ := List.any_eq_true.mp (List.all_eq_true.mp crit a (List.mem_toFinset.mp ha))
  obtain ⟨b, hb, hd⟩ := live_separates (differs H i) (goal_differs i) (ops_differs i) hr
  have eq := List.all_eq_true.mp all _ (List.mem_toFinset.mp (hs hb))
  simp only [Bool.or_eq_true, beq_iff_eq] at eq
  exact eq.resolve_left hd ▸ hb

end Generic

namespace MinorSearch

open Check LiveSearch Generic ThetaSigned SignedCofactor

abbrev Minor (H : ℕ) := ℕ × W H × Fin (2 * H)

def crop {H : ℕ} (m : W H) (r : Fin (2 * H)) (x : W H) : W H :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def pos (H : ℕ) (m : W H) (r : Fin (2 * H)) (i : ℕ) : ℕ :=
  if m.getLsbD i then i else r.val

theorem pos_lt {H : ℕ} (m : W H) (r : Fin (2 * H)) {i : ℕ} (hi : i < 2 * H) :
    pos H m r i < 2 * H := by
  unfold pos; split <;> omega

theorem crop_bit {H : ℕ} (m : W H) (r : Fin (2 * H)) (x : W H) (i : ℕ) (hi : i < 2 * H) :
    (crop m r x).getLsbD i = x.getLsbD (pos H m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_eq_getElem hi (x := m)]
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm, hi]

theorem crop_and {H : ℕ} (m : W H) (r : Fin (2 * H)) (x y : W H) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg {H : ℕ} (m : W H) (r : Fin (2 * H)) (x : W H) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap {H : ℕ} (x : W H) : Option (W H) := if canon x = 0 then none else some (canon x)

theorem wrap_neg {H : ℕ} (x : W H) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt {H : ℕ} (m : W H) (r : Fin (2 * H)) (x : W H) : Option (W H) := wrap (crop m r x)

theorem crop_canon {H : ℕ} (m : W H) (r : Fin (2 * H)) (x : W H) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

theorem binary_project {H : ℕ} {x y v : W H} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps H u w := by
  have trivial (t : W H) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes (2 * H) := by
    rcases sign t with h' | h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr (h'.trans (not_zero_eq_allOnes (2 * H)))
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl | rfl
    · rw [show (0 : W H) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap (0 : W H) = none := by rw [wrap, canon_zero]; rfl
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl | rfl
    · rw [show x &&& (0 : W H) = 0 from BitVec.and_zero] at h
      have h0 : wrap (0 : W H) = none := by rw [wrap, canon_zero]; rfl
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by
    unfold wrap at h
    split at h
    · contradiction
    · exact Option.some.inj h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same | bad
    · exact .inl (by unfold wrap; split <;> simp_all)
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x, canon y, by unfold wrap; split <;> simp_all,
      by unfold wrap; split <;> simp_all, eq,
      hval ▸ signed_both (sign x) (sign y)⟩)

theorem mask_projects (H : ℕ) (m : W H) (r : Fin (2 * H)) :
    projects (cropOpt m r) (basicOps H) (basicOps H) := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

def interpret {H : ℕ} {T : Type} (pick : T → Fin (2 * H)) (w : W H) : Wire T :=
  fun x => w.getLsbD (pick x).val

theorem interpret_neg {H : ℕ} {T : Type} (pick : T → Fin (2 * H)) (w : W H) :
    interpret pick (neg w) = inv (interpret pick w) := by
  funext x
  simp [neg, interpret, inv, (pick x).isLt]

theorem interpret_canon {H : ℕ} {T : Type} (pick : T → Fin (2 * H)) (w : W H) :
    interpret pick (canon w) = interpret pick w ∨ interpret pick (canon w) = inv (interpret pick w) := by
  unfold canon; split
  · exact Or.inr (interpret_neg _ _)
  · exact Or.inl rfl

theorem interpret_both {H : ℕ} {T : Type} (pick : T → Fin (2 * H)) (a b : W H) :
    interpret pick (both a b) = bin false (interpret pick a) (interpret pick b) := by
  funext x; simp [interpret, both, bin]

theorem decode_build {H : ℕ} {T : Type} (pick : T → Fin (2 * H)) {g : W H} {k : ℕ} {s : Finset (W H)}
    (h : build (basicOps H) g k s) {P : Set (Wire T)} (hp : Closed P)
    (raw : ∀ a ∈ s, interpret pick a ∈ P) : Run P k (interpret pick g) := by
  induction k generalizing s P with
  | zero => exact .done (raw _ h)
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, _, z, hz, ht⟩
    · exact Run_pad (ih skip hp raw)
    · have put {s₁ s₂ : W H} (ha' : interpret pick s₁ ∈ P) (hb' : interpret pick s₂ ∈ P)
          (ed : z = canon (both s₁ s₂)) : Run P (k + 1) (interpret pick g) := by
        apply Run.gate false ha' hb'
        apply ih ht (plus_closed hp _)
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · rcases interpret_canon pick (both s₁ s₂) with same | opp
          · exact Or.inr (Or.inl (ed ▸ same.trans (interpret_both _ _ _)))
          · exact Or.inr (Or.inr (ed ▸ opp.trans (congrArg inv (interpret_both _ _ _))))
        · exact Or.inl (raw _ hv)
      have an : interpret pick (neg a) ∈ P := interpret_neg pick a ▸ hp.2 _ (raw _ ha)
      have bn : interpret pick (neg b) ∈ P := interpret_neg pick b ▸ hp.2 _ (raw _ hb)
      simp [basicOps, ops] at hz
      rcases hz with hz | hz | hz | hz
      · exact put (raw _ ha) (raw _ hb) hz
      · exact put (raw _ ha) bn hz
      · exact put an (raw _ hb) hz
      · exact put an bn hz

def MinorValid (H : ℕ) (c : Minor H) (base : List (W H)) : Prop :=
  ∃ g, cropOpt c.2.1 c.2.2 (goal H) = some g ∧
    ∀ k, build (basicOps H) g k (kept (cropOpt c.2.1 c.2.2) base.toFinset) → c.1 ≤ k

theorem transfer (H : ℕ) {T : Type} (base : List (W H)) (c : Minor H) (pick : T → Fin (2 * H))
    (inside : ∀ t, c.2.1.getLsbD (pick t).val = true) (P : Set (Wire T)) (closed : Closed P)
    (raw : ∀ w ∈ base, interpret pick w ∈ P) (F : Wire T)
    (target : interpret pick (goal H) = F) (someGoal : ∃ g, cropOpt c.2.1 c.2.2 (goal H) = some g)
    (lower : ∀ k, Run P k F → c.1 ≤ k) : MinorValid H c base := by
  obtain ⟨g, hg⟩ := someGoal
  refine ⟨g, hg, ?_⟩
  intro k proof
  have same (w : W H) : interpret pick (crop c.2.1 c.2.2 w) = interpret pick w := by
    funext y
    simp only [interpret, crop_bit _ _ _ _ (pick y).isLt, pos, inside, ite_true]
  have image (u v : W H) (ev : cropOpt c.2.1 c.2.2 u = some v) :
      interpret pick v = interpret pick u ∨ interpret pick v = inv (interpret pick u) := by
    unfold cropOpt wrap at ev
    split at ev
    · contradiction
    obtain rfl := Option.some.inj ev
    simpa only [same] using interpret_canon pick (crop c.2.1 c.2.2 u)
  have haveRaw (w : W H) (hw : w ∈ kept (cropOpt c.2.1 c.2.2) base.toFinset) : interpret pick w ∈ P := by
    obtain ⟨u, hu, m⟩ := Finset.mem_biUnion.mp hw
    have pr : cropOpt c.2.1 c.2.2 u = some w := by simpa using m
    rcases image u w pr with e | e
    · rw [e]; exact raw _ (List.mem_toFinset.mp hu)
    · rw [e]; exact closed.2 _ (raw _ (List.mem_toFinset.mp hu))
  have yes := decode_build pick proof closed haveRaw
  apply lower k
  rcases image (goal H) g hg with e | e
  · rwa [e, target] at yes
  · rw [e, target] at yes
    simpa only [inv_inv] using Run_inv yes closed

def seen {H : ℕ} (base h : List (W H)) : Finset (W H) := h.toFinset ∪ base.toFinset

def rejects (H : ℕ) (base : List (W H)) (c : Minor H) (k : ℕ) (ws hist : List (W H)) : Bool :=
  let p := cropOpt c.2.1 c.2.2
  decide (k - zeros p ws.toFinset + price p base.toFinset (seen base hist) < c.1)

theorem safe {H : ℕ} {base : List (W H)} {c : Minor H} {k : ℕ} {ws hist : List (W H)}
    (valid : MinorValid H c base)
    (past : History (basicOps H) base.toFinset (seen base hist)) (pool : ws.toFinset ⊆ seen base hist)
    (run : live (basicOps H) (goal H) k ws.toFinset) : rejects H base c k ws hist = false := by
  obtain ⟨g, hg, lower⟩ := valid
  exact decide_eq_false (Nat.not_lt.mpr (lower _ (face_budget (mask_projects H _ _) past pool hg run)))

def gone {H : ℕ} (p : W H → Option (W H)) (ws : List (W H)) : ℕ :=
  (ws.filter fun w => (p w).isNone).length

def paid {H : ℕ} (p : W H → Option (W H)) (ws base : List (W H)) : ℕ :=
  ((ws.filterMap p).filter (fun z => !base.contains z)).dedup.length

theorem gone_eq {H : ℕ} (p : W H → Option (W H)) {ws : List (W H)} (hn : ws.Nodup) :
    gone p ws = zeros p ws.toFinset := by
  unfold gone zeros
  rw [← List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist ..))]
  congr 1
  ext a
  simp [Option.isNone_iff_eq_none]

def limited {H : ℕ} (m : W H) (r : Fin (2 * H)) (w : W H) : W H :=
  (if w[r.val] then ~~~w else w) &&& m

theorem limited_anchor {H : ℕ} (m : W H) (r : Fin (2 * H)) (w : W H) :
    (limited m r w)[r.val] = false := by
  cases e : w[r.val] <;> simp [limited, e]

theorem limited_crop {H : ℕ} (m : W H) (r : Fin (2 * H)) (w : W H) :
    canon (crop m r w) = canon (limited m r w) := by
  cases e : w[r.val] with
  | false => simp [crop, limited, e]
  | true =>
    have eq : crop m r w = ~~~(limited m r w) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simp only [crop, limited, e, ite_true, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
      cases w[i] <;> cases m[i] <;> rfl
    rw [eq, canon_neg]

theorem limited_zero {H : ℕ} (m : W H) (r : Fin (2 * H)) (w : W H) :
    canon (limited m r w) = 0 ↔ limited m r w = 0 := by
  constructor
  · intro h
    rcases sign (limited m r w) with a | a
    · exact a.trans h
    · rw [h] at a
      have e := congrArg (fun z : W H => z[r.val]) a
      rw [limited_anchor] at e
      have h1 : (neg (0 : W H))[r.val] = true := by
        rw [neg, not_zero_eq_allOnes]
        exact BitVec.getElem_allOnes _ _
      exact False.elim (Bool.noConfusion (e.trans h1))
  · intro h; rw [h, canon_zero]

def projectFast {H : ℕ} (m : W H) (r : Fin (2 * H)) (w : W H) : Option (W H) :=
  let q := limited m r w
  if q = 0 then none else some (canon q)

theorem projectFast_eq {H : ℕ} (m : W H) (r : Fin (2 * H)) : projectFast m r = cropOpt m r := by
  funext w
  simp only [projectFast, cropOpt, wrap, limited_crop, limited_zero]

theorem kept_list {H : ℕ} (p : W H → Option (W H)) (ws : List (W H)) :
    kept p ws.toFinset = (ws.filterMap p).toFinset := by
  ext a; simp [kept, List.mem_filterMap]

theorem price_eq {H : ℕ} (base : List (W H)) (p : W H → Option (W H)) (hist : List (W H)) :
    paid p hist (base.filterMap p) = price p base.toFinset (seen base hist) := by
  let h := (hist.filterMap p).filter fun z => !(base.filterMap p).contains z
  change h.dedup.length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_dedup _), List.toFinset_dedup]
  unfold price seen
  rw [show kept p (hist.toFinset ∪ base.toFinset) = kept p hist.toFinset ∪ kept p base.toFinset by
    ext a; simp [kept, or_and_right, exists_or]]
  rw [kept_list, kept_list]
  congr 1
  ext a
  simp [h]

def cheap (H : ℕ) (base : List (W H)) (c : Minor H) (k : ℕ) (ws hist : List (W H)) : Bool :=
  let p := projectFast c.2.1 c.2.2
  let rem := k - (ws.filter (fun w => limited c.2.1 c.2.2 w == 0)).length
  if c.1 ≤ rem then false else
    decide (rem + paid p hist (base.filterMap p) < c.1)

theorem cheap_eq (H : ℕ) (base : List (W H)) (c : Minor H) (k : ℕ) (ws hist : List (W H)) (hn : ws.Nodup) :
    cheap H base c k ws hist = rejects H base c k ws hist := by
  have columns (w : W H) : (projectFast c.2.1 c.2.2 w).isNone = (limited c.2.1 c.2.2 w == 0) := by
    let z := limited c.2.1 c.2.2 w
    change (if z = 0 then none else some (canon z)).isNone = (z == 0)
    split
    · next hz => simp [hz]
    · next hz => exact (beq_eq_false_iff_ne.mpr hz).symm
  change _ = decide (_ < _)
  rw [← projectFast_eq, ← gone_eq _ hn, ← price_eq]
  unfold cheap gone
  simp only [columns]
  split
  · symm; apply decide_eq_false; omega
  · rfl

def index {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (List.finRange n).foldl (fun a i => a + if x i then 2 ^ i.val else 0) 0

def truth (n t : ℕ) (x : Fin n → Bool) : Bool := t.testBit (index x)

def select {H n : ℕ} (hH : 0 < H) (rows : List (Fin (2 * H))) (x : Fin n → Bool) : Fin (2 * H) :=
  rows.getD (index x) ⟨0, by omega⟩

theorem validates {H n t : ℕ} (hH : 0 < H) (base : List (W H)) (c : Minor H) (rows : List (Fin (2 * H)))
    (inside : (allInputs n).all (fun x => c.2.1.getLsbD (select hH rows x).val) = true)
    (raw : base.all (fun w => isLiteral n (interpret (select hH rows) w)) = true)
    (target : (allInputs n).all (fun x => interpret (select hH rows) (goal H) x == truth n t x) = true)
    (someGoal : ∃ g, cropOpt c.2.1 c.2.2 (goal H) = some g)
    (lower : ∀ k, Run (literals n) k (truth n t) → c.1 ≤ k) : MinorValid H c base := by
  apply transfer H base c (select hH rows)
    (fun x => List.all_eq_true.mp inside x (mem_allInputs x))
    _ (literals_closed n) _ (truth n t)
    (funext fun x => beq_iff_eq.mp (List.all_eq_true.mp target x (mem_allInputs x)))
    someGoal lower
  intro w hw
  exact isLiteral_spec (List.all_eq_true.mp raw w hw)

theorem table_live {H n k t : ℕ} (hH : 0 < H) (cols : List (W H)) (sites : List (Fin H))
    (len : cols.length = n) (agrees : ∀ r : Fin (2 * H), truth n t (columnPick cols r) = wordBit r (goal H))
    (crit : critical H (signals H cols) sites = true) (run : Run (literals n) k (truth n t)) :
    live (basicOps H) (goal H) k (signals H cols).toFinset := by
  obtain ⟨s, hs, hr⟩ := compress (anyBuild hH _ agrees run _ (columnGood cols len))
  exact all_required crit hs hr ▸ hr

theorem table_lower {H n t cap extra k : ℕ} (hH : 0 < H) (cols : List (W H)) (sites : List (Fin H))
    (len : cols.length = n)
    (agrees : (List.finRange (2 * H)).all (fun r => truth n t (columnPick cols r) == wordBit r (goal H)) = true)
    (crit : critical H (signals H cols) sites = true) (nodup : (signals H cols).Nodup)
    (room : extra + (signals H cols).length = cap + 1)
    (scan : optimized H cap extra (signals H cols) = false)
    (run : Run (literals n) k (truth n t)) : cap + 1 ≤ k := by
  by_contra! tooSmall
  have hag : ∀ r : Fin (2 * H), truth n t (columnPick cols r) = wordBit r (goal H) :=
    fun r => beq_iff_eq.mp (List.all_eq_true.mp agrees r (List.mem_finRange r))
  have hl := table_live hH cols sites len hag crit run
  have pad (k' : ℕ) (h : k ≤ k') : live (basicOps H) (goal H) k' (signals H cols).toFinset := by
    induction h with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have yes := optimized_complete H cap (signals H cols) extra nodup room (pad _ (by omega))
  exact Bool.noConfusion (yes.symm.trans scan)

def checkChild (H : ℕ) (base : List (W H)) (ad : List (W H) → List (W H) → List (Minor H))
    (further : ℕ → List (W H) → List (W H) → Bool) (k : ℕ)
    (ws hist : List (W H)) (extra : ℕ) (child : List (W H)) : Bool :=
  match child with
  | [] => false
  | z :: _ => !(ws.contains z) && !((ad ws hist).any (fun c => cheap H base c k child (z :: hist))) &&
      further extra child (z :: hist)

def guided (H : ℕ) (base : List (W H)) (ad : List (W H) → List (W H) → List (Minor H)) :
    ℕ → ℕ → List (W H) → List (W H) → Bool
  | 0, _, ws, _ => ws == [goal H]
  | k + 1, extra, ws, hist => ws == [goal H] ||
    let more := checkChild H base ad (guided H base ad k) k ws hist
    (pairs ws).any (fun (a, b, r) => dispatch H extra more a b r)

theorem guided_complete (H : ℕ) (base : List (W H)) (ad : List (W H) → List (W H) → List (Minor H))
    (valid : ∀ ws hist, ∀ c ∈ ad ws hist, MinorValid H c base)
    (n : ℕ) (ws hist : List (W H)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (past : History (basicOps H) base.toFinset (seen base hist))
    (pool : ws.toFinset ⊆ seen base hist) (h : live (basicOps H) (goal H) n ws.toFinset) :
    guided H base ad n extra ws hist = true := by
  induction n generalizing ws hist extra with
  | zero => simp [guided, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [guided, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have extendSeen : seen base (z :: hist) = insert z (seen base hist) := by simp [seen]
      have extended : History (basicOps H) base.toFinset (seen base (z :: hist)) :=
        extendSeen ▸ History.gate past (pool ha) (pool hb) hz
      have go {a b : W H} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps H a b) :
          dispatch H extra (checkChild H base ad (guided H base ad k) k ws hist) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live (basicOps H) (goal H) k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) _ hop hk (by omega) (by omega) (cuts_full hl)
        have pool' : (z :: kept).toFinset ⊆ seen base (z :: hist) := by
          rw [extendSeen, List.toFinset_cons]
          exact Finset.insert_subset_insert _ (Finset.Subset.trans (by
            rw [hfin, hset]
            exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)) pool)
        have succ := ih _ _ (k - kept.length) hnd (by simp; omega) extended pool' hl
        have none : (ad ws hist).any (fun c => cheap H base c k (z :: kept) (z :: hist)) = false :=
          List.any_eq_false.mpr fun c hc => by
            rw [cheap_eq H base c k (z :: kept) (z :: hist) hnd, safe (valid _ _ c hc) extended pool' hl]; decide
        have fresh : z ∉ ws := by simpa using hout
        simp [checkChild, fresh, none, succ]
      simp only [guided, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem table_guided {H n t cap extra k : ℕ} (hH : 0 < H) (cols : List (W H))
    (sites : List (Fin H)) (faces : List (Minor H))
    (hfaces : ∀ c ∈ faces, MinorValid H c (signals H cols))
    (len : cols.length = n)
    (agrees : (List.finRange (2 * H)).all (fun r => truth n t (columnPick cols r) == wordBit r (goal H)) = true)
    (crit : critical H (signals H cols) sites = true) (nodup : (signals H cols).Nodup)
    (room : extra + (signals H cols).length = cap + 1)
    (scan : guided H (signals H cols) (fun _ _ => faces) cap extra (signals H cols) [] = false)
    (run : Run (literals n) k (truth n t)) : cap + 1 ≤ k := by
  by_contra! tooSmall
  have hag : ∀ r : Fin (2 * H), truth n t (columnPick cols r) = wordBit r (goal H) :=
    fun r => beq_iff_eq.mp (List.all_eq_true.mp agrees r (List.mem_finRange r))
  have hl := table_live hH cols sites len hag crit run
  have pad (k' : ℕ) (h : k ≤ k') : live (basicOps H) (goal H) k' (signals H cols).toFinset := by
    induction h with
    | refl => exact hl
    | step _ ih => exact Or.inl ih
  have hseen : seen (signals H cols) [] = (signals H cols).toFinset := by simp [seen]
  have yes := guided_complete H (signals H cols) (fun _ _ => faces) (fun _ _ c hc => hfaces c hc)
    cap (signals H cols) [] extra nodup room (hseen ▸ History.initial) (by simp [seen]) (pad _ (by omega))
  exact Bool.noConfusion (yes.symm.trans scan)

end MinorSearch

namespace MAJ3

open Check Generic ThetaSigned SignedCofactor MinorSearch

def cols : List (W 16) := [(wordsBV 32 [0xddb72406]), (wordsBV 32 [0xbeeb4809]), (wordsBV 32 [0x7f7c9050])]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 16 3 1 (signals 16 cols) = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ k, Run (literals 3) k (truth 3 0xe8) → 4 ≤ k :=
  fun k run => table_lower (H := 16) (n := 3) (t := 0xe8) (cap := 3) (extra := 1)
    (by decide) cols [0, 1, 2] (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) scan run

end MAJ3

namespace K4

open Check Generic ThetaSigned SignedCofactor MinorSearch

def cols : List (W 55) := [(wordsBV 110 [0x37bdc1b7cb17, 0xa78000f80380000e]), (wordsBV 110 [0x3bd86eded57b, 0x19801f001c000031]), (wordsBV 110 [0x3d0ef77b66bd, 0x6a03e000e00040c0]), (wordsBV 110 [0x21ef7bedb8de, 0xd47c000700018100])]
def base : List (W 55) := signals 55 cols


def face0 : Minor 55 := (4, (wordsBV 110 [0x8423e4834e8, 0x587fff07fc7ffff1]), 9)
def pick0 : List (Fin 110) := [9, 0, 6, 59, 8, 60, 62, 67]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid0 : MinorValid 55 face0 base :=
  validates (H := 55) (n := 3) (t := 0xe8) (by decide) base face0 pick0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) MAJ3.lower

def face1 : Minor 55 := (4, (wordsBV 110 [0x42791212a84, 0xe67fe0ffe3ffffce]), 9)
def pick1 : List (Fin 110) := [9, 1, 6, 57, 8, 58, 62, 66]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid1 : MinorValid 55 face1 base :=
  validates (H := 55) (n := 3) (t := 0xe8) (by decide) base face1 pick1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) MAJ3.lower

def face2 : Minor 55 := (4, (wordsBV 110 [0x2f108849942, 0x95fc1fff1fffbf3f]), 9)
def pick2 : List (Fin 110) := [9, 1, 0, 55, 8, 58, 60, 65]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid2 : MinorValid 55 face2 base :=
  validates (H := 55) (n := 3) (t := 0xe8) (by decide) base face2 pick2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) MAJ3.lower

def face3 : Minor 55 := (4, (wordsBV 110 [0x1e1084124721, 0x2b83fff8fffe7eff]), 9)
def pick3 : List (Fin 110) := [9, 1, 0, 55, 6, 57, 59, 64]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid3 : MinorValid 55 face3 base :=
  validates (H := 55) (n := 3) (t := 0xe8) (by decide) base face3 pick3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) MAJ3.lower

def faces : List (Minor 55) := [face0, face1, face2, face3]

theorem faces_valid : ∀ c ∈ faces, MinorValid 55 c base := by
  intro c hc
  simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : guided 55 base (fun _ _ => faces) 6 3 base [] = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ k, Run (literals 4) k (truth 4 0xfee8) → 7 ≤ k :=
  fun k run => table_guided (H := 55) (n := 4) (t := 0xfee8) (cap := 6) (extra := 3)
    (by decide) cols [0, 1, 2, 3] faces faces_valid (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) scan run

end K4

namespace Leaf5

open Check Generic ThetaSigned SignedCofactor MinorSearch

def cols : List (W 64) := [(wordsBV 128 [0x5ed97f8b0dbe8b9d, 0x7f81f800000039c]), (wordsBV 128 [0xaf67e59436d43be2, 0x7ffe00000003be0]), (wordsBV 128 [0xfa4aaaa1571dbc85, 0xf80000001001bc01]), (wordsBV 128 [0x3474d3469fe5d12a, 0x1801c002]), (wordsBV 128 [0xc7871c78e7fb6650, 0xe0020000])]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : optimized 64 6 2 (signals 64 cols) = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ k, Run (literals 5) k (truth 5 0xfffeeea0) → 7 ≤ k :=
  fun k run => table_lower (H := 64) (n := 5) (t := 0xfffeeea0) (cap := 6) (extra := 2)
    (by decide) cols [0, 1, 2, 3, 4] (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) scan run

end Leaf5

namespace Fixed2

open Check Generic ThetaSigned SignedCofactor MinorSearch

def cols : List (W 72) := [(wordsBV 144 [0xb00d, 0x555b7b7d209e3d00, 0x1e3c]), (wordsBV 144 [0x4136, 0x666dada8079fc200, 0x79fc0]), (wordsBV 144 [0x1257, 0x878e3e38e7e20500, 0x1000000000e7e001]), (wordsBV 144 [0x649f, 0xf80fcfc8f9044a00, 0x1800000000f80002]), (wordsBV 144 [0x88e7, 0xfff00ff34a289000, 0xe000000003000000]), (wordsBV 144 [0xf07, 0xfffff0069451200f, 0x4000000])]
def base : List (W 72) := signals 72 cols


def face0 : Minor 72 := (7, (wordsBV 144 [0x4da0, 0x282080821801c2ff, 0xefffffffff1801c2]), 27)
def pick0 : List (Fin 144) := [27, 6, 1, 73, 24, 79, 91, 103, 26, 80, 92, 111, 97, 117, 123, 125]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid0 : MinorValid 72 face0 base :=
  validates (H := 72) (n := 4) (t := 0xfee8) (by decide) base face0 pick0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) K4.lower

def face1 : Minor 72 := (7, (wordsBV 144 [0xac88, 0x18104047180038ff, 0xefffffffff18003e]), 27)
def pick1 : List (Fin 144) := [27, 2, 1, 75, 24, 76, 91, 102, 26, 77, 92, 110, 97, 116, 123, 124]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid1 : MinorValid 72 face1 base :=
  validates (H := 72) (n := 4) (t := 0xfee8) (by decide) base face1 pick1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) K4.lower

def face2 : Minor 72 := (7, (wordsBV 144 [0x9a40, 0x1901017006035ff, 0xe7ffffffff00603d]), 27)
def pick2 : List (Fin 144) := [27, 2, 0, 72, 24, 76, 85, 100, 26, 77, 86, 108, 97, 116, 119, 120]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid2 : MinorValid 72 face2 base :=
  validates (H := 72) (n := 4) (t := 0xfee8) (by decide) base face2 pick2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) K4.lower

def face3 : Minor 72 := (7, (wordsBV 144 [0x7718, 0xff00cb5d76fff, 0x1ffffffffcffffff]), 27)
def pick3 : List (Fin 144) := [27, 2, 6, 9, 0, 72, 15, 81, 1, 75, 73, 82, 21, 93, 88, 99, 26, 77, 80, 84, 86, 108, 90, 109, 92, 110, 111, 112, 95, 113, 114, 115]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid3 : MinorValid 72 face3 base :=
  validates (H := 72) (n := 5) (t := 0xfffeeea0) (by decide) base face3 pick3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) Leaf5.lower

def face4 : Minor 72 := (7, (wordsBV 144 [0xf0f8, 0xff96baedff0, 0xfffffffffbffffff]), 27)
def pick4 : List (Fin 144) := [27, 2, 6, 9, 0, 72, 15, 81, 1, 75, 73, 82, 21, 93, 88, 99, 24, 76, 79, 83, 85, 100, 89, 101, 91, 102, 103, 104, 94, 105, 106, 107]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem valid4 : MinorValid 72 face4 base :=
  validates (H := 72) (n := 5) (t := 0xfffeeea0) (by decide) base face4 pick4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (Option.isSome_iff_exists.mp (by decide +kernel)) Leaf5.lower

def faces : List (Minor 72) := [face0, face1, face2, face3, face4]

theorem faces_valid : ∀ c ∈ faces, MinorValid 72 c base := by
  intro c hc
  simp only [faces, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem scan : guided 72 base (fun _ _ => faces) 9 4 base [] = false := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower : ∀ k, Run (literals 6) k (truth 6 0xfffffffefffeeea0) → 10 ≤ k :=
  fun k run => table_guided (H := 72) (n := 6) (t := 0xfffffffefffeeea0) (cap := 9) (extra := 4)
    (by decide) cols [0, 1, 2, 3, 4, 5] faces faces_valid (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) scan run

end Fixed2

def target7 (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def wg : List Gate := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [8, 6]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [12, 0]⟩, ⟨GateOp.and, [13, 11]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.and, [15, 10]⟩, ⟨GateOp.or, [16, 14]⟩]

def graph7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool :=
  (b0 && b3) || (b0 && b4) || (b1 && b4) || (b0 && b5) || (b1 && b5) || (b3 && b5) || (b4 && b5) ||
  (b0 && b6) || (b1 && b6) || (b2 && b6) || (b3 && b6) || (b4 && b6) || (b5 && b6)

theorem exists_lt_13 (Q : ℕ → Prop) :
    (∃ i < 13, Q i) ↔
      Q 0 ∨ Q 1 ∨ Q 2 ∨ Q 3 ∨ Q 4 ∨ Q 5 ∨ Q 6 ∨ Q 7 ∨ Q 8 ∨ Q 9 ∨ Q 10 ∨ Q 11 ∨ Q 12 := by
  constructor
  · rintro ⟨i, hi, hq⟩
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
        i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hq]
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
    · exact ⟨0, by decide, h⟩
    · exact ⟨1, by decide, h⟩
    · exact ⟨2, by decide, h⟩
    · exact ⟨3, by decide, h⟩
    · exact ⟨4, by decide, h⟩
    · exact ⟨5, by decide, h⟩
    · exact ⟨6, by decide, h⟩
    · exact ⟨7, by decide, h⟩
    · exact ⟨8, by decide, h⟩
    · exact ⟨9, by decide, h⟩
    · exact ⟨10, by decide, h⟩
    · exact ⟨11, by decide, h⟩
    · exact ⟨12, by decide, h⟩

theorem ofFn7_eq (x : Fin 7 → Bool) :
    List.ofFn x = [x ⟨0, by decide⟩, x ⟨1, by decide⟩, x ⟨2, by decide⟩, x ⟨3, by decide⟩,
      x ⟨4, by decide⟩, x ⟨5, by decide⟩, x ⟨6, by decide⟩] := by
  simp [List.ofFn_succ]

theorem graph7_decide : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    decide ((b0 = true ∧ b3 = true) ∨ (b0 = true ∧ b4 = true) ∨ (b1 = true ∧ b4 = true) ∨
      (b0 = true ∧ b5 = true) ∨ (b1 = true ∧ b5 = true) ∨ (b3 = true ∧ b5 = true) ∨
      (b4 = true ∧ b5 = true) ∨ (b0 = true ∧ b6 = true) ∨ (b1 = true ∧ b6 = true) ∨
      (b2 = true ∧ b6 = true) ∨ (b3 = true ∧ b6 = true) ∨ (b4 = true ∧ b6 = true) ∨
      (b5 = true ∧ b6 = true)) = graph7 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem target7_eq (x : Fin 7 → Bool) :
    target7 x = graph7 (x ⟨0, by decide⟩) (x ⟨1, by decide⟩) (x ⟨2, by decide⟩)
      (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩) := by
  unfold target7
  have hl : ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2 = 13 := rfl
  rw [hl]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, exists_lt_13, ofFn7_eq,
    List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.mul_one, Nat.reduceMul]
  have hdec := congrArg (· = true) (graph7_decide (x ⟨0, by decide⟩) (x ⟨1, by decide⟩)
    (x ⟨2, by decide⟩) (x ⟨3, by decide⟩) (x ⟨4, by decide⟩) (x ⟨5, by decide⟩) (x ⟨6, by decide⟩))
  exact iff_of_eq (by simpa only [decide_eq_true_eq] using hdec)

theorem wg_fits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wg_bool_eq : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    Circuit.eval ⟨wg, 17⟩ [b0, b1, b2, b3, b4, b5, b6] = graph7 b0 b1 b2 b3 b4 b5 b6 := by
  decide +kernel

theorem wg_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = target7 x := by
  intro x
  rw [ofFn7_eq, wg_bool_eq, target7_eq]

def pad2 (y : Fin 6 → Bool) : Fin 7 → Bool := fun i =>
  if h0 : i.val = 0 then y ⟨0, by decide⟩
  else if h1 : i.val = 1 then y ⟨1, by decide⟩
  else if h2 : i.val = 2 then false
  else if h3 : i.val = 3 then y ⟨2, by decide⟩
  else if h4 : i.val = 4 then y ⟨3, by decide⟩
  else if h5 : i.val = 5 then y ⟨4, by decide⟩
  else y ⟨5, by decide⟩

def inputs6 (y : Fin 6 → Bool) : List Bool := List.ofFn (pad2 y)

theorem inputs6_length (y : Fin 6 → Bool) : (inputs6 y).length = 7 := by
  simp [inputs6]

theorem inputs6_read (i : ℕ) : ThetaSigned.readW inputs6 i ∈ SignedCofactor.literals 6 := by
  by_cases hi : i < 7
  · have hread : ThetaSigned.readW inputs6 i = fun y => pad2 y ⟨i, hi⟩ := by
      funext y
      change (List.ofFn (pad2 y)).getD i false = pad2 y ⟨i, hi⟩
      rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
    rw [hread]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨⟨0, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
    · exact Or.inr ⟨⟨1, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
    · exact Or.inl ⟨false, funext fun y => by simp [pad2, ThetaSigned.bit]⟩
    · exact Or.inr ⟨⟨2, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
    · exact Or.inr ⟨⟨3, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
    · exact Or.inr ⟨⟨4, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
    · exact Or.inr ⟨⟨5, by decide⟩, Or.inl (funext fun y => by simp [pad2])⟩
  · refine Or.inl ⟨false, ?_⟩
    funext y
    change (inputs6 y).getD i false = false
    exact List.getD_eq_default _ _ (by rw [inputs6_length]; omega)

theorem index6_eq (y : Fin 6 → Bool) :
    MinorSearch.index y =
      (if y ⟨0, by decide⟩ then 1 else 0) + (if y ⟨1, by decide⟩ then 2 else 0) +
      (if y ⟨2, by decide⟩ then 4 else 0) + (if y ⟨3, by decide⟩ then 8 else 0) +
      (if y ⟨4, by decide⟩ then 16 else 0) + (if y ⟨5, by decide⟩ then 32 else 0) := by
  simp [MinorSearch.index, List.finRange_succ]

theorem pad2_bool_eq : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    graph7 b0 b1 false b2 b3 b4 b5 =
      (0xfffffffefffeeea0 : ℕ).testBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) +
        (if b2 then 4 else 0) + (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)) := by
  decide +kernel

theorem pad2_truth : (fun y : Fin 6 → Bool => target7 (pad2 y)) = MinorSearch.truth 6 0xfffffffefffeeea0 := by
  funext y
  rw [target7_eq]
  simp only [pad2, MinorSearch.truth, index6_eq]
  exact pad2_bool_eq _ _ _ _ _ _

theorem main_proof : ∀ (gates : List Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
    (∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target7 x) →
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = target7 x := by
  intro gates o hok _ heval
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g, hg, hgn⟩ := hnot
    have hrun := ThetaSigned.compile gates o hok inputs6 7 inputs6_length
      (SignedCofactor.literals 6) (SignedCofactor.literals_closed 6) inputs6_read
    have hfun : (fun y : Fin 6 → Bool => (ThetaSigned.wiresFrom gates (inputs6 y)).getD o false) =
        MinorSearch.truth 6 0xfffffffefffeeea0 := by
      rw [← pad2_truth]
      funext y
      exact heval (pad2 y)
    have hlow := Fixed2.lower (ThetaSigned.budget gates) (hfun ▸ hrun)
    have hlt := ThetaSigned.budget_lt_of_not gates g hg hgn
    have hlen : wg.length ≤ gates.length := by
      change 11 ≤ gates.length
      omega
    exact ⟨wg, 17, wg_fits, hlen, wg_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, heval⟩
    intro g hg
    rcases hok g hg with ⟨h | h | h, hl⟩
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact False.elim (hnot ⟨g, hg, h⟩)

end PEqualNP.Outside.L_meta_10784

theorem PEqualNP.Outside.L_meta_10784 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  exact PEqualNP.Outside.L_meta_10784.main_proof
