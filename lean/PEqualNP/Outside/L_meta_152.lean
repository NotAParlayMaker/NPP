import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_152

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Fn := (Fin 4 → Bool) → Bool

def J (h : Fn) : Prop :=
  h (fun _ => false) = false ∧ ∀ x y : Fin 4 → Bool, h (fun i => x i || y i) = (h x || h y)

def Good (a : Fn) : Prop :=
  (∃ h1 h2 : Fn, J h1 ∧ J h2 ∧ ∀ x, a x = (h1 x && h2 x)) ∨ ∀ x, a x = true

def Kls (a h : Fn) : Prop :=
  J h ∨ ∃ g : Fn, J g ∧ ∀ x, h x = (g x || a x)

def wf (W : (Fin 4 → Bool) → List Bool) (i : ℕ) : Fn := fun x => (W x).getD i false

def Inv (P : Prop) (W : (Fin 4 → Bool) → List Bool) : Prop :=
  (¬ P → ∀ i, J (wf W i)) ∧ ∃ a, Good a ∧ ∀ i, Kls a (wf W i)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma J_false : J (fun _ => false) := by
  constructor <;> simp

lemma J_or {f g : Fn} (hf : J f) (hg : J g) : J (fun x => f x || g x) := by
  refine ⟨by simp [hf.1, hg.1], fun x y => ?_⟩
  simp only [hf.2, hg.2]
  cases f x <;> cases f y <;> cases g x <;> cases g y <;> rfl

lemma J_congr {f g : Fn} (hf : J f) (h : ∀ x, g x = f x) : J g := by
  have : g = f := funext h
  subst this; exact hf

lemma Kls_or {a f g : Fn} (hf : Kls a f) (hg : Kls a g) : Kls a (fun x => f x || g x) := by
  rcases hf with hf | ⟨f', hf', ef⟩ <;> rcases hg with hg | ⟨g', hg', eg⟩
  · exact Or.inl (J_or hf hg)
  · refine Or.inr ⟨fun x => f x || g' x, J_or hf hg', fun x => ?_⟩
    simp only [eg]; cases f x <;> cases g' x <;> cases a x <;> rfl
  · refine Or.inr ⟨fun x => f' x || g x, J_or hf' hg, fun x => ?_⟩
    simp only [ef]; cases f' x <;> cases g x <;> cases a x <;> rfl
  · refine Or.inr ⟨fun x => f' x || g' x, J_or hf' hg', fun x => ?_⟩
    simp only [ef, eg]; cases f' x <;> cases g' x <;> cases a x <;> rfl

lemma Kls_of_J {a h : Fn} (hh : J h) : Kls a h := Or.inl hh

lemma getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false)
      else w.getD i false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · have h' : ¬ i = w.length := by omega
    simp only [h', ↓reduceIte]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h' : ¬ i = w.length := by omega
    simp only [h', ↓reduceIte]
    have h1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length ≤ i := by
      simp; omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ (le_of_lt h)]

lemma wf_step (W : (Fin 4 → Bool) → List Bool) (L : ℕ) (hL : ∀ x, (W x).length = L)
    (g : Gate) (i : ℕ) :
    wf (fun x => step (W x) g) i = if i = L then
      (fun x => g.op.eval (g.inputs.map fun j => (W x).getD j false)) else wf W i := by
  funext x
  simp only [wf, getD_step, hL]
  split_ifs <;> rfl

lemma inv_step (P : Prop) (W : (Fin 4 → Bool) → List Bool) (L : ℕ)
    (hL : ∀ x, (W x).length = L) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g.inputs.length ≤ 2) (hand : g.op = GateOp.and → ¬ P) (hI : Inv P W) :
    Inv (P ∨ g.op = GateOp.and) (fun x => step (W x) g) := by
  obtain ⟨hJ, a, ha, hK⟩ := hI
  obtain ⟨op, ins⟩ := g
  simp only at hop h2 hand ⊢
  rcases hop with rfl | rfl
  · -- the AND gate: every earlier wire is a join map
    have hJ' := hJ (hand rfl)
    rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
    · refine ⟨fun h => absurd (Or.inr rfl) h, fun _ => true, Or.inr (fun _ => rfl), fun i => ?_⟩
      rw [wf_step W L hL]
      split_ifs
      · exact Or.inr ⟨fun _ => false, J_false, fun x => by simp [GateOp.eval]⟩
      · exact Kls_of_J (hJ' i)
    · refine ⟨fun h => absurd (Or.inr rfl) h, a, ha, fun i => ?_⟩
      rw [wf_step W L hL]
      split_ifs
      · exact Kls_of_J (J_congr (hJ' p) (fun x => by simp [GateOp.eval, wf]))
      · exact Kls_of_J (hJ' i)
    · refine ⟨fun h => absurd (Or.inr rfl) h, fun x => wf W p x && wf W q x,
        Or.inl ⟨wf W p, wf W q, hJ' p, hJ' q, fun x => rfl⟩, fun i => ?_⟩
      rw [wf_step W L hL]
      split_ifs
      · exact Or.inr ⟨fun _ => false, J_false, fun x => by simp [GateOp.eval, wf]⟩
      · exact Kls_of_J (hJ' i)
    · simp at h2
  · -- an OR gate
    have hv : (fun x => GateOp.or.eval (ins.map fun j => (W x).getD j false)) =
        fun x => (ins.map fun j => wf W j x).any id := by
      funext x; simp [GateOp.eval, wf]
    rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
    · refine ⟨fun hP i => ?_, a, ha, fun i => ?_⟩ <;> rw [wf_step W L hL] <;> split_ifs <;>
        first
        | exact J_congr J_false (fun x => by simp [GateOp.eval])
        | exact Kls_of_J (J_congr J_false (fun x => by simp [GateOp.eval]))
        | exact hJ (fun h => hP (Or.inl h)) i
        | exact hK i
    · refine ⟨fun hP i => ?_, a, ha, fun i => ?_⟩ <;> rw [wf_step W L hL] <;> split_ifs
      · exact J_congr (hJ (fun h => hP (Or.inl h)) p) (fun x => by simp [GateOp.eval, wf])
      · exact hJ (fun h => hP (Or.inl h)) i
      · rcases hK p with h | ⟨g', hg', e⟩
        · exact Or.inl (J_congr h (fun x => by simp [GateOp.eval, wf]))
        · exact Or.inr ⟨g', hg', fun x => by rw [← e]; simp [GateOp.eval, wf]⟩
      · exact hK i
    · refine ⟨fun hP i => ?_, a, ha, fun i => ?_⟩ <;> rw [wf_step W L hL] <;> split_ifs
      · exact J_congr (J_or (hJ (fun h => hP (Or.inl h)) p) (hJ (fun h => hP (Or.inl h)) q))
          (fun x => by simp [GateOp.eval, wf])
      · exact hJ (fun h => hP (Or.inl h)) i
      · have := Kls_or (hK p) (hK q)
        rcases this with h | ⟨g', hg', e⟩
        · exact Or.inl (J_congr h (fun x => by simp [GateOp.eval, wf]))
        · exact Or.inr ⟨g', hg', fun x => by rw [← e]; simp [GateOp.eval, wf]⟩
      · exact hK i
    · simp at h2

lemma inv_fold : ∀ (gs : List Gate) (P : Prop) (W : (Fin 4 → Bool) → List Bool) (L : ℕ),
    (∀ x, (W x).length = L) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (P → ∀ g ∈ gs, g.op ≠ GateOp.and) →
    (∀ (i j : ℕ) (gi gj : Gate), gs[i]? = some gi → gs[j]? = some gj →
      gi.op = GateOp.and → gj.op = GateOp.and → i = j) →
    Inv P W → ∃ Q, Inv Q (fun x => gs.foldl step (W x)) := by
  intro gs
  induction gs with
  | nil => intro P W L _ _ _ _ hI; exact ⟨P, hI⟩
  | cons g gs ih =>
    intro P W L hL hm hP hu hI
    have hg := hm g (List.mem_cons_self ..)
    have hand : g.op = GateOp.and → ¬ P := fun ha hp => hP hp g (List.mem_cons_self ..) ha
    have hI' := inv_step P W L hL g hg.1 hg.2 hand hI
    have := ih (P ∨ g.op = GateOp.and) (fun x => step (W x) g) (L + 1)
      (fun x => by simp [step, hL]) (fun g' h' => hm g' (List.mem_cons_of_mem _ h'))
      (by
        rintro (hp | ha) g' hg' ha'
        · exact hP hp g' (List.mem_cons_of_mem _ hg') ha'
        · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg'
          have := hu 0 (k + 1) g g' rfl (by simpa using hk) ha ha'
          omega)
      (fun i j gi gj hi hj hai haj => by
        have := hu (i + 1) (j + 1) gi gj (by simpa using hi) (by simpa using hj) hai haj
        omega)
      hI'
    simpa [List.foldl_cons] using this

lemma ofFn_getD (x : Fin 4 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 4 then x ⟨i, h⟩ else false := by
  split_ifs with h
  · interval_cases i <;> rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma J_input (i : ℕ) : J (wf (fun x => List.ofFn x) i) := by
  refine ⟨?_, fun x y => ?_⟩ <;> simp only [wf, ofFn_getD] <;> split_ifs <;> rfl

lemma jd {f : Fn} (hf : J f) (x y z : Fin 4 → Bool) (hz : ∀ i, z i = (x i || y i)) :
    f z = (f x || f y) := by
  have : z = fun i => x i || y i := funext hz
  subst this; exact hf.2 x y

end PEqualNP.Outside.L_meta_152

open PEqualNP.Outside.L_meta_152 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  rintro ⟨C, hmono, ⟨A, hA, hAnd⟩, hf⟩
  have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have hu : ∀ (i j : ℕ) (gi gj : Gate), C.gates[i]? = some gi → C.gates[j]? = some gj →
      gi.op = GateOp.and → gj.op = GateOp.and → i = j := fun i j gi gj hi hj hai haj =>
    Finset.card_le_one.mp hA i (hAnd i gi hi hai) j (hAnd j gj hj haj)
  have h0 : Inv False (fun x => List.ofFn x) :=
    ⟨fun _ i => J_input i, fun _ => false,
      Or.inl ⟨fun _ => false, fun _ => false, J_false, J_false, fun _ => rfl⟩,
      fun i => Kls_of_J (J_input i)⟩
  obtain ⟨Q, -, a, ha, hK⟩ :=
    inv_fold C.gates False (fun x => List.ofFn x) 4 (fun x => by simp) hm (fun h => h.elim) hu h0
  have hK' := hK C.output
  set h : Fn := wf (fun x => C.gates.foldl step (List.ofFn x)) C.output with hdef
  have hh : ∀ x, h x = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true :=
    fun x => hf x
  have hT : ∀ x, (∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) → h x = true :=
    fun x hx => (hh x).2 hx
  have hF : ∀ x, ¬ (∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) →
      h x = false := fun x hx => by
    cases hv : h x
    · rfl
    · exact absurd ((hh x).1 hv) hx
  have z0 := hF ![false, false, false, false] (by decide)
  have s0 := hF ![true, false, false, false] (by decide)
  have s1 := hF ![false, true, false, false] (by decide)
  have s2 := hF ![false, false, true, false] (by decide)
  have s3 := hF ![false, false, false, true] (by decide)
  have t01 := hT ![true, true, false, false] (by decide)
  have t23 := hT ![false, false, true, true] (by decide)
  have f02 := hF ![true, false, true, false] (by decide)
  have f03 := hF ![true, false, false, true] (by decide)
  have f13 := hF ![false, true, false, true] (by decide)
  rcases hK' with hJ | ⟨g, hg, e⟩
  · rw [jd hJ ![true, false, false, false] ![false, true, false, false] _
      (fun i => by fin_cases i <;> rfl), s0, s1] at t01
    exact absurd t01 (by decide)
  · rcases ha with ⟨h1, h2, j1, j2, ea⟩ | ea
    · have E : ∀ z, h z = (g z || (h1 z && h2 z)) := fun z => by rw [e z, ea z]
      have D : ∀ f : Fn, J f → ∀ (x y z : Fin 4 → Bool), (∀ i, z i = (x i || y i)) →
          f z = (f x || f y) := fun f hf x y z hz => jd hf x y z hz
      rw [E] at s0 s1 s2 s3 t01 t23 f02 f03 f13
      rw [D g hg ![true, false, false, false] ![false, true, false, false] _
          (fun i => by fin_cases i <;> rfl),
        D h1 j1 ![true, false, false, false] ![false, true, false, false] _
          (fun i => by fin_cases i <;> rfl),
        D h2 j2 ![true, false, false, false] ![false, true, false, false] _
          (fun i => by fin_cases i <;> rfl)] at t01
      rw [D g hg ![false, false, true, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h1 j1 ![false, false, true, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h2 j2 ![false, false, true, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl)] at t23
      rw [D g hg ![true, false, false, false] ![false, false, true, false] _
          (fun i => by fin_cases i <;> rfl),
        D h1 j1 ![true, false, false, false] ![false, false, true, false] _
          (fun i => by fin_cases i <;> rfl),
        D h2 j2 ![true, false, false, false] ![false, false, true, false] _
          (fun i => by fin_cases i <;> rfl)] at f02
      rw [D g hg ![true, false, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h1 j1 ![true, false, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h2 j2 ![true, false, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl)] at f03
      rw [D g hg ![false, true, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h1 j1 ![false, true, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl),
        D h2 j2 ![false, true, false, false] ![false, false, false, true] _
          (fun i => by fin_cases i <;> rfl)] at f13
      revert s0 s1 s2 s3 t01 t23 f02 f03 f13
      generalize g ![true, false, false, false] = c0
      generalize g ![false, true, false, false] = c1
      generalize g ![false, false, true, false] = c2
      generalize g ![false, false, false, true] = c3
      generalize h1 ![true, false, false, false] = a0
      generalize h1 ![false, true, false, false] = a1
      generalize h1 ![false, false, true, false] = a2
      generalize h1 ![false, false, false, true] = a3
      generalize h2 ![true, false, false, false] = b0
      generalize h2 ![false, true, false, false] = b1
      generalize h2 ![false, false, true, false] = b2
      generalize h2 ![false, false, false, true] = b3
      revert c0 c1 c2 c3 a0 a1 a2 a3 b0 b1 b2 b3
      decide
    · rw [e, ea] at z0
      exact absurd z0 (by simp)
