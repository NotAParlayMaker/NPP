import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta152

open PEqualNP.CircuitLowerBounds

abbrev In := Fin 4 → Bool

-- A wire function that is an OR of some inputs: it preserves joins and is false at zero.
def Jp (F : In → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ x y : In, F (fun q => x q || y q) = (F x || F y)

-- The possible values of the single AND gate.
def Gand (g : In → Bool) : Prop :=
  (∃ h1 h2 : In → Bool, Jp h1 ∧ Jp h2 ∧ ∀ x, g x = (h1 x && h2 x)) ∨ (∀ x, g x = true)

-- A wire after the AND gate: an OR of inputs, or-ed with the AND gate.
def Good2 (g F : In → Bool) : Prop :=
  ∃ h : In → Bool, Jp h ∧ ∀ x, F x = (h x || g x)

def Good (m : Option (In → Bool)) (F : In → Bool) : Prop :=
  match m with
  | none => Jp F
  | some g => Jp F ∨ Good2 g F

def Inv (m : Option (In → Bool)) (W : In → List Bool) : Prop :=
  (∀ g, m = some g → Gand g) ∧ ∀ i : ℕ, Good m (fun x => (W x).getD i false)

theorem jp_false : Jp (fun _ => false) := ⟨rfl, fun _ _ => rfl⟩

theorem jp_or {F G : In → Bool} (hF : Jp F) (hG : Jp G) : Jp (fun x => F x || G x) := by
  refine ⟨by simp [hF.1, hG.1], fun x y => ?_⟩
  simp only [hF.2 x y, hG.2 x y]
  cases F x <;> cases F y <;> cases G x <;> cases G y <;> rfl

theorem good_false (m : Option (In → Bool)) : Good m (fun _ => false) := by
  cases m with
  | none => exact jp_false
  | some g => exact Or.inl jp_false

theorem good_or {m : Option (In → Bool)} {F G : In → Bool} (hF : Good m F) (hG : Good m G) :
    Good m (fun x => F x || G x) := by
  cases m with
  | none => exact jp_or hF hG
  | some g =>
    rcases hF with hF | ⟨h, hh, hFx⟩ <;> rcases hG with hG | ⟨h', hh', hGx⟩
    · exact Or.inl (jp_or hF hG)
    · refine Or.inr ⟨fun x => F x || h' x, jp_or hF hh', fun x => ?_⟩
      simp only [hGx x]; cases F x <;> cases h' x <;> cases g x <;> rfl
    · refine Or.inr ⟨fun x => h x || G x, jp_or hh hG, fun x => ?_⟩
      simp only [hFx x]; cases G x <;> cases h x <;> cases g x <;> rfl
    · refine Or.inr ⟨fun x => h x || h' x, jp_or hh hh', fun x => ?_⟩
      simp only [hFx x, hGx x]; cases h x <;> cases h' x <;> cases g x <;> rfl

theorem getD_append_single (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then v else false := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · have : w.length + 1 ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_inv (A : Finset ℕ) (hA : A.card ≤ 1) : ∀ (gs : List Gate) (k : ℕ)
    (m : Option (In → Bool)) (W : In → List Bool) (len : ℕ),
    (∀ x, (W x).length = len) → Inv m W → (m.isSome → ∃ j0 ∈ A, j0 < k) →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → k + j ∈ A) →
    ∃ m', Inv m' (fun x => gs.foldl step (W x)) := by
  intro gs
  induction gs with
  | nil => intro k m W len _ hI _ _ _; exact ⟨m, hI⟩
  | cons g gs ih =>
    intro k m W len hlen hI hseen hok hand
    simp only [List.foldl_cons]
    have hg := hok g (by simp)
    -- the value function of the new wire
    set F : ℕ → In → Bool := fun i x => (W x).getD i false with hFdef
    have hval : ∀ x, g.op.eval (g.inputs.map fun i => (W x).getD i false)
        = g.op.eval (g.inputs.map fun i => F i x) := fun x => rfl
    have hW' : ∀ i x, (step (W x) g).getD i false =
        if i < len then F i x else if i = len then
          g.op.eval (g.inputs.map fun i => F i x) else false := by
      intro i x
      simp only [step, getD_append_single, hlen x, hFdef]
    -- the new invariant
    obtain ⟨m', hI', hseen'⟩ : ∃ m', Inv m' (fun x => step (W x) g) ∧
        (m'.isSome → ∃ j0 ∈ A, j0 < k + 1) := by
      have hop := hg.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have hgood_old : ∀ i, Good m (F i) := hI.2
      rcases hop with hop | hop
      · -- an AND gate
        have hk : k ∈ A := by
          have := hand 0 g (by simp) hop
          simpa using this
        cases m with
        | some g0 =>
          exfalso
          obtain ⟨j0, hj0, hlt⟩ := hseen rfl
          have := Finset.card_le_one.mp hA j0 hj0 k hk
          omega
        | none =>
          set V : In → Bool := fun x => g.op.eval (g.inputs.map fun i => F i x) with hV
          have hGand : Gand V := by
            have hlen2 := hg.2
            rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · right; intro x; simp [hV, hin, hop, GateOp.eval]
            · left; refine ⟨F a, F a, hgood_old a, hgood_old a, fun x => ?_⟩
              simp [hV, hin, hop, GateOp.eval]
            · left; refine ⟨F a, F b, hgood_old a, hgood_old b, fun x => ?_⟩
              simp [hV, hin, hop, GateOp.eval]
            · rw [hin] at hlen2; simp at hlen2
          refine ⟨some V, ⟨(fun g' hg' => (Option.some_inj.mp hg') ▸ hGand), fun i => ?_⟩,
            (fun _ => ⟨k, hk, by omega⟩)⟩
          show Jp _ ∨ Good2 V _
          by_cases h1 : i < len
          · left
            have : (fun x => (step (W x) g).getD i false) = F i := by
              funext x; rw [hW']; simp [h1]
            rw [this]; exact hgood_old i
          · by_cases h2 : i = len
            · right
              refine ⟨fun _ => false, jp_false, fun x => ?_⟩
              show (step (W x) g).getD i false = (false || V x)
              rw [hW']; simp [h1, h2, hV]
            · left
              have : (fun x => (step (W x) g).getD i false) = fun _ => false := by
                funext x; rw [hW']; simp [h1, h2]
              rw [this]; exact jp_false
      · -- an OR gate
        refine ⟨m, ⟨hI.1, fun i => ?_⟩, fun h => by
          obtain ⟨j0, hj0, hlt⟩ := hseen h; exact ⟨j0, hj0, by omega⟩⟩
        by_cases h1 : i < len
        · have : (fun x => (step (W x) g).getD i false) = F i := by
            funext x; rw [hW']; simp [h1]
          rw [this]; exact hgood_old i
        · by_cases h2 : i = len
          · have : (fun x => (step (W x) g).getD i false) =
                fun x => g.op.eval (g.inputs.map fun i => F i x) := by
              funext x; rw [hW']; simp [h1, h2]
            rw [this]
            have hlen2 := hg.2
            rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · have e1 : (fun x => g.op.eval (g.inputs.map fun i => F i x)) =
                  fun _ => false := by funext x; simp [hin, hop, GateOp.eval]
              rw [← hin, e1]; exact good_false m
            · have e1 : (fun x => g.op.eval (g.inputs.map fun i => F i x)) = F a := by
                funext x; simp [hin, hop, GateOp.eval]
              rw [← hin, e1]; exact hgood_old a
            · have e1 : (fun x => g.op.eval (g.inputs.map fun i => F i x)) =
                  fun x => F a x || F b x := by
                funext x; simp [hin, hop, GateOp.eval]
              rw [← hin, e1]; exact good_or (hgood_old a) (hgood_old b)
            · rw [hin] at hlen2; simp at hlen2
          · have : (fun x => (step (W x) g).getD i false) = fun _ => false := by
              funext x; rw [hW']; simp [h1, h2]
            rw [this]; exact good_false m
    exact ih (k + 1) m' (fun x => step (W x) g) (len + 1)
      (fun x => by simp [step, hlen x]) hI' hseen'
      (fun g' hg' => hok g' (by simp [hg']))
      (fun j g' hj hop => by
        have := hand (j + 1) g' (by simpa using hj) hop
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)

theorem init_inv : Inv none (fun x : In => List.ofFn x) := by
  refine ⟨(fun g h => by simp at h), fun i => ?_⟩
  show Jp (fun x : In => (List.ofFn x).getD i false)
  by_cases hi : i < 4
  · have : (fun x : In => (List.ofFn x).getD i false) = fun x => x ⟨i, hi⟩ := by
      funext x
      interval_cases i <;> rfl
    rw [this]; exact ⟨rfl, fun _ _ => rfl⟩
  · have : (fun x : In => (List.ofFn x).getD i false) = fun _ => false := by
      funext x
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]; exact jp_false

abbrev P4 (x : In) : Prop := ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true

def e (i : Fin 4) : In := fun q => decide (q = i)

def pr (a b : Fin 4) : In := fun q => e a q || e b q

theorem key : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Bool,
    (a0 || (b0 && c0)) = false → (a1 || (b1 && c1)) = false →
    (a2 || (b2 && c2)) = false → (a3 || (b3 && c3)) = false →
    ((a0 || a1) || ((b0 || b1) && (c0 || c1))) = true →
    ((a2 || a3) || ((b2 || b3) && (c2 || c3))) = true →
    ((a0 || a2) || ((b0 || b2) && (c0 || c2))) = false →
    ((a0 || a3) || ((b0 || b3) && (c0 || c3))) = false →
    ((a1 || a3) || ((b1 || b3) && (c1 || c3))) = false → False := by
  decide

theorem not_p4 (m : Option (In → Bool)) (F : In → Bool) (hm : ∀ g, m = some g → Gand g)
    (hF : Good m F) (hP : ∀ x, F x = true ↔ P4 x) : False := by
  have hv : ∀ x, F x = decide (P4 x) := by
    intro x; by_cases h : P4 x
    · simp [h, (hP x).2 h]
    · simp [h]; exact Bool.eq_false_iff.mpr (fun h' => h ((hP x).1 h'))
  have hpr : ∀ a b : Fin 4, pr a b = fun q => e a q || e b q := fun _ _ => rfl
  have v0 : F (fun _ => false) = false := by rw [hv]; decide
  have ve : ∀ i, F (e i) = false := by intro i; rw [hv]; revert i; decide
  have p01 : F (pr 0 1) = true := by rw [hv]; decide
  have p23 : F (pr 2 3) = true := by rw [hv]; decide
  have p02 : F (pr 0 2) = false := by rw [hv]; decide
  have p03 : F (pr 0 3) = false := by rw [hv]; decide
  have p13 : F (pr 1 3) = false := by rw [hv]; decide
  have hjp : Jp F → False := by
    intro hJ
    have := hJ.2 (e 0) (e 1)
    rw [← hpr, p01, ve, ve] at this
    simp at this
  cases m with
  | none => exact hjp hF
  | some g =>
    rcases hF with hF | ⟨h, hh, hFx⟩
    · exact hjp hF
    · rcases hm g rfl with ⟨h1, h2, hh1, hh2, hg⟩ | hg
      · have expand : ∀ a b : Fin 4, F (pr a b) =
            ((h (e a) || h (e b)) || ((h1 (e a) || h1 (e b)) && (h2 (e a) || h2 (e b)))) := by
          intro a b
          rw [hFx, hg, hpr, hh.2, hh1.2, hh2.2]
        have single : ∀ i, F (e i) = (h (e i) || (h1 (e i) && h2 (e i))) := by
          intro i; rw [hFx, hg]
        exact key _ _ _ _ _ _ _ _ _ _ _ _
          ((single 0).symm.trans (ve 0)) ((single 1).symm.trans (ve 1))
          ((single 2).symm.trans (ve 2)) ((single 3).symm.trans (ve 3))
          ((expand 0 1).symm.trans p01) ((expand 2 3).symm.trans p23)
          ((expand 0 2).symm.trans p02) ((expand 0 3).symm.trans p03)
          ((expand 1 3).symm.trans p13)
      · have := hFx (fun _ => false)
        rw [v0, hg] at this
        simp at this

end PEqualNP.Outside.Meta152

open PEqualNP.Outside.Meta152 in
theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  rintro ⟨C, hmono, ⟨A, hA, hand⟩, hf⟩
  obtain ⟨m, hI⟩ := fold_inv A hA C.gates 0 none (fun x : In => List.ofFn x) 4
    (fun x => by simp) init_inv (fun h => by simp at h) hmono
    (fun j g hj hop => by simpa using hand j g hj hop)
  exact not_p4 m (fun x => (C.wires (List.ofFn x)).getD C.output false) hI.1 (hI.2 C.output)
    (fun x => hf x)
