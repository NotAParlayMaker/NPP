import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem getD_append_len (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem getD_ofFn (m : ℕ) (f : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def mu (k n w : ℕ) : ℕ := if w < k then w else w + n

def mapGate (k n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (mu k n)⟩

theorem remap (k n : ℕ) (hk : k ≤ n) : ∀ (gs : List Gate) (w1 w2 : List Bool),
    n ≤ w1.length → w2.length = w1.length + n →
    (∀ w, w2.getD (mu k n w) false = w1.getD w false) →
    ∀ w, ((gs.map (mapGate k n)).foldl step w2).getD (mu k n w) false =
      (gs.foldl step w1).getD w false := by
  intro gs
  induction gs with
  | nil =>
    intro w1 w2 _ _ h
    exact h
  | cons g gs ih =>
    intro w1 w2 hn hl h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [step]; omega
    · simp [step]; omega
    · intro w
      have hv : (mapGate k n g).op.eval ((mapGate k n g).inputs.map fun i => w2.getD i false) =
          g.op.eval (g.inputs.map fun i => w1.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      unfold step
      by_cases h1 : w < w1.length
      · have hm : mu k n w < w2.length := by
          unfold mu; split_ifs <;> omega
        rw [getD_append_lt _ _ _ hm, getD_append_lt _ _ _ h1]
        exact h w
      · by_cases h2 : w = w1.length
        · have hm : mu k n w = w2.length := by
            unfold mu; split_ifs <;> omega
          rw [hm, h2, getD_append_len, getD_append_len]
          exact hv
        · have hm : w2.length + 1 ≤ mu k n w := by
            unfold mu; split_ifs <;> omega
          rw [getD_of_length_le _ _ (by simp; omega), getD_of_length_le _ _ (by simp; omega)]


theorem mu_lt (k n : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < n) : mu k n i < n + n := by
  unfold mu; split_ifs <;> omega

theorem mu_mono (k n : ℕ) (i j : ℕ) (h : i < n + j) : mu k n i < n + n + j := by
  unfold mu; split_ifs <;> omega

def extra (n : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → List Gate
  | _, _, [] => []
  | prev, base, (a, b) :: t =>
    ⟨GateOp.and, [a, n + b]⟩ :: ⟨GateOp.or, [prev, base]⟩ :: extra n (base + 1) (base + 2) t

def outW : ℕ → ℕ → List (ℕ × ℕ) → ℕ
  | prev, _, [] => prev
  | _, base, _ :: t => outW (base + 1) (base + 2) t

theorem extra_length (n : ℕ) : ∀ (L : List (ℕ × ℕ)) (prev base : ℕ),
    (extra n prev base L).length = 2 * L.length := by
  intro L
  induction L with
  | nil => intro prev base; rfl
  | cons p t ih =>
    intro prev base
    obtain ⟨a, b⟩ := p
    simp only [extra, List.length_cons, ih]
    ring

theorem extra_ops (n : ℕ) : ∀ (L : List (ℕ × ℕ)) (prev base : ℕ), ∀ g ∈ extra n prev base L,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro L
  induction L with
  | nil => intro prev base g hg; simp [extra] at hg
  | cons p t ih =>
    intro prev base g hg
    obtain ⟨a, b⟩ := p
    simp only [extra, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact ih _ _ g hg

theorem extra_reads (n : ℕ) : ∀ (L : List (ℕ × ℕ)) (prev base : ℕ), prev < base →
    (∀ p ∈ L, p.1 < base ∧ n + p.2 < base) →
    ∀ t (ht : t < (extra n prev base L).length), ∀ i ∈ ((extra n prev base L)[t]).inputs,
      i < base + t := by
  intro L
  induction L with
  | nil => intro prev base _ _ t ht; simp [extra] at ht
  | cons p tl ih =>
    intro prev base hp hb t ht i hi
    obtain ⟨a, b⟩ := p
    have hab := hb (a, b) List.mem_cons_self
    match t, ht, hi with
    | 0, _, hi =>
      simp only [extra, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simp at hab; omega
      · simp at hab; omega
    | 1, _, hi =>
      simp only [extra, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    | t + 2, ht, hi =>
      simp only [extra, List.getElem_cons_succ] at hi
      simp only [extra, List.length_cons] at ht
      have := ih (base + 1) (base + 2) (by omega)
        (fun q hq => by have := hb q (List.mem_cons_of_mem _ hq); omega) t (by omega) i hi
      omega

theorem chain (n bound : ℕ) (ρ : ℕ → Bool) : ∀ (L : List (ℕ × ℕ)) (prev base : ℕ) (w : List Bool),
    w.length = base → bound ≤ base → prev < base →
    (∀ p ∈ L, p.1 < bound ∧ n + p.2 < bound) →
    (∀ i, i < bound → w.getD i false = ρ i) →
    ((extra n prev base L).foldl step w).getD (outW prev base L) false =
      (w.getD prev false || L.any (fun p => ρ p.1 && ρ (n + p.2))) := by
  intro L
  induction L with
  | nil => intro prev base w _ _ _ _ _; simp [extra, outW]
  | cons p tl ih =>
    intro prev base w hl hbd hp hb hρ
    obtain ⟨a, b⟩ := p
    have hab := hb (a, b) List.mem_cons_self
    simp only at hab
    simp only [extra, outW, List.foldl_cons]
    set w1 := step w ⟨GateOp.and, [a, n + b]⟩ with hw1
    set w2 := step w1 ⟨GateOp.or, [prev, base]⟩ with hw2
    have hl1 : w1.length = base + 1 := by simp [hw1, step, hl]
    have hl2 : w2.length = base + 2 := by simp [hw2, step, hl1]
    have e1 : ∀ i, i < base → w1.getD i false = w.getD i false := fun i hi => by
      rw [hw1]; unfold step; exact getD_append_lt _ _ _ (by omega)
    have e2 : ∀ i, i < base + 1 → w2.getD i false = w1.getD i false := fun i hi => by
      rw [hw2]; unfold step; exact getD_append_lt _ _ _ (by omega)
    have hand : w1.getD base false = (ρ a && ρ (n + b)) := by
      rw [hw1]; unfold step
      rw [← hl, getD_append_len]
      show GateOp.and.eval [w.getD a false, w.getD (n + b) false] = _
      rw [hρ a (by omega), hρ (n + b) (by omega)]
      simp [GateOp.eval]
    have hor : w2.getD (base + 1) false = (w.getD prev false || (ρ a && ρ (n + b))) := by
      rw [hw2]; unfold step
      rw [← hl1, getD_append_len]
      show GateOp.or.eval [w1.getD prev false, w1.getD base false] = _
      rw [e1 prev hp, hand]
      simp [GateOp.eval]
    rw [ih (base + 1) (base + 2) w2 hl2 (by omega) (by omega)
      (fun q hq => hb q (List.mem_cons_of_mem _ hq))
      (fun i hi => by rw [e2 i (by omega), e1 i (by omega)]; exact hρ i hi), hor]
    simp [List.any_cons, Bool.or_assoc]

end PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd x8 x13) = Bool.true ∧ x12 (Fin.natAdd x8 x14) = Bool.true) := by
  intro x1 x2 x3 C hne hC hf
  dsimp only
  intro x10
  have hk : x1 ≤ x1 + x2 := Nat.le_add_right x1 x2
  have hout : C.output < (x1 + x2) + C.gates.length := by
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    by_contra hge
    push_neg at hge
    have h1 := hf (fun q => decide (q = Fin.castAdd x2 p ∨ q = Fin.natAdd x1 l))
    have h2 : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C
        (fun q => decide (q = Fin.castAdd x2 p ∨ q = Fin.natAdd x1 l)) = false := by
      show (C.wires _).getD C.output false = false
      apply PEqualNP.Outside.L_meta_3264.getD_of_length_le
      rw [PEqualNP.Outside.L_meta_3264.wires_eq, PEqualNP.Outside.L_meta_3264.foldl_step_length, List.length_ofFn]
      exact hge
    have h3 : decide (∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧
        (fun q => decide (q = Fin.castAdd x2 p ∨ q = Fin.natAdd x1 l)) (Fin.castAdd x2 a) = true ∧
        (fun q => decide (q = Fin.castAdd x2 p ∨ q = Fin.natAdd x1 l)) (Fin.natAdd x1 b) = true) = true :=
      decide_eq_true ⟨p, l, hpl, by simp, by simp⟩
    rw [h2, h3] at h1
    exact absurd h1 (by decide)
  let L : List (ℕ × ℕ) := x10.toList.map (fun p => (p.1.val, p.2.val))
  let base := (x1 + x2) + (x1 + x2) + C.gates.length
  have hprev : PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) C.output < base := PEqualNP.Outside.L_meta_3264.mu_mono x1 (x1 + x2) _ _ hout
  have hpairs : ∀ p ∈ L, p.1 < (x1 + x2) + (x1 + x2) ∧ (x1 + x2) + p.2 < (x1 + x2) + (x1 + x2) := by
    intro p hp
    simp only [L, List.mem_map, Finset.mem_toList] at hp
    obtain ⟨q, _, rfl⟩ := hp
    exact ⟨by have := q.1.isLt; omega, by have := q.2.isLt; omega⟩
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_3264.mapGate x1 (x1 + x2)) ++
      PEqualNP.Outside.L_meta_3264.extra (x1 + x2) (PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) C.output) base L,
      PEqualNP.Outside.L_meta_3264.outW (PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) C.output) base L⟩, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg
      · exact hC.1 g0 hg0
      · exact (PEqualNP.Outside.L_meta_3264.extra_ops _ _ _ _ g hg).1
    · intro j hj i hi
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
      simp only at hj hi
      by_cases hjA : j < C.gates.length
      · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_left (by simpa using hjA),
          List.getElem_map] at hi
        simp only [PEqualNP.Outside.L_meta_3264.mapGate, List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have hr := hC.2.1 j hjA i0 (by
          unfold PEqualNP.MetaComplexity.NestedCover.gateAt
          rw [List.getD_eq_getElem _ _ hjA]
          exact hi0)
        exact PEqualNP.Outside.L_meta_3264.mu_mono x1 (x1 + x2) i0 j hr
      · rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right (by simpa using hjA)] at hi
        have hlen : j - (C.gates.map (PEqualNP.Outside.L_meta_3264.mapGate x1 (x1 + x2))).length <
            (PEqualNP.Outside.L_meta_3264.extra (x1 + x2) (PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) C.output) base L).length := by
          simp only [List.length_append, List.length_map] at hj ⊢
          omega
        have := PEqualNP.Outside.L_meta_3264.extra_reads (x1 + x2) L _ base hprev
          (fun p hp => ⟨by have := (hpairs p hp).1; omega, by have := (hpairs p hp).2; omega⟩)
          _ hlen i hi
        simp only [List.length_map] at this
        omega
    · intro g hg
      simp only [List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg
      · simp only [PEqualNP.Outside.L_meta_3264.mapGate, List.length_map]
        exact hC.2.2 g0 hg0
      · exact (PEqualNP.Outside.L_meta_3264.extra_ops _ _ _ _ g hg).2
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map,
      PEqualNP.Outside.L_meta_3264.extra_length, L, Finset.length_toList]
    exact le_refl _
  · intro y
    let x : Fin (x1 + x2) → Bool := fun i => y ⟨PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) i, PEqualNP.Outside.L_meta_3264.mu_lt x1 (x1 + x2) hk i i.isLt⟩
    let ρ : ℕ → Bool := fun i => (List.ofFn y).getD i false
    show (PEqualNP.CircuitLowerBounds.Circuit.wires _ (List.ofFn y)).getD _ false = _
    rw [PEqualNP.Outside.L_meta_3264.wires_eq]
    simp only [List.foldl_append]
    have hlenW : ((C.gates.map (PEqualNP.Outside.L_meta_3264.mapGate x1 (x1 + x2))).foldl PEqualNP.Outside.L_meta_3264.step (List.ofFn y)).length = base := by
      rw [PEqualNP.Outside.L_meta_3264.foldl_step_length, List.length_ofFn, List.length_map]
    have hρ : ∀ i, i < (x1 + x2) + (x1 + x2) →
        ((C.gates.map (PEqualNP.Outside.L_meta_3264.mapGate x1 (x1 + x2))).foldl PEqualNP.Outside.L_meta_3264.step (List.ofFn y)).getD i false = ρ i := by
      intro i hi
      exact PEqualNP.Outside.L_meta_3264.foldl_step_getD _ _ _ (by simpa using hi)
    rw [PEqualNP.Outside.L_meta_3264.chain (x1 + x2) ((x1 + x2) + (x1 + x2)) ρ L _ base _ hlenW (by omega) hprev hpairs hρ]
    have hbase : ∀ w, (List.ofFn y).getD (PEqualNP.Outside.L_meta_3264.mu x1 (x1 + x2) w) false = (List.ofFn x).getD w false := by
      intro w
      by_cases hw : w < x1 + x2
      · rw [PEqualNP.Outside.L_meta_3264.getD_ofFn _ _ _ (PEqualNP.Outside.L_meta_3264.mu_lt x1 (x1 + x2) hk w hw), PEqualNP.Outside.L_meta_3264.getD_ofFn _ _ _ hw]
      · rw [PEqualNP.Outside.L_meta_3264.getD_of_length_le _ _ (by simp; unfold PEqualNP.Outside.L_meta_3264.mu; split_ifs <;> omega),
          PEqualNP.Outside.L_meta_3264.getD_of_length_le _ _ (by simp; omega)]
    rw [PEqualNP.Outside.L_meta_3264.remap x1 (x1 + x2) hk C.gates (List.ofFn x) (List.ofFn y) (by simp) (by simp) hbase C.output]
    have hCx := hf x
    change (C.gates.foldl PEqualNP.Outside.L_meta_3264.step (List.ofFn x)).getD C.output false = _ at hCx
    rw [hCx]
    have hxp : ∀ p : Fin x1, x (Fin.castAdd x2 p) = y (Fin.castAdd (x1 + x2) (Fin.castAdd x2 p)) := by
      intro p
      simp only [x]
      congr 1
      ext
      simp [PEqualNP.Outside.L_meta_3264.mu, p.isLt]
    have hxl : ∀ l : Fin x2, x (Fin.natAdd x1 l) = y (Fin.natAdd (x1 + x2) (Fin.natAdd x1 l)) := by
      intro l
      simp only [x]
      congr 1
      ext
      simp [PEqualNP.Outside.L_meta_3264.mu]
    have hρa : ∀ a : Fin (x1 + x2), ρ a.val = y (Fin.castAdd (x1 + x2) a) := by
      intro a
      simp only [ρ]
      rw [PEqualNP.Outside.L_meta_3264.getD_ofFn _ _ _ (by have := a.isLt; omega)]
      rfl
    have hρb : ∀ b : Fin (x1 + x2), ρ ((x1 + x2) + b.val) = y (Fin.natAdd (x1 + x2) b) := by
      intro b
      simp only [ρ]
      rw [PEqualNP.Outside.L_meta_3264.getD_ofFn _ _ _ (by have := b.isLt; omega)]
      rfl
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, L,
      List.mem_map, Finset.mem_toList]
    constructor
    · rintro (⟨p, l, hpl, h1, h2⟩ | ⟨q, ⟨a, ha, rfl⟩, h1, h2⟩)
      · exact ⟨Fin.castAdd x2 p, Fin.natAdd x1 l,
          Finset.mem_union_left _ (Finset.mem_image.2 ⟨(p, l), hpl, rfl⟩),
          by rw [← hxp]; exact h1, by rw [← hxl]; exact h2⟩
      · exact ⟨a.1, a.2, Finset.mem_union_right _ ha, by rw [← hρa]; exact h1, by rw [← hρb]; exact h2⟩
    · rintro ⟨a, b, hab, h1, h2⟩
      rcases Finset.mem_union.1 hab with h | h
      · obtain ⟨⟨p, l⟩, hpl, he⟩ := Finset.mem_image.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        left
        exact ⟨p, l, hpl, by rw [hxp]; exact h1, by rw [hxl]; exact h2⟩
      · right
        exact ⟨(a.val, b.val), ⟨(a, b), h, rfl⟩, by rw [hρa]; exact h1, by rw [hρb]; exact h2⟩
