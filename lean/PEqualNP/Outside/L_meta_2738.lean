import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2738

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mo (i : ℕ) : ℕ := if i < 10 then i else i + 2

def m (j a : ℕ) : ℕ := if a < 10 then a else if a < 10 + j then a + 2 else 10

def norm (j : ℕ) : GateOp → List ℕ → Gate
  | GateOp.not, [] => ⟨GateOp.not, [10]⟩
  | GateOp.not, a :: _ => ⟨GateOp.not, [m j a]⟩
  | GateOp.and, [] => ⟨GateOp.or, [10, 11]⟩
  | GateOp.or, [] => ⟨GateOp.and, [10, 11]⟩
  | _, [a] => ⟨GateOp.and, [m j a, 11]⟩
  | op, [a, b] => if m j a = m j b then ⟨GateOp.and, [m j a, 11]⟩ else ⟨op, [m j a, m j b]⟩
  | _, _ => ⟨GateOp.and, [10, 11]⟩

def normList : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => norm j g.op g.inputs :: normList (j + 1) gs

lemma normList_length (j : ℕ) (gs : List Gate) : (normList j gs).length = gs.length := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih => simp [normList, ih]

lemma m_ne (j a : ℕ) : m j a ≠ 11 := by
  unfold m; split_ifs <;> omega

lemma m_lt (j a : ℕ) : m j a < 12 + j := by
  unfold m; split_ifs <;> omega

def Shape (s : ℕ) (g : Gate) : Prop :=
  (∀ a ∈ g.inputs, a < 12 + s) ∧ g.inputs.Nodup ∧
    (g.op = GateOp.not ∧ g.inputs.length = 1 ∨ g.op ≠ GateOp.not ∧ g.inputs.length = 2) ∧
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)

lemma norm_shape (j : ℕ) (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ins : List ℕ)
    (hlen : ins.length ≤ 2) : Shape j (norm j op ins) := by
  have h1 := m_ne j
  have h2 := m_lt j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [norm, Shape] <;> omega
  · rcases hop with rfl | rfl | rfl <;> simp [norm, Shape, h1 a, h2 a] <;> omega
  · rcases hop with rfl | rfl | rfl
    · dsimp only [norm]; split_ifs with h
      · simp [Shape, h1 a, h2 a]; omega
      · simp [Shape, h, h2 a, h2 b]
    · dsimp only [norm]; split_ifs with h
      · simp [Shape, h1 a, h2 a]; omega
      · simp [Shape, h, h2 a, h2 b]
    · simp [norm, Shape, h2 a]
  · simp at hlen

lemma normList_shape (gs : List Gate)
    (hF : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ (j k : ℕ) (hk : k < (normList j gs).length), Shape (j + k) ((normList j gs)[k]) := by
  induction gs with
  | nil => intro j k hk; simp [normList] at hk
  | cons g gs ih =>
    intro j k hk
    cases k with
    | zero =>
      simp only [normList, List.getElem_cons_zero, Nat.add_zero]
      exact norm_shape j g.op (hF g (by simp)).1 g.inputs (hF g (by simp)).2
    | succ k =>
      simp only [normList, List.getElem_cons_succ]
      have hk' : k < (normList (j + 1) gs).length := by simpa [normList] using hk
      have := ih (fun g hg => hF g (by simp [hg])) (j + 1) k hk'
      rwa [show j + 1 + k = j + (k + 1) by omega] at this

lemma getD_app (w l : List Bool) (k : ℕ) (hk : k < w.length) :
    (w ++ l).getD k false = w.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_len (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_out (w : List Bool) (k : ℕ) (hk : w.length ≤ k) : w.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma gate_ok (j : ℕ) (w w' : List Bool)
    (hm : ∀ a, w'.getD (m j a) false = w.getD a false)
    (h10 : w'.getD 10 false = false) (h11 : w'.getD 11 false = true) (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ins : List ℕ)
    (hlen : ins.length ≤ 2) :
    (norm j op ins).op.eval ((norm j op ins).inputs.map fun i => w'.getD i false) =
      op.eval (ins.map fun i => w.getD i false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only [List.getD_eq_getElem?_getD] at hm h10 h11 ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [norm, GateOp.eval, h10, h11]
  · rcases hop with rfl | rfl | rfl <;> simp [norm, GateOp.eval, hm, h11]
  · rcases hop with rfl | rfl | rfl
    · dsimp only [norm]; split_ifs with h
      · have hab : w[a]?.getD false = w[b]?.getD false := by rw [← hm a, ← hm b, h]
        simp [GateOp.eval, hm, h11, hab]
      · simp [GateOp.eval, hm]
    · dsimp only [norm]; split_ifs with h
      · have hab : w[a]?.getD false = w[b]?.getD false := by rw [← hm a, ← hm b, h]
        simp [GateOp.eval, hm, h11, hab]
      · simp [GateOp.eval, hm]
    · simp [norm, GateOp.eval, hm]
  · simp at hlen

lemma sim (gs : List Gate)
    (hF : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ (j : ℕ) (w w' : List Bool), w.length = 10 + j → w'.length = 12 + j →
      (∀ i < 10 + j, w'.getD (mo i) false = w.getD i false) →
      w'.getD 10 false = false → w'.getD 11 false = true →
      ∀ i < 10 + j + gs.length,
        ((normList j gs).foldl step w').getD (mo i) false = (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro j w w' _ _ hR _ _ i hi; exact hR i (by simpa using hi)
  | cons g gs ih =>
    intro j w w' hw hw' hR h10 h11
    have hm : ∀ a, w'.getD (m j a) false = w.getD a false := by
      intro a
      by_cases ha : a < 10 + j
      · have : m j a = mo a := by unfold m mo; split_ifs <;> omega
        rw [this, hR a ha]
      · have : m j a = 10 := by unfold m; split_ifs <;> omega
        rw [this, h10, getD_out w a (by omega)]
    have hg := gate_ok j w w' hm h10 h11 g.op (hF g (by simp)).1 g.inputs (hF g (by simp)).2
    simp only [normList, List.foldl_cons]
    have key := ih (fun g hg => hF g (by simp [hg])) (j + 1) (step w g)
      (step w' (norm j g.op g.inputs))
      (by simp [step, hw]; omega) (by simp [step, hw']; omega)
      (by
        intro i hi
        unfold step
        rw [hg]
        by_cases hi' : i < 10 + j
        · rw [getD_app _ _ _ (by unfold mo; split_ifs <;> omega), getD_app _ _ _ (by omega)]
          exact hR i hi'
        · have e1 : i = w.length := by omega
          have e2 : mo i = w'.length := by unfold mo; split_ifs <;> omega
          rw [e2, getD_len, e1, getD_len])
      (by unfold step; rw [getD_app _ _ _ (by omega)]; exact h10)
      (by unfold step; rw [getD_app _ _ _ (by omega)]; exact h11)
    intro i hi
    exact key i (by simp at hi; omega)

end PEqualNP.Outside.L_meta_2738

theorem PEqualNP.Outside.L_meta_2738 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     x2 < x3 →       x3 < (10 : ℕ) + x1.length →         ∃ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ) (x9 : ℕ),           x7.length ≤ x1.length ∧             x8 < (12 : ℕ) + x7.length ∧               x9 < (12 : ℕ) + x7.length ∧                 PEqualNP.MetaComplexity.FanInTwo { gates := x7, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } ∧                   (∀ (x10 : Fin x7.length),                       have x11 : PEqualNP.CircuitLowerBounds.Gate := x7.get x10;                       (∀ x12 ∈ x11.inputs, x12 < (12 : ℕ) + ↑x10) ∧ x11.inputs.Nodup ∧ (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (1 : ℕ) ∨ x11.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x11.inputs.length = (2 : ℕ))) ∧                     ∀ (x10 : List Bool), x10.length = (10 : ℕ) → ({ gates := x7, output := x8 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true]) || { gates := x7, output := x9 : PEqualNP.CircuitLowerBounds.Circuit }.eval (x10 ++ [Bool.false, Bool.true])) = ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x10) := by
  intro x1 x2 x3 hF h23 h3
  have hF' : ∀ g ∈ x1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := hF
  have hmo : ∀ i, i < 10 + x1.length → L_meta_2738.mo i < 12 + x1.length := by
    intro i hi; unfold L_meta_2738.mo; split_ifs <;> omega
  refine ⟨L_meta_2738.normList 0 x1, L_meta_2738.mo x2, L_meta_2738.mo x3,
    by rw [L_meta_2738.normList_length],
    by rw [L_meta_2738.normList_length]; exact hmo x2 (by omega),
    by rw [L_meta_2738.normList_length]; exact hmo x3 h3, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, _, hs, hop⟩ := L_meta_2738.normList_shape x1 hF' 0 k hk
    refine ⟨hop, ?_⟩
    show (L_meta_2738.normList 0 x1)[k].inputs.length ≤ 2
    rcases hs with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · intro k
    obtain ⟨ha, hb, hc, _⟩ := L_meta_2738.normList_shape x1 hF' 0 k k.2
    simp only [List.get_eq_getElem, Nat.zero_add] at ha hb hc ⊢
    exact ⟨ha, hb, hc⟩
  · intro x10 hx
    have hR : ∀ i < 10 + 0, (x10 ++ [false, true]).getD (L_meta_2738.mo i) false =
        x10.getD i false := by
      intro i hi
      have : L_meta_2738.mo i = i := by unfold L_meta_2738.mo; split_ifs <;> omega
      rw [this, L_meta_2738.getD_app _ _ _ (by omega)]
    have h10 : (x10 ++ [false, true]).getD 10 false = false := by
      simp [List.getD_eq_getElem?_getD, hx]
    have h11 : (x10 ++ [false, true]).getD 11 false = true := by
      simp [List.getD_eq_getElem?_getD, hx]
    have hS := L_meta_2738.sim x1 hF' 0 x10 (x10 ++ [false, true]) (by omega)
      (by simp [hx]) hR h10 h11
    show ((List.foldl L_meta_2738.step _ _).getD _ _ ||
        (List.foldl L_meta_2738.step _ _).getD _ _) =
      ((List.foldl L_meta_2738.step _ _).getD _ _ || (List.foldl L_meta_2738.step _ _).getD _ _)
    rw [hS x2 (by omega), hS x3 (by omega)]
