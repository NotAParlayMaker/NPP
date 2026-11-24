import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5032

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def reads (g : Gate) (w : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = Option.some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs

lemma foldl_len (f : List Bool → Gate → Bool) : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl (fun w g => w ++ [f w g]) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma foldl_getD (f : List Bool → Gate → Bool) : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
    i < w.length → (gs.foldl (fun w g => w ++ [f w g]) w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_snoc (w : List Bool) (v : Bool) (n : ℕ) (hn : w.length = n) :
    (w ++ [v]).getD n false = v := by
  subst hn
  simp [List.getD_eq_getElem?_getD]

lemma all_false_getD (i : ℕ) : (List.ofFn (fun _ : Fin 9 => false)).getD i false = false := by
  rcases Nat.lt_or_ge i 9 with h | h
  · interval_cases i <;> rfl
  · exact List.getD_eq_default _ _ (by simpa using h)

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_len _ _ _

lemma first_gate (L : List Gate)
    (h : ∀ x : Fin 9 → Bool, (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD 9 false = (x 0 || x 2)) :
    ∃ g0 rest, L = g0 :: rest ∧ g0.op ≠ GateOp.not ∧ ∀ x : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
  cases L with
  | nil =>
    have h1 := h (fun _ => true)
    rw [List.foldl_nil, List.getD_eq_default _ _ (by simp)] at h1
    simp at h1
  | cons g0 rest =>
    have hv : ∀ x : Fin 9 → Bool,
        g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2) := by
      intro x
      have h1 := h x
      simp only [List.foldl_cons] at h1
      rw [foldl_getD (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) rest _ 9 (by simp),
        getD_snoc _ _ 9 (by simp)] at h1
      exact h1
    refine ⟨g0, rest, rfl, ?_, hv⟩
    intro hop
    have h2 := hv (fun _ => false)
    rw [hop] at h2
    have h3 : (g0.inputs.map fun i => (List.ofFn (fun _ : Fin 9 => false)).getD i false).headD false
        = false := by
      cases g0.inputs with
      | nil => rfl
      | cons i t => exact all_false_getD i
    have h2' : (!(g0.inputs.map fun i =>
        (List.ofFn (fun _ : Fin 9 => false)).getD i false).headD false) = (false || false) := h2
    rw [h3] at h2'
    exact absurd h2' (by decide)

lemma not_step (w : List Bool) (ga : Gate) (hga : ga.op = GateOp.not) (hlen : w.length ≤ 12) :
    ga.op.eval (ga.inputs.map fun i => w.getD i false)
      = !w.getD (min (ga.inputs.headD 12) 12) false := by
  rw [hga]
  cases ga.inputs with
  | nil =>
    have h9 : w.getD 12 false = false := List.getD_eq_default _ _ hlen
    show (!false) = !w.getD (min 12 12) false
    rw [Nat.min_self, h9]
  | cons i t =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    rcases Nat.lt_or_ge i 12 with h | h
    · rw [Nat.min_eq_left (le_of_lt h)]
    · rw [Nat.min_eq_right h, List.getD_eq_default _ _ hlen,
        List.getD_eq_default _ _ (le_trans hlen h)]

lemma countP_one {α : Type} (p : α → Bool) (l : List α) (k : ℕ) (hk : k < l.length)
    (hp : p l[k] = true) (hu : ∀ (i : ℕ) (hi : i < l.length), p l[i] = true → i = k) :
    l.countP p = 1 := by
  have hs : l.take k ++ l[k] :: l.drop (k + 1) = l := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have h1 : (l.take k).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    rw [List.getElem_take]
    intro hc
    have h4 := hu i (by simp at hi; omega) hc
    simp at hi
    omega
  have h2 : (l.drop (k + 1)).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    rw [List.getElem_drop]
    intro hc
    have h4 := hu (k + 1 + i) (by simp at hi; omega) hc
    omega
  calc l.countP p = (l.take k ++ l[k] :: l.drop (k + 1)).countP p := by rw [hs]
    _ = 1 := by rw [List.countP_append, List.countP_cons_of_pos hp, h1, h2]

lemma split_one {α : Type} (p : α → Bool) (l : List α) (a b : ℕ) (hab : a < b)
    (hb : b < l.length) (hpb : p l[b] = true)
    (hu : ∀ (i : ℕ) (hi : i < l.length), p l[i] = true → i = a ∨ i = b) :
    (∀ g ∈ l.take a, p g = false) ∧ (l.drop (a + 1)).countP p = 1 := by
  constructor
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hi' : i < a := by simp at hi; omega
    rw [List.getElem_take]
    by_contra hc
    have h4 := hu i (by omega) (by simpa using hc)
    omega
  · apply countP_one p (l.drop (a + 1)) (b - a - 1) (by simp; omega)
    · have h5 : a + 1 + (b - a - 1) = b := by omega
      simp only [List.getElem_drop, h5]
      exact hpb
    · intro i hi hp
      rw [List.getElem_drop] at hp
      have h4 := hu (a + 1 + i) (by simp at hi; omega) hp
      omega

lemma fan_cases {g : Gate}
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
  simpa using h

lemma eval_false_not {g : Gate}
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hp : g.op.eval [false] = true) : g.op = GateOp.not := by
  rcases fan_cases h with h | h | h
  · rw [h] at hp; simp [GateOp.eval] at hp
  · rw [h] at hp; simp [GateOp.eval] at hp
  · exact h

lemma core (g0 : Gate) (Mg : List Gate) (ga : Gate) (post : List Gate) (out : ℕ)
    (hfan : ∀ g ∈ g0 :: (Mg ++ ga :: post),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hsize : (g0 :: (Mg ++ ga :: post)).length ≤ 15)
    (hMlen : Mg.length ≤ 2)
    (hMmono : ∀ g ∈ Mg, g.op.eval [false] = false)
    (hga : ga.op = GateOp.not)
    (hcount : post.countP (fun g => g.op.eval [false]) = 1)
    (hv0 : ∀ x : Fin 9 → Bool,
      g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 2))
    (hread : ∀ w : ℕ, w = 0 ∨ w = 2 → ∃ g ∈ Mg ++ ga :: post, reads g w) :
    ∃ (M N : Circuit) (j : Fin 13), Monotone2 M ∧ FanInTwo N ∧ M.size ≤ 2 ∧
      M.size + N.size ≤ 13 ∧
      List.countP (fun g : Gate => g.op.eval [false]) N.gates = 1 ∧
      (∀ w : ℕ, w = 0 ∨ w = 2 → (j : ℕ) = w ∨ ∃ g ∈ M.gates ++ N.gates, reads g w) ∧
      ∀ x : Fin 9 → Bool,
        N.eval (M.wires (List.ofFn x ++ [x 0 || x 2]) ++
          [!(M.wires (List.ofFn x ++ [x 0 || x 2])).getD (j : ℕ) false])
          = (Circuit.mk (g0 :: (Mg ++ ga :: post)) out).eval (List.ofFn x) := by
  refine ⟨⟨Mg, 0⟩, ⟨post, out⟩, ⟨min (ga.inputs.headD 12) 12, by omega⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ Mg := hg
    have h1 := hfan g (by simp [hg'])
    have h2 := hMmono g hg'
    refine ⟨?_, h1.2⟩
    rcases fan_cases h1.1 with h | h | h
    · simp [h]
    · simp [h]
    · rw [h] at h2
      simp [GateOp.eval] at h2
  · intro g hg
    have hg' : g ∈ post := hg
    exact hfan g (by simp [hg'])
  · exact hMlen
  · simp only [Circuit.size]
    simp at hsize
    omega
  · exact hcount
  · intro w hw
    obtain ⟨g, hg, hr⟩ := hread w hw
    rcases List.mem_append.1 hg with h | h
    · right
      exact ⟨g, List.mem_append_left _ h, hr⟩
    · rcases List.mem_cons.1 h with h | h
      · left
        subst h
        rcases hr with ⟨_, hh⟩ | ⟨hne, _⟩
        · have h6 : g.inputs.headD 12 = w := by
            cases hi : g.inputs with
            | nil => simp [hi] at hh
            | cons i t =>
              simp [hi] at hh
              simp [hh]
          show min (g.inputs.headD 12) 12 = w
          rw [h6]
          omega
        · exact absurd hga hne
      · right
        exact ⟨g, List.mem_append_right _ h, hr⟩
  · intro x
    have hlen : (Circuit.wires ⟨Mg, 0⟩ (List.ofFn x ++ [x 0 || x 2])).length ≤ 12 := by
      rw [wires_length]
      simp
      omega
    have e1 := hv0 x
    have e2 := not_step (Circuit.wires ⟨Mg, 0⟩ (List.ofFn x ++ [x 0 || x 2])) ga hga hlen
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_append] at e2 ⊢
    rw [e1, e2]

lemma main (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 15)
    (hnot : ∃ (a b : Fin C.gates.length), a < b ∧ (a : ℕ) ≤ 3 ∧
      (C.gates.get a).op = GateOp.not ∧ (C.gates.get b).op = GateOp.not ∧
      ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i = a ∨ i = b)
    (hw9 : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hread : ∀ w : ℕ, w = 0 ∨ w = 2 → ∃ g ∈ List.drop 1 C.gates, reads g w) :
    ∃ (M N : Circuit) (j : Fin 13), Monotone2 M ∧ FanInTwo N ∧ M.size ≤ 2 ∧
      M.size + N.size ≤ 13 ∧
      List.countP (fun g : Gate => g.op.eval [false]) N.gates = 1 ∧
      (∀ w : ℕ, w = 0 ∨ w = 2 → (j : ℕ) = w ∨ ∃ g ∈ M.gates ++ N.gates, reads g w) ∧
      ∀ x : Fin 9 → Bool,
        N.eval (M.wires (List.ofFn x ++ [x 0 || x 2]) ++
          [!(M.wires (List.ofFn x ++ [x 0 || x 2])).getD (j : ℕ) false])
          = C.eval (List.ofFn x) := by
  obtain ⟨L, out⟩ := C
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, ha3, hna, hnb, hu⟩ := hnot
  obtain ⟨g0, rest, rfl, hg0, hv0⟩ := first_gate L hw9
  have hfan' : ∀ g ∈ g0 :: rest,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := hfan
  have hsize' : (g0 :: rest).length ≤ 15 := hsize
  have hread' : ∀ w : ℕ, w = 0 ∨ w = 2 → ∃ g ∈ rest, reads g w := by
    intro w hw
    simpa using hread w hw
  cases a with
  | zero => exact absurd hna hg0
  | succ a' =>
    cases b with
    | zero => exact absurd hab (by simp)
    | succ b' =>
      have ha' : a' < rest.length := Nat.lt_of_succ_lt_succ ha
      have hb' : b' < rest.length := Nat.lt_of_succ_lt_succ hb
      have hna' : rest[a'].op = GateOp.not := hna
      have hnb' : rest[b'].op = GateOp.not := hnb
      have hab' : a' < b' := by simpa using hab
      have ha3' : a' ≤ 2 := by
        have h7 : a' + 1 ≤ 3 := ha3
        omega
      have hu' : ∀ (i : ℕ) (hi : i < rest.length),
          (fun g : Gate => g.op.eval [false]) rest[i] = true → i = a' ∨ i = b' := by
        intro i hi hp
        have hop : rest[i].op = GateOp.not :=
          eval_false_not (hfan' rest[i] (List.mem_cons_of_mem _ (List.getElem_mem hi))).1 hp
        rcases hu ⟨i + 1, Nat.succ_lt_succ hi⟩ hop with h | h
        · left
          have h8 := Fin.ext_iff.1 h
          simp at h8
          exact h8
        · right
          have h8 := Fin.ext_iff.1 h
          simp at h8
          exact h8
      obtain ⟨hpre, hcnt⟩ := split_one (fun g : Gate => g.op.eval [false]) rest a' b' hab' hb'
        (by show rest[b'].op.eval [false] = true; rw [hnb']; rfl) hu'
      have hsplit : rest.take a' ++ rest[a'] :: rest.drop (a' + 1) = rest := by
        rw [← List.drop_eq_getElem_cons ha', List.take_append_drop]
      have key := core g0 (rest.take a') rest[a'] (rest.drop (a' + 1)) out
        (by rw [hsplit]; exact hfan') (by rw [hsplit]; exact hsize')
        (by simp; omega) hpre hna' hcnt hv0 (by rw [hsplit]; exact hread')
      rw [hsplit] at key
      exact key

end PEqualNP.Outside.L_meta_5032

theorem PEqualNP.Outside.L_meta_5032 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       (∃ (x5 : Fin x2.gates.length) (x6 : Fin x2.gates.length), x5 < x6 ∧ ↑x5 ≤ (3 : ℕ) ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x7 : Fin x2.gates.length), (x2.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not → x7 = x5 ∨ x7 = x6) →         (∀ (x6 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)))) →           (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) →             ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin (13 : ℕ)),               PEqualNP.MetaComplexity.Monotone2 x8 ∧                 PEqualNP.MetaComplexity.FanInTwo x9 ∧                   x8.size ≤ (2 : ℕ) ∧                     x8.size + x9.size ≤ (13 : ℕ) ∧                       List.countP (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.false]) x9.gates = (1 : ℕ) ∧                         (∀ (x11 : ℕ), x11 = (0 : ℕ) ∨ x11 = (2 : ℕ) → ↑x10 = x11 ∨ ∃ x13 ∈ x8.gates ++ x9.gates, x1 x13 x11) ∧                           ∀ (x11 : Fin (9 : ℕ) → Bool),                             have x12 : List Bool := x8.wires (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ))]);                             x9.eval (x12 ++ [!x12.getD (↑x10) Bool.false]) = x2.eval (List.ofFn x11) := by
  intro x1 C h1 h2 h3 h4 h5
  exact PEqualNP.Outside.L_meta_5032.main C h1 h2 h3 h4 h5
