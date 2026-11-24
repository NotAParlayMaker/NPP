import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2227_aux
open PEqualNP.CircuitLowerBounds

-- Wire-value helpers adapted from c4ss, PR4206, and degree-fold helpers
-- from the project line-degree proof development.
-- https://github.com/brilliant-hq/pequalnp-proofs/pull/4206

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

lemma V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val_aux (n : ℕ) (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) :
    V gs x (n + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (n + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at n pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

def deval (op : GateOp) (xs : List ℕ) : ℕ :=
  if op = GateOp.and then xs.sum else xs.foldr max 0

def stepD (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [deval g.op (g.inputs.map fun i => w.getD i 0)]

lemma foldlD_len (gs : List Gate) (w : List ℕ) :
    (gs.foldl stepD w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepD]
    omega

lemma foldlD_getD_lt (gs : List Gate) (w : List ℕ) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepD w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepD w g).length := by simp [stepD]; omega
    rw [ih (stepD w g) hlt]
    simp [stepD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldlD_char (gs : List Gate) (w : List ℕ) :
    ∀ j, j < gs.length → (gs.foldl stepD w).getD (w.length + j) 0 =
      deval (gs.getD j ⟨GateOp.or, []⟩).op ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepD w).getD i 0 else 0) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldlD_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepD (gs.foldl stepD w) g).getD i 0 = (gs.foldl stepD w).getD i 0 := by
      intro i hi
      simp only [stepD, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepD (gs.foldl stepD w) g).getD (w.length + gs.length) 0 =
          deval g.op (g.inputs.map fun i => (gs.foldl stepD w).getD i 0) := by
        simp only [stepD, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def dg (n : ℕ) (u : Fin n) (C : Circuit) (i : ℕ) : ℕ :=
  (C.lineDegrees n {u.val}).getD i 0

lemma dg_input (n : ℕ) (u : Fin n) (C : Circuit) (i : ℕ) (hi : i < n) :
    dg n u C i = if i = u.val then 1 else 0 := by
  unfold dg Circuit.lineDegrees
  change (C.gates.foldl stepD _).getD i 0 = _
  rw [foldlD_getD_lt _ _ i (by simpa using hi)]
  simp [List.getD,hi]

lemma dg_gate (n : ℕ) (u : Fin n) (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hb : ∀ a ∈ g.inputs, a < n + j) :
    dg n u C (n+j) = deval g.op (g.inputs.map (dg n u C)) := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).choose
  have h := foldlD_char C.gates ((List.range n).map fun i => if i ∈ ({u.val} : Finset ℕ) then 1 else 0) j hj
  simp only [List.length_map,List.length_range] at h
  have hget : C.gates.getD j ⟨GateOp.or,[]⟩ = g := by
    simp [List.getD,hg]
  rw [hget] at h
  unfold dg Circuit.lineDegrees
  change (C.gates.foldl stepD _).getD (n+j) 0 = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hb i hi)]
  rfl

lemma V_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    V C.gates (List.ofFn x) i = x ⟨i,hi⟩ := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD,hi]

lemma and_step (a b c d p q : Bool) (da db : ℕ)
    (ha0 : da = 0 → c = true → a = true)
    (hb0 : db = 0 → d = true → b = true)
    (ha1 : da ≤ 1 → c = true → a = true ∨ p = true)
    (hb1 : db ≤ 1 → d = true → b = true ∨ q = true) :
    (da + db = 0 → (c && d) = true → (a && b) = true) ∧
    (da + db ≤ 1 → (c && d) = true →
      (a && b) = true ∨ (a && q || p && b) = true) := by
  constructor
  · intro h hcd
    have hcd' : c = true ∧ d = true := by simpa using hcd
    obtain ⟨hc,hd⟩ := hcd'
    simp [ha0 (by omega) hc,hb0 (by omega) hd]
  · intro h hcd
    have hcd' : c = true ∧ d = true := by simpa using hcd
    obtain ⟨hc,hd⟩ := hcd'
    have ha := ha1 (by omega) hc
    have hb := hb1 (by omega) hd
    by_cases hda : da = 0
    · have hat := ha0 hda hc
      rcases hb with hb | hq
      · exact Or.inl (by simp [hat,hb])
      · exact Or.inr (by simp [hat,hq])
    · have hbt := hb0 (by omega) hd
      rcases ha with ha | hp
      · exact Or.inl (by simp [ha,hbt])
      · exact Or.inr (by simp [hp,hbt])

lemma or_step (a b c d p q : Bool) (da db : ℕ)
    (ha0 : da = 0 → c = true → a = true)
    (hb0 : db = 0 → d = true → b = true)
    (ha1 : da ≤ 1 → c = true → a = true ∨ p = true)
    (hb1 : db ≤ 1 → d = true → b = true ∨ q = true) :
    (max da db = 0 → (c || d) = true → (a || b) = true) ∧
    (max da db ≤ 1 → (c || d) = true →
      (a || b) = true ∨ (p || q) = true) := by
  constructor
  · intro h hcd
    have hcd' : c = true ∨ d = true := by simpa using hcd
    rcases hcd' with hc | hd
    · simp [ha0 (by omega) hc]
    · simp [hb0 (by omega) hd]
  · intro h hcd
    have hcd' : c = true ∨ d = true := by simpa using hcd
    rcases hcd' with hc | hd
    · rcases ha1 (by omega) hc with ha | hp
      · exact Or.inl (by simp [ha])
      · exact Or.inr (by simp [hp])
    · rcases hb1 (by omega) hd with hb | hq
      · exact Or.inl (by simp [hb])
      · exact Or.inr (by simp [hq])
lemma invariant (n : ℕ) (C : Circuit) (u : Fin n) (x : Fin n → Bool) (D : ℕ → Bool)
    (hshape : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j)
    (hinput : ∀ v : Fin n, D v.val = decide (u = v))
    (hgate : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = GateOp.and → D (n+j) =
        (V C.gates (List.ofFn x) a && D b || D a && V C.gates (List.ofFn x) b)) ∧
      (g.op = GateOp.or → D (n+j) = (D a || D b))) :
    ∀ i, (dg n u C i = 0 →
      V C.gates (List.ofFn fun v => if u = v then true else x v) i = true →
      V C.gates (List.ofFn x) i = true) ∧
      (dg n u C i ≤ 1 →
      V C.gates (List.ofFn fun v => if u = v then true else x v) i = true →
      V C.gates (List.ofFn x) i = true ∨ D i = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hi : i < n
    · have hd := hinput ⟨i,hi⟩
      by_cases he : u = ⟨i,hi⟩
      · have hiu : i = u.val := by rw [he]
        have hdi : dg n u C i = 1 := by rw [dg_input n u C i hi,if_pos hiu]
        have hD : D i = true := by simpa [he] using hd
        constructor
        · intro hz; omega
        · intro _ _; exact Or.inr hD
      · have hv : V C.gates (List.ofFn fun v => if u = v then true else x v) i =
            V C.gates (List.ofFn x) i := by
          rw [V_input n C _ i hi,V_input n C _ i hi]
          simp [he]
        exact ⟨fun _ ht => hv ▸ ht,fun _ ht => Or.inl (hv ▸ ht)⟩
    · by_cases ho : n + C.gates.length ≤ i
      · have hz : V C.gates (List.ofFn fun v => if u = v then true else x v) i = false :=
          V_out _ _ _ (by simpa using ho)
        exact ⟨fun _ ht => by rw [hz] at ht; contradiction,
          fun _ ht => by rw [hz] at ht; contradiction⟩
      · let j := i-n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have hij : i = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hget : C.gates[j]? = some g := List.getElem?_eq_getElem hj
        obtain ⟨hop,a,b,hin,hne,ha,hb⟩ := hshape j g hget
        have hback : ∀ z ∈ g.inputs, z < n+j := by
          intro z hz
          simp only [hin,List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with rfl | rfl <;> assumption
        have hVa := gate_val_aux n C.gates (List.ofFn x) (by simp) j g hget hback
        have hVb := gate_val_aux n C.gates
          (List.ofFn fun v => if u = v then true else x v) (by simp) j g hget hback
        have hdeg := dg_gate n u C j g hget hback
        have hD := hgate j g a b hget hin
        have hia := ih a (by omega)
        have hib := ih b (by omega)
        rw [hij,hVa,hVb,hdeg]
        rcases hop with hop | hop
        · rw [hD.1 hop]
          simpa [hin,hop,deval,GateOp.eval] using
            and_step (V C.gates (List.ofFn x) a) (V C.gates (List.ofFn x) b)
              (V C.gates (List.ofFn fun v => if u = v then true else x v) a)
              (V C.gates (List.ofFn fun v => if u = v then true else x v) b)
              (D a) (D b) (dg n u C a) (dg n u C b) hia.1 hib.1 hia.2 hib.2
        · rw [hD.2 hop]
          simpa [hin,hop,deval,GateOp.eval] using
            or_step (V C.gates (List.ofFn x) a) (V C.gates (List.ofFn x) b)
              (V C.gates (List.ofFn fun v => if u = v then true else x v) a)
              (V C.gates (List.ofFn fun v => if u = v then true else x v) b)
              (D a) (D b) (dg n u C a) (dg n u C b) hia.1 hib.1 hia.2 hib.2

end PEqualNP.Outside.L_meta_2227_aux

open PEqualNP.Outside.L_meta_2227_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_2227 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ) → Bool) (x4 : ℕ → Bool), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) → (∀ (x6 : Fin (14 : ℕ)), x4 ↑x6 = Decidable.decide (x2 = x6)) → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x1.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x7) = ((x1.wires (List.ofFn x3)).getD x9 Bool.false && x4 x10 || x4 x9 && (x1.wires (List.ofFn x3)).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x7) = (x4 x9 || x4 x10))) → x1.eval (List.ofFn x3) = Bool.false → x1.eval (List.ofFn fun (x9 : Fin (14 : ℕ)) => if x2 = x9 then Bool.true else x3 x9) = Bool.true → x4 x1.output = Bool.false → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} := by
  intro C u x D hshape hinput hgate hfalse htrue hDfalse
  by_contra h
  have hd : dg 14 u C C.output ≤ 1 := by
    change ¬ 2 ≤ dg 14 u C C.output at h
    omega
  have hh := (invariant 14 C u x D hshape hinput hgate C.output).2 hd htrue
  rcases hh with hh | hh
  · change C.eval (List.ofFn x) = true at hh
    rw [hfalse] at hh
    contradiction
  · rw [hDfalse] at hh
    contradiction
