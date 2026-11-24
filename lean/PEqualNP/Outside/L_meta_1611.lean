import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1611

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]; rw [fold_length]; exact h

def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

theorem eval_gate (gates : List Gate) (x : List Bool) (j : ℕ) (hj : j < gates.length)
    (hin : ∀ w ∈ gates[j].inputs, w < x.length + j) :
    Circuit.eval ⟨gates, x.length + j⟩ x
      = gates[j].op.eval (gates[j].inputs.map fun i => Circuit.eval ⟨gates, i⟩ x) := by
  have h := wires_gate ⟨gates, 0⟩ x j hj
  unfold Circuit.eval
  change (Circuit.wires ⟨gates, 0⟩ x).getD (x.length + j) false = _
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  unfold rd
  rw [if_pos (hin i hi)]
  rfl

theorem eval_input (gates : List Gate) (N : ℕ) (f : Fin N → Bool) (w : ℕ) (hw : w < N) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn f) = f ⟨w, hw⟩ := by
  unfold Circuit.eval
  change (Circuit.wires ⟨gates, w⟩ (List.ofFn f)).getD w false = _
  rw [wires_input _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem eval_high (gates : List Gate) (x : List Bool) (w : ℕ)
    (hw : x.length + gates.length ≤ w) : Circuit.eval ⟨gates, w⟩ x = false :=
  fold_getD_ge gates x w hw

theorem gate_val (N : ℕ) (gates : List Gate)
    (hin : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (f : Fin N → Bool) (j : ℕ) (hj : j < gates.length) :
    Circuit.eval ⟨gates, N + j⟩ (List.ofFn f)
      = gates[j].op.eval (gates[j].inputs.map fun i => Circuit.eval ⟨gates, i⟩ (List.ofFn f)) := by
  have h := eval_gate gates (List.ofFn f) j hj (by
    intro w hw
    rw [List.length_ofFn]
    exact hin ⟨j, hj⟩ w hw)
  rw [List.length_ofFn] at h
  exact h

theorem or_val (N : ℕ) (gates : List Gate)
    (hin : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (f : Fin N → Bool) (j : ℕ) (hj : j < gates.length)
    (hor : gates[j].op = GateOp.or) (a b : ℕ) (hab : gates[j].inputs = [a, b]) :
    Circuit.eval ⟨gates, N + j⟩ (List.ofFn f) = true ↔
      (Circuit.eval ⟨gates, a⟩ (List.ofFn f) = true ∨
        Circuit.eval ⟨gates, b⟩ (List.ofFn f) = true) := by
  rw [gate_val N gates hin f j hj, hor, hab]
  simp [GateOp.eval]

def Sw (N : ℕ) (gates : List Gate) (T0 : Finset (Fin N)) (w : ℕ) : Finset (Fin N) :=
  T0.filter (fun y => Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true)

def Cf (N : ℕ) (gates : List Gate) (Z : Finset (Fin N)) (w : ℕ) : Prop :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin N => decide (v ∉ Z))) = false

def Core (N : ℕ) (gates : List Gate) (Z : Finset (Fin N)) (j : ℕ) : Prop :=
  ∃ g, gates[j]? = some g ∧ g.op = GateOp.or ∧ Cf N gates Z (N + j) ∧ ∃ a b, g.inputs = [a, b]

def merge {α : Type} (r : α → α → Prop) (A : Finset α) (x y : α) : Prop :=
  r x y ∨ ((∃ a ∈ A, r x a) ∧ (∃ b ∈ A, r y b))

open Classical in
noncomputable def E (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) : ℕ → Fin N → Fin N → Prop
  | 0 => fun x y => x = y
  | j + 1 => if Core N gates Z j then merge (E N gates T0 Z j) (Sw N gates T0 (N + j))
      else E N gates T0 Z j

theorem E_zero (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) (x y : Fin N) :
    E N gates T0 Z 0 x y ↔ x = y := Iff.rfl

open Classical in
theorem E_succ (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) (j : ℕ) :
    E N gates T0 Z (j + 1) = if Core N gates Z j then merge (E N gates T0 Z j)
      (Sw N gates T0 (N + j)) else E N gates T0 Z j := rfl

theorem merge_equiv {α : Type} {r : α → α → Prop} (hr : Equivalence r) (A : Finset α) :
    Equivalence (merge r A) := by
  constructor
  · intro x; exact Or.inl (hr.refl x)
  · intro x y h
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hr.symm h)
    · exact Or.inr ⟨h2, h1⟩
  · intro x y z h1 h2
    rcases h1 with h1 | ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ <;>
      rcases h2 with h2 | ⟨⟨c, hc, hyc⟩, ⟨d, hd, hzd⟩⟩
    · exact Or.inl (hr.trans h1 h2)
    · exact Or.inr ⟨⟨c, hc, hr.trans h1 hyc⟩, ⟨d, hd, hzd⟩⟩
    · exact Or.inr ⟨⟨a, ha, hxa⟩, ⟨b, hb, hr.trans (hr.symm h2) hyb⟩⟩
    · exact Or.inr ⟨⟨a, ha, hxa⟩, ⟨d, hd, hzd⟩⟩

theorem E_equiv (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) :
    ∀ j, Equivalence (E N gates T0 Z j)
  | 0 => ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩
  | j + 1 => by
    rw [E_succ]
    split_ifs
    · exact merge_equiv (E_equiv N gates T0 Z j) _
    · exact E_equiv N gates T0 Z j

theorem E_succ_of (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) (j : ℕ) (x y : Fin N)
    (h : E N gates T0 Z j x y) : E N gates T0 Z (j + 1) x y := by
  rw [E_succ]
  split_ifs
  · exact Or.inl h
  · exact h

theorem E_mono (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) {j k : ℕ} (hjk : j ≤ k)
    (x y : Fin N) (h : E N gates T0 Z j x y) : E N gates T0 Z k x y := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact E_succ_of N gates T0 Z _ x y ih

theorem E_gen (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) (j : ℕ)
    (hc : Core N gates Z j) (y y' : Fin N) (hy : y ∈ Sw N gates T0 (N + j))
    (hy' : y' ∈ Sw N gates T0 (N + j)) : E N gates T0 Z (j + 1) y y' := by
  rw [E_succ, if_pos hc]
  exact Or.inr ⟨⟨y, hy, (E_equiv N gates T0 Z j).refl y⟩,
    ⟨y', hy', (E_equiv N gates T0 Z j).refl y'⟩⟩

theorem inv (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N))
    (hop : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) :
    ∀ j, j ≤ gates.length → ∀ w, w < N + j → Cf N gates Z w →
      ∀ y ∈ Sw N gates T0 w, ∀ y' ∈ Sw N gates T0 w, E N gates T0 Z j y y' := by
  intro j
  induction j with
  | zero =>
    intro _ w hw _ y hy y' hy'
    simp only [Sw, Finset.mem_filter] at hy hy'
    rw [eval_input gates N _ w (by omega)] at hy hy'
    simp only [decide_eq_true_eq] at hy hy'
    rw [E_zero, ← hy.2, ← hy'.2]
  | succ j ih =>
    intro hj w hw hcf y hy y' hy'
    by_cases hlt : w < N + j
    · exact E_succ_of N gates T0 Z j y y' (ih (by omega) w hlt hcf y hy y' hy')
    · have hwe : w = N + j := by omega
      subst hwe
      have hjl : j < gates.length := by omega
      have hg := hop gates[j] (List.getElem_mem hjl)
      have hinj : ∀ a ∈ gates[j].inputs, a < N + j := fun a ha => hin ⟨j, hjl⟩ a ha
      have child : ∀ a ∈ gates[j].inputs, Cf N gates Z a →
          Sw N gates T0 (N + j) ⊆ Sw N gates T0 a → E N gates T0 Z (j + 1) y y' := by
        intro a ha hca hsub
        exact E_succ_of N gates T0 Z j y y'
          (ih (by omega) a (hinj a ha) hca y (hsub hy) y' (hsub hy'))
      rcases hg with ⟨hand | hor, hlen⟩
      · have hcf' := hcf
        unfold Cf at hcf'
        rw [gate_val N gates hin _ j hjl, hand] at hcf'
        simp only [GateOp.eval] at hcf'
        have hex : ∃ a ∈ gates[j].inputs, Cf N gates Z a := by
          by_contra hne
          push_neg at hne
          have h2 : (gates[j].inputs.map fun i => Circuit.eval ⟨gates, i⟩
              (List.ofFn (fun v : Fin N => decide (v ∉ Z)))).all id = true := by
            rw [List.all_eq_true]
            intro b hb
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
            have := hne a ha
            unfold Cf at this
            simpa using this
          rw [h2] at hcf'
          cases hcf'
        obtain ⟨a, ha, hca⟩ := hex
        apply child a ha hca
        intro z hz
        simp only [Sw, Finset.mem_filter] at hz ⊢
        refine ⟨hz.1, ?_⟩
        have h3 := hz.2
        rw [gate_val N gates hin _ j hjl, hand] at h3
        simp only [GateOp.eval, List.all_eq_true] at h3
        simpa using h3 _ (List.mem_map_of_mem ha)
      · rcases hI : gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · simp only [Sw, Finset.mem_filter] at hy
          rw [gate_val N gates hin _ j hjl, hor, hI] at hy
          simp [GateOp.eval] at hy
        · have ha : a ∈ gates[j].inputs := by rw [hI]; simp
          apply child a ha
          · unfold Cf at hcf ⊢
            rw [gate_val N gates hin _ j hjl, hor, hI] at hcf
            simpa [GateOp.eval] using hcf
          · intro z hz
            simp only [Sw, Finset.mem_filter] at hz ⊢
            refine ⟨hz.1, ?_⟩
            have h3 := hz.2
            rw [gate_val N gates hin _ j hjl, hor, hI] at h3
            simpa [GateOp.eval] using h3
        · have hc : Core N gates Z j :=
            ⟨gates[j], List.getElem?_eq_getElem hjl, hor, hcf, a, b, hI⟩
          exact E_gen N gates T0 Z j hc y y' hy hy'
        · rw [hI] at hlen
          simp at hlen

theorem X_resp (N : ℕ) (gates : List Gate) (T0 Z : Finset (Fin N)) (X : Finset (Fin N)) :
    ∀ j, (∀ i < j, Core N gates Z i → ∀ y ∈ Sw N gates T0 (N + i),
      ∀ y' ∈ Sw N gates T0 (N + i), (y ∈ X ↔ y' ∈ X)) →
    ∀ y y', E N gates T0 Z j y y' → (y ∈ X ↔ y' ∈ X) := by
  intro j
  induction j with
  | zero =>
    intro _ y y' h
    rw [E_zero] at h
    rw [h]
  | succ j ih =>
    intro hres y y' h
    have ih' := ih (fun i hi => hres i (by omega))
    rw [E_succ] at h
    split_ifs at h with hc
    · rcases h with h | ⟨⟨a, ha, hya⟩, ⟨b, hb, hyb⟩⟩
      · exact ih' y y' h
      · rw [ih' y a hya, hres j (by omega) hc a ha b hb, ← ih' y' b hyb]
    · exact ih' y y' h

open Classical in
noncomputable def cls {α : Type} (T : Finset α) (r : α → α → Prop) (y : α) : Finset α := T.filter (r y)

open Classical in
noncomputable def cnt {α : Type} (T : Finset α) (r : α → α → Prop) : ℕ := (T.image (cls T r)).card

theorem mem_cls {α : Type} {T : Finset α} {r : α → α → Prop} {y z : α} :
    z ∈ cls T r y ↔ z ∈ T ∧ r y z := by
  simp only [cls, Finset.mem_filter]

theorem cnt_congr {α : Type} (T : Finset α) (r s : α → α → Prop)
    (h : ∀ x y, r x y ↔ s x y) : cnt T r = cnt T s := by
  have : r = s := funext fun x => funext fun y => propext (h x y)
  rw [this]

theorem cnt_eq_one {α : Type} (T : Finset α) (r : α → α → Prop) (hne : T.Nonempty)
    (h : ∀ y ∈ T, ∀ y' ∈ T, r y y') : cnt T r = 1 := by
  classical
  unfold cnt
  have : T.image (cls T r) = T.image (fun _ => T) := by
    apply Finset.image_congr
    intro y hy
    have hy' : y ∈ T := by simpa using hy
    ext z
    rw [mem_cls]
    constructor
    · exact fun hz => hz.1
    · intro hz; exact ⟨hz, h y hy' z hz⟩
  rw [this, Finset.image_const hne, Finset.card_singleton]

theorem cnt_zero {α : Type} (T : Finset α) : cnt T (fun x y => x = y) = T.card := by
  classical
  unfold cnt
  rw [Finset.card_image_of_injOn]
  intro y hy y' hy' h
  have hyT : y ∈ T := by simpa using hy
  have h1 : y ∈ cls T (fun x y => x = y) y := mem_cls.mpr ⟨hyT, rfl⟩
  have h2 : cls T (fun x y => x = y) y = cls T (fun x y => x = y) y' := h
  rw [h2, mem_cls] at h1
  exact h1.2.symm

theorem cnt_drop {α : Type} (T : Finset α) (r : α → α → Prop) (hr : Equivalence r)
    (p q : α) (hp : p ∈ T) (hq : q ∈ T) (hpq : ¬ r p q) :
    cnt T (fun x y => r x y ∨ ((r x p ∨ r x q) ∧ (r y p ∨ r y q))) + 1 = cnt T r := by
  classical
  unfold cnt
  set r' : α → α → Prop := fun x y => r x y ∨ ((r x p ∨ r x q) ∧ (r y p ∨ r y q)) with hr'
  set P := T.image (cls T r) with hP
  set U := cls T r p ∪ cls T r q with hU
  have F1 : ∀ y, (r y p ∨ r y q) → cls T r' y = U := by
    intro y hy
    ext z
    rw [mem_cls, hU, Finset.mem_union, mem_cls, mem_cls]
    constructor
    · rintro ⟨hz, h | ⟨_, h2⟩⟩
      · rcases hy with hy | hy
        · exact Or.inl ⟨hz, hr.trans (hr.symm hy) h⟩
        · exact Or.inr ⟨hz, hr.trans (hr.symm hy) h⟩
      · rcases h2 with h2 | h2
        · exact Or.inl ⟨hz, hr.symm h2⟩
        · exact Or.inr ⟨hz, hr.symm h2⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, Or.inr ⟨hy, Or.inl (hr.symm h)⟩⟩
      · exact ⟨hz, Or.inr ⟨hy, Or.inr (hr.symm h)⟩⟩
  have F2 : ∀ y, ¬ (r y p ∨ r y q) → cls T r' y = cls T r y := by
    intro y hy
    ext z
    rw [mem_cls, mem_cls]
    constructor
    · rintro ⟨hz, h | ⟨h1, _⟩⟩
      · exact ⟨hz, h⟩
      · exact absurd h1 hy
    · rintro ⟨hz, h⟩
      exact ⟨hz, Or.inl h⟩
  have F3 : ∀ y t, r y t → cls T r y = cls T r t := by
    intro y t h
    ext z
    rw [mem_cls, mem_cls]
    constructor
    · rintro ⟨hz, h2⟩; exact ⟨hz, hr.trans (hr.symm h) h2⟩
    · rintro ⟨hz, h2⟩; exact ⟨hz, hr.trans h h2⟩
  have F5 : ∀ y t, t ∈ T → cls T r y = cls T r t → r y t := by
    intro y t ht h
    have : t ∈ cls T r t := mem_cls.mpr ⟨ht, hr.refl t⟩
    rw [← h, mem_cls] at this
    exact this.2
  have F4 : cls T r p ≠ cls T r q := by
    intro h
    exact hpq (hr.symm (F5 q p hp h.symm))
  have hpP : cls T r p ∈ P := Finset.mem_image_of_mem _ hp
  have hqP : cls T r q ∈ P.erase (cls T r p) :=
    Finset.mem_erase.mpr ⟨fun h => F4 h.symm, Finset.mem_image_of_mem _ hq⟩
  have himg : T.image (cls T r') = insert U ((P.erase (cls T r p)).erase (cls T r q)) := by
    ext Z
    rw [Finset.mem_image, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, hP,
      Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases hm : r y p ∨ r y q
      · exact Or.inl (F1 y hm)
      · right
        rw [F2 y hm]
        refine ⟨fun h => hm (Or.inr (F5 y q hq h)), fun h => hm (Or.inl (F5 y p hp h)),
          y, hy, rfl⟩
    · rintro (rfl | ⟨hZq, hZp, y, hy, rfl⟩)
      · exact ⟨p, hp, F1 p (Or.inl (hr.refl p))⟩
      · have hm : ¬ (r y p ∨ r y q) := by
          rintro (h | h)
          · exact hZp (F3 y p h)
          · exact hZq (F3 y q h)
        exact ⟨y, hy, F2 y hm⟩
  have hUn : U ∉ (P.erase (cls T r p)).erase (cls T r q) := by
    intro h
    rw [Finset.mem_erase, Finset.mem_erase, hP, Finset.mem_image] at h
    obtain ⟨hUq, hUp, y, _, hyU⟩ := h
    have hpU : p ∈ U := by
      rw [hU, Finset.mem_union]
      exact Or.inl (mem_cls.mpr ⟨hp, hr.refl p⟩)
    rw [← hyU, mem_cls] at hpU
    exact hUp (hyU.symm.trans (F3 y p hpU.2))
  rw [himg, Finset.card_insert_of_notMem hUn, Finset.card_erase_add_one hqP,
    Finset.card_erase_add_one hpP]

end PEqualNP.Outside.L_meta_1611

theorem PEqualNP.Outside.L_meta_1611 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false → (∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = true) →
    ∀ K : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ K ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (g : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ T0, ∃ r' ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = r))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = r'))) = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ T0, ∀ y' ∈ T0,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X)))) →
      K.card = m - 1 ∧ ∀ g ∈ K, ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧
        ∃ x ∈ T0, ∃ y ∈ T0, x ≠ y ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true := by
  intro q m N L i0 T0 _ hm _ _ _ _ _ _ hcard gates o hop hin hout hT K hK
  classical
  refine ⟨?_, ?_⟩
  · have hne : T0.Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    have ho : o < N + gates.length := by
      by_contra hlt
      obtain ⟨x, hx⟩ := hne
      have h1 := hT x hx
      rw [PEqualNP.Outside.L_meta_1611.eval_high gates _ o (by rw [List.length_ofFn]; omega)] at h1
      cases h1
    have hall : ∀ y ∈ T0, ∀ y' ∈ T0,
        PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) gates.length y y' := by
      intro y hy y' hy'
      exact PEqualNP.Outside.L_meta_1611.inv N gates T0 (L i0) hop hin gates.length le_rfl o ho
        hout y (Finset.mem_filter.mpr ⟨hy, hT y hy⟩) y' (Finset.mem_filter.mpr ⟨hy', hT y' hy'⟩)
    have hcore_of_K : ∀ (j : ℕ) (hj : j < gates.length), (⟨j, hj⟩ : Fin gates.length) ∈ K →
        PEqualNP.Outside.L_meta_1611.Core N gates (L i0) j := by
      intro j hj hk
      obtain ⟨hor, hcf, w1, w2, hw, _⟩ := (hK ⟨j, hj⟩).mp hk
      exact ⟨gates[j], List.getElem?_eq_getElem hj, hor, hcf, w1, w2, hw⟩
    have hresp : ∀ (j : ℕ) (hj : j < gates.length) (X : Finset (Fin N)),
        (∀ i : Fin gates.length, i < ⟨j, hj⟩ → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ T0, ∀ y' ∈ T0,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y))) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (fun v : Fin N => decide (v = y'))) = true) → (y ∈ X ↔ y' ∈ X)) →
        ∀ y y', PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j y y' → (y ∈ X ↔ y' ∈ X) := by
      intro j hj X hX
      apply PEqualNP.Outside.L_meta_1611.X_resp N gates T0 (L i0) X j
      intro i hij hci y hy y' hy'
      obtain ⟨g', hg', hor', hcf', a, b, hab⟩ := hci
      have hil : i < gates.length := by omega
      have hge : gates[i] = g' := by
        rw [List.getElem?_eq_getElem hil] at hg'
        exact Option.some.inj hg'
      subst hge
      simp only [PEqualNP.Outside.L_meta_1611.Sw, Finset.mem_filter] at hy hy'
      rw [PEqualNP.Outside.L_meta_1611.or_val N gates hin _ i hil hor' a b hab] at hy hy'
      exact hX ⟨i, hil⟩ (Fin.mk_lt_mk.mpr hij) hor' hcf' a b hab y hy.1 y' hy'.1 hy.2 hy'.2
    have hstep : ∀ (j : ℕ) (hj : j < gates.length),
        PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) (j + 1))
          + (if (⟨j, hj⟩ : Fin gates.length) ∈ K then 1 else 0)
          = PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j) := by
      intro j hj
      by_cases hc : PEqualNP.Outside.L_meta_1611.Core N gates (L i0) j
      · have hc0 := hc
        obtain ⟨g, hg, hor, hcf, a, b, hab⟩ := hc0
        have hge : gates[j] = g := by
          rw [List.getElem?_eq_getElem hj] at hg
          exact Option.some.inj hg
        subst hge
        have hSw : ∀ z, z ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 (N + j) ↔
            z ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 a ∨
              z ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 b := by
          intro z
          simp only [PEqualNP.Outside.L_meta_1611.Sw, Finset.mem_filter]
          rw [PEqualNP.Outside.L_meta_1611.or_val N gates hin _ j hj hor a b hab]
          tauto
        have hcfab : PEqualNP.Outside.L_meta_1611.Cf N gates (L i0) a ∧
            PEqualNP.Outside.L_meta_1611.Cf N gates (L i0) b := by
          have h1 := hcf
          unfold PEqualNP.Outside.L_meta_1611.Cf at h1 ⊢
          have h2 : ¬ (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + j⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true) := by
            rw [h1]; simp
          rw [PEqualNP.Outside.L_meta_1611.or_val N gates hin _ j hj hor a b hab] at h2
          push_neg at h2
          simpa using h2
        have hab_in : a ∈ gates[j].inputs ∧ b ∈ gates[j].inputs := by rw [hab]; simp
        have ha_lt : a < N + j := hin ⟨j, hj⟩ a hab_in.1
        have hb_lt : b < N + j := hin ⟨j, hj⟩ b hab_in.2
        have hia := PEqualNP.Outside.L_meta_1611.inv N gates T0 (L i0) hop hin j (by omega) a ha_lt hcfab.1
        have hib := PEqualNP.Outside.L_meta_1611.inv N gates T0 (L i0) hop hin j (by omega) b hb_lt hcfab.2
        have hEq := PEqualNP.Outside.L_meta_1611.E_equiv N gates T0 (L i0) j
        rw [PEqualNP.Outside.L_meta_1611.E_succ, if_pos hc]
        by_cases hk : (⟨j, hj⟩ : Fin gates.length) ∈ K
        · rw [if_pos hk]
          obtain ⟨_, _, w1, w2, hw, p, hp, p', hp', h1, h2, X, hpX, hp'X, hX⟩ := (hK ⟨j, hj⟩).mp hk
          have hw' : gates[j].inputs = [w1, w2] := hw
          rw [hab] at hw'
          simp only [List.cons.injEq, and_true] at hw'
          obtain ⟨rfl, rfl⟩ := hw'
          have hnot : ¬ PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j p p' := by
            intro h
            have := (hresp j hj X hX p p' h).mp hpX
            exact hp'X this
          have hpa : p ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 a := Finset.mem_filter.mpr ⟨hp, h1⟩
          have hpb : p' ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 b := Finset.mem_filter.mpr ⟨hp', h2⟩
          rw [← PEqualNP.Outside.L_meta_1611.cnt_drop T0 _ hEq p p' hp hp' hnot]
          congr 1
          apply PEqualNP.Outside.L_meta_1611.cnt_congr
          intro x y
          have key : ∀ t, (∃ c ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 (N + j),
              PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j t c) ↔
              (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j t p ∨
                PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j t p') := by
            intro t
            constructor
            · rintro ⟨c, hc', htc⟩
              rcases (hSw c).mp hc' with hca | hcb
              · exact Or.inl (hEq.trans htc (hia c hca p hpa))
              · exact Or.inr (hEq.trans htc (hib c hcb p' hpb))
            · rintro (h | h)
              · exact ⟨p, (hSw p).mpr (Or.inl hpa), h⟩
              · exact ⟨p', (hSw p').mpr (Or.inr hpb), h⟩
          unfold PEqualNP.Outside.L_meta_1611.merge
          rw [key x, key y]
        · rw [if_neg hk, Nat.add_zero]
          have hjoin : ∀ c ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 a,
              ∀ d ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 b,
              PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j c d := by
            intro c hc' d hd
            by_contra hn
            apply hk
            have hc2 := Finset.mem_filter.mp hc'
            have hd2 := Finset.mem_filter.mp hd
            refine (hK ⟨j, hj⟩).mpr ⟨hor, hcf, a, b, hab, c, hc2.1, d, hd2.1, hc2.2, hd2.2,
              Finset.univ.filter (fun z => PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j c z),
              ?_, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hEq.refl c
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hn
            · intro i hij hor' hcf' a' b' hab' y hy y' hy' h1 h2
              have hil : i.val < gates.length := i.isLt
              have hci : PEqualNP.Outside.L_meta_1611.Core N gates (L i0) i.val :=
                ⟨gates[i.val], List.getElem?_eq_getElem hil, hor', hcf', a', b', hab'⟩
              have hyS : y ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 (N + i.val) := by
                refine Finset.mem_filter.mpr ⟨hy, ?_⟩
                exact (PEqualNP.Outside.L_meta_1611.or_val N gates hin _ i.val hil hor' a' b' hab').mpr h1
              have hyS' : y' ∈ PEqualNP.Outside.L_meta_1611.Sw N gates T0 (N + i.val) := by
                refine Finset.mem_filter.mpr ⟨hy', ?_⟩
                exact (PEqualNP.Outside.L_meta_1611.or_val N gates hin _ i.val hil hor' a' b' hab').mpr h2
              have hyy := PEqualNP.Outside.L_meta_1611.E_gen N gates T0 (L i0) i.val hci y y' hyS hyS'
              have hlt : i.val + 1 ≤ j := by
                have := Fin.lt_def.mp hij
                simp at this
                omega
              have hyy' := PEqualNP.Outside.L_meta_1611.E_mono N gates T0 (L i0) hlt y y' hyy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨fun h => hEq.trans h hyy', fun h => hEq.trans h (hEq.symm hyy')⟩
          apply PEqualNP.Outside.L_meta_1611.cnt_congr
          intro x y
          unfold PEqualNP.Outside.L_meta_1611.merge
          constructor
          · rintro (h | ⟨⟨c, hc', hxc⟩, ⟨d, hd, hyd⟩⟩)
            · exact h
            · have hcd : PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j c d := by
                rcases (hSw c).mp hc' with hca | hcb <;> rcases (hSw d).mp hd with hda | hdb
                · exact hia c hca d hda
                · exact hjoin c hca d hdb
                · exact hEq.symm (hjoin d hda c hcb)
                · exact hib c hcb d hdb
              exact hEq.trans hxc (hEq.trans hcd (hEq.symm hyd))
          · exact fun h => Or.inl h
      · have hk : (⟨j, hj⟩ : Fin gates.length) ∉ K := fun hk => hc (hcore_of_K j hj hk)
        rw [if_neg hk, Nat.add_zero, PEqualNP.Outside.L_meta_1611.E_succ, if_neg hc]
    have htel : ∀ j, j ≤ gates.length →
        PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) 0)
          = PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) j)
            + (K.filter (fun g => g.val < j)).card := by
      intro j
      induction j with
      | zero =>
        intro _
        have : K.filter (fun g : Fin gates.length => g.val < 0) = ∅ := by
          ext g; simp
        rw [this, Finset.card_empty, Nat.add_zero]
      | succ j ih =>
        intro hj1
        have hj : j < gates.length := by omega
        rw [ih (by omega), ← hstep j hj]
        by_cases hk : (⟨j, hj⟩ : Fin gates.length) ∈ K
        · rw [if_pos hk]
          have hf : K.filter (fun g : Fin gates.length => g.val < j + 1) =
              insert ⟨j, hj⟩ (K.filter (fun g : Fin gates.length => g.val < j)) := by
            ext g
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hg, hlt⟩
              by_cases he : g.val = j
              · left; exact Fin.ext he
              · right; exact ⟨hg, by omega⟩
            · rintro (rfl | ⟨hg, hlt⟩)
              · exact ⟨hk, by simp⟩
              · exact ⟨hg, by omega⟩
          have hnm : (⟨j, hj⟩ : Fin gates.length) ∉ K.filter (fun g : Fin gates.length => g.val < j) := by
            simp
          rw [hf, Finset.card_insert_of_notMem hnm]
          omega
        · rw [if_neg hk]
          have hf : K.filter (fun g : Fin gates.length => g.val < j + 1) =
              K.filter (fun g : Fin gates.length => g.val < j) := by
            apply Finset.filter_congr
            intro g hg
            constructor
            · intro hlt
              by_cases he : g.val = j
              · have hgj : g = (⟨j, hj⟩ : Fin gates.length) := Fin.ext he
                exact absurd (hgj ▸ hg) hk
              · omega
            · intro hlt; omega
          rw [hf]
          omega
    have h0 := htel gates.length le_rfl
    have hfK : K.filter (fun g : Fin gates.length => g.val < gates.length) = K := by
      apply Finset.filter_true_of_mem
      intro g _
      exact g.isLt
    rw [hfK] at h0
    have hc0 : PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) 0) = m := by
      rw [← hcard]
      exact PEqualNP.Outside.L_meta_1611.cnt_zero T0
    have hc1 : PEqualNP.Outside.L_meta_1611.cnt T0 (PEqualNP.Outside.L_meta_1611.E N gates T0 (L i0) gates.length) = 1 :=
      PEqualNP.Outside.L_meta_1611.cnt_eq_one T0 _ hne hall
    omega
  · intro g hg
    obtain ⟨_, _, w1, w2, hw, r, hr, r', hr', h1, h2, X, hrX, hr'X, _⟩ := (hK g).mp hg
    refine ⟨w1, w2, hw, r, hr, r', hr', ?_, h1, h2⟩
    intro he
    rw [he] at hrX
    exact hr'X hrX
