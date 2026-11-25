import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11573

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

end Generic

abbrev BF := (Fin 7 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 7) : BF := fun x => x i

def zF : BF := fun _ => false

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem var_inj {i j : Fin 7} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 7 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def MonoA : Fin 4 → Prop := fun k => k.val < 2

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 7 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 7 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [if_neg (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 7)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

def graph (x : Fin 7 → Bool) : Bool :=
  ((x 0 || x 1 || x 2) && x 5) || ((x 0 || x 1 || x 3 || x 4) && x 6)

def voisin : Fin 7 → Fin 7 := ![5, 5, 5, 6, 6, 0, 0]

theorem sensible : ∀ i : Fin 7, graph (singleInput (voisin i)) ≠
    graph (Function.update (singleInput (voisin i)) i true) := by decide

theorem nonNul : graph ≠ zF := by
  intro h
  exact (by decide : graph (pairInput 0 5) ≠ false) (congrFun h (pairInput 0 5))

theorem borne (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x) :
    7 ≤ gates.length := by
  classical
  have hg : (wiresF gates (List.ofFn var)).getD o zF = graph := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (rfl : graph (fun _ => false) = false)] at start
  rcases start with e | base
  · exact (nonNul e).elim
  obtain ⟨t, ht, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    _ _ _ (fun _ _ => trivial) nonNul base
  have toutes (i : Fin 7) : var i ∈ ws := by
    by_contra hmiss
    apply sensible i
    apply TRF_det run _ _ _ graph (by simp)
    intro w hw
    obtain ⟨j, _, rfl⟩ := (hws w hw).1
    have hji : j ≠ i := fun e => hmiss (e ▸ hw)
    change singleInput (voisin i) j = Function.update (singleInput (voisin i)) i true j
    rw [Function.update_of_ne hji]
  have incl : (Finset.univ.image var) ⊆ ws.toFinset := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_toFinset.mpr (toutes i)
  have hc := (Finset.card_le_card incl).trans (List.toFinset_card_le ws)
  rw [Finset.card_image_of_injective _ (fun _ _ e => var_inj e)] at hc
  change 7 ≤ ws.length at hc
  have hlen := TR.len run
  change ws.length ≤ t + 1 at hlen
  have hextra := countBinary_lt gates hnot
  omega

def temoin : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [7, 9]⟩,
   ⟨.and, [8, 5]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [11, 12]⟩]

theorem baseTemoin : ∀ g ∈ temoin, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [temoin, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem calcTemoin : ∀ x : Fin 7 → Bool, Circuit.eval ⟨temoin, 13⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
theorem specGraphe : ∀ x : Fin 7 → Bool, graph x = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_11573

open PEqualNP.Outside.L_meta_11573 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_11573 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have h := borne gates o legal hnot (fun x => (computes x).trans (specGraphe x).symm)
    exact ⟨temoin, 13, baseTemoin, h, fun x => (calcTemoin x).trans (specGraphe x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hl⟩ := legal g hg
    refine ⟨?_, hl⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
