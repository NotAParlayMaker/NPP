import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13651

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Binary gates with free negations, runs, their normal form and the count of dropped inputs follow L_meta_10886 (k-sandhu,
-- Apache-2.0); the base point, the restriction to a core by sample points and the small search are ours.

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

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

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

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

abbrev BF := (Fin 6 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 6) : BF := fun x => x i

def zF : BF := fun _ => false

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_zero (k : Fin 4) : gN k 0 0 = 0 := by
  fin_cases k <;> simp [gN, gM]

theorem gN_swap (k : Fin 4) (a b : ℕ) : ∃ k', gN k a b = gN k' b a := by
  fin_cases k
  · exact ⟨0, by simp [gN, gM, Nat.land_comm]⟩
  · exact ⟨1, by simp [gN, gM, Nat.lor_comm]⟩
  · exact ⟨3, by simp [gN, gM, Nat.land_comm]⟩
  · exact ⟨2, by simp [gN, gM, Nat.land_comm]⟩

def enc (w : BF) : List (Fin 6 → Bool) → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit (w : BF) : ∀ (l : List (Fin 6 → Bool)) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 6 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h, gF]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

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

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 6 → Bool) :
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

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 6 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 6 → Bool) : ∀ (gs : List Gate) (W : List BF),
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

def MonoA : Fin 4 → Prop := fun k => k.val < 2

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

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

def assignment (a : ℕ) (i : Fin 6) : Bool := a.testBit i.val

def zP : Fin 6 → Bool := assignment 2

def ori (w : BF) : BF := fun x => xor (w x) (w zP)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a zP <;> rfl

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a zP <;> cases hv : b zP
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a zP <;> cases hv : b zP
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

def src (i : Fin 6) : BF := ori (var i)

def tb : ℕ := 17215830820328761856

def fN (x : Fin 6 → Bool) : Bool :=
  tb.testBit (cond (x 0) 1 0 + cond (x 1) 2 0 + cond (x 2) 4 0 + cond (x 3) 8 0 + cond (x 4) 16 0 + cond (x 5) 32 0)

theorem inputVector (x : Fin 6 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
  funext i
  fin_cases i <;> rfl

theorem equalSix {f g : (Fin 6 → Bool) → Bool}
    (h : ∀ a b c d e v : Bool, f ![a, b, c, d, e, v] = g ![a, b, c, d, e, v]) : f = g := by
  funext x
  rw [inputVector x]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def dp (i : Fin 6) : ℕ := ([8, 12, 10, 1, 1, 1] : List ℕ).getD i.val 0

theorem dp_ne : ∀ i : Fin 6, fN (assignment (dp i)) ≠ fN (assignment (dp i ^^^ 2 ^ i.val)) := by
  decide +kernel

theorem dp_same : ∀ i j : Fin 6, j ≠ i → assignment (dp i) j = assignment (dp i ^^^ 2 ^ i.val) j := by
  decide +kernel

theorem src_mem {C : Fin 4 → BF → BF → Prop} {t : ℕ} {ws : List BF} (h : TR gF C [ori fN] t ws)
    (hs : ∀ w ∈ ws, ∃ i, w = src i) (i : Fin 6) : src i ∈ ws := by
  by_contra hmiss
  have hd := TRF_det h (assignment (dp i)) (assignment (dp i ^^^ 2 ^ i.val)) (by
    intro w hw
    obtain ⟨j, rfl⟩ := hs w hw
    have hj : j ≠ i := fun e => hmiss (e ▸ hw)
    simp only [src, ori, var, dp_same i j hj]) (ori fN) (by simp)
  apply dp_ne i
  simpa [ori] using hd

theorem src_inj : Function.Injective src := by
  intro i j h
  by_contra hne
  have e := congrFun h (fun k => if k = i then !zP k else zP k)
  simp only [src, ori, var] at e
  rw [if_pos trivial, if_neg (fun h => hne h.symm)] at e
  revert e
  cases zP i <;> cases zP j <;> decide

theorem src_nodup : (List.ofFn src).Nodup := List.nodup_ofFn.2 src_inj

theorem src_len {C : Fin 4 → BF → BF → Prop} {t : ℕ} {ws : List BF} (h : TR gF C [ori fN] t ws)
    (hs : ∀ w ∈ ws, ∃ i, w = src i) : List.Subperm (List.ofFn src) ws := by
  apply src_nodup.subperm
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
  exact src_mem h hs i

def pts : List (Fin 6 → Bool) := ([2, 3, 10, 11, 18, 19, 26, 27] : List ℕ).map assignment

def dc (ws : List BF) : ℕ := ws.countP fun w => decide (enc w pts = 0)

theorem dc_cons (a : BF) (l : List BF) : dc (a :: l) = dc l + if enc a pts = 0 then 1 else 0 := by
  simp [dc, List.countP_cons]

theorem dc_rep (n : ℕ) (g : BF) (r : List BF) :
    dc (List.replicate n g ++ r) = (if enc g pts = 0 then n else 0) + dc r := by
  simp only [dc, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {F : BF} (hF : enc F pts ≠ 0) {s : ℕ} {ws : List BF}
    (h : TR gF (fun _ _ _ => True) [F] s ws) :
    dc ws ≤ s ∧ ∀ S : ℕ → Prop, (∀ w ∈ ws, enc w pts ≠ 0 → S (enc w pts)) →
      UC gN (fun _ => True) (s - dc ws) S (enc F pts) := by
  refine TR.ind (P := fun s ws => dc ws ≤ s ∧ ∀ S : ℕ → Prop,
    (∀ w ∈ ws, enc w pts ≠ 0 → S (enc w pts)) → UC gN (fun _ => True) (s - dc ws) S (enc F pts)) h ?_ ?_ ?_
  · have h0 : dc [F] = 0 := by simp [dc, hF]
    refine ⟨by rw [h0], fun S hS => ?_⟩
    rw [h0]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dc zs = dc xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u _ _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : enc (gF k a b) pts = gN k (enc a pts) (enc b pts) := enc_gF k a b pts
    rw [dc_rep] at ih1 ih2
    rw [dc_cons, dc_cons]
    have hmem : ∀ (S : ℕ → Prop), (∀ w ∈ a :: b :: r, enc w pts ≠ 0 → S (enc w pts)) →
        ∀ w ∈ r, enc w pts ≠ 0 → S (enc w pts) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : enc a pts = 0 <;> by_cases hb : enc b pts = 0
    · have hgz : enc (gF k a b) pts = 0 := by rw [hg, ha, hb, gN_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : enc (gF k a b) pts = 0
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : enc (gF k a b) pts = enc b pts := by
          rcases gN_zero_left k (enc b pts) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : enc (gF k a b) pts = 0
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : enc (gF k a b) pts = enc a pts := by
          rcases gN_zero_right k (enc a pts) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : enc (gF k a b) pts = 0
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gN k (enc a pts) (enc b pts) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (enc a pts) (enc b pts) trivial (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def ucB : ℕ → List ℕ → ℕ → Bool
  | 0, l, f => l.any fun a => a == f
  | t + 1, l, f => ucB t l f ||
      l.any fun a => l.any fun b => Nat.ble a b && (ucB t (gM 0 a b :: l) f || (ucB t (gM 1 a b :: l) f ||
        (ucB t (gM 2 a b :: l) f || ucB t (gM 3 a b :: l) f)))

theorem ucB_gate {t : ℕ} {l : List ℕ} {f a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≤ b) (k : Fin 4)
    (h : ucB t (gN k a b :: l) f = true) : ucB (t + 1) l f = true := by
  have hk : (ucB t (gM 0 a b :: l) f || (ucB t (gM 1 a b :: l) f ||
        (ucB t (gM 2 a b :: l) f || ucB t (gM 3 a b :: l) f))) = true := by
    fin_cases k <;> simp_all [gN, gM]
  simp only [ucB, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
  refine Or.inr ⟨a, ha, b, hb, (by rw [Nat.ble_eq]; exact hab), ?_⟩
  simpa only [Bool.or_eq_true] using hk

theorem ucB_true : ∀ (t : ℕ) (l : List ℕ) (f : ℕ), UC gN (fun _ => True) t (fun w => w ∈ l) f → ucB t l f = true
  | 0, l, f, h => by
    simp only [ucB, List.any_eq_true]
    exact ⟨f, h, by simp⟩
  | t + 1, l, f, h => by
    rcases h with h | ⟨k, a, b, _, ha, hb, h⟩
    · simp only [ucB, Bool.or_eq_true]
      exact Or.inl (ucB_true t l f h)
    · rcases Nat.le_total a b with hab | hab
      · refine ucB_gate ha hb hab k (ucB_true t _ f (UC_monoS _ _ t _ _ f ?_ h))
        intro w hw; simpa using hw
      · obtain ⟨k', hk'⟩ := gN_swap k a b
        refine ucB_gate hb ha hab k' (ucB_true t _ f (UC_monoS _ _ t _ _ f ?_ h))
        intro w hw; rw [← hk']; simpa using hw

theorem core_false : ucB 2 [170, 204, 240] 232 = false := by decide +kernel

theorem enc_f : enc (ori fN) pts = 232 := by decide +kernel

theorem enc_src : ∀ i : Fin 6, enc (src i) pts = 0 ∨ enc (src i) pts ∈ ([170, 204, 240] : List ℕ) := by decide +kernel

theorem dc_src : dc (List.ofFn src) = 3 := by decide +kernel

theorem run_long {t : ℕ} {ws : List BF} (h : TR gF (strictC gF zF (fun _ => True) (fun _ => True)) [ori fN] t ws)
    (hs : ∀ w ∈ ws, ∃ i, w = src i) : 6 ≤ t := by
  by_contra! hlt
  have hp := src_len h hs
  have hd : 3 ≤ dc ws := by rw [← dc_src]; exact hp.countP_le _
  have hr := (pot_dead (by rw [enc_f]; decide) (TR.monoC (C' := fun _ _ _ => True) (fun _ _ _ _ => trivial) h)).2
    (fun w => w ∈ ([170, 204, 240] : List ℕ)) (by
      intro w hw hwz
      obtain ⟨i, rfl⟩ := hs w hw
      exact (enc_src i).resolve_left hwz)
  rw [enc_f] at hr
  have hb := ucB_true 2 _ _ (UC_le (show t - dc ws ≤ 2 by omega) hr)
  rw [core_false] at hb
  exact Bool.noConfusion hb

theorem fN_ne : ori fN ≠ zF := by
  intro e
  have h := src_mem (C := fun _ _ _ => True) (t := 0) (ws := [ori fN])
  have c1 := congrFun e (assignment (dp 0))
  have c2 := congrFun e (assignment (dp 0 ^^^ 2 ^ (0 : Fin 6).val))
  simp only [ori, zF] at c1 c2
  apply dp_ne 0
  have := c1.trans c2.symm
  simpa using this

theorem lower (gates : List Gate) (o : ℕ) (legal : GOK gates) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = fN x) : 7 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = fN := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (fun w => ∃ i, w = src i) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, rfl⟩) o
  rw [hg] at start
  rcases start with e | base
  · exact absurd e fN_ne
  obtain ⟨t, ht, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    _ _ _ (fun _ _ => trivial) fN_ne base
  have hb := run_long run fun w hw => (hws w hw).1
  have extra := countBinary_lt gates hnot
  omega

def witness : List Gate := [⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩]

theorem witnessBasis : ∀ g ∈ witness, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witnessCorrect : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness, 12⟩ (List.ofFn x) = fN x := by
  have h : (fun x : Fin 6 → Bool => Circuit.eval ⟨witness, 12⟩ (List.ofFn x)) = fN := equalSix (by decide +kernel)
  exact fun x => congrFun h x

theorem table_eq : (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) = fN :=
  equalSix (by decide +kernel)

end PEqualNP.Outside.L_meta_13651

open PEqualNP.Outside.L_meta_13651 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_13651 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008372736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hF, hs, hC⟩
  have hT : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = fN x := fun x => (hC x).trans (congrFun table_eq x)
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · have large := lower C.gates C.output hF hnot hT
    have hw : witness.length = 7 := rfl
    have hsz : C.size = C.gates.length := rfl
    refine ⟨⟨witness, 12⟩, witnessBasis, ?_, fun x => (witnessCorrect x).trans (congrFun table_eq x).symm⟩
    change witness.length ≤ s
    omega
  · refine ⟨C, ?_, hs, hC⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := hF g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hnot
