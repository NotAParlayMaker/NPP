import PEqualNP.Defs

namespace PEqualNP.Outside.V_meta_14056__k7

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word16 := BitVec 16

def Allowed (op : GateOp) : Prop :=
  op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not

def Known (w : List Word16) (a : Word16) : Prop :=
  a = 0 ∨ a = BitVec.allOnes 16 ∨ a ∈ w

def wordOp (op : GateOp) (as : List Word16) : Word16 :=
  match op, as with
  | .and, [] => BitVec.allOnes 16
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes 16
  | .not, a :: _ => ~~~a
  | _, _ => 0

def wordStep (ws : List Word16) (g : Gate) : Word16 :=
  wordOp g.op (g.inputs.map fun i => ws.getD i 0)

def wordRun (ws : List Word16) : List Gate → List Word16
  | [] => ws
  | g :: gs => wordRun (ws ++ [wordStep ws g]) gs

def bits (ws : List Word16) (j : ℕ) : List Bool :=
  ws.map fun w => w.getLsbD j

lemma bits_get (ws : List Word16) (i j : ℕ) :
    (bits ws j).getD i false = (ws.getD i 0).getLsbD j := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : ws[i]? with
  | none => simp
  | some w => simp

lemma wordOp_bits (op : GateOp) (as : List Word16) (j : ℕ) (hj : j < 16)
    (h : Allowed op) (hlen : as.length ≤ 2) :
    (wordOp op as).getLsbD j = op.eval (bits as j) := by
  have hz : (0 : Word16).getLsbD j = false := BitVec.getLsbD_zero
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      simp only [wordOp, GateOp.eval, bits, List.map_nil, List.all_nil,
        List.any_nil, List.headD_nil, BitVec.getLsbD_allOnes, hj, decide_true, Bool.not_false, hz]
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and, id_eq]
      | cons b rest2 =>
        cases rest2 with
        | nil =>
          simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons,
            Bool.and_true, Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or,
            BitVec.getLsbD_not, hj, decide_true, Bool.true_and, id_eq]
        | cons c rest3 => simp at hlen

lemma wordStep_bits (ws : List Word16) (g : Gate) (j : ℕ) (hj : j < 16)
    (h : Allowed g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep ws g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits ws j).getD i false) := by
  unfold wordStep
  rw [wordOp_bits g.op _ j hj h (by simpa using hlen)]
  congr 1
  simp only [bits, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simpa [bits] using (bits_get ws i j).symm

lemma wordRun_bits (ws : List Word16) (gs : List Gate) (j : ℕ) (hj : j < 16)
    (hok : ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2) :
    bits (wordRun ws gs) j = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (bits ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := hok g List.mem_cons_self
    have hrest : ∀ g' ∈ gs, Allowed g'.op ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hok g' (List.mem_cons_of_mem g hg')
    simp only [wordRun, List.foldl_cons]
    rw [ih (ws ++ [wordStep ws g]) hrest]
    congr 1
    simp only [bits, List.map_append, List.map_cons, List.map_nil]
    rw [wordStep_bits ws g j hj hg.1 hg.2]
    rfl

def Next (w : List Word16) (z : Word16) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨ (∃ a ∈ w, ∃ b ∈ w, z = a &&& b ∨ z = a ||| b)

def Reach : List Word16 → ℕ → Word16 → Prop
  | w, 0, t => t ∈ w
  | w, k + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 16 ∧ Next w z ∧ Reach (z :: w) k t

lemma reach_mono {w : List Word16} {k : ℕ} {t : Word16} (h : Reach w k t) : Reach w (k + 1) t := by
  induction k generalizing w with
  | zero => exact Or.inl h
  | succ k ih =>
    rcases h with ht | ⟨z, h1, h2, h3, h4, hr⟩
    · exact Or.inl ht
    · exact Or.inr ⟨z, h1, h2, h3, h4, ih hr⟩

lemma known_get {w ws : List Word16} (h : ∀ a ∈ ws, Known w a) (i : ℕ) : Known w (ws.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : ws[i]? with
  | none => exact Or.inl rfl
  | some a => exact h a (List.mem_of_getElem? hi)

lemma wordOp_next (w : List Word16) (op : GateOp) (as : List Word16)
    (ha : ∀ a ∈ as, Known w a) (hok : Allowed op) :
    Known w (wordOp op as) ∨ Next w (wordOp op as) := by
  have hnot : ∀ a, Known w a → Known w (~~~a) ∨ Next w (~~~a) := by
    intro a ha'
    rcases ha' with rfl | rfl | hm
    · exact Or.inl (Or.inr (Or.inl (by decide)))
    · exact Or.inl (Or.inl (by decide))
    · exact Or.inr (Or.inl ⟨a, hm, rfl⟩)
  have hand : ∀ a b, Known w a → Known w b → Known w (a &&& b) ∨ Next w (a &&& b) := by
    intro a b ha' hb'
    rcases ha' with rfl | rfl | hma
    · exact Or.inl (Or.inl BitVec.zero_and)
    · rw [BitVec.allOnes_and]; exact Or.inl hb'
    · rcases hb' with rfl | rfl | hmb
      · exact Or.inl (Or.inl BitVec.and_zero)
      · rw [BitVec.and_allOnes]; exact Or.inl (Or.inr (Or.inr hma))
      · exact Or.inr (Or.inr ⟨a, hma, b, hmb, Or.inl rfl⟩)
  have hor : ∀ a b, Known w a → Known w b → Known w (a ||| b) ∨ Next w (a ||| b) := by
    intro a b ha' hb'
    rcases ha' with rfl | rfl | hma
    · rw [show (0 : Word16) ||| b = b from BitVec.zero_or]; exact Or.inl hb'
    · exact Or.inl (Or.inr (Or.inl (BitVec.allOnes_or)))
    · rcases hb' with rfl | rfl | hmb
      · rw [show a ||| (0 : Word16) = a from BitVec.or_zero]; exact Or.inl (Or.inr (Or.inr hma))
      · exact Or.inl (Or.inr (Or.inl (BitVec.or_allOnes)))
      · exact Or.inr (Or.inr ⟨a, hma, b, hmb, Or.inr rfl⟩)
  rcases hok with rfl | rfl | rfl <;> cases as with
  | nil =>
    first | exact Or.inl (Or.inr (Or.inl rfl)) | exact Or.inl (Or.inl rfl)
  | cons a rest =>
    cases rest with
    | nil =>
      first
      | exact Or.inl (ha a List.mem_cons_self)
      | exact hnot a (ha a List.mem_cons_self)
    | cons b rest2 =>
      first
      | exact hand a b (ha a List.mem_cons_self) (ha b (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact hor a b (ha a List.mem_cons_self) (ha b (List.mem_cons_of_mem _ List.mem_cons_self))
      | exact hnot a (ha a List.mem_cons_self)

lemma reachable (w ws : List Word16) (gs : List Gate) (k o : ℕ) (t : Word16)
    (hk : gs.length ≤ k) (hknown : ∀ a ∈ ws, Known w a)
    (hok : ∀ g ∈ gs, Allowed g.op) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 16)
    (ht : (wordRun ws gs).getD o 0 = t) : Reach w k t := by
  induction gs generalizing ws w k with
  | nil =>
    change ws.getD o 0 = t at ht
    have h := known_get hknown o
    rw [ht] at h
    have hm := (h.resolve_left h0).resolve_left h1
    induction k with
    | zero => exact hm
    | succ k ih => exact Or.inl hm
  | cons g gs ih =>
    let z := wordStep ws g
    change (wordRun (ws ++ [z]) gs).getD o 0 = t at ht
    have hrest := fun g' (hg' : g' ∈ gs) => hok g' (List.mem_cons_of_mem g hg')
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases h : Known w z
      · apply reach_mono
        apply ih w (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hknown a ha
        · exact h
      · have hz : Known w z ∨ Next w z :=
          wordOp_next w g.op _ (fun a ha => by
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact known_get hknown i) (hok g List.mem_cons_self)
        refine Or.inr ⟨z, fun hm => h (Or.inr (Or.inr hm)), fun hz0 => h (Or.inl hz0),
          fun hz1 => h (Or.inr (Or.inl hz1)), hz.resolve_left h, ?_⟩
        apply ih (z :: w) (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · rcases hknown a ha with h0' | h1' | hm
          · exact Or.inl h0'
          · exact Or.inr (Or.inl h1')
          · exact Or.inr (Or.inr (List.mem_cons_of_mem z hm))
        · exact Or.inr (Or.inr List.mem_cons_self)

def inputCols : List Word16 := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

def row4 (j : ℕ) (i : Fin 4) : Bool := (inputCols.getD i.val 0).getLsbD j

lemma table_reach {f : (Fin 4 → Bool) → Bool} {k : ℕ} {t : Word16}
    (hf : HasCircuitSize 4 f k) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 16)
    (hb : ∀ j : Fin 16, f (row4 j.val) = t.getLsbD j.val) : Reach inputCols k t := by
  obtain ⟨C, hok, hs, hev⟩ := hf
  have hok' : ∀ g ∈ C.gates, Allowed g.op ∧ g.inputs.length ≤ 2 := hok
  refine reachable inputCols inputCols C.gates k C.output t hs ?_ (fun g hg => (hok' g hg).1) h0 h1 ?_
  · intro a ha; exact Or.inr (Or.inr ha)
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← bits_get, wordRun_bits _ _ _ hj hok']
    have hinput : bits inputCols j = List.ofFn (row4 j) := by rfl
    rw [hinput]
    exact (hev (row4 j)).trans (hb ⟨j, hj⟩)

lemma next_sub {w w' : List Word16} (hw : ∀ a, a ∈ w → a ∈ w') {z : Word16} (h : Next w z) : Next w' z := by
  rcases h with ⟨a, ha, e⟩ | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ⟨a, hw a ha, e⟩
  · exact Or.inr ⟨a, hw a ha, b, hw b hb, e⟩

lemma reach_congr : ∀ (k : ℕ) {w w' : List Word16} {t : Word16},
    (∀ a, a ∈ w ↔ a ∈ w') → Reach w k t → Reach w' k t
  | 0, _, _, t, hw, h => (hw t).1 h
  | k + 1, w, w', t, hw, h => by
    rcases h with ht | ⟨z, h1, h2, h3, h4, hr⟩
    · exact Or.inl ((hw t).1 ht)
    · refine Or.inr ⟨z, fun hm => h1 ((hw z).2 hm), h2, h3, next_sub (fun a ha => (hw a).1 ha) h4,
        reach_congr k (fun a => ?_) hr⟩
      simp only [List.mem_cons, hw a]

def nt (a : ℕ) : ℕ := Nat.sub 65535 a

noncomputable def allR (p : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => Bool.rec (motive := fun _ => Bool) false ih (p a)) l

noncomputable def pairAll (f : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a r ih => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false ih
        (allR (fun b => Bool.rec (motive := fun _ => Bool) false (f (Nat.lor a b)) (f (Nat.land a b))) r))
      (f (nt a))) l

noncomputable def andPart (t : ℕ) (w : List ℕ) (z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (allR (fun a => Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.land z a) t)) w)
    (Nat.beq (Nat.land z t) t)

noncomputable def orPart (t : ℕ) (w : List ℕ) (z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (allR (fun a => Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.lor z a) t)) w)
    (Nat.beq (Nat.lor z t) t)

noncomputable def zc (t : ℕ) (w : List ℕ) (z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false (orPart t w z) (andPart t w z)) false (Nat.beq (nt z) t)

noncomputable def two (t : ℕ) (w : List ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (pairAll (zc t w) w) (allR (zc t w) w)

noncomputable def anyEq (z : ℕ) (w : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq z a)) w

noncomputable def known (w : List ℕ) (z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (anyEq z w) true (Nat.beq z 65535)) true (Nat.beq z 0)

noncomputable def go (t : ℕ) (chk : ℕ → List ℕ → Bool) (w : List ℕ) (z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (chk z (z :: w)) false (Nat.beq z t)) true (known w z)

noncomputable def step (t m : ℕ) (chk : ℕ → List ℕ → Bool) (w : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h w0 _ =>
    Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (pairAll (fun z => Bool.rec (motive := fun _ => Bool) true (go t chk (h :: w0) z) (Nat.ble m z)) w0)
        (allR (fun a => Bool.rec (motive := fun _ => Bool) false (go t chk (h :: w0) (Nat.lor h a))
          (go t chk (h :: w0) (Nat.land h a))) w0))
      (go t chk (h :: w0) (nt h))) w

noncomputable def neAnd (t a z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.land z a) t)

noncomputable def neOr (t a z : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.lor z a) t)

noncomputable def twoU (t : ℕ) (zw : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z w _ =>
    Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) true (pairAll (neOr t z) w) (Nat.beq (Nat.lor z t) t))
            (Bool.rec (motive := fun _ => Bool) true (pairAll (neAnd t z) w) (Nat.beq (Nat.land z t) t)))
          (allR (fun a => Bool.rec (motive := fun _ => Bool) false (zc t (z :: w) (Nat.lor z a))
            (zc t (z :: w) (Nat.land z a))) w))
        (zc t (z :: w) (nt z)))
      (zc t w z)) zw

noncomputable def srch (t : ℕ) (r : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → List ℕ → Bool)
    (fun m w => Bool.rec (motive := fun _ => Bool) false (step t m (fun _ zw => twoU t zw) w) (two t w))
    (fun _ ih m w => step t m ih w) r

lemma ft {P : Prop} (h : false = true) : P := Bool.noConfusion h

lemma brec_true {x y c : Bool} (h : Bool.rec (motive := fun _ => Bool) x y c = true) :
    (c = false ∧ x = true) ∨ (c = true ∧ y = true) := by
  cases c
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

lemma allR_true {p : ℕ → Bool} : ∀ {l : List ℕ}, allR p l = true → ∀ a ∈ l, p a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allR p l) (p b) = true := h
    rcases brec_true h' with ⟨_, hf⟩ | ⟨hb, hl⟩
    · exact ft hf
    · rcases List.mem_cons.1 ha with e | ha'
      · rw [e]; exact hb
      · exact allR_true hl a ha'

lemma land_absorb (z a : ℕ) : Nat.land z (Nat.land z a) = Nat.land z a := by
  show z &&& (z &&& a) = z &&& a
  rw [← Nat.and_assoc, Nat.and_self]

lemma lor_absorb (z a : ℕ) : Nat.lor z (Nat.lor z a) = Nat.lor z a := by
  show z ||| (z ||| a) = z ||| a
  rw [← Nat.or_assoc, Nat.or_self]

lemma land_comm' (a b : ℕ) : Nat.land a b = Nat.land b a := Nat.and_comm a b

lemma lor_comm' (a b : ℕ) : Nat.lor a b = Nat.lor b a := Nat.or_comm a b

lemma andPart_spec {t : ℕ} {w : List ℕ} {z : ℕ} (h : andPart t w z = true) :
    ∀ a ∈ w, Nat.land z a ≠ t := by
  intro a ha he
  unfold andPart at h
  rcases brec_true h with ⟨hc, _⟩ | ⟨_, hs⟩
  · have e : Nat.land z t = t := by rw [← he]; exact land_absorb z a
    exact Nat.ne_of_beq_eq_false hc e
  · have h2 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.land z a) t) = true :=
      allR_true hs a ha
    rcases brec_true h2 with ⟨hc, _⟩ | ⟨_, hf⟩
    · exact Nat.ne_of_beq_eq_false hc he
    · exact ft hf

lemma orPart_spec {t : ℕ} {w : List ℕ} {z : ℕ} (h : orPart t w z = true) :
    ∀ a ∈ w, Nat.lor z a ≠ t := by
  intro a ha he
  unfold orPart at h
  rcases brec_true h with ⟨hc, _⟩ | ⟨_, hs⟩
  · have e : Nat.lor z t = t := by rw [← he]; exact lor_absorb z a
    exact Nat.ne_of_beq_eq_false hc e
  · have h2 : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.lor z a) t) = true :=
      allR_true hs a ha
    rcases brec_true h2 with ⟨hc, _⟩ | ⟨_, hf⟩
    · exact Nat.ne_of_beq_eq_false hc he
    · exact ft hf

lemma zc_spec {t : ℕ} {w : List ℕ} {z : ℕ} (h : zc t w z = true) :
    nt z ≠ t ∧ (∀ a ∈ w, Nat.land z a ≠ t) ∧ (∀ a ∈ w, Nat.lor z a ≠ t) := by
  unfold zc at h
  rcases brec_true h with ⟨hc, h2⟩ | ⟨_, hf⟩
  · rcases brec_true h2 with ⟨_, hf⟩ | ⟨ha, ho⟩
    · exact ft hf
    · exact ⟨Nat.ne_of_beq_eq_false hc, andPart_spec ha, orPart_spec ho⟩
  · exact ft hf

lemma pairAll_spec {f : ℕ → Bool} : ∀ {l : List ℕ}, pairAll f l = true →
    (∀ a ∈ l, f (nt a) = true) ∧
      ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f (Nat.land a b) = true ∧ f (Nat.lor a b) = true
  | [], _ => ⟨fun _ ha => absurd ha List.not_mem_nil, fun _ ha => absurd ha List.not_mem_nil⟩
  | x :: r, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (pairAll f r)
          (allR (fun b => Bool.rec (motive := fun _ => Bool) false (f (Nat.lor x b)) (f (Nat.land x b))) r))
        (f (nt x)) = true := h
    rcases brec_true h' with ⟨_, hf⟩ | ⟨hx, h2⟩
    · exact ft hf
    rcases brec_true h2 with ⟨_, hf⟩ | ⟨hr, h3⟩
    · exact ft hf
    obtain ⟨i1, i2⟩ := pairAll_spec (l := r) h3
    have hxr : ∀ b ∈ r, f (Nat.land x b) = true ∧ f (Nat.lor x b) = true := by
      intro b hb
      have h4 : Bool.rec (motive := fun _ => Bool) false (f (Nat.lor x b)) (f (Nat.land x b)) = true :=
        allR_true hr b hb
      rcases brec_true h4 with ⟨_, hf⟩ | ⟨h5, h6⟩
      · exact ft hf
      · exact ⟨h5, h6⟩
    refine ⟨?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.1 ha with e | ha'
      · rw [e]; exact hx
      · exact i1 a ha'
    · intro a ha b hb hab
      rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hb with eb | hb'
      · exact (hab (ea.trans eb.symm)).elim
      · rw [ea]; exact hxr b hb'
      · rw [eb, land_comm' a x, lor_comm' a x]; exact hxr a ha'
      · exact i2 a ha' b hb' hab

lemma anyEq_true {z : ℕ} : ∀ {w : List ℕ}, anyEq z w = true → z ∈ w
  | [], h => ft h
  | a :: w, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (anyEq z w) true (Nat.beq z a) = true := h
    rcases brec_true h' with ⟨_, h2⟩ | ⟨hc, _⟩
    · exact List.mem_cons_of_mem _ (anyEq_true h2)
    · exact List.mem_cons.2 (Or.inl (Nat.eq_of_beq_eq_true hc))

lemma known_spec {w : List ℕ} {z : ℕ} (h : known w z = true) : z = 0 ∨ z = 65535 ∨ z ∈ w := by
  unfold known at h
  rcases brec_true h with ⟨_, h2⟩ | ⟨hc, _⟩
  · rcases brec_true h2 with ⟨_, h3⟩ | ⟨hc, _⟩
    · exact Or.inr (Or.inr (anyEq_true h3))
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true hc))
  · exact Or.inl (Nat.eq_of_beq_eq_true hc)

lemma go_spec {t : ℕ} {chk : ℕ → List ℕ → Bool} {w : List ℕ} {z : ℕ} (h : go t chk w z = true) :
    known w z = true ∨ (z ≠ t ∧ chk z (z :: w) = true) := by
  unfold go at h
  rcases brec_true h with ⟨_, h2⟩ | ⟨hk, _⟩
  · rcases brec_true h2 with ⟨hc, h3⟩ | ⟨_, hf⟩
    · exact Or.inr ⟨Nat.ne_of_beq_eq_false hc, h3⟩
    · exact ft hf
  · exact Or.inl hk

lemma step_spec {t m : ℕ} {chk : ℕ → List ℕ → Bool} {h : ℕ} {w0 : List ℕ}
    (hs : step t m chk (h :: w0) = true) :
    go t chk (h :: w0) (nt h) = true ∧
    (∀ a ∈ w0, go t chk (h :: w0) (Nat.land h a) = true ∧ go t chk (h :: w0) (Nat.lor h a) = true) ∧
    (∀ a ∈ w0, m ≤ nt a → go t chk (h :: w0) (nt a) = true) ∧
    (∀ a ∈ w0, ∀ b ∈ w0, a ≠ b →
      (m ≤ Nat.land a b → go t chk (h :: w0) (Nat.land a b) = true) ∧
      (m ≤ Nat.lor a b → go t chk (h :: w0) (Nat.lor a b) = true)) := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (pairAll (fun z => Bool.rec (motive := fun _ => Bool) true (go t chk (h :: w0) z) (Nat.ble m z)) w0)
        (allR (fun a => Bool.rec (motive := fun _ => Bool) false (go t chk (h :: w0) (Nat.lor h a))
          (go t chk (h :: w0) (Nat.land h a))) w0))
      (go t chk (h :: w0) (nt h)) = true := hs
  rcases brec_true h' with ⟨_, hf⟩ | ⟨g1, h2⟩
  · exact ft hf
  rcases brec_true h2 with ⟨_, hf⟩ | ⟨ha, hp⟩
  · exact ft hf
  obtain ⟨p1, p2⟩ := pairAll_spec hp
  have ble : ∀ z, Bool.rec (motive := fun _ => Bool) true (go t chk (h :: w0) z) (Nat.ble m z) = true →
      m ≤ z → go t chk (h :: w0) z = true := by
    intro z hz hle
    rcases brec_true hz with ⟨hc, _⟩ | ⟨_, hg⟩
    · rw [Nat.ble_eq_true_of_le hle] at hc; exact ft hc.symm
    · exact hg
  refine ⟨g1, ?_, fun a ha' => ble _ (p1 a ha'), fun a ha' b hb' hab =>
    ⟨ble _ (p2 a ha' b hb' hab).1, ble _ (p2 a ha' b hb' hab).2⟩⟩
  intro a ha'
  have h4 : Bool.rec (motive := fun _ => Bool) false (go t chk (h :: w0) (Nat.lor h a))
      (go t chk (h :: w0) (Nat.land h a)) = true := allR_true ha a ha'
  rcases brec_true h4 with ⟨_, hf⟩ | ⟨h5, h6⟩
  · exact ft hf
  · exact ⟨h5, h6⟩

lemma n_and (a b : Word16) : (a &&& b).toNat = Nat.land a.toNat b.toNat := BitVec.toNat_and a b

lemma n_or (a b : Word16) : (a ||| b).toNat = Nat.lor a.toNat b.toNat := BitVec.toNat_or a b

lemma n_not (a : Word16) : (~~~a).toNat = nt a.toNat := by
  rw [BitVec.toNat_not]; rfl

lemma n_mem {a : Word16} {w : List Word16} (h : a ∈ w) : a.toNat ∈ w.map BitVec.toNat :=
  List.mem_map.2 ⟨a, h, rfl⟩

lemma n_mem' {a : Word16} {w : List Word16} (h : a.toNat ∈ w.map BitVec.toNat) : a ∈ w := by
  obtain ⟨b, hb, e⟩ := List.mem_map.1 h
  rw [← BitVec.eq_of_toNat_eq e]; exact hb

lemma cand_zc {t : ℕ} {w : List Word16}
    (h1 : allR (zc t (w.map BitVec.toNat)) (w.map BitVec.toNat) = true)
    (h2 : pairAll (zc t (w.map BitVec.toNat)) (w.map BitVec.toNat) = true) {z : Word16}
    (hz : Next w z) : zc t (w.map BitVec.toNat) z.toNat = true := by
  obtain ⟨p1, p2⟩ := pairAll_spec h2
  rcases hz with ⟨a, ha, e⟩ | ⟨a, ha, b, hb, e | e⟩
  · rw [e, n_not]; exact p1 _ (n_mem ha)
  · by_cases hab : a = b
    · rw [e, hab, BitVec.and_self]; exact allR_true h1 _ (n_mem hb)
    · rw [e, n_and]
      exact (p2 _ (n_mem ha) _ (n_mem hb) (fun he => hab (BitVec.eq_of_toNat_eq he))).1
  · by_cases hab : a = b
    · rw [e, hab, BitVec.or_self]; exact allR_true h1 _ (n_mem hb)
    · rw [e, n_or]
      exact (p2 _ (n_mem ha) _ (n_mem hb) (fun he => hab (BitVec.eq_of_toNat_eq he))).2

lemma two_AC {t : Word16} {w : List Word16} (h : two t.toNat (w.map BitVec.toNat) = true) :
    (∀ z, Next w z → t ≠ z) ∧ ∀ z, Next w z → nt z.toNat ≠ t.toNat ∧
      (∀ a ∈ w.map BitVec.toNat, Nat.land z.toNat a ≠ t.toNat) ∧
      (∀ a ∈ w.map BitVec.toNat, Nat.lor z.toNat a ≠ t.toNat) := by
  unfold two at h
  rcases brec_true h with ⟨_, hf⟩ | ⟨h1, h2⟩
  · exact ft hf
  refine ⟨?_, fun z hz => zc_spec (cand_zc h1 h2 hz)⟩
  intro z hz hzt
  rcases hz with ⟨a, ha, e⟩ | ⟨a, ha, b, hb, e | e⟩
  · exact (zc_spec (allR_true h1 _ (n_mem ha))).1 (by rw [hzt, e, n_not])
  · exact (zc_spec (allR_true h1 _ (n_mem ha))).2.1 _ (n_mem hb) (by rw [hzt, e, n_and])
  · exact (zc_spec (allR_true h1 _ (n_mem ha))).2.2 _ (n_mem hb) (by rw [hzt, e, n_or])

theorem two_tail {t : Word16} {w : List Word16} (ht : t ∉ w) (A : ∀ z, Next w z → t ≠ z)
    (C : ∀ z, Next w z → z ∉ w → nt z.toNat ≠ t.toNat ∧
      (∀ a ∈ w.map BitVec.toNat, Nat.land z.toNat a ≠ t.toNat) ∧
      (∀ a ∈ w.map BitVec.toNat, Nat.lor z.toNat a ≠ t.toNat)) : ¬ Reach w 2 t := by
  intro hr
  rcases hr with hm | ⟨z, hzw, _, _, hzn, hr1⟩
  · exact ht hm
  rcases hr1 with hm | ⟨y, _, _, _, hyn, hr0⟩
  · rcases List.mem_cons.1 hm with e | hm'
    · exact A z hzn e
    · exact ht hm'
  · have hr0' : t ∈ y :: z :: w := hr0
    rcases List.mem_cons.1 hr0' with hty | hm
    · obtain ⟨c1, c2, c3⟩ := C z hzn hzw
      rcases hyn with ⟨a, ha, e⟩ | ⟨a, ha, b, hb, e⟩
      · rcases List.mem_cons.1 ha with ea | ha'
        · exact c1 (by rw [hty, e, ea, n_not])
        · exact A y (Or.inl ⟨a, ha', e⟩) hty
      · rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hb with eb | hb'
        · have hyz : y = z := by
            rcases e with e | e
            · rw [e, ea, eb, BitVec.and_self]
            · rw [e, ea, eb, BitVec.or_self]
          exact A z hzn (hty.trans hyz)
        · rcases e with e | e
          · exact c2 _ (n_mem hb') (by rw [hty, e, ea, n_and])
          · exact c3 _ (n_mem hb') (by rw [hty, e, ea, n_or])
        · rcases e with e | e
          · exact c2 _ (n_mem ha') (by rw [hty, e, eb, BitVec.and_comm, n_and])
          · exact c3 _ (n_mem ha') (by rw [hty, e, eb, BitVec.or_comm, n_or])
        · exact A y (Or.inr ⟨a, ha', b, hb', e⟩) hty
    · rcases List.mem_cons.1 hm with e | hm'
      · exact A z hzn e
      · exact ht hm'

theorem two_sound {t : Word16} {w : List Word16} (ht : t ∉ w)
    (h : two t.toNat (w.map BitVec.toNat) = true) : ¬ Reach w 2 t :=
  two_tail ht (two_AC h).1 (fun z hz _ => (two_AC h).2 z hz)

lemma neAnd_spec {t a z : ℕ} (h : neAnd t a z = true) : Nat.land z a ≠ t := by
  unfold neAnd at h
  rcases brec_true h with ⟨hc, _⟩ | ⟨_, hf⟩
  · exact Nat.ne_of_beq_eq_false hc
  · exact ft hf

lemma neOr_spec {t a z : ℕ} (h : neOr t a z = true) : Nat.lor z a ≠ t := by
  unfold neOr at h
  rcases brec_true h with ⟨hc, _⟩ | ⟨_, hf⟩
  · exact Nat.ne_of_beq_eq_false hc
  · exact ft hf

lemma twoU_spec {t z : ℕ} {w : List ℕ} (h : twoU t (z :: w) = true) :
    zc t w z = true ∧ zc t (z :: w) (nt z) = true ∧
    (∀ a ∈ w, zc t (z :: w) (Nat.land z a) = true ∧ zc t (z :: w) (Nat.lor z a) = true) ∧
    (Nat.land z t = t → pairAll (neAnd t z) w = true) ∧
    (Nat.lor z t = t → pairAll (neOr t z) w = true) := by
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) true (pairAll (neOr t z) w) (Nat.beq (Nat.lor z t) t))
            (Bool.rec (motive := fun _ => Bool) true (pairAll (neAnd t z) w) (Nat.beq (Nat.land z t) t)))
          (allR (fun a => Bool.rec (motive := fun _ => Bool) false (zc t (z :: w) (Nat.lor z a))
            (zc t (z :: w) (Nat.land z a))) w))
        (zc t (z :: w) (nt z)))
      (zc t w z) = true := h
  rcases brec_true h' with ⟨_, hf⟩ | ⟨u1, h2⟩
  · exact ft hf
  rcases brec_true h2 with ⟨_, hf⟩ | ⟨u2, h3⟩
  · exact ft hf
  rcases brec_true h3 with ⟨_, hf⟩ | ⟨u3, h4⟩
  · exact ft hf
  rcases brec_true h4 with ⟨_, hf⟩ | ⟨u4, u5⟩
  · exact ft hf
  refine ⟨u1, u2, ?_, ?_, ?_⟩
  · intro a ha
    have h5 : Bool.rec (motive := fun _ => Bool) false (zc t (z :: w) (Nat.lor z a))
        (zc t (z :: w) (Nat.land z a)) = true := allR_true u3 a ha
    rcases brec_true h5 with ⟨_, hf⟩ | ⟨h6, h7⟩
    · exact ft hf
    · exact ⟨h6, h7⟩
  · intro e
    rcases brec_true u4 with ⟨hc, _⟩ | ⟨_, hp⟩
    · exact (Nat.ne_of_beq_eq_false hc e).elim
    · exact hp
  · intro e
    rcases brec_true u5 with ⟨hc, _⟩ | ⟨_, hp⟩
    · exact (Nat.ne_of_beq_eq_false hc e).elim
    · exact hp

theorem twoU_sound {t z : Word16} {w : List Word16} (ht : t ∉ z :: w)
    (h2 : two t.toNat (w.map BitVec.toNat) = true)
    (hu : twoU t.toNat (z.toNat :: w.map BitVec.toNat) = true) : ¬ Reach (z :: w) 2 t := by
  obtain ⟨A, C⟩ := two_AC h2
  obtain ⟨u1, u2, u3, u4, u5⟩ := twoU_spec hu
  obtain ⟨v1, v2, v3⟩ := zc_spec u1
  have htz : t ≠ z := fun e => ht (e ▸ List.mem_cons_self)
  have old : ∀ y, Next w y → y ∉ z :: w → nt y.toNat ≠ t.toNat ∧
      (∀ a ∈ (z :: w).map BitVec.toNat, Nat.land y.toNat a ≠ t.toNat) ∧
      (∀ a ∈ (z :: w).map BitVec.toNat, Nat.lor y.toNat a ≠ t.toNat) := by
    intro y hy hym
    obtain ⟨c1, c2, c3⟩ := C y hy
    refine ⟨c1, ?_, ?_⟩
    · intro a ha he
      rcases List.mem_cons.1 ha with ea | ha'
      · rw [ea] at he
        have hzt : Nat.land z.toNat t.toNat = t.toNat := by
          rw [← he, land_comm' y.toNat z.toNat]; exact land_absorb _ _
        obtain ⟨p1, p2⟩ := pairAll_spec (u4 hzt)
        rcases hy with ⟨c, hc, e⟩ | ⟨c, hc, d, hd, e | e⟩
        · exact neAnd_spec (p1 _ (n_mem hc)) (by rw [← n_not, ← e]; exact he)
        · by_cases hcd : c = d
          · exact hym (List.mem_cons_of_mem _ (by rw [e, hcd, BitVec.and_self]; exact hd))
          · exact neAnd_spec (p2 _ (n_mem hc) _ (n_mem hd) (fun h => hcd (BitVec.eq_of_toNat_eq h))).1
              (by rw [← n_and, ← e]; exact he)
        · by_cases hcd : c = d
          · exact hym (List.mem_cons_of_mem _ (by rw [e, hcd, BitVec.or_self]; exact hd))
          · exact neAnd_spec (p2 _ (n_mem hc) _ (n_mem hd) (fun h => hcd (BitVec.eq_of_toNat_eq h))).2
              (by rw [← n_or, ← e]; exact he)
      · exact c2 a ha' he
    · intro a ha he
      rcases List.mem_cons.1 ha with ea | ha'
      · rw [ea] at he
        have hzt : Nat.lor z.toNat t.toNat = t.toNat := by
          rw [← he, lor_comm' y.toNat z.toNat]; exact lor_absorb _ _
        obtain ⟨p1, p2⟩ := pairAll_spec (u5 hzt)
        rcases hy with ⟨c, hc, e⟩ | ⟨c, hc, d, hd, e | e⟩
        · exact neOr_spec (p1 _ (n_mem hc)) (by rw [← n_not, ← e]; exact he)
        · by_cases hcd : c = d
          · exact hym (List.mem_cons_of_mem _ (by rw [e, hcd, BitVec.and_self]; exact hd))
          · exact neOr_spec (p2 _ (n_mem hc) _ (n_mem hd) (fun h => hcd (BitVec.eq_of_toNat_eq h))).1
              (by rw [← n_and, ← e]; exact he)
        · by_cases hcd : c = d
          · exact hym (List.mem_cons_of_mem _ (by rw [e, hcd, BitVec.or_self]; exact hd))
          · exact neOr_spec (p2 _ (n_mem hc) _ (n_mem hd) (fun h => hcd (BitVec.eq_of_toNat_eq h))).2
              (by rw [← n_or, ← e]; exact he)
      · exact c3 a ha' he
  refine two_tail ht ?_ ?_
  · intro y hy hty
    rcases hy with ⟨c, hc, e⟩ | ⟨c, hc, d, hd, e⟩
    · rcases List.mem_cons.1 hc with ec | hc'
      · exact v1 (by rw [hty, e, ec, n_not])
      · exact A y (Or.inl ⟨c, hc', e⟩) hty
    · rcases List.mem_cons.1 hc with ec | hc' <;> rcases List.mem_cons.1 hd with ed | hd'
      · apply htz
        rcases e with e | e
        · rw [hty, e, ec, ed, BitVec.and_self]
        · rw [hty, e, ec, ed, BitVec.or_self]
      · rcases e with e | e
        · exact v2 _ (n_mem hd') (by rw [hty, e, ec, n_and])
        · exact v3 _ (n_mem hd') (by rw [hty, e, ec, n_or])
      · rcases e with e | e
        · exact v2 _ (n_mem hc') (by rw [hty, e, ed, BitVec.and_comm, n_and])
        · exact v3 _ (n_mem hc') (by rw [hty, e, ed, BitVec.or_comm, n_or])
      · exact A y (Or.inr ⟨c, hc', d, hd', e⟩) hty
  · intro y hy hym
    rcases hy with ⟨c, hc, e⟩ | ⟨c, hc, d, hd, e⟩
    · rcases List.mem_cons.1 hc with ec | hc'
      · rw [e, ec, n_not]; exact zc_spec u2
      · exact old y (Or.inl ⟨c, hc', e⟩) hym
    · rcases List.mem_cons.1 hc with ec | hc' <;> rcases List.mem_cons.1 hd with ed | hd'
      · exfalso
        apply hym
        have hyz : y = z := by
          rcases e with e | e
          · rw [e, ec, ed, BitVec.and_self]
          · rw [e, ec, ed, BitVec.or_self]
        rw [hyz]; exact List.mem_cons_self
      · rcases e with e | e
        · rw [e, ec, n_and]; exact zc_spec (u3 _ (n_mem hd')).1
        · rw [e, ec, n_or]; exact zc_spec (u3 _ (n_mem hd')).2
      · rcases e with e | e
        · rw [e, ed, BitVec.and_comm, n_and]; exact zc_spec (u3 _ (n_mem hc')).1
        · rw [e, ed, BitVec.or_comm, n_or]; exact zc_spec (u3 _ (n_mem hc')).2
      · exact old y (Or.inr ⟨c, hc', d, hd', e⟩) hym

def Inv (w0 : List Word16) (h : Word16) (m b : ℕ) (t : Word16) : Prop :=
  ∀ z, Next w0 z → z ∉ w0 → z ≠ 0 → z ≠ BitVec.allOnes 16 → z.toNat < m → ¬ Reach (z :: h :: w0) b t

theorem step_sound {t : Word16} {b m : ℕ} {chk : ℕ → List ℕ → Bool} {h : Word16} {w0 : List Word16}
    (ht : t ∉ h :: w0) (hinv : Inv w0 h m (b + 1) t)
    (hs : step t.toNat m chk ((h :: w0).map BitVec.toNat) = true)
    (hchk : ∀ z : Word16, z ∉ h :: w0 → z ≠ t →
      chk z.toNat (z.toNat :: (h :: w0).map BitVec.toNat) = true →
      Inv (h :: w0) z z.toNat b t → ¬ Reach (z :: h :: w0) (b + 1) t) :
    ¬ Reach (h :: w0) (b + 2) t := by
  have hs' : step t.toNat m chk (h.toNat :: w0.map BitVec.toNat) = true := hs
  obtain ⟨g1, g2, g3, g4⟩ := step_spec hs'
  have key : ∀ n, ∀ z : Word16, z.toNat = n → Next (h :: w0) z → z ∉ h :: w0 → z ≠ 0 →
      z ≠ BitVec.allOnes 16 → ¬ Reach (z :: h :: w0) (b + 1) t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hzn hnext hnm h0 h1
      have K : go t.toNat chk (h.toNat :: w0.map BitVec.toNat) z.toNat = true ∨
          (Next w0 z ∧ z.toNat < m) := by
        rcases hnext with ⟨a, ha, e⟩ | ⟨a, ha, c, hc, e⟩
        · rcases List.mem_cons.1 ha with ea | ha'
          · left; rw [e, ea, n_not]; exact g1
          · by_cases hlt : z.toNat < m
            · exact Or.inr ⟨Or.inl ⟨a, ha', e⟩, hlt⟩
            · left
              have hle : m ≤ nt a.toNat := by rw [← n_not, ← e]; omega
              rw [e, n_not]; exact g3 _ (n_mem ha') hle
        · rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hc with ec | hc'
          · exfalso
            apply hnm
            have hzh : z = h := by
              rcases e with e | e
              · rw [e, ea, ec, BitVec.and_self]
              · rw [e, ea, ec, BitVec.or_self]
            rw [hzh]; exact List.mem_cons_self
          · left
            rcases e with e | e
            · rw [e, ea, n_and]; exact (g2 _ (n_mem hc')).1
            · rw [e, ea, n_or]; exact (g2 _ (n_mem hc')).2
          · left
            rcases e with e | e
            · rw [e, ec, BitVec.and_comm, n_and]; exact (g2 _ (n_mem ha')).1
            · rw [e, ec, BitVec.or_comm, n_or]; exact (g2 _ (n_mem ha')).2
          · by_cases hac : a = c
            · exfalso
              apply hnm
              have hza : z = c := by
                rcases e with e | e
                · rw [e, hac, BitVec.and_self]
                · rw [e, hac, BitVec.or_self]
              rw [hza]; exact List.mem_cons_of_mem _ hc'
            · by_cases hlt : z.toNat < m
              · exact Or.inr ⟨Or.inr ⟨a, ha', c, hc', e⟩, hlt⟩
              · left
                have hne : a.toNat ≠ c.toNat := fun he => hac (BitVec.eq_of_toNat_eq he)
                rcases e with e | e
                · have hle : m ≤ Nat.land a.toNat c.toNat := by rw [← n_and, ← e]; omega
                  rw [e, n_and]; exact (g4 _ (n_mem ha') _ (n_mem hc') hne).1 hle
                · have hle : m ≤ Nat.lor a.toNat c.toNat := by rw [← n_or, ← e]; omega
                  rw [e, n_or]; exact (g4 _ (n_mem ha') _ (n_mem hc') hne).2 hle
      rcases K with hg | ⟨hn0, hlt⟩
      · rcases go_spec hg with hk | ⟨hne, hc⟩
        · rcases known_spec hk with e | e | e
          · exact (h0 (BitVec.eq_of_toNat_eq e)).elim
          · exact (h1 (BitVec.eq_of_toNat_eq e)).elim
          · exact (hnm (n_mem' e)).elim
        · refine hchk z hnm (fun e => hne (congrArg BitVec.toNat e)) hc ?_
          intro y hy hym hy0 hy1 hylt hr
          refine ih y.toNat (hzn ▸ hylt) y rfl hy hym hy0 hy1 ?_
          refine Or.inr ⟨z, ?_, h0, h1, next_sub (fun a ha => List.mem_cons_of_mem _ ha) hnext,
            reach_congr b (fun a => ?_) hr⟩
          · intro hm
            rcases List.mem_cons.1 hm with e | hm'
            · rw [e] at hylt; exact lt_irrefl _ hylt
            · exact hnm hm'
          · simp only [List.mem_cons]; tauto
      · exact hinv z hn0 (fun hm => hnm (List.mem_cons_of_mem _ hm)) h0 h1 hlt
  intro hr
  rcases hr with hm | ⟨z, hz1, hz2, hz3, hzn, hr1⟩
  · exact ht hm
  · exact key z.toNat z rfl hzn hz1 hz2 hz3 hr1

theorem srch_sound {t : Word16} : ∀ (r m : ℕ) (h : Word16) (w0 : List Word16), t ∉ h :: w0 →
    Inv w0 h m (r + 2) t → srch t.toNat r m ((h :: w0).map BitVec.toNat) = true →
    ¬ Reach (h :: w0) (r + 3) t
  | 0, m, h, w0, ht, hinv, hs => by
    have hs' : Bool.rec (motive := fun _ => Bool) false
        (step t.toNat m (fun _ zw => twoU t.toNat zw) ((h :: w0).map BitVec.toNat))
        (two t.toNat ((h :: w0).map BitVec.toNat)) = true := hs
    rcases brec_true hs' with ⟨_, hf⟩ | ⟨h2, h3⟩
    · exact ft hf
    · exact step_sound (b := 1) (chk := fun _ zw => twoU t.toNat zw) ht hinv h3 (fun z _ hzt hc _ =>
        twoU_sound (fun hm => (List.mem_cons.1 hm).elim (fun e => hzt e.symm) ht) h2 hc)
  | r + 1, _, h, w0, ht, hinv, hs =>
    step_sound (b := r + 2) (chk := srch t.toNat r) ht hinv hs (fun z _ hzt hc hi =>
      srch_sound r z.toNat z (h :: w0)
        (fun hm => (List.mem_cons.1 hm).elim (fun e => hzt e.symm) ht) hi hc)

theorem mid_sound {t : Word16} {b : ℕ} {h : Word16} {w0 : List Word16} (zN : ℕ) (L : List ℕ)
    (hs : step t.toNat zN (fun y _ => anyEq y L) (zN :: (h :: w0).map BitVec.toNat) = true)
    (hall : ∀ y ∈ L, srch t.toNat b y (y :: zN :: (h :: w0).map BitVec.toNat) = true)
    (ht : t ∉ h :: w0) (z : Word16) (hz : z.toNat = zN) (hzt : z ≠ t)
    (hi : Inv (h :: w0) z z.toNat (b + 3) t) : ¬ Reach (z :: h :: w0) (b + 4) t := by
  subst hz
  have ht' : t ∉ z :: h :: w0 := fun hm => (List.mem_cons.1 hm).elim (fun e => hzt e.symm) ht
  exact step_sound (b := b + 2) (chk := fun y _ => anyEq y L) ht' hi hs (fun y _ hyt hc hi2 =>
    srch_sound b y.toNat y (z :: h :: w0)
      (fun hm => (List.mem_cons.1 hm).elim (fun e => hyt e.symm) ht') hi2 (hall y.toNat (anyEq_true hc)))

theorem root_sound {t : Word16} {b : ℕ} {h : Word16} {w0 : List Word16} (L : List ℕ)
    (hs : step t.toNat 0 (fun z _ => anyEq z L) ((h :: w0).map BitVec.toNat) = true)
    (hall : ∀ zN ∈ L, ∀ z : Word16, z.toNat = zN → z ≠ t → Inv (h :: w0) z z.toNat (b + 3) t →
      ¬ Reach (z :: h :: w0) (b + 4) t)
    (ht : t ∉ h :: w0) : ¬ Reach (h :: w0) (b + 5) t :=
  step_sound (b := b + 3) (chk := fun z _ => anyEq z L) ht
    (fun _ _ _ _ _ hlt => absurd hlt (Nat.not_lt_zero _)) hs
    (fun z _ hzt hc hi => hall z.toNat (anyEq_true hc) z rfl hzt hi)

def targetWord : Word16 := 130

def L : List ℕ := [21845, 34952, 61166, 41120, 64250, 43520, 65450, 13107, 49344, 64764, 52224, 65484, 3855, 61440, 65520, 255]

def L0 : List ℕ := [17476, 56797, 20560, 62965, 21760, 65365, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T0_0 : srch 130 1 17476 [17476, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_1 : srch 130 1 56797 [56797, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_2 : srch 130 1 20560 [20560, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_3 : srch 130 1 62965 [62965, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_4 : srch 130 1 21760 [21760, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_5 : srch 130 1 65365 [65365, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_6 : srch 130 1 34952 [34952, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_7 : srch 130 1 61166 [61166, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_8 : srch 130 1 41120 [41120, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_9 : srch 130 1 64250 [64250, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_10 : srch 130 1 43520 [43520, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_11 : srch 130 1 65450 [65450, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_12 : srch 130 1 49344 [49344, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_13 : srch 130 1 64764 [64764, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_14 : srch 130 1 52224 [52224, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_15 : srch 130 1 65484 [65484, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_16 : srch 130 1 61440 [61440, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T0_17 : srch 130 1 65520 [65520, 21845, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A0 : ∀ y ∈ L0, srch targetWord.toNat 1 y (y :: 21845 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L0, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T0_0, T0_1, T0_2, T0_3, T0_4, T0_5, T0_6, T0_7, T0_8, T0_9, T0_10, T0_11, T0_12, T0_13, T0_14, T0_15, T0_16, T0_17]

theorem M0 : step targetWord.toNat 21845 (fun y _ => anyEq y L0) (21845 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L1 : List ℕ := [30583, 32896, 63736, 34816, 65416, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T1_0 : srch 130 1 30583 [30583, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_1 : srch 130 1 32896 [32896, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_2 : srch 130 1 63736 [63736, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_3 : srch 130 1 34816 [34816, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_4 : srch 130 1 65416 [65416, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_5 : srch 130 1 61166 [61166, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_6 : srch 130 1 41120 [41120, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_7 : srch 130 1 64250 [64250, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_8 : srch 130 1 43520 [43520, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_9 : srch 130 1 65450 [65450, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_10 : srch 130 1 49344 [49344, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_11 : srch 130 1 64764 [64764, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_12 : srch 130 1 52224 [52224, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_13 : srch 130 1 65484 [65484, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_14 : srch 130 1 61440 [61440, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T1_15 : srch 130 1 65520 [65520, 34952, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A1 : ∀ y ∈ L1, srch targetWord.toNat 1 y (y :: 34952 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L1, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T1_0, T1_1, T1_2, T1_3, T1_4, T1_5, T1_6, T1_7, T1_8, T1_9, T1_10, T1_11, T1_12, T1_13, T1_14, T1_15]

theorem M1 : step targetWord.toNat 34952 (fun y _ => anyEq y L1) (34952 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L2 : List ℕ := [4369, 57568, 65278, 60928, 65518, 64250, 65450, 64764, 65484, 61440, 65520]

theorem T2_0 : srch 130 1 4369 [4369, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_1 : srch 130 1 57568 [57568, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_2 : srch 130 1 65278 [65278, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_3 : srch 130 1 60928 [60928, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_4 : srch 130 1 65518 [65518, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_5 : srch 130 1 64250 [64250, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_6 : srch 130 1 65450 [65450, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_7 : srch 130 1 64764 [64764, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_8 : srch 130 1 65484 [65484, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_9 : srch 130 1 61440 [61440, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T2_10 : srch 130 1 65520 [65520, 61166, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A2 : ∀ y ∈ L2, srch targetWord.toNat 1 y (y :: 61166 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L2, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T2_0, T2_1, T2_2, T2_3, T2_4, T2_5, T2_6, T2_7, T2_8, T2_9, T2_10]

theorem M2 : step targetWord.toNat 61166 (fun y _ => anyEq y L2) (61166 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L3 : List ℕ := [24415, 32896, 60652, 40960, 65440, 61166, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T3_0 : srch 130 1 24415 [24415, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_1 : srch 130 1 32896 [32896, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_2 : srch 130 1 60652 [60652, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_3 : srch 130 1 40960 [40960, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_4 : srch 130 1 65440 [65440, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_5 : srch 130 1 61166 [61166, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_6 : srch 130 1 64250 [64250, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_7 : srch 130 1 43520 [43520, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_8 : srch 130 1 65450 [65450, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_9 : srch 130 1 49344 [49344, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_10 : srch 130 1 64764 [64764, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_11 : srch 130 1 52224 [52224, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_12 : srch 130 1 65484 [65484, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_13 : srch 130 1 61440 [61440, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T3_14 : srch 130 1 65520 [65520, 41120, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A3 : ∀ y ∈ L3, srch targetWord.toNat 1 y (y :: 41120 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L3, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T3_0, T3_1, T3_2, T3_3, T3_4, T3_5, T3_6, T3_7, T3_8, T3_9, T3_10, T3_11, T3_12, T3_13, T3_14]

theorem M3 : step targetWord.toNat 41120 (fun y _ => anyEq y L3) (41120 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L4 : List ℕ := [1285, 51400, 65278, 64000, 65530, 65450, 64764, 65484, 65520]

theorem T4_0 : srch 130 1 1285 [1285, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_1 : srch 130 1 51400 [51400, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_2 : srch 130 1 65278 [65278, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_3 : srch 130 1 64000 [64000, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_4 : srch 130 1 65530 [65530, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_5 : srch 130 1 65450 [65450, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_6 : srch 130 1 64764 [64764, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_7 : srch 130 1 65484 [65484, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T4_8 : srch 130 1 65520 [65520, 64250, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A4 : ∀ y ∈ L4, srch targetWord.toNat 1 y (y :: 64250 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L4, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T4_0, T4_1, T4_2, T4_3, T4_4, T4_5, T4_6, T4_7, T4_8]

theorem M4 : step targetWord.toNat 64250 (fun y _ => anyEq y L4) (64250 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L5 : List ℕ := [22015, 34816, 61132, 40960, 64240, 61166, 64250, 65450, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T5_0 : srch 130 1 22015 [22015, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_1 : srch 130 1 34816 [34816, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_2 : srch 130 1 61132 [61132, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_3 : srch 130 1 40960 [40960, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_4 : srch 130 1 64240 [64240, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_5 : srch 130 1 61166 [61166, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_6 : srch 130 1 64250 [64250, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_7 : srch 130 1 65450 [65450, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_8 : srch 130 1 49344 [49344, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_9 : srch 130 1 64764 [64764, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_10 : srch 130 1 52224 [52224, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_11 : srch 130 1 65484 [65484, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_12 : srch 130 1 61440 [61440, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T5_13 : srch 130 1 65520 [65520, 43520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A5 : ∀ y ∈ L5, srch targetWord.toNat 1 y (y :: 43520 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L5, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T5_0, T5_1, T5_2, T5_3, T5_4, T5_5, T5_6, T5_7, T5_8, T5_9, T5_10, T5_11, T5_12, T5_13]

theorem M5 : step targetWord.toNat 43520 (fun y _ => anyEq y L5) (43520 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L6 : List ℕ := [85, 52360, 65518, 61600, 65530, 65484, 65520]

theorem T6_0 : srch 130 1 85 [85, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_1 : srch 130 1 52360 [52360, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_2 : srch 130 1 65518 [65518, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_3 : srch 130 1 61600 [61600, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_4 : srch 130 1 65530 [65530, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_5 : srch 130 1 65484 [65484, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T6_6 : srch 130 1 65520 [65520, 65450, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A6 : ∀ y ∈ L6, srch targetWord.toNat 1 y (y :: 65450 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L6, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T6_0, T6_1, T6_2, T6_3, T6_4, T6_5, T6_6]

theorem M6 : step targetWord.toNat 65450 (fun y _ => anyEq y L6) (65450 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L7 : List ℕ := [8738, 48059, 12336, 62451, 13056, 65331, 21845, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T7_0 : srch 130 1 8738 [8738, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_1 : srch 130 1 48059 [48059, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_2 : srch 130 1 12336 [12336, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_3 : srch 130 1 62451 [62451, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_4 : srch 130 1 13056 [13056, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_5 : srch 130 1 65331 [65331, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_6 : srch 130 1 21845 [21845, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_7 : srch 130 1 34952 [34952, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_8 : srch 130 1 61166 [61166, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_9 : srch 130 1 41120 [41120, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_10 : srch 130 1 64250 [64250, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_11 : srch 130 1 43520 [43520, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_12 : srch 130 1 65450 [65450, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_13 : srch 130 1 49344 [49344, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_14 : srch 130 1 64764 [64764, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_15 : srch 130 1 52224 [52224, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_16 : srch 130 1 65484 [65484, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_17 : srch 130 1 61440 [61440, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T7_18 : srch 130 1 65520 [65520, 13107, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A7 : ∀ y ∈ L7, srch targetWord.toNat 1 y (y :: 13107 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L7, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T7_0, T7_1, T7_2, T7_3, T7_4, T7_5, T7_6, T7_7, T7_8, T7_9, T7_10, T7_11, T7_12, T7_13, T7_14, T7_15, T7_16, T7_17, T7_18]

theorem M7 : step targetWord.toNat 13107 (fun y _ => anyEq y L7) (13107 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L8 : List ℕ := [16191, 32896, 60138, 49152, 65472, 61166, 64250, 65450, 64764, 52224, 65484, 61440, 65520]

theorem T8_0 : srch 130 1 16191 [16191, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_1 : srch 130 1 32896 [32896, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_2 : srch 130 1 60138 [60138, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_3 : srch 130 1 49152 [49152, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_4 : srch 130 1 65472 [65472, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_5 : srch 130 1 61166 [61166, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_6 : srch 130 1 64250 [64250, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_7 : srch 130 1 65450 [65450, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_8 : srch 130 1 64764 [64764, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_9 : srch 130 1 52224 [52224, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_10 : srch 130 1 65484 [65484, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_11 : srch 130 1 61440 [61440, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T8_12 : srch 130 1 65520 [65520, 49344, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A8 : ∀ y ∈ L8, srch targetWord.toNat 1 y (y :: 49344 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L8, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T8_0, T8_1, T8_2, T8_3, T8_4, T8_5, T8_6, T8_7, T8_8, T8_9, T8_10, T8_11, T8_12]

theorem M8 : step targetWord.toNat 49344 (fun y _ => anyEq y L8) (49344 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L9 : List ℕ := [771, 43176, 65278, 64512, 65532, 65450, 65484, 65520]

theorem T9_0 : srch 130 1 771 [771, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_1 : srch 130 1 43176 [43176, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_2 : srch 130 1 65278 [65278, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_3 : srch 130 1 64512 [64512, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_4 : srch 130 1 65532 [65532, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_5 : srch 130 1 65450 [65450, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_6 : srch 130 1 65484 [65484, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T9_7 : srch 130 1 65520 [65520, 64764, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A9 : ∀ y ∈ L9, srch targetWord.toNat 1 y (y :: 64764 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L9, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T9_0, T9_1, T9_2, T9_3, T9_4, T9_5, T9_6, T9_7]

theorem M9 : step targetWord.toNat 64764 (fun y _ => anyEq y L9) (64764 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L10 : List ℕ := [13311, 34816, 61098, 49152, 64752, 61166, 64250, 65450, 64764, 65484, 61440, 65520]

theorem T10_0 : srch 130 1 13311 [13311, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_1 : srch 130 1 34816 [34816, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_2 : srch 130 1 61098 [61098, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_3 : srch 130 1 49152 [49152, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_4 : srch 130 1 64752 [64752, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_5 : srch 130 1 61166 [61166, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_6 : srch 130 1 64250 [64250, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_7 : srch 130 1 65450 [65450, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_8 : srch 130 1 64764 [64764, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_9 : srch 130 1 65484 [65484, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_10 : srch 130 1 61440 [61440, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T10_11 : srch 130 1 65520 [65520, 52224, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A10 : ∀ y ∈ L10, srch targetWord.toNat 1 y (y :: 52224 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L10, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T10_0, T10_1, T10_2, T10_3, T10_4, T10_5, T10_6, T10_7, T10_8, T10_9, T10_10, T10_11]

theorem M10 : step targetWord.toNat 52224 (fun y _ => anyEq y L10) (52224 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L11 : List ℕ := [51, 43656, 65518, 61632, 65532, 65520]

theorem T11_0 : srch 130 1 51 [51, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T11_1 : srch 130 1 43656 [43656, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T11_2 : srch 130 1 65518 [65518, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T11_3 : srch 130 1 61632 [61632, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T11_4 : srch 130 1 65532 [65532, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T11_5 : srch 130 1 65520 [65520, 65484, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A11 : ∀ y ∈ L11, srch targetWord.toNat 1 y (y :: 65484 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L11, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T11_0, T11_1, T11_2, T11_3, T11_4, T11_5]

theorem M11 : step targetWord.toNat 65484 (fun y _ => anyEq y L11) (65484 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L12 : List ℕ := [2570, 44975, 3084, 53199, 3840, 65295, 21845, 34952, 61166, 41120, 64250, 43520, 65450, 13107, 49344, 64764, 52224, 65484, 61440, 65520]

theorem T12_0 : srch 130 1 2570 [2570, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_1 : srch 130 1 44975 [44975, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_2 : srch 130 1 3084 [3084, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_3 : srch 130 1 53199 [53199, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_4 : srch 130 1 3840 [3840, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_5 : srch 130 1 65295 [65295, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_6 : srch 130 1 21845 [21845, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_7 : srch 130 1 34952 [34952, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_8 : srch 130 1 61166 [61166, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_9 : srch 130 1 41120 [41120, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_10 : srch 130 1 64250 [64250, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_11 : srch 130 1 43520 [43520, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_12 : srch 130 1 65450 [65450, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_13 : srch 130 1 13107 [13107, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_14 : srch 130 1 49344 [49344, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_15 : srch 130 1 64764 [64764, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_16 : srch 130 1 52224 [52224, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_17 : srch 130 1 65484 [65484, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_18 : srch 130 1 61440 [61440, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T12_19 : srch 130 1 65520 [65520, 3855, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A12 : ∀ y ∈ L12, srch targetWord.toNat 1 y (y :: 3855 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L12, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T12_0, T12_1, T12_2, T12_3, T12_4, T12_5, T12_6, T12_7, T12_8, T12_9, T12_10, T12_11, T12_12, T12_13, T12_14, T12_15, T12_16, T12_17, T12_18, T12_19]

theorem M12 : step targetWord.toNat 3855 (fun y _ => anyEq y L12) (3855 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L13 : List ℕ := [4095, 40960, 64170, 49152, 64716, 64250, 65450, 64764, 65484, 65520]

theorem T13_0 : srch 130 1 4095 [4095, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_1 : srch 130 1 40960 [40960, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_2 : srch 130 1 64170 [64170, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_3 : srch 130 1 49152 [49152, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_4 : srch 130 1 64716 [64716, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_5 : srch 130 1 64250 [64250, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_6 : srch 130 1 65450 [65450, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_7 : srch 130 1 64764 [64764, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_8 : srch 130 1 65484 [65484, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T13_9 : srch 130 1 65520 [65520, 61440, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A13 : ∀ y ∈ L13, srch targetWord.toNat 1 y (y :: 61440 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L13, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T13_0, T13_1, T13_2, T13_3, T13_4, T13_5, T13_6, T13_7, T13_8, T13_9]

theorem M13 : step targetWord.toNat 61440 (fun y _ => anyEq y L13) (61440 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L14 : List ℕ := [15, 43680, 65530, 52416, 65532]

theorem T14_0 : srch 130 1 15 [15, 65520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T14_1 : srch 130 1 43680 [43680, 65520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T14_2 : srch 130 1 65530 [65530, 65520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T14_3 : srch 130 1 52416 [52416, 65520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T14_4 : srch 130 1 65532 [65532, 65520, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A14 : ∀ y ∈ L14, srch targetWord.toNat 1 y (y :: 65520 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L14, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  exacts [T14_0, T14_1, T14_2, T14_3, T14_4]

theorem M14 : step targetWord.toNat 65520 (fun y _ => anyEq y L14) (65520 :: inputCols.map BitVec.toNat) = true := by decide +kernel

def L15 : List ℕ := [170, 43775, 204, 52479, 240, 61695, 21845, 34952, 61166, 41120, 64250, 43520, 65450, 13107, 49344, 64764, 52224, 65484, 3855, 61440, 65520]

theorem T15_0 : srch 130 1 170 [170, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_1 : srch 130 1 43775 [43775, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_2 : srch 130 1 204 [204, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_3 : srch 130 1 52479 [52479, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_4 : srch 130 1 240 [240, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_5 : srch 130 1 61695 [61695, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_6 : srch 130 1 21845 [21845, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_7 : srch 130 1 34952 [34952, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_8 : srch 130 1 61166 [61166, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_9 : srch 130 1 41120 [41120, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_10 : srch 130 1 64250 [64250, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_11 : srch 130 1 43520 [43520, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_12 : srch 130 1 65450 [65450, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_13 : srch 130 1 13107 [13107, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_14 : srch 130 1 49344 [49344, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_15 : srch 130 1 64764 [64764, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_16 : srch 130 1 52224 [52224, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_17 : srch 130 1 65484 [65484, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_18 : srch 130 1 3855 [3855, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_19 : srch 130 1 61440 [61440, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem T15_20 : srch 130 1 65520 [65520, 255, 43690, 52428, 61680, 65280] = true := by decide +kernel

theorem A15 : ∀ y ∈ L15, srch targetWord.toNat 1 y (y :: 255 :: inputCols.map BitVec.toNat) = true := by
  intro y hy
  simp only [L15, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [T15_0, T15_1, T15_2, T15_3, T15_4, T15_5, T15_6, T15_7, T15_8, T15_9, T15_10, T15_11, T15_12, T15_13, T15_14, T15_15, T15_16, T15_17, T15_18, T15_19, T15_20]

theorem M15 : step targetWord.toNat 255 (fun y _ => anyEq y L15) (255 :: inputCols.map BitVec.toNat) = true := by decide +kernel

theorem R : step targetWord.toNat 0 (fun z _ => anyEq z L) (inputCols.map BitVec.toNat) = true := by decide +kernel

theorem mids : ∀ zN ∈ L, ∀ z : Word16, z.toNat = zN → z ≠ targetWord → Inv inputCols z z.toNat 4 targetWord →
    ¬ Reach (z :: inputCols) 5 targetWord := by
  intro zN hz
  simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [mid_sound 21845 L0 M0 A0 (by decide), mid_sound 34952 L1 M1 A1 (by decide), mid_sound 61166 L2 M2 A2 (by decide), mid_sound 41120 L3 M3 A3 (by decide), mid_sound 64250 L4 M4 A4 (by decide), mid_sound 43520 L5 M5 A5 (by decide), mid_sound 65450 L6 M6 A6 (by decide), mid_sound 13107 L7 M7 A7 (by decide), mid_sound 49344 L8 M8 A8 (by decide), mid_sound 64764 L9 M9 A9 (by decide), mid_sound 52224 L10 M10 A10 (by decide), mid_sound 65484 L11 M11 A11 (by decide), mid_sound 3855 L12 M12 A12 (by decide), mid_sound 61440 L13 M13 A13 (by decide), mid_sound 65520 L14 M14 A14 (by decide), mid_sound 255 L15 M15 A15 (by decide)]

theorem noReach : ¬ Reach inputCols 6 targetWord := root_sound L R mids (by decide)

def C : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩

theorem lower (t : ℕ) (h : HasCircuitSize 4 (fun x : Fin 4 → Bool => (130 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 7 ≤ t := by
  by_contra! hlt
  obtain ⟨D, legal, sz, ev⟩ := h
  have hsm : HasCircuitSize 4 (fun x : Fin 4 → Bool => (130 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 6 := ⟨D, legal, by omega, ev⟩
  exact noReach (table_reach hsm (by decide) (by decide) (by decide))

end PEqualNP.Outside.V_meta_14056__k7

theorem PEqualNP.Outside.V_meta_14056__k7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (130 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 7 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (130 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 7 ≤ t :=
  ⟨⟨PEqualNP.Outside.V_meta_14056__k7.C, by simp [PEqualNP.Outside.V_meta_14056__k7.C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩, PEqualNP.Outside.V_meta_14056__k7.lower⟩
