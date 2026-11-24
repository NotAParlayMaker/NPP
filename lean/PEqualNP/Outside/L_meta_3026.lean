import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3026_aux.Basis
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩


lemma W_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x x' : Fin n → Bool)
    (hx : ∀ i, x i = true → x' i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C x' u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu h
    by_cases h1 : u < n
    · rw [W_input n C x' u h1]
      rw [W_input n C x u h1] at h
      exact hx _ h
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb] at h
        rw [W_and n C x' k hk hop a b hab ha hb]
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ih a ha (by omega) h.1, ih b hb (by omega) h.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at h
        rw [W_or n C x' k hk hop a b hab ha hb]
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact Or.inl (ih a ha (by omega) h)
        · exact Or.inr (ih b hb (by omega) h)

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

end PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux

variable {V : Type*} [DecidableEq V]

def productOn (A B T : Finset V) : Prop :=
  (∃ a ∈ A, a ∈ T) ∧ (∃ b ∈ B, b ∈ T)

theorem bottom_rectangle (A B : Finset V) (f : Finset V → Bool) (safe : V → Prop)
    (ad : Disjoint A B) (an : A.Nonempty)
    (zero : f ∅ = false)
    (factor : ∀ X Y : Finset V,
      (∀ i, i ∉ A → i ∉ B → (i ∈ X ↔ i ∈ Y)) →
      (productOn A B X ↔ productOn A B Y) → f X = f Y)
    (covered : ∀ i ∈ A ∪ B, f {i} = true ∨
      ∃ j, f {i,j} = true ∧ f {j} = false ∧ (safe i ∨ safe j))
    (both : ∀ i j, safe i → safe j → f {i,j} ≠ true) :
    ∀ a ∈ A, ∀ b ∈ B, f {a,b} = true ∧ (safe a ∨ safe b) := by
  have dis := Finset.disjoint_left.mp ad
  have monoOne (i : V) : ¬productOn A B {i} := by
    rintro ⟨⟨a,ha,hai⟩,⟨b,hb,hbi⟩⟩
    have ea := Finset.mem_singleton.mp hai
    have eb := Finset.mem_singleton.mp hbi
    exact dis (ea ▸ ha) (eb ▸ hb)
  have monoPair (i j : V) : productOn A B {i,j} ↔ (i ∈ A ∧ j ∈ B) ∨ (i ∈ B ∧ j ∈ A) := by
    simp only [productOn,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a,ha,rfl | rfl⟩,⟨b,hb,rfl | rfl⟩⟩
      all_goals first | exact (dis ha hb).elim | exact Or.inl ⟨ha,hb⟩ | exact Or.inr ⟨hb,ha⟩
    · rintro (⟨hi,hj⟩|⟨hi,hj⟩)
      · exact ⟨⟨i,hi,Or.inl rfl⟩,⟨j,hj,Or.inr rfl⟩⟩
      · exact ⟨⟨j,hj,Or.inr rfl⟩,⟨i,hi,Or.inl rfl⟩⟩
  have notOutside {i z : V} (hi : i ∈ A ∪ B) (za : z ∉ A) (zb : z ∉ B) : z ≠ i := by
    rintro rfl
    exact (Finset.mem_union.mp hi).elim za zb
  have off (i : V) (hi : i∈A∪B) : f {i}=false := by
    rw [← zero]
    apply factor
    · intro z za zb
      simp [notOutside hi za zb]
    · exact iff_of_false (monoOne i) (by simp [productOn])
  have witness (i : V) (hi : i∈A∪B) : ∃ j, productOn A B {i,j} ∧ f {i,j}=true ∧ (safe i ∨ safe j) := by
    obtain h|⟨j,hpair,hs,hh⟩ := covered i hi
    · rw [off i hi] at h; contradiction
    · refine ⟨j,?_,hpair,hh⟩
      by_contra hp
      have same : f {i,j}=f {j} := by
        apply factor
        · intro z za zb; simp [notOutside hi za zb]
        · simp [hp,monoOne]
      rw [hpair,hs] at same
      contradiction
  obtain ⟨a0,ha0⟩ := an
  obtain ⟨b0,h0,on,_⟩ := witness a0 (Finset.mem_union_left _ ha0)
  have hb0 : b0 ∈ B := ((monoPair _ _).1 h0).resolve_right (fun h => dis ha0 h.1) |>.2
  have allOn (a : V) (ha : a∈A) (b : V) (hb : b∈B) : f {a,b} = true := by
    rw [← on]
    apply factor
    · intro z za zb
      simp [notOutside (Finset.mem_union_left B ha) za zb,notOutside (Finset.mem_union_right A hb) za zb,
        notOutside (Finset.mem_union_left B ha0) za zb,notOutside (Finset.mem_union_right A hb0) za zb]
    · exact iff_of_true ((monoPair _ _).2 (Or.inl ⟨ha,hb⟩)) h0
  intro a ha b hb
  refine ⟨allOn a ha b hb,?_⟩
  by_contra! h
  obtain ⟨b',hr,_,hss⟩ := witness a (Finset.mem_union_left _ ha)
  have hb' : b' ∈ B := (((monoPair _ _).1 hr).resolve_right (fun r => dis ha r.1)).2
  have sb' := hss.resolve_left h.1
  obtain ⟨a',hr,_,hss⟩ := witness b (Finset.mem_union_right _ hb)
  have ha' : a' ∈ A := (((monoPair _ _).1 hr).resolve_left (fun r => dis r.1 hb)).2
  exact both a' b' (hss.resolve_left h.2) sb' (allOn a' ha' b' hb')


end PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux

variable {P L : Nat}

def word {N : ℕ} (T : Finset (Fin N)) (i : Fin N) : Bool := decide (i∈T)

def wval {N : ℕ} (C : Circuit) (w : ℕ) (T : Finset (Fin N)) := W N C (word T) w

def target (I : Fin P → Fin L → Prop) (x : Fin (P+L) → Bool) : Prop :=
  ∃ (p : Fin P) (l : Fin L), I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true

def below (I : Fin P → Fin L → Prop) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x, W (P+L) C x w = true → target I x

def shield (I : Fin P → Fin L → Prop) (C : Circuit) (c : ℕ) (v : Fin (P+L)) : Prop :=
  ∀ T : Finset (Fin (P+L)), wval C (P+L+c) T = true → v∈T → target I (word T)

lemma wval_mono {N : ℕ} (C : Circuit) (ha : AO N C) {x y : Finset (Fin N)}
    (hxy : x ⊆ y) {w : ℕ} (hw : w < N+C.gates.length) (h : wval C w x=true) :
    wval C w y=true := by
  apply W_mono N C ha _ _ _ w hw h
  intro i hi
  exact decide_eq_true (hxy (of_decide_eq_true hi))

lemma zero_wire {N : ℕ} (C : Circuit) (ha : AO N C) :
    ∀ w < N+C.gates.length, wval C w (∅ : Finset (Fin N))=false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    change W N C (word ∅) w=false
    by_cases h : w<N
    · rw [W_input N C _ w h]; simp [word]
    · obtain ⟨j,rfl⟩ : ∃j,w=N+j := ⟨w-N,by omega⟩
      obtain ⟨op,a,b,ins,al,bl⟩ := ha j (by omega)
      have a0 := ih a al (by omega)
      have b0 := ih b bl (by omega)
      change W N C (word ∅) a=false at a0
      change W N C (word ∅) b=false at b0
      rcases op with op|op
      · rw [W_and N C _ j (by omega) op _ _ ins al bl,a0,b0]; rfl
      · rw [W_or N C _ j (by omega) op _ _ ins al bl,a0,b0]; rfl

lemma pair_sides (I : Fin P → Fin L → Prop) (a b : Fin (P+L)) (h : target I (word {a,b})) :
    a.val < P ↔ ¬b.val < P := by
  obtain ⟨p,l,_,hp,hl⟩ := h
  have ip := of_decide_eq_true hp
  have il := of_decide_eq_true hl
  simp only [Finset.mem_insert,Finset.mem_singleton] at ip il
  have hp' : (Fin.castAdd L p).val < P := p.isLt
  have hl' : P ≤ (Fin.natAdd P l).val := by simp
  rcases ip with ip|ip <;> rcases il with il|il
  all_goals rw [ip] at hp'; rw [il] at hl'; omega

lemma shields_same_side (I : Fin P → Fin L → Prop) (C : Circuit) (c : ℕ) (hc : c<C.gates.length)
    (ha : AO (P+L) C) (z : Fin (P+L)) (lin : wval C (P+L+c) {z}=true) :
    ∀ i j, shield I C c i → shield I C c j → wval C (P+L+c) {i,j} ≠ true := by
  have opposite (v : Fin (P+L)) (hv : shield I C c v) : z.val < P ↔ ¬v.val < P := by
    apply pair_sides I z v
    apply hv _ _ (by simp)
    exact wval_mono C ha (by simp) (by omega) lin
  intro i j hi hj yes
  have a := opposite i hi
  have b := opposite j hj
  have e := pair_sides I i j (hi _ yes (by simp))
  omega

lemma partner_shield (I : Fin P → Fin L → Prop) (C : Circuit) (ha : AO (P+L) C)
    (c j w : ℕ) (hj : j<C.gates.length) (andOp : (gateAt C j).op=.and)
    (clean : below I C (P+L+j))
    (ports : (gateAt C j).inputs=[P+L+c,w] ∨ (gateAt C j).inputs=[w,P+L+c])
    (v : Fin (P+L)) (on : wval C w {v}=true) : shield I C c v := by
  intro T cf vt
  obtain ⟨_,a,b,ab,al,bl⟩ := ha j hj
  have bounds : w<P+L+j ∧ P+L+c<P+L+j := by
    rcases ports with h|h <;> rw [h] at ab <;> simp at ab <;> omega
  have wf := wval_mono C ha (Finset.singleton_subset_iff.mpr vt) (by omega) on
  apply clean
  rcases ports with h|h
  · rw [W_and _ C _ j hj andOp _ _ h bounds.2 bounds.1,Bool.and_eq_true]; exact ⟨cf,wf⟩
  · rw [W_and _ C _ j hj andOp _ _ h bounds.1 bounds.2,Bool.and_eq_true]; exact ⟨wf,cf⟩

lemma killed_same {N : ℕ} (C : Circuit) (c : ℕ) (hc : c<C.gates.length) (x : Fin N → Bool)
    (off : W N C x (N+c)=false) :
    (⟨C.gates.set c ⟨.or,[]⟩,C.output⟩ : Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let l := C.gates.take c
  let r := C.gates.drop (c+1)
  let g := C.gates[c]
  have hl : l.length=c := by simp [l,Nat.min_eq_left (Nat.le_of_lt hc)]
  have e : C.gates=l++g::r := by rw [← List.take_append_drop c C.gates,List.drop_eq_getElem_cons hc]
  let pre := l.foldl stepWire (List.ofFn x)
  have plen : pre.length = N+c := by simp [pre,foldl_stepWire_length,hl]
  have gate : g.op.eval (g.inputs.map fun i => pre.getD i false)=false := by
    change (C.gates.foldl stepWire (List.ofFn x)).getD (N+c) false = false at off
    rw [e,List.foldl_append,List.foldl_cons] at off
    change (r.foldl stepWire (stepWire pre g)).getD (N+c) false=false at off
    rw [foldl_stepWire_getD_lt r _ _ (by simp [stepWire,plen])] at off
    simpa [stepWire,List.getD_eq_getElem?_getD,← plen] using off
  change (((C.gates.set c _).foldl stepWire (List.ofFn x)).getD C.output false) = _
  rw [List.set_eq_take_append_cons_drop,if_pos hc]
  change ((l ++ ⟨.or,[]⟩::r).foldl stepWire (List.ofFn x)).getD C.output false =
    (C.gates.foldl stepWire (List.ofFn x)).getD C.output false
  rw [e,List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_cons]
  have eq : stepWire pre ⟨.or,[]⟩=stepWire pre g := by
    change pre++[false]=pre++[_]
    rw [gate]
  change (r.foldl stepWire (stepWire pre ⟨.or,[]⟩)).getD C.output false =
    (r.foldl stepWire (stepWire pre g)).getD C.output false
  rw [eq]

lemma ancestor_dirty (I : Fin P → Fin L → Prop) (C : Circuit)
    (stop : ∀ j<C.gates.length, ¬below I C (P+L+j) → ∀ w∈(gateAt C j).inputs, ¬below I C w) :
    ∀ j<C.gates.length, ¬below I C (P+L+j) →
    ∀ i, InCone (P+L) C i j → ¬below I C (P+L+i) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj dirt i h
    obtain ⟨w,hw,beginAt,earlier,e|anc⟩ := (inCone_iff _ C _ _ hj).1 h
    · have eq : P+L+i=w := by omega
      rw [eq]; exact stop j hj dirt w hw
    · apply ih (w-(P+L)) (by omega) (by omega) _ i anc
      rw [show P+L+(w-(P+L))=w from by omega]
      exact stop j hj dirt w hw


end PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux

variable {P L : Nat} (I : Fin P → Fin L → Prop) (C : Circuit) (c : Nat)

def killed : Circuit := ⟨C.gates.set c ⟨.or,[]⟩, C.output⟩

abbrev lost (p : Fin P) (l : Fin L) : Prop :=
  let u := Fin.castAdd L p
  let v := Fin.natAdd P l
  I p l ∧ wval C (P+L+c) {u}=false ∧ wval C (P+L+c) {v}=false ∧
    circuitFun (P+L) C (word {u,v})=true ∧ circuitFun (P+L) (killed C c) (word {u,v})=false

def lin (N : Nat) (C : Circuit) (c : Nat) : Finset (Fin N) :=
  Finset.univ.filter fun v => wval C (N+c) {v}=true

def points [DecidableRel I] : Finset (Fin P) :=
  Finset.univ.filter fun p => ∃ l, lost I C c p l

def lines [DecidableRel I] : Finset (Fin L) :=
  Finset.univ.filter fun l => ∃ p, lost I C c p l

def charged [DecidableRel I] : Finset (Fin (P+L)) :=
  lin (P+L) C c ∪ ((points I C c).image (Fin.castAdd L) ∪ (lines I C c).image (Fin.natAdd P))

lemma one_word {N : Nat} (a : Fin N) : (fun k : Fin N => decide (k=a)) = word {a} := by
  funext k; simp [word]

lemma two_word {N : Nat} (a b : Fin N) : (fun k : Fin N => decide (k=a ∨ k=b)) = word {a,b} := by
  funext k; simp [word]

lemma lost_on {p : Fin P} {l : Fin L} (hc : c<C.gates.length) (h : lost I C c p l) :
    wval C (P+L+c) {Fin.castAdd L p,Fin.natAdd P l}=true := by
  rcases h with ⟨_,_,_,old,new⟩
  cases on : wval C (P+L+c) {Fin.castAdd L p,Fin.natAdd P l}
  · have eq := killed_same C c hc (word {Fin.castAdd L p,Fin.natAdd P l}) on
    have bad : false=true := new.symm.trans (eq.trans old)
    contradiction
  · rfl

lemma charged_card [DecidableRel I] :
    (charged I C c).card = (lin (P+L) C c).card + (points I C c).card + (lines I C c).card := by
  classical
  let Ps := (points I C c).image (Fin.castAdd L)
  let Ls := (lines I C c).image (Fin.natAdd P)
  have ds : Disjoint Ps Ls := by
    rw [Finset.disjoint_left]
    rintro u hu hv
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨l,_,eq⟩ := Finset.mem_image.1 hv
    have h := congrArg Fin.val eq
    change P+l.val=p.val at h; omega
  have ds' : Disjoint (lin (P+L) C c) (Ps ∪ Ls) := by
    rw [Finset.disjoint_left]
    intro u hu hin
    have old := (Finset.mem_filter.1 hu).2
    rcases Finset.mem_union.1 hin with h|h
    · obtain ⟨p,pp,rfl⟩ := Finset.mem_image.1 h
      obtain ⟨l,hl⟩ := (Finset.mem_filter.1 pp).2
      exact Bool.false_ne_true (hl.2.1.symm.trans old)
    · obtain ⟨l,ll,rfl⟩ := Finset.mem_image.1 h
      obtain ⟨p,hp⟩ := (Finset.mem_filter.1 ll).2
      exact Bool.false_ne_true (hp.2.2.1.symm.trans old)
  change ((lin (P+L) C c) ∪ (Ps ∪ Ls)).card = _
  rw [Finset.card_union_of_disjoint ds',Finset.card_union_of_disjoint ds]
  have pcard : Ps.card=(points I C c).card := Finset.card_image_of_injective _ (fun x y h => by
    apply Fin.ext
    exact congrArg (fun z : Fin (P+L) => z.val) h)
  have lcard : Ls.card=(lines I C c).card := Finset.card_image_of_injective _ (fun x y h => by
    apply Fin.ext
    have eq := congrArg Fin.val h
    change P+x.val=P+y.val at eq; omega)
  rw [pcard,lcard]; omega

def partner : Prop :=
  ∀ p l, lost I C c p l → ∃ j<C.gates.length, (gateAt C j).op=.and ∧ below I C (P+L+j) ∧
    ∃ w, ((gateAt C j).inputs=[P+L+c,w] ∨ (gateAt C j).inputs=[w,P+L+c]) ∧
      (wval C w {Fin.castAdd L p}=true ∨ wval C w {Fin.natAdd P l}=true)

lemma charged_cover [DecidableRel I] (ha : AO (P+L) C) (hc : c<C.gates.length) (part : partner I C c)
    {i : Fin (P+L)} (hi : i∈charged I C c) :
    wval C (P+L+c) {i}=true ∨ ∃ j, wval C (P+L+c) {i,j}=true ∧ wval C (P+L+c) {j}=false ∧
      (shield I C c i ∨ shield I C c j) := by
  have safe (p : Fin P) (l : Fin L) (h : lost I C c p l) :
      shield I C c (Fin.castAdd L p) ∨ shield I C c (Fin.natAdd P l) := by
    obtain ⟨j,hj,op,clean,w,ports,hit⟩ := part p l h
    exact hit.imp (partner_shield I C ha c j w hj op clean ports _) (partner_shield I C ha c j w hj op clean ports _)
  rcases Finset.mem_union.1 hi with hlin|hn
  · exact Or.inl (Finset.mem_filter.1 hlin).2
  rcases Finset.mem_union.1 hn with hp|hl
  · obtain ⟨p,pp,rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨l,h⟩ := (Finset.mem_filter.1 pp).2
    exact Or.inr ⟨_,lost_on I C c hc h,h.2.2.1,safe p l h⟩
  · obtain ⟨l,ll,rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨p,h⟩ := (Finset.mem_filter.1 ll).2
    refine Or.inr ⟨Fin.castAdd L p,?_,h.2.1,(safe p l h).symm⟩
    simpa only [Finset.pair_comm (Fin.natAdd P l) (Fin.castAdd L p)] using (lost_on I C c hc h)

lemma essential_charged [DecidableRel I] (ha : AO (P+L) C) (hc : c<C.gates.length)
    (part : partner I C c) {i : Fin (P+L)} (hi : i∈charged I C c) :
    ∃ T : Finset (Fin (P+L)), wval C (P+L+c) (insert i T) ≠ wval C (P+L+c) T := by
  rcases charged_cover I C c ha hc part hi with on|⟨j,on,off,_⟩
  · refine ⟨∅,?_⟩
    rw [zero_wire C ha _ (by omega)]
    simp [on]
  · exact ⟨{j},by rw [on,off]; decide⟩

end PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.SplitCount

namespace PEqualNP.Outside.L_meta_3026_aux

def cut (N : Nat) (C : Circuit) (c : Nat) (R : Finset (Fin N)) : Prop :=
  ∃ t, InConeOrSelf N C t c ∧ ∃ A B : Finset (Fin N),
    Disjoint A B ∧ A.Nonempty ∧ A ∪ B ⊆ R ∧
    (∀ T : Finset (Fin N), wval C (N+t) T=true ↔ productOn A B T) ∧
    ∀ X Y : Finset (Fin N),
      (∀ i, i ∉ A → i ∉ B → (i ∈ X ↔ i ∈ Y)) →
      (productOn A B X ↔ productOn A B Y) → wval C (N+c) X = wval C (N+c) Y

end PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux

def band (n : Nat) (C : Circuit) (j : Nat) : Finset Nat :=
    (Finset.range C.gates.length).filter fun k => InConeOrSelf n C k j

lemma cone_lt (n : Nat) (C : Circuit) (j : Nat) : j<C.gates.length →
    ∀ i, InCone n C i j → i<j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i h
    rcases (inCone_iff n C i j hj).1 h with ⟨w,_,hn,hl,eq|prev⟩
    · omega
    · have hlt : w-n < j := by omega
      have hlen : w-n < C.gates.length := by omega
      have := ih (w-n) hlt hlen i prev
      omega

lemma cone_trans (n : Nat) (C : Circuit) (j : Nat) : j<C.gates.length →
    ∀ i k, InCone n C k i → InCone n C i j → InCone n C k j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i k ki ij
    rcases (inCone_iff n C i j hj).1 ij with ⟨w,hw,hn,hl,eq|prev⟩
    · exact (inCone_iff n C k j hj).2 ⟨w,hw,hn,hl,Or.inr (eq ▸ ki)⟩
    · exact (inCone_iff n C k j hj).2 ⟨w,hw,hn,hl,Or.inr (ih (w-n) (by omega) (by omega) i k ki prev)⟩

lemma band_mem {n : Nat} {C : Circuit} {c j : Nat} :
    j ∈ band n C c ↔ j<C.gates.length ∧ (j=c ∨ InCone n C j c) := by
  rw [band,Finset.mem_filter,Finset.mem_range]
  rfl

lemma outside_factor {n : Nat} (C : Circuit) (ha : AO n C) {c t : Nat}
    (hc : c<C.gates.length) (ht : t∈band n C c) (A B : Finset (Fin n))
    (privateReads : ∀ j∈band n C c, j∉band n C t →
      (∀ v∈A∪B,v.val∉(gateAt C j).inputs) ∧
      (∀ k∈band n C t,k≠t → n+k∉(gateAt C j).inputs))
    (X Y : Finset (Fin n)) (agree : ∀ v, v∉A → v∉B → (v∈X ↔ v∈Y))
    (same : wval C (n+t) X = wval C (n+t) Y) :
    wval C (n+c) X = wval C (n+c) Y := by
  have step (j : Nat) : j∈band n C c → j∉band n C t →
      wval C (n+j) X = wval C (n+j) Y := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj out
      have jl := (band_mem.1 hj).1
      have opEq (w : Nat) (hw : w∈(gateAt C j).inputs) (before : w<n+j) :
          wval C w X = wval C w Y := by
        by_cases raw : w<n
        · let i : Fin n := ⟨w,raw⟩
          have avoid : i ∉ A∪B := fun mem => (privateReads j hj out).1 i mem hw
          have ai := fun h : i∈A => avoid (Finset.mem_union_left _ h)
          have bi := fun h : i∈B => avoid (Finset.mem_union_right _ h)
          change W n C (word X) w = W n C (word Y) w
          rw [W_input n C _ w raw,W_input n C _ w raw]
          exact decide_eq_decide.mpr (agree i ai bi)
        · let k := w-n
          have ek : w = n+k := by dsimp [k]; omega
          have lt : k<j := by omega
          have read : n+k ∈ (gateAt C j).inputs := ek ▸ hw
          have kj := inCone_c1 n C ha k j jl read
          have kc : k∈band n C c := by
            refine band_mem.2 ⟨by omega,Or.inr ?_⟩
            rcases (band_mem.1 hj).2 with rfl|jc
            · exact kj
            · exact cone_trans n C c hc j k kj jc
          by_cases kt : k=t
          · simpa only [ek,kt] using same
          · have ko : k∉band n C t := fun mem => (privateReads j hj out).2 k mem kt read
            rw [ek]; exact ih k lt kc ko
      change W n C (word X) (n+j) = W n C (word Y) (n+j)
      rw [W_gate n C _ j jl, W_gate n C _ j jl]
      congr 1
      apply List.map_congr_left
      intro w hw
      by_cases h : w<n+j
      · simp only [if_pos h]
        exact opEq w hw h
      · simp only [if_neg h]
  rcases (band_mem.1 ht).2 with rfl|tc
  · exact same
  · apply step c (band_mem.2 ⟨hc,Or.inl rfl⟩)
    have lt := cone_lt n C c hc t tc
    have tl := (band_mem.1 ht).1
    rintro h
    rcases (band_mem.1 h).2 with eq|ct
    · omega
    · have := cone_lt n C t tl c ct
      omega

end PEqualNP.Outside.L_meta_3026_aux

namespace PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux.Basis

def core (n : ℕ) (C : Circuit) (c : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => InConeOrSelf n C j c

theorem memCore {n : ℕ} {C : Circuit} {c j : ℕ} :
    j ∈ core n C c ↔ j < C.gates.length ∧ (j = c ∨ InCone n C j c) := by
  unfold core
  rw [Finset.mem_filter,Finset.mem_range]
  rfl

theorem coreSelf {n : ℕ} {C : Circuit} {c : ℕ} (hc : c < C.gates.length) :
    c ∈ core n C c := memCore.2 ⟨hc,Or.inl rfl⟩

theorem cone_lt (n : ℕ) (C : Circuit) :
    ∀ j < C.gates.length, ∀ i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hi
    obtain ⟨w,_,hn,hl,e | he⟩ := (inCone_iff n C i j hj).1 hi
    · omega
    · have := ih (w - n) (by omega) (by omega) i he
      omega

theorem cone_trans (n : ℕ) (C : Circuit) :
    ∀ k < C.gates.length, ∀ j i, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk j i hij hjk
    obtain ⟨w,hw,hn,hl,e | h⟩ := (inCone_iff n C j k hk).1 hjk
    · exact (inCone_iff n C i k hk).2 ⟨w,hw,hn,hl,Or.inr (e ▸ hij)⟩
    · exact (inCone_iff n C i k hk).2
        ⟨w,hw,hn,hl,Or.inr (ih (w-n) (by omega) (by omega) j i hij h)⟩

theorem core_le {n : ℕ} {C : Circuit} {c j : ℕ} (hc : c < C.gates.length)
    (hj : j ∈ core n C c) : j ≤ c := by
  rcases (memCore.1 hj).2 with e|h
  · omega
  · exact (cone_lt n C c hc j h).le

theorem readLt {n : ℕ} {C : Circuit} (ha : AO n C) {j w : ℕ}
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) : w < n+j := by
  obtain ⟨_,a,b,e,ha,hb⟩ := ha j hj
  rw [e] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  omega

theorem readGateCore {n : ℕ} {C : Circuit} {c j w : ℕ}
    (ha : AO n C) (hc : c < C.gates.length) (hj : j ∈ core n C c)
    (hw : w ∈ (gateAt C j).inputs) (hn : n ≤ w) : w-n ∈ core n C c := by
  obtain ⟨hjlen,hjc⟩ := memCore.1 hj
  have hlt := readLt ha hjlen hw
  have ww : n+(w-n)=w := by omega
  have h : InCone n C (w-n) j := inCone_c1 n C ha _ j hjlen (by rwa [ww])
  refine memCore.2 ⟨by omega,Or.inr ?_⟩
  rcases hjc with rfl | hh
  · exact h
  · exact cone_trans n C c hc j _ h hh

theorem hasReader (n : ℕ) (C : Circuit) :
    ∀ j < C.gates.length, ∀ i, InCone n C i j →
      ∃ k, (k = j ∨ InCone n C k j) ∧ n+i ∈ (gateAt C k).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i hi
    obtain ⟨w,hw,hn,hl,e|he⟩ := (inCone_iff n C i j hj).1 hi
    · have ww : n+i=w := by omega
      exact ⟨j,Or.inl rfl,by rwa [ww]⟩
    · obtain ⟨k,hk,hread⟩ := ih (w-n) (by omega) (by omega) i he
      exact ⟨k,Or.inr ((inCone_iff n C k j hj).2 ⟨w,hw,hn,hl,hk⟩),hread⟩

noncomputable def raw (n : ℕ) (C : Circuit) (c : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ j ∈ core n C c, v.val ∈ (gateAt C j).inputs

theorem memRaw {n : ℕ} {C : Circuit} {c : ℕ} {v : Fin n} :
    v ∈ raw n C c ↔ ∃ j ∈ core n C c, v.val ∈ (gateAt C j).inputs := by
  classical
  simp [raw]

def slots (n : ℕ) (C : Circuit) (c : ℕ) : Finset (ℕ × Fin 2) :=
  (core n C c).product Finset.univ

def source (C : Circuit) (p : ℕ × Fin 2) : ℕ :=
  (gateAt C p.1).inputs.getD p.2.val 0

def used (n : ℕ) (C : Circuit) (c : ℕ) : Finset ℕ :=
  (slots n C c).image (source C)

theorem slot_input {n : ℕ} {C : Circuit} (ha : AO n C) {j : ℕ} (hj : j < C.gates.length)
    (i : Fin 2) : source C (j,i) ∈ (gateAt C j).inputs := by
  obtain ⟨_,a,b,hs,_,_⟩ := ha j hj
  unfold source
  simp only [hs]
  fin_cases i <;> simp

theorem input_slot {n : ℕ} {C : Circuit} (ha : AO n C) {j w : ℕ} (hj : j < C.gates.length)
    (h : w ∈ (gateAt C j).inputs) : ∃ i : Fin 2, source C (j,i) = w := by
  obtain ⟨_,a,b,hs,_,_⟩ := ha j hj
  simp only [hs,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl
  · exact ⟨0,by simp [source,hs]⟩
  · exact ⟨1,by simp [source,hs]⟩

theorem memUsed {n : ℕ} {C : Circuit} {c w : ℕ} (ha : AO n C) :
    w ∈ used n C c ↔ ∃ j ∈ core n C c, w ∈ (gateAt C j).inputs := by
  constructor
  · intro hw
    obtain ⟨⟨j,i⟩,hm,rfl⟩ := Finset.mem_image.1 hw
    have hj : j ∈ core n C c := (Finset.mem_product.1 hm).1
    exact ⟨j,hj,slot_input ha (memCore.1 hj).1 i⟩
  · rintro ⟨j,hj,hw⟩
    obtain ⟨i,hi⟩ := input_slot ha (memCore.1 hj).1 hw
    exact Finset.mem_image.2 ⟨(j,i),Finset.mem_product.2 ⟨hj,Finset.mem_univ _⟩,hi⟩

theorem used_eq {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c < C.gates.length) :
    used n C c = (raw n C c).image Fin.val ∪ ((core n C c).erase c).image (n+·) := by
  ext w
  rw [memUsed ha,Finset.mem_union]
  constructor
  · rintro ⟨j,hj,hw⟩
    by_cases h : w<n
    · exact Or.inl (Finset.mem_image.2 ⟨⟨w,h⟩,memRaw.2 ⟨j,hj,hw⟩,rfl⟩)
    · have hn : n ≤ w := by omega
      have hjle := core_le hc hj
      have hwlt := readLt ha (memCore.1 hj).1 hw
      have hb := readGateCore ha hc hj hw hn
      exact Or.inr (Finset.mem_image.2 ⟨w-n,Finset.mem_erase.2 ⟨by omega,hb⟩,by omega⟩)
  · rintro (h|h)
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 h
      exact memRaw.1 hv
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 h
      obtain ⟨hjn,hm⟩ := Finset.mem_erase.1 hj
      have hcone := ((memCore.1 hm).2).resolve_left hjn
      obtain ⟨k,hk,hs⟩ := hasReader n C c hc j hcone
      have hkl : k ≤ c := hk.elim (fun e => e.le) (fun h => (cone_lt n C c hc k h).le)
      exact ⟨k,memCore.2 ⟨by omega,hk⟩,hs⟩

theorem used_card {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c < C.gates.length) :
    (used n C c).card + 1 = (raw n C c).card + (core n C c).card := by
  have hd : Disjoint ((raw n C c).image Fin.val) (((core n C c).erase c).image (n+·)) := by
    rw [Finset.disjoint_left]
    intro w hi hj
    obtain ⟨v,_,e⟩ := Finset.mem_image.1 hi
    obtain ⟨j,_,e'⟩ := Finset.mem_image.1 hj
    have := v.isLt
    omega
  rw [used_eq ha hc,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (by intro i j h; change n+i=n+j at h; omega)]
  have h := Finset.card_erase_add_one (coreSelf (n:=n) (C:=C) hc)
  omega

theorem slot_card (n : ℕ) (C : Circuit) (c : ℕ) :
    (slots n C c).card = 2 * (core n C c).card := by
  simp [slots,Nat.mul_comm]

theorem raw_size {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c < C.gates.length) :
    (raw n C c).card ≤ (core n C c).card + 1 := by
  have h := used_card ha hc
  have hl : (used n C c).card ≤ (slots n C c).card := Finset.card_image_le
  rw [slot_card] at hl
  omega

theorem tight_slots {n : ℕ} {C : Circuit} {c : ℕ} {R : Finset (Fin n)}
    (ha : AO n C) (hc : c < C.gates.length)
    (hsub : R ⊆ raw n C c) (hsize : (core n C c).card < R.card) :
    raw n C c = R ∧ Set.InjOn (source C) (↑(slots n C c) : Set (ℕ × Fin 2)) := by
  have hR := Finset.card_le_card hsub
  have hraw := raw_size ha hc
  have heq : (raw n C c).card = (core n C c).card + 1 := by omega
  refine ⟨(Finset.eq_of_subset_of_card_le hsub (by omega)).symm,?_⟩
  apply Finset.card_image_iff.1
  have h := used_card ha hc
  change (used n C c).card = (slots n C c).card
  rw [slot_card]
  omega

end PEqualNP.Outside.L_meta_3026_aux.Tight

namespace PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux.Basis
open Relation

def Arc (n : ℕ) (C : Circuit) (c a b : ℕ) : Prop :=
  ∃ j ∈ core n C c, b = n+j ∧ a ∈ (gateAt C j).inputs

abbrev Path (n : ℕ) (C : Circuit) (c a b : ℕ) : Prop :=
  ReflTransGen (Arc n C c) a b

def Available (n : ℕ) (C : Circuit) (c w : ℕ) : Prop :=
  w<n ∨ ∃ j ∈ core n C c, w=n+j

theorem readAvailable {n : ℕ} {C : Circuit} {c j w : ℕ}
    (ha : AO n C) (hc : c < C.gates.length) (hj : j ∈ core n C c)
    (hw : w ∈ (gateAt C j).inputs) : Available n C c w := by
  by_cases h : w<n
  · exact Or.inl h
  · right
    have h' : n≤w := by omega
    exact ⟨w-n,readGateCore ha hc hj hw h',by omega⟩

theorem arc_lt {n : ℕ} {C : Circuit} {c a b : ℕ}
    (ha : AO n C) (h : Arc n C c a b) : a<b := by
  obtain ⟨j,hj,rfl,hp⟩ := h
  exact readLt ha (memCore.1 hj).1 hp

theorem path_le {n : ℕ} {C : Circuit} {c a b : ℕ}
    (ha : AO n C) (h : Path n C c a b) : a≤b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h' ih => exact ih.trans (arc_lt ha h').le

theorem arc_right_unique {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (h : Set.InjOn (source C) (↑(slots n C c) : Set (ℕ × Fin 2))) :
    Relator.RightUnique (Arc n C c) := by
  intro w a b ha' hb'
  obtain ⟨j,hj,rfl,hread1⟩ := ha'
  obtain ⟨k,hk,rfl,hread2⟩ := hb'
  obtain ⟨i,hi⟩ := input_slot ha (memCore.1 hj).1 hread1
  obtain ⟨l,hl⟩ := input_slot ha (memCore.1 hk).1 hread2
  have e := h (x₁ := (j,i)) (x₂ := (k,l)) (Finset.mem_product.2 ⟨hj,Finset.mem_univ _⟩)
    (Finset.mem_product.2 ⟨hk,Finset.mem_univ _⟩) (hi.trans hl.symm)
  exact congrArg (fun q : ℕ × Fin 2 => n+q.1) e

theorem different_reads {n : ℕ} {C : Circuit} {c j a b : ℕ}
    (hj : j ∈ core n C c) (hins : (gateAt C j).inputs = [a,b])
    (h : Set.InjOn (source C) (↑(slots n C c) : Set (ℕ × Fin 2))) : a ≠ b := by
  intro he
  have e := h (x₁ := (j,0)) (x₂ := (j,1))
    (Finset.mem_product.2 ⟨hj,Finset.mem_univ _⟩) (Finset.mem_product.2 ⟨hj,Finset.mem_univ _⟩)
    (by simpa [source,hins] using he)
  have b := congrArg Prod.snd e
  exact absurd b (by decide : (0 : Fin 2) ≠ 1)

theorem transfer_head {n : ℕ} {C : Circuit} {c a b t : ℕ}
    (hdet : Relator.RightUnique (Arc n C c)) (h : Path n C c a t)
    (hne : a≠t) (hread : Arc n C c a b) : Path n C c b t := by
  rcases h.cases_head with he | ⟨w,hw,hwt⟩
  · exact (hne he).elim
  · have e := hdet hread hw
    exact e.symm ▸ hwt

theorem gatePath {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c<C.gates.length) :
    ∀ j∈core n C c, ∀ i, InCone n C i j → Path n C c (n+i) (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj i h
    obtain ⟨w,hw,hn,hl,he|h'⟩ := (inCone_iff n C i j (memCore.1 hj).1).1 h
    · have e : n+i=w := by omega
      rw [e]
      exact ReflTransGen.single ⟨j,hj,rfl,hw⟩
    · have hp := ih (w-n) (by omega) (readGateCore ha hc hj hw hn) i h'
      have he : n+(w-n)=w := by omega
      rw [he] at hp
      exact hp.tail ⟨j,hj,rfl,hw⟩

theorem path_gate {n : ℕ} {C : Circuit} {c i j : ℕ}
    (ha : AO n C) (h : Path n C c (n+i) (n+j)) : i=j ∨ InCone n C i j := by
  have hf : ∀ w, Path n C c (n+i) w → ∃ k, w=n+k ∧ (i=k ∨ InCone n C i k) := by
    intro w h
    induction h with
    | refl => exact ⟨i,rfl,Or.inl rfl⟩
    | tail _ hstep ih =>
      obtain ⟨k,rfl,hi|hi⟩ := ih <;> obtain ⟨l,hl,rfl,hread⟩ := hstep
      · subst i
        exact ⟨l,rfl,Or.inr (inCone_c1 n C ha _ _ (memCore.1 hl).1 hread)⟩
      · exact ⟨l,rfl,Or.inr (inCone_c2 n C ha i k l (memCore.1 hl).1 hi hread)⟩
  obtain ⟨k,he,hk⟩ := hf (n+j) h
  have ke : k=j := by omega
  rwa [← ke]

theorem noOutsideReader {n : ℕ} {C : Circuit} {c t a j : ℕ}
    (ha : AO n C) (hdet : Relator.RightUnique (Arc n C c))
    (hpath : Path n C c a (n+t)) (hne : a≠n+t) (hj : j∈core n C c)
    (hout : j∉core n C t) : a∉(gateAt C j).inputs := by
  intro hread
  have hpost := transfer_head hdet hpath hne (show Arc n C c a (n+j) from ⟨j,hj,rfl,hread⟩)
  exact hout (memCore.2 ⟨(memCore.1 hj).1,path_gate ha hpost⟩)

theorem rawPathInSupport {n : ℕ} {C : Circuit} {c t : ℕ} {v : Fin n}
    (h : Path n C c v.val (n+t)) : v∈raw n C c := by
  rcases h.cases_head with he | ⟨w,hw,_⟩
  · have := v.isLt
    omega
  · obtain ⟨j,hj,_,hr⟩ := hw
    exact memRaw.2 ⟨j,hj,hr⟩

noncomputable def rawAnc (n : ℕ) (C : Circuit) (c w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => Path n C c v.val w

theorem memRawAnc {n : ℕ} {C : Circuit} {c w : ℕ} {v : Fin n} :
    v∈rawAnc n C c w ↔ Path n C c v.val w := by
  classical
  simp [rawAnc]

theorem rawAncNonempty {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c<C.gates.length) :
    ∀ w, Available n C c w → (rawAnc n C c w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (h | ⟨j,hj,rfl⟩)
    · exact ⟨⟨w,h⟩,memRawAnc.2 ReflTransGen.refl⟩
    · obtain ⟨_,a,b,hin,al,bl⟩ := ha j (memCore.1 hj).1
      have hap : a∈(gateAt C j).inputs := by simp [hin]
      obtain ⟨v,hv⟩ := ih a al (readAvailable ha hc hj hap)
      exact ⟨v,memRawAnc.2 ((memRawAnc.1 hv).tail ⟨j,hj,rfl,hap⟩)⟩

theorem rawAncDisjoint {n : ℕ} {C : Circuit} {c t a b : ℕ}
    (ha : AO n C) (hdet : Relator.RightUnique (Arc n C c)) (hne : a≠b)
    (aedge : Arc n C c a (n+t)) (bedge : Arc n C c b (n+t)) :
    Disjoint (rawAnc n C c a) (rawAnc n C c b) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have cmp := (memRawAnc.1 h1).total_of_right_unique hdet (memRawAnc.1 h2)
  rcases cmp with hab|hba
  · have hpost := path_le ha (transfer_head hdet hab hne aedge)
    have := arc_lt ha bedge
    omega
  · have hpost := path_le ha (transfer_head hdet hba hne.symm bedge)
    have := arc_lt ha aedge
    omega

end PEqualNP.Outside.L_meta_3026_aux.Tight

namespace PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux PEqualNP.Outside.L_meta_3026_aux.Basis
open Relation

theorem rawAgreement {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c<C.gates.length)
    (x y : Fin n → Bool) (hagree : ∀ v ∈ raw n C c, x v = y v) :
    ∀ j ∈ core n C c, W n C x (n+j) = W n C y (n+j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have jlen := (memCore.1 hj).1
    obtain ⟨op,a,b,hin,al,bl⟩ := ha j jlen
    have ep (w : ℕ) (hw : w ∈ (gateAt C j).inputs) : W n C x w = W n C y w := by
      by_cases hn : w<n
      · rw [W_input n C x w hn,W_input n C y w hn]
        exact hagree ⟨w,hn⟩ (memRaw.2 ⟨j,hj,hw⟩)
      · have wl := readLt ha jlen hw
        have hmem := readGateCore ha hc hj hw (by omega)
        have e := ih (w-n) (by omega) hmem
        rwa [show n+(w-n)=w by omega] at e
    have ap := ep a (by simp [hin])
    have bp := ep b (by simp [hin])
    rcases op with op | op
    · rw [W_and n C x j jlen op _ _ hin al bl,W_and n C y j jlen op _ _ hin al bl,ap,bp]
    · rw [W_or n C x j jlen op _ _ hin al bl,W_or n C y j jlen op _ _ hin al bl,ap,bp]

theorem essentialInRaw {n : ℕ} {C : Circuit} {c : ℕ} (ha : AO n C) (hc : c<C.gates.length)
    (R : Finset (Fin n))
    (he : ∀ i ∈ R, ∃ T : Finset (Fin n), wval C (n+c) (insert i T) ≠ wval C (n+c) T) :
    R ⊆ raw n C c := by
  intro v hv
  by_contra hn
  obtain ⟨T,hT⟩ := he v hv
  apply hT
  apply rawAgreement ha hc _ _ _ c (coreSelf hc)
  intro i hi
  have hne : i≠v := fun e => hn (e ▸ hi)
  simp [word,hne]

theorem splitStructure {n : ℕ} {C : Circuit} {c t a b : ℕ} {R : Finset (Fin n)}
    (ha : AO n C) (hc : c<C.gates.length) (ht : t∈core n C c)
    (hin : (gateAt C t).inputs=[a,b])
    (hraw : raw n C c = R)
    (hinj : Set.InjOn (source C) (↑(slots n C c) : Set (ℕ × Fin 2))) :
    let A := rawAnc n C c a
    let B := rawAnc n C c b
    Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧ A ∪ B ⊆ R ∧
      ∀ j ∈ core n C c, j ∉ core n C t →
        (∀ v ∈ A∪B, v.val∉(gateAt C j).inputs) ∧
        (∀ k ∈ core n C t, k≠t → n+k∉(gateAt C j).inputs) := by
  let A := rawAnc n C c a
  let B := rawAnc n C c b
  show Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧ A ∪ B ⊆ R ∧ _
  have ha' : a∈(gateAt C t).inputs := by simp [hin]
  have hb' : b∈(gateAt C t).inputs := by simp [hin]
  have ae : Arc n C c a (n+t) := ⟨t,ht,rfl,ha'⟩
  have be : Arc n C c b (n+t) := ⟨t,ht,rfl,hb'⟩
  have hdet := arc_right_unique ha hinj
  have hne := different_reads ht hin hinj
  have hp (v : Fin n) (hv : v∈A∪B) : Path n C c v.val (n+t) := by
    rcases Finset.mem_union.1 hv with hv|hv
    · exact (memRawAnc.1 hv).tail ae
    · exact (memRawAnc.1 hv).tail be
  refine ⟨rawAncDisjoint ha hdet hne ae be,
    rawAncNonempty ha hc a (readAvailable ha hc ht ha'),
    rawAncNonempty ha hc b (readAvailable ha hc ht hb'),
    ?_,?_⟩
  · intro v hv
    rw [← hraw]
    exact rawPathInSupport (hp v hv)
  · intro j hj hnot
    constructor
    · intro v hv
      exact noOutsideReader ha hdet (hp v hv) (by have := v.isLt; omega) hj hnot
    · intro k hk hkt
      have anc := ((memCore.1 hk).2).resolve_left hkt
      exact noOutsideReader ha hdet (gatePath ha hc t ht k anc) (by omega) hj hnot

end PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3026_aux PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux.Tight

lemma rawAnc_input {n : Nat} {C : Circuit} {c w : Nat} (h : w<n) (v : Fin n) :
    v ∈ rawAnc n C c w ↔ v.val=w := by
  rw [memRawAnc]
  constructor
  · intro path
    rcases path.cases_tail with eq | ⟨u,_,arc⟩
    · exact eq.symm
    · obtain ⟨j,_,hj,_⟩ := arc
      omega
  · rintro rfl; exact Relation.ReflTransGen.refl

lemma rawAnc_gate {n : Nat} {C : Circuit} {c j a b : Nat} (hj : j ∈ core n C c)
    (ins : (gateAt C j).inputs=[a,b]) (v : Fin n) :
    v ∈ rawAnc n C c (n+j) ↔ v ∈ rawAnc n C c a ∨ v ∈ rawAnc n C c b := by
  simp only [memRawAnc]
  constructor
  · intro path
    rcases path.cases_tail with eq|⟨w,pw,arc⟩
    · have h := v.isLt
      omega
    · obtain ⟨k,_,eq,read⟩ := arc
      have : k=j := by omega
      subst k
      rw [ins] at read
      rcases (by simpa using read : w=a ∨ w=b) with rfl|rfl
      · exact Or.inl pw
      · exact Or.inr pw
  · rintro (pa|pb)
    · exact pa.tail ⟨j,hj,rfl,by simp [ins]⟩
    · exact pb.tail ⟨j,hj,rfl,by simp [ins]⟩

theorem orEval {n : Nat} {C : Circuit} {c bound : Nat} (ha : AO n C) (hc : c<C.gates.length)
    (before : ∀ j ∈ core n C c, n+j < bound → (gateAt C j).op=.or)
    (T : Finset (Fin n)) :
    ∀ w, Available n C c w → w<bound →
      (wval C w T=true ↔ ∃ z ∈ rawAnc n C c w, z∈T) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro (raw|⟨j,hj,rfl⟩) lt
    · change W n C (word T) w=true ↔ _
      rw [W_input n C _ w raw]
      simp only [word,decide_eq_true_eq,rawAnc_input raw]
      constructor
      · intro h; exact ⟨⟨w,raw⟩,rfl,h⟩
      · rintro ⟨z,eq,h⟩
        have hz : z=⟨w,raw⟩ := Fin.ext eq
        exact hz ▸ h
    · have jl := (memCore.1 hj).1
      obtain ⟨_,a,b,ins,al,bl⟩ := ha j jl
      have aAvail := readAvailable ha hc hj (show a∈(gateAt C j).inputs by simp [ins])
      have bAvail := readAvailable ha hc hj (show b∈(gateAt C j).inputs by simp [ins])
      have aEq := ih a al aAvail (by omega)
      have bEq := ih b bl bAvail (by omega)
      change W n C (word T) (n+j)=true ↔ _
      rw [W_or n C (word T) j jl (before _ hj lt) a b ins al bl,Bool.or_eq_true]
      change (wval C a T=true ∨ wval C b T=true) ↔ _
      rw [aEq,bEq]
      simp only [rawAnc_gate hj ins]
      constructor
      · rintro (⟨z,h,t⟩|⟨z,h,t⟩)
        · exact ⟨z,Or.inl h,t⟩
        · exact ⟨z,Or.inr h,t⟩
      · rintro ⟨z,h|h,t⟩
        · exact Or.inl ⟨z,h,t⟩
        · exact Or.inr ⟨z,h,t⟩

theorem earliestAnd {n : Nat} {C : Circuit} {c : Nat} (ha : AO n C) (hc : c<C.gates.length)
    (nonlinear : ∃ i j : Fin n, wval C (n+c) {i,j}=true ∧ wval C (n+c) {i}=false ∧
      wval C (n+c) {j}=false) :
    ∃ t ∈ core n C c, (gateAt C t).op=.and ∧ ∀ j ∈ core n C c, j<t → (gateAt C j).op=.or := by
  classical
  by_cases hex : ∃ t, t ∈ core n C c ∧ (gateAt C t).op=.and
  · let t := Nat.find hex
    have ok := Nat.find_spec hex
    refine ⟨t,ok.1,ok.2,?_⟩
    intro j hj lt
    exact (ha j (memCore.1 hj).1).1.resolve_left (fun hand => Nat.find_min hex lt ⟨hj,hand⟩)
  · have no (j : Nat) (hj : j∈core n C c) (_ : n+j < n+c+1) : (gateAt C j).op=.or :=
      (ha j (memCore.1 hj).1).1.resolve_left (fun hand => hex ⟨j,hj,hand⟩)
    have root : Available n C c (n+c) := Or.inr ⟨c,coreSelf hc,rfl⟩
    have eq (S : Finset (Fin n)) := orEval ha hc no S _ root (by omega)
    obtain ⟨i,j,on,fi,fj⟩ := nonlinear
    obtain ⟨v,hv,one⟩ := (eq _).1 on
    rcases (by simpa using one : v=i ∨ v=j) with hi|hj
    · exact (Bool.false_ne_true (fi.symm.trans ((eq _).2 ⟨v,hv,Finset.mem_singleton.2 hi⟩))).elim
    · exact (Bool.false_ne_true (fj.symm.trans ((eq _).2 ⟨v,hv,Finset.mem_singleton.2 hj⟩))).elim

theorem essential_mem_raw {n : Nat} {C : Circuit} {c : Nat} (ha : AO n C) (hc : c<C.gates.length)
    (i : Fin n) (ess : ∃ T : Finset (Fin n), wval C (n+c) (insert i T) ≠ wval C (n+c) T) :
    i∈raw n C c := by
  by_contra absent
  obtain ⟨T,changeOut⟩ := ess
  have eq (j : Nat) : j∈core n C c → wval C (n+j) (insert i T) = wval C (n+j) T := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have jl := (memCore.1 hj).1
      change W n C _ (n+j) = W n C _ (n+j)
      rw [W_gate n C _ j jl, W_gate n C _ j jl]
      congr 1
      apply List.map_congr_left
      intro w hw
      have lt := readLt ha jl hw
      simp only [if_pos lt]
      by_cases hwraw : w<n
      · have idx : (⟨w,hwraw⟩ : Fin n) ≠ i := by
          intro e
          have read : (⟨w,hwraw⟩ : Fin n).val ∈ (gateAt C j).inputs := hw
          exact absent (memRaw.2 ⟨j,hj,e ▸ read⟩)
        rw [W_input n C _ w hwraw,W_input n C _ w hwraw]
        simp [word,idx]
      · have here := readGateCore ha hc hj hw (by omega)
        have e : w=n+(w-n) := by omega
        have hh := ih (w-n) (by omega) here
        change W n C (word (insert i T)) (n+(w-n)) = W n C (word T) (n+(w-n)) at hh
        rwa [← e] at hh
  exact changeOut (eq c (coreSelf hc))

end PEqualNP.Outside.L_meta_3026_aux.Tight

namespace PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux PEqualNP.Outside.L_meta_3026_aux.Basis

theorem cut_of_two_sides {n : ℕ} {C : Circuit} {c t a b : ℕ}
    (ha : AO n C) (hc : c<C.gates.length) (R : Finset (Fin n))
    (he : ∀ i∈R, ∃ T : Finset (Fin n), wval C (n+c) (insert i T) ≠ wval C (n+c) T)
    (hsmall : (core n C c).card < R.card)
    (ht : t∈core n C c) (hin : (gateAt C t).inputs=[a,b])
    (real : ∀ T : Finset (Fin n), wval C (n+t) T=true ↔
      productOn (rawAnc n C c a) (rawAnc n C c b) T) : cut n C c R := by
  obtain ⟨hR,hi⟩ := tight_slots ha hc (essentialInRaw ha hc R he) hsmall
  obtain ⟨hd,haN,_,hs,hports⟩ := splitStructure ha hc ht hin hR hi
  refine ⟨t,(memCore.1 ht).2,rawAnc n C c a,rawAnc n C c b,hd,haN,hs,real,?_⟩
  intro X Y hxy hp
  have heq : wval C (n+t) X = wval C (n+t) Y := Bool.eq_iff_iff.2
    ((real X).trans (hp.trans (real Y).symm))
  exact outside_factor C ha hc ht _ _ hports X Y hxy heq

theorem tightCut {n : ℕ} {C : Circuit} {c : ℕ}
    (ha : AO n C) (hc : c<C.gates.length) (R : Finset (Fin n))
    (he : ∀ i∈R, ∃ T : Finset (Fin n), wval C (n+c) (insert i T) ≠ wval C (n+c) T)
    (nonlinear : ∃ u v : Fin n,
      wval C (n+c) {u,v}=true ∧ wval C (n+c) {u}=false ∧ wval C (n+c) {v}=false)
    (hsmall : (core n C c).card < R.card) : cut n C c R := by
  obtain ⟨t,ht,hop,hbefore⟩ := earliestAnd ha hc nonlinear
  have htl := (memCore.1 ht).1
  obtain ⟨_,a,b,hin,al,bl⟩ := ha t htl
  have hA := readAvailable ha hc ht (show a∈(gateAt C t).inputs by simp [hin])
  have hB := readAvailable ha hc ht (show b∈(gateAt C t).inputs by simp [hin])
  have before : ∀ j∈core n C c, n+j<n+t → (gateAt C j).op=.or := by
    intro j hj hl
    exact hbefore j hj (by omega)
  apply cut_of_two_sides ha hc R he hsmall ht hin
  intro T
  have eA := orEval ha hc before T a hA al
  have eB := orEval ha hc before T b hB bl
  change W n C (word T) (n+t)=true ↔ productOn (rawAnc n C c a) (rawAnc n C c b) T
  rw [W_and n C _ t htl hop a b hin al bl,Bool.and_eq_true]
  exact and_congr eA eB



end PEqualNP.Outside.L_meta_3026_aux.Tight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux.Basis

namespace PEqualNP.Outside.L_meta_3026_aux

variable {P L : Nat} (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit) (c : Nat)

lemma no_cut (ao : AO (P+L) C) (hc : c<C.gates.length) (part : partner I C c)
    (stop : ∀ j<C.gates.length, ¬below I C (P+L+j) → ∀ w∈(gateAt C j).inputs, ¬below I C w)
    (dirty : ¬below I C (P+L+c)) (linear : ∃ z : Fin (P+L), wval C (P+L+c) {z}=true) :
    ¬cut (P+L) C c (charged I C c) := by
  rintro ⟨t,cone,A,B,dis,an,inside,real,factor⟩
  obtain ⟨z,zOn⟩ := linear
  have block := bottom_rectangle A B (wval C (P+L+c)) (shield I C c) dis an
    (zero_wire C ao (P+L+c) (by omega)) factor
    (fun i hi => charged_cover I C c ao hc part (inside hi))
    (shields_same_side I C c hc ao z zOn)
  have clean : below I C (P+L+t) := by
    intro x xt
    let T := Finset.univ.filter fun i => x i=true
    have eq : word T=x := by funext i; simp [word,T]
    have product := (real T).1 (show wval C (P+L+t) T=true from by
      change W (P+L) C (word T) (P+L+t)=true
      rwa [eq])
    obtain ⟨⟨a,ha,aT⟩,⟨b,hb,bT⟩⟩ := product
    obtain ⟨cf,sh⟩ := block a ha b hb
    have good : target I (word {a,b}) := sh.elim (fun h => h _ cf (by simp)) (fun h => h _ cf (by simp))
    obtain ⟨p,l,pl,hp,hl⟩ := good
    have sub : ({a,b}:Finset _) ⊆ T := Finset.insert_subset_iff.2 ⟨aT,Finset.singleton_subset_iff.2 bT⟩
    exact ⟨p,l,pl,(Finset.mem_filter.1 (sub (of_decide_eq_true hp))).2,
      (Finset.mem_filter.1 (sub (of_decide_eq_true hl))).2⟩
  rcases cone with rfl|ancestor
  · exact dirty clean
  · exact ancestor_dirty I C stop c hc dirty t ancestor clean

abbrev tightClaim (N : Nat) (C : Circuit) (c : ℕ) (R : Finset (Fin N)) :=
  AO N C → c<C.gates.length →
  (∀ i∈R, ∃ T : Finset (Fin N), wval C (N+c) (insert i T) ≠ wval C (N+c) T) →
  (∃ i j : Fin N, wval C (N+c) {i,j}=true ∧ wval C (N+c) {i}=false ∧ wval C (N+c) {j}=false) →
  ((Finset.range C.gates.length).filter fun k => InConeOrSelf N C k c).card < R.card →
  cut N C c R

theorem finish (hAO : PEqualNP.TopForm.IsAO2 (P+L) C) (hc : c<C.gates.length)
    (part : partner I C c)
    (stop : ∀ j<C.gates.length, ¬below I C (P+L+j) → ∀ w∈(gateAt C j).inputs, ¬below I C w)
    (dirty : ¬below I C (P+L+c)) (linear : ∃ z : Fin (P+L), wval C (P+L+c) {z}=true)
    (someLost : ∃ p l, lost I C c p l) (extract : tightClaim (P+L) C c (charged I C c)) :
    (lin (P+L) C c).card + (points I C c).card + (lines I C c).card ≤
    ((Finset.range C.gates.length).filter fun k => InConeOrSelf (P+L) C k c).card := by
  rw [← charged_card I C c]
  by_contra! less
  have ao := ao_of _ C hAO
  apply no_cut I C c ao hc part stop dirty linear
  apply extract ao hc (fun i hi => essential_charged I C c ao hc part hi) _ less
  obtain ⟨p,l,h⟩ := someLost
  exact ⟨Fin.castAdd L p,Fin.natAdd P l,lost_on I C c hc h,h.2.1,h.2.2.1⟩


end PEqualNP.Outside.L_meta_3026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_3026_aux.Basis PEqualNP.Outside.L_meta_3026_aux

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_3026 :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (∀ p47 : Fin Np, ∀ l48 : Fin Nl, (I p47 l48 ∧ (C.wires (List.ofFn (fun i51 : Fin (Np + Nl) => decide (i51 = Fin.castAdd Nl p47)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i52 : Fin (Np + Nl) => decide (i52 = Fin.natAdd Np l48)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i53 : Fin (Np + Nl) => decide (i53 = Fin.castAdd Nl p47 ∨ i53 = Fin.natAdd Np l48)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p47 ∨ i54 = Fin.natAdd Np l48)) = false) → ∃ j49 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ z55 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z55)).getD ((Np + Nl) + j49) false = true → ∃ p56 : Fin Np, ∃ l57 : Fin Nl, I p56 l57 ∧ z55 (Fin.castAdd Nl p56) = true ∧ z55 (Fin.natAdd Np l57) = true) ∧ ∃ w50 : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [(Np + Nl) + c, w50] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j49).inputs = [w50, (Np + Nl) + c]) ∧ ((C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p47)))).getD (w50) false = true ∨ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l48)))).getD (w50) false = true)) → (Finset.univ.filter fun v60 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i66 : Fin (Np + Nl) => decide (i66 = v60)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p61 : Fin Np => ∃ l62 : Fin Nl, (I p61 l62 ∧ (C.wires (List.ofFn (fun i67 : Fin (Np + Nl) => decide (i67 = Fin.castAdd Nl p61)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i68 : Fin (Np + Nl) => decide (i68 = Fin.natAdd Np l62)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i69 : Fin (Np + Nl) => decide (i69 = Fin.castAdd Nl p61 ∨ i69 = Fin.natAdd Np l62)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i70 : Fin (Np + Nl) => decide (i70 = Fin.castAdd Nl p61 ∨ i70 = Fin.natAdd Np l62)) = false)).card + (Finset.univ.filter fun l64 : Fin Nl => ∃ p63 : Fin Np, (I p63 l64 ∧ (C.wires (List.ofFn (fun i71 : Fin (Np + Nl) => decide (i71 = Fin.castAdd Nl p63)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i72 : Fin (Np + Nl) => decide (i72 = Fin.natAdd Np l64)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i73 : Fin (Np + Nl) => decide (i73 = Fin.castAdd Nl p63 ∨ i73 = Fin.natAdd Np l64)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i74 : Fin (Np + Nl) => decide (i74 = Fin.castAdd Nl p63 ∨ i74 = Fin.natAdd Np l64)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k65 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k65 c).card := by
  have extract : ∀ (N : Nat) (C : Circuit) (c : Nat) (R : Finset (Fin N)), tightClaim N C c R :=
    fun _ _ _ R ha hc he nonlinear hlt => PEqualNP.Outside.L_meta_3026_aux.Tight.tightCut ha hc R he nonlinear hlt
  intro P L I inst C c noFour hAO computes live stop topConditions separate hc dirty privateCone linear someLost part
  simp only [one_word,two_word] at linear someLost part ⊢
  exact finish I C c hAO hc part (fun j hj h => stop j hj (Or.inr h)) dirty linear someLost
    (extract (P+L) C c (charged I C c))
