import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_701_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The low five bits are singleton inputs, followed by the five edges and the five maximal
-- independent inputs. The edge predicate is true exactly in the middle block.
abbrev M := BitVec 15

def goalMask : M := 992

def wideMask (z : M) : Bool := let t := z.setWidth 5; (t &&& (t-1)) != 0

def price (z : M) : ℕ := if wideMask z then 1 else 2

def initial : List M := [0, 32, 64, 128, 256, 512, 1024, 1377, 2048, 4096, 6306, 8192, 11016, 16384, 22032, 24772, 32767]

def closed (B : List M) : Prop :=
  (32767 : M) ∈ B ∧ ∀ a ∈ B, ∀ b ∈ B, a &&& b ∈ B

def grow (B : List M) (v : M) := B ++ B.map (· &&& v)

theorem grow_closed {B : List M} (h : closed B) (v : M) : closed (grow B v) := by
  refine ⟨List.mem_append_left _ h.1, ?_⟩
  intro a ha b hb
  simp only [grow, List.mem_append, List.mem_map] at ha hb ⊢
  rcases ha with ha | ⟨u,hu,rfl⟩ <;> rcases hb with hb | ⟨w,hw,rfl⟩
  · exact Or.inl (h.2 _ ha _ hb)
  · exact Or.inr ⟨a &&& w, h.2 _ ha _ hw, by ac_rfl⟩
  · exact Or.inr ⟨u &&& b, h.2 _ hu _ hb, by ac_rfl⟩
  · exact Or.inr ⟨u &&& w, h.2 _ hu _ hw, by
      rw [show (u &&& v) &&& (w &&& v) = (u &&& w) &&& (v &&& v) by ac_rfl]
      simp⟩

def next (B : List M) (v : M) : List M :=
  if v ∈ B then B else (grow B v).eraseDups

theorem next_mem {B : List M} {v t : M} (h : closed B) :
    t ∈ next B v ↔ t ∈ grow B v := by
  unfold next
  split
  · rename_i hv
    constructor
    · exact List.mem_append_left _
    · intro ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ht
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
        exact h.2 b hb v hv
  · simp

theorem next_closed {B : List M} (hc : closed B) (v : M) : closed (next B v) := by
  have hg := grow_closed hc v
  exact ⟨(next_mem hc).mpr hg.1, fun a ha b hb =>
    (next_mem hc).mpr (hg.2 a ((next_mem hc).mp ha) b ((next_mem hc).mp hb))⟩

theorem initial_closed : closed initial := by
  constructor
  · decide
  · have h : initial.all (fun a => initial.all (fun b => initial.contains (a &&& b))) = true := by decide
    simpa only [List.all_eq_true, List.contains_iff_mem] using h

private abbrev F := (Fin 5 → Bool) → Bool

private def inputs : List F := (fun _ => false) :: List.ofFn (fun i x => x i)

private def cl (G : List F) (w : F) : Prop :=
  ∃ S : List F, (∀ f ∈ S, f ∈ G ++ inputs) ∧ ∀ x, w x = S.all (fun f => f x)

private def good : List F → Prop
  | [] => True
  | g :: G => (∃ u v, cl G u ∧ cl G v ∧ ∀ x, g x = (u x || v x)) ∧ good G

private theorem member {G : List F} {f : F} (h : f ∈ G ++ inputs) : cl G f :=
  ⟨[f], by simpa using h, by simp⟩

private theorem cl_congr {G : List F} {u v : F} (hu : cl G u) (h : ∀ x, v x = u x) :
    cl G v := by
  obtain ⟨S, hs, he⟩ := hu
  exact ⟨S, hs, fun x => (h x).trans (he x)⟩

private theorem cl_new (G : List F) (f : F) : cl (f :: G) f := member (by simp)

private theorem cl_mono {G : List F} {f : F} (g : F) (h : cl G f) : cl (g :: G) f := by
  obtain ⟨S, hs, he⟩ := h
  exact ⟨S, fun v hv => List.mem_cons_of_mem _ (hs v hv), he⟩

private theorem cl_true (G : List F) : cl G (fun _ => true) := ⟨[], by simp, by simp⟩

private theorem cl_false (G : List F) : cl G (fun _ => false) := member (by simp [inputs])

private theorem cl_and {G : List F} {a b : F} (ha : cl G a) (hb : cl G b) :
    cl G (fun x => a x && b x) := by
  obtain ⟨A,hA,eA⟩ := ha
  obtain ⟨B,hB,eB⟩ := hb
  exact ⟨A ++ B, fun g hg => (List.mem_append.mp hg).elim (hA g) (hB g),
    fun x => by simp [eA x, eB x]⟩

private theorem gate_and (G : List ((Fin 5 → Bool) → Bool)) (f : ℕ → (Fin 5 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    cl G (fun x => GateOp.eval GateOp.and (ins.map fun i => f i x)) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact cl_congr (cl_true G) (fun x => by simp [GateOp.eval])
  · exact cl_congr (hw i) (fun x => by simp [GateOp.eval])
  · exact cl_congr (cl_and (hw i) (hw j)) (fun x => by simp [GateOp.eval])
  · exact absurd hl (by simp only [List.length_cons]; omega)

private theorem gate_or (G : List ((Fin 5 → Bool) → Bool)) (f : ℕ → (Fin 5 → Bool) → Bool)
    (hw : ∀ k, cl G (f k)) (ins : List ℕ) (hl : ins.length ≤ 2) :
    ∃ u v, cl G u ∧ cl G v ∧
      ∀ x, GateOp.eval GateOp.or (ins.map fun i => f i x) = (u x || v x) := by
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, t⟩⟩⟩
  · exact ⟨fun _ => false, fun _ => false, cl_false G, cl_false G,
      fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f i, hw i, hw i, fun x => by simp [GateOp.eval]⟩
  · exact ⟨f i, f j, hw i, hw j, fun x => by simp [GateOp.eval]⟩
  · exact absurd hl (by simp only [List.length_cons]; omega)

def W (gs : List Gate) (x : Fin 5 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 5 → Bool) → Bool :=
  fun x => (W gs x).getD k false

private theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 5 → Bool) :
    (W gs x).length = 5 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 5 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 5 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 5 + gs.length
  · rw [ite_eq_left hk]
    show (W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, hl, hk]
  · rw [ite_eq_right hk]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (5 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

private theorem base (k : ℕ) : cl [] (wf [] k) := by
  by_cases hk : k < 5
  · apply cl_congr (member (G := []) (f := fun x => x ⟨k,hk⟩) (by interval_cases k <;> simp [inputs]))
    intro x
    interval_cases k <;> rfl
  · apply cl_congr (cl_false [])
    intro x
    simp [wf, W, List.getD_eq_getElem?_getD, hk]

private def inputMasks : Fin 5 → M := ![1377, 6306, 24772, 11016, 22032]

private def sample (j : Fin 15) (i : Fin 5) : Bool := (inputMasks i)[j.val]

private def rep (f : F) (v : M) : Prop := ∀ j : Fin 15, f (sample j) = v[j.val]

private def covers (B : List M) (S : List F) : Prop :=
  ∀ f ∈ S, ∃ a ∈ B, rep f a

private theorem cl_rep {B : List M} {G : List F} {w : F} (hc : closed B)
    (hG : covers B (G ++ inputs)) (hw : cl G w) : ∃ a ∈ B, rep w a := by
  obtain ⟨S,hS,he⟩ := hw
  have aux (T : List F) (hT : ∀ f ∈ T, f ∈ G ++ inputs) :
      ∃ a ∈ B, ∀ j : Fin 15, T.all (fun f => f (sample j)) = a[j.val] := by
    induction T with
    | nil =>
      refine ⟨32767, hc.1, ?_⟩
      intro j; fin_cases j <;> rfl
    | cons f T ih =>
      obtain ⟨a,ha,ea⟩ := hG f (hT f (by simp))
      obtain ⟨b,hb,eb⟩ := ih (fun t ht => hT t (List.mem_cons_of_mem _ ht))
      exact ⟨a &&& b, hc.2 _ ha _ hb, fun j => by simp [ea j, eb j, List.all_cons]⟩
  obtain ⟨a,ha,ea⟩ := aux S hS
  exact ⟨a,ha,fun j => (he _).trans (ea j)⟩


private theorem target_rep (w : F) (hw : ∀ x, w x = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) : rep w 992 := by
  have tab : ∀ j : Fin 15, (992 : M)[j.val] = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ sample j u = true ∧ sample j v = true := by decide
  intro j
  have h := (hw (sample j)).trans (tab j).symm
  exact Bool.eq_iff_iff.mpr h

private theorem initial_covers : covers initial inputs := by
  intro f hf
  simp only [inputs, List.mem_cons, List.mem_ofFn] at hf
  rcases hf with rfl | ⟨i,rfl⟩
  · exact ⟨0, by decide, fun _ => by simp⟩
  · exact ⟨inputMasks i, by fin_cases i <;> decide, fun _ => rfl⟩


private def sing (u i : Fin 5) : Bool := decide (i=u)

private def fWide (f : F) : Prop := ∃ u v : Fin 5, u≠v ∧ f (sing u)=true ∧ f (sing v)=true

private noncomputable def fPrice (f : F) : ℕ := by
  classical exact if fWide f then 1 else 2

private noncomputable def charge : List F → ℕ
  | [] => 0
  | g :: gs => fPrice g + charge gs

private def cap (B D : Finset ℕ) (k : ℕ) :=
  (B.filter (fun j => j<k)).card + 2*(D.filter (fun j => j<k)).card

private lemma growth (B : Finset ℕ) (k : ℕ) :
    (B.filter (fun j => j<k)).card ≤ (B.filter (fun j => j<k+1)).card :=
  Finset.card_le_card (by intro j h; obtain ⟨h,l⟩ := Finset.mem_filter.mp h; exact Finset.mem_filter.mpr ⟨h,by omega⟩)

private lemma paid (B : Finset ℕ) (k : ℕ) (hk : k ∈ B) :
    (B.filter (fun j => j<k)).card + 1 ≤ (B.filter (fun j => j<k+1)).card := by
  have h : insert k (B.filter (fun j => j<k)) ⊆ B.filter (fun j => j<k+1) := by
    intro j h
    rcases Finset.mem_insert.mp h with rfl|h
    · exact Finset.mem_filter.mpr ⟨hk,by omega⟩
    · obtain ⟨h,l⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨h,by omega⟩
  simpa [Finset.card_insert_of_notMem] using Finset.card_le_card h

private theorem inv_weight (B D : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op=.or ∨ g.op=.and) ∧ g.inputs.length≤2)
    (hwB : ∀ j g, gs[j]?=some g → g.op=.or → fWide (wf gs (5+j)) → j∈B)
    (hwD : ∀ j g, gs[j]?=some g → g.op=.or → ¬fWide (wf gs (5+j)) → j∈D) :
    ∃ G, good G ∧ charge G ≤ cap B D gs.length ∧ ∀ k, cl G (wf gs k) := by
  classical
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[],trivial,Nat.zero_le _,base⟩
  | append_singleton gs g ih =>
    have old {j : ℕ} {g' : Gate} (hj : gs[j]?=some g') :
        (gs++[g])[j]?=some g' ∧ wf (gs++[g]) (5+j) = wf gs (5+j) := by
      have lt := (List.getElem?_eq_some_iff.mp hj).1
      exact ⟨by rwa [List.getElem?_append_left lt], by rw [wf_snoc,ite_eq_right (by omega)]⟩
    obtain ⟨G,gg,gcap,gcl⟩ := ih (fun k hk => hm k (by simp [hk]))
      (fun j k hj ho hwide => hwB _ k (old hj).1 ho ((old hj).2 ▸ hwide))
      (fun j k hj ho hnarrow => hwD _ k (old hj).1 ho ((old hj).2 ▸ hnarrow))
    obtain ⟨op,hfanin⟩ := hm g (by simp)
    have sz : (gs++[g]).length=gs.length+1 := by simp
    have incB := growth B gs.length
    have incD := growth D gs.length
    rcases op with ho|ha
    · let h : F := fun x => GateOp.eval .or (g.inputs.map fun i => wf gs i x)
      have wh : wf (gs++[g]) (5+gs.length)=h := by simp [wf_snoc,ho,h]
      obtain ⟨u,v,cu,cv,ev⟩ := gate_or G (wf gs) gcl g.inputs hfanin
      refine ⟨h::G,⟨⟨u,v,cu,cv,ev⟩,gg⟩,?_,?_⟩
      · rw [sz]
        change fPrice h + charge G ≤ _
        unfold cap at gcap ⊢
        by_cases wide : fWide h
        · have mem := hwB gs.length g (by simp) ho (wh ▸ wide)
          have c := paid B _ mem
          simp only [fPrice,ite_eq_left wide]
          omega
        · have mem := hwD gs.length g (by simp) ho (wh ▸ wide)
          have c := paid D _ mem
          simp only [fPrice,ite_eq_right wide]
          omega
      · intro k
        rw [wf_snoc,ho]
        by_cases hit : k=5+gs.length
        · rw [ite_eq_left hit]
          exact cl_new _ _
        · rw [ite_eq_right hit]
          exact cl_mono _ (gcl k)
    · refine ⟨G,gg,?_,?_⟩
      · rw [sz]
        unfold cap at gcap ⊢
        omega
      · intro k
        rw [wf_snoc,ha]
        by_cases hit : k=5+gs.length
        · rw [ite_eq_left hit]
          exact gate_and G (wf gs) gcl g.inputs hfanin
        · rw [ite_eq_right hit]
          exact gcl k

private lemma singleton_rows : ∀ u i : Fin 5, sample ⟨u.val,by omega⟩ i = sing u i := by decide

private lemma fPrice_rep {f : F} {v : M} (hv : rep f v) : fPrice f = price v := by
  classical
  have row (i : Fin 5) : f (sing i) = v.getLsbD i.val := by
    have eq : sample ⟨i.val,by omega⟩ = sing i := funext (singleton_rows i)
    rw [BitVec.getLsbD_eq_getElem (by omega)]
    simpa only [eq] using hv ⟨i.val,by omega⟩
  let t := v.setWidth 5
  have eqbit (i : Fin 5) : v.getLsbD i.val = t.getLsbD i.val := by simp [t,i.isLt]
  have match5 : ∀ t : BitVec 5,
      (∃ i j : Fin 5, i≠j ∧ t.getLsbD i.val=true ∧ t.getLsbD j.val=true) ↔
      ((t &&& (t-1)) != 0) = true := by decide
  have wide_iff : fWide f ↔ (t &&& (t-1)) != 0 := by
    unfold fWide
    simpa only [row,eqbit] using match5 t
  unfold fPrice price
  change (if fWide f then 1 else 2) = (if (t &&& (t-1)) != 0 then 1 else 2)
  by_cases h : fWide f
  · rw [ite_eq_left h,ite_eq_left (wide_iff.mp h)]
  · rw [ite_eq_right h,ite_eq_right (fun hv => h (wide_iff.mpr hv))]

private theorem realize_weight (Safe : ℕ → List M → Prop)
    (advance : ∀ {k : ℕ} {B : List M} {a b : M}, Safe k B → closed B → a ∈ B → b ∈ B →
       price (a|||b) ≤ k → Safe (k-price (a|||b)) (next B (a|||b)))
    {G : List F} (hg : good G) (safe : Safe 5 initial) (small : charge G ≤ 5) :
    ∃ B, closed B ∧ covers B (G ++ inputs) ∧ Safe (5-charge G) B := by
  induction G with
  | nil => exact ⟨initial,initial_closed,initial_covers,safe⟩
  | cons g G ih =>
    change fPrice g + charge G ≤ 5 at small
    obtain ⟨⟨u,v,hu,hv,he⟩,htail⟩ := hg
    obtain ⟨B,hB,hcov,hs⟩ := ih htail (by omega)
    obtain ⟨a,ha,ea⟩ := cl_rep hB hcov hu
    obtain ⟨b,hb,eb⟩ := cl_rep hB hcov hv
    have rg : rep g (a|||b) := fun j => by simp [he _,ea j,eb j]
    have repr := fPrice_rep rg
    have hs' := advance hs hB ha hb (by omega)
    refine ⟨next B (a|||b),next_closed hB _,?_,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl|her
      · exact ⟨a|||b, (next_mem hB).mpr (List.mem_append_right _ (List.mem_map.mpr
          ⟨32767,hB.1,BitVec.allOnes_and⟩)), rg⟩
      · obtain ⟨t',ht',et⟩ := hcov t her
        exact ⟨t',(next_mem hB).mpr (List.mem_append_left _ ht'),et⟩
    · change Safe (5-(fPrice g+charge G)) _
      have eq : 5-(fPrice g+charge G) = (5-charge G)-price (a|||b) := by omega
      rwa [eq]

theorem weighted_or_lower (Safe : ℕ → List M → Prop)
    (advance : ∀ {k : ℕ} {B : List M} {a b : M}, Safe k B → closed B → a ∈ B → b ∈ B →
       price (a|||b) ≤ k → Safe (k-price (a|||b)) (next B (a|||b)))
    (exclude : ∀ {k B}, Safe k B → goalMask ∉ B) (safe : Safe 5 initial)
    (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x)=true ↔ ∃ u v : Fin 5,
      (u.val,v.val) ∈ ([(0,1),(0,2),(1,2),(0,3),(3,4)] : List (ℕ×ℕ)) ∧ x u=true ∧ x v=true)
    (B D : Finset ℕ)
    (hwB : ∀ j g, C.gates[j]?=some g → g.op=.or → fWide (wf C.gates (5+j)) → j∈B)
    (hwD : ∀ j g, C.gates[j]?=some g → g.op=.or → ¬fWide (wf C.gates (5+j)) → j∈D) :
    6 ≤ B.card + 2*D.card := by
  by_contra! low
  obtain ⟨G,gg,cs,clo⟩ := inv_weight B D C.gates (fun g mem => by
    obtain ⟨hop,hlen⟩ := mono g mem
    exact ⟨by simpa [Set.mem_insert_iff,or_comm] using hop,hlen⟩) hwB hwD
  have boundB := Finset.card_filter_le B (fun j => j < C.gates.length)
  have boundD := Finset.card_filter_le D (fun j => j < C.gates.length)
  unfold cap at cs
  obtain ⟨T,ht,cov,hs⟩ := realize_weight Safe advance gg safe (by omega)
  obtain ⟨v,hv,rv⟩ := cl_rep ht cov (clo C.output)
  have goal := target_rep (wf C.gates C.output) correct
  have eq : v=goalMask := BitVec.eq_of_getElem_eq fun i hi =>
    (rv ⟨i,hi⟩).symm.trans (goal ⟨i,hi⟩)
  exact exclude hs (eq ▸ hv)

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux.AndBound

open PEqualNP.CircuitLowerBounds

-- The join-input signature is adapted from the checked bowtie result L-meta-702.
def boundedBit (z x y : Bool) := z = true → x = true ∨ y = true

lemma bounded_gate (g : Gate) (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z x y : ℕ → Bool) (h : ∀ k, boundedBit (z k) (x k) (y k))
    (same : g.op = GateOp.and → x (g.inputs.headD 0) = y (g.inputs.headD 0)) :
    boundedBit (g.op.eval (g.inputs.map z)) (g.op.eval (g.inputs.map x)) (g.op.eval (g.inputs.map y)) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,len⟩ := hm
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at len
  cases ins with
  | nil => rcases hop with rfl|rfl <;> simp [boundedBit,GateOp.eval]
  | cons i tail =>
    cases tail with
    | nil => rcases hop with rfl|rfl <;> simpa [GateOp.eval] using h i
    | cons j rest =>
      cases rest with
      | cons l t => simp at len
      | nil =>
        have hi := h i
        have hj := h j
        rcases hop with rfl|rfl
        · have e : x i = y i := same rfl
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,
            Bool.and_true,boundedBit,Bool.and_eq_true,e] at hi hj ⊢
          tauto
        · simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,
            Bool.or_false,boundedBit,Bool.or_eq_true] at hi hj ⊢
          tauto

def joinInput (x y : Fin 5 → Bool) := fun i => x i || y i

lemma bounded_wires (gs : List Gate) (x y : Fin 5 → Bool)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (record : ∀ j g, gs[j]? = some g → g.op = GateOp.and →
      wf (gs.take j) (g.inputs.headD 0) x = wf (gs.take j) (g.inputs.headD 0) y) :
    ∀ k, boundedBit (wf gs k (joinInput x y)) (wf gs k x) (wf gs k y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k
    by_cases hk : k < 5
    · interval_cases k <;> simp [wf,W,joinInput,boundedBit]
    · simp [wf,W,List.getD_eq_getElem?_getD,hk,boundedBit]
  | append_singleton gs g ih =>
    have prev := ih (fun a ha => hm a (by simp [ha])) (by
      intro j a hj hop
      have hjl := (List.getElem?_eq_some_iff.mp hj).1
      have h := record j a (by rw [List.getElem?_append_left hjl]; exact hj) hop
      simpa [List.take_append_of_le_length (Nat.le_of_lt hjl)] using h)
    intro k
    rw [wf_snoc]
    split
    · have eq (hop : g.op = GateOp.and) := record gs.length g (by simp) hop
      exact bounded_gate g (hm g (by simp)) _ _ _ prev (by simpa using eq)
    · exact prev k

def zeroSample (r i : Fin 5) : Bool := (([17,10,18,12,20] : List ℕ).getD r.val 0).testBit i.val
abbrev hasEdge (x : Fin 5 → Bool) := ∃ u v : Fin 5, (u.val, v.val) ∈
  ([(0,1),(0,2),(1,2),(0,3),(3,4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true

lemma zero_free : ∀ r, ¬ hasEdge (zeroSample r) := by decide
lemma union_edge : ∀ r s, r ≠ s → hasEdge (joinInput (zeroSample r) (zeroSample s)) := by decide

lemma three_and (C : Circuit) (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔ hasEdge x)
    (A : Finset ℕ) (hA : ∀ j (g : Gate), C.gates[j]? = some g →
      g.op = GateOp.and → j ∈ A) : 3 ≤ A.card := by
  classical
  let sig (r : Fin 5) (j : A) : Bool := (C.gates[j.val]?).elim false
    (fun g => wf (C.gates.take j.val) (g.inputs.headD 0) (zeroSample r))
  have inj : Function.Injective sig := by
    intro r s eq
    by_contra ne
    have bw := bounded_wires C.gates (zeroSample r) (zeroSample s) (fun g hg => by
      have z := mono g hg
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using z) (by
      intro j g hj hop
      have entry := congrFun eq (⟨j,hA j g hj hop⟩ : A)
      simpa [sig,hj] using entry) C.output
    have b : C.eval (List.ofFn (joinInput (zeroSample r) (zeroSample s))) = true :=
      (correct _).mpr (union_edge r s ne)
    rcases bw b with left|right
    · exact zero_free r ((correct _).mp left)
    · exact zero_free s ((correct _).mp right)
  have cap := Fintype.card_le_of_injective _ inj
  have pow : 5 ≤ 2 ^ A.card := by simpa [Fintype.card_fun] using cap
  by_contra! h
  have b := Nat.pow_le_pow_right (by decide : 0 < 2) (show A.card ≤ 2 by omega)
  omega

end PEqualNP.Outside.L_meta_701_aux.AndBound

namespace PEqualNP.Outside.L_meta_701_aux

inductive PaidBuild : ℕ → List M → Prop
  | found {k B} (h : goalMask ∈ B) : PaidBuild k B
  | add {k B a b} (ha : a ∈ B) (hb : b ∈ B) (fresh : a ||| b ∉ B)
      (budget : price (a ||| b) ≤ k) (tail : PaidBuild (k-price (a ||| b)) (next B (a ||| b))) :
      PaidBuild k B

def Safe (k : ℕ) (B : List M) := ¬PaidBuild k B

theorem safe_exclude {k B} (h : Safe k B) : goalMask ∉ B := fun hm => h (.found hm)

theorem paid_mono {k B} (h : PaidBuild k B) {k' : ℕ} (hle : k ≤ k') : PaidBuild k' B := by
  induction h generalizing k' with
  | found hm => exact .found hm
  | add ha hb fresh budget tail ih =>
    exact .add ha hb fresh (budget.trans hle) (ih (Nat.sub_le_sub_right hle _))

theorem safe_step {k B a b} (h : Safe k B) (_hc : closed B) (ha : a ∈ B) (hb : b ∈ B)
    (hbudget : price (a ||| b) ≤ k) : Safe (k-price (a ||| b)) (next B (a ||| b)) := by
  intro hr
  by_cases hz : a ||| b ∈ B
  · rw [next,ite_eq_left hz] at hr
    exact h (paid_mono hr (Nat.sub_le _ _))
  · exact h (.add ha hb hz hbudget hr)

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

-- The five independent inputs are the pairs 04, 13, 14, 23 and 24.
-- A wire true on a singleton is true on every such pair containing that vertex.
def pairRow (r : Fin 5) : BitVec 5 := ![17, 10, 18, 12, 20] r

def admiss (x : M) : Prop := ∀ r : Fin 5,
  x.setWidth 5 &&& pairRow r ≠ 0 → x[10 + r.val] = true

lemma adm_and {x y : M} (hx : admiss x) (hy : admiss y) : admiss (x &&& y) := by
  intro r p
  rw [BitVec.setWidth_and] at p
  have a : x.setWidth 5 &&& pairRow r ≠ 0 := by
    intro h
    apply p
    rw [show (x.setWidth 5 &&& y.setWidth 5) &&& pairRow r = (x.setWidth 5 &&& pairRow r) &&& y.setWidth 5 by ac_rfl,h]
    simp
  have b : y.setWidth 5 &&& pairRow r ≠ 0 := by
    intro h
    apply p
    rw [BitVec.and_assoc,h]
    simp
  simp [BitVec.getElem_and,hx r a,hy r b]

lemma adm_or {x y : M} (hx : admiss x) (hy : admiss y) : admiss (x ||| y) := by
  intro r p
  rw [BitVec.setWidth_or,BitVec.and_or_distrib_right] at p
  by_cases a : x.setWidth 5 &&& pairRow r = 0
  · have b : y.setWidth 5 &&& pairRow r ≠ 0 := by simpa [a] using p
    simp [hy r b]
  · simp [hx r a]

def singletonWide (x : BitVec 5) : Bool := (x &&& (x - 1)) != 0

lemma sharedRow {x y : M} (hx : admiss x) (hy : admiss y)
    (wx : wideMask x) (wy : wideMask y) :
    ∃ r : Fin 5, x[10+r.val] = true ∧ y[10+r.val] = true := by
  have h : ∀ a b : BitVec 5, singletonWide a = true → singletonWide b = true →
      ∃ r : Fin 5, a &&& pairRow r ≠ 0 ∧ b &&& pairRow r ≠ 0 := by decide +kernel
  obtain ⟨r,ha,hb⟩ := h _ _ wx wy
  exact ⟨r,hx r ha,hy r hb⟩



lemma initAdm : ∀ a ∈ initial, admiss a := by
  have h : initial.all (fun a => (List.finRange 5).all fun r =>
    (a.setWidth 5 &&& pairRow r == 0) || a[10+r.val]) = true := by decide
  simp only [List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at h
  intro a ha r hn
  exact (h a ha r (by simp)).resolve_left hn

lemma moveAdm {B : List M} (hc : closed B) (hB : ∀ x ∈ B, admiss x) {z : M} (hz : admiss z) :
    ∀ x ∈ next B z, admiss x := by
  intro x hx
  rcases List.mem_append.mp ((next_mem hc).mp hx) with h | h
  · exact hB _ h
  · obtain ⟨y,hy,rfl⟩ := List.mem_map.mp h
    exact adm_and (hB _ hy) hz

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

def keeps (B : List M) (r : Fin 5) : Prop := ∀ (c : M), c ∈ B → c &&& goalMask = goalMask → (c)[10 + r.val] = true

lemma preserves_row {B : List M} (hc : closed B) {r : Fin 5} (hw : keeps B r)
    {z : M} (hz : z[10+r.val] = true) : keeps (next B z) r := by
  intro c h hg
  rcases List.mem_append.mp ((next_mem hc).mp h) with m | m
  · exact hw _ m hg
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp m
    have hge : a &&& goalMask = goalMask := by
      rw [←hg]
      have e : a &&& ((a &&& z) &&& goalMask) = (a &&& a) &&& (z &&& goalMask) := by ac_rfl
      rw [e,BitVec.and_self,BitVec.and_assoc]
    simp [hw _ ha hge,hz]

lemma keeps_excl {B : List M} {r : Fin 5} (hk : keeps B r) : goalMask ∉ B := by
  intro h
  have bad := hk _ h (by simp)
  have clear : ∀ r : Fin 5, goalMask[10+r.val] = false := by decide
  simp [clear r] at bad

lemma excludesTwo {B : List M} (hc : closed B) (hb : ∀ r : Fin 5, keeps B r)
    {z w : M} (hz : admiss z) (hzw : wideMask z) (hv : admiss w) (hvw : wideMask w) :
    goalMask ∉ next (next B z) w := by
  obtain ⟨r,hr,hs⟩ := sharedRow hz hv hzw hvw
  exact keeps_excl (preserves_row (next_closed hc _) (preserves_row hc (hb r) hr) hs)

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

def supports (a b : M) := ∀ i : Fin 15, a[i.val] = true → b[i.val] = true

lemma pos_transfer {u v : M} (hs : supports u v) (hu : u &&& goalMask = goalMask) :
    v &&& goalMask = goalMask := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hh := congrArg (fun n : M => n[i]) hu
  simp only [BitVec.getElem_and] at hh ⊢
  cases h : goalMask[i] <;> simp_all [supports]
  exact hs ⟨i,hi⟩ hh

lemma sub_or {a b c d : M} (ha : supports a c) (hb : supports b d) :
    supports (a ||| b) (c ||| d) := by
  intro i h
  simp only [BitVec.getElem_or,Bool.or_eq_true] at h ⊢
  exact h.imp (ha i) (hb i)

def noPair (B : List M) (r : Fin 5) : Prop := ∀ (a : M), a ∈ B → ∀ (b : M), b ∈ B →
  a[10+r.val] = false → b[10+r.val] = false → (a ||| b) &&& goalMask ≠ goalMask

lemma biggerOnFalse {B : List M} {z v : M} {r : Fin 5} (hc : closed B) (hz : z[10+r.val] = true)
    (hv : v ∈ next B z) (hw : v[10+r.val] = false) :
    ∃ a ∈ B, a[10+r.val] = false ∧ supports v a := by
  rcases List.mem_append.mp ((next_mem hc).mp hv) with h | h
  · exact ⟨v,h,hw,fun _ ht => ht⟩
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    refine ⟨a,ha,by simpa [hz] using hw,?_⟩
    intro i hi
    simp only [BitVec.getElem_and,Bool.and_eq_true] at hi
    exact hi.1

lemma noPair_step {B : List M} (hc : closed B) {r : Fin 5} (h : noPair B r) {z : M}
    (hz : z[10+r.val] = true) : noPair (next B z) r := by
  intro a ha b hb hfa hfb goal
  obtain ⟨a',ha',f',s'⟩ := biggerOnFalse hc hz ha hfa
  obtain ⟨b',hb',f'',s''⟩ := biggerOnFalse hc hz hb hfb
  exact h _ ha' _ hb' f' f'' (pos_transfer (sub_or s' s'') goal)

lemma noPair_covering {B : List M} {r : Fin 5} (h : noPair B r) {a b : M} (ha : a ∈ B)
    (hb : b ∈ B) (goal : (a ||| b) &&& goalMask = goalMask) : (a ||| b)[10+r.val] = true := by
  cases aa : a[10+r.val] <;> cases bb : b[10+r.val] <;> simp_all [noPair]

lemma keeps_small {B : List M} (hc : closed B) {r : Fin 5} (h : keeps B r) {z : M}
    (hz : z &&& goalMask ≠ goalMask) : keeps (next B z) r := by
  intro c hm hg
  rcases List.mem_append.mp ((next_mem hc).mp hm) with m | m
  · exact h _ m hg
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp m
    apply False.elim (hz (pos_transfer (u:=a &&& z) ?_ hg))
    intro i hi
    simp only [BitVec.getElem_and,Bool.and_eq_true] at hi
    exact hi.2

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

abbrev F5 := BitVec 5

def negRows (z : M) : F5 := (z >>> 10).setWidth 5

-- Zero rows cost nothing. One wide OR suffices as a possible payment only if all the
-- rows avoid the same two singleton vertices. Every other nonempty mask costs at least two.
def fee (s : F5) : ℕ :=
  if s == 0 then 0 else
  if (18023799 : Nat).testBit s.toNat then 1 else 2

lemma fee_pos {s : F5} (hs : s ≠ 0) : 0 < fee s := by
  simp only [fee, beq_iff_eq, hs, ite_false]
  split <;> decide

lemma fee_le_two (s : F5) : fee s ≤ 2 := by
  unfold fee
  split <;> first | decide | split <;> decide

lemma negRows_bit (z : M) (r : Fin 5) : (negRows z)[r.val] = z[10+r.val] := by
  simp only [negRows, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  exact BitVec.getLsbD_eq_getElem (by omega)

private lemma costly_keeps : ∀ p s : F5, singletonWide p = true → 2 ≤ fee s →
    ∃ r : Fin 5, s[r.val] = true ∧ p &&& pairRow r ≠ 0 := by decide +kernel

lemma fee_and_price {z : M} (legal : admiss z) (s : F5) :
    fee s ≤ price z + fee (s &&& negRows z) := by
  have hmax := fee_le_two s
  by_cases hwide : wideMask z = true
  · rw [price, ite_eq_left hwide]
    by_cases hcost : 2 ≤ fee s
    · obtain ⟨r, hr, hab⟩ := costly_keeps (z.setWidth 5) s hwide hcost
      have hnonzero : s &&& negRows z ≠ 0 := by
        intro hz
        have hbit := congrArg (fun t : F5 => t[r.val]) hz
        simp [hr, negRows_bit, legal r hab] at hbit
      have := fee_pos hnonzero
      omega
    · omega
  · rw [price, ite_eq_right hwide]
    omega

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

-- The first mask records rows where no two available false operands can cover all edges.
-- The second records rows on which every available signal covering all edges is true.
-- An OR accepting all edges can change only the second obligation. Any other OR can
-- change only the first. An AND creates no new opportunity to discharge either.
def need (B : List M) (f g : F5) : Prop :=
  (∀ r : Fin 5, f[r.val] = true → noPair B r) ∧
  (∀ r : Fin 5, g[r.val] = true → keeps B r)

def newF (f : F5) (z : M) : F5 := if z &&& goalMask == goalMask then f else f &&& negRows z
def newG (g : F5) (z : M) : F5 := if z &&& goalMask == goalMask then g &&& negRows z else g

lemma need_step {B : List M} {f g : F5} {a b : M} (hc : closed B) (hn : need B f g)
    (ha : a ∈ B) (hb : b ∈ B) :
    need (next B (a ||| b)) (newF f (a ||| b)) (newG g (a ||| b)) := by
  by_cases hg : (a ||| b) &&& goalMask = goalMask
  · unfold need newF newG
    simp only [hg,beq_self_eq_true,ite_true,BitVec.getElem_and,Bool.and_eq_true,negRows_bit]
    exact ⟨fun r hr => noPair_step hc (hn.1 r hr) (noPair_covering (hn.1 r hr) ha hb hg),
      fun r hr => preserves_row hc (hn.2 r hr.1) hr.2⟩
  · unfold need newF newG
    simp only [beq_iff_eq,hg,ite_false,BitVec.getElem_and,Bool.and_eq_true,negRows_bit]
    exact ⟨fun r hr => noPair_step hc (hn.1 r hr.1) hr.2,
      fun r hr => keeps_small hc (hn.2 r hr) hg⟩

lemma need_fee {B : List M} {f g : F5} (hg : goalMask ∈ B) (hn : need B f g) :
    fee f + fee g = 0 := by
  have clear : ∀ r : Fin 5, goalMask[10+r.val] = false := by decide
  have bit0 : ∀ r : Fin 5, (0 : F5)[r.val] = false := by decide
  have ff : f = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [bit0 ⟨i,hi⟩]
    by_contra! he
    have h := hn.1 ⟨i,hi⟩ (by simpa using he) _ hg _ hg (clear _) (clear _)
    exact h (by simp)
  have gg : g = 0 := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [bit0 ⟨i,hi⟩]
    by_contra! he
    exact keeps_excl (hn.2 ⟨i,hi⟩ (by simpa using he)) hg
  rw [ff,gg]
  decide

lemma fee_drop (f g : F5) {z : M} (h : admiss z) :
    fee f + fee g ≤ price z + (fee (newF f z) + fee (newG g z)) := by
  unfold newF newG
  split
  · have := fee_and_price h g
    omega
  · have := fee_and_price h f
    omega

lemma remaining_fee {k : ℕ} {B : List M} (existsBuild : PaidBuild k B) (hc : closed B)
    (hB : ∀ a ∈ B, admiss a) {f g : F5} (hn : need B f g) : fee f + fee g ≤ k := by
  induction existsBuild generalizing f g with
  | found h => rw [need_fee h hn]; omega
  | add ha hb _ priceok _ ih =>
    have hz := adm_or (hB _ ha) (hB _ hb)
    have htail := ih (next_closed hc _) (moveAdm hc hB hz) (need_step hc hn ha hb)
    have := fee_drop f g hz
    omega

-- Enumerate new unions only when the remaining budget can still pay both obligations.
def moves (k : ℕ) (B : List M) (f g : F5) : List M :=
  ((B.flatMap fun a => B.filterMap fun b =>
    let z := a ||| b
    if price z + fee (newF f z) + fee (newG g z) ≤ k then some z else none).eraseDups).filter (· ∉ B)

lemma mem_moves {k : ℕ} {B : List M} {f g : F5} {a b : M} (ha : a ∈ B) (hb : b ∈ B)
    (fresh : a ||| b ∉ B) (h : price (a ||| b) + fee (newF f (a ||| b)) + fee (newG g (a ||| b)) ≤ k) :
    a ||| b ∈ moves k B f g := by
  simp only [moves,List.mem_filter,List.mem_eraseDups,List.mem_flatMap,List.mem_filterMap,decide_eq_true_eq]
  exact ⟨⟨a,ha,b,hb,by simp [h]⟩,fresh⟩

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

/-- With every independent-set row still present in covering masks, a single new
union producing the goal must combine two masks zero on all five of those rows. -/
def twoRows (B : List M) : Bool :=
  let T := B.filter fun u => negRows u == 0
  T.all fun a => T.all fun b => (a ||| b) &&& goalMask != goalMask

private lemma negRows_zero {v : M} (h : ∀ r : Fin 5, v[10+r.val] = false) :
    negRows v = 0 := by
  have zero : ∀ r : Fin 5, (0 : F5)[r.val] = false := by decide
  apply BitVec.eq_of_getElem_eq
  intro i hi
  let r : Fin 5 := ⟨i,hi⟩
  exact ((negRows_bit v r).trans (h r)).trans (zero r).symm

private lemma twoRows_single {B : List M} (hc : closed B) (hk : ∀ r : Fin 5, keeps B r)
    (ok : twoRows B = true) {a b : M} (ha : a ∈ B) (hb : b ∈ B) : goalMask ∉ next B (a ||| b) := by
  intro h
  rcases List.mem_append.mp ((next_mem hc).mp h) with old|added
  · exact keeps_excl (hk 0) old
  obtain ⟨c,hm,eq⟩ := List.mem_map.mp added
  have cg : c &&& goalMask = goalMask := by rw [←eq,←BitVec.and_assoc]; simp
  have zg : (a ||| b) &&& goalMask = goalMask := by
    rw [←eq,BitVec.and_comm (a ||| b),BitVec.and_assoc,BitVec.and_self]
  have clear : ∀ r : Fin 5, goalMask[10+r.val] = false := by decide
  have zero (r : Fin 5) : a[10+r.val] = false ∧ b[10+r.val] = false := by
    have E := congrArg (fun t : M => t[10+r.val]) eq
    simpa only [BitVec.getElem_and,BitVec.getElem_or,hk r c hm cg,Bool.true_and,clear r,Bool.or_eq_false_iff] using E
  simp only [twoRows,List.all_eq_true,List.mem_filter,beq_iff_eq,bne_iff_ne] at ok
  exact ok a ⟨ha,negRows_zero (fun r => (zero r).1)⟩ b ⟨hb,negRows_zero (fun r => (zero r).2)⟩ zg

lemma wTwoRows_sound {B : List M} (hc : closed B) (adm : ∀ a ∈ B, admiss a)
    (hk : ∀ r : Fin 5, keeps B r) (ok : twoRows B = true) : Safe 2 B := by
  intro path
  cases path with
  | found h => exact keeps_excl (hk 0) h
  | @add _ _ a b ha hb _ _ tail =>
    have no := twoRows_single hc hk ok ha hb
    by_cases wide : wideMask (a ||| b) = true
    · have p : price (a ||| b) = 1 := by simp [price,wide]
      rw [p] at tail
      cases tail with
      | found h => exact no h
      | @add _ _ c d hc' hd' _ room final =>
        have wide' : wideMask (c ||| d) = true := by
          by_contra! hn
          simp [price,hn] at room
        have p' : price (c ||| d) = 1 := by simp [price,wide']
        rw [p'] at final
        have ad := adm_or (adm _ ha) (adm _ hb)
        have now := moveAdm hc adm ad
        have no' := excludesTwo hc hk ad wide (adm_or (now _ hc') (now _ hd')) wide'
        cases final with
        | found h => exact no' h
        | add _ _ _ room _ => simp [price] at room; split at room <;> omega
    · have p : price (a ||| b) = 2 := by simp [price,wide]
      rw [p] at tail
      cases tail with
      | found h => exact no h
      | add _ _ _ room _ => simp [price] at room; split at room <;> omega

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

def coloursQuick : ℕ → List M → F5 → F5 → Bool
  | 0, B, _, _ => !(B.contains goalMask)
  | 1, B, f, g => !(B.contains goalMask) && (moves 1 B f g).all fun z =>
      coloursQuick 0 (next B z) (newF f z) (newG g z)
  | k+2, B, f, g => if k == 0 && g == 31 then twoRows B else
      !(B.contains goalMask) && (moves (k+2) B f g).all fun z =>
        if wideMask z then coloursQuick (k+1) (next B z) (newF f z) (newG g z)
        else coloursQuick k (next B z) (newF f z) (newG g z)

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

lemma coloursQuick_sound (k : ℕ) (B : List M) (f g : F5) (hc : closed B)
    (hB : ∀ a ∈ B, admiss a) (hn : need B f g) (ok : coloursQuick k B f g = true) : Safe k B := by
  match k with
  | 0 =>
    intro path
    cases path with
    | found h => simp [coloursQuick,h] at ok
    | add _ _ _ budget _ => simp [price] at budget; split at budget <;> omega
  | 1 =>
    simp only [coloursQuick,Bool.and_eq_true,List.all_eq_true] at ok
    intro path
    cases path with
    | found h => simp [h] at ok
    | @add _ _ a b ha hb fresh hp tail =>
      have legal := adm_or (hB _ ha) (hB _ hb)
      have nextadm := moveAdm hc hB legal
      have nx := need_step hc hn ha hb
      have close := next_closed hc (a ||| b)
      have remain := remaining_fee tail close nextadm nx
      have hm := mem_moves ha hb fresh (f:=f) (g:=g) (k:=1) (by omega)
      have h := ok.2 _ hm
      apply coloursQuick_sound 0 _ _ _ close nextadm nx h
      have d : 1 - price (a ||| b) = 0 := by unfold price; split <;> decide
      rwa [d] at tail
  | k+2 =>
    by_cases fast : k = 0 ∧ g = 31
    · obtain ⟨rfl,rfl⟩ := fast
      have bits : ∀ r : Fin 5, (31 : F5)[r.val] = true := by decide
      exact wTwoRows_sound hc hB (fun r => hn.2 r (bits r)) (by simpa [coloursQuick] using ok)
    · have fold := ok
      simp only [coloursQuick,Bool.and_eq_true,beq_iff_eq,fast,ite_false,List.all_eq_true] at fold
      intro path
      cases path with
      | found h => simp [h] at fold
      | @add _ _ a b ha hb fresh hp tail =>
        have legal := adm_or (hB _ ha) (hB _ hb)
        have nextadm := moveAdm hc hB legal
        have nx := need_step hc hn ha hb
        have close := next_closed hc (a ||| b)
        have remain := remaining_fee tail close nextadm nx
        have hm := mem_moves ha hb fresh (f:=f) (g:=g) (k:=k+2) (by omega)
        have h := fold.2 _ hm
        by_cases hw : wideMask (a ||| b) = true
        · rw [ite_eq_left hw] at h
          apply coloursQuick_sound (k+1) _ _ _ close nextadm nx h
          simpa [price,hw] using tail
        · rw [ite_eq_right hw] at h
          apply coloursQuick_sound k _ _ _ close nextadm nx h
          simpa [price,hw] using tail
termination_by k

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

lemma initialNeed : need initial 31 31 := by
  have test : (List.finRange 5).all (fun r =>
      initial.all (fun a => initial.all fun b => a[10+r.val] || b[10+r.val] ||
        (((a ||| b) &&& goalMask) != goalMask)) &&
      initial.all (fun a => (a &&& goalMask != goalMask) || a[10+r.val])) = true := by decide +kernel
  simp only [List.all_eq_true,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne] at test
  refine ⟨?_,?_⟩
  · intro r _ a ha b hb aa bb
    have h := (test r (by simp)).1 a ha b hb
    simpa [aa,bb] using h
  · intro r _ a ha goal
    exact ((test r (by simp)).2 a ha).resolve_left (by simpa using goal)

end PEqualNP.Outside.L_meta_701_aux

namespace PEqualNP.Outside.L_meta_701_aux

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem verifiedColours : coloursQuick 5 initial 31 31 = true := by decide +kernel

end PEqualNP.Outside.L_meta_701_aux

theorem PEqualNP.Outside.L_meta_701 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) → 9 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D mono correct hA hB hD
  have ands := PEqualNP.Outside.L_meta_701_aux.AndBound.three_and C mono correct A hA
  have safe := PEqualNP.Outside.L_meta_701_aux.coloursQuick_sound 5 _ 31 31 PEqualNP.Outside.L_meta_701_aux.initial_closed PEqualNP.Outside.L_meta_701_aux.initAdm PEqualNP.Outside.L_meta_701_aux.initialNeed PEqualNP.Outside.L_meta_701_aux.verifiedColours
  have ors := PEqualNP.Outside.L_meta_701_aux.weighted_or_lower _ PEqualNP.Outside.L_meta_701_aux.safe_step PEqualNP.Outside.L_meta_701_aux.safe_exclude safe C mono correct B D hB hD
  omega
