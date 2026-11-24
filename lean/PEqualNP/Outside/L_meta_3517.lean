import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517
namespace Embed
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def inputMap (i : Fin 10) : Fin 14 :=
  ([0, 1, 2, 3, 5, 6, 7, 8, 9, 12] : List (Fin 14)).getD i.val 0

private theorem inputMap_injective : Function.Injective inputMap := by
  change ∀ a b : Fin 10, inputMap a = inputMap b → a = b
  decide +kernel

/-- Inputs go to the ten selected positions, and every gate wire shifts by four. -/
def wire (j : Nat) : Nat :=
  if h : j < 10 then (inputMap ⟨j, h⟩).val else j + 4

theorem wire_lt (j k : Nat) : wire j < 14 + k ↔ j < 10 + k := by
  by_cases h : j < 10
  · simp only [wire, dite_eq_left h]
    have hi := (inputMap ⟨j, h⟩).isLt
    omega
  · simp only [wire, dite_eq_right h]
    omega

private theorem wire_injective : Function.Injective wire := by
  intro a b he
  by_cases ha : a < 10 <;> by_cases hb : b < 10
  · have h : inputMap ⟨a, ha⟩ = inputMap ⟨b, hb⟩ :=
      Fin.ext (by simpa only [wire, dite_eq_left ha, dite_eq_left hb] using he)
    exact congrArg Fin.val (inputMap_injective h)
  · simp only [wire, dite_eq_left ha, dite_eq_right hb] at he
    have h := (inputMap ⟨a, ha⟩).isLt
    omega
  · simp only [wire, dite_eq_right ha, dite_eq_left hb] at he
    have h := (inputMap ⟨b, hb⟩).isLt
    omega
  · simp only [wire, dite_eq_right ha, dite_eq_right hb] at he
    omega

def mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩

def embed (C : Circuit) : Circuit :=
  ⟨C.gates.map mapGate, wire C.output⟩

theorem embed_size (C : Circuit) : (embed C).size = C.size := by
  simp [embed, Circuit.size]

private theorem gateAt_embed (C : Circuit) (j : Nat) (hj : j < C.gates.length) :
    gateAt (embed C) j = mapGate (gateAt C j) := by
  have hj' : j < (C.gates.map mapGate).length := by simpa using hj
  change (C.gates.map mapGate).getD j ⟨.or, []⟩ =
    mapGate (C.gates.getD j ⟨.or, []⟩)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj',
    List.getElem?_eq_getElem hj, List.getElem_map, Option.getD_some]

theorem embed_ao (C : Circuit) (h : IsAO2 10 C) : IsAO2 14 (embed C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨orig, horig, rfl⟩ :=
      List.mem_map.mp (show g ∈ C.gates.map mapGate from hg)
    exact h.1 orig horig
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [embed] using hj
    rw [gateAt_embed C j hj'] at hi
    obtain ⟨orig, horig, rfl⟩ :=
      List.mem_map.mp (show i ∈ (gateAt C j).inputs.map wire from hi)
    exact (wire_lt orig j).mpr (h.2.1 j hj' orig horig)
  · intro g hg
    obtain ⟨orig, horig, rfl⟩ :=
      List.mem_map.mp (show g ∈ C.gates.map mapGate from hg)
    simpa only [mapGate, List.length_map] using h.2.2 orig horig

theorem embed_nodup (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.Nodup) :
    ∀ g ∈ (embed C).gates, g.inputs.Nodup := by
  intro g hg
  obtain ⟨orig, horig, rfl⟩ :=
    List.mem_map.mp (show g ∈ C.gates.map mapGate from hg)
  exact (h orig horig).map wire_injective

private theorem getD_left (a b : List Bool) (i : Nat) (h : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_right (a b : List Bool) (i : Nat) (h : a.length ≤ i) :
    (a ++ b).getD i false = b.getD (i - a.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem read_ofFn {n : Nat} (f : Fin n → Bool) {i : Nat} (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h, Option.getD_some]

private theorem read_wire (x : Fin 14 → Bool) (s : List Bool) (j : Nat) :
    (List.ofFn x ++ s).getD (wire j) false =
      (List.ofFn (fun i => x (inputMap i)) ++ s).getD j false := by
  by_cases h : j < 10
  · have hi := (inputMap ⟨j, h⟩).isLt
    have hi' : (inputMap ⟨j, h⟩).val < (List.ofFn x).length := by
      simpa only [List.length_ofFn] using hi
    have hj' : j < (List.ofFn (fun i => x (inputMap i))).length := by
      simpa only [List.length_ofFn] using h
    simp only [wire, dite_eq_left h]
    rw [getD_left _ _ _ hi', getD_left _ _ _ hj', read_ofFn x hi, read_ofFn _ h]
  · have hi' : (List.ofFn x).length ≤ j + 4 := by
      simp only [List.length_ofFn]
      omega
    have hj' : (List.ofFn (fun i => x (inputMap i))).length ≤ j := by
      simp only [List.length_ofFn]
      omega
    simp only [wire, dite_eq_right h]
    rw [getD_right _ _ _ hi', getD_right _ _ _ hj']
    have hsub : j + 4 - 14 = j - 10 := by omega
    simp only [List.length_ofFn, hsub]

private def advance (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_tail (x : Fin 14 → Bool) (gs : List Gate) (s : List Bool) (o : Nat) :
    ((gs.map mapGate).foldl advance (List.ofFn x ++ s)).getD (wire o) false =
      (gs.foldl advance (List.ofFn (fun i => x (inputMap i)) ++ s)).getD o false := by
  induction gs generalizing s with
  | nil => exact read_wire x s o
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i =>
      (List.ofFn (fun i => x (inputMap i)) ++ s).getD i false)
    have hgate :
        (mapGate g).op.eval ((mapGate g).inputs.map fun i =>
          (List.ofFn x ++ s).getD i false) = b := by
      simp only [mapGate, List.map_map, b]
      congr 1
      exact List.map_congr_left (fun i _ => read_wire x s i)
    simp only [List.map_cons, List.foldl_cons, advance, hgate]
    change ((gs.map mapGate).foldl advance ((List.ofFn x ++ s) ++ [b])).getD
        (wire o) false =
      (gs.foldl advance ((List.ofFn (fun i => x (inputMap i)) ++ s) ++ [b])).getD
        o false
    simpa only [List.append_assoc] using ih (s ++ [b])

theorem embed_eval (C : Circuit) (x : Fin 14 → Bool) :
    (embed C).eval (List.ofFn x) = C.eval (List.ofFn fun i => x (inputMap i)) := by
  change ((C.gates.map mapGate).foldl advance (List.ofFn x)).getD (wire C.output) false =
    (C.gates.foldl advance (List.ofFn fun i => x (inputMap i))).getD C.output false
  simpa only [List.append_nil] using read_tail x C.gates [] C.output

end Embed
namespace Append
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def term1 (x : Fin 14 → Bool) : Bool := x 10 && ((x 0 || x 4) || x 5)
def term2 (x : Fin 14 → Bool) : Bool := x 11 && ((x 3 || x 4) || x 6)
def term3 (x : Fin 14 → Bool) : Bool := x 13 && ((x 1 || x 2) || x 4)
def extra (x : Fin 14 → Bool) : Bool := (term1 x || term2 x) || term3 x

private def edges : List (Fin 14 × Fin 14) :=
  [(0,10),(1,13),(2,13),(3,11),(4,10),(4,11),(4,13),(5,10),(6,11)]

theorem extra_eq_decide (x : Fin 14 → Bool) :
    extra x = decide (∃ u v : Fin 14, (u.val,v.val) ∈
      [(0,10),(1,13),(2,13),(3,11),(4,10),(4,11),(4,13),(5,10),(6,11)] ∧
      x u = true ∧ x v = true) := by
  have h (a b : Bool) (he : a = true ↔ b = true) : a = b := by
    cases a <;> cases b <;> simp_all
  apply h
  rw [decide_eq_true_eq]
  have hmem (u v : Fin 14) :
      (u.val,v.val) ∈ edges.map (fun e => (e.1.val,e.2.val)) ↔ (u,v) ∈ edges := by
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨a,b⟩, hab, he⟩
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj he
      have ea : a = u := Fin.ext h₁
      have eb : b = v := Fin.ext h₂
      simpa [ea, eb] using hab
    · intro huv
      exact ⟨(u,v), huv, rfl⟩
  change extra x = true ↔ ∃ u v : Fin 14,
    (u.val,v.val) ∈ edges.map (fun e => (e.1.val,e.2.val)) ∧ x u = true ∧ x v = true
  simp only [hmem]
  rw [show (∃ u v : Fin 14, (u,v) ∈ edges ∧ x u = true ∧ x v = true) ↔
        edges.any (fun e => x e.1 && x e.2) = true by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨u,v,hmem,hu,hv⟩
      exact ⟨(u,v),hmem, Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
    · rintro ⟨⟨u,v⟩,hmem,hb⟩
      exact ⟨u,v,hmem, (Bool.and_eq_true_iff.mp hb).1, (Bool.and_eq_true_iff.mp hb).2⟩]
  simp only [extra, term1, term2, term3, edges, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true_iff, Bool.and_eq_true_iff]
  tauto

private def gates (k src : Nat) : List Gate :=
  [⟨.or,[0,4]⟩, ⟨.or,[k,5]⟩, ⟨.and,[10,k+1]⟩,
   ⟨.or,[3,4]⟩, ⟨.or,[k+3,6]⟩, ⟨.and,[11,k+4]⟩,
   ⟨.or,[1,2]⟩, ⟨.or,[k+6,4]⟩, ⟨.and,[13,k+7]⟩,
   ⟨.or,[k+2,k+5]⟩, ⟨.or,[k+9,k+8]⟩, ⟨.or,[src,k+10]⟩]

private def start (C : Circuit) : Nat := 14 + C.size
private def source (C : Circuit) : Nat := if C.output < start C then C.output else start C + 8

def extend (C : Circuit) : Circuit :=
  ⟨C.gates ++ gates (start C) (source C), start C + 11⟩

theorem extend_size (C : Circuit) : (extend C).size = C.size + 12 := by
  simp [extend, Circuit.size, gates]

private theorem source_lt (C : Circuit) : source C < start C + 10 := by
  unfold source
  split <;> omega

private theorem index_cases {j : Nat} (hj : j < 12) :
    j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by
  omega

private theorem gates_property (k src j : Nat) (hk : 14 ≤ k) (hs : src < k+10)
    (hj : j < (gates k src).length) :
    let g := (gates k src).getD j ⟨.or,[]⟩
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
      ∀ i ∈ g.inputs, i < k + j := by
  have hj' : j < 12 := by simpa [gates] using hj
  rcases index_cases hj' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [gates] <;> omega

private theorem wires_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem circuit_wires_len (C : Circuit) (x : Fin 14 → Bool) :
    (C.wires (List.ofFn x)).length = start C := by
  unfold Circuit.wires start Circuit.size
  rw [wires_len, List.length_ofFn]

private theorem wires_old (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def gateValue (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem trace (gs : List Gate) (vs w : List Bool) (hlen : gs.length = vs.length)
    (hv : ∀ j < gs.length, gateValue (w ++ vs.take j) (gs.getD j ⟨.or,[]⟩) = vs.getD j false) :
    gs.foldl (fun w g => w ++ [gateValue w g]) w = w ++ vs := by
  induction gs generalizing vs w with
  | nil =>
    cases vs <;> simp_all
  | cons g gs ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have h0 : gateValue w g = v := by
        have he := hv 0 (by simp)
        simpa using he
      have hl : gs.length = vs.length := by simpa using hlen
      rw [List.foldl_cons, h0, ih vs (w ++ [v]) hl]
      · simp
      · intro j hj
        have he := hv (j+1) (by simp; omega)
        simpa [List.take_succ_cons, List.append_assoc] using he

private def values (C : Circuit) (x : Fin 14 → Bool) : List Bool :=
  [x 0 || x 4, (x 0 || x 4) || x 5, term1 x,
   x 3 || x 4, (x 3 || x 4) || x 6, term2 x,
   x 1 || x 2, (x 1 || x 2) || x 4, term3 x,
   term1 x || term2 x, extra x, C.eval (List.ofFn x) || extra x]

private theorem append_read_base (w vs : List Bool) (i : Nat) (h : i < w.length) :
    (w ++ vs).getD i false = w.getD i false := List.getD_append _ _ _ _ h

private theorem append_read_suffix (w vs : List Bool) (k j : Nat) (h : w.length = k) :
    (w ++ vs).getD (k + j) false = vs.getD j false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

private theorem append_trace (C : Circuit) (x : Fin 14 → Bool) :
    (gates (start C) (source C)).foldl (fun w g => w ++ [gateValue w g])
      (C.wires (List.ofFn x)) = C.wires (List.ofFn x) ++ values C x := by
  let w := C.wires (List.ofFn x)
  have hw : w.length = start C := circuit_wires_len C x
  have hk : 14 ≤ start C := by simp [start]
  have hinput (i : Fin 14) (vs : List Bool) : (w ++ vs).getD i.val false = x i := by
    rw [append_read_base _ _ _ (by omega)]
    change (C.gates.foldl _ (List.ofFn x)).getD i.val false = x i
    rw [wires_old _ _ _ (by rw [List.length_ofFn]; exact i.isLt),
      List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]
  have hindex (j : Nat) (vs : List Bool) :
      (w ++ vs).getD (start C + j) false = vs.getD j false :=
    append_read_suffix w vs _ _ hw
  have hraw (i : Nat) (vs : List Bool) (hi : i < 14) :
      (w ++ vs).getD i false = x ⟨i, hi⟩ := hinput ⟨i, hi⟩ vs
  have hstart (vs : List Bool) : (w ++ vs).getD (start C) false = vs.getD 0 false :=
    hindex 0 vs
  change (gates (start C) (source C)).foldl (fun w g => w ++ [gateValue w g]) w = _
  apply trace _ _ _ (by simp [gates,values])
  intro j hj
  have hj' : j < 12 := by simpa [gates] using hj
  rcases index_cases hj' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp (disch := decide) only [gates, values, List.getD_cons_zero, List.getD_cons_succ, List.take_zero,
      List.take_succ_cons, gateValue, GateOp.eval, List.map_cons, List.map_nil,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true,
      Bool.or_false, hraw, hstart, hindex, term1, term2, term3, extra]
  all_goals try rfl
  by_cases ho : C.output < start C
  · rw [source, if_pos ho, append_read_base _ _ _ (by omega)] <;> rfl
  · rw [source, if_neg ho, hindex]
    have hout : C.eval (List.ofFn x) = false := List.getD_eq_default w _ (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, hout, Bool.false_or]
    have hor (a b : Bool) : (b || (a || b)) = (a || b) := by cases a <;> cases b <;> rfl
    exact hor _ _

theorem extend_eval (C : Circuit) (x : Fin 14 → Bool) :
    (extend C).eval (List.ofFn x) = (C.eval (List.ofFn x) || extra x) := by
  unfold extend Circuit.eval Circuit.wires at *
  simp only [List.foldl_append]
  have h := append_trace C x
  change ((gates (start C) (source C)).foldl (fun w g => w ++ [gateValue w g])
    (C.wires (List.ofFn x))).getD (start C + 11) false = _
  rw [h, append_read_suffix _ _ _ _ (circuit_wires_len C x)]
  rfl

theorem extend_ok (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 14 C)
    (hnd : ∀ g ∈ C.gates, g.inputs.Nodup) :
    PEqualNP.TopForm.IsAO2 14 (extend C) ∧
      (∀ g ∈ (extend C).gates, g.inputs.Nodup) ∧
      (extend C).size = C.size + 12 ∧
      (∀ x : Fin 14 → Bool, (extend C).eval (List.ofFn x) = (C.eval (List.ofFn x) || extra x)) := by
  have hp : ∀ g ∈ gates (start C) (source C),
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
    have h := gates_property (start C) (source C) j (by simp [start]) (source_lt C) hj
    rw [List.getD_eq_getElem _ _ hj, hgj] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hr : ReadsBack 14 (extend C) := by
    intro j hj i hi
    by_cases hlt : j < C.gates.length
    · have h' : gateAt (extend C) j = gateAt C j := by
        exact List.getD_append _ _ _ _ hlt
      rw [h'] at hi
      exact hAO.2.1 j hlt i hi
    · have h' : gateAt (extend C) j =
          (gates (start C) (source C)).getD (j - C.gates.length) ⟨.or,[]⟩ := by
        exact List.getD_append_right _ _ _ _ (by omega)
      rw [h'] at hi
      have hj' : j - C.gates.length < (gates (start C) (source C)).length := by
        have hu : j < C.gates.length + (gates (start C) (source C)).length := by
          simpa [extend] using hj
        omega
      have hh := (gates_property (start C) (source C) _ (by simp [start])
        (source_lt C) hj').2.2.2 i hi
      unfold start Circuit.size at hh
      omega
  refine ⟨⟨?_, hr, ?_⟩, ?_, extend_size C, extend_eval C⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hAO.1 g h
    · exact (hp g h).1
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hAO.2.2 g h
    · exact (hp g h).2.1
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hnd g h
    · exact (hp g h).2.2

end Append
end PEqualNP.Outside.L_meta_3517

open PEqualNP.Outside.L_meta_3517

theorem PEqualNP.Outside.L_meta_3517 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro C hAO hNodup
  obtain ⟨hValid, hDistinct, hSize, hEval⟩ :=
    Append.extend_ok (Embed.embed C) (Embed.embed_ao C hAO) (Embed.embed_nodup C hNodup)
  refine ⟨Append.extend (Embed.embed C), hValid, hDistinct, ?_, ?_, ?_⟩
  · rw [hSize]
    omega
  · simp [hSize, Embed.embed_size]
  · intro x
    rw [hEval x, Embed.embed_eval, Append.extra_eq_decide]
    simp only [Embed.inputMap]
