import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- A trace records only the gates beyond the compulsory outputs.
namespace PEqualNP.Outside.L_meta_1036_aux

def Trace (base : Nat → Prop) : List Nat → Prop
  | [] => True
  | z :: prior => Trace base prior ∧ ∃ u v : Nat,
      (base u ∨ u ∈ prior) ∧ (base v ∨ v ∈ prior) ∧ (z = (u &&& v) ∨ z = (u ||| v))

theorem Trace.nil {base : Nat → Prop} : Trace base [] := True.intro

theorem Trace.add {base : Nat → Prop} {prior : List Nat} {u v z : Nat}
    (ht : Trace base prior) (hu : base u ∨ u ∈ prior) (hv : base v ∨ v ∈ prior)
    (hz : z = (u &&& v) ∨ z = (u ||| v)) : Trace base (z :: prior) :=
  ⟨ht, u, v, hu, hv, hz⟩

end PEqualNP.Outside.L_meta_1036_aux

-- Count distinct compulsory outputs as functions on all input assignments.
namespace PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

abbrev W (n : ℕ) := (Fin n → Bool) → Bool

def Good (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def Source {n : ℕ} (mask : W n → ℕ) (ws : List (W n)) (v : ℕ) : Prop :=
  v = 0 ∨ v = 255 ∨ ∃ f ∈ ws, mask f = v

def wireValue {n : ℕ} (ws : List (W n)) (g : Gate) : W n :=
  fun x => g.op.eval (g.inputs.map fun i => (ws.getD i (fun _ => false)) x)

private def appendG {n : ℕ} (ws : List (W n)) (g : Gate) :=
  ws ++ [wireValue ws g]

private def initW (n : ℕ) : List (W n) := List.ofFn (fun i x => x i)

private theorem specialize {n : ℕ} (gs : List Gate) (ws : List (W n)) (x : Fin n → Bool) :
    (gs.foldl appendG ws).map (fun f => f x) =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [appendG, List.map_append, List.map_cons, List.map_nil, wireValue]
    congr 3
    apply List.map_congr_left
    intro i _
    exact (List.getD_map ws (fun _ => false) (fun f => f x)).symm

private theorem bridge {n : ℕ} (gs : List Gate) (o : ℕ) :
    (fun x => (Circuit.mk gs o).eval (List.ofFn x)) =
      ((gs.foldl appendG (initW n)).getD o (fun _ => false)) := by
  funext x
  change (gs.foldl _ (List.ofFn x)).getD o false = _
  rw [← List.getD_map (gs.foldl appendG (initW n)) (fun _ => false) (fun f => f x), specialize]
  simp only [initW, List.map_ofFn]
  rfl

private theorem getD_choice {α : Type} (ws : List α) (i : ℕ) (d : α) :
    ws.getD i d = d ∨ ws.getD i d ∈ ws := by
  by_cases h : i < ws.length
  · right
    rw [List.getD_eq_getElem ws d h]
    exact List.getElem_mem h
  · left
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : ws.length ≤ i)]

private theorem foldCount {n : ℕ} (mask : W n → ℕ) (base : ℕ → Prop)
    (req : Finset (W n)) (h0 : base 0) (h1 : base 255)
    (hr : ∀ f ∈ req, base (mask f))
    (law : ∀ (ws : List (W n)) (g : Gate), Good g →
      ∃ u v : ℕ, Source mask ws u ∧ Source mask ws v ∧
        (mask (wireValue ws g) = (u &&& v) ∨ mask (wireValue ws g) = (u ||| v)))
    (gs : List Gate) (hg : ∀ g ∈ gs, Good g) (ws : List (W n))
    (seen : Finset (W n)) (extra : List ℕ) (ht : Trace base extra)
    (hc : ∀ f ∈ ws, f ∈ req → f ∈ seen)
    (hv : ∀ f ∈ ws, base (mask f) ∨ mask f ∈ extra) :
    ∃ (final : Finset (W n)) (out : List ℕ), Trace base out ∧
      out.length + final.card ≤ extra.length + seen.card + gs.length ∧
      (∀ f ∈ gs.foldl appendG ws, f ∈ req → f ∈ final) ∧
      (∀ f ∈ gs.foldl appendG ws, base (mask f) ∨ mask f ∈ out) := by
  classical
  induction gs generalizing ws seen extra with
  | nil => exact ⟨seen, extra, ht, by simp, hc, hv⟩
  | cons g tail ih =>
    have tailOK : ∀ g ∈ tail, Good g := fun k hk => hg k (List.mem_cons_of_mem _ hk)
    let z := wireValue ws g
    by_cases hm : z ∈ req
    · have nc : ∀ f ∈ appendG ws g, f ∈ req → f ∈ insert z seen := by
        intro f hf hreq
        rcases (show f ∈ ws ∨ f = z by simpa [appendG, z] using hf) with hold | rfl
        · exact Finset.mem_insert_of_mem (hc f hold hreq)
        · exact Finset.mem_insert_self _ _
      have nv : ∀ f ∈ appendG ws g, base (mask f) ∨ mask f ∈ extra := by
        intro f hf
        rcases (show f ∈ ws ∨ f = z by simpa [appendG, z] using hf) with hold | rfl
        · exact hv f hold
        · exact .inl (hr _ hm)
      obtain ⟨s,e,t,l,c,v⟩ := ih tailOK _ _ _ ht nc nv
      refine ⟨s,e,t,?_,c,v⟩
      have lim := Finset.card_insert_le z seen
      simp only [List.length_cons]
      omega
    · obtain ⟨u,v,hu,hv',hz⟩ := law ws g (hg g (by simp))
      have avail {i : ℕ} (hs : Source mask ws i) : base i ∨ i ∈ extra := by
        rcases hs with rfl | rfl | ⟨f,hf,rfl⟩
        · exact .inl h0
        · exact .inl h1
        · exact hv f hf
      have nt : Trace base (mask z :: extra) := .add ht (avail hu) (avail hv') hz
      have nc : ∀ f ∈ appendG ws g, f ∈ req → f ∈ seen := by
        intro f hf hreq
        rcases (show f ∈ ws ∨ f = z by simpa [appendG, z] using hf) with hold | rfl
        · exact hc f hold hreq
        · contradiction
      have nv : ∀ f ∈ appendG ws g, base (mask f) ∨ mask f ∈ (mask z :: extra) := by
        intro f hf
        rcases (show f ∈ ws ∨ f = z by simpa [appendG, z] using hf) with hold | rfl
        · exact (hv f hold).imp_right (List.mem_cons_of_mem _)
        · exact .inr (by simp)
      obtain ⟨s,e,t,l,c,v'⟩ := ih tailOK _ _ _ nt nc nv
      exact ⟨s,e,t,by simp only [List.length_cons] at l ⊢; omega,c,v'⟩

theorem short_trace {n : ℕ} (mask : W n → ℕ) (base : ℕ → Prop)
    (req : Finset (W n)) (gs : List Gate) (hg : ∀ g ∈ gs, Good g)
    (law : ∀ (ws : List (W n)) (g : Gate), Good g →
      ∃ u v : ℕ, Source mask ws u ∧ Source mask ws v ∧
        (mask (wireValue ws g) = (u &&& v) ∨ mask (wireValue ws g) = (u ||| v)))
    (h0 : base 0) (h1 : base 255) (maskFalse : mask (fun _ => false) = 0)
    (projs : ∀ i : Fin n, base (mask (fun x => x i)))
    (reqBase : ∀ f ∈ req, base (mask f))
    (noFalse : (fun _ => false) ∉ req)
    (noProj : ∀ i : Fin n, (fun x => x i : W n) ∉ req)
    (realized : ∀ f ∈ req, ∃ o : ℕ, ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = f x)
    (o : ℕ) :
    ∃ extra : List ℕ, Trace base extra ∧ extra.length + req.card ≤ gs.length ∧
      (base (mask (fun x => (Circuit.mk gs o).eval (List.ofFn x))) ∨
       mask (fun x => (Circuit.mk gs o).eval (List.ofFn x)) ∈ extra) := by
  classical
  have memInit (f : W n) (hf : f ∈ initW n) : ∃ i : Fin n, (fun x => x i : W n) = f := by
    simpa [initW, List.mem_ofFn] using hf
  obtain ⟨final,extra,ht,hlen,hc,hv⟩ :=
    foldCount mask base req h0 h1 reqBase law gs hg (initW n) ∅ [] .nil
      (by intro f hf hr; obtain ⟨i,rfl⟩ := memInit f hf; exact (noProj i hr).elim)
      (by intro f hf; obtain ⟨i,rfl⟩ := memInit f hf; exact .inl (projs i))
  have hsub : req ⊆ final := by
    intro f hf
    obtain ⟨k, hk⟩ := realized f hf
    have heq : f = (gs.foldl appendG (initW n)).getD k (fun _ => false) :=
      (funext hk).symm.trans (bridge gs k)
    have hmem := getD_choice (gs.foldl appendG (initW n)) k (fun _ => false)
    rw [← heq] at hmem
    exact hc _ (hmem.resolve_left (fun e => noFalse (e ▸ hf))) hf
  refine ⟨extra,ht,?_,?_⟩
  · have le := Finset.card_le_card hsub
    simp only [List.length_nil, Finset.card_empty, zero_add] at hlen
    omega
  · rw [bridge]
    rcases getD_choice (gs.foldl appendG (initW n)) o (fun _ => false) with h | h
    · exact .inl (by rwa [h, maskFalse])
    · exact hv _ h

end PEqualNP.Outside.L_meta_1036_aux

-- Restrict to eight inputs with exactly one selected bit in each pair.
namespace PEqualNP.Outside.L_meta_1036_aux.Witness

abbrev Input := Fin 6 → Bool

def clean (q : Fin 8) (i : Fin 6) : Bool :=
  (q.val.testBit (i.val / 2)) == (i.val % 2 == 1)

def mask (f : Input → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn (fun q : Fin 8 => f (clean q)))).toNat

end PEqualNP.Outside.L_meta_1036_aux.Witness

-- The first 21 computed wires are outputs. One further monotone output uses the sole NOT.
namespace PEqualNP.Outside.L_meta_1036_aux.Witness

open PEqualNP.CircuitLowerBounds

private def meet (a b : Bool) := [a,b].all id
private def join (a b : Bool) := [a,b].any id

private def v6 (x : Input) := join (x 0) (x 1)
private def v7 (x : Input) := join (x 2) (x 3)
private def v8 (x : Input) := join (x 4) (x 5)
private def v9 (x : Input) := meet (v6 x) (v7 x)
private def v10 (x : Input) := meet (v9 x) (v8 x)
private def v11 (x : Input) := meet (x 0) (x 1)
private def v12 (x : Input) := meet (x 2) (x 3)
private def v13 (x : Input) := meet (x 4) (x 5)
private def v14 (x : Input) := join (v11 x) (v12 x)
private def v15 (x : Input) := join (v14 x) (v13 x)
private def v16 (x : Input) := meet (x 1) (x 2)
private def v17 (x : Input) := meet (v16 x) (x 4)
private def v18 (x : Input) := meet (x 0) (x 3)
private def v19 (x : Input) := meet (v18 x) (x 4)
private def v20 (x : Input) := meet (x 0) (x 2)
private def v21 (x : Input) := meet (v20 x) (x 5)
private def v22 (x : Input) := meet (x 1) (x 3)
private def v23 (x : Input) := meet (v22 x) (x 5)
private def v24 (x : Input) := join (v17 x) (v19 x)
private def v25 (x : Input) := join (v24 x) (v21 x)
private def v26 (x : Input) := join (v25 x) (v23 x)
private def v27 (x : Input) := !(v26 x)
private def v28 (x : Input) := meet (v10 x) (v27 x)
private def v29 (x : Input) := join (v15 x) (v28 x)

def gates : List Gate :=
  [⟨.or,[0, 1]⟩, ⟨.or,[2, 3]⟩, ⟨.or,[4, 5]⟩, ⟨.and,[6, 7]⟩, ⟨.and,[9, 8]⟩, ⟨.and,[0, 1]⟩, ⟨.and,[2, 3]⟩, ⟨.and,[4, 5]⟩, ⟨.or,[11, 12]⟩, ⟨.or,[14, 13]⟩, ⟨.and,[1, 2]⟩, ⟨.and,[16, 4]⟩, ⟨.and,[0, 3]⟩, ⟨.and,[18, 4]⟩, ⟨.and,[0, 2]⟩, ⟨.and,[20, 5]⟩, ⟨.and,[1, 3]⟩, ⟨.and,[22, 5]⟩, ⟨.or,[17, 19]⟩, ⟨.or,[24, 21]⟩, ⟨.or,[25, 23]⟩, ⟨.not,[26]⟩, ⟨.and,[10, 27]⟩, ⟨.or,[15, 28]⟩]

def out (j : Fin 22) : Nat := if j.val < 21 then 6 + j.val else 29

private def values (x : Input) : List Bool :=
  [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x]

def family (j : Fin 22) (x : Input) := (values x).getD (out j) false

theorem gates_length : gates.length = 24 := rfl

theorem allowed : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 := by
  simp [gates]

theorem oneNot (i j : Fin gates.length) (hi : (gates.get i).op = GateOp.not)
    (hj : (gates.get j).op = GateOp.not) : i = j := by
  have pos (k : Fin 24) : (gates.get k).op = GateOp.not → k.val = 21 := by
    fin_cases k <;> simp [gates]
  exact Fin.ext ((pos i hi).trans (pos j hj).symm)

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxHeartbeats 3000000 in
private theorem list_eval (x : Input) : gates.foldl step (List.ofFn x) = values x := by
  let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
  have inputs : List.ofFn x = w6 := rfl
  let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x]
  have g6 : step w6 ⟨.or,[0, 1]⟩ = w7 := rfl
  let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x]
  have g7 : step w7 ⟨.or,[2, 3]⟩ = w8 := rfl
  let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x]
  have g8 : step w8 ⟨.or,[4, 5]⟩ = w9 := rfl
  let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x]
  have g9 : step w9 ⟨.and,[6, 7]⟩ = w10 := rfl
  let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x]
  have g10 : step w10 ⟨.and,[9, 8]⟩ = w11 := rfl
  let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x]
  have g11 : step w11 ⟨.and,[0, 1]⟩ = w12 := rfl
  let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x]
  have g12 : step w12 ⟨.and,[2, 3]⟩ = w13 := rfl
  let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x]
  have g13 : step w13 ⟨.and,[4, 5]⟩ = w14 := rfl
  let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x]
  have g14 : step w14 ⟨.or,[11, 12]⟩ = w15 := rfl
  let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x]
  have g15 : step w15 ⟨.or,[14, 13]⟩ = w16 := rfl
  let w17 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x]
  have g16 : step w16 ⟨.and,[1, 2]⟩ = w17 := rfl
  let w18 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x]
  have g17 : step w17 ⟨.and,[16, 4]⟩ = w18 := rfl
  let w19 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x]
  have g18 : step w18 ⟨.and,[0, 3]⟩ = w19 := rfl
  let w20 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x]
  have g19 : step w19 ⟨.and,[18, 4]⟩ = w20 := rfl
  let w21 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x]
  have g20 : step w20 ⟨.and,[0, 2]⟩ = w21 := rfl
  let w22 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x]
  have g21 : step w21 ⟨.and,[20, 5]⟩ = w22 := rfl
  let w23 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x]
  have g22 : step w22 ⟨.and,[1, 3]⟩ = w23 := rfl
  let w24 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x]
  have g23 : step w23 ⟨.and,[22, 5]⟩ = w24 := rfl
  let w25 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x]
  have g24 : step w24 ⟨.or,[17, 19]⟩ = w25 := rfl
  let w26 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x]
  have g25 : step w25 ⟨.or,[24, 21]⟩ = w26 := rfl
  let w27 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x]
  have g26 : step w26 ⟨.or,[25, 23]⟩ = w27 := rfl
  let w28 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x]
  have g27 : step w27 ⟨.not,[26]⟩ = w28 := rfl
  let w29 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x]
  have g28 : step w28 ⟨.and,[10, 27]⟩ = w29 := rfl
  let w30 := [x 0, x 1, x 2, x 3, x 4, x 5, v6 x, v7 x, v8 x, v9 x, v10 x, v11 x, v12 x, v13 x, v14 x, v15 x, v16 x, v17 x, v18 x, v19 x, v20 x, v21 x, v22 x, v23 x, v24 x, v25 x, v26 x, v27 x, v28 x, v29 x]
  have g29 : step w29 ⟨.or,[15, 28]⟩ = w30 := rfl
  rw [inputs]
  simp only [gates, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29]
  rfl

theorem computes (j : Fin 22) (x : Input) :
    Circuit.eval ⟨gates,out j⟩ (List.ofFn x) = family j x := by
  exact congrArg (fun w : List Bool => w.getD (out j) false) (list_eval x)

private theorem meet_le : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → meet a b ≤ meet c d := by decide
private theorem join_le : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → join a b ≤ join c d := by decide

private theorem fix_pair : ∀ a b A B : Bool, a ≤ A → b ≤ B → join a b = true →
    meet A B = false → a = A ∧ b = B := by decide

private theorem full_same (x y : Input) (h : ∀ i, x i ≤ y i)
    (u : v10 x = true) (v : v15 y = false) : x = y := by
  have mt : ∀ a b : Bool, meet a b = true → a = true ∧ b = true := by decide
  have jf : ∀ a b : Bool, join a b = false → a = false ∧ b = false := by decide
  have uR := mt (v9 x) (v8 x) u
  have uL := mt (v6 x) (v7 x) uR.1
  have vR := jf (v14 y) (v13 y) v
  have vL := jf (v11 y) (v12 y) vR.1
  have p := fix_pair (x 0) (x 1) (y 0) (y 1) (h 0) (h 1) uL.1 vL.1
  have q := fix_pair (x 2) (x 3) (y 2) (y 3) (h 2) (h 3) uL.2 vL.2
  have r := fix_pair (x 4) (x 5) (y 4) (y 5) (h 4) (h 5) uR.2 vR.2
  funext i
  fin_cases i <;> first | exact p.1 | exact p.2 | exact q.1 | exact q.2 | exact r.1 | exact r.2

theorem monotone_family (j : Fin 22) (x y : Input) (h : ∀ i, x i ≤ y i) : family j x ≤ family j y := by
  have h6 : v6 x ≤ v6 y := join_le (h 0) (h 1)
  have h7 : v7 x ≤ v7 y := join_le (h 2) (h 3)
  have h8 : v8 x ≤ v8 y := join_le (h 4) (h 5)
  have h9 : v9 x ≤ v9 y := meet_le h6 h7
  have h10 : v10 x ≤ v10 y := meet_le h9 h8
  have h11 : v11 x ≤ v11 y := meet_le (h 0) (h 1)
  have h12 : v12 x ≤ v12 y := meet_le (h 2) (h 3)
  have h13 : v13 x ≤ v13 y := meet_le (h 4) (h 5)
  have h14 : v14 x ≤ v14 y := join_le h11 h12
  have h15 : v15 x ≤ v15 y := join_le h14 h13
  have h16 : v16 x ≤ v16 y := meet_le (h 1) (h 2)
  have h17 : v17 x ≤ v17 y := meet_le h16 (h 4)
  have h18 : v18 x ≤ v18 y := meet_le (h 0) (h 3)
  have h19 : v19 x ≤ v19 y := meet_le h18 (h 4)
  have h20 : v20 x ≤ v20 y := meet_le (h 0) (h 2)
  have h21 : v21 x ≤ v21 y := meet_le h20 (h 5)
  have h22 : v22 x ≤ v22 y := meet_le (h 1) (h 3)
  have h23 : v23 x ≤ v23 y := meet_le h22 (h 5)
  have h24 : v24 x ≤ v24 y := join_le h17 h19
  have h25 : v25 x ≤ v25 y := join_le h24 h21
  have h26 : v26 x ≤ v26 y := join_le h25 h23
  have h29 : v29 x ≤ v29 y := by
    cases vy : v15 y with
    | true => simp [v29, vy, join]
    | false =>
      have vx : v15 x = false := (by decide : ∀ b : Bool, b ≤ false → b = false)
        (v15 x) (by simpa only [vy] using h15)
      cases ux : v10 x with
      | false => simp [v29, v28, vx, ux, meet, join]
      | true => rw [full_same x y h ux vy]
  fin_cases j
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h29

def tag (f : Input → Bool) : Nat := (BitVec.ofBoolListLE
    ([58, 15, 37, 23, 60, 27, 1, 21].map (fun row : Nat => f (fun i => row.testBit i.val)))).toNat

private def prefixTag (j : Fin 21) : Nat := [239, 191, 189, 175, 173, 42, 18, 17, 58, 59, 10, 8, 34, 32, 142, 4, 35, 1, 40, 44, 45].getD j.val 0
private def inputTag (i : Fin 6) : Nat := [238, 43, 158, 51, 185, 21].getD i.val 0

set_option maxRecDepth 10000 in
private theorem tags (j : Fin 21) : tag (family j.castSucc) = prefixTag j := by
  fin_cases j <;> decide

private theorem input_tags (i : Fin 6) : tag (fun x => x i) = inputTag i := by
  fin_cases i <;> decide

theorem prefix_distinct : Function.Injective (fun j : Fin 21 => family j.castSucc) := by
  intro i j h
  have id : ∀ a b : Fin 21, prefixTag a = prefixTag b → a = b := by decide
  apply id
  simpa only [tags] using (congrArg tag h)

theorem prefix_noninput (j : Fin 21) (i : Fin 6) : family j.castSucc ≠ fun x => x i := by
  intro h
  have id : ∀ a : Fin 21, ∀ b : Fin 6, prefixTag a ≠ inputTag b := by decide
  exact id j i (by simpa only [tags, input_tags] using congrArg tag h)

theorem prefix_nonzero (j : Fin 21) : family j.castSucc ≠ fun _ => false := by
  intro h
  have id : ∀ a : Fin 21, prefixTag a ≠ 0 := by decide
  have z : tag (fun _ => false) = 0 := by decide
  exact id j (by simpa only [tags, z] using congrArg tag h)

def prefixMask (i : Fin 21) : Nat := [255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 34, 2, 68, 4, 17, 16, 136, 128, 6, 22, 150].getD i.val 0

set_option maxRecDepth 10000 in
theorem prefix_mask (i : Fin 21) : mask (family i.castSucc) = prefixMask i := by
  fin_cases i <;> decide

theorem final_mask : mask (family (Fin.last 21)) = 105 := by decide

end PEqualNP.Outside.L_meta_1036_aux.Witness

-- On the eight selected inputs, three additional positive gates cannot produce mask 105.
namespace PEqualNP.Outside.L_meta_1036_aux

def baseMasks : List Nat := [0,2,4,6,15,16,17,22,34,51,68,85,128,136,150,170,204,240,255]
private def firstMasks : List Nat := [0,1,2,3,4,5,6,8,10,12,15,16,17,18,19,20,21,22,23,31,32,34,38,47,48,50,51,54,55,63,64,68,70,79,80,84,85,86,87,95,102,119,128,130,132,134,136,138,140,142,143,144,145,150,151,152,153,158,159,160,162,170,174,175,179,182,183,186,187,190,192,196,204,206,207,213,214,215,220,221,222,238,240,241,242,243,244,245,246,248,250,252,255]
private abbrev secondOK (z : Nat) : Prop := z < 256 ∧ z ≠ 41 ∧ z ≠ 73 ∧ z ≠ 97 ∧ z ≠ 104 ∧ z ≠ 105

private def ops (x y : Nat) : List Nat := [x &&& y, x ||| y]

private theorem covered {xs ys : List Nat} (ck : xs.all (fun u => u ∈ ys) = true)
    {x : Nat} (hx : x ∈ xs) : x ∈ ys := by
  simpa using List.all_eq_true.mp ck x hx

private theorem table {xs ys zs : List Nat}
    (ck : xs.all (fun x => ys.all (fun y => (ops x y).all (fun z => z ∈ zs))) = true)
    {x y z : Nat} (hx : x ∈ xs) (hy : y ∈ ys)
    (hz : z = (x &&& y) ∨ z = (x ||| y)) : z ∈ zs := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp ck x hx) y hy
  apply covered h
  simpa [ops] using hz

private theorem base_first {x} (h : x ∈ baseMasks) : x ∈ firstMasks := covered (by decide) h
private theorem first_second {x} (h : x ∈ firstMasks) : secondOK x := by
  have ck : firstMasks.all (fun n => secondOK n) = true := by decide
  simpa using List.all_eq_true.mp ck x h

set_option maxHeartbeats 1000000 in
private theorem firstCert : baseMasks.all
    (fun x => baseMasks.all (fun y => (ops x y).all (fun z => z ∈ firstMasks))) = true := by decide

set_option maxHeartbeats 5000000 in
private theorem secondCert : firstMasks.all
    (fun x => firstMasks.all (fun y => (ops x y).all (fun z => secondOK z))) = true := by decide

set_option maxRecDepth 2500 in
private theorem excludeCert : firstMasks.all (fun x => (List.range 256).all
    (fun y => !(decide (secondOK y)) || ((x &&& y) != 105 && (x ||| y) != 105))) = true := by decide

private theorem exclude {x y : Nat} (hx : x ∈ firstMasks) (hy : secondOK y) :
    (x &&& y) ≠ 105 ∧ (x ||| y) ≠ 105 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp excludeCert x hx) y (List.mem_range.mpr hy.1)
  simpa [hy] using h

private theorem secondNo : ¬ secondOK 105 := by decide

private theorem one {a} (t : Trace (fun n => n ∈ baseMasks) [a]) : a ∈ firstMasks := by
  obtain ⟨prev, x, y, hx, hy, hz⟩ := t
  exact table firstCert (by simpa using hx) (by simpa using hy) hz

private theorem two {a b} (t : Trace (fun n => n ∈ baseMasks) [b,a]) :
    a ∈ firstMasks ∧ secondOK b := by
  obtain ⟨prev, x, y, hx, hy, hz⟩ := t
  have ha := one prev
  have lift {v} (hv : v ∈ baseMasks ∨ v ∈ [a]) : v ∈ firstMasks := by
    rcases hv with h | h
    · exact base_first h
    · simpa [List.mem_singleton.mp h] using ha
  have h := List.all_eq_true.mp (List.all_eq_true.mp secondCert _ (lift hx)) _ (lift hy)
  refine ⟨ha, ?_⟩
  have hb := List.all_eq_true.mp h b (by simpa [ops] using hz)
  simpa using hb

private theorem three {a b c} (t : Trace (fun n => n ∈ baseMasks) [c,b,a]) :
    a ≠ 105 ∧ b ≠ 105 ∧ c ≠ 105 := by
  obtain ⟨prev, x, y, hx, hy, hz⟩ := t
  obtain ⟨ha,hb⟩ := two prev
  have hb' : b ≠ 105 := fun e => secondNo (e ▸ hb)
  refine ⟨fun e => secondNo (e ▸ first_second ha), hb', ?_⟩
  have lift {v} (hv : v ∈ baseMasks ∨ v ∈ [b,a]) : v ∈ firstMasks ∨ v = b := by
    rcases hv with h | h
    · exact Or.inl (base_first h)
    · rcases (show v = b ∨ v = a by simpa using h) with eq | rfl
      · exact Or.inr eq
      · exact Or.inl ha
  have ex (h : x ∈ firstMasks) (h' : secondOK y) : c ≠ 105 := by
    obtain ⟨hand,hor⟩ := exclude h h'
    rcases hz with rfl | rfl <;> assumption
  rcases lift hx with hx' | rfl
  · rcases lift hy with hy' | rfl
    · exact ex hx' (first_second hy')
    · exact ex hx' hb
  · rcases lift hy with hy' | rfl
    · obtain ⟨hand,hor⟩ := exclude hy' hb
      rcases hz with rfl | rfl
      · rwa [Nat.and_comm]
      · rwa [Nat.or_comm]
    · rcases hz with rfl | rfl <;> simpa using hb'

theorem no_short_105 {xs : List Nat} (ht : Trace (fun n => n ∈ baseMasks) xs)
    (hlen : xs.length ≤ 3) : ¬ (105 ∈ baseMasks ∨ 105 ∈ xs) := by
  have hb : 105 ∉ baseMasks := by decide
  intro h
  obtain h := h.resolve_left hb
  match xs with
  | [] => simp at h
  | [a] =>
    have ha := one ht
    have ea : 105 = a := by simpa using h
    exact secondNo (ea ▸ first_second ha)
  | [b,a] =>
    obtain ⟨ha,hb'⟩ := two ht
    rcases (show 105 = b ∨ 105 = a by simpa using h) with rfl | rfl
    · exact secondNo hb'
    · exact secondNo (first_second ha)
  | [c,b,a] =>
    obtain ⟨ha,hb',hc⟩ := three ht
    rcases (show 105 = c ∨ 105 = b ∨ 105 = a by simpa using h) with hc' | hb'' | ha'
    · exact hc hc'.symm
    · exact hb' hb''.symm
    · exact ha ha'.symm
  | _ :: _ :: _ :: _ :: _ => simp only [List.length_cons] at hlen <;> omega

end PEqualNP.Outside.L_meta_1036_aux

-- Reading eight truth values commutes with every allowed positive gate.
namespace PEqualNP.Outside.L_meta_1036_aux.Witness

open PEqualNP.CircuitLowerBounds

theorem maskFalse : mask (fun _ => false) = 0 := by decide

theorem maskTrue : mask (fun _ => true) = 255 := by decide

private theorem testMask (f : Input → Bool) (i : Nat) :
    (mask f).testBit i = if h : i < 8 then f (clean ⟨i,h⟩) else false := by
  simp only [mask, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

theorem maskAnd (f g : Input → Bool) :
    mask (fun x => f x && g x) = (mask f &&& mask g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, testMask]
  split <;> rfl

theorem maskOr (f g : Input → Bool) :
    mask (fun x => f x || g x) = (mask f ||| mask g) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, testMask]
  split <;> rfl

private theorem srcLookup (ws : List (W 6)) (i : Nat) :
    Source mask ws (mask (ws.getD i (fun _ => false))) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inl maskFalse
  | some v =>
    exact Or.inr (Or.inr ⟨v, List.mem_of_getElem? h, rfl⟩)

theorem gateLaw (ws : List (W 6)) (g : Gate) (good : Good g) :
    ∃ u v : Nat, Source mask ws u ∧ Source mask ws v ∧
    (mask (wireValue ws g) = (u &&& v) ∨ mask (wireValue ws g) = (u ||| v)) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨hop, hlen⟩ := good
  change op = .and ∨ op = .or at hop
  change ins.length ≤ 2 at hlen
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨255,255,Or.inr (Or.inl rfl),Or.inr (Or.inl rfl),Or.inl maskTrue⟩
    · exact ⟨0,0,Or.inl rfl,Or.inl rfl,Or.inr maskFalse⟩
  | cons a rest =>
    let A := ws.getD a (fun _ => false)
    have ha := srcLookup ws a
    cases rest with
    | nil =>
      refine ⟨mask A, mask A, ha, ha, Or.inl ?_⟩
      rw [Nat.and_self]
      congr 1
      funext x
      rcases hop with rfl | rfl <;> simp [wireValue, GateOp.eval, A]
    | cons b tail =>
      have empty : tail = [] := List.length_eq_zero_iff.mp (by
        change tail.length + 1 + 1 ≤ 2 at hlen
        omega)
      subst tail
      let B := ws.getD b (fun _ => false)
      refine ⟨mask A, mask B, ha, srcLookup ws b, ?_⟩
      rcases hop with rfl | rfl
      · left
        rw [← maskAnd A B]
        apply congrArg mask
        funext x
        simp [wireValue, GateOp.eval, A, B]
      · right
        rw [← maskOr A B]
        apply congrArg mask
        funext x
        simp [wireValue, GateOp.eval, A, B]

end PEqualNP.Outside.L_meta_1036_aux.Witness

-- Twenty-one distinct compulsory outputs leave at most three gates in a list of size 24.
namespace PEqualNP.Outside.L_meta_1036_aux

open PEqualNP.CircuitLowerBounds

theorem monotoneLower (gs : List Gate) (outs : Fin 22 → ℕ)
    (hg : ∀ g ∈ gs, Good g)
    (hr : ∀ j x, (Circuit.mk gs (outs j)).eval (List.ofFn x) = Witness.family j x) :
    25 ≤ gs.length := by
  classical
  let pre (j : Fin 21) : W 6 := Witness.family j.castSucc
  let req : Finset (W 6) := Finset.univ.image pre
  have count : req.card = 21 := by
    change (Finset.univ.image pre).card = 21
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective (Finset.univ : Finset (Fin 21)) Witness.prefix_distinct
  have index {f : W 6} (hf : f ∈ req) : ∃ j : Fin 21, pre j = f := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hf
    exact ⟨j,hj⟩
  have projBase : ∀ i : Fin 6, Witness.mask (fun x => x i) ∈ baseMasks := by decide
  have prefixBase : ∀ j : Fin 21, Witness.prefixMask j ∈ baseMasks := by decide
  have reqBase (f : W 6) (hf : f ∈ req) : Witness.mask f ∈ baseMasks := by
    obtain ⟨j,rfl⟩ := index hf
    rw [show Witness.mask (pre j) = Witness.prefixMask j from Witness.prefix_mask j]
    exact prefixBase j
  have nfalse : (fun _ => false) ∉ req := by
    intro hf
    obtain ⟨j,hj⟩ := index hf
    exact Witness.prefix_nonzero j hj
  have nproj (i : Fin 6) : (fun x => x i : W 6) ∉ req := by
    intro hf
    obtain ⟨j,hj⟩ := index hf
    exact Witness.prefix_noninput j i hj
  have outputs (f : W 6) (hf : f ∈ req) :
      ∃ o : ℕ, ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = f x := by
    obtain ⟨j,rfl⟩ := index hf
    exact ⟨outs j.castSucc,hr j.castSucc⟩
  let last := Fin.last 21
  obtain ⟨extra,trace,hsize,hout⟩ := short_trace Witness.mask (fun v => v ∈ baseMasks)
      req gs hg Witness.gateLaw (by decide) (by decide) Witness.maskFalse
      projBase reqBase nfalse nproj outputs (outs last)
  rw [count] at hsize
  have et : (fun x => (Circuit.mk gs (outs last)).eval (List.ofFn x)) = Witness.family last :=
    funext (hr last)
  rw [et, Witness.final_mask] at hout
  by_contra! h
  exact (no_short_105 trace (by omega)) hout

end PEqualNP.Outside.L_meta_1036_aux

theorem PEqualNP.Outside.L_meta_1036 : ∃ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 ∧ (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) ∧ ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) ∧ ∀ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) → gates.length < gates'.length := by
  refine ⟨6, 22, PEqualNP.Outside.L_meta_1036_aux.Witness.family, by decide,
    PEqualNP.Outside.L_meta_1036_aux.Witness.monotone_family,
    PEqualNP.Outside.L_meta_1036_aux.Witness.gates, PEqualNP.Outside.L_meta_1036_aux.Witness.out,
    PEqualNP.Outside.L_meta_1036_aux.Witness.allowed, PEqualNP.Outside.L_meta_1036_aux.Witness.oneNot,
    PEqualNP.Outside.L_meta_1036_aux.Witness.computes, ?_⟩
  intro gs outs good realizes
  have lower := PEqualNP.Outside.L_meta_1036_aux.monotoneLower gs outs good realizes
  rw [PEqualNP.Outside.L_meta_1036_aux.Witness.gates_length]
  omega
