import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1035_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upGates : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [5, 2]⟩, ⟨GateOp.or, [6, 3]⟩, ⟨GateOp.or, [7, 4]⟩,
   ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [9, 10]⟩,
   ⟨GateOp.or, [12, 11]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [8, 14]⟩, ⟨GateOp.or, [13, 15]⟩]

def upOuts : Fin 10 → ℕ := ![5, 6, 7, 8, 9, 10, 11, 12, 13, 16]

def cf (j : Fin 10) (x : Fin 5 → Bool) : Bool := Circuit.eval ⟨upGates, upOuts j⟩ (List.ofFn x)

lemma cf_closed : ∀ x : Fin 5 → Bool,
    cf 0 x = (x 0 || x 1) ∧
    cf 1 x = ((x 0 || x 1) && x 2) ∧
    cf 2 x = (((x 0 || x 1) && x 2) || x 3) ∧
    cf 3 x = ((((x 0 || x 1) && x 2) || x 3) || x 4) ∧
    cf 4 x = (x 0 && x 1) ∧
    cf 5 x = (x 0 && x 3) ∧
    cf 6 x = (x 0 && x 4) ∧
    cf 7 x = ((x 0 && x 1) || (x 0 && x 3)) ∧
    cf 8 x = (((x 0 && x 1) || (x 0 && x 3)) || (x 0 && x 4)) ∧
    cf 9 x = (x 3 || x 4 || (x 1 && (x 0 || x 2))) := by
  decide

lemma mono_forms (x y : Fin 5 → Bool) (h0 : x 0 = true → y 0 = true) (h1 : x 1 = true → y 1 = true)
    (h2 : x 2 = true → y 2 = true) (h3 : x 3 = true → y 3 = true) (h4 : x 4 = true → y 4 = true) :
    ((x 0 || x 1) = true → (y 0 || y 1) = true) ∧
    (((x 0 || x 1) && x 2) = true → ((y 0 || y 1) && y 2) = true) ∧
    ((((x 0 || x 1) && x 2) || x 3) = true → (((y 0 || y 1) && y 2) || y 3) = true) ∧
    (((((x 0 || x 1) && x 2) || x 3) || x 4) = true → ((((y 0 || y 1) && y 2) || y 3) || y 4) = true) ∧
    ((x 0 && x 1) = true → (y 0 && y 1) = true) ∧
    ((x 0 && x 3) = true → (y 0 && y 3) = true) ∧
    ((x 0 && x 4) = true → (y 0 && y 4) = true) ∧
    (((x 0 && x 1) || (x 0 && x 3)) = true → ((y 0 && y 1) || (y 0 && y 3)) = true) ∧
    ((((x 0 && x 1) || (x 0 && x 3)) || (x 0 && x 4)) = true →
      (((y 0 && y 1) || (y 0 && y 3)) || (y 0 && y 4)) = true) ∧
    ((x 3 || x 4 || (x 1 && (x 0 || x 2))) = true → (y 3 || y 4 || (y 1 && (y 0 || y 2))) = true) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

lemma cf_mono : ∀ (j : Fin 10) (x y : Fin 5 → Bool), (∀ i : Fin 5, x i ≤ y i) → cf j x ≤ cf j y := by
  intro j x y hxy
  have h := mono_forms x y (Bool.le_iff_imp.mp (hxy 0)) (Bool.le_iff_imp.mp (hxy 1))
    (Bool.le_iff_imp.mp (hxy 2)) (Bool.le_iff_imp.mp (hxy 3)) (Bool.le_iff_imp.mp (hxy 4))
  have cx := cf_closed x
  have cy := cf_closed y
  rw [Bool.le_iff_imp]
  match j with
  | ⟨0, _⟩ => show cf 0 x = true → cf 0 y = true; rw [cx.1, cy.1]; exact h.1
  | ⟨1, _⟩ => show cf 1 x = true → cf 1 y = true; rw [cx.2.1, cy.2.1]; exact h.2.1
  | ⟨2, _⟩ => show cf 2 x = true → cf 2 y = true; rw [cx.2.2.1, cy.2.2.1]; exact h.2.2.1
  | ⟨3, _⟩ => show cf 3 x = true → cf 3 y = true; rw [cx.2.2.2.1, cy.2.2.2.1]; exact h.2.2.2.1
  | ⟨4, _⟩ => show cf 4 x = true → cf 4 y = true; rw [cx.2.2.2.2.1, cy.2.2.2.2.1]; exact h.2.2.2.2.1
  | ⟨5, _⟩ => show cf 5 x = true → cf 5 y = true; rw [cx.2.2.2.2.2.1, cy.2.2.2.2.2.1]; exact h.2.2.2.2.2.1
  | ⟨6, _⟩ => show cf 6 x = true → cf 6 y = true; rw [cx.2.2.2.2.2.2.1, cy.2.2.2.2.2.2.1]; exact h.2.2.2.2.2.2.1
  | ⟨7, _⟩ => show cf 7 x = true → cf 7 y = true; rw [cx.2.2.2.2.2.2.2.1, cy.2.2.2.2.2.2.2.1]; exact h.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => show cf 8 x = true → cf 8 y = true; rw [cx.2.2.2.2.2.2.2.2.1, cy.2.2.2.2.2.2.2.2.1]; exact h.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => show cf 9 x = true → cf 9 y = true; rw [cx.2.2.2.2.2.2.2.2.2, cy.2.2.2.2.2.2.2.2.2]; exact h.2.2.2.2.2.2.2.2.2

lemma gate_shape : ∀ g ∈ upGates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upGates, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

lemma up_length : upGates.length = 12 := rfl

lemma not_only_at_9 : ∀ i : Fin upGates.length, (upGates.get i).op = GateOp.not → i.val = 9 := by
  intro i hi
  have hlt : i.val < 12 := i.isLt
  rcases i with ⟨k, hk⟩
  simp only at hlt ⊢
  interval_cases k <;> simp_all [upGates]

lemma single_not : ∀ i j : Fin upGates.length, (upGates.get i).op = GateOp.not →
    (upGates.get j).op = GateOp.not → i = j := by
  intro i j hi hj
  exact Fin.ext ((not_only_at_9 i hi).trans (not_only_at_9 j hj).symm)

abbrev Sig := BitVec 32

def Makes (xs : List Sig) (v : Sig) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, v = (a &&& b) ∨ v = (a ||| b)

def Built : List Sig → List Sig → Prop
  | _, [] => True
  | xs, t :: ts => Makes xs t ∧ Built (t :: xs) ts

def baseSignals : List Sig := [0, 4294967295, 2863311530, 3435973836, 4042322160, 4278255360,
  4294901760, 4008636142, 3772834016, 4292935648, 4294967264, 2290649224, 2852170240, 2863267840,
  2861083272, 2863311496]

def targetSig : Sig := 4294967240

def requiredSigs : List Sig := [4008636142, 3772834016, 4292935648, 4294967264, 2290649224,
  2852170240, 2863267840, 2861083272, 2863311496, 4294967240]

def sample (j : Fin 32) (i : Fin 5) : Bool :=
  j.val.testBit i.val

def readTable (j : Fin 32) (t : Sig) : Bool := t.getLsbD j.val

lemma read_zero (j : Fin 32) : readTable j 0 = false := BitVec.getLsbD_zero

lemma read_not (j : Fin 32) (t : Sig) : readTable j (~~~t) = !(readTable j t) := by
  simp [readTable, j.isLt]

def inputSigs : List Sig := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760]

lemma inputTables (j : Fin 32) : List.ofFn (sample j) = inputSigs.map (readTable j) := by
  fin_cases j <;> decide

lemma table_ext (a b : Sig) (h : ∀ j, readTable j a = readTable j b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i, hi⟩

lemma getD_table (x : Fin 32) (ws : List Sig) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

def gateTable (ws : List Sig) (g : Gate) : Sig :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

lemma read_gateTable (x : Fin 32) (ws : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

def wireTables (gs : List Gate) (ws : List Sig) : List Sig :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

lemma read_wireTables (x : Fin 32) (gs : List Gate) (ws : List Sig)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

lemma wires_match (C : Circuit) (h : FanInTwo C) (j : Fin 32) (o : ℕ) :
    (C.wires (List.ofFn (sample j))).getD o false =
    readTable j ((wireTables C.gates inputSigs).getD o 0) := by
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (sample j))).getD o false = _
  rw [inputTables, read_wireTables j C.gates inputSigs h, getD_table]

def outputsFrom : List Gate → List Sig → List Sig
  | [], _ => []
  | g :: gs, ws => gateTable ws g :: outputsFrom gs (ws ++ [gateTable ws g])

lemma outputs_length (gs : List Gate) (ws : List Sig) :
    (outputsFrom gs ws).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp [outputsFrom, ih]

lemma outputs_append (gs : List Gate) (ws : List Sig) :
    wireTables gs ws = ws ++ outputsFrom gs ws := by
  induction gs generalizing ws with
  | nil => simp [wireTables, outputsFrom]
  | cons g gs ih =>
    change wireTables gs (ws ++ [gateTable ws g]) = ws ++ gateTable ws g :: _
    rw [ih]
    simp

lemma makes_self {xs : List Sig} {v : Sig} (hv : v ∈ xs) : Makes xs v :=
  ⟨v, hv, v, hv, Or.inl (by simp)⟩

lemma getD_avail (ws env : List Sig) (i : ℕ) (z : 0 ∈ env)
    (hw : ∀ v ∈ ws, v ∈ env) : ws.getD i 0 ∈ env := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact z

lemma made_gate (ws env : List Sig) (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (z : 0 ∈ env) (one : (~~~(0 : Sig)) ∈ env) (hw : ∀ v ∈ ws, v ∈ env) :
    Makes env (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  rcases h with h | h <;> change op = _ at h <;> subst op
  · cases ins with
    | nil => exact makes_self one
    | cons i is =>
      cases is with
      | nil => exact makes_self (getD_avail _ _ _ z hw)
      | cons j _ => exact ⟨_, getD_avail _ _ i z hw, _, getD_avail _ _ j z hw, Or.inl rfl⟩
  · cases ins with
    | nil => exact makes_self z
    | cons i is =>
      cases is with
      | nil => exact makes_self (getD_avail _ _ _ z hw)
      | cons j _ => exact ⟨_, getD_avail _ _ i z hw, _, getD_avail _ _ j z hw, Or.inr rfl⟩

lemma built_outputs (gs : List Gate) (ws env : List Sig)
    (hp : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (z : 0 ∈ env) (one : (~~~(0 : Sig)) ∈ env) (hw : ∀ v ∈ ws, v ∈ env) :
    Built env (outputsFrom gs ws) := by
  induction gs generalizing ws env with
  | nil => trivial
  | cons g gs ih =>
    let t := gateTable ws g
    refine ⟨made_gate ws env g (hp g List.mem_cons_self) z one hw, ?_⟩
    apply ih (ws ++ [t]) (t :: env) (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
      (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ one)
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_cons_of_mem _ (hw v h)
    · have he : v = t := by simpa using h
      exact List.mem_cons.mpr (Or.inl he)

lemma up_fan : FanInTwo ⟨upGates, 0⟩ := by
  intro g hg
  obtain ⟨h, hl⟩ := gate_shape g hg
  refine ⟨?_, hl⟩
  rcases h with h | h | h <;> simp [h]

set_option maxRecDepth 100000 in
lemma up_tables : ∀ j : Fin 10,
    (wireTables upGates inputSigs).getD (upOuts j) 0 = requiredSigs.getD j.val 0 := by
  decide +kernel

lemma cf_sample (j : Fin 10) (r : Fin 32) :
    cf j (sample r) = readTable r (requiredSigs.getD j.val 0) := by
  rw [← up_tables j]
  exact wires_match ⟨upGates, 0⟩ up_fan r (upOuts j)

lemma required_index (v : Sig) (hv : v ∈ requiredSigs.toFinset) :
    ∃ j : Fin 10, requiredSigs.getD j.val 0 = v := by
  obtain ⟨i, hi, eq⟩ := List.getElem_of_mem (List.mem_toFinset.mp hv)
  have len : requiredSigs.length = 10 := by decide
  exact ⟨⟨i, by omega⟩, (List.getD_eq_getElem _ _ hi).trans eq⟩

lemma required_in_outputs (gs : List Gate) (out : Fin 10 → ℕ)
    (hp : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (j : Fin 10) (x : Fin 5 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = cf j x) :
    ∀ v ∈ requiredSigs.toFinset, v ∈ outputsFrom gs inputSigs := by
  intro v hv
  obtain ⟨j, rfl⟩ := required_index v hv
  have hh : FanInTwo ⟨gs, 0⟩ := by
    intro g hg
    obtain ⟨ha | ho, hl⟩ := hp g hg
    · exact ⟨Or.inl ha, hl⟩
    · exact ⟨Or.inr (Or.inl ho), hl⟩
  have hval : (wireTables gs inputSigs).getD (out j) 0 = requiredSigs.getD j.val 0 :=
    table_ext _ _ (fun r => (wires_match ⟨gs, 0⟩ hh r (out j)).symm.trans
      ((he j (sample r)).trans (cf_sample j r)))
  have bounds : ∀ j : Fin 10, requiredSigs.getD j.val 0 ≠ 0 ∧
      requiredSigs.getD j.val 0 ∉ inputSigs := by decide +kernel
  have hi : out j < (wireTables gs inputSigs).length := by
    by_contra! hh'
    rw [List.getD_eq_default _ _ hh'] at hval
    exact (bounds j).1 hval.symm
  rw [List.getD_eq_getElem _ _ hi] at hval
  have hm : requiredSigs.getD j.val 0 ∈ wireTables gs inputSigs := hval ▸ List.getElem_mem hi
  rw [outputs_append] at hm
  exact (List.mem_append.mp hm).resolve_left (bounds j).2

lemma ready_trace (gs : List Gate)
    (hp : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Built baseSignals (outputsFrom gs inputSigs) := by
  apply built_outputs gs inputSigs baseSignals (fun g hg => (hp g hg).1) (by decide) (by decide)
  intro v hv
  have sub : inputSigs ⊆ baseSignals := by decide
  exact sub hv

lemma two_other_gates {α : Type*} [DecidableEq α] (vals : List α) (required : Finset α)
    (hcard : required.card = 10) (hmem : ∀ v ∈ required, v ∈ vals)
    (hlen : vals.length ≤ 12) :
    (vals.filter (fun v => decide (v ∉ required))).length ≤ 2 := by
  have hsub : required ⊆ (vals.filter (fun v => decide (v ∈ required))).toFinset := by
    intro v hv
    apply List.mem_toFinset.mpr
    exact List.mem_filter.mpr ⟨hmem v hv, by simp [hv]⟩
  have hinside := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  have htotal := List.length_eq_length_filter_add (l := vals) (fun v => decide (v ∈ required))
  have hneg : (fun v => !(decide (v ∈ required))) = (fun v => decide (v ∉ required)) := by
    funext v
    by_cases h : v ∈ required <;> simp [h]
  rw [hneg] at htotal
  omega

lemma trace_makes_weaken {xs ys : List Sig} {v : Sig}
    (h : ∀ z ∈ xs, z ∈ ys) (hv : Makes xs v) : Makes ys v := by
  obtain ⟨a, ha, b, hb, he⟩ := hv
  exact ⟨a, h a ha, b, h b hb, he⟩

lemma trace_prefix {vals src xs : List Sig} {R : Finset Sig} {t : Sig}
    (hb : Built src vals) (hm : t ∈ vals) (hs : ∀ z ∈ src, z ∈ xs)
    (hr : ∀ v ∈ R, v ≠ t → v ∈ xs) :
    ∃ ws : List Sig, ws.length ≤ (vals.filter (fun v => decide (v ∉ R))).length ∧
      Built xs ws ∧ Makes (ws.reverse ++ xs) t := by
  induction vals generalizing src xs with
  | nil => simp at hm
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := hb
    have hmake := trace_makes_weaken hs hv
    by_cases he : v = t
    · subst v
      exact ⟨[], Nat.zero_le _, trivial, by simpa using hmake⟩
    have hm' : t ∈ vs := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
    by_cases hR : v ∈ R
    · have havev := hr v hR he
      have hsrc : ∀ z ∈ v :: src, z ∈ xs := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact havev
        · exact hs _ hz
      obtain ⟨ws, hw, hbuilt, hfinal⟩ := ih hvs hm' hsrc hr
      exact ⟨ws, by simpa [hR] using hw, hbuilt, hfinal⟩
    · have hsrc : ∀ z ∈ v :: src, z ∈ v :: xs := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs _ hz)
      have hR' : ∀ z ∈ R, z ≠ t → z ∈ v :: xs :=
        fun z hz he' => List.mem_cons_of_mem _ (hr z hz he')
      obtain ⟨ws, hw, hbuilt, hfinal⟩ := ih hvs hm' hsrc hR'
      exact ⟨v :: ws, by simpa [hR] using Nat.succ_le_succ hw, ⟨hmake, hbuilt⟩,
        by simpa [List.reverse_cons, List.append_assoc] using hfinal⟩

lemma trace_three {xs vals : List Sig} {R : Finset Sig} {t : Sig}
    (hb : Built xs vals) (hmem : t ∈ vals) (hr : ∀ v ∈ R, v ≠ t → v ∈ xs)
    (hc : (vals.filter (fun v => decide (v ∉ R))).length ≤ 2)
    (h0 : 0 ∈ xs) :
    ∃ a b, Makes xs a ∧ Makes (a :: xs) b ∧ Makes (b :: a :: xs) t := by
  obtain ⟨ws, hl, hbuilt, hfinal⟩ := trace_prefix hb hmem (fun _ h => h) hr
  have hle := hl.trans hc
  have hz : Makes xs 0 := ⟨0, h0, 0, h0, Or.inl (by decide)⟩
  cases ws with
  | nil =>
    simp only [List.reverse_nil, List.nil_append] at hfinal
    refine ⟨0, 0, hz, trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hz, ?_⟩
    exact trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) hfinal
  | cons a ws =>
    cases ws with
    | nil =>
      obtain ⟨ha, _⟩ := hbuilt
      have hm : Makes (a :: xs) t := by simpa using hfinal
      exact ⟨a, 0, ha, trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hz,
        trace_makes_weaken (fun _ h => List.mem_cons_of_mem _ h) hm⟩
    | cons b ws =>
      cases ws with
      | nil =>
        obtain ⟨ha, hb, _⟩ := hbuilt
        exact ⟨a, b, ha, hb, by simpa using hfinal⟩
      | cons c ws => simp at hle

def certFirst : List Sig := [0, 2155905152, 2281736192, 2290124928, 2290614272, 2290649216,
  2290649224, 2684395520, 2692784256, 2694840320, 2694881408, 2694881440, 2852126720, 2852170240,
  2860558976, 2861039616, 2861083264, 2861083272, 2862612480, 2862656128, 2862656160, 2863267840,
  2863302792, 2863311360, 2863311488, 2863311496, 2863311520, 2863311530, 3233857728, 3422604288,
  3435187392, 3435921408, 3435973824, 3435973836, 3758153728, 3772776448, 3772834016, 3907578088,
  3940608736, 3941133032, 3941261536, 3941264104, 3941264106, 3974950124, 3993038336, 4006407884,
  4007718624, 4008574976, 4008627404, 4008636108, 4008636128, 4008636142, 4026593280, 4041273568,
  4042260480, 4042322144, 4042322160, 4177066232, 4210096880, 4210621176, 4210749680, 4210752248,
  4210752250, 4244438268, 4278124286, 4278190080, 4278255360, 4287168392, 4289396480, 4289396616,
  4289396650, 4291624908, 4292870144, 4292935648, 4293459944, 4293591008, 4293591016, 4293591018,
  4293722092, 4293853166, 4293984240, 4294901760, 4294936712, 4294945280, 4294945416, 4294945450,
  4294954188, 4294959328, 4294962926, 4294963440, 4294967040, 4294967264, 4294967272, 4294967274,
  4294967276, 4294967278, 4294967280, 4294967295]

abbrev certSeparate (x y : Sig) : Prop :=
  targetSig ≠ (x &&& y) ∧ targetSig ≠ (x ||| y)

abbrev certSafe (xs : List Sig) (b : Sig) : Prop :=
  targetSig ≠ b ∧ ∀ y ∈ xs, certSeparate b y

def certGood (xs : List Sig) (b : Sig) : Bool :=
  decide (targetSig ≠ b) &&
    ((if b &&& targetSig = targetSig then xs.all (fun y => decide (targetSig ≠ (b &&& y)))
      else true) &&
     (if b ||| targetSig = targetSig then xs.all (fun y => decide (targetSig ≠ (b ||| y)))
      else true))

lemma certGood_sound {xs : List Sig} {b : Sig} (h : certGood xs b = true) : certSafe xs b := by
  have hh : targetSig ≠ b ∧
      ((b &&& targetSig = targetSig) → ∀ y ∈ xs, targetSig ≠ (b &&& y)) ∧
      ((b ||| targetSig = targetSig) → ∀ y ∈ xs, targetSig ≠ (b ||| y)) := by
    by_cases h1 : b &&& targetSig = targetSig <;> by_cases h2 : b ||| targetSig = targetSig <;>
      simpa [certGood, h1, h2] using h
  refine ⟨hh.1, ?_⟩
  intro y hy
  constructor
  · intro e
    exact hh.2.1 (by rw [e]; simp [← BitVec.and_assoc]) y hy e
  · intro e
    exact hh.2.2 (by rw [e]; simp [← BitVec.or_assoc]) y hy e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_base_mem : ∀ x ∈ baseSignals, x ∈ certFirst := by
  have h : baseSignals.all (fun x => certFirst.contains x) = true := by decide +kernel
  simpa [List.contains_iff_mem] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_first_ops : ∀ x ∈ baseSignals, ∀ y ∈ baseSignals,
    (x &&& y) ∈ certFirst ∧ (x ||| y) ∈ certFirst := by
  have h : baseSignals.all (fun x => baseSignals.all (fun y =>
    certFirst.contains (x &&& y) && certFirst.contains (x ||| y))) = true := by decide +kernel
  simpa [List.contains_iff_mem] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_first_sep : ∀ x ∈ certFirst, ∀ y ∈ certFirst, certSeparate x y := by
  have h : certFirst.all (certGood certFirst) = true := by decide +kernel
  intro x hx
  exact (certGood_sound (List.all_eq_true.mp h x hx)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_mixed_safe : ∀ a ∈ certFirst, ∀ x ∈ baseSignals,
    certSafe (a :: baseSignals) (a &&& x) ∧ certSafe (a :: baseSignals) (a ||| x) := by
  have h : certFirst.all (fun a => baseSignals.all (fun x =>
    certGood (a :: baseSignals) (a &&& x) && certGood (a :: baseSignals) (a ||| x))) = true := by
    decide +kernel
  intro a ha x hx
  have e := List.all_eq_true.mp (List.all_eq_true.mp h a ha) x hx
  exact ⟨certGood_sound (Bool.and_eq_true_iff.mp e).1, certGood_sound (Bool.and_eq_true_iff.mp e).2⟩

lemma cert_first_made {a : Sig} (hm : Makes baseSignals a) : a ∈ certFirst := by
  rcases hm with ⟨x, hx, y, hy, h | h⟩
  · exact h ▸ (cert_first_ops x hx y hy).1
  · exact h ▸ (cert_first_ops x hx y hy).2

lemma cert_first_subset {a : Sig} (ha : a ∈ certFirst) :
    ∀ x ∈ a :: baseSignals, x ∈ certFirst := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact h ▸ ha
  · exact cert_base_mem x h

lemma cert_no_sub {xs : List Sig} (hs : ∀ x ∈ xs, x ∈ certFirst) :
    ¬ Makes xs targetSig := by
  rintro ⟨x, hx, y, hy, he⟩
  exact he.elim (cert_first_sep x (hs x hx) y (hs y hy)).1
    (cert_first_sep x (hs x hx) y (hs y hy)).2

lemma cert_no_cons {xs : List Sig} {b : Sig} (hs : ¬ Makes xs targetSig)
    (hb : certSafe xs b) : ¬ Makes (b :: xs) targetSig := by
  rintro ⟨x, hx, y, hy, he⟩
  rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
  · rcases he with h | h <;> exact hb.1 (by simpa using h)
  · exact he.elim (hb.2 y hy).1 (hb.2 y hy).2
  · rcases he with h | h
    · exact (hb.2 x (by assumption)).1 (by simpa only [BitVec.and_comm] using h)
    · exact (hb.2 x (by assumption)).2 (by simpa only [BitVec.or_comm] using h)
  · exact hs ⟨x, hx, y, hy, he⟩

lemma certificate_no_three {a b : Sig} (ha0 : Makes baseSignals a)
    (hb : Makes (a :: baseSignals) b) : ¬ Makes (b :: a :: baseSignals) targetSig := by
  have ha := cert_first_made ha0
  have hs := cert_first_subset ha
  have first_case (h : b ∈ certFirst) : ¬ Makes (b :: a :: baseSignals) targetSig := by
    apply cert_no_sub
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · exact e ▸ h
    · exact hs x e
  have mixed_case := cert_no_cons (b := b) (cert_no_sub hs)
  rcases hb with ⟨x, hx, y, hy, he⟩
  rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
  · apply first_case
    rcases he with h | h <;> simpa [h] using ha
  · apply mixed_case
    rcases he with h | h
    · exact h ▸ (cert_mixed_safe x ha y hy).1
    · exact h ▸ (cert_mixed_safe x ha y hy).2
  · apply mixed_case
    rcases he with h | h
    · exact (h.trans (BitVec.and_comm _ _)) ▸ (cert_mixed_safe y ha x (by assumption)).1
    · exact (h.trans (BitVec.or_comm _ _)) ▸ (cert_mixed_safe y ha x (by assumption)).2
  · apply first_case
    exact cert_first_made ⟨x, hx, y, hy, he⟩

lemma lower_bound (gs : List Gate) (out : Fin 10 → ℕ)
    (hp : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (j : Fin 10) (x : Fin 5 → Bool), Circuit.eval ⟨gs, out j⟩ (List.ofFn x) = cf j x) :
    12 < gs.length := by
  by_contra! hsmall
  let vals := outputsFrom gs inputSigs
  let R := requiredSigs.toFinset
  have req : ∀ v ∈ R, v ∈ vals := required_in_outputs _ _ hp he
  have hc := two_other_gates vals R (by decide) req (by simpa [vals, outputs_length] using hsmall)
  have inside : ∀ v ∈ R, v ≠ targetSig → v ∈ baseSignals := by
    intro v hv hne
    obtain ⟨j, rfl⟩ := required_index v hv
    have cert : ∀ j : Fin 10, requiredSigs.getD j.val 0 ≠ targetSig →
        requiredSigs.getD j.val 0 ∈ baseSignals := by decide +kernel
    exact cert j hne
  obtain ⟨a, b, ha, hb, ht⟩ := trace_three (ready_trace gs hp) (req targetSig (by decide))
    inside hc (by decide)
  exact certificate_no_three ha hb ht

end PEqualNP.Outside.L_meta_1035_aux

theorem PEqualNP.Outside.L_meta_1035 : ¬ (∀ (n m : ℕ) (f : Fin m → (Fin n → Bool) → Bool), n ≤ 7 → (∀ (j : Fin m) (x y : Fin n → Bool), (∀ i : Fin n, x i ≤ y i) → f j x ≤ f j y) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out j⟩ (List.ofFn x) = f j x) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ (j : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' j⟩ (List.ofFn x) = f j x) ∧ gates'.length ≤ gates.length) := by
  intro H
  obtain ⟨g', o', h1, h2, h3⟩ :=
    H 5 10 PEqualNP.Outside.L_meta_1035_aux.cf (by norm_num) PEqualNP.Outside.L_meta_1035_aux.cf_mono
      PEqualNP.Outside.L_meta_1035_aux.upGates PEqualNP.Outside.L_meta_1035_aux.upOuts
      ⟨PEqualNP.Outside.L_meta_1035_aux.gate_shape, PEqualNP.Outside.L_meta_1035_aux.single_not,
        fun j x => rfl⟩
  have hlow := PEqualNP.Outside.L_meta_1035_aux.lower_bound g' o' h1 h2
  rw [PEqualNP.Outside.L_meta_1035_aux.up_length] at h3
  omega
