import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2608_317
    (geometry :
    let hit (z : Fin 26 → Bool) := ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
      z (Fin.castAdd 13 p)=true ∧ z (Fin.natAdd 13 l)=true
    ∀ z : Fin 26 → Bool, Maximal (fun x => ¬hit x) z → ∃ m : Fin 8192,
      let y (l : Fin 13) := (m.val+0).testBit l.val
      let x (p : Fin 13) := !(y p || y (p-1) || y (p-3) || y (p-9))
      z = Fin.append (m:=13) (n:=13) x y ∧
        z 13 = !(x 0 || x 1 || x 3 || x 9))
    (reify : ∀ (ι : Type) (rows : ι → Fin 26 → Bool) (fs : List (ι → Bool)),
    let p := List.ofFn fun k => fun r => rows r k
    (∀ j : Fin fs.length, ∃ a b : Fin (26+j.val), a≠b ∧ ∃ m : Bool, ∀ r,
      let x := ((p++fs.take j.val).getD a.val (fun _ => false)) r
      let y := ((p++fs.take j.val).getD b.val (fun _ => false)) r
      fs.get j r = if m then x && y else x || y) →
    ∀ a b : Fin (26+fs.length), a≠b → ∃ C : Circuit,
      C.size=fs.length+1 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates,g.inputs.Nodup) ∧
      C.output=26+fs.length ∧ C.gates[fs.length]?=some ⟨.and,[a.val,b.val]⟩ ∧
      ∀ r (i : Fin (26+fs.length)), PEqualNP.BlindGate.wireValue C 26 (rows r) i.val =
        ((p++fs).getD i.val (fun _ => false)) r)
    (finite :
      let Q := (Fin 13 × Fin 4) ⊕ Fin 8192
      let ds : List (Fin 13) := [0,1,3,9]
      let flag (t : Fin 13 × Fin 4) (v : Fin 26) := decide (v = Fin.castAdd 13 (t.1 + ds.getD t.2.val 0) ∨ v=Fin.natAdd 13 t.1)
      let neg (m : Fin 8192) : Fin 26 → Bool :=
        let y (l : Fin 13) := (m.val+0).testBit l.val
        Fin.append (m:=13) (n:=13) (fun p => !(ds.any fun d => y (p-d))) y
      let rows : Q → Fin 26 → Bool := Sum.elim flag neg
      let p := List.ofFn fun k => fun r => rows r k
      ∃ fs : List (Q → Bool), fs.length ≤ 63 ∧
        (∀ j : Fin fs.length, ∃ a b : Fin (26+j.val), a≠b ∧
          let w (k : Nat) := (p++fs.take j.val).getD k (fun _ => false)
          fs.get j = w a ⊓ w b ∨ fs.get j = w a ⊔ w b) ∧
        ∃ a b : Fin (26+fs.length), a≠b ∧
          let read (k : Nat) := (p++fs).getD k (fun _ => false)
          (∀ t : Fin 13 × Fin 4, read a (.inl t) = true ∧ read b (.inl t)=true) ∧
          ∀ m : Fin 8192, read (if ds.any (fun d => neg m (Fin.castAdd 13 d)) then b else a) (.inr m) = false) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  let Q := (Fin 13 × Fin 4) ⊕ Fin 8192
  let pt (l : Fin 13) (k : Fin 4) := l + ([0,1,3,9] : List (Fin 13)).getD k.val 0
  let flag (t : Fin 13 × Fin 4) (v : Fin 26) := decide (v = Fin.castAdd 13 (pt t.1 t.2) ∨ v=Fin.natAdd 13 t.1)
  let neg (m : Fin 8192) :=
    let y (l : Fin 13) := (m.val+0).testBit l.val
    Fin.append (m:=13) (n:=13) (fun p => !(y p || y (p-1) || y (p-3) || y (p-9))) y
  let rows : Q → Fin 26 → Bool := Sum.elim flag neg
  let p := List.ofFn fun k => fun r => rows r k
  obtain ⟨fs,len,law,a,b,ne,pos,nos⟩ := finite
  let ds : List (Fin 13) := [0,1,3,9]
  let neg' (m : Fin 8192) : Fin 26 → Bool :=
    let y (l : Fin 13) := (m.val+0).testBit l.val
    Fin.append (m:=13) (n:=13) (fun p => !(ds.any fun d => y (p-d))) y
  have same (m : Fin 8192) : neg' m = neg m := by
    apply congrArg (fun f : Fin 13 → Bool => Fin.append (m:=13) (n:=13) f (fun l => (m.val+0).testBit l.val))
    funext k
    simp [ds, Bool.or_assoc]
  let rows' : Q → Fin 26 → Bool := Sum.elim flag neg'
  have eqRows : rows' = rows := by
    funext r
    cases r with
    | inl t => rfl
    | inr m => exact same m
  have law' : ∀ j : Fin fs.length, ∃ u v : Fin (26+j.val), u≠v ∧ ∃ m : Bool, ∀ r : Q,
      let w (i : ℕ) := ((p++fs.take j.val).getD i (fun _ => false)) r
      fs.get j r = if m then w u && w v else w u || w v := by
    intro j
    obtain ⟨u,v,h,op⟩ := law j
    change (let col (i : ℕ) := ((List.ofFn (fun k r => rows' r k)) ++ fs.take j.val).getD i (fun _ => false)
            fs.get j = col u ⊓ col v ∨ fs.get j = col u ⊔ col v) at op
    rw [eqRows] at op
    rcases op with op|op
    · exact ⟨u,v,h,true,fun r => congrFun op r⟩
    · exact ⟨u,v,h,false,fun r => congrFun op r⟩
  obtain ⟨C,sz,ao,nodup,out,gate,reads⟩ := reify Q rows fs law' a b ne
  refine ⟨C,fs.length,a.val,b.val,by omega,ao,nodup,out,gate,?_,?_⟩
  · intro u l inc
    have choice : ∃ k : Fin 4, pt l k = u := by
      rcases inc with h|h|h|h
      · exact ⟨0, by simpa [pt,List.getD_eq_getElem?_getD] using h.symm⟩
      · exact ⟨1, by simpa [pt,List.getD_eq_getElem?_getD] using h.symm⟩
      · exact ⟨2, by simpa [pt,List.getD_eq_getElem?_getD] using h.symm⟩
      · exact ⟨3, by simpa [pt,List.getD_eq_getElem?_getD] using h.symm⟩
    obtain ⟨k,hk⟩ := choice
    let t : Fin 13 × Fin 4 := (l,k)
    let v : Fin 26 → Bool := fun j => decide (j=Fin.castAdd 13 u ∨ j=Fin.natAdd 13 l)
    have eq : rows (.inl t) = v := by change (fun j => decide (j=Fin.castAdd 13 (pt l k) ∨ j=Fin.natAdd 13 l)) = v; rw [hk]
    change PEqualNP.BlindGate.wireValue C 26 v a.val=true ∧ PEqualNP.BlindGate.wireValue C 26 v b.val=true
    rw [←eq,reads (.inl t) a,reads (.inl t) b]
    have h := pos t
    change ((List.ofFn (fun k r => rows' r k) ++ fs).getD a.val (fun _ => false)) (.inl t) = true ∧
      ((List.ofFn (fun k r => rows' r k) ++ fs).getD b.val (fun _ => false)) (.inl t) = true at h
    rwa [eqRows] at h
  · intro z hz
    obtain ⟨m,heq,hsel⟩ := geometry z hz
    have eq : z = rows (.inr m) := heq
    have sel : z 13 = !((neg m) 0 || (neg m) 1 || (neg m) 3 || (neg m) 9) := hsel
    have raw := nos m
    change ((List.ofFn (fun k r => rows' r k) ++ fs).getD (if ds.any (fun d => neg' m (Fin.castAdd 13 d)) then b.val else a.val) (fun _ => false)) (.inr m) = false at raw
    rw [eqRows, same] at raw
    have selector : ds.any (fun d => neg m (Fin.castAdd 13 d)) = !z 13 := by
      rw [sel]
      simp [ds, Bool.or_assoc]
    rw [selector] at raw
    cases pick : z 13
    · rw [pick] at raw
      change PEqualNP.BlindGate.wireValue C 26 z b.val = false
      rw [eq, reads (.inr m) b]
      exact raw
    · rw [pick] at raw
      change PEqualNP.BlindGate.wireValue C 26 z a.val = false
      rw [eq, reads (.inr m) a]
      exact raw
