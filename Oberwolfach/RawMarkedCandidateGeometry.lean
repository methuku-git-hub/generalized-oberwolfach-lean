module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.TypedMarkedPotentialResources

@[expose] public section

/-! Independence within a separated parent wheel is proved from its actual
physical edges and interval-coordinate sets. The whole potential arc map
is not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b : ℕ} {π : Equiv.Perm V} {H₀ Hₖ : V→U→Prop}

theorem markedPairCycle_edge_ordinary
    (C : MarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b) (i : Fin m) :
    markedCycleTypedEdge Prod.fst Prod.snd Prod.fst Prod.snd m π b C i.castSucc=
      Sum.inl (C.val i.castSucc,C.val i.succ) := by
  simp only [markedCycleTypedEdge,Fin.snoc_castSucc]
  exact congrArg Sum.inl (Prod.ext (Classical.choose_spec (C.property.2.1 i)).1
    (Classical.choose_spec (C.property.2.1 i)).2)

theorem markedPairCycle_edge_marked
    (C : MarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b) :
    markedCycleTypedEdge Prod.fst Prod.snd Prod.fst Prod.snd m π b C (Fin.last m)=
      Sum.inr (C.val (Fin.last m),C.val 0) := by
  simp only [markedCycleTypedEdge,Fin.snoc_last]
  exact congrArg Sum.inr (Prod.ext (Classical.choose_spec C.property.2.2).1
    (Classical.choose_spec C.property.2.2).2)

theorem markedPairCycle_physical_injective (hm : 2≤m) (hb : 1≤b)
    (C : MarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b) :
    Function.Injective (markedPairPhysical π ∘
      markedCycleTypedEdge Prod.fst Prod.snd Prod.fst Prod.snd m π b C) := by
  have hinj := separated_successor_edges_injective hm π b hb C.val C.property.1
  intro i j
  refine Fin.lastCases ?_ (fun i=>?_) i <;>
    refine Fin.lastCases ?_ (fun j=>?_) j
  · intro _;rfl
  · intro h
    simp only [Function.comp_apply,markedPairCycle_edge_marked,markedPairCycle_edge_ordinary,
      markedPairPhysical,Sum.elim_inl,Sum.elim_inr] at h
    have he : (Sum.inr () : Fin m⊕Unit)=Sum.inl j := hinj h
    cases he
  · intro h
    simp only [Function.comp_apply,markedPairCycle_edge_marked,markedPairCycle_edge_ordinary,
      markedPairPhysical,Sum.elim_inl,Sum.elim_inr] at h
    have he : (Sum.inl i : Fin m⊕Unit)=Sum.inr () := hinj h
    cases he
  · intro h
    simp only [Function.comp_apply,markedPairCycle_edge_ordinary,
      markedPairPhysical,Sum.elim_inl] at h
    have he : (Sum.inl i : Fin m⊕Unit)=Sum.inl j := hinj h
    exact congrArg Fin.castSucc (Sum.inl.inj he)

theorem rawMarkedCoordinates_candidate_disjoint (d : ℕ) (hd : 1≤d) (hm : 2≤m)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (a b : ((V×V)⊕(V×V))⊕(Bool×V×U))
    (ha : a∈typedMarkedOccurrenceResources W) (hb : b∈typedMarkedOccurrenceResources W) (hne : a≠b) :
    Disjoint (rawMarkedResourceCoordinates π d a) (rawMarkedResourceCoordinates π d b) := by
  cases a with
  | inl a=>
    cases b with
    | inl b=>
      obtain ⟨i,hi⟩ := (typedMarkedOccurrenceResources_rim W a).mp ha
      obtain ⟨j,hj⟩ := (typedMarkedOccurrenceResources_rim W b).mp hb
      apply Finset.disjoint_singleton.mpr
      intro he
      have hp : markedPairPhysical π a=markedPairPhysical π b := Sum.inl.inj he
      have hij : i=j := markedPairCycle_physical_injective hm (by omega : 1≤3*d) W.1 (by
        simpa only [Function.comp_apply,hi,hj] using hp)
      apply hne
      exact congrArg Sum.inl (hi.symm.trans (hij ▸ hj))
    | inr b=>simp [rawMarkedResourceCoordinates]
  | inr a=>
    cases b with
    | inl b=>simp [rawMarkedResourceCoordinates]
    | inr b=>
      obtain ⟨i,hi⟩ := (typedMarkedOccurrenceResources_spoke W a).mp ha
      obtain ⟨j,hj⟩ := (typedMarkedOccurrenceResources_spoke W b).mp hb
      have hij : i≠j := by
        intro hij;subst j;exact hne (congrArg Sum.inr (hi.symm.trans hj))
      have hv : W.1.val i=a.2.1 := congrArg (fun z : Bool×V×U=>z.2.1) hi
      have hw : W.1.val j=b.2.1 := congrArg (fun z : Bool×V×U=>z.2.1) hj
      have hsep : ¬PermutationClose π (3*d) a.2.1 b.2.1 := by
        rw [← hv,← hw];exact W.1.property.1 i j hij
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp he
      obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hf
      have hxy := Sum.inr.inj (he.trans hf.symm)
      exact Finset.disjoint_left.mp (rawIntervalFamilyCoordinates_disjoint π d a.2 b.2 (Or.inr hsep))
        hx (hxy ▸ hy)

end Oberwolfach
