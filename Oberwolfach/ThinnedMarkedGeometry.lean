module

public import Oberwolfach.ThinnedMarkedCoordinates

@[expose] public section

/-! Separation of the actual supports for the two-hub common weighting.
Both root spokes and the root coin are absent when its virtual spoke
resource is omitted; no presence assumption on those roots is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m d : ℕ} {π : Equiv.Perm V} {H₀ Hₖ : V→Unit→Prop}

theorem commonMappedCoordinates_candidate_disjoint (hd : 1≤d) (hm : 2≤m)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (a b : ((V×V)⊕(V×V))⊕(Bool×V×Unit))
    (ha : a∈typedMarkedOccurrenceResources W) (hb : b∈typedMarkedOccurrenceResources W) (hne : a≠b)
    (u u' : U) :
    Disjoint (rawMarkedResourceCoordinates π d (commonResourceAtHub u a))
      (rawMarkedResourceCoordinates π d (commonResourceAtHub u' b)) := by
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
    | inr b=>simp [commonResourceAtHub,rawMarkedResourceCoordinates]
  | inr a=>
    cases b with
    | inl b=>simp [commonResourceAtHub,rawMarkedResourceCoordinates]
    | inr b=>
      obtain ⟨i,hi⟩ := (typedMarkedOccurrenceResources_spoke W a).mp ha
      obtain ⟨j,hj⟩ := (typedMarkedOccurrenceResources_spoke W b).mp hb
      have hij : i≠j := by intro hij;subst j;exact hne (congrArg Sum.inr (hi.symm.trans hj))
      have hv : W.1.val i=a.2.1 := congrArg (fun z : Bool×V×Unit=>z.2.1) hi
      have hw : W.1.val j=b.2.1 := congrArg (fun z : Bool×V×Unit=>z.2.1) hj
      have hsep : ¬PermutationClose π (3*d) a.2.1 b.2.1 := by
        rw [← hv,← hw];exact W.1.property.1 i j hij
      apply Finset.disjoint_left.mpr
      intro e he hf
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp he
      obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hf
      have hxy := Sum.inr.inj (he.trans hf.symm)
      exact Finset.disjoint_left.mp (rawIntervalFamilyCoordinates_disjoint π d (a.2.1,u) (b.2.1,u') (Or.inr hsep))
        hx (hxy ▸ hy)

theorem thinnedMarkedCoordinates_candidate_disjoint (hd : 1≤d) (hm : 2≤m)
    (W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ)
    (a b : ((V×V)⊕(V×V))⊕(Bool×V×Unit))
    (ha : a∈typedMarkedOccurrenceResources W) (hb : b∈typedMarkedOccurrenceResources W) (hne : a≠b)
    (u u' : U) :
    Disjoint (thinnedMarkedResourceCoordinates π d u u' a) (thinnedMarkedResourceCoordinates π d u u' b) := by
  have hraw := commonMappedCoordinates_candidate_disjoint (U:=U) hd hm W a b ha hb hne
  have himage : Disjoint
      ((rawMarkedResourceCoordinates π d (commonResourceAtHub u a) ∪ rawMarkedResourceCoordinates π d (commonResourceAtHub u' a)).image (Sum.inl (β:=V)))
      ((rawMarkedResourceCoordinates π d (commonResourceAtHub u b) ∪ rawMarkedResourceCoordinates π d (commonResourceAtHub u' b)).image (Sum.inl (β:=V))) := by
    rw [Finset.disjoint_image Sum.inl_injective]
    exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hraw u u,hraw u u'⟩,
      Finset.disjoint_union_right.mpr ⟨hraw u' u,hraw u' u'⟩⟩
  have hcross (S : Finset (RawWheelCoordinate V U)) (x : V) :
      Disjoint (S.image (Sum.inl (β:=V))) {Sum.inr x} := by simp
  unfold thinnedMarkedResourceCoordinates
  cases a with
  | inl a=>
    cases b with
    | inl b=>simpa only [Finset.union_empty] using himage
    | inr b=>
      simpa only [Finset.union_empty,Finset.disjoint_union_right] using ⟨himage,hcross _ b.2.1⟩
  | inr a=>
    cases b with
    | inl b=>
      simpa only [Finset.union_empty,Finset.disjoint_union_left] using ⟨himage,(hcross _ a.2.1).symm⟩
    | inr b=>
      have hv : a.2.1≠b.2.1 := by
        obtain ⟨i,hi⟩ := (typedMarkedOccurrenceResources_spoke W a).mp ha
        obtain ⟨j,hj⟩ := (typedMarkedOccurrenceResources_spoke W b).mp hb
        intro hv
        have hij : i=j := permutationSeparated_injective π (3*d) W.1.val W.1.property.1 (by
          simpa only [← congrArg (fun z : Bool×V×Unit=>z.2.1) hi,
            ← congrArg (fun z : Bool×V×Unit=>z.2.1) hj] using hv)
        exact hne (congrArg Sum.inr (hi.symm.trans (hij ▸ hj)))
      dsimp only
      rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
      exact ⟨⟨himage,hcross _ b.2.1⟩,⟨(hcross _ a.2.1).symm,
        Finset.disjoint_singleton.mpr (fun he=>hv (Sum.inr.inj he))⟩⟩

end Oberwolfach
