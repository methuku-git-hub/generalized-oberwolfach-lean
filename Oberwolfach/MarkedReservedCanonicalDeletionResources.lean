module

public import Oberwolfach.MarkedReservedInnerResourceSetLift
public import Oberwolfach.MarkedReservedCanonicalStarArcs
public import Oberwolfach.MarkedReservedCanonicalSpokes
public import Oberwolfach.MarkedFiniteResourcesPackingUnion

@[expose] public section
/-! The physical resources deleted for the canonical first cover agree
before and after removing the reserved absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_canonical_deletion_resources_equal
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset;
    ∀ (DA:Finset (E⊕K)) (DS₀:Finset (V×U)),
    let CA:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    let CA':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I))\DA'
    let CS':=(S'.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    let KA':=CA'.filter (fun a=>Sum.elim t' kt' a∈T∨Sum.elim h' kh' a∈T)
    let KS':=CS'.filter (fun z=>z.1∈T∨z.2∈W);
    ∀ (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (M':Finset (MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true))),
    M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources→
    markedFiniteResources t' h' kt' kh' π (KA'∪M'.biUnion markedWheelArcs) (KS'∪M'.biUnion markedWheelSpokePairs)=
    markedFiniteResources tail head ktail khead π (KA∪M.biUnion markedWheelArcs) (KS∪M.biUnion markedWheelSpokePairs):=by
  intro E K tail head ktail khead S DR DS σ' H' E' K' t' h' kt' kh' emb DA DS₀ CA CS KA KS DA' S' CA' CS' KA' KS' M M' hres
  have hKAin:∀ a∈KA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1).2
  have hKA:KA'=Finset.univ.filter (fun a:E'⊕K'=>emb a∈KA):=
    marked_sample_canonical_star_arcs_preimage P π d σ DR.edgeFinset I T DA
  have hCS:CS'=CS:=by
    simpa only [CS',CS,S',S,Finset.filter_filter,Finset.mem_filter,Finset.mem_univ,true_and] using
      marked_reserved_canonical_inner_spokes H C I J hC DS₀
  have hKS:KS'=KS:=by simp only [KS',KS,hCS]
  have hlift:=marked_reserved_inner_resources_lift P π d σ C I J hI hC KA KS hKAin
  rw [marked_finite_resources_union_packing,marked_finite_resources_union_packing,hres,hKS,hKA]
  exact congrArg (fun R=>R∪M.biUnion markedWheelPhysicalResources) hlift.2.2
end Oberwolfach
