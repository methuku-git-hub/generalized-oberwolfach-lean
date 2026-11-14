module

public import Oberwolfach.MarkedReservedPackingInnerExactness
public import Oberwolfach.MarkedReservedCanonicalStarArcs
public import Oberwolfach.MarkedPackingSpokesInHost
public import Oberwolfach.MarkedReservedCanonicalSpokes
public import Oberwolfach.MarkedReservedBothDivisibleRemainders
public import Oberwolfach.MarkedReservedInnerOmissions

@[expose] public section
/-! Transfer the first packing with the canonical inputs used by the deep
cover-down: prescribed omissions, star exclusions, and inner resource identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_canonical_deep_inputs_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (DA:Finset (E⊕K)) (DS₀:Finset (V×U)),
    let CA:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W);
    (∀ v u,¬(H false v u∧H true v u))→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    HasResourceDecomposition (fun X:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources X) C→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS m→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    M.biUnion markedWheelArcs⊆Finset.univ\KA→M.biUnion markedWheelSpokePairs⊆S\KS→
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)→
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
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    let CA':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I))\DA'
    let CS':=(S'.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    let KA':=CA'.filter (fun a=>Sum.elim t' kt' a∈T∨Sum.elim h' kh' a∈T)
    let KS':=CS'.filter (fun z=>z.1∈T∨z.2∈W);
    ∃ M':Finset (MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true)),
      (∀ X∈M',∀ Y∈M',X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
      M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
      M'.biUnion markedWheelArcs⊆Finset.univ\KA'∧M'.biUnion markedWheelSpokePairs⊆S'\KS'∧
      (M'.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
        (markedFiniteResources t' h' kt' kh' π DA' DS₀).filter (markedStarResource T W) ∧
      (∀ v u,¬(H' false v u∧H' true v u)) ∧
      MarkedRemainderDivisible t' h' kt' kh' (H' true) Finset.univ S' m ∧
      MarkedRemainderDivisible t' h' kt' kh' (H' true) CA' CS' m ∧
      (∀ a∈DA',Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I) ∧
      (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S'):=by
  intro E K tail head ktail khead S DA DS₀ CA CS KA KS hH hOuter hDec hInner hDS M hM hdis hMA hMS hDA hexact DR DS σ' H' E' K' t' h' kt' kh' emb DA' S' CA' CS' KA' KS'
  have hA:Disjoint KA (M.biUnion markedWheelArcs):=Finset.disjoint_left.mpr (by
    intro a ha hmem
    exact (Finset.mem_sdiff.mp (hMA hmem)).2 ha)
  have hS:Disjoint KS (M.biUnion markedWheelSpokePairs):=Finset.disjoint_left.mpr (by
    intro z hz hmem
    exact (Finset.mem_sdiff.mp (hMS hmem)).2 hz)
  obtain ⟨M',hM',hres,hA',hS',hexact'⟩:=
    marked_reserved_packing_transfer_preserves_inner_exactness P π d m σ H C I T J W hI hC M KA DA KS DS₀ hM hdis hA hS hDA hexact
  have hKA:KA'=Finset.univ.filter (fun a:E'⊕K'=>emb a∈KA):=
    marked_sample_canonical_star_arcs_preimage P π d σ DR.edgeFinset I T DA
  have hCS:CS'=CS:=by
    simpa only [CS',CS,S',S,Finset.filter_filter,Finset.mem_filter,Finset.mem_univ,true_and] using
      marked_reserved_canonical_inner_spokes H C I J hC DS₀
  have hKS:KS'=KS:=by simp only [KS',KS,hCS]
  rw [←hKA] at hA'
  rw [←hKS] at hS'
  have hsub:=marked_packing_disjoint_exclusions_give_host_subsets M' KA' KS' hA' hS'
  have hH':∀ v u,¬(H' false v u∧H' true v u):=by
    intro v u hh
    exact hH v u ⟨hh.1.1,hh.2.1⟩
  have hboth:=marked_reserved_outer_and_inner_remainders_divisible P π d m σ H C I J hI hC hH hOuter hDec DA DS₀
    (by simpa only [CS,S,Finset.filter_filter,Finset.mem_filter,Finset.mem_univ,true_and] using hInner)
  have hvalid:=marked_reserved_inner_omissions_remain_valid P π d σ H C I J hC DA DS₀ hDA hDS
  refine ⟨M',hM',hres,hsub.1,hsub.2,hexact',hH',hboth.1,?_,hvalid.1,hvalid.2⟩
  simpa only [CS',S',Finset.filter_filter,Finset.mem_filter,Finset.mem_univ,true_and] using hboth.2.1
end Oberwolfach
