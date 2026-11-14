module

public import Oberwolfach.MarkedReservedCanonicalDeepInputs
public import Oberwolfach.MarkedInnerExactnessStarExclusions
public import Oberwolfach.MarkedPackingResourceDegreeTransfer
public import Oberwolfach.MarkedReservedDeepHost
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
theorem marked_reserved_prescribed_deep_host_balanced
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hTI:T⊆I) (hWJ:W⊆J) (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T) (hC:∀ e∈C,¬markedInnerResource I J e):
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
      (∀ x,(markedPackingRimGraph M').degree x=(markedPackingRimGraph M).degree x)∧
      (∀ x,(Finset.univ.filter (markedPackingSpokes M' x)).card=(Finset.univ.filter (markedPackingSpokes M x)).card)∧
      (∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M' x u)).card=
        (Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card)∧
      let DR₂:=markedSampleArcSetGraph P π d σ' (KA'∪M'.biUnion markedWheelArcs)
      let DS₂:=markedFiniteSpokeGraph (KS'∪M'.biUnion markedWheelSpokePairs)
      let σ₂:=rawMarkedDeleteRims σ' DR₂.edgeFinset
      let H₂:=markedDeletePhysicalSpokes H' DS₂
      let E₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) false
      let K₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) true
      let src₂:=Sum.elim (fun e:E₂=>e.val.1) (fun e:K₂=>e.val.1)
      let dst₂:=Sum.elim (fun e:E₂=>e.val.2) (fun e:K₂=>e.val.2);
      (∀ v∈T,
        (Finset.univ.filter (fun a=>dst₂ a=v)).card=(Finset.univ.filter (fun a=>src₂ a=v)).card ∧
        (Finset.univ.filter (fun a=>dst₂ a=v)).card=
          (Finset.univ.filter (fun z:V×U=>(H₂ false z.1 z.2∨H₂ true z.1 z.2)∧z.1=v)).card ∧
        (Finset.univ.filter (fun a=>dst₂ a=v∧markedArcType a=true)).card=
          (Finset.univ.filter (fun z:V×U=>H₂ true z.1 z.2∧z.1=v)).card) ∧
      (∀ u∈W,Fintype.card (hubNeighbourClass (H₂ false) (H₂ true) u false)=
        m*Fintype.card (hubNeighbourClass (H₂ false) (H₂ true) u true)) ∧
      (∀ a:E₂⊕K₂,dst₂ a∈T→src₂ a∉I) ∧
      (∀ a:E₂⊕K₂,src₂ a∈T→dst₂ a∉I) ∧
      (∀ x∈T,∀ u,H₂ false x u∨H₂ true x u→u∉J) ∧
      (∀ u∈W,∀ x,H₂ false x u∨H₂ true x u→x∉I):=by
  intro E K tail head ktail khead S DA DS₀ CA CS KA KS hH hOuter hDec hInner hDS M hM hdis hDA hexact DR DS σ' H' E' K' t' h' kt' kh' emb DA' S' CA' CS' KA' KS'
  have hexcl:=marked_inner_exactness_implies_star_exclusions
    (markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))) I T J W hI DA DS₀ M hexact
  obtain ⟨M',hM',hres,hMA',hMS',hexact',hH',hOuter',hInner',hDA',hDS'⟩:=
    marked_reserved_canonical_deep_inputs_transfer P π d m σ H C I T J W hI hC DA DS₀ hH hOuter hDec hInner hDS M hM hdis hexcl.1 hexcl.2 hDA hexact
  have hdeg:=marked_packing_resource_equality_degree_counts M' M hres
  refine ⟨M',hM',hres,hdeg.1,hdeg.2.1,hdeg.2.2,?_⟩
  exact marked_reserved_deep_host_inputs P π d m σ' H' hH' I T J W hTI hWJ hI hT DA' DS₀ hDA' hDS' hOuter' hInner' M' hM' hMA' hMS' hexact'
end Oberwolfach
