module

public import Oberwolfach.MarkedSampleReservedDeepBalances
public import Oberwolfach.MarkedSampleClearedStarNeighbours
public import Oberwolfach.MarkedFiniteStarClearing

@[expose] public section

/-! All support and local balance inputs for the actual deep cover follow
from the divisible outer graph, the divisible corrected inner graph, and
the exact prescribed-edge intersection of the preceding packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_deep_host_inputs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hH:∀ x u,¬(H false x u∧H true x u))
    (I T:Finset V) (J W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS m→
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    M.biUnion markedWheelArcs⊆Finset.univ\KA→
    M.biUnion markedWheelSpokePairs⊆S\KS→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)→
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let src':=Sum.elim (fun e:E₀'=>e.val.1) (fun e:E₁'=>e.val.1)
    let dst':=Sum.elim (fun e:E₀'=>e.val.2) (fun e:E₁'=>e.val.2)
    (∀ v∈T,
      (Finset.univ.filter (fun a=>dst' a=v)).card=(Finset.univ.filter (fun a=>src' a=v)).card ∧
      (Finset.univ.filter (fun a=>dst' a=v)).card=
        (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1=v)).card ∧
      (Finset.univ.filter (fun a=>dst' a=v∧markedArcType a=true)).card=
        (Finset.univ.filter (fun z:V×U=>H' true z.1 z.2∧z.1=v)).card) ∧
    (∀ u∈W,Fintype.card (hubNeighbourClass (H' false) (H' true) u false)=
      m*Fintype.card (hubNeighbourClass (H' false) (H' true) u true)) ∧
    (∀ a:E₀'⊕E₁',dst' a∈T→src' a∉I) ∧
    (∀ a:E₀'⊕E₁',src' a∈T→dst' a∉I) ∧
    (∀ x∈T,∀ u,H' false x u∨H' true x u→u∉J) ∧
    (∀ u∈W,∀ x,H' false x u∨H' true x u→x∉I):=by
  intro E₀ E₁ tail head ktail khead S DA DS₀ hDA hDS CA CS houter hinner KA KS M hM hMA hMS hexact
  let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
  let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
  have hCS:CS⊆S:=fun z hz=>(Finset.mem_filter.mp (Finset.mem_sdiff.mp hz).1).1
  have hbal:=marked_sample_reserved_star_packing_balances P π d m σ H hH T W CA CS hCS
    houter hinner M hM hMA hMS
  have hpres:markedFiniteResources tail head ktail khead π DA DS₀⊆
      (markedFiniteResources tail head ktail khead π Finset.univ S).filter (markedInnerResource I J):=by
    rw [←markedFiniteResources_inner tail head ktail khead π Finset.univ S I J hI]
    apply Finset.union_subset
    · apply Finset.Subset.trans _ Finset.subset_union_left
      apply Finset.image_subset_image
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hDA a ha⟩
    · apply Finset.Subset.trans _ Finset.subset_union_right
      apply Finset.image_subset_image
      intro z hz
      exact Finset.mem_filter.mpr ⟨(hDS z hz).2.2,(hDS z hz).1,(hDS z hz).2.1⟩
  have hclear:=marked_finite_prescribed_star_clearing tail head ktail khead π
    (markedSampleArc_physical_injective P π (3*d) _) Finset.univ DA S DS₀ I T J W hI hT hpres M hexact
  have harcs:Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)=
      (Finset.univ\KA)\M.biUnion markedWheelArcs:=by
    rw [markedSampleArcSetGraph_remaining]
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union]
    tauto
  have hspokes:Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧
      ¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))=(S\KS)\M.biUnion markedWheelSpokePairs:=by
    ext z
    simp only [DS,markedFiniteSpokeGraph_adj,S,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_sdiff,Finset.mem_union]
    tauto
  have hsupp:=marked_sample_cleared_star_neighbours P π d σ H DR DS I T J W hTI hWJ hI hT
  dsimp only at hsupp
  have hsupp':=hsupp (by rw [harcs,hspokes];exact hclear)
  exact ⟨hbal.1,hbal.2,hsupp'⟩

end Oberwolfach
