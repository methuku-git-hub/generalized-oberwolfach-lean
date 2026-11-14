module

public import Oberwolfach.MarkedReservedAbsorberAdaptiveDeletion
public import Oberwolfach.MarkedReservedDecompositionAfterDeletion
public import Oberwolfach.MarkedSupportedReserveAvoidsInnerSubset
public import Oberwolfach.MarkedReservedAbsorberUniversalTransfer
public import Oberwolfach.MarkedReservedResourceDeletionProtection
public import Oberwolfach.MarkedSampleDeletedArcs

@[expose] public section

/-! One absorber is chosen before all later physical deletions. Whenever a
later deletion avoids its resources and the terminal spoke pair, the same
absorber works for every divisible terminal remainder of that later host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_preselected_absorber_decomposes_and_avoids_inner_after_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l size a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    MarkedReservedTerminalAbsorberProperty tail head ktail khead (H false) (H true) π (3*d) l size a₀ b₀ e₀ f ε→
    ∀ (X W:Finset V) (Z B:Finset U), X.card+Z.card≤size→X⊆W→Z⊆B→
    (W.card:ℝ)≤ε*Fintype.card V+f→(B.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e)∧
      (∀ (I:Finset V) (J:Finset U),(∀ x,π x∈I↔x∈I)→I⊆W→J⊆B→
        ∀ e∈C.edges,¬markedInnerResource I J e)∧
      HasResourceDecomposition
        (fun Q:MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources Q) C.edges∧
      (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
        (∀ x y,Sum.inl ({x,y}:Finset V)∈C.edges→¬DR.Adj x y)→
        (∀ v u,Sum.inr (v,u)∈C.edges→¬DS.Adj (Sum.inl v) (Sum.inr u) )→
        let σ':=rawMarkedDeleteRims σ DR.edgeFinset
        let H':=markedDeletePhysicalSpokes H DS
        let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
        let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
        HasResourceDecomposition
          (fun Q:MarkedWheel (fun e:E'=>e.val.1) (fun e:E'=>e.val.2)
            (fun e:K'=>e.val.1) (fun e:K'=>e.val.2) (l+4) π (3*d) (H' false) (H' true)=>markedWheelPhysicalResources Q) C.edges)∧
      ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
        (∀ x y,Sum.inl ({x,y}:Finset V)∈C.edges→¬DR.Adj x y)→
        (∀ v u,Sum.inr (v,u)∈C.edges→¬DS.Adj (Sum.inl v) (Sum.inr u))→
        (∀ v∈X,∀ u∈Z,¬DS.Adj (Sum.inl v) (Sum.inr u))→
        let σ':=rawMarkedDeleteRims σ DR.edgeFinset
        let H':=markedDeletePhysicalSpokes H DS
        let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
        let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
        let t':=fun e:E'=>e.val.1
        let h':=fun e:E'=>e.val.2
        let kt':=fun e:K'=>e.val.1
        let kh':=fun e:K'=>e.val.2;
        ∀ (A:Finset (E'⊕K')) (S:Finset (V×U)),
        (∀ a∈A,Sum.elim t' kt' a∈X∧Sum.elim h' kh' a∈X)→
        (∀ z∈S,z.1∈X∧z.2∈Z∧(H' false z.1 z.2∨H' true z.1 z.2))→
        MarkedRemainderDivisible t' h' kt' kh' (H' true) A S (l+4)→
        IsResourceAbsorber
          (fun Q:MarkedWheel t' h' kt' kh' (l+4) π (3*d) (H' false) (H' true)=>markedWheelPhysicalResources Q)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr) C.edges  :=by
  intro E K tail head ktail khead habs X W Z B hs hX hZ hW hB F₀ hF
  obtain ⟨C,hF₀,hCe,hCr,hCu,hCold,hCdec,htransfer⟩:=
    marked_preselected_absorber_after_adaptive_deletions P π d l size a₀ b₀ e₀ f ε σ H habs X W Z B hs hX hZ hW hB F₀ hF
  refine ⟨C,hF₀,hCe,hCr,hCu,hCold,?_,hCdec,?_,htransfer⟩
  · intro I J hI hIW hJB
    exact marked_supported_reserve_avoids_inner_subset C I W J B hI hIW hJB hCold
  · intro DR DS hR hS σ' H' E' K'
    exact marked_reserved_decomposition_after_avoiding_deletions P π d (l+4) σ H C.edges DR DS hR hS hCdec
end Oberwolfach
