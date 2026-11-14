module

public import Oberwolfach.MarkedReservedAbsorberAdaptiveDeletion
public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! A robust sampled host has the original-host absorber property by taking
empty physical deletions. Select its absorber before all later changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_robust_sample_selects_absorber_for_adaptive_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l size a₀ b₀ e₀ f:ℕ) (ε ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    0≤ζ→
    (∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→
      (∀ x,(DS.degree x:ℝ)≤ζ*Fintype.card V)→
      let σ':=rawMarkedDeleteRims σ DR.edgeFinset
      let H':=markedDeletePhysicalSpokes H DS
      MarkedReservedTerminalAbsorberProperty
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (H' false) (H' true) π (3*d) l size a₀ b₀ e₀ f ε)→
    ∀ (X W:Finset V) (Z B:Finset U), X.card+Z.card≤size→X⊆W→Z⊆B→
    (W.card:ℝ)≤ε*Fintype.card V+f→(B.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e)∧
      HasResourceDecomposition
        (fun Q:MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources Q) C.edges∧
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
          (A.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr) C.edges :=by
  intro E K tail head ktail khead hζ hrob X W Z B hs hX hZ hW hB F₀ hF
  have hn:0≤ζ*(Fintype.card V:ℝ):=mul_nonneg hζ (Nat.cast_nonneg _)
  have hbase:=hrob ⊥ ⊥ (by intro x;simpa using hn) (by intro x;simpa using hn)
  let adjInst:DecidableRel (⊥:SimpleGraph V).Adj:=fun a b=>Classical.propDecidable ((⊥:SimpleGraph V).Adj a b)
  let edgeInst:Fintype (⊥:SimpleGraph V).edgeSet:=@SimpleGraph.fintypeEdgeSet V ⊥ (Sym2.instFintype) adjInst
  change MarkedReservedTerminalAbsorberProperty
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V ⊥ edgeInst) (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V ⊥ edgeInst) (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    (markedDeletePhysicalSpokes H ⊥ false) (markedDeletePhysicalSpokes H ⊥ true) π (3*d) l size a₀ b₀ e₀ f ε at hbase
  rw [graph_bottom_edgeFinset_any_instance edgeInst,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hbase
  have habs:MarkedReservedTerminalAbsorberProperty tail head ktail khead (H false) (H true) π (3*d) l size a₀ b₀ e₀ f ε:=hbase
  exact marked_preselected_absorber_after_adaptive_deletions P π d l size a₀ b₀ e₀ f ε σ H habs
    X W Z B hs hX hZ hW hB F₀ hF
end Oberwolfach
