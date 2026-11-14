module

public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedFiniteRemainderTransfer
public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedPhysicalDeletionComposition

@[expose] public section
/-! A divisible terminal remainder disjoint from deleted physical resources
can be represented by the same typed arcs and spokes in the deleted host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_terminal_remainder_survives_cumulative_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Covered:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
    (∀ z∈S,z.1∈X∧z.2∈Z∧(H false z.1 z.2∨H true z.1 z.2))→
    MarkedRemainderDivisible tail head ktail khead (H true) A S m→
    Disjoint (markedFiniteResources tail head ktail khead π A S) Covered→
    let DR:=physicalEdgeGraph (markedReservedRimPairs Covered)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs Covered)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∃ A':Finset (E'⊕K'),
    (∀ a∈A',Sum.elim t' kt' a∈X∧Sum.elim h' kh' a∈X)∧
    (∀ z∈S,z.1∈X∧z.2∈Z∧(H' false z.1 z.2∨H' true z.1 z.2))∧
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A' S m∧
    markedFiniteResources t' h' kt' kh' π A' S=markedFiniteResources tail head ktail khead π A S:=by
  intro E K tail head ktail khead A S hA hS hdiv hdis DR DS σ' H' E' K' t' h' kt' kh'
  have hgraphs:=marked_reserved_resource_graphs Covered
  have harc:∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉Covered:=by
    intro a ha hc
    apply Finset.disjoint_left.mp hdis ?_ hc
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hsp:∀ z∈S,¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=by
    intro z hz hadj
    have hc:Sum.inr z∈Covered:=(hgraphs.2.1 z.1 z.2).mp hadj
    apply Finset.disjoint_left.mp hdis ?_ hc
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
  let f:A→E'⊕K':=fun a=>by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl e=>
      have hc:=harc (Sum.inl e) ha
      have hn:¬DR.Adj e.val.1 e.val.2:=by
        intro he
        exact hc ((hgraphs.1 e.val.1 e.val.2).mp he).2
      have he:s(e.val.1,e.val.2)∉DR.edgeFinset:=by
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn
      exact Sum.inl ⟨e.val,(markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false e.val.1 e.val.2).mpr ⟨e.property,by simpa using he⟩⟩
    | inr e=>
      have hc:=harc (Sum.inr e) ha
      have hn:¬DR.Adj e.val.1 (π e.val.2):=by
        intro he
        exact hc ((hgraphs.1 e.val.1 (π e.val.2)).mp he).2
      have he:s(e.val.1,π e.val.2)∉DR.edgeFinset:=by
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn
      exact Sum.inr ⟨e.val,(markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true e.val.1 e.val.2).mpr ⟨e.property,by simpa using he⟩⟩
  have htail:∀ a,Sum.elim t' kt' (f a)=Sum.elim tail ktail a.val:=by
    intro ⟨a,ha⟩;cases a <;> rfl
  have hhead:∀ a,Sum.elim h' kh' (f a)=Sum.elim head khead a.val:=by
    intro ⟨a,ha⟩;cases a <;> rfl
  have htype:∀ a,markedArcType (f a)=markedArcType a.val:=by
    intro ⟨a,ha⟩;cases a <;> rfl
  have hf:=marked_finite_remainder_map_injective π
    (markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))) A f htail hhead htype
  have hH:∀ z∈S,H' true z.1 z.2↔H true z.1 z.2:=by
    intro z hz
    change (H true z.1 z.2∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))↔_
    simp [hsp z hz]
  refine ⟨Finset.univ.image f,?_,?_,?_,?_⟩
  · intro a ha
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp ha
    rw [htail, hhead]
    exact hA a.val a.property
  · intro z hz
    obtain ⟨hv,hu,hh⟩:=hS z hz
    exact ⟨hv,hu,hh.elim (fun h=>Or.inl ⟨h,hsp z hz⟩) (fun h=>Or.inr ⟨h,hsp z hz⟩)⟩
  · exact marked_finite_remainder_image_divisible A S f hf htail hhead htype hH hdiv
  · exact marked_finite_remainder_image_resources π A S f htail hhead htype
end Oberwolfach
