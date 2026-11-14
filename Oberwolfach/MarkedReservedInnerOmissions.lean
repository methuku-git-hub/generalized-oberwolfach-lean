module

public import Oberwolfach.MarkedReservedDeletionInnerAgreement
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section
/-! Prescribed omissions remain inside the same inner pair and the spoke
omissions remain present after reserving resources outside that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_inner_omissions_remain_valid
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hC:∀ e∈C,¬markedInnerResource I J e):
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
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2);
    (∀ a∈DA',Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I)∧
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S'):=by
  intro E K tail head ktail khead S DR DS σ' H' E' K' t' h' kt' kh' emb DA DS₀ hDA hDS DA' S'
  constructor
  · intro a ha
    have hh:=hDA (emb a) (Finset.mem_filter.mp ha).2
    have he:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ DR.edgeFinset a
    exact ⟨he.1 ▸ hh.1,he.2.1 ▸ hh.2⟩
  · intro z hz
    obtain ⟨hi,hj,hs⟩:=hDS z hz
    have hd:¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=(marked_reserved_graphs_avoid_internal_resources C I J hC).2 _ hi _ hj
    refine ⟨hi,hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    simpa only [H',markedDeletePhysicalSpokes,hd,not_false_eq_true,and_true] using (Finset.mem_filter.mp hs).2
end Oberwolfach
