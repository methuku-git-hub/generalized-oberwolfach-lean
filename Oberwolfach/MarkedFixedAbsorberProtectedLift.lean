module

public import Oberwolfach.MarkedTerminalRemainderSurvival
public import Oberwolfach.MarkedCommonSubhostTransfer
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! A fixed absorber selected after deletion remains fixed in the original
sample when the deleted resources avoid the protected terminal pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_fixed_absorber_protected_deletion_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Covered Reserve:Finset (Finset V⊕(V×U))) (I X:Finset V) (J Z:Finset U)
    (hI:∀v,π v∈I↔v∈I) (hXI:X⊆I) (hZJ:Z⊆J)
    (hCovered:Covered.filter (markedInnerResource I J)=∅):
    let DR:=physicalEdgeGraph (markedReservedRimPairs Covered)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs Covered)
    MarkedFixedTerminalAbsorber P π d m (rawMarkedDeleteRims σ DR.edgeFinset)
      (markedDeletePhysicalSpokes H DS) Reserve X Z→
    MarkedFixedTerminalAbsorber P π d m σ H Reserve X Z :=by
  intro DR DS habs
  intro A S hA hS hdiv
  have hdis:Disjoint (markedFiniteResources
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π A S) Covered:=by
    apply Finset.disjoint_left.mpr
    intro e he hc
    have heInner:markedInnerResource I J e:=by
      have hAr:A.filter (fun a=>Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈I ∧
          Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈I)=A:=by
        apply Finset.filter_eq_self.mpr
        intro a ha;exact ⟨hXI (hA a ha).1,hXI (hA a ha).2⟩
      have hSr:S.filter (fun z=>z.1∈I∧z.2∈J)=S:=by
        apply Finset.filter_eq_self.mpr
        intro z hz;exact ⟨hXI (hS z hz).1,hZJ (hS z hz).2.1⟩
      have hh:=markedFiniteResources_inner
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π A S I J hI
      rw [hAr,hSr] at hh
      rw [hh] at he
      exact (Finset.mem_filter.mp he).2
    have :e∈Covered.filter (markedInnerResource I J):=Finset.mem_filter.mpr ⟨hc,heInner⟩
    simpa only [hCovered,Finset.notMem_empty] using this
  obtain ⟨A',hA',hS',hdiv',hres⟩:=marked_terminal_remainder_survives_cumulative_deletion
    P π d m σ H Covered X Z A S hA hS hdiv hdis
  have hh:=habs A' S hA' hS' hdiv'
  rw [hres] at hh
  apply marked_common_subhost_transfer_to_later P π d m σ σ H H DR DS
  · intro mark x y he
    exact ((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset mark x y).mp he).1
  · intro b v u he
    exact he.1
  · exact hh
end Oberwolfach
