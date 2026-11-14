module

public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal
public import Oberwolfach.MarkedPreselectedAbsorberProtectedDecomposition

@[expose] public section
/-! Select the manuscript's fixed terminal absorber before the cover-down,
retaining its size, exclusions and avoidance of the first inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_select_fixed_terminal_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l size a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    MarkedReservedTerminalAbsorberProperty tail head ktail khead (H false) (H true) π (3*d) l size a₀ b₀ e₀ f ε→
    ∀ (X W I:Finset V) (Z B J:Finset U),
    X.card+Z.card≤size→X⊆W→Z⊆B→I⊆W→J⊆B→(∀ v,π v∈I↔v∈I)→
    (W.card:ℝ)≤ε*Fintype.card V+f→(B.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      C.edges.filter (markedInnerResource I J)=∅∧
      MarkedFixedTerminalAbsorber P π d (l+4) σ H C.edges X Z:=by
  intro E K tail head ktail khead hprop X W I Z B J hsize hX hZ hI hJ hπ hW hB F₀ hF
  obtain ⟨C,hF₀,hCe,hCr,hCu,hCold,hAvoid,hDec,hTransfer,hUniversal⟩:=
    marked_preselected_absorber_decomposes_and_avoids_inner_after_deletions
      P π d l size a₀ b₀ e₀ f ε σ H hprop X W Z B hsize hX hZ hW hB F₀ hF
  have hEmpty:C.edges.filter (markedInnerResource I J)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heC,heInner⟩:=Finset.mem_filter.mp he
    exact hAvoid I J hπ hI hJ e heC heInner
  have hU:MarkedUniversalTerminalDeletionAbsorber P π d (l+4) σ H C.edges X Z:=hUniversal
  exact ⟨C,hF₀,hCe,hCr,hCu,hEmpty,
    marked_universal_terminal_absorber_is_fixed P π d (l+4) σ H C.edges X Z hU⟩
end Oberwolfach
