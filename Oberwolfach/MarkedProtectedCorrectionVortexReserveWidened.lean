module

public import Oberwolfach.MarkedProtectedCorrectionVortexReserve
public import Oberwolfach.MarkedReferenceDeletionLossMonotone
public import Oberwolfach.MarkedProtectedCorrectionReferenceState
public import Oberwolfach.MarkedCorrectedVortexTerminalReserve

@[expose] public section
/-! From the protected correction on the selected sample, choose the actual
terminal reserve and retain the valid deletion used by the matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_protected_correction_vortex_reserve_widened
    (r d size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ ξ:ℝ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size)
    (gammaLoss sigmaLoss extra gammaTotal sigmaTotal:ℝ)
    (hγTotal:gammaLoss+extra≤gammaTotal) (hσTotal:sigmaLoss+extra≤sigmaTotal) (hξ:0≤ξ)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card V)≤min gammaLoss sigmaLoss)
    (hsep:∀v u,¬(H false v u∧H true v u))
    (hCorr:MarkedProtectedAbsorbableCorrectionWithBounds G π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1))
    (F₀:Finset (Finset V⊕(V×U))) (hF₀:F₀.card≤f₀) (hExtra:(e₀:ℝ)≤extra):
    ∃D₀:MarkedReferenceDeletion G π d σ,
      D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) gammaLoss sigmaLoss ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph G π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) true;
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ' H' C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
    ∃ D₂:MarkedReferenceDeletion G π d σ,
      D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) gammaTotal sigmaTotal ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges :=by
  obtain ⟨D₀,hvalid,C,hF₀,hCe,hCr,hCu,hfixed,horiginal,D₂,h₂,hremoved,hremain,hdis⟩:=
    marked_protected_correction_vortex_reserve r d size a₀ b₀ e₀ f₀ εAbs ζ ξ G D m β ε Q π hpres L hL σ H
      hreg hn hD hρhi he heAbs hsize gammaLoss sigmaLoss extra hξ hbudget hsep hCorr F₀ hF₀ hExtra
  refine ⟨D₀,hvalid,C,hF₀,hCe,hCr,hCu,hfixed,horiginal,D₂,?_,hremoved,hremain,hdis⟩
  exact marked_reference_deletion_valid_loss_mono D₂ H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
    (gammaLoss+extra) (sigmaLoss+extra) gammaTotal sigmaTotal hγTotal hσTotal h₂
end Oberwolfach
