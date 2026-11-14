module

public import Oberwolfach.MarkedProtectedCorrectionVortexReserve
public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.FirstVortexConcreteBoundaryEvent

@[expose] public section
/-! Select the valid correction and its supported terminal reserve from the
protected-correction test on the same retained expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedCorrectionReserveFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_protected_correction_reserve
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (r d size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ ξ:ℝ) (G:SimpleGraph (Fin n)) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm (Fin n))
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length)
    (σ:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (hreg:G.IsRegularOfDegree D) (hD:0<D) (hρhi:initialIndexDensity U D≤1)
    (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size)
    (gammaLoss sigmaLoss:ℝ) (hξ:0≤ξ)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n)):
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      t J false false;
    MarkedProtectedAbsorbableCorrectionWithBounds G π d r size a₀ b₀ e₀ f₀ εAbs ζ ξ σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1) →
    ∃D₀:MarkedReferenceDeletion G π d σ,
      D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*n) (sigmaLoss*n) ∧
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph G π d σ D₀.arcs).edgeFinset
    let E':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) true;
    ∃C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      C.edges.card≤e₀ ∧ Disjoint D₀.removed C.edges ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) :=by
  intro H hCorr
  have hn:0<Fintype.card (Fin n):=by simp;obtain ⟨x⟩:=‹Nonempty (Fin n)›; exact Fin.pos x
  have hsep:∀v u,¬(H false v u∧H true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>σ (Sum.inr e)) false t J false false v u
  have hb:6*(8*((((r+4):ℕ):ℝ)+1)*ξ*Fintype.card (Fin n))≤min (gammaLoss*n) (sigmaLoss*n):=by simpa using hbudget
  obtain ⟨D₀,hvalid,C,havoid,hcard,hrows,hhubs,hcorrected,hfixed,D₂,hvalid₂,hremoved,hremaining,hdisjoint⟩:=
    marked_protected_correction_vortex_reserve r d size a₀ b₀ e₀ f₀ εAbs ζ ξ G D m β ε Q π hpres L hL σ H
      hreg hn hD hρhi he heAbs hsize (gammaLoss*n) (sigmaLoss*n) e₀ hξ hb hsep hCorr ∅ (by simp) (by rfl)
  exact ⟨D₀,hvalid,C,hcard,hdisjoint,hfixed⟩
end Oberwolfach
