module

public import Oberwolfach.MarkedCorrectionSelectReserve
public import Oberwolfach.MarkedCorrectionAbsorberOriginal
public import Oberwolfach.MarkedVortexPreselectReservedProperty

@[expose] public section
/-! Select the terminal reserve in the corrected sample using the actual
vortex pair, retaining both the corrected and original fixed absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_corrected_vortex_terminal_reserve
    (r d size a₀ b₀ e₀ f₀:ℕ) (εAbs:ℝ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (hL:L+1=Q.length) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (heAbs:ε≤εAbs) (hsize:2*m≤size)
    (gammaLoss sigmaLoss extra:ℝ) (D₀:MarkedReferenceDeletion G π d σ)
    (h₀:D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) gammaLoss sigmaLoss)
    (hsep:∀v u,¬(H false v u∧H true v u)):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph G π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc G π (3*d) (fun x=>σ' (Sum.inl x)) true;
    MarkedReservedTerminalAbsorberProperty (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs→
    ∀ F₀:Finset (Finset V⊕(V×U)),F₀.card≤f₀→(e₀:ℝ)≤extra→
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ' H' C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
      MarkedFixedTerminalAbsorber G π d (r+4) σ H C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
    ∃ D₂:MarkedReferenceDeletion G π d σ,
      D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss+extra) (sigmaLoss+extra) ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges :=by
  intro σ' H' E' K' hprop F₀ hF heCorr
  have hcap:=marked_vortex_reserved_capacity_fields Q hreg hn hD hρhi he εAbs heAbs L hL
    (Function.Embedding.refl (markedVortexVertexType Q L)) (Function.Embedding.refl (markedVortexHubType Q L))
  obtain ⟨hI0,_,hJ0,_⟩:=marked_vortex_inner_cardinalities Q 0
  obtain ⟨hIL,_,hJL,_⟩:=marked_vortex_inner_cardinalities Q L
  have hcard0:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V := by
    change Fintype.card ↥(Q.extendedVertices 0)=Fintype.card V
    rw [Fintype.card_coe,Q.extendedVertices_eq (Nat.zero_le _),Q.initial,Finset.card_univ]
  have hfirstV:((Q.extendedVertices 1).card:ℝ)≤εAbs*Fintype.card V+f₀ := by
    have hh:=hcap.1
    rw [hI0,hcard0] at hh
    have hf:(0:ℝ)≤f₀:=Nat.cast_nonneg _
    linarith
  have hfirstU:((Q.extendedIndices 1).card:ℝ)≤εAbs*Fintype.card V+f₀ := by
    have hh:=hcap.2.1
    rw [hJ0,hcard0] at hh
    have hf:(0:ℝ)≤f₀:=Nat.cast_nonneg _
    linarith
  have hterm:(Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤size := by
    have hh:=hcap.2.2
    simp only [Function.Embedding.coe_refl,Finset.image_id] at hh
    rw [hIL,hJL] at hh
    exact hh.trans hsize
  obtain ⟨C,hF₀,hCe,hCr,hCu,hfixed,D₂,h₂,hremoved,hremain,hdis⟩:=
    marked_correction_select_reserve G π d r size a₀ b₀ e₀ f₀ εAbs σ H
      (Q.extendedVertices 1) (Q.extendedIndices 1) gammaLoss sigmaLoss extra D₀ h₀ hsep hprop
      (Q.extendedVertices (L+1)) (Q.extendedVertices 1)
      (Q.extendedIndices (L+1)) (Q.extendedIndices 1) hterm
      (Q.extendedVertices_subset (by omega)) (Q.extendedIndices_subset (by omega))
      Finset.Subset.rfl Finset.Subset.rfl (hpres 1) hfirstV hfirstU F₀ hF heCorr
  have horiginal:=marked_correction_absorber_fixed_original G π d (r+4) σ H D₀ C.edges
    (Q.extendedVertices 1) (Q.extendedVertices (L+1)) (Q.extendedIndices 1) (Q.extendedIndices (L+1))
    (hpres 1) (Q.extendedVertices_subset (by omega)) (Q.extendedIndices_subset (by omega)) h₀.2.1 hfixed
  exact ⟨C,hF₀,hCe,hCr,hCu,hfixed,horiginal,D₂,h₂,hremoved,hremain,hdis⟩
end Oberwolfach
