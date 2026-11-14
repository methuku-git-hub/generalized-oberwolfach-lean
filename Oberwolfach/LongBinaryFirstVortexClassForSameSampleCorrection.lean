module

public import Oberwolfach.LongSelectedFirstVortexClassForSameSampleCorrection
public import Oberwolfach.LongBinaryFirstVortexClassEvent

@[expose] public section
/-! Choose the regular class protected by the actual inner pair and
resource graph, then keep its matching and retained packing on one deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_binary_first_vortex_class_for_same_sample_correction
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (αHost:ℝ) (hε:0≤ε) (hsmall:ε≤αHost/100000) (γLoss σLoss ξClass:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (Bpart:ℕ)
    (hEvery:LongEveryClassValidDeletionEvent Δ P π d r γLoss σLoss ξClass z (Vort.extendedVertices 1) (Vort.extendedIndices 1) K Bpart θ Dv a γ eps βList F hF weight w):
    let Zpart:=spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1)
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false;
    ∀D₀:MarkedReferenceDeletion P π d σ,
      D₀.Valid H (r+4) (Vort.extendedVertices 1) (Vort.extendedIndices 1) (γLoss*n) (σLoss*n)→
    let Ddeleted:=(markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let σ':=rawMarkedDeleteRims σ Ddeleted
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤Bpart→Disjoint D₀.removed C.edges→
    ∀ (hPart:∀T:SimpleGraph (Fin n),(∀v,T.degree v≤Bpart)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*binaryClassMultiplicity Dv (Fintype.card U) 0) ∧
        (∀x y,(Zpart⊔T).Adj x y→(S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n))
    (hPrepared:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C.edges≤S→
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2),
    ∃(S:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ) (Del:SimpleGraph (Fin n)),
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C.edges S M Del ∧
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,(longSelectedPhysicalGraph P π d z.1).Adj x y→S.Adj x y) ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithGlobalLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) := by
  intro Zpart σ H D₀ hvalid Ddeleted σ' E' K' C hcard hdis hPart hPrepared
  have hPart':=long_binary_first_vortex_class_event P β ε Vort π d Bpart ξClass z hPart
  exact long_selected_first_vortex_class_for_same_sample_correction P π d r Dv mm β ε Vort αHost hε hsmall γLoss σLoss ξClass z
    θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList F hF weight w Bpart hEvery D₀ hvalid C hcard hdis hPart' hPrepared
end Oberwolfach
