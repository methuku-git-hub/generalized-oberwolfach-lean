module

public import Oberwolfach.OrdinaryUniformColumnEmbedding
public import Oberwolfach.OrdinaryTrackedComplementFromPostmatchingStateZero
public import Oberwolfach.OrdinaryLostEdgesEditDegree

@[expose] public section
/-! The matching embedding and corrected reservoir are fixed on the same
sample.  Original protected edits give tracked wheel remainders uniformly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 35000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_tracked_complement_from_columns {n q K:ℕ}
    (Fs:Fin q → SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (i₀:Fin K) (r m d:ℕ)
    (rsv θ lamMatch a γ δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hn:0<n) (hδ:0 ≤ δ)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hzero:OrdinaryZeroRetentionEvent π d false σ)
    (p k p₂ k₂ u t κ edit e tcol:ℝ)
    (hk:0 ≤ k) (hk₂:0 ≤ k₂) (hu:0 ≤ u) (ht:0 ≤ t) (hκ:0 ≤ κ) (hedit:0 ≤ edit)
    (hκrow:(max a γ)*n ≤ κ):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)
    let Changed:=fun S:SimpleGraph (Fin n)=>∀v,
      ((Finset.univ.filter (fun w=>Xor (S.Adj v w) (Sample.Adj v w))).card:ℝ) ≤ edit;
    Kabs⊆ordinaryHostResources Reference Href → 
    (∀c x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) c x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u c*P.degree x|<t) → 
    (∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))| ≤ e) → 
    (∀w,|((Finset.univ.filter (fun v=>Href v w)).card:ℝ)-rsv*n| ≤ tcol) → 
    (∀S,Changed S → 
      OrdinarySelectedPostmatchingEmbeddingTrackedResult Fs hFs C i₀ rsv θ lamMatch a γ m d π P (Sample\S) S Protect Sample Reference Bad σ 0 J
        Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δ) → 
    ∀S:SimpleGraph (Fin n), S.IsRegularOfDegree (2*q) → ordinaryResourceRim Reference Kabs ≤ S → 
      (∀v∈Inner,∀w∈Inner,S.Adj v w↔Sample.Adj v w) → Changed S → 
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=κ+(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+edit+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+tcol);
    ∃f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs
        (Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card) f ∧
      (S\ordinaryEmbeddedComplements Fs C f) ≤ Sample ∧
      (S\ordinaryEmbeddedComplements Fs C f) ≤ P :=by
  intro Sample Bad Reference Href Protect J Changed hA hcolour hbalance hcolumns hmatching S hS hReserve hAgreement hEdit
  let Del:=Sample\S
  have hDel:∀v,(Del.degree v:ℝ) ≤ edit:=by
    have hh:=lost_graph_degree_le_symmetric_edit S Sample edit hEdit
    intro v
    exact hh v
  have hh:=ordinary_tracked_complement_from_postmatching_state_zero Fs hFs C i₀ r m d
    rsv θ lamMatch a γ δ P S π σ Inner Hubs Kabs
  unfold OrdinaryTrackedComplementFromPostmatchingStateZeroShape at hh
  exact hh hn hδ hS hsize hCard hzero hA hReserve hAgreement (hmatching S hEdit)
    p k p₂ k₂ u t edit κ edit e tcol hk hk₂ hu ht hedit hκ hedit hκrow hDel hEdit hcolour hbalance hcolumns
end Oberwolfach
