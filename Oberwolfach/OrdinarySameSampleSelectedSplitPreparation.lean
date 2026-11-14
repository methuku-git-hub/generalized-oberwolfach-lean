module

public import Oberwolfach.OrdinaryUniformColumnsNaturalPreparation
public import Oberwolfach.OrdinaryProtectedEditsSelectedSplitCompletion

@[expose] public section
/-! The same sample, matching, corrected reservoir and selected-cost wheel
chain give the natural preparation certificate for every protected edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 45000000
set_option maxRecDepth 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_selected_split_preparation {n q K:ℕ}
    (Fs:Fin q → SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (i₀:Fin K) (r m d:ℕ)
    (rsv θ lamMatch a γ δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (aAbs bAbs:ℕ) (ξ:ℝ)
    (hn:0<n) (hδ:0 ≤ δ) (hξ:0 ≤ ξ)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hCard:∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)
    (hzero:OrdinaryZeroRetentionEvent π d false σ)
    (hrow:(ordinaryResourceRows Kabs).card ≤ aAbs)
    (hhub:(ordinaryResourceHubs Kabs).card ≤ bAbs)
    (p k p₂ k₂ u t κ e tcol:ℝ)
    (hk:0 ≤ k) (hk₂:0 ≤ k₂) (hu:0 ≤ u) (ht:0 ≤ t) (hκ:0 ≤ κ)
    (hκrow:(max a γ)*n ≤ κ)
    (mAbs tAbs:ℕ) (A Z Wterm:Finset (Fin n)) (Bterm Bprotect:Finset (Fin q)) (ξAbs:ℝ)
    (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (hr:0<r) (hAbsSize:Wterm.card+Bterm.card≤mAbs) (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs)
    (D mv:ℕ) (βv εv:ℝ) (Vor:Vortex (Fin q) P D βv εv mv)
    (L:ℕ) (hL:0<L) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)
    let Changed:=fun S:SimpleGraph (Fin n)=>∀v,
      ((Finset.univ.filter (fun w=>Xor (S.Adj v w) (Sample.Adj v w))).card:ℝ) ≤ ξ*n
    let edit:=ξ*n
    let LF:ℝ:=2*((3*d:ℕ):ℝ)
    let newLoss:ℝ:=5*Real.sqrt δ*n
    let κref:ℝ:=κ+(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+edit+LF
    let Lrim:ℝ:=edit+κref+newLoss
    let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+tcol)
    let editCost:ℝ:=Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card;
    Kabs⊆ordinaryHostResources Reference Href → 
    (∀c x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) c x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u c*P.degree x|<t) → 
    (∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))| ≤ e) → 
    (∀w,|((Finset.univ.filter (fun v=>Href v w)).card:ℝ)-rsv*n| ≤ tcol) → 
    (∀S,Changed S → 
      OrdinarySelectedPostmatchingEmbeddingTrackedResult Fs hFs C i₀ rsv θ lamMatch a γ m d π P (Sample\S) S Protect Sample Reference Bad σ 0 J
        Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δ) → 
    OrdinaryCorrectedProtectedReservoirWitness r mAbs tAbs aAbs bAbs ξAbs Reference Bad Href
      A Z Wterm Bterm Bprotect Kabs JQ JH →
    (∀(S:SimpleGraph (Fin n)),S≤P→S.IsRegularOfDegree (2*q)→
      ordinaryResourceRim Reference Kabs≤S→
      (∀v∈Inner,∀w∈Inner,S.Adj v w↔Sample.Adj v w)→Changed S→
      ∀(f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n),
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f→
      OrdinaryTrackedSplitWheelCertificatesAt P S Bad Fs C r Kabs D mv βv εv Vor L
        (ordinaryVortexSelectedCost Vor rate) (ordinaryFineDeepCost Vor ξroot) f)→
    OrdinaryNaturalPreparationCertificate (r:=r) P Sample Inner ξ (aAbs*aAbs+aAbs*bAbs) Fs C :=by
  intro Sample Bad Reference Href Protect J Changed edit LF newLoss κref Lrim Lspoke editCost
    hA hcolour hbalance hcolumns hmatching hw hsplit
  apply ordinary_uniform_columns_natural_preparation Fs hFs C i₀ r m d rsv θ lamMatch a γ δ P π σ Inner Hubs Kabs aAbs bAbs ξ
    hn hδ hξ hsize hCard hzero hrow hhub p k p₂ k₂ u t κ e tcol hk hk₂ hu ht hκ hκrow
    hA hcolour hbalance hcolumns hmatching
  intro S hSP hreg hReserve hAgreement hEdit f hf
  have hcomplete:=ordinary_protected_edits_selected_split_completion P π d σ Fs hFs C hr hsize Inner Hubs A Z Wterm Bterm Bprotect ξAbs ξ
    Kabs JQ JH hAbsSize hWsub hBsub D mv βv εv Vor L hL rate ξroot hrate hξroot hWterm hBterm editCost
    hw hsplit S hSP hreg hReserve hAgreement hEdit f hf
  exact hcomplete.1
end Oberwolfach
