module

public import Oberwolfach.OrdinaryProtectedEditsVortexWheelCompletion
public import Oberwolfach.OrdinaryTrackedSplitWheelCertificates
public import Oberwolfach.OrdinaryVortexSelectedCostSchedule
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! Apply the vortex wheel chain uniformly to the original protected edits,
using one corrected reservoir and the corresponding tracked remainders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_edits_selected_split_completion {n q r mAbs t aAbs bAbs:ℕ}
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q → SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hr:0<r)
    (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin q)) (ξAbs ξedit:ℝ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n → Fin q → Prop)
    (hsize:Wterm.card+Bterm.card ≤ mAbs) (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (L:ℕ) (hL:0<L) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm)
    (editCost:ℝ):
    let cost:=ordinaryVortexSelectedCost Vor rate
    let deepCost:=ordinaryFineDeepCost Vor ξroot
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let Changed:=fun S:SimpleGraph (Fin n)=>∀v,
      ((Finset.univ.filter (fun w=>Xor (S.Adj v w) (Sample.Adj v w))).card:ℝ) ≤ ξedit*n;
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξAbs Reference Bad Href
      A Z Wterm Bterm B Kabs JQ JH → 
    (∀S:SimpleGraph (Fin n),S ≤ P → S.IsRegularOfDegree (2*q) → ordinaryResourceRim Reference Kabs ≤ S → 
      (∀v∈Inner,∀w∈Inner,S.Adj v w↔Sample.Adj v w) → Changed S → 
      ∀f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f → 
      OrdinaryTrackedSplitWheelCertificatesAt P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f) → 
    ∀S:SimpleGraph (Fin n),S ≤ P → S.IsRegularOfDegree (2*q) → ordinaryResourceRim Reference Kabs ≤ S → 
      (∀v∈Inner,∀w∈Inner,S.Adj v w↔Sample.Adj v w) → Changed S → 
      ∀f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f → 
      HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u)) r ∧
      HasFactorDecomposition S Fs :=by
  intro cost deepCost Sample Bad Reference Href Changed hw hsplit
  obtain ⟨hc,hd,_,_⟩:=ordinary_vortex_selected_cost_schedule Vor rate ξroot 0 hrate hξroot (by norm_num)
  apply ordinary_protected_edits_vortex_wheel_completion P π d σ Fs hFs C hr hsizeC Inner Hubs A Z Wterm Bterm B ξAbs ξedit
    Kabs JQ JH hsize hWsub hBsub D mv β ε Vor L hL cost deepCost hc hd hWterm hBterm editCost hw
  intro S hSP hreg hReserve hAgreement hEdit f hf
  exact ordinary_tracked_split_wheel_certificates P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f
    (hsplit S hSP hreg hReserve hAgreement hEdit f hf)
end Oberwolfach
