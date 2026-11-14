module

public import Oberwolfach.OrdinaryTrackedReferenceLocalWheel
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! Uniform wheel completion from the actual per-level local certificates,
for the same protected reservoir and the same tracked complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedWheelLocalCertificates {n q:ℕ}
    (P S Bad:SimpleGraph (Fin n)) (Fs:Fin q → SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent) (r:ℕ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (L:ℕ) (cost deepCost:ℕ → ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):Prop :=
  let Q:=S\ordinaryEmbeddedComplements Fs C f
  let H:=fun v u=>v∉Set.range (f u)
  let X:=fun k=>Vor.extendedVertices (k+1);let T:=fun k=>Vor.extendedVertices (k+2)
  let Zs:=fun k=>Vor.extendedIndices (k+1);let Ws:=fun k=>Vor.extendedIndices (k+2)
  let Gstart:=Q\ordinaryResourceRim Q Kabs
  let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kabs);
  ∀i,i<L → ∀R (G:SimpleGraph (Fin n)) (Hs:Fin n → Fin q → Prop),
    OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r i L R
      (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
      (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0) → 
    ordinaryHostResources G Hs=R → G ≤ Q → (∀v u,Hs v u → H v u) → 
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) → 
    (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) → 
    let fv:=markedVortexVertexEmbedding Vor i;let gu:=markedVortexHubEmbedding Vor i;
    OrdinaryWheelLikelySeparateCostsCertificate (G.comap fv) (Bad.comap fv) (fun v u=>Hs (fv v) (gu u))
      (markedVortexInnerVertices Vor i) (ordinaryVortexBufferedVertices Vor i 2)
      (markedVortexInnerHubs Vor i) (ordinaryVortexBufferedHubs Vor i 2) r (cost i) (deepCost i)

theorem ordinary_uniform_tracked_vortex_certificates {n q r mAbs t aAbs bAbs:ℕ}
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q → SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hr:0<r)
    (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin q)) (ξ:ℝ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n → Fin q → Prop)
    (hsize:Wterm.card+Bterm.card ≤ mAbs) (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (L:ℕ) (hL:0<L) (cost deepCost:ℕ → ℝ)
    (hc:∀i,0 ≤ cost i) (hd:∀i,0 ≤ deepCost i)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm)
    (editCost:ℝ) (Admissible:SimpleGraph (Fin n) → Prop):
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B Kabs JQ JH → 
    (∀S,Admissible S → S.IsRegularOfDegree (2*q) → 
      ∀f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f → 
      OrdinaryTrackedWheelLocalCertificates P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f) → 
    ∀S,Admissible S → S.IsRegularOfDegree (2*q) → 
      ∀f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n,
      OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f → 
      HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u)) r ∧
      HasFactorDecomposition S Fs :=by
  intro Bad Reference Href hw hcert S hAdmissible hS f hf
  have hdata:=ordinary_tracked_wheel_reference_data P S π d σ Fs hFs C hsizeC hS
    Inner Hubs A Z Wterm Bterm B ξ Kabs JQ JH hWsub hBsub editCost f hw hf
  have hlocal:=hcert S hAdmissible hS f hf
  have hwheel:=ordinary_tracked_reference_local_wheel P S π d σ Fs C Wterm Bterm hsize Kabs
    D mv β ε Vor L hL cost deepCost hc hd hWterm hBterm f hdata hlocal
  have hfcopy:=hf
  unfold OrdinaryTrackedComplementFor at hfcopy
  obtain ⟨hC,hCC,_,_,_,_,_⟩:=hfcopy
  have hfactor:=ordinary_complement_remainder_decomposition S hS hr Fs hFs C hsizeC f hC hCC hwheel
  exact ⟨hwheel,hfactor⟩
end Oberwolfach
