module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryVortexReferenceAbsorberChain
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness

@[expose] public section
/-! A fixed corrected absorber and the actual tracked complement feed the
two-host vortex chain. The local wheel certificates remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedComplementVortexChainForShape {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hr:0<r)
    (hsizeC:∀u (c:↥(C u)),Fintype.card c.val=r) (hS:S.IsRegularOfDegree (2*q))
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin q)) (ξ:ℝ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (hsize:Wterm.card+Bterm.card≤mAbs) (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (L:ℕ) (hL:0<L) (cost deepCost:ℕ→ℝ)
    (hc:∀i,0≤cost i) (hd:∀i,0≤deepCost i)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm)
    (editCost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):Prop :=
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B Kabs JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs Kabs editCost f→
    (let Q:=S\ordinaryEmbeddedComplements Fs C f
      let H:=fun v u=>v∉Set.range (f u)
      let X:=fun k=>Vor.extendedVertices (k+1);let T:=fun k=>Vor.extendedVertices (k+2)
      let Zs:=fun k=>Vor.extendedIndices (k+1);let Ws:=fun k=>Vor.extendedIndices (k+2)
      let Gstart:=Q\ordinaryResourceRim Q Kabs
      let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kabs);
      ∀i,i<L→∀R (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
        OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r i L R
          (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
          (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
        ordinaryHostResources G Hs=R→G≤Q→(∀v u,Hs v u→H v u)→
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
        let fv:=markedVortexVertexEmbedding Vor i;let gu:=markedVortexHubEmbedding Vor i;
        OrdinaryWheelLikelySeparateCostsCertificate (G.comap fv) (Bad.comap fv) (fun v u=>Hs (fv v) (gu u))
          (markedVortexInnerVertices Vor i) (ordinaryVortexBufferedVertices Vor i 2)
          (markedVortexInnerHubs Vor i) (ordinaryVortexBufferedHubs Vor i 2) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u)) r ∧
      HasFactorDecomposition S Fs
end Oberwolfach
