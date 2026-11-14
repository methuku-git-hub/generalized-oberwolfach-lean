module

public import Oberwolfach.OrdinaryTrackedComplementVortexChainForShape

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

def OrdinaryTrackedWheelCertificateInputs {n q:ℕ}
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

end Oberwolfach
