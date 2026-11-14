module

public import Oberwolfach.OrdinaryUniformTrackedVortexCertificates

@[expose] public section
/-! The initial tracked wheel host is fixed, while later certificates must
hold for every protected deletion history on the same tracked remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_local_certificates_from_split {n q:ℕ}
    (P S Bad:SimpleGraph (Fin n)) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent) (r:ℕ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (D mv:ℕ) (β ε:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv) (L:ℕ) (cost deepCost:ℕ→ℝ)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n):
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let X:=fun k=>Vor.extendedVertices (k+1);let T:=fun k=>Vor.extendedVertices (k+2)
    let Zs:=fun k=>Vor.extendedIndices (k+1);let Ws:=fun k=>Vor.extendedIndices (k+2)
    let Gstart:=Q\ordinaryResourceRim Q Kabs
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kabs);
    (let fv:=markedVortexVertexEmbedding Vor 0;let gu:=markedVortexHubEmbedding Vor 0;
      OrdinaryWheelLikelySeparateCostsCertificate (Gstart.comap fv) (Bad.comap fv) (fun v u=>Hstart (fv v) (gu u))
        (markedVortexInnerVertices Vor 0) (ordinaryVortexBufferedVertices Vor 0 2)
        (markedVortexInnerHubs Vor 0) (ordinaryVortexBufferedHubs Vor 0 2) r (cost 0) (deepCost 0)) →
    (∀i,i+1<L→∀R (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r (i+1) L R
        (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=R→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let fv:=markedVortexVertexEmbedding Vor (i+1);let gu:=markedVortexHubEmbedding Vor (i+1);
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap fv) (Bad.comap fv) (fun v u=>Hs (fv v) (gu u))
        (markedVortexInnerVertices Vor (i+1)) (ordinaryVortexBufferedVertices Vor (i+1) 2)
        (markedVortexInnerHubs Vor (i+1)) (ordinaryVortexBufferedHubs Vor (i+1) 2) r (cost (i+1)) (deepCost (i+1))) →
    OrdinaryTrackedWheelLocalCertificates P S Bad Fs C r Kabs D mv β ε Vor L cost deepCost f :=by
  intro Q H X T Zs Ws Gstart Hstart hInitial hLater
  intro i hi R G Hs hhist hstate hG hH hbal hdiv
  cases i with
  | zero =>
      have hq:ordinaryHistoryRim Gstart hhist.rim hhist.spokes 0=Gstart:=by
        ext x y
        simp [ordinaryHistoryRim,ordinaryDeletionHistory]
      have hh:ordinaryHistorySpokes Hstart hhist.rim hhist.spokes 0=Hstart:=by
        funext x u
        simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
      have he:=hhist.trace.1
      rw [hq,hh] at he
      obtain ⟨hge,hhe⟩:=ordinaryHostResources_injective G Gstart Hs Hstart (hstate.trans he.symm)
      subst G
      subst Hs
      exact hInitial
  | succ i =>
      have hi':i+1<L:=by omega
      have hh:=hLater i hi' R G Hs hhist hstate hG hH hbal hdiv
      convert hh using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
