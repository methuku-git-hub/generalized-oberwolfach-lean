module

public import Oberwolfach.OrdinaryApproximateOldAvoidsBadEdges

@[expose] public section
/-! On the same outcome, the old factor pieces avoid all edges added to the
realized sample graph, without an extra separation assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryOldAvoidAddedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_old_family_avoids_sample_added_edges
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P Host Del S:SimpleGraph (Fin n)) (hHP:Host≤P) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (F u))
    (hempty:∀u,IsEmpty (A u)) (hs:∀u,(data u).s₁=firstSumIndices) (ψ:∀u,X u→Fin n)
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4};
    ∀u,Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) (S\S₀).edgeFinset:=by
  intro S₀
  let Old:=fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))
  have hOld:∀u,Old u⊆(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
    intro u
    simpa only [Old] using ordinary_old_edges_in_approximate_layer P Host Del hHP π d σ
      (data u) (hempty u) (hs u) (ψ u) (hdir u)
  have hh:=ordinary_approximate_old_avoids_added_edges P S π d σ Old hOld
  have hset:(letI:DecidableEq (Fin 6):=instDecidableEqFin 6; ({0,1,2,3,4}:Finset (Fin 6)))=
      (letI:DecidableEq (Fin 6):=ordinaryOldAvoidAddedFin 6; ({0,1,2,3,4}:Finset (Fin 6))):=by
    ext x
    simp
  dsimp only at hh
  rw [hset] at hh
  simpa only [Old,S₀] using hh
end Oberwolfach
