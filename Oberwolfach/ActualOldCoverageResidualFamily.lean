module

public import Oberwolfach.ActualOldCoverageSymmetricDirect

@[expose] public section
/-! Disjoint covered wheel packs yield the disjoint symmetric old-edge
family and the common old-edge pack needed by residual complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_coverage_residual_family
    {U V:Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {X K J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (ψ:∀u,X u→V) (Pack:U→Finset (Finset V))
    (hcover:∀u,ActualOldPhysicalCoverage (data u) (ψ u) (Pack u))
    (hdis:∀u v,u≠v→Disjoint (Pack u) (Pack v)):
    let Old:=fun u=>((data u).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data u).s₁}=>((data u).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ u));
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 V),(∀u,Old u⊆All) ∧
      (∀e∈All,e.toFinset∈Finset.univ.biUnion Pack):=by
  intro Old
  have hOld:∀u e,e∈Old u→e.toFinset∈Pack u:=fun u=>
    actual_old_coverage_symmetric_direct (data u) (ψ u) (Pack u) (hcover u)
  constructor
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro e heu hev
    exact Finset.disjoint_left.mp (hdis u v huv) (hOld u e heu) (hOld v e hev)
  · refine ⟨Finset.univ.biUnion Old,?_,?_⟩
    · intro u e he
      exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,he⟩
    · intro e he
      obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,hOld u e hu⟩
end Oberwolfach
