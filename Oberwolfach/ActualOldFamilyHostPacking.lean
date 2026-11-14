module

public import Oberwolfach.ActualOldCoverageResidualFamily
public import Oberwolfach.ActualOldDirectedPhysicalHost

@[expose] public section
/-! Assemble the old edges needed for residual complement embedding into a
single host-contained physical pack, retaining disjointness across factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_family_host_packing
    {U V:Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {X K J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,DecidableEq (K u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (data:∀u,ActualResidualData (K:=K u) (J:=J u) (F u))
    (ψ:∀u,X u→V) (Pack:U→Finset (Finset V))
    (hcover:∀u,ActualOldPhysicalCoverage (data u) (ψ u) (Pack u))
    (hdis:∀u v,u≠v→Disjoint (Pack u) (Pack v))
    (H:SimpleGraph V) (Arc:V→V→Prop) (hArc:∀x y,Arc x y→H.Adj x y)
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u) Arc):
    let Old:=fun u=>((data u).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data u).s₁}=>((data u).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ u));
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 V),(∀u,Old u⊆All) ∧ All⊆H.edgeFinset :=by
  intro Old
  have hpair:∀u v,u≠v→Disjoint (Old u) (Old v):=
    (actual_old_coverage_residual_family F data ψ Pack hcover hdis).1
  have hhost:∀u,Old u⊆H.edgeFinset:=fun u=>
    actual_old_directed_physical_host (data u) (ψ u) H Arc hArc (hdir u)
  refine ⟨hpair,Finset.univ.biUnion Old,?_,?_⟩
  · intro u e he
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,he⟩
  · intro e he
    obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp he
    exact hhost u hu
end Oberwolfach
