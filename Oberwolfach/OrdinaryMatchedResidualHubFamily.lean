module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage

@[expose] public section
/-! Choose the per-hub matching data once and retain the physical old-edge
packing disjointness and containment in the same target host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_residual_hub_family
    {U V:Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {X A B J W:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,Fintype (B u)] [∀u,DecidableEq (B u)]
    [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (G:∀u,SimpleGraph (X u)) (m d:ℕ) (π:Equiv.Perm V) (root:∀u,A u⊕B u→V)
    (Arc:V→V→Prop) (Avail Reserve:U→Finset V) (Good:∀u,W u→Prop)
    (Pack:∀u,W u→Finset (Finset V)) (Pos:∀u,W u→B u→Finset ℕ) (len:∀u,J u→ℕ)
    (source:∀u,Nonempty (OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u)))
    (hpack:∀w:∀u,W u,(∀u,Good u (w u))→∀u v,u≠v→Disjoint (Pack u (w u)) (Pack v (w v)))
    (Host:SimpleGraph V) (hArc:∀x y,Arc x y→Host.Adj x y):
    ∃p:∀u,OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u) (Good u) (Pack u) (Pos u) (len u),
    (∀u v,u≠v→Disjoint (Pack u (p u).marker) (Pack v (p v).marker)) ∧
    let Old:=fun u=>((p u).data.deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(p u).data.s₁}=>((p u).data.path (.inl i)).edges.toFinset))).image (Sym2.map (p u).ψ);
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 V),(∀u,Old u⊆All) ∧ All⊆Host.edgeFinset :=by
  let p:=fun u=>Classical.choice (source u)
  refine ⟨p,?_⟩
  have hdis:∀u v,u≠v→Disjoint (Pack u (p u).marker) (Pack v (p v).marker):=by
    exact hpack (fun u=>(p u).marker) (fun u=>(p u).hGood)
  refine ⟨hdis,?_⟩
  exact actual_old_family_host_packing G (fun u=>(p u).data) (fun u=>(p u).ψ)
    (fun u=>Pack u (p u).marker) (fun u=>(p u).hCoverage) hdis Host Arc hArc (fun u=>(p u).hDirected)
end Oberwolfach
