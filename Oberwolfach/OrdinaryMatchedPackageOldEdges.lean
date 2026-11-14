module

public import Oberwolfach.OrdinaryMatchedResidualHubPackage
public import Oberwolfach.ActualFinalEdgesEmpty

@[expose] public section
/-! A coherent physical matching package with no first-index paths has
pairwise disjoint old edges, all inside its displayed host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_package_old_edges
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    {X A B J W:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,Fintype (B u)] [∀u,DecidableEq (B u)]
    [∀u,Fintype (J u)] [∀u,DecidableEq (J u)]
    (F:∀u,SimpleGraph (X u)) (m d:ℕ) (π:Equiv.Perm V) (root:∀u,A u⊕B u→V)
    (Arc:V→V→Prop) (Avail Reserve:U→Finset V) (Good:∀u,W u→Prop)
    (Pack:∀u,W u→Finset (Finset V)) (Pos:∀u,W u→B u→Finset ℕ) (len:∀u,J u→ℕ)
    (p:∀u,OrdinaryMatchedResidualHubPackage (F u) m d π (root u) Arc (Avail u) (Reserve u)
      (Good u) (Pack u) (Pos u) (len u))
    (hempty:∀u,IsEmpty (A u))
    (hpack:∀u v,u≠v→Disjoint (Pack u (p u).marker) (Pack v (p v).marker))
    (Host:SimpleGraph V) (hArc:∀x y,Arc x y→Host.Adj x y):
    let Old:=fun u=>(p u).data.deletedEdges.image (Sym2.map (p u).ψ);
    (∀u v,u≠v→Disjoint (Old u) (Old v)) ∧
    ∃All:Finset (Sym2 V),(∀u,Old u⊆All) ∧ All⊆Host.edgeFinset :=by
  intro Old
  have hfinal:∀u,(Finset.univ.biUnion (fun i:{i // i∈(p u).data.s₁}=>((p u).data.path (.inl i)).edges.toFinset))=∅:=
    fun u=>actual_final_edges_empty_of_empty_first_index (p u).data (hempty u) (p u).hs₁
  have hh:=actual_old_family_host_packing F (fun u=>(p u).data) (fun u=>(p u).ψ)
    (fun u=>Pack u (p u).marker) (fun u=>(p u).hCoverage) hpack Host Arc hArc (fun u=>(p u).hDirected)
  simpa only [hfinal,Finset.sdiff_empty] using hh
end Oberwolfach
