module

public import Oberwolfach.OrdinaryInducedUnreservedPair

@[expose] public section
/-! The restricted reserve is a deterministic pullback of the same
physical coin outcome; no new random sample is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A:Type} [Fintype V] [Fintype U] [Fintype A] [DecidableEq V] [DecidableEq U] [DecidableEq A]

theorem ordinary_retained_graph_comap (G:SimpleGraph V) (φ:A↪V) (σ:Sym2 V→Bool):
    (retainedGraph G σ).comap φ=retainedGraph (G.comap φ) (fun e=>σ (Sym2.map φ e)):=by
  ext x y
  rfl

theorem ordinary_boundary_graph_comap (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U):
    let I:=Finset.univ\T;let J:=Finset.univ\W;
    let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:J↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset I:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset J:=Finset.univ.filter (fun u=>u.val∈Z);
    (ordinaryBoundaryGraph Q H X Z).comap (φ.sumMap ψ)=
      ordinaryBoundaryGraph (Q.induce (I:Set V)) (fun (v:I) (u:J)=>H v.val u.val) Xf Zf:=by
  intro I J φ ψ Xf Zf
  ext a b
  cases a <;> cases b <;>
    simp [ordinaryBoundaryGraph_adj,ordinaryPhysicalGraph,ordinaryInnerVertices_left,
      ordinaryInnerVertices_right,Xf,Zf,φ,ψ,SimpleGraph.comap_adj] <;> intros <;> rfl

theorem ordinary_induced_reserve_same_sample (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (σ:Sym2 (V⊕U)→Bool):
    let I:=Finset.univ\T;let J:=Finset.univ\W;
    let φ:I↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:J↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset I:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset J:=Finset.univ.filter (fun u=>u.val∈Z);
    (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ).comap (φ.sumMap ψ)=
      retainedGraph (ordinaryBoundaryGraph (Q.induce (I:Set V)) (fun (v:I) (u:J)=>H v.val u.val) Xf Zf)
        (fun e=>σ (Sym2.map (φ.sumMap ψ) e)):=by
  intro I J φ ψ Xf Zf
  rw [ordinary_retained_graph_comap,ordinary_boundary_graph_comap]
  rfl
end Oberwolfach
