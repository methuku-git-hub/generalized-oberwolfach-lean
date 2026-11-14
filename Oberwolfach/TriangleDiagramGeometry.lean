module

public import Oberwolfach.TriangleDenseGeometry

@[expose] public section
/-! Minimum degree and near-completeness imply the geometric input of the
finite ordinary diagram for triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_diagram_dense_geometry {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q:SimpleGraph V) (H:V→U→Prop) (β ε:ℝ) (hβ:0<β) (hε:0≤ε) (hεβ:ε≤β) (hε18:ε≤1/18)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ)):
    (∀ v w,β*(Fintype.card V:ℝ)≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    (∀ u u' v w,β*(Fintype.card V:ℝ)≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    (∀ T:Finset V,T.card≤3→(1/2:ℝ)*Fintype.card U≤
      ((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ)) :=by
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  constructor
  · intro v w
    have hh:=triangle_four_graph_neighbours Q β hdeg v w v w
    have he:(Finset.univ.filter (fun x=>Q.Adj v x∧Q.Adj w x∧Q.Adj v x∧Q.Adj w x))=
        Q.neighborFinset v∩Q.neighborFinset w:=by ext x;simp [SimpleGraph.mem_neighborFinset];tauto
    rw [he] at hh
    nlinarith [mul_nonneg hβ.le hn]
  constructor
  · intro u u' v w
    have hh:=triangle_four_neighbours_two_hubs Q H β ε hεβ hdeg hnearV u u' v w v w
    have he:(Finset.univ.filter (fun x=>H x u∧H x u'∧Q.Adj v x∧Q.Adj w x∧Q.Adj v x∧Q.Adj w x))=
        (Finset.univ.filter (fun x=>H x u∧H x u'))∩Q.neighborFinset v∩Q.neighborFinset w:=by
      ext x;simp [SimpleGraph.mem_neighborFinset, and_assoc];tauto
    rw [he] at hh
    nlinarith [mul_nonneg hβ.le hn]
  · intro T hT
    have hh:=triangle_common_hub_neighbours H ε hε hnearU T (by omega)
    have hu:0≤(Fintype.card U:ℝ):=by positivity
    nlinarith
end Oberwolfach
