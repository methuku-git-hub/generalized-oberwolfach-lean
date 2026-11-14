module

public import Oberwolfach.PrescribedPhysicalUnionImageLoad
public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Apply the degree-two image bound to the actual residual source graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_physical_union_degree_from_image_load
    {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (F:I→SimpleGraph V) (hF:∀i,(F i).IsRegularOfDegree 2)
    (K J:I→Type) [∀i,DecidableEq (K i)] [∀i,DecidableEq (J i)]
    (a:∀i,ActualResidualData (K:=K i) (J:=J i) (F i))
    (Q:∀i,SimpleGraph {x // x∈(a i).remaining})
    (hQ:∀i,Q i=((a i).graph).induce (↑(a i).remaining:Set V))
    (Φ:∀i,{x // x∈(a i).remaining}→V) (hinj:∀i,Function.Injective (Φ i))
    (v:V) (L:ℝ)
    (hload:((Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card:ℝ)≤L):
    let E:I→Finset (Sym2 V):=fun i=>(Q i).edgeFinset.image (Sym2.map (Φ i));
    ((prescribedPhysicalUnion E).degree v:ℝ)≤2*L :=by
  have hdegree:∀i x,(Q i).degree x≤2:=by
    intro i x
    let e:{x // x∈(a i).remaining}↪V:=⟨Subtype.val,Subtype.val_injective⟩
    have hmap:((Q i).map e)≤F i:=by
      intro u v huv
      obtain ⟨x,y,hxy,rfl,rfl⟩:=(SimpleGraph.map_adj e (Q i) u v).mp huv
      have hxy':((a i).graph).Adj x.1 y.1:=by
        have hh:=hxy
        rw [hQ i] at hh
        exact hh
      exact ((a i).graph_facts (hF i)).1 hxy'
    have hle:((Q i).map e).degree (e x)≤(F i).degree (e x):=SimpleGraph.degree_le_of_le hmap
    have heq:((Q i).map e).degree (e x)=(Q i).degree x:=SimpleGraph.degree_map_apply (Q i) e x
    have hreg:(F i).degree (e x)=2:=hF i (e x)
    omega
  exact prescribed_physical_union_degree_from_image_load (fun i=>{x // x∈(a i).remaining}) Q Φ hinj hdegree v L hload
end Oberwolfach
