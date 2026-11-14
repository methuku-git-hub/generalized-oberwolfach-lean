module

public import Oberwolfach.GraphSingleEdge
public import Oberwolfach.EdgeRetention
public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! Forcing the omitted root costs at most one extra deleted rim edge at
each vertex beyond the original edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_forced_root_deletion_subgraph (P Q F:SimpleGraph V) (σ:Sym2 V→Bool) (x y:V):
    ((retainedGraph P (Function.update σ s(x,y) true)\F)\Q)≤
      (((retainedGraph P σ\F)\Q)⊔SimpleGraph.edge x y):=by
  intro a b hab
  by_cases hroot:s(a,b)=s(x,y)
  · right
    have hne:a≠b:=hab.1.1.1.ne
    rcases Sym2.eq_iff.mp hroot with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp [SimpleGraph.edge_adj,hne,Ne.symm hne]
  · left
    have hs:σ s(a,b)=true:=by simpa only [Function.update_of_ne hroot] using hab.1.1.2
    exact ⟨⟨⟨hab.1.1.1,hs⟩,hab.1.2⟩,hab.2⟩

theorem ordinary_forced_root_deletion_degree (P Q F:SimpleGraph V) (σ:Sym2 V→Bool) (x y:V)
    (hxy:x≠y) (d:ℝ) (hbase:∀v,(((retainedGraph P σ\F)\Q).degree v:ℝ)≤d):
    ∀v,(((retainedGraph P (Function.update σ s(x,y) true)\F)\Q).degree v:ℝ)≤d+1:=by
  intro v
  let D:SimpleGraph V:=(retainedGraph P σ\F)\Q
  have hsub:=ordinary_forced_root_deletion_subgraph P Q F σ x y
  have hd:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have hs:=graph_degree_sup_le D (SimpleGraph.edge x y) v
  have he:((SimpleGraph.edge x y).degree v:ℝ)≤1:=by
    rw [single_edge_degree x y hxy v]
    split_ifs <;> norm_num
  have hd':((((retainedGraph P (Function.update σ s(x,y) true)\F)\Q).degree v:ℝ)≤
      ((D⊔SimpleGraph.edge x y).degree v:ℝ)):=by exact_mod_cast hd
  have hs':((D⊔SimpleGraph.edge x y).degree v:ℝ)≤(D.degree v:ℝ)+(SimpleGraph.edge x y).degree v:=by
    have hsc:=(Nat.cast_le (α:=ℝ)).mpr hs
    push_cast at hsc
    convert hsc using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hb:(D.degree v:ℝ)≤d:=by convert hbase v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  linarith only [hd',hs',he,hb]
end Oberwolfach
