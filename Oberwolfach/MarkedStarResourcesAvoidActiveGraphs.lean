module

public import Oberwolfach.MarkedInnerStarAvoidsActive
public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Physical graphs of star resources avoid the active inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_star_resources_avoid_active_graphs
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (I T:Finset V) (J W:Finset U)
    (hstar:∀ e∈markedFiniteResources tail head ktail khead π A S,markedStarResource T W e):
    let ER:=physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let ES:=markedFiniteSpokeGraph S
    (∀ x∈I\T,∀ y∈I\T,¬ER.Adj x y) ∧
    (∀ x∈I\T,∀ u∈J\W,¬ES.Adj (Sum.inl x) (Sum.inr u)) :=by
  intro ER ES
  have hno (e:Finset V⊕(V×U))
      (he:e∈markedFiniteResources tail head ktail khead π A S)
      (hi:markedInnerResource (I\T) (J\W) e):False:=
    (marked_active_inner_avoids_star I T J W e hi) (hstar e he)
  constructor
  · intro x hx y hy hadj
    have hp:{x,y}∈A.image (markedPhysicalEdge tail head ktail khead π):=by
      have hh:=hadj
      simp only [ER,physicalEdgeGraph] at hh
      exact hh.2
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hp
    have hres:Sum.inl ({x,y}:Finset V)∈markedFiniteResources tail head ktail khead π A S:=by
      unfold markedFiniteResources
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,by rw [he]⟩)
    have hi:markedInnerResource (I\T) (J\W) (Sum.inl ({x,y}:Finset V)):=by
      change ({x,y}:Finset V)⊆I\T
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> assumption
    exact hno _ hres hi
  · intro x hx u hu hadj
    have hs:(x,u)∈S:=(markedFiniteSpokeGraph_adj S x u).mp hadj
    have hres:Sum.inr (x,u)∈markedFiniteResources tail head ktail khead π A S:=by
      unfold markedFiniteResources
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x,u),hs,rfl⟩)
    exact hno _ hres ⟨hx,hu⟩
end Oberwolfach
