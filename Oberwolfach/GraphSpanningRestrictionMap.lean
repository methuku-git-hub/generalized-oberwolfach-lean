module

public import Oberwolfach.OrdinaryPhysicalPairMap

@[expose] public section
/-! Restricting a graph and then embedding it agrees with embedding and
restricting to the embedded set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem graph_spanning_restriction_map (G:SimpleGraph A) (S:Finset A) (e:A↪B):
    (spanningRestriction G S).map e=spanningRestriction (G.map e) (S.image e):=by
  have hm (x:A):e x∈S.image e↔x∈S:=by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,h⟩
      exact e.injective h ▸ hy
    · intro h
      exact ⟨x,h,rfl⟩
  ext x y
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj e (spanningRestriction G S) x y).mp h
    have ha:=(spanningRestriction_adj G S a b).mp hab
    apply (spanningRestriction_adj (G.map e) (S.image e) (e a) (e b)).mpr
    exact ⟨SimpleGraph.map_adj_apply.mpr ha.1,(hm a).mpr ha.2.1,(hm b).mpr ha.2.2⟩
  · intro h
    have hh:=(spanningRestriction_adj (G.map e) (S.image e) x y).mp h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj e G x y).mp hh.1
    apply SimpleGraph.map_adj_apply.mpr
    exact (spanningRestriction_adj G S a b).mpr ⟨hab,(hm a).mp hh.2.1,(hm b).mp hh.2.2⟩
end Oberwolfach
