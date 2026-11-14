module

public import Oberwolfach.LocalFactorGraphChoice
public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section

/-! Embed a rim factor into the physical vertex space, preserving its
original cycle identifiers, maximum degree, and avoidance of physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem graph_map_degree_bound (G:SimpleGraph V) (e:V↪W) (d:ℕ)
    (hd:∀ v,G.degree v≤d) (w:W):(G.map e).degree w≤d:=by
  by_cases hw:w∈Set.range e
  · obtain ⟨v,rfl⟩:=hw
    have hh:=SimpleGraph.degree_map_apply G e v
    have he:(G.map e).degree (e v)=G.degree v:=by
      simpa only [←SimpleGraph.ncard_neighborSet] using hh
    rw [he];exact hd v
  · have hi:(G.map e).IsIsolated w:=by
      intro z hz
      rw [SimpleGraph.map_adj] at hz
      obtain ⟨x,y,hxy,hx,hy⟩:=hz
      exact hw ⟨x,hx⟩
    rw [hi.degree_eq_zero];exact Nat.zero_le _

theorem graph_map_restriction (G Q:SimpleGraph V) (P:SimpleGraph W) (e:V↪W) (Y:Finset V)
    (hG:G≤spanningRestriction Q Y) (hQ:Q.map e≤P):
    G.map e≤spanningRestriction P (Y.image e):=by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨v,w,hvw,rfl,rfl⟩:=hxy
  obtain ⟨hq,hv,hw⟩:=(spanningRestriction_adj Q Y v w).mp (hG hvw)
  exact (spanningRestriction_adj _ _ _ _).mpr
    ⟨hQ (by rw [SimpleGraph.map_adj];exact ⟨v,w,hq,rfl,rfl⟩),Finset.mem_image.mpr ⟨v,hv,rfl⟩,
      Finset.mem_image.mpr ⟨w,hw,rfl⟩⟩

theorem graph_map_disjoint_of_comap (G:SimpleGraph V) (K:SimpleGraph W) (e:V↪W)
    (hG:Disjoint G (K.comap e)):
    Disjoint (G.map e) K:=by
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have hh:=hxy.1
  rw [SimpleGraph.map_adj] at hh
  obtain ⟨v,w,hvw,hv,hw⟩:=hh
  subst x;subst y
  have hb:(⊥:SimpleGraph V).Adj v w:=(disjoint_iff_inf_le.mp hG) ⟨hvw,hxy.2⟩
  exact hb.elim

theorem mapped_local_factor_choice (Q F:SimpleGraph V) (P K:SimpleGraph W) (e:V↪W)
    (T Y:Finset V) (r:ℕ) (hQ:Q.map e≤P)
    (D:Finset (LocalOrdinaryCycle Q F T r))
    (hfactor:(∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
      D.biUnion localOrdinaryVertices=Y)
    (havoid:Disjoint (localOrdinaryFactorGraph D) (K.comap e)):
    (localOrdinaryFactorGraph D).map e≤spanningRestriction P (Y.image e) ∧
      (∀ w,((localOrdinaryFactorGraph D).map e).degree w≤2) ∧
      Disjoint ((localOrdinaryFactorGraph D).map e) K:=by
  exact ⟨graph_map_restriction _ Q P e Y (localOrdinaryFactorGraph_restriction D Y hfactor.2) hQ,
    graph_map_degree_bound _ e 2 (localOrdinaryFactorGraph_degree D hfactor.1),
    graph_map_disjoint_of_comap _ K e havoid⟩

end Oberwolfach
