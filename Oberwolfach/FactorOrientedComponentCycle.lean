module

public import Oberwolfach.ForwardCycleGraphWalk
public import Oberwolfach.FactorOrientationOrbit

@[expose] public section
/-! Each factor component has a cycle walk that follows its globally chosen
orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_component_has_forward_cycle
    {X:Type} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (C:G.ConnectedComponent):
    ∃(z:X) (p:G.Walk z z),p.IsCycle ∧ p.length=Fintype.card C ∧
      (∀k<p.length,factorCycleOrientation G E (p.getVert k)=p.getVert (k+1)) ∧
      p.toSubgraph.verts=C.supp:=by
  classical
  have hN:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
  obtain ⟨z,p,hp,hlen,hstep⟩:=forward_cycle_graph_walk (Fintype.card C) hN
  let f:SimpleGraph.cycleGraph (Fintype.card C) →g G :=
    ⟨fun i=>(E C i).val,by
      intro x y hxy
      exact ((E C).map_rel_iff).2 hxy⟩
  have hfinj:Function.Injective f:=by
    intro x y hxy
    apply (E C).injective
    exact Subtype.ext hxy
  let q:=p.map f
  refine ⟨f z,q,hp.map hfinj,by simpa [q] using hlen,?_,?_⟩
  · intro k hk
    have hk':k<p.length:=by simpa [q] using hk
    simp only [q,SimpleGraph.Walk.getVert_map]
    change factorCycleOrientation G E (E C (p.getVert k)).val=(E C (p.getVert (k+1))).val
    rw [factor_cycle_orientation_on_component G E C (E C (p.getVert k))]
    simp only [RelIso.symm_apply_apply]
    rw [hstep k hk']
  · ext x
    constructor
    · intro hx
      have hmem:x∈q.support:=q.mem_verts_toSubgraph.mp hx
      obtain ⟨i,hi,hxi⟩:=List.mem_map.mp (by simpa only [q,SimpleGraph.Walk.support_map] using hmem)
      rw [←hxi]
      exact (E C i).property
    · intro hx
      let i:Fin (Fintype.card C):=(E C).symm ⟨x,hx⟩
      have hfull:p.support.dropLast.toFinset=Finset.univ:=by
        apply Finset.eq_univ_of_card
        rw [List.toFinset_card_of_nodup hp.nodup_dropLast_support,List.length_dropLast,p.length_support,hlen,Fintype.card_fin]
        omega
      have hi:i∈p.support:=List.mem_of_mem_dropLast (List.mem_toFinset.mp (by rw [hfull];exact Finset.mem_univ _))
      apply q.mem_verts_toSubgraph.mpr
      change x∈(p.map f).support
      rw [SimpleGraph.Walk.support_map]
      apply List.mem_map.mpr
      refine ⟨i,hi,?_⟩
      change (E C i).val=x
      simp [i]
end Oberwolfach
