module

public import Oberwolfach.OrdinaryReferenceSpokeLossFromNewEdges

@[expose] public section
/-! At a reference spoke used by a factor, a regular factor has an incident
edge. If old edges avoid that spoke, this edge is newly placed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_spoke_new_edge_coverage
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (f:∀u,X u↪V) (Href:V→U→Prop) (Old New:U→Finset (Sym2 V))
    (hpart:∀u,((F u).edgeFinset).image (Sym2.map (f u))=Old u∪New u)
    (hOld:∀u e,e∈Old u→∀v,v∈e.toFinset→¬Href v u):
    ∀u x,Href (f u x) u→∃y:V,f u x≠y ∧ s(f u x,y)∈New u :=by
  intro u x href
  have hp:0<((F u).neighborFinset x).card:=by
    rw [SimpleGraph.card_neighborFinset_eq_degree,hF u x]
    norm_num
  obtain ⟨y,hy⟩:=Finset.card_pos.mp hp
  have hadj:(F u).Adj x y:=by simpa only [SimpleGraph.mem_neighborFinset] using hy
  have hmem:s(f u x,f u y)∈((F u).edgeFinset).image (Sym2.map (f u)):=by
    apply Finset.mem_image.mpr
    exact ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hadj,by simp⟩
  rw [hpart u] at hmem
  have hnew:s(f u x,f u y)∈New u:=by
    rcases Finset.mem_union.mp hmem with hold|hnew
    · exact False.elim (hOld u _ hold (f u x) (by simp) href)
    · exact hnew
  exact ⟨f u y,fun he=>hadj.ne ((f u).injective he),hnew⟩
end Oberwolfach
