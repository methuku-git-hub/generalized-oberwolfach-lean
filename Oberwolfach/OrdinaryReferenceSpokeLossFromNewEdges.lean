module

public import Oberwolfach.PrescribedFamilyPhysicalDegree
public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! Every used reference spoke is charged to a new physical edge of its
factor. Pairwise edge-disjointness bounds row loss by the new-edge degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_spoke_loss_from_new_edges
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (f:∀u,X u↪V) (Href:V→U→Prop) (New:U→Finset (Sym2 V))
    (hpair:PairwisePhysicalDisjoint New)
    (hcover:∀u x,Href (f u x) u→∃y:V,f u x≠y ∧ s(f u x,y)∈New u)
    (loss:ℝ) (hdegree:∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤loss):
    ∀v,((Finset.univ.filter (fun u=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤loss :=by
  intro v
  let Lost:Finset U:=Finset.univ.filter (fun u=>Href v u ∧ v∈Set.range (f u))
  have hex:∀u∈Lost,∃y:V,v≠y ∧ s(v,y)∈New u:=by
    intro u hu
    obtain ⟨href,x,hx⟩:=(Finset.mem_filter.mp hu).2
    subst v
    exact hcover u x href
  let pick:U→V:=fun u=>if h:∃y:V,v≠y ∧ s(v,y)∈New u then Classical.choose h else v
  have hpick:∀u∈Lost,v≠pick u ∧ s(v,pick u)∈New u:=by
    intro u hu
    have h:=hex u hu
    simpa only [pick,dif_pos h] using (Classical.choose_spec h)
  have hcard:Lost.card≤(prescribedPhysicalUnion New).degree v:=by
    have hh:Lost.card≤((prescribedPhysicalUnion New).neighborFinset v).card:=by
      apply Finset.card_le_card_of_injOn pick (t:=(prescribedPhysicalUnion New).neighborFinset v)
      · intro u hu
        simp only [Finset.mem_coe,SimpleGraph.mem_neighborFinset]
        apply (SimpleGraph.fromEdgeSet_adj _).mpr
        exact ⟨Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,(hpick u hu).2⟩,(hpick u hu).1⟩
      · intro u hu w hw heq
        by_contra hne
        have hmem:s(v,pick u)∈New w:=by simpa only [heq] using (hpick w hw).2
        exact Finset.disjoint_left.mp (hpair u w hne) (hpick u hu).2 hmem
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh
  have hh:(Lost.card:ℝ)≤(prescribedPhysicalUnion New).degree v:=by exact_mod_cast hcard
  exact hh.trans (hdegree v)

theorem ordinary_reference_spoke_column_loss_from_remaining
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (f:∀u,X u↪V) (Href:V→U→Prop) (Old Rem:∀u,Finset (X u))
    (hcover:∀u,Old u∪Rem u=Finset.univ)
    (hOld:∀u x,x∈Old u→¬Href (f u x) u)
    (loss:ℝ) (hRem:∀u,((Rem u).card:ℝ)≤loss):
    ∀u,((Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤loss :=by
  intro u
  have hsub:Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u))⊆(Rem u).image (f u):=by
    intro v hv
    obtain ⟨href,x,hx⟩:=(Finset.mem_filter.mp hv).2
    have hnot:x∉Old u:=by intro ho;exact hOld u x ho (hx ▸ href)
    have hrem:x∈Rem u:=by
      have hh:x∈Old u∪Rem u:=by rw [hcover u];exact Finset.mem_univ _
      exact (Finset.mem_union.mp hh).resolve_left hnot
    exact Finset.mem_image.mpr ⟨x,hrem,hx⟩
  have hc:((Finset.univ.filter (fun v=>Href v u ∧ v∈Set.range (f u))).card:ℝ)≤(Rem u).card:=by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le)
  exact hc.trans (hRem u)
end Oberwolfach
