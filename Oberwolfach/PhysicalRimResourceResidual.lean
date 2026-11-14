module

public import Oberwolfach.LargeOrSmallResourceSets
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section
/-! Uncovered active rim resources bound the degree of their actual
physical residual graph, using the injective physical representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W:Type} [Fintype V] [Fintype U] [Fintype W] [DecidableEq V] [DecidableEq U] [DecidableEq W]

def rimIncidentResources (φ:W↪Sym2 V⊕(V×U)) (x:V):Finset W:=
  Finset.univ.filter (fun w=>∃y,y≠x ∧ φ w=Sum.inl s(x,y))

def physicalRimResidualGraph (φ:W↪Sym2 V⊕(V×U)) (covered:Finset W):SimpleGraph V where
  Adj x y:=x≠y ∧ ∃w,w∉covered ∧ φ w=Sum.inl s(x,y)
  symm:=⟨by
    intro x y h
    refine ⟨Ne.symm h.1,?_⟩
    obtain ⟨w,hw,he⟩:=h.2
    exact ⟨w,hw,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless:=⟨by intro x h;exact h.1 rfl⟩

def physicalRimCoveredGraph (φ:W↪Sym2 V⊕(V×U)) (covered:Finset W):SimpleGraph V where
  Adj x y:=x≠y ∧ ∃w,w∈covered ∧ φ w=Sum.inl s(x,y)
  symm:=⟨by
    intro x y h
    refine ⟨Ne.symm h.1,?_⟩
    obtain ⟨w,hw,he⟩:=h.2
    exact ⟨w,hw,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless:=⟨by intro x h;exact h.1 rfl⟩

/-- The physical rim edges used by a family of selected resource sets. -/
def physicalRimCandidateUnion {C:Type} [Fintype C] [DecidableEq C]
    (φ:W↪Sym2 V⊕(V×U)) (R:C→Finset W) (M:Finset C):SimpleGraph V where
  Adj x y:=x≠y ∧ ∃c∈M,∃w∈R c,φ w=Sum.inl s(x,y)
  symm:=⟨by
    intro x y h
    obtain ⟨hxy,c,hc,w,hw,he⟩:=h
    exact ⟨Ne.symm hxy,c,hc,w,hw,by simpa only [Sym2.eq_swap] using he⟩⟩
  loopless:=⟨by intro x h;exact h.1 rfl⟩

theorem physical_rim_covered_eq_candidate_union {C:Type} [Fintype C] [DecidableEq C]
    (φ:W↪Sym2 V⊕(V×U)) (R:C→Finset W) (M:Finset C):
    physicalRimCoveredGraph φ (M.biUnion R)=physicalRimCandidateUnion φ R M := by
  ext x y
  simp only [physicalRimCoveredGraph,physicalRimCandidateUnion,Finset.mem_biUnion]
  constructor
  · rintro ⟨h,w,⟨c,hc,hw⟩,he⟩
    exact ⟨h,c,hc,w,hw,he⟩
  · rintro ⟨h,c,hc,w,hw,he⟩
    exact ⟨h,w,⟨c,hc,hw⟩,he⟩

theorem physical_rim_residual_degree_le_uncovered
    (φ:W↪Sym2 V⊕(V×U)) (covered:Finset W) (x:V):
    (physicalRimResidualGraph φ covered).degree x≤(rimIncidentResources φ x\covered).card := by
  let G:=physicalRimResidualGraph φ covered
  let f : {y:V // G.Adj x y} → {w:W // w∈rimIncidentResources φ x\covered} := fun y=>
    ⟨Classical.choose y.property.2,by
      have hw:=Classical.choose_spec y.property.2
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨y.val,Ne.symm y.property.1,hw.2⟩⟩,hw.1⟩⟩
  have hf:Function.Injective f := by
    intro a b hab
    have heq:φ (f a).val=φ (f b).val:=congrArg φ (congrArg Subtype.val hab)
    have ha:= (Classical.choose_spec a.property.2).2
    have hb:= (Classical.choose_spec b.property.2).2
    have hp:s(x,a.val)=s(x,b.val):=Sum.inl.inj (ha.symm.trans (heq.trans hb))
    rcases Sym2.eq_iff.mp hp with ⟨_,h⟩|⟨h,_⟩
    · exact Subtype.ext h
    · exact (b.property.1 h).elim
  have hh:=Fintype.card_le_of_injective f hf
  have hh':Fintype.card (G.neighborSet x)≤(rimIncidentResources φ x\covered).card := by
    convert hh using 1 <;> congr! 4
    simp only [Fintype.card_subtype,Finset.sdiff_eq_filter]
    congr 1
    ext w
    simp
  rw [SimpleGraph.card_neighborSet_eq_degree] at hh'
  exact hh' 
theorem rim_incident_resources_card_le
    (φ:W↪Sym2 V⊕(V×U)) (x:V):
    (rimIncidentResources φ x).card≤Fintype.card V := by
  let f : {w:W // w∈rimIncidentResources φ x}→V := fun w=>
    Classical.choose ((Finset.mem_filter.mp w.property).2)
  have hf:Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply φ.injective
    have ha:φ a.val=Sum.inl s(x,f a):=(Classical.choose_spec ((Finset.mem_filter.mp a.property).2)).2
    have hb:φ b.val=Sum.inl s(x,f b):=(Classical.choose_spec ((Finset.mem_filter.mp b.property).2)).2
    rw [ha,hb,hab]
  have hh:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hh
/-- Only incident sets of size at least the matching threshold need to be
tested; all smaller sets satisfy the same additive degree bound directly. -/
theorem physical_rim_residual_degree_from_large_coverage
    (φ:W↪Sym2 V⊕(V×U)) (covered:Finset W) (a γ:ℝ) (hγ:0≤γ)
    (hlarge:∀x,a*(Fintype.card V:ℝ)≤(rimIncidentResources φ x).card →
      (((rimIncidentResources φ x\covered).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card):
    ∀x,((physicalRimResidualGraph φ covered).degree x:ℝ)≤max a γ*(Fintype.card V:ℝ) := by
  have hsize:∀x,((rimIncidentResources φ x).card:ℝ)≤1*(Fintype.card V:ℝ):=by
    intro x
    simpa using (show ((rimIncidentResources φ x).card:ℝ)≤Fintype.card V by exact_mod_cast rim_incident_resources_card_le φ x)
  have h:=all_resource_sets_from_large_sets (rimIncidentResources φ) covered (Fintype.card V:ℝ) a γ 1
    (Nat.cast_nonneg _) hγ (by norm_num) hsize hlarge
  intro x
  have hh:((physicalRimResidualGraph φ covered).degree x:ℝ)≤(rimIncidentResources φ x\covered).card:=by
    exact_mod_cast physical_rim_residual_degree_le_uncovered φ covered x
  simpa using hh.trans (h x)
end Oberwolfach
