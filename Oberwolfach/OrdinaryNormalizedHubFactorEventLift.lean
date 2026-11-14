module

public import Oberwolfach.OrdinaryNormalizedHubFactorsOnPhysicalSample
public import Oberwolfach.OrdinaryNormalizedHubConflictDegree
public import Oberwolfach.OrdinaryInducedFactorLift
public import Oberwolfach.OrdinaryInducedFinsetTransfer

@[expose] public section
/-! Translate the normalized factor event back to the ambient hub class.
The sample, requested vertices, and forbidden edges remain the same. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_normalized_hub_factor_event_lift
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (p ζ:ℝ) (σ:Sym2 (V⊕U)→Bool)
    (h:OrdinaryNormalizedHubFactorEvent m Q F H A Z p ζ σ):
    ∀j:{u:U // u∉Z},∀Y:Finset V,Y⊆ordinaryBoundaryHubSet H Z A j→(m+1)∣Y.card→
      (((((ordinaryBoundaryHubSet H Z A j).filter (fun v=>σ (hubSpokeCoin j.val v)=true))\Y).card+
        (Y\((ordinaryBoundaryHubSet H Z A j).filter (fun v=>σ (hubSpokeCoin j.val v)=true))).card:ℕ):ℝ)≤
          ζ*(p*(ordinaryBoundaryHubSet H Z A j).card)→
      ∀K:SimpleGraph V,(∀v,(K.degree v:ℝ)≤ζ*(p*(ordinaryBoundaryHubSet H Z A j).card))→
      ∃D:Finset (LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) (m+1)),
        (∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        D.biUnion localOrdinaryVertices=Y ∧
        (∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  intro j Y hYT hdiv hchange K hK
  let T:=ordinaryBoundaryHubSet H Z A j
  let R:=T.filter (fun v=>σ (hubSpokeCoin j.val v)=true)
  let Yi:=ordinaryInducedFinset T Y
  let Ri:=ordinaryInducedFinset T R
  have hRT:R⊆T:=Finset.filter_subset _ _
  have hYcard:Yi.card=Y.card:=ordinary_induced_finset_card T Y hYT
  have hYimage:Yi.image Subtype.val=Y:=ordinary_induced_finset_image T Y hYT
  have hsample:Finset.univ∩bernoulliVertexSet (fun v:{v:V // v∈T}=>σ (hubSpokeCoin j.val v.val))=Ri:=by
    ext v
    simp [Ri,R,ordinaryInducedFinset,bernoulliVertexSet,v.property]
  have hdiff1:(Ri\Yi).card=(R\Y).card:=by
    rw [←ordinary_induced_finset_sdiff]
    exact ordinary_induced_finset_card T (R\Y) (Finset.sdiff_subset.trans hRT)
  have hdiff2:(Yi\Ri).card=(Y\R).card:=by
    rw [←ordinary_induced_finset_sdiff]
    exact ordinary_induced_finset_card T (Y\R) (Finset.sdiff_subset.trans hYT)
  have hc:Fintype.card {v:V // v∈T}=T.card:=by simp
  have hchange':((((Finset.univ∩bernoulliVertexSet (fun v:{v:V // v∈T}=>σ (hubSpokeCoin j.val v.val)))\Yi).card+
      (Yi\(Finset.univ∩bernoulliVertexSet (fun v:{v:V // v∈T}=>σ (hubSpokeCoin j.val v.val)))).card:ℕ):ℝ)≤
        ζ*(p*Fintype.card {v:V // v∈T}):=by
    rw [hsample,hdiff1,hdiff2,hc]
    exact hchange
  have hK':∀v:{v:V // v∈T},((K.induce (T:Set V)).degree v:ℝ)≤ζ*(p*Fintype.card {v:V // v∈T}):=by
    intro v
    rw [hc]
    have hk:((K.induce (T:Set V)).degree v:ℝ)≤K.degree v.val:=by
      exact_mod_cast ordinary_induced_degree_le K T v
    exact hk.trans (hK v.val)
  have hdiv':(m+1)∣Yi.card:=by rw [hYcard];exact hdiv
  obtain ⟨D,⟨hd,hcover⟩,ha⟩:=h j Yi hdiv' hchange' (K.induce (T:Set V)) hK'
  obtain ⟨D',hd',hc',ha'⟩:=ordinary_induced_factor_lift (spanningRestriction Q A) F K T Yi D hd hcover ha
  refine ⟨D',hd',?_,ha'⟩
  exact hc'.trans hYimage
end Oberwolfach
