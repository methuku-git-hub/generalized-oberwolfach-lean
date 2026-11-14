module

public import Oberwolfach.MarkedEmbeddedHubPaths
public import Oberwolfach.MarkedEmbeddedHostGeometry
public import Oberwolfach.InnerAmbientCountWeightScale

@[expose] public section

/-! The local count and fixed-weight hypotheses supply the ambient inputs
of the mixed boundary selector. Only the numerical bounds are converted;
the cycle weights, omitted-root path conditions and original arc IDs stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_embedded_hub_inputs
    {W V U E K:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V) (hf:∀ x,f (ρ x)=π (f x))
    (tail head:E→W) (ktail khead:K→W) (m b:ℕ) (H₀ HK:W→U→Prop) (u:U)
    (κ κhub β bLo B η:ℝ) (hk:0<κ) (hk1:κ≤1) (hkh:0≤κhub) (hβ:0≤β) (hb:0≤bLo) (hB:0≤B)
    (hn:0<Fintype.card V) (hkn:κ*Fintype.card V≤Fintype.card W)
    (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead ρ))
    (hdis:∀ x,¬(H₀ x u∧HK x u)) (hsep:∀ x y,H₀ x u→HK y u→x≠ρ y)
    (hsize:κhub*Fintype.card W≤((Finset.univ.filter (fun v=>H₀ v u∨HK v u)).card:ℝ))
    (hcycles:β*(Fintype.card W:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m ρ b H₀ HK u))
    (hpaths:∀ j:Bool,∀ x y:W,x≠y→(if j then HK x u else H₀ x u)→(if j then HK y u else H₀ y u)→
      β*(Fintype.card W:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK j x y u u))
    (wt:HubMarkedCycle tail head ktail khead m ρ b H₀ HK u→ℝ)
    (hw:∀ C,bLo/(Fintype.card W:ℝ)^m≤wt C∧wt C≤B/(Fintype.card W:ℝ)^m)
    (herr:∀ x,H₀ x u∨HK x u→|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt x|≤η):
    let H₀':=spokeRelationImage f H₀
    let HK':=spokeRelationImage f HK
    let wt':=fun C=>wt ((hubCycleEmbeddingEquiv f ρ π hf tail head ktail khead m b H₀ HK u).symm C)
    Function.Injective (markedPhysicalEdge (f∘tail) (f∘head) (f∘ktail) (f∘khead) π)∧
    (∀ v,¬(H₀' v u∧HK' v u))∧
    (∀ v z,H₀' v u→HK' z u→v≠π z)∧
    (κhub*κ)*Fintype.card V≤((Finset.univ.filter (fun v=>H₀' v u∨HK' v u)).card:ℝ)∧
    (β*κ^(m+1))*(Fintype.card V:ℝ)^(m+1)≤
      Fintype.card (HubMarkedCycle (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b H₀' HK' u)∧
    (∀ j:Bool,∀ v z:V,v≠z→(if j then HK' v u else H₀' v u)→(if j then HK' z u else H₀' z u)→
      (β*κ^(m+1))*(Fintype.card V:ℝ)^m≤
        Fintype.card (RootFirstCommonMarkedPath (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b H₀' HK' j v z u u))∧
    (∀ C,bLo/(Fintype.card V:ℝ)^m≤wt' C∧wt' C≤(B/κ^m)/(Fintype.card V:ℝ)^m)∧
    (∀ v,H₀' v u∨HK' v u→|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt' v|≤η):=by
  intro H₀' HK' wt'
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have haR:(0:ℝ)<Fintype.card W:=(mul_pos hk hnR).trans_le hkn
  have han:(Fintype.card W:ℝ)≤Fintype.card V:=by exact_mod_cast Fintype.card_le_of_injective f f.injective
  have hsc:=inner_ambient_count_scales m (Fintype.card V) (Fintype.card W) κ β
    hnR.le haR.le hk.le hk1 hβ hkn
  refine ⟨markedPhysicalEdge_embedding_injective f ρ π hf tail head ktail khead hphys,
    spokeRelationImage_disjoint f H₀ HK u hdis,
    spokeRelationImage_separated f ρ π hf H₀ HK u hsep,?_,?_,?_,?_,?_⟩
  · change (κhub*κ)*Fintype.card V≤((Finset.univ.filter (fun v=>spokeRelationImage f H₀ v u∨spokeRelationImage f HK v u)).card:ℝ)
    rw [spokeRelationImage_neighbourhood_card]
    nlinarith only [mul_le_mul_of_nonneg_left hkn hkh,hsize]
  · have hc:=Fintype.card_congr (hubCycleEmbeddingEquiv f ρ π hf tail head ktail khead m b H₀ HK u)
    exact hsc.1.trans (hcycles.trans_eq (by exact_mod_cast hc))
  · intro j v z hvz hv hz
    have hv':∃ x,f x=v∧(if j then HK x u else H₀ x u):=by cases j <;> exact hv
    have hz':∃ x,f x=z∧(if j then HK x u else H₀ x u):=by cases j <;> exact hz
    obtain ⟨x,hx,hxH⟩:=hv'
    obtain ⟨y,hy,hyH⟩:=hz'
    have hxy:x≠y:=by intro he;apply hvz;exact hx.symm.trans ((congrArg f he).trans hy)
    have hp:=hpaths j x y hxy hxH hyH
    have hcard:=hubPathEmbedding_card f ρ π hf tail head ktail khead m b H₀ HK j x y u u
    have hcardR:(Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK j x y u u):ℝ)≤
      Fintype.card (RootFirstCommonMarkedPath (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b H₀' HK' j (f x) (f y) u u):=by exact_mod_cast hcard
    rw [hx,hy] at hcardR
    exact hsc.2.trans (hp.trans hcardR)
  · intro C
    exact inner_ambient_weight_scale m _ _ κ bLo B _ hnR haR hk hb hB han hkn (hw _)
  · intro v hv
    have hv':∃ x,f x=v∧(H₀ x u∨HK x u):=by
      rcases hv with ⟨x,hx,hH⟩|⟨x,hx,hH⟩
      · exact ⟨x,hx,Or.inl hH⟩
      · exact ⟨x,hx,Or.inr hH⟩
    obtain ⟨x,hx,hxH⟩:=hv'
    subst v
    rw [hubCycleEmbedding_weighted_degree]
    exact herr x hxH

end Oberwolfach
