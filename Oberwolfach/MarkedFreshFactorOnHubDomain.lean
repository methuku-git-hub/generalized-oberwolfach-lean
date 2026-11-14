module

public import Oberwolfach.MarkedFreshPhysicalHubFactor
public import Oberwolfach.HubSelectedClassGeometry
public import Oberwolfach.HubFactorWeightScales

@[expose] public section

/-! Fresh marked factors on the actual hub-neighbour domain. Coefficients
retain their original ambient normalization. The final ordinary/marked
ratio is imposed on the selected set, not on its parent domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_factor_on_hub_domain (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
    ∀ (A U E K:Type) [Fintype A] [DecidableEq A],N≤Fintype.card A→
    ∀ (tail head:E→A) (ktail khead:K→A) (π:Equiv.Perm A) (b:ℕ)
      (H₀ HK:A→U→Prop) (u:U),
      (∀ v,¬(H₀ v u∧HK v u))→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ v z,H₀ v u→HK z u→v≠π z)→
      κ*Fintype.card A≤((Finset.univ.filter (fun v=>H₀ v u∨HK v u)).card:ℝ)→
      β*(Fintype.card A:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ HK u)→
      (∀ j:Bool,∀ v v':A,v≠v'→(if j then HK v u else H₀ v u)→(if j then HK v' u else H₀ v' u)→
        β*(Fintype.card A:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK j v v' u u))→
      ∀ wt:HubMarkedCycle tail head ktail khead m π b H₀ HK u→ℝ,
      (∀ C,bLo/(Fintype.card A:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card A:ℝ)^m)→
      (∀ v,H₀ v u∨HK v u→|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt v|≤η)→
      1-1/((Finset.univ.filter (fun v=>H₀ v u∨HK v u)).card:ℝ)^q≤
      (FiniteLaw.pi (fun _:A=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ Y:Finset A,(∀ v∈Y,H₀ v u∨HK v u)→
          (Y.filter (fun v=>H₀ v u)).card=m*(Y.filter (fun v=>HK v u)).card→
          ((changed Y ((Finset.univ.filter (fun v=>H₀ v u∨HK v u)).filter (fun v=>σ v=true))).card:ℝ)≤ζ*(p*Fintype.card A)→
          ∀ F:SimpleGraph A,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card A))→
          ∃ D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u),
            ((∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u C')) ∧
              D.biUnion (hubMarkedCycleVertices u)=Y) ∧
            Disjoint (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))) F ∧
            (∀ v,(physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))).degree v≤2) ∧
            (∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubCyclePhysicalEdges u C) (hubCyclePhysicalEdges u C'))) := by
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=marked_fresh_physical_hub_factor m hm β (bLo*κ^m) B hβ (by positivity) hB
  refine ⟨η,ζ*κ,hη,mul_pos hζ hκ,?_⟩
  intro p hp hp1 q
  obtain ⟨N₀,hN₀⟩:=hfresh p hp hp1 q
  obtain ⟨N,hN⟩:=exists_nat_gt (max (1:ℝ) ((N₀:ℝ)/κ))
  refine ⟨N,?_⟩
  intro A U E K _ _ hn tail head ktail khead π b H₀ HK u hd hphys hsep hsize hbase hpath wt hw herr
  let V:=hubNeighbourClass H₀ HK u
  let e:=hubNeighbourEmbedding H₀ HK u hd
  have hcard:Fintype.card (Σ i,V i)=(Finset.univ.filter (fun v=>H₀ v u∨HK v u)).card:=
    hub_neighbour_total_card H₀ HK u hd
  have hNn:(N:ℝ)≤Fintype.card A:=by exact_mod_cast hn
  have hnpos:(0:ℝ)<Fintype.card A:=by linarith [le_max_left (1:ℝ) ((N₀:ℝ)/κ)]
  have hsize':κ*Fintype.card A≤(Fintype.card (Σ i,V i):ℝ):=by simpa only [hcard] using hsize
  have hkpos:(0:ℝ)<Fintype.card (Σ i,V i):=(mul_pos hκ hnpos).trans_le hsize'
  have hkN:N₀≤Fintype.card (Σ i,V i):=by
    have hh:(N₀:ℝ)/κ≤Fintype.card A:=(le_max_right _ _).trans (hN.le.trans hNn)
    have ht:(N₀:ℝ)≤Fintype.card (Σ i,V i):=by linarith [(div_le_iff₀ hκ).mp hh]
    exact_mod_cast ht
  have hkn:(Fintype.card (Σ i,V i):ℝ)≤Fintype.card A:=by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  have hwt (C):(bLo*κ^m)/(Fintype.card (Σ i,V i):ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card (Σ i,V i):ℝ)^m:=
    hub_factor_weight_scale m _ _ κ bLo B (wt C) hnpos hkpos hκ hbLo.le hB hkn hsize' (hw C)
  have herr' (v:Σ i,V i):|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt (e v)|≤η:=by
    apply herr
    rcases v with ⟨i,v⟩
    cases i
    · exact Or.inl v.property
    · exact Or.inr v.property
  have hh:=hN₀ V A U E K hkN e tail head ktail khead π b H₀ HK u
    (hubNeighbourEmbedding_type H₀ HK u hd true) (hubNeighbourEmbedding_type H₀ HK u hd false)
    hphys hsep hbase hpath wt hwt herr'
  conv_lhs at hh => rw [hcard]
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hY hratio hchange F hF
  let Y₁:=selectedHubClasses H₀ HK u Y
  let k:=(Y.filter (fun v=>HK v u)).card
  have hprofile (i:Bool):(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y₁)).card=twoClassProfile m i*k:=by
    rw [selected_hub_class_card]
    cases i
    · exact hratio
    · simp [twoClassProfile,k]
  have hbudget:(ζ*κ)*(p*Fintype.card A)≤ζ*(p*Fintype.card (Σ i,V i)):=by
    have ht:=mul_le_mul_of_nonneg_left hsize' (mul_nonneg hζ.le hp.le)
    nlinarith only [ht]
  have hchange':((((bernoulliVertexSet (fun z=>σ (e z)))\Y₁).card+
      (Y₁\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (Σ i,V i)):=by
    rw [←changed_card_eq_differences,selected_hub_class_change_card H₀ HK u hd Y hY]
    exact hchange.trans hbudget
  obtain ⟨D,hD,havoid,hdeg,hedges⟩:=hσ Y₁ k hprofile hchange' F (fun v=>(hF v).trans hbudget)
  refine ⟨D,⟨hD.1,?_⟩,havoid,hdeg,hedges⟩
  exact hD.2.trans (by convert selected_hub_classes_image H₀ HK u hd Y hY using 1 <;> congr!)

end Oberwolfach
