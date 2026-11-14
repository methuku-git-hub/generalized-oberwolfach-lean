module

public import Oberwolfach.MarkedFreshHubFactor
public import Oberwolfach.MarkedPhysicalConflictGraph
public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section

/-! A fresh marked factor with parent classes of arbitrary sizes. The exact
one-to-m ratio is imposed only on the final selected classes. The paired
absorber counts are derived from the actual cycle and root-omitted common
path counts. One event includes all permitted later class changes and
forbidden graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 10000000
noncomputable section
open scoped BigOperators
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_physical_hub_factor (m : ℕ) (hm : 3<m+1) (β b₀ B₀ : ℝ)
    (hβ : 0<β) (hb₀ : 0<b₀) (hB₀ : 0≤B₀) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V : Bool→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (A U E K : Type) [Fintype A] [DecidableEq A],N≤Fintype.card (Σ i,V i)→
      ∀ (e:(Σ i,V i)↪A) (tail head:E→A) (ktail khead:K→A)
        (π:Equiv.Perm A) (b:ℕ) (H₀ HK:A→U→Prop) (u:U),
      (∀ v,HK v u↔∃ z:V true,e ⟨true,z⟩=v)→
      (∀ v,H₀ v u↔∃ z:V false,e ⟨false,z⟩=v)→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ v z,H₀ v u→HK z u→v≠π z)→
      β*(Fintype.card A:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ HK u)→
      (∀ j:Bool,∀ v v':A,v≠v'→(if j then HK v u else H₀ v u)→(if j then HK v' u else H₀ v' u)→
        β*(Fintype.card A:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK j v v' u u))→
      ∀ wt:HubMarkedCycle tail head ktail khead m π b H₀ HK u→ℝ,
      (∀ C,b₀/(Fintype.card (Σ i,V i):ℝ)^m≤wt C ∧ wt C≤B₀/(Fintype.card (Σ i,V i):ℝ)^m)→
      (∀ v,|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt (e v)|≤η)→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
      (FiniteLaw.pi (fun _:A=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
          (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=twoClassProfile m i*k)→
          ((((bernoulliVertexSet (fun z=>σ (e z)))\Y).card+(Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)
            ≤ζ*(p*Fintype.card (Σ i,V i))→
          ∀ F:SimpleGraph A,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
          ∃ D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u),
            ((∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u C')) ∧
              D.biUnion (hubMarkedCycleVertices u)=Y.image e) ∧
            Disjoint (physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))) F ∧
            (∀ v,(physicalEdgeGraph (D.biUnion (hubCyclePhysicalEdges u))).degree v≤2) ∧
            (∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubCyclePhysicalEdges u C) (hubCyclePhysicalEdges u C'))) := by
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=marked_fresh_hub_factor m hm β b₀ B₀ hβ hb₀ hB₀
  refine ⟨η,ζ/3,hη,by positivity,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hfresh p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ A U E K _ _ hn e tail head ktail khead π b H₀ HK u hK hO hphys hsep hbase hpath wt hw herr
  have hh:=hN V A U E K hn e tail head ktail khead π b H₀ HK u hK hO hbase hpath wt hw herr
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y k hprofile hchange F hF
  have hchange':((((bernoulliVertexSet (fun z=>σ (e z)))\Y).card+
      (Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (Σ i,V i)):=by
    have hn:0≤ζ*(p*Fintype.card (Σ i,V i)):=by positivity
    nlinarith only [hchange,hn]
  have hD (v:A):((markedPhysicalConflictGraph F π).degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)):=by
    have ht:=marked_physical_conflict_degree_bound F π ((ζ/3)*(p*Fintype.card (Σ i,V i))) hF v
    nlinarith only [ht]
  obtain ⟨M,hM,havoid⟩:=hσ Y k hprofile hchange' (markedPhysicalConflictGraph F π) hD
  exact ⟨M,hM,marked_factor_avoids_physical_rims (by omega) u M F havoid,
    marked_factor_physical_degree u hsep M hM.1,marked_factor_physical_edges_disjoint u hphys M hM.1⟩

end Oberwolfach
