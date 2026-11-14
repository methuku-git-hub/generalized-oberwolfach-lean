module

public import Oberwolfach.MarkedSequentialHubCover
public import Oberwolfach.MarkedDeletionRobustHubFactor

@[expose] public section

/-! Cover every spoke at the prescribed distinct marked hubs. The factors
are constructed from fixed weights and original cycle/path counts; the
previously selected physical rim edges are a bounded-degree deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_cover_from_fixed_weights (m:ℕ) (hm:3≤m) (β bLo B:ℝ)
    (hβ:0<β) (hbLo:0<bLo) (hB:0≤B):
    ∃ θ:ℝ,0<θ∧∃ N:ℕ,1≤N∧∀ (V U E K:Type)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→∀ (n:ℕ) (u:Fin n→U),Function.Injective u→
      (2*n:ℝ)≤θ*Fintype.card V→
      ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
      (b:ℕ) (H₀ Hₖ:V→U→Prop),1≤b→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ i v,¬(H₀ v (u i)∧Hₖ v (u i)))→
      (∀ i v z,H₀ v (u i)→Hₖ z (u i)→v≠π z)→
      (∀ i,β*Fintype.card V≤Fintype.card (hubNeighbourClass H₀ Hₖ (u i) true))→
      (∀ i,Fintype.card (hubNeighbourClass H₀ Hₖ (u i) false)=m*Fintype.card (hubNeighbourClass H₀ Hₖ (u i) true))→
      (∀ i,β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ (u i)))→
      (∀ i j,∀ v v':V,v≠v'→(if j then Hₖ v (u i) else H₀ v (u i))→(if j then Hₖ v' (u i) else H₀ v' (u i))→
        β*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' (u i) (u i)))→
      ∀ w:Fin n→MarkedCycleTuple tail head ktail khead m π b→ℝ,
      (∀ i C,bLo/(Fintype.card V:ℝ)^m≤w i C∧w i C≤B/(Fintype.card V:ℝ)^m)→
      (∀ i v,H₀ v (u i)∨Hₖ v (u i)→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) (u i))
        (fun C=>w i (hubCycleAsMarked (u i) C)) v|≤θ)→
      ∃ M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
        M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H₀ v (u i)∨Hₖ v (u i))).image (fun v=>Sum.inr (v,u i)))∧
        (∀ v,(markedPackingRimGraph M).degree v≤2*n)∧
        (∀ i v,H₀ v (u i)∨Hₖ v (u i)→∃! W:M,Sum.inr (v,u i)∈markedWheelPhysicalResources W.val)∧
        (∀ e∈markedPackingRims M,e.card=2):=by
  obtain ⟨θ,hθ,N,hN,hfactor⟩:=marked_deletion_robust_hub_factor m hm β bLo B hβ hbLo hB
  refine ⟨θ,hθ,N,hN,?_⟩
  intro V U E K _ _ _ _ _ hn n u hu hnθ tail head ktail khead π b H₀ Hₖ hb hp hdis hsep hsize hratio hbase hpath w hw herr
  apply sequential_marked_hub_wheels (by omega) hb hp u hu hsep
  intro i D hD
  exact hfactor V U E K hn tail head ktail khead π b H₀ Hₖ (u i) hb hp (hdis i) (hsep i)
    (hsize i) (hratio i) (hbase i) (hpath i) (w i) (hw i) (herr i) D (fun v=>
      (show (D.degree v:ℝ)≤2*(n:ℝ) by exact_mod_cast hD v).trans hnθ)

end Oberwolfach
