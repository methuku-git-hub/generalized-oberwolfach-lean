module

public import Oberwolfach.MarkedHubCoverFromWeights
public import Oberwolfach.MarkedSampleHubLoadTransfer
public import Oberwolfach.MarkedSampleHubCountTransfer
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.SuccessorSeedBounds

@[expose] public section

/-! A hub packing from the actual physical sample, fixed successor weights,
and local configuration and spoke-load estimates. No factor-existence
hypothesis is supplied to this construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_hub_cover (r:ℕ) (β aLo B pstar:ℝ)
    (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ θ:ℝ,0<θ∧∃ N:ℕ,1≤N∧∀ (V U Γ Color:Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→∀ (n:ℕ) (u:Fin n→U),Function.Injective u→
      (2*n:ℝ)≤θ*Fintype.card V→
      ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ),1≤d→
      ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
      pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
      ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
      ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
      (∀ i v,¬(H false v (u i)∧H true v (u i)))→
      (∀ i v z,H false v (u i)→H true z (u i)→v≠π z)→
      (∀ i,β*Fintype.card V≤Fintype.card (hubNeighbourClass (H false) (H true) (u i) true))→
      (∀ i,Fintype.card (hubNeighbourClass (H false) (H true) (u i) false)=
        (r+4)*Fintype.card (hubNeighbourClass (H false) (H true) (u i) true))→
      MarkedLocalConfigurationsWithSpokes r P π d Finset.univ β β σ H→
      MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight θ σ H→
      ∃ M:Finset (MarkedWheel
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (r+4) π (3*d) (H false) (H true)),
        (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
        M.biUnion markedWheelPhysicalResources=(markedPackingRims M).image Sum.inl∪
          Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun v=>H false v (u i)∨H true v (u i))).image (fun v=>Sum.inr (v,u i)))∧
        (∀ v,(markedPackingRimGraph M).degree v≤2*n)∧
        (∀ i v,H false v (u i)∨H true v (u i)→∃! W:M,Sum.inr (v,u i)∈markedWheelPhysicalResources W.val)∧
        (∀ e∈markedPackingRims M,e.card=2):=by
  obtain ⟨θ,hθ,N,hN,hcover⟩:=marked_hub_cover_from_fixed_weights (r+4) (by omega) β
    (aLo/2) (2*B/pstar^(2*(r+4)+1)) hβ (by positivity) (by positivity)
  refine ⟨θ,hθ,N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn n u hu hnθ P π d hd D τ p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 weight hw σ H hdis hsep hsize hratio hconfigs hload
  have hnpos:0<Fintype.card V:=by omega
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
  have hcounts:=marked_local_configurations_hub_counts r P π d Finset.univ β β σ H hconfigs
  refine hcover V U E K hn n u hu hnθ (fun e=>e.val.1) (fun e=>e.val.2)
    (fun e=>e.val.1) (fun e=>e.val.2) π (3*d) (H false) (H true) (by omega)
    (markedSampleArc_physical_injective P π (3*d) _) hdis hsep hsize hratio ?_ ?_
    (fun _ C=>weight C.val/(D*p^(r+4)*k*s₀^(r+4))) ?_ ?_
  · intro i
    simpa only [Finset.card_univ,Nat.add_assoc,Nat.reduceAdd] using hcounts.1 (u i)
  · intro i j v v' hv _ _
    simpa only [Finset.card_univ] using hcounts.2 (u i) j v v' hv
  · intro i C
    exact ⟨successor_seed_positive_lower hw (by omega) hnpos hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 haLo.le hB C.val
      (marked_sample_cycle_valid P π (3*d) (r+4) _ C) C.property.1,
      (successor_seed_nonneg_upper hw (by omega) hnpos hDlo hDhi
        p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB C.val).2⟩
  · intro i v hv
    simpa only [hubCycleAsMarked] using
      marked_sample_hub_degree_error P π d (r+4) D p k s₀ θ weight σ H hload (u i) (hdis i) v hv

end Oberwolfach
