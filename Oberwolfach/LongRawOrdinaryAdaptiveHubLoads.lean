module

public import Oberwolfach.LongRawAdaptivePhysicalDeletion
public import Oberwolfach.LongRawHubFrequenciesForAssignment

@[expose] public section
/-! Actual ordinary seed families inherit their fixed raw load targets after
any physical rim deletion, once their near/far pair bounds are supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_ordinary_hub_loads_after_physical_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (w:∀i:Fin K,longRawHubCandidates (U:=U) π d m ℓ (some i)→ℝ)
    (hw:∀i c,0≤w i c) (target:Fin K→LongRawHubResource n U→ℝ)
    (err:Fin K→LongRawHubResource n U→ℝ)
    (δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ)
    (M N:Fin K→LongRawHubResource n U→ℝ) (hM:∀i z,0≤M i z) (hN:∀i z,0≤N i z)
    (Sroot Troot:Fin K→LongRawHubResource n U→Finset (Fin n)):
    let state:=longRawHubState P π d raw g j
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let survived:=fun z=>decide (z∈S)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈D.edgeFinset)
    (∀i z,z∈T→|resourcePatternLoad (longRawHubResources (U:=U) π d m ℓ (some i))
      (w i) (fun _ _=>true) z state-target i z|≤err i z)→
    (∀i z,∀a∈Deleted,resourceOmittedPairWeight (longRawHubResources (U:=U) π d m ℓ (some i))
      (w i) z a≤(if longRawResourceTail a∈Sroot i z ∨ longRawResourceHead a∈Troot i z then M i z else N i z))→
    ∀i z,z∈S→|resourcePatternLoad (longRawHubResources (U:=U) π d m ℓ (some i))
      (w i) (fun _ _=>true) z survived-target i z|≤err i z+
        2*δ*(((Sroot i z).card+(Troot i z).card:ℝ)*M i z+(n:ℝ)*N i z) :=by
  intro state T S survived Deleted hload hpair i z hz
  have ht:z∈T:=(long_raw_surviving_resources_subset P π d raw g j D.edgeFinset) hz
  have hp:=long_raw_adaptive_pattern_load_physical_deletion P D π d raw g j
    (longRawHubResources (U:=U) π d m ℓ (some i)) (w i) (hw i) z (target i z) δ (M i z) (N i z)
    (hM i z) (hN i z) hD (Sroot i z) (Troot i z) (hpair i z)
  change |resourcePatternLoad (longRawHubResources (U:=U) π d m ℓ (some i))
    (w i) (fun _ _=>true) z survived-target i z|≤
      |resourcePatternLoad (longRawHubResources (U:=U) π d m ℓ (some i))
        (w i) (fun _ _=>true) z state-target i z|+
        2*δ*(((Sroot i z).card+(Troot i z).card:ℝ)*M i z+(n:ℝ)*N i z) at hp
  exact hp.trans (add_le_add (hload i z ht) (le_refl _))
end Oberwolfach
