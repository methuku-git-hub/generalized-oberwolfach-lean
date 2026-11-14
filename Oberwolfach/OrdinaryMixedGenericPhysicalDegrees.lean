module

public import Oberwolfach.OrdinaryMixedGenericPhysicalInjection
public import Oberwolfach.PhysicalMixedSampledDegreeTargets

@[expose] public section
/-! Near-unit physical degrees from the mixed-family root targets and their
active-fiber normalization, on the very same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [LinearOrder V] [DecidableEq U]

theorem ordinary_mixed_generic_physical_degrees
    (π:Equiv.Perm V) (b m:ℕ) (hm:2≤m) (hb:1≤b) (f:I→ℕ) (hf:∀i,1≤f i)
    (wM:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π b (f i+2)→ℝ)
    (σ:(((V×V)⊕(V×V))⊕(Bool×V×U))→Bool) (target:Option I→(((V×V)⊕(V×V))⊕(Bool×V×U))→ℝ)
    (τ t:ℝ) (ht:0≤t):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (f i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    (∀x:PhysicalSampledActive φ σ,
      ∑a∈Finset.univ.filter (fun a=>φ a=x.val ∧ σ a=true),∑i,target i a=1)→
    (∀i a,σ a=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ-target i a|≤t+τ*target i a)→
    ∀x:PhysicalSampledActive φ σ,
      |hypergraphWeightedDegree (physicalSampledCandidateSet φ (mixedCandidateResources R) σ)
        (fun c=>mixedCandidateWeight w c.val) x-1|≤4*((Fintype.card I:ℝ)+1)*t+τ :=by
  intro R w φ htarget hload x
  have hinj:=ordinary_mixed_generic_physical_injective (U:=U) π b m hm hb f hf
  have hh:=physical_mixed_sampled_degree_from_targets φ R w σ hinj 4
    (ordinary_mixed_physical_resource_fiber_card π) target τ t ht htarget hload x
  convert hh using 1 <;> (try simp) <;> (try ring) <;> congr! 5
end Oberwolfach
