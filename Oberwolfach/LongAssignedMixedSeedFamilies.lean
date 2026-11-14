module

public import Oberwolfach.LongAssignedSeedTargets
public import Oberwolfach.MixedActiveTargetMatching
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! The actual marked candidate family and each ordinary-length family
share one typed resource universe and retain their original identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U CM:Type} {CO:Fin K→Type} [Fintype U] [DecidableEq U]
  [Fintype CM] [∀i,Fintype (CO i)]

abbrev LongMixedSeedFamily (CM:Type) (CO:Fin K→Type):Option (Fin K)→Type
  | none => CM
  | some i => CO i

instance longMixedSeedFamilyFintype : ∀i,Fintype (LongMixedSeedFamily CM CO i)
  | none => inferInstance
  | some _ => inferInstance

def longMixedSeedResources
    (RM:CM→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (RO:∀i,CO i→Finset ((Fin n×Fin n)⊕(Fin n×U))):
    ∀i,LongMixedSeedFamily CM CO i→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))
  | none,c => RM c
  | some i,c => (RO i c).map ordinaryMarkedResourceEmbedding

def longMixedSeedWeight (wM:CM→ℝ) (wO:∀i,CO i→ℝ):
    ∀i,LongMixedSeedFamily CM CO i→ℝ
  | none,c => wM c
  | some i,c => wO i c

theorem long_assigned_mixed_seed_component_loads
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k t τ:ℝ) (ht:0≤t)
    (RM:CM→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (RO:∀i,CO i→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (wM:CM→ℝ) (wO:∀i,CO i→ℝ)
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (hM:∀root,state root=true→
      |resourcePatternLoad RM wM (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ D p k none root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k none root)
    (hO:∀i root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad (RO i) (wO i) (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        longAssignedMixedTarget F hF K m θ D p k (some i) (ordinaryMarkedResourceEmbedding root)|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) (ordinaryMarkedResourceEmbedding root)):
    ∀i root,root∈bernoulliVertexSet state →
      |resourcePatternLoad (longMixedSeedResources RM RO i) (longMixedSeedWeight wM wO i)
        (fun _ _=>true) root state-longAssignedMixedTarget F hF K m θ D p k i root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p k i root := by
  intro i root hactive
  have ha:state root=true:=(mem_bernoulliVertexSet state root).mp hactive
  cases i with
  | none => exact hM root ha
  | some i =>
    change |resourcePatternLoad (fun c=>(RO i c).map ordinaryMarkedResourceEmbedding) (wO i)
      (fun _ _=>true) root state-longAssignedMixedTarget F hF K m θ D p k (some i) root|≤_
    by_cases hr:∃r,ordinaryMarkedResourceEmbedding r=root
    · obtain ⟨r,rfl⟩:=hr
      rw [resource_pattern_load_map]
      exact hO i r ha
    · have hzero:=resource_pattern_load_map_outside (RO i) (wO i) ordinaryMarkedResourceEmbedding state root
        (fun r h=>hr ⟨r,h⟩)
      rw [hzero]
      have htarget:longAssignedMixedTarget F hF K m θ D p k (some i) root=0 := by
        cases root with
        | inl e=>
          cases e with
          | inl xy=>exact (hr ⟨Sum.inl xy,rfl⟩).elim
          | inr xy=>rfl
        | inr a=>
          rcases a with ⟨b,v,u⟩
          cases b
          · exact (hr ⟨Sum.inr (v,u),rfl⟩).elim
          · rfl
      simp [htarget,ht]
end Oberwolfach
