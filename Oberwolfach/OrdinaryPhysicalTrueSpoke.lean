module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.PhysicalSampledCandidateRestriction
public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section
/-! When the sampled true and false spoke states are exclusive, a physical
spoke covered by a sampled candidate has the correct true typed coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_physical_candidate_true_spoke
    {V U C:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (π:Equiv.Perm V) (R:C→Finset (((V×V)⊕(V×V))⊕(Bool×V×U)))
    (Rim:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop)
    (hexclusive:∀v u,H true v u→¬H false v u):
    let state:=typedMarkedResourceState Rim H
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(c:PhysicalSampledCandidate R state) (x:PhysicalSampledActive φ state) (v:V) (u:U),
      x.val=Sum.inr (v,u)→x∈physicalSampledCandidateSet φ R state c→H true v u→
      Sum.inr (true,v,u)∈R c.val:=by
  intro state φ c x v u hx hc ht
  have hm: x.val∈(R c.val).image φ:=(physical_sampled_candidate_set_mem φ R state c x).mp hc
  obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hm
  have he':φ a=Sum.inr (v,u):=he.trans hx
  cases a with
  | inl a=>simp [φ,ordinaryMixedPhysicalResource] at he'
  | inr a=>
    obtain ⟨b,z,w⟩:=a
    simp only [φ,ordinaryMixedPhysicalResource,Sum.elim_inr,Sum.inr.injEq,Prod.mk.injEq] at he'
    obtain ⟨rfl,rfl⟩:=he'
    cases b with
    | false=>
      have hh:=c.property (Sum.inr (false,z,w)) ha
      have hf:H false z w:=by simpa only [state,typedMarkedResourceState,Sum.elim_inr,decide_eq_true_eq] using hh
      exact False.elim (hexclusive z w ht hf)
    | true=>exact ha
end Oberwolfach
