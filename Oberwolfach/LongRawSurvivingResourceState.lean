module

public import Oberwolfach.LongRawHubContext
public import Oberwolfach.MarkedRawSampledPhysicalEmbedding
public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! Delete specified physical rim edges from the fixed raw approximate state;
all sampled spokes remain available. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longRawSurvivingResources (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    Finset (LongRawHubResource n U) :=
  (bernoulliVertexSet (longRawHubState P π d raw g j)).filter (fun z=>
    match typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z) with
    | Sum.inl edge => edge∉F
    | Sum.inr _ => True)

theorem long_raw_surviving_resources_subset (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    longRawSurvivingResources P π d raw g j F ⊆ bernoulliVertexSet (longRawHubState P π d raw g j):=by
  exact Finset.filter_subset _ _

theorem long_raw_surviving_resource_not_deleted (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (z:LongRawHubResource n U) (hz:z∈longRawSurvivingResources P π d raw g j F):
    ∀edge,typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F :=by
  have h:=(Finset.mem_filter.mp hz).2
  intro edge he
  rw [he] at h
  exact h

theorem long_raw_surviving_sample_spoke (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (z:LongRawHubResource n U) (hz:z∈bernoulliVertexSet (longRawHubState P π d raw g j))
    (hspoke:∃v u,typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inr (v,u)):
    z∈longRawSurvivingResources P π d raw g j F :=by
  apply Finset.mem_filter.mpr
  obtain ⟨v,u,hu⟩:=hspoke
  refine ⟨hz,?_⟩
  rw [hu]
  trivial
end Oberwolfach
