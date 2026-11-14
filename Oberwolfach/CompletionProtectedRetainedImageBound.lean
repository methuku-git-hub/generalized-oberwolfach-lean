module

public import Oberwolfach.CompletionProtectedDomainImage
public import Oberwolfach.CompletionProtectedImageMatchingBound

@[expose] public section
/-! Missing targets are outside the retained ordinary-spoke set. Thus, on
the protected set, the completion image can consume retained spokes only
through prescribed vertices or assigned matching endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_protected_retained_image_bound
    {X V:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    (I Outer:Finset V) (B:Finset X) (Φ g:X→V) (Lists Pre Required:Finset V)
    (M:Finset (V×V))
    (hfixed:∀x∈B,Φ x=g x) (hfree:∀x,x∉B→Φ x∈Lists)
    (havoid:Disjoint Lists I) (hRequired:Disjoint Required Outer)
    (hforced:B.image g=Pre∪prescribedMatchingEndpoints M∪Required):
    ((((Finset.univ.image Φ)∩I)∩Outer).card)≤Pre.card+2*M.card :=by
  have hfree':∀x,x∉B→Φ x∉I:=by
    intro x hx hi
    exact (Finset.disjoint_left.mp havoid) (hfree x hx) hi
  have hsub:= (completion_protected_domain_image I B Φ g (Pre∪prescribedMatchingEndpoints M∪Required)
    hfixed hfree' (by rw [hforced])).1
  have hsub':((Finset.univ.image Φ)∩I)∩Outer⊆Pre∪prescribedMatchingEndpoints M:=by
    intro v hv
    have hv0: v∈(Finset.univ.image Φ)∩I:=(Finset.mem_inter.mp hv).1
    have hvo:v∈Outer:=(Finset.mem_inter.mp hv).2
    have hh: v∈Pre∪prescribedMatchingEndpoints M∪Required:=(Finset.mem_inter.mp (hsub hv0)).1
    rcases Finset.mem_union.mp hh with hp|hr
    · exact hp
    · exact False.elim ((Finset.disjoint_left.mp hRequired) hr hvo)
  have hh:=(Finset.card_le_card hsub').trans (Finset.card_union_le Pre (prescribedMatchingEndpoints M))
  have hm:=prescribed_matching_endpoints_card_le_twice M
  omega
end Oberwolfach
