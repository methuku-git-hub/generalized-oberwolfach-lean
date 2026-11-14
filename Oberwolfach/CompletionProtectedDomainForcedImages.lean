module

public import Oberwolfach.CompletionProtectedDomainImage

@[expose] public section
/-! On a protected set, completion images come only from the already
prescribed vertices, assigned edge endpoints, or explicitly required targets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_protected_domain_forced_images
    {X V:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    (I:Finset V) (B:Finset X) (Φ g:X→V) (Lists Pre Endpoints Required:Finset V)
    (hfixed:∀x∈B,Φ x=g x) (hfree:∀x,x∉B→Φ x∈Lists)
    (havoid:Disjoint Lists I)
    (hforced:B.image g=Pre∪Endpoints∪Required):
    (((Finset.univ.image Φ)∩I).card)≤(Pre∩I).card+(Endpoints∩I).card+(Required∩I).card :=by
  have hfree':∀x,x∉B→Φ x∉I:=by
    intro x hx hi
    exact (Finset.disjoint_left.mp havoid) (hfree x hx) hi
  have hsub:= (completion_protected_domain_image I B Φ g (Pre∪Endpoints∪Required) hfixed hfree' (by rw [hforced])).1
  have hsub':(Finset.univ.image Φ)∩I⊆(Pre∩I)∪(Endpoints∩I)∪(Required∩I):=by
    intro x hx
    have hh:=hsub hx
    simp only [Finset.mem_inter,Finset.mem_union] at hh ⊢
    tauto
  have hcard:=Finset.card_le_card hsub'
  have h₁:=Finset.card_union_le (Pre∩I) (Endpoints∩I)
  have h₂:=Finset.card_union_le ((Pre∩I)∪(Endpoints∩I)) (Required∩I)
  omega
end Oberwolfach
