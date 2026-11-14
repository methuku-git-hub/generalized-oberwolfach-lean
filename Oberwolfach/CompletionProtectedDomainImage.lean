module

public import Oberwolfach.MarkedSpokeChangeGraph

@[expose] public section
/-! The free part of a residual completion avoids the protected vertex set;
only explicitly prescribed images can contribute to its local load. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completion_protected_domain_image
    {X V:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    (I:Finset V) (B:Finset X) (Φ g:X→V) (Forced:Finset V)
    (hfixed:∀x∈B,Φ x=g x) (hfree:∀x,x∉B→Φ x∉I)
    (hforced:B.image g⊆Forced):
    (Finset.univ.image Φ)∩I⊆Forced∩I ∧
      (((Finset.univ.image Φ)∩I).card≤(Forced∩I).card) :=by
  have hsub:(Finset.univ.image Φ)∩I⊆Forced∩I:=by
    intro v hv
    obtain ⟨⟨x,_,rfl⟩,hi⟩:=Finset.mem_inter.mp hv |>.imp (fun h=>Finset.mem_image.mp h) id
    have hx:x∈B:=by
      by_contra hx
      exact hfree x hx hi
    have hg:g x∈Forced:=hforced (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    exact Finset.mem_inter.mpr ⟨by simpa only [hfixed x hx] using hg,hi⟩
  exact ⟨hsub,Finset.card_le_card hsub⟩
end Oberwolfach
