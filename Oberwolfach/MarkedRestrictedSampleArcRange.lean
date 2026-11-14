module

public import Oberwolfach.MarkedSampleArcEmbedding
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! The active sample has exactly the original typed arcs with both
auxiliary endpoints in the embedded row domain. No physical edge receives
a new orientation or mark under restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A U B Gamma Color:Type} [Fintype V] [Fintype A] [Fintype U] [Fintype B]
  [Fintype Gamma] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

def markedRestrictedSampleArcEmbedding
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (j:Bool):
    MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) j↪
      MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j:=
  markedSampleArcEmbedding f π ρ hf P (3*d) (rawMarkedRestrictHubs g σ) j

theorem markedRestrictedSampleArcEmbedding_range
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Gamma Color) (j:Bool):
    Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j)=
      Finset.univ.filter (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j=>
        e.val.1∈Finset.univ.image f∧e.val.2∈Finset.univ.image f):=by
  ext e
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.1,rfl⟩,⟨a.val.2,rfl⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    have he:markedPhysicalRim (P.comap f) ρ (3*d)
        (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) j x y=1:=by
      apply (markedPhysicalRim_orderEmbedding f π ρ hf P (3*d) (fun e=>σ (Sum.inl e)) j x y).mpr
      simpa only [hx,hy] using e.property
    refine ⟨⟨(x,y),he⟩,?_⟩
    exact Subtype.ext (Prod.ext hx hy)

end Oberwolfach
