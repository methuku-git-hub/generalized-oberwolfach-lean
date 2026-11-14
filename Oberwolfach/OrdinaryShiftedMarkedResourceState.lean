module

public import Oberwolfach.RawMarkedPotentialSampling

@[expose] public section
/-! Ordinary preparation uses the same physical edge state for both
ordinary and shifted closing arcs. Their geometry remains distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def ordinaryShiftedPairRims (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color):(V×V)⊕(V×V)→Prop :=
  Sum.elim
    (fun xy=>¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 xy.2 ∧
      σ (Sum.inl s(xy.1,xy.2))=some (false,orientationBit xy.1 xy.2))
    (fun xy=>¬PermutationClose π (3*d) xy.1 xy.2 ∧ P.Adj xy.1 (π xy.2) ∧
      σ (Sum.inl s(xy.1,π xy.2))=some (false,orientationBit xy.1 (π xy.2)))

theorem ordinary_shifted_resource_state_supported (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (g:Γ) (j:Color) (a:((V×V)⊕(V×V))⊕(Bool×V×U))
    (σ τ:RawMarkedOutcome V U Γ Color)
    (ha:∀e∈rawMarkedResourceCoordinates π d a,σ e=τ e):
    Sum.elim (ordinaryShiftedPairRims P π d σ) (fun jvu=>rawMarkedPairSpokes π d σ g j jvu.1 jvu.2.1 jvu.2.2) a ↔
      Sum.elim (ordinaryShiftedPairRims P π d τ) (fun jvu=>rawMarkedPairSpokes π d τ g j jvu.1 jvu.2.1 jvu.2.2) a :=by
  cases a with
  | inl a=>
    have hh:=ha (Sum.inl (markedPairPhysical π a)) (Finset.mem_singleton_self _)
    cases a with
    | inl xy=>
      change σ (Sum.inl s(xy.1,xy.2))=τ (Sum.inl s(xy.1,xy.2)) at hh
      simp only [ordinaryShiftedPairRims,Sum.elim_inl,hh]
    | inr xy=>
      change σ (Sum.inl s(xy.1,π xy.2))=τ (Sum.inl s(xy.1,π xy.2)) at hh
      simp only [ordinaryShiftedPairRims,Sum.elim_inl,Sum.elim_inr,hh]
  | inr a=>
    have hh:=rawIntervalFamilyState_supported π d (fun e=>σ (Sum.inr e))
      (fun e=>τ (Sum.inr e)) a.2 (by
        intro e he
        exact ha (Sum.inr e) (Finset.mem_image.mpr ⟨e,he,rfl⟩))
    obtain ⟨a,v,u⟩:=a
    cases a <;> simpa only [Sum.elim_inr,rawMarkedPairSpokes,rawMarkedSpokes,hh]
end Oberwolfach
