module

public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.MarkedRowCommonEvent

@[expose] public section

/-! Deterministic deletion of physical rim edges from the original outcome.
The retained states keep their original orientation and type, and all
interval/spoke coordinates are unchanged. No new sampling law is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def rawMarkedDeleteRims (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V)):
    RawMarkedOutcome V U Γ Color
  | Sum.inl e=>if e∈D then none else σ (Sum.inl e)
  | Sum.inr e=>σ (Sum.inr e)

theorem rawMarkedDeleteRims_spokes
    (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (D:Finset (Sym2 V))
    (g:Γ) (j:Color) (a:Bool) (v:V) (u:U):
    rawMarkedPairSpokes π d (rawMarkedDeleteRims σ D) g j a v u↔rawMarkedPairSpokes π d σ g j a v u:=Iff.rfl

theorem rawMarkedDeleteRims_rims
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (a:(V×V)⊕(V×V)):
    rawMarkedPairRims P π d (rawMarkedDeleteRims σ D) a↔
      rawMarkedPairRims P π d σ a∧markedPairPhysical π a∉D:=by
  cases a with
  | inl a=>
    by_cases hd:s(a.1,a.2)∈D
    · simp [rawMarkedPairRims,markedPhysicalRim,permutationSeparatedMatrix,
        markedPhysicalOrientation,rawMarkedDeleteRims,markedPairPhysical,hd]
    · simp [rawMarkedPairRims,markedPhysicalRim,permutationSeparatedMatrix,
        markedPhysicalOrientation,rawMarkedDeleteRims,markedPairPhysical,hd]
  | inr a=>
    by_cases hd:s(a.1,π a.2)∈D
    · simp [rawMarkedPairRims,markedPhysicalRim,permutationSeparatedMatrix,
        markedPhysicalOrientation,rawMarkedDeleteRims,markedPairPhysical,hd]
    · simp [rawMarkedPairRims,markedPhysicalRim,permutationSeparatedMatrix,
        markedPhysicalOrientation,rawMarkedDeleteRims,markedPairPhysical,hd]

end Oberwolfach
