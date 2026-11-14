module

public import Oberwolfach.BipartiteCutChanges
public import Oberwolfach.ExponentialMarkedReferenceCuts

@[expose] public section

/-! The four reference cut conditions under changes of the spoke
relations. Physical rims and their cut coefficients remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedCutFamiliesWithSpokes (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (α p k tstar ζ : ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) : Prop :=
  (∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
    1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
    (tstar/8-ζ)*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
      (bipartiteMatrixCut (fun v u=>if H b v u then 1 else 0) X Y:ℝ)) ∧
  (∀ b : Bool,∀ δ : ℝ,δ≤α/32 → δ≤(if b then k else p)/32 → ∀ S T : Finset V,
    (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
    (α*(if b then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
      (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) b) S T:ℝ))

theorem markedCutFamilies_spoke_changes (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (a : Γ) (j : Color) (α p k tstar ζ : ℝ) (hζ : 0≤ζ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hc : MarkedReferenceCutFamilies P π d a j α p k tstar σ)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card U)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤ζ*Fintype.card V) :
    MarkedCutFamiliesWithSpokes P π d α p k tstar ζ σ H := by
  refine ⟨?_,hc.2⟩
  intro b S T hlarge
  exact bipartite_cut_lower_after_changes (rawMarkedPairSpokes π d σ a j b) (H b)
    ζ hζ (hrow b) (hcol b) (tstar/8) S T (hc.1 b S T hlarge)

end Oberwolfach
