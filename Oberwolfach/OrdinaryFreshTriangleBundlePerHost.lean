module

public import Oberwolfach.OrdinaryFreshTrianglePerHost
public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside

@[expose] public section
/-! After the original outcome is fixed, every admissible cleanup parent
    can choose its own fresh auxiliary sample. No union over parents is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_triangle_bundle_for_each_cleanup_parent
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1)
      (εres εsup βe βh:ℝ) (hres:0<εres) (hsup:0<εsup) (hβe:0<βe) (hβh:0<βh),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P Q₀ F:SimpleGraph V) (H₀:V→U→Prop) (X:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
      (pR pH density tR tH Ledit:ℝ),
    let Q:=spanningRestriction Q₀ X;
    let H:=fun v u=>H₀ v u ∧ v∈X ∧ u∈Z;
    OrdinaryCleanupParentProfiles P Q₀ F H₀ π d X Z pR pH density tR tH Ledit βe βh s j raw→
    Nonempty (MixedFreshParentDataInsideRoots γ κ b B ε η Q F
      (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr))→
    ∃data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F
      (ordinaryPhysicalGraph Q H) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H₀ Z X)
      (fun i=>(ordinaryBoundaryRimSet Q₀ X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H₀ X Z i).image Sum.inr),
    ∃σ:Sym2 (V⊕U)→Bool,
      OrdinaryFreshTriangleBoundaryEventInside Q₀ Q F H₀ H X Z
        γ κ b B ε η ζ p εres εsup βe βh data σ :=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hmain⟩:=ordinary_fresh_triangle_for_each_cleanup_parent γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 εres εsup βe βh hres hsup hβe hβh
  obtain ⟨N,hN⟩:=hmain p hp hp1 (2*p) (by positivity) εres εsup βe βh hres hsup hβe hβh
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P Q₀ F H₀ X Z π d s j raw pR pH density tR tH Ledit Q H hprofile hparent
  obtain ⟨σ,hreserve,hsupport,⟨data,hfactors⟩,hext,hhub⟩:=
    hN V U Γ Color hn hu P Q₀ F H₀ X Z π d s j raw pR pH density tR tH Ledit hprofile hparent
  exact ⟨data,σ,⟨hreserve,hsupport,hfactors,hext,hhub⟩⟩
end Oberwolfach
