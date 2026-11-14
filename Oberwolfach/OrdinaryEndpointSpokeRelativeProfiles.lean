module

public import Oberwolfach.OrdinaryCleanupEndpointSpokeProfiles
public import Oberwolfach.OrdinaryCleanupSpokeCodegrees
public import Oberwolfach.OrdinaryEndpointRelativeCountArithmetic

@[expose] public section
/-! At an actual boundary endpoint, the spoke degrees and codegrees have
    the relative targets required by the same-sample pairing construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_spoke_relative_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ):
    (∀x v,Q.Adj x v→
      |((B.filter (fun u=>H x u∧H v u)).card:ℝ)-pH*(B.filter (H x)).card|≤
        (tH+2*L)+pH*(tH+L)) ∧
    (∀x v w,Q.Adj x v→Q.Adj x w→v≠w→¬F.Adj v w→
      |((B.filter (fun u=>H x u∧H v u∧H w u)).card:ℝ)-pH^2*(B.filter (H x)).card|≤
        (tH+3*L)+pH^2*(tH+L)):=by
  have hs:=ordinary_cleanup_spoke_degrees_and_codegrees P Q F H π d A B pR pH density tR tH L βe βh s j σ profile
  have hpair:=ordinary_cleanup_endpoint_spoke_profiles P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  constructor
  · intro x v hxv
    have hfree:¬F.Adj x v:=fun hf=>(disjoint_iff_inf_le.mp profile.forbidden_disjoint) ⟨hxv,hf⟩
    have hh:=hpair.1 x v (Q.ne_of_adj hxv) hfree
    have hY:|((B.filter (fun u=>H x u∧H v u)).card:ℝ)-pH*(pH*B.card)|≤tH+2*L:=by
      convert hh using 1 <;> ring
    exact ordinary_relative_count_from_common_centre _ _ (pH*B.card) pH (tH+L) (tH+2*L)
      profile.spoke_nonneg (hs.1 x) hY
  · intro x v w hxv hxw hvw hvwF
    have hxvF:¬F.Adj x v:=fun hf=>(disjoint_iff_inf_le.mp profile.forbidden_disjoint) ⟨hxv,hf⟩
    have hxwF:¬F.Adj x w:=fun hf=>(disjoint_iff_inf_le.mp profile.forbidden_disjoint) ⟨hxw,hf⟩
    have hh:=hpair.2 x v w (Q.ne_of_adj hxv) (Q.ne_of_adj hxw) hvw hxvF hxwF hvwF
    have hY:|((B.filter (fun u=>H x u∧H v u∧H w u)).card:ℝ)-pH^2*(pH*B.card)|≤tH+3*L:=by
      convert hh using 1 <;> ring
    exact ordinary_relative_count_from_common_centre _ _ (pH*B.card) (pH^2) (tH+L) (tH+3*L)
      (sq_nonneg pH) (hs.1 x) hY
end Oberwolfach
