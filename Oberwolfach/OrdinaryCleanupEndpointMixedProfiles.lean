module

public import Oberwolfach.OrdinaryCleanupAbsoluteDomainCounts

@[expose] public section
/-! The actual rim-spoke intersection at an endpoint retains the exact
    sampled target up to the allowed rim and spoke edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_endpoint_mixed_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ):
    ∀x u,
      |((A.filter (fun v=>Q.Adj x v∧H v u)).card:ℝ)-
        pR*pH*(A∩P.neighborFinset x).card|≤tR+2*L:=by
  intro x u
  have hc:=ordinary_cleanup_absolute_domain_counts P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  have hh:=hc.1 {x} {u} (by simp) (by simp)
  have he:common (common A ({x}:Finset V) (fun v=>Q.neighborFinset v)) ({u}:Finset U)
      (fun u=>Finset.univ.filter (fun v=>H v u)) =
      A.filter (fun v=>Q.Adj x v∧H v u):=by
    ext v
    simp [mem_common_iff,SimpleGraph.mem_neighborFinset,and_assoc]
  have hp:common A ({x}:Finset V) (fun v=>P.neighborFinset v)=A∩P.neighborFinset x:=by
    ext v
    simp [mem_common_iff,SimpleGraph.mem_neighborFinset]
  rw [he,hp] at hh
  simp only [Finset.card_singleton,pow_one,Nat.cast_one,one_mul] at hh
  convert hh using 1 <;> ring
end Oberwolfach
