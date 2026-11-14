module

public import Oberwolfach.OrdinaryMixedOtherParentInputs

@[expose] public section
/-! A proper spanning restriction cannot satisfy a positive common-neighbor
bound quantified over all ambient roots. This records the host mismatch in
the earlier conditional mixed-parent assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_restricted_host_global_common_obstruction (Q:SimpleGraph V) (A T:Finset V)
    (γ:ℝ) (hγ:0<γ) (hn:0<Fintype.card V) (x:V) (hx:x∉A):
    ¬(∀S:Finset V,S.card≤3→γ*Fintype.card V≤
      ((common T S (fun v=>(spanningRestriction Q A).neighborFinset v)).card:ℝ)):=by
  intro h
  have he:common T {x} (fun v=>(spanningRestriction Q A).neighborFinset v)=∅:=by
    ext v
    simp [common,SimpleGraph.mem_neighborFinset,spanningRestriction_adj,hx]
  have hh:=h {x} (by simp)
  rw [he] at hh
  have hn':(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  have hp:=mul_pos hγ hn'
  have hz:γ*Fintype.card V≤0:=by simpa using hh
  exact not_le_of_gt hp hz
end Oberwolfach
