module

public import Oberwolfach.MarkedCommonPairCycleProfiles

@[expose] public section

/-! Increasing only the allowed error retains exactly the same classes,
densities and coefficient functions on the original cycle domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {q₀ β blo bhi ε ε':ℝ}

def MarkedCommonPairCycleProfiles.mono_error
    (P:MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε) (he:ε≤ε'):
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε':=by
  have hen:ε*Fintype.card V≤ε'*Fintype.card V:=mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
  exact {
    A:=P.A
    B:=P.B
    q:=P.q
    w:=P.w
    q_lower:=P.q_lower
    marked_class:=P.marked_class
    ordinary_class:=P.ordinary_class
    marked_size:=fun u u' h=>(P.marked_size u u' h).trans hen
    ordinary_size:=fun u u' h=>(P.ordinary_size u u' h).trans hen
    overlap:=fun u u' h=>(P.overlap u u' h).trans hen
    cycles:=P.cycles
    paths:=P.paths
    weight_bounds:=P.weight_bounds
    root_loads:=fun u u' h j v=>(P.root_loads u u' h j v).trans he}

end Oberwolfach
