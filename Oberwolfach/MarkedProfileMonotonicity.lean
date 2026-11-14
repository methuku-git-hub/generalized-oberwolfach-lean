module

public import Oberwolfach.MarkedCommonPairCycleProfiles
public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! Decreasing explicit lower bounds preserves the same graphs, classes,
coefficient functions and root domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

def MarkedCommonPairCycleProfiles.lowerDensity {q₀ q₁ β blo bhi ε:ℝ}
    (Q:MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₁ β blo bhi ε) (hq:q₀≤q₁):
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε:=
  {Q with q_lower:=fun u u' h=>hq.trans (Q.q_lower u u' h)}

theorem MarkedHostExtensionCounts.lowerBounds {c c' h h':ℝ}
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c h) (hc:c'≤c) (hh:h'≤h):
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c' h' where
  outgoing j k x P hP:=hc.trans (Q.outgoing j k x P hP)
  incoming j k x P hP:=hc.trans (Q.incoming j k x P hP)
  twoOutgoing k x y P hxy hP:=hc.trans (Q.twoOutgoing k x y P hxy hP)
  twoIncoming j k x y P hxy hP:=hc.trans (Q.twoIncoming j k x y P hxy hP)
  twoStep k x y P hxy hP:=hc.trans (Q.twoStep k x y P hxy hP)
  hubs A B hd hs hp:=hh.trans (Q.hubs A B hd hs hp)

end Oberwolfach
