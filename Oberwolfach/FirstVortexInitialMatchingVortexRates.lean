module

public import Oberwolfach.FirstVortexInitialMatchingVortexChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexInitialMatchingVortexRates
    (ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar hostCap bmatch α ε:ℝ):Prop :=
    0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<α ∧ (2*α)/16≤bmatch ∧ 2*α≤4*δglobal ∧
      0<ε ∧ ε<1/4 ∧ ε≤εLevel ∧ ε≤εInner ∧ ε≤εAbs ∧ ε≤εRob ∧ ε≤hostCap ∧
      ε≤min ((γRich/2)*kstar) tstar/128 ∧ ε≤(2*α)/100000 ∧
      ε≤α/1000 ∧ ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧
      ε≤δglobal ∧ βfinal+ε≤βList
end Oberwolfach
