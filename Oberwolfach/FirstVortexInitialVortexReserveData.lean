module

public import Oberwolfach.FirstVortexInitialVortexReserveHierarchy

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def FirstVortexInitialVortexReserveData (αRef ρ₀:ℝ):Prop :=
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      (∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n) ∧
    ∀δglobal εLevel εInner εAbs εRob γRich kstar tstar:ℝ,
      0<δglobal→0<εLevel→0<εInner→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→
    ∃bmatch α ε:ℝ,0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<α ∧ (2*α)/16≤bmatch ∧ 2*α≤4*δglobal ∧
      0<ε ∧ ε<1/4 ∧ ε≤εLevel ∧ ε≤εInner ∧ ε≤εAbs ∧ ε≤εRob ∧ ε≤βList/32 ∧
      ε≤min ((γRich/2)*kstar) tstar/128 ∧ ε≤(2*α)/100000 ∧
      ε≤α/1000 ∧ ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧
      ε≤δglobal ∧ βfinal+ε≤βList
end Oberwolfach
