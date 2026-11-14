module

public import Oberwolfach.LongSelectedSelectorLoadMargins
public import Oberwolfach.MarkedSelectedLevelMatchingScales

@[expose] public section
/-! The numerical assumptions of the actual-host selector follow from the
selected level margins at the very same reference scale. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach

theorem long_host_selected_selector_margins
    (r k₀:ℕ) (αHost ρ₀ ρ tstar kstar βA βCommon βrec κ κinner εref:ℝ)
    (δ ε thetaDeep η xiDeep omegaInner hIcut x epsBal ζBal etaBal deltaI:ℝ)
    (ht:tstar=(1/100:ℝ)/(((r+4):ℕ):ℝ)) (hρ:ρ₀≤ρ)
    (hGap:∀rho t:ℝ,ρ₀≤rho→tstar≤t→(1+2/rho)*xiDeep≤t*omegaInner/32)
    (hβA:βA≤βCommon) (hrec:βrec≤βA) (hδκ:δ≤κ/4)
    (hCycle:3*βA≤markedLocalCycleCoefficient r (αHost/2) (tstar/2) kstar-(r+5:ℕ)*δ)
    (hPath:3*βA≤markedLocalPathCoefficient r (αHost/2) (tstar/2) kstar-(r+4:ℕ)*δ)
    (hEndpoint:δ+(r+12:ℕ)*δ≤κ/4) (hEndpointX:δ+(r+12:ℕ)*δ≤x/2)
    (hεref:εref=κinner/4) (hκinner:κinner≤κ)
    (hParent:δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*tstar/2)^(2*(r+4)+1))*δ≤κ/4)
    (hDeep:δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*tstar/2)^(2*(r+4)+1))*δ≤thetaDeep/4)
    (hLocal:δ+δ+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*tstar/2)^(2*(r+4)+1))*(4/ε)*δ≤η/4)
    (hRow:δ+δ≤tstar/8) (hCut:2*hIcut≤tstar/8-δ)
    (hBal:epsBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hBalX:epsBal+((r+4)+2:ℕ)*ζBal≤x/2)
    (hδα:deltaI≤(αHost/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(αHost/2)*kstar/4):
    (1+2/ρ)*xiDeep≤((1/100:ℝ)/(((r+4):ℕ):ℝ))*omegaInner/32 ∧
    βA≤βCommon ∧ δ≤κ/4 ∧
    3*βA≤markedLocalCycleCoefficient r (αHost/2) (tstar/2) kstar-(r+5:ℕ)*δ ∧
    3*βA≤markedLocalPathCoefficient r (αHost/2) (tstar/2) kstar-(r+4:ℕ)*δ ∧
    βrec≤βA ∧ δ+(r+12:ℕ)*δ≤κ/4 ∧ δ≤κ/4 ∧ εref≤κ/4 ∧
    δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*(1/100)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ≤κ/4 ∧
    δ+δ+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*(1/100)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ≤thetaDeep/4 ∧
    epsBal+((r+4)+2:ℕ)*ζBal≤etaBal ∧ epsBal+((r+4)+2:ℕ)*ζBal≤x/2 ∧
    δ+δ≤((1/100:ℝ)/((r+4:ℕ):ℝ))/8 ∧
    δ+δ+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αHost/4)/(ρ₀*(1/100)/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*δ≤η/4 ∧
    deltaI≤(αHost/2)/32 ∧ deltaI≤kstar/32 ∧ 2*deltaI≤tstar/8 ∧
    2*hIcut≤(αHost/2)*kstar/4 ∧ 2*hIcut≤tstar/8-δ ∧
    δ+(r+12:ℕ)*δ≤x/2 := by
  obtain ⟨hg,hp,hd,hl,hr,hc⟩ := long_selected_selector_load_margins r ρ₀ ρ (1/100) tstar
    (successorWeightUpper k₀ (αHost/4)) δ ε κ thetaDeep η xiDeep omegaInner hIcut
    ht hρ hGap hParent hDeep hLocal hRow hCut
  have he:εref≤κ/4 := by rw [hεref]; linarith
  exact ⟨hg,hβA,hδκ,hCycle,hPath,hrec,hEndpoint,hδκ,he,hp,hd,hBal,hBalX,hr,hl,
    hδα,hδstar,hδt,hhstar,hc,hEndpointX⟩
end Oberwolfach
