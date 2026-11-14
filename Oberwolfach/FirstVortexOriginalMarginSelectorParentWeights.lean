module

public import Oberwolfach.FirstVortexOriginalMarginSelectorHostGeometry
public import Oberwolfach.FirstVortexSharedVortexTailParentWeights

@[expose] public section
/-! The original degree margin supplies the selector on the actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_original_margin_selector_parent_weights
    (α:ℝ) (hα:0<α):
    ∃ (αRef κL ρ₀:ℝ) (href:0<αRef) (hρ:0<ρ₀), 2*αRef≤1 ∧ 2*αRef≤α/2 ∧
      0<κL ∧ κL≤α/1000 ∧ ρ₀≤1 ∧ ρ₀≤2*κL ∧
      (∀δ D:ℝ,∀n:ℕ,(δ+α/2)*(n:ℝ)≤D→(δ+2*αRef)*(n:ℝ)≤D) ∧
    ∀L₀:ℕ,
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→
        ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
      ∃(hm':7≤r+4) (htstar:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ)),
      FirstVortexSharedVortexTailParentWeights r k₀ αRef ρ₀ href hρ hm' htstar :=by
  obtain ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρκ,hmargin,hHost⟩:=
    first_vortex_original_margin_selector_host_geometry α hα
  refine ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρκ,hmargin,?_⟩
  intro L₀ βList
  obtain ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hTail⟩:=hHost L₀
  have hm':7≤r+4:=by omega
  have hmreal:(0:ℝ)≤(((r+4):ℕ):ℝ):=by positivity
  have htstar:1/(200*((r+4:ℕ):ℝ))≤(1/100)/(((r+4):ℕ):ℝ):=by
    have hh:=div_le_div_of_nonneg_right (show (1:ℝ)/200≤1/100 by norm_num) hmreal
    convert hh using 1 <;> ring
  refine ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hm',htstar,?_⟩
  exact first_vortex_shared_vortex_parent_weights r k₀ αRef ρ₀ href hρ hm' htstar (first_vortex_shared_vortex_actual_matching r k₀ αRef ρ₀ href hρ hm' htstar (first_vortex_shared_vortex_parent_ready r k₀ αRef ρ₀ href hρ hm' htstar (first_vortex_shared_vortex_chain_ready r k₀ αRef ρ₀ href hρ hm' htstar hρone (first_vortex_shared_vortex_applied_selector r k₀ αRef ρ₀ href hρ hm' htstar (first_vortex_shared_vortex_numeric_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_caller_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_selected_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_explicit_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_level_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_transfer_ready r k₀ αRef ρ₀ href hρ (first_vortex_shared_vortex_late_threshold r k₀ αRef ρ₀ href hρ hTail)))))))))))
end Oberwolfach
