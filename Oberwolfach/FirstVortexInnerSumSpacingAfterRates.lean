module

public import Oberwolfach.FirstVortexLateSpacingStrictChoice
public import Oberwolfach.FirstVortexAllHubBoundaryEventually

@[expose] public section
/-! Choose the matching spacing after the local rates and absorb the
actual all-hub boundary error at a later host threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_spacing_after_rates
    (r:ℕ) (s θcap ε active:ℝ) (hs:0<s) (hθcap:0<θcap) (hε:0<ε) (hactive:0<active):
    ∃θ:ℝ,0<θ ∧ θ≤s ∧ θ≤θcap ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
      (∃N:ℕ,∀n:ℕ,N≤n→∀u:ℕ,u≤n→4*(u:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)≤s*n) ∧
      ∃KMin:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
        5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 :=by
  let θ:=min (s/2) (θcap/2)
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθs:θ≤s:=by dsimp [θ];have hh:=min_le_left (s/2) (θcap/2);linarith
  have hθcap':θ≤θcap:=by dsimp [θ];have hh:=min_le_right (s/2) (θcap/2);linarith
  obtain ⟨dMin,hd⟩:=first_vortex_late_spacing_and_class_strict_choice r θ ε active s hθ hε hactive hs
  refine ⟨θ,hθ,hθs,hθcap',dMin,?_⟩
  intro d hdmin
  obtain ⟨hd3,hdr,hθspace,haspace,hboundary,hcut,KMin,hK⟩:=hd d hdmin
  have hd0:0<d:=by omega
  obtain ⟨N,hN⟩:=first_vortex_all_hub_boundary_eventually d s hd0 hs hboundary
  exact ⟨hd3,hdr,hθspace,haspace,hcut,⟨N,hN⟩,KMin,hK⟩
end Oberwolfach
