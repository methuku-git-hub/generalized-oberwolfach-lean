module

public import Oberwolfach.MarkedPairProfileMonotonicity

@[expose] public section

/-! Choose one deletion fraction before the host and its later deletion.
The loss leaves positive common-cycle/path coefficients and the requested
profile error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem common_physical_profile_margins (r:ℕ) (K bc bp η:ℝ)
    (hK:0≤K) (hbc:0<bc) (hbp:0<bp) (hη:0<η) :
    ∃ ζ:ℝ,0<ζ ∧ η/2+2*ζ≤η ∧ η/2+20*K*ζ≤η ∧
      bc/2≤bc-3*(r+5:ℕ)*ζ ∧ bp/2≤bp-4*(r+5:ℕ)*ζ := by
  let ζ:=min (η/4) (min (η/(40*(K+1))) (min (bc/(6*(r+5:ℕ))) (bp/(8*(r+5:ℕ)))))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hz1:ζ≤η/4:=min_le_left _ _
  have hz2:ζ≤η/(40*(K+1)):=(min_le_right _ _).trans (min_le_left _ _)
  have hz3:ζ≤bc/(6*(r+5:ℕ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hz4:ζ≤bp/(8*(r+5:ℕ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h2:ζ*(40*(K+1))≤η:=(le_div_iff₀ (by positivity:0<40*(K+1))).mp hz2
  have h3:ζ*(6*(r+5:ℕ))≤bc:=(le_div_iff₀ (by positivity:0<6*((r+5:ℕ):ℝ))).mp hz3
  have h4:ζ*(8*(r+5:ℕ))≤bp:=(le_div_iff₀ (by positivity:0<8*((r+5:ℕ):ℝ))).mp hz4
  refine ⟨ζ,hζ,by linarith,?_,?_,?_⟩ <;> push_cast at * <;> nlinarith

variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V]
  {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

def MarkedCommonPairCycleProfiles.lowerCount {q₀ β β' blo bhi ε:ℝ}
    (P:MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε) (hβ:β'≤β):
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β' blo bhi ε :=
  {P with
    cycles:=fun u u' h=>(mul_le_mul_of_nonneg_right hβ (by positivity)).trans (P.cycles u u' h)
    paths:=fun u u' h j v v' hv=>(mul_le_mul_of_nonneg_right hβ (by positivity)).trans (P.paths u u' h j v v' hv)}

end Oberwolfach
