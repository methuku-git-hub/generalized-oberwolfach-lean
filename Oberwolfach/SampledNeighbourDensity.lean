module

public import Oberwolfach.RawIntervalNeighbourCounts

@[expose] public section

/-! Numerical margins converting simultaneous all-root counts into dense
random common neighbourhoods. The root need not belong to the sampled set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem sampled_neighbour_density (n p θ α t size deg count : ℝ)
    (hn : 0≤n) (hp : 0≤p) (hα : 0<α) (hθ : 0≤θ+α/2) (hθ1 : θ+α/2≤1)
    (ht : 0≤t) (htsize : t≤p*n/2) (htmargin : t≤α*p*n/4)
    (hsize : |size-p*n|≤t) (hdeg : (θ+α)*n≤deg)
    (hcount : |count-p*deg|≤t) :
    p*n/2≤size ∧ (θ+α/2)*size≤count := by
  have hlo := (abs_le.mp hsize).1
  have hhi := (abs_le.mp hsize).2
  have hclo := (abs_le.mp hcount).1
  have hd := mul_le_mul_of_nonneg_left hdeg hp
  have hs := mul_le_mul_of_nonneg_left (show size≤p*n+t by linarith only [hhi]) hθ
  have hterr := mul_le_mul_of_nonneg_right hθ1 ht
  constructor
  · linarith only [hlo,htsize]
  · nlinarith only [hs,hclo,hd,hterr,htmargin]

end Oberwolfach
