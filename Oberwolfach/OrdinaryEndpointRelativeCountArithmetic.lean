module

public import Oberwolfach.OrdinaryCleanupMarginHierarchy

@[expose] public section
/-! Convert sampled counts around a common deterministic centre into the
    relative row, column and codegree estimates needed for pairings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach

theorem ordinary_relative_count_from_common_centre
    (X Y c p eX eY:ℝ) (hp:0≤p) (hX:|X-c|≤eX) (hY:|Y-p*c|≤eY):
    |Y-p*X|≤eY+p*eX:=by
  have heq:p*c-p*X= -(p*(X-c)):=by ring
  have hdiff:|p*c-p*X|≤p*eX:=by
    rw [heq,abs_neg,abs_mul,abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left hX hp
  exact (abs_sub_le Y (p*c) (p*X)).trans (add_le_add hY hdiff)

theorem ordinary_relative_codegree_from_common_centre
    (X Y c p eX eY η:ℝ) (hX:|X-c|≤eX) (hY:|Y-p^2*c|≤eY)
    (hbudget:eY+p^2*eX≤η*X):
    Y≤(p^2+η)*X:=by
  have hrel:=ordinary_relative_count_from_common_centre X Y c (p^2) eX eY (sq_nonneg p) hX hY
  have hh:=(abs_le.mp hrel).2
  nlinarith only [hh,hbudget]
end Oberwolfach
