module

public import Oberwolfach.LongTrueSpokeDefectCount
public import Oberwolfach.LongRawIncidenceSizes

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance LongTrueSpokeDefectFromMatchingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_true_spoke_defect_count_from_matching
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (C:Finset {r // r∈S}) (H:Finset U)
    (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\C).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card)):
    ∀v:Fin n,((H.filter (fun w=>∃z∈longRawIncidenceSet S (.inr (true,.inl v))\C,
      z.1=Sum.inr (true,v,w))).card:ℝ)≤max a γ*n:=by
  intro v
  have hIncNat: (longRawIncidenceSet S (.inr (true,.inl v))).card≤n:=
    (long_raw_vertex_spoke_incidence_card_le S true v).trans hu
  have hInc:((longRawIncidenceSet S (.inr (true,.inl v))).card:ℝ)≤n:=by exact_mod_cast hIncNat
  have hm:=hmatch (.inr (true,.inl v))
  have hγinc:γ*((longRawIncidenceSet S (.inr (true,.inl v))).card:ℝ)≤γ*n:=mul_le_mul_of_nonneg_left hInc hγ
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg n
  have ha:a*n≤max a γ*n:=mul_le_mul_of_nonneg_right (le_max_left a γ) hn
  have hg:γ*n≤max a γ*n:=mul_le_mul_of_nonneg_right (le_max_right a γ) hn
  exact (long_true_spoke_defect_count_le_incidence S C H v).trans (hm.trans (max_le ha (hγinc.trans hg)))
end Oberwolfach
