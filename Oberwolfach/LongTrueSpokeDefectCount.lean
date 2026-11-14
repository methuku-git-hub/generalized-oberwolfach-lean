module

public import Oberwolfach.FiniteResourceFibreBound
public import Oberwolfach.LongRawIncidenceFamily

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance LongTrueSpokeDefectCountFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_true_spoke_defect_count_le_incidence
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U))
    (C:Finset {r // r∈S}) (H:Finset U) (v:Fin n):
    ((H.filter (fun w=>∃z∈longRawIncidenceSet S (.inr (true,.inl v))\C,
      z.1=Sum.inr (true,v,w))).card:ℝ) ≤
    ((longRawIncidenceSet S (.inr (true,.inl v))\C).card:ℝ):=by
  have hh:=finite_resource_fibre_card_le S (longRawIncidenceSet S (.inr (true,.inl v))\C) H
    (fun w=>Sum.inr (true,v,w)) (by intro x y h;simpa using h)
  exact_mod_cast hh
end Oberwolfach
