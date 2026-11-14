module

public import Oberwolfach.LongUnusedSpokeLocalIncidence
public import Oberwolfach.FiniteResourceFibreBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_true_spoke_defect_count_le_local_incidence
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (C:Finset S) (H:Finset U) (v:Fin n):
    ((H.filter (fun w=>∃z∈longRawIncidenceSet S (.inr (true,.inl v))\C,
      z.1=Sum.inr (true,v,w))).card:ℝ) ≤
    ((longLocalVertexSpokeDefects S C true v H).card:ℝ):=by
  have hh:=finite_resource_fibre_card_le S (longLocalVertexSpokeDefects S C true v H) H
    (fun w=>Sum.inr (true,v,w)) (by intro x y h;simpa using h)
  have heq:H.filter (fun w=>∃z∈longRawIncidenceSet S (.inr (true,.inl v))\C,
      z.1=Sum.inr (true,v,w)) = H.filter (fun w=>∃z∈longLocalVertexSpokeDefects S C true v H,
      z.1=Sum.inr (true,v,w)):=by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw,z,hz,hzval⟩
      exact ⟨hw,z,Finset.mem_filter.mpr ⟨hz,⟨w,hw,hzval⟩⟩,hzval⟩
    · rintro ⟨hw,z,hz,hzval⟩
      exact ⟨hw,z,(Finset.mem_filter.mp hz).1,hzval⟩
  rw [heq]
  exact_mod_cast hh
end Oberwolfach
