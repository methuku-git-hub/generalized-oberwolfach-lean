module

public import Oberwolfach.LongOriginalBasicInputs

@[expose] public section
/-! The original density and regularity assumptions imply the index family
has at most n members, with no separate size assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem original_regular_host_factor_count
    {n D q:ℕ} (hn:0<n) (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D)
    (θ α:ℝ) (hθ:1/2≤θ) (hα:0<α) (hdegree:(θ+α)*(n:ℝ)≤D)
    (hρhi:2*(q:ℝ)/(D:ℝ)≤1):0<D ∧ 2*q≤D ∧ q≤n :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hDreal:0<(D:ℝ):=(mul_pos (by linarith : 0<θ+α) hnR).trans_le hdegree
  have hD:0<D:=by exact_mod_cast hDreal
  have h2qR:2*(q:ℝ)≤D:=(div_le_one hDreal).mp hρhi
  have h2q:2*q≤D:=by exact_mod_cast h2qR
  let v:Fin n:=⟨0,hn⟩
  have hDn:D≤n:=by
    have hh:=P.degree_lt_card_verts v
    rw [hP v] at hh
    simpa only [Fintype.card_fin] using hh.le
  exact ⟨hD,h2q,by omega⟩
end Oberwolfach
