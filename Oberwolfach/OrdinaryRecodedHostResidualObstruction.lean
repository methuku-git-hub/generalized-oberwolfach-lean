module

public import Oberwolfach.OrdinaryRecodedListResidualObstruction

@[expose] public section
/-! A feasible original host automatically supplies the slack bound used in
the incompatibility audit of the unassigned-list route. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_recoded_residual_host_obstruction
    {n:ℕ} (hn:0<n) (P:SimpleGraph (Fin n)) (θ γ pstar β lam ζ δ d:ℝ)
    (hθ:0<θ) (hθ1:θ≤1) (hγ:0≤γ)
    (hP:∀x,(1/2+γ)*n≤(P.degree x:ℝ)) (hp:0≤pstar) (hp1:pstar≤1)
    (hlam:0≤lam) (hζ:0≤ζ) (hd:0<d)
    (hlist:β*n+(n:ℝ)^(3/4:ℝ)≤(γ*pstar^2)*n*(θ/2))
    (hmarg:(lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n)
    (hresidual:2*θ≤δ) (hplacement:δ≤(lam/100)^2):False :=by
  let x:Fin n:=⟨0,hn⟩
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hdeg:(P.degree x:ℝ)<n:=by
    have hh:=P.degree_lt_card_verts x
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hγ1:γ≤1:=by
    by_contra hh
    have hh':1<γ:=lt_of_not_ge hh
    have hm:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤1/2+γ by linarith) hnR.le
    have hp':=(hP x)
    linarith
  exact ordinary_recoded_list_residual_obstruction θ γ pstar β lam ζ δ n d hθ hθ1 hγ hγ1 hp hp1 hlam hζ hnR hd hlist hmarg hresidual hplacement
end Oberwolfach
