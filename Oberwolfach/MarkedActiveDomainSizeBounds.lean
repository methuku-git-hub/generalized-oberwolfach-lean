module

public import Oberwolfach.MarkedProtectedActiveReferenceStatistics

@[expose] public section

/-! The parent graph's degree hypotheses give the required active domain
ratios and degree-target range. Removing hubs changes the target by its
actual amount; no near-regularity assumption on a different graph is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [DecidableEq V]

theorem marked_active_domain_size_bounds
    (f:A↪V) (g:B↪U) (P:SimpleGraph V) (hA:0<Fintype.card A)
    (rho gamma omega eps:ℝ) (hrho:0<rho) (hrho1:rho≤1)
    (hg:0≤gamma) (ho:0≤omega) (hepsG:eps≤gamma/4) (heps1:eps≤1/4)
    (hdeg:∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))
    (hreg:∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)
    (hsize:(3/4:ℝ)*Fintype.card V≤Fintype.card A)
    (hubs:omega*Fintype.card V≤Fintype.card U)
    (hloseG:(Fintype.card U:ℝ)-Fintype.card B≤(gamma*rho/16)*Fintype.card V)
    (hloseO:(Fintype.card U:ℝ)-Fintype.card B≤(omega/2)*Fintype.card V):
    (Fintype.card A:ℝ)/2≤2*Fintype.card B/rho∧
    2*Fintype.card B/rho≤2*Fintype.card A∧
    (omega/2)*Fintype.card A≤Fintype.card B∧Fintype.card B≤Fintype.card A:=by
  have hn:(Fintype.card A:ℝ)≤Fintype.card V:=Nat.cast_le.mpr (Fintype.card_le_of_injective f f.injective)
  have hm:(Fintype.card B:ℝ)≤Fintype.card U:=Nat.cast_le.mpr (Fintype.card_le_of_injective g g.injective)
  have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hm0:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
  have ha0:(0:ℝ)≤Fintype.card A:=Nat.cast_nonneg _
  obtain ⟨x⟩:=Fintype.card_pos_iff.mp hA
  have hregx:=abs_le.mp (hreg (f x))
  have hdegx:=hdeg (f x)
  have hmax:(P.degree (f x):ℝ)≤Fintype.card V:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_univ (s:=P.neighborFinset (f x)))
  have heG:=mul_le_mul_of_nonneg_right hepsG hn0
  have he1:=mul_le_mul_of_nonneg_right heps1 hn0
  have hDlo:(1/2+gamma/4)*Fintype.card V≤2*Fintype.card U/rho:=by
    nlinarith only [hregx.2,hdegx,heG]
  have hDhi:2*Fintype.card U/rho≤(5/4:ℝ)*Fintype.card V:=by
    nlinarith only [hregx.1,hmax,he1]
  have hDlo':((1/2+gamma/4)*Fintype.card V)*rho≤2*Fintype.card U:=(le_div_iff₀ hrho).mp hDlo
  have hDhi':2*(Fintype.card U:ℝ)≤((5/4:ℝ)*Fintype.card V)*rho:=(div_le_iff₀ hrho).mp hDhi
  have hγrho:0≤gamma*rho*(Fintype.card V:ℝ):=by positivity
  have hnρ:=mul_le_mul_of_nonneg_right hn hrho.le
  have hmBound:(Fintype.card U:ℝ)≤(5/8:ℝ)*Fintype.card V:=by
    have hρ:=mul_le_mul_of_nonneg_left hrho1 (show 0≤(5/4:ℝ)*Fintype.card V by positivity)
    nlinarith only [hDhi',hρ]
  refine ⟨?_,?_,?_,?_⟩
  · apply (le_div_iff₀ hrho).mpr
    nlinarith only [hDlo',hloseG,hnρ,hγrho]
  · apply (div_le_iff₀ hrho).mpr
    have hs:=mul_le_mul_of_nonneg_right hsize hrho.le
    have hnrho:0≤(Fintype.card V:ℝ)*rho:=by positivity
    nlinarith only [hDhi',hm,hs,hnrho]
  · have hs:=mul_le_mul_of_nonneg_left hn (show 0≤omega/2 by positivity)
    linarith only [hs,hubs,hloseO]
  · exact_mod_cast (show (Fintype.card B:ℝ)≤Fintype.card A by linarith only [hm,hmBound,hsize,hn0])

end Oberwolfach
