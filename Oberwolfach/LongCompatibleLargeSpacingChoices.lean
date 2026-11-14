module

public import Oberwolfach.LongManuscriptMatchingParameters

@[expose] public section
/-! A compatible auxiliary choice: fix spacing before the length cutoff and
then choose the matching error and coverage tolerance below it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem long_compatible_large_spacing_choices
    (m dMin:ℕ) (θ lam:ℝ) (hθ:0<θ) (hlam:0<lam):
    ∃d:ℕ,3≤d ∧ dMin≤d ∧ 1/(d:ℝ)≤θ/1024 ∧
      (1/((m:ℝ)+1))/(d:ℝ)≤θ ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)≤θ/4 ∧
      ∀K:ℕ,3≤K→
        ∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
          0<γ ∧ γ≤eps ∧ γ≤1/2 ∧ γ≤lam/(10*(d:ℝ)) ∧ γ≤lam/10 ∧
          (4*((m:ℝ)+1)*(d:ℝ)/θ≤K→
            5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/K≤θ/2):=by
  obtain ⟨D,hD⟩:=exists_nat_gt (max (1024/θ) (dMin:ℝ))
  let d:=max D 3
  have hd:3≤d:=le_max_right _ _
  have hdMin:dMin≤d:=by
    have hh:(dMin:ℝ)<D:=lt_of_le_of_lt (le_max_right _ _) hD
    have hh':dMin≤D:=by exact_mod_cast hh.le
    exact hh'.trans (le_max_left _ _)
  have hlarge:1024/θ<(d:ℝ):=by
    have hh:1024/θ<(D:ℝ):=lt_of_le_of_lt (le_max_left _ _) hD
    have hh':(D:ℝ)≤d:=by exact_mod_cast (le_max_left D 3)
    exact hh.trans_le hh' 
  have hdR:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hc:(1:ℝ)≤(m:ℝ)+1:=by have hm:(0:ℝ)≤m:=Nat.cast_nonneg _;linarith
  have hD':20/θ<(d:ℝ):=by
    have hh:20/θ≤1024/θ:=div_le_div_of_nonneg_right (by norm_num) hθ.le
    exact lt_of_le_of_lt hh hlarge
  have hbig:20<θ*d:=by simpa only [mul_comm] using (div_lt_iff₀ hθ).1 hD'
  have hprod:(d:ℝ)≤((m:ℝ)+1)*d:=by nlinarith
  have hspace:(1/((m:ℝ)+1))/(d:ℝ)≤θ:=by
    apply (div_le_iff₀ hdR).2
    have : (1:ℝ)/((m:ℝ)+1)≤1:=by
      apply (div_le_one (by positivity : (0:ℝ)<(m:ℝ)+1)).2
      linarith
    nlinarith
  have hbuffer:5/(((m:ℝ)+1)*(d:ℝ)+5)≤θ/4:=by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<((m:ℝ)+1)*d+5)).2
    nlinarith
  have hinv:1/(d:ℝ)≤θ/1024:=by
    apply (div_le_iff₀ hdR).2
    have hh:1024≤(d:ℝ)*θ:=(div_le_iff₀ hθ).1 hlarge.le
    nlinarith
  refine ⟨d,hd,hdMin,hinv,hspace,hbuffer,?_⟩
  intro K hK
  have hKR:(0:ℝ)<K:=by exact_mod_cast (show 0<K by omega)
  let eps:ℝ:=min (1/2) (lam*θ/(600*(K:ℝ)^2))
  have heps:0<eps:=lt_min (by norm_num) (by positivity)
  have heps1:eps≤1:=by have hh:=min_le_left (1/2:ℝ) (lam*θ/(600*(K:ℝ)^2));dsimp [eps];linarith
  have hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:eps≤lam*θ/(600*(K:ℝ)^2):=min_le_right _ _
    have heq:lam*(θ/(100*(K:ℝ)^2))=6*(lam*θ/(600*(K:ℝ)^2)):=by ring
    rw [heq]
    have hp:0≤lam*θ/(600*(K:ℝ)^2):=by positivity
    linarith
  let γ:ℝ:=min (eps/2) (min (1/2) (min (lam/(10*(d:ℝ))) (lam/10)))
  have hγ:0<γ:=lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  have hγeps:γ≤eps:=by have hh:=min_le_left (eps/2) (min (1/2) (min (lam/(10*(d:ℝ))) (lam/10)));dsimp [γ];linarith
  have hγhalf:γ≤1/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hγd:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγlam:γ≤lam/10:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨eps,γ,heps,heps1,hepsAssign,hγ,hγeps,hγhalf,hγd,hγlam,?_⟩
  intro hKlarge
  have hbound:((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/4:=by
    apply (div_le_iff₀ hKR).2
    have hh:4*((m:ℝ)+1)*(d:ℝ)≤(K:ℝ)*θ:=(div_le_iff₀ hθ).1 hKlarge
    nlinarith
  linarith
end Oberwolfach
