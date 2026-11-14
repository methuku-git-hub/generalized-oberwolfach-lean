module

public import Oberwolfach.MarkedEndpointBlockNumerics

@[expose] public section

/-! Choose the free-use cap and allowed fraction of processed roots before
the separation radius. Only the final order threshold depends on that
radius. These are the explicit budgets of the actual hub-and-row constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach

theorem marked_deep_row_numeric_budget
    (l:ℕ) (beta theta lam tau:ℝ) (hb:0<beta) (ht:0<theta) (hl:0<lam) (hta:0<tau):
    ∃ K:ℕ,0<K∧∃ eps:ℝ,0<eps∧∀ b:ℕ,∃ N:ℕ,1≤N∧∀ size:ℕ,N≤size→
    ∀ h n excluded S:ℕ,(h:ℝ)≤eps*size→(n:ℝ)≤eps*size→
      (excluded:ℝ)≤eps*size→S≤size→
      (2*h:ℕ)≤theta*(size:ℝ)∧
      (n*(K+4):ℕ)≤(n*(K+l+8):ℕ)∧
      (n*(l+4):ℕ)≤(n*(K+l+8):ℕ)∧
      (n*(K+l+8):ℕ)≤lam*(tau*size)∧
      (excluded:ℝ)+(S*(l+4):ℕ)/(K:ℝ)+(l+5)*(2*b+1)+8*(K+4:ℕ)+
        2*(n*(4*(K+4)):ℕ)+2*(n*(l+4):ℕ)+4*h<beta*size:=by
  obtain ⟨K,hK⟩:=exists_nat_gt (max 1 (4*(l+4:ℕ)/beta))
  have hKpos:0<K:=by exact_mod_cast (lt_of_le_of_lt (by positivity : (0:ℝ)≤1) ((le_max_left _ _).trans_lt hK))
  have hKr:0<(K:ℝ):=by exact_mod_cast hKpos
  have hsmall:(l+4:ℕ)/(K:ℝ)<beta/4:=by
    have hh:=((div_lt_iff₀ hb).mp ((le_max_right _ _).trans_lt hK))
    apply (div_lt_iff₀ hKr).mpr
    nlinarith only [hh]
  let C:ℝ:=1+8*(K+4:ℕ)+2*(l+4:ℕ)+4
  have hC:0<C:=by dsimp [C];positivity
  let cap:ℝ:=K+l+8
  have hcap:0<cap:=by dsimp [cap];positivity
  let eps:=min (theta/4) (min (lam*tau/(2*cap)) (beta/(4*C)))
  have heps:0<eps:=by dsimp [eps];positivity
  have hept:eps≤theta/4:=min_le_left _ _
  have hepc:eps≤lam*tau/(2*cap):=(min_le_right _ _).trans (min_le_left _ _)
  have hepb:eps≤beta/(4*C):=(min_le_right _ _).trans (min_le_right _ _)
  have hecap:eps*cap≤lam*tau/2:=by
    have hh:=(le_div_iff₀ (by positivity : 0<2*cap)).mp hepc
    nlinarith only [hh]
  have heC:eps*C≤beta/4:=by
    have hh:=(le_div_iff₀ (by positivity : 0<4*C)).mp hepb
    nlinarith only [hh]
  refine ⟨K,hKpos,eps,heps,?_⟩
  intro b
  let constant:ℝ:=(l+5:ℕ)*(2*b+1:ℕ)+8*(K+4:ℕ)
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 (4*constant/beta))
  have hN1:1≤N:=by exact_mod_cast ((le_max_left _ _).trans_lt hN).le
  refine ⟨N,hN1,?_⟩
  intro size hsize h n excluded S hh hn he hS
  have hnsize:(N:ℝ)≤size:=by exact_mod_cast hsize
  have hsizepos:0<(size:ℝ):=by exact_mod_cast (show 0<size by omega)
  have hconst:constant<beta*size/4:=by
    have hbN:4*constant/beta<(size:ℝ):=((le_max_right _ _).trans_lt hN).trans_le hnsize
    have hm:=(div_lt_iff₀ hb).mp hbN
    nlinarith only [hm]
  have hhub:(2*h:ℕ)≤theta*(size:ℝ):=by
    have hlim:=mul_le_mul_of_nonneg_right hept hsizepos.le
    push_cast
    nlinarith only [hh,hlim,mul_nonneg ht.le hsizepos.le]
  have hloss:(n*(K+l+8):ℕ)≤lam*(tau*(size:ℝ)):=by
    have h1:=mul_le_mul_of_nonneg_right hn hcap.le
    have h2:=mul_le_mul_of_nonneg_right hecap hsizepos.le
    dsimp only [cap] at h1 h2
    push_cast
    nlinarith only [h1,h2,mul_nonneg (mul_nonneg hl.le hta.le) hsizepos.le]
  have hSreal:(S:ℝ)≤size:=by exact_mod_cast hS
  have hfrac:(S*(l+4):ℕ)/(K:ℝ)≤beta*size/4:=by
    have hratio0:0≤(l+4:ℕ)/(K:ℝ):=by positivity
    have h1:=mul_le_mul_of_nonneg_right hSreal hratio0
    have h2:=mul_le_mul_of_nonneg_left hsmall.le hsizepos.le
    convert h1.trans h2 using 1 <;> push_cast <;> ring
  have hrest:(excluded:ℝ)+2*(n*(4*(K+4)):ℕ)+2*(n*(l+4):ℕ)+4*h≤beta*size/4:=by
    have hn1:=mul_le_mul_of_nonneg_right hn (show (0:ℝ)≤8*(K+4:ℕ) by positivity)
    have hn2:=mul_le_mul_of_nonneg_right hn (show (0:ℝ)≤2*(l+4:ℕ) by positivity)
    have hh4:=mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤4 by positivity)
    have htotal:=mul_le_mul_of_nonneg_right heC hsizepos.le
    dsimp [C] at htotal
    push_cast at hn1 hn2 htotal ⊢
    nlinarith only [he,hn1,hn2,hh4,htotal]
  refine ⟨hhub,Nat.mul_le_mul_left n (by omega),Nat.mul_le_mul_left n (by omega),hloss,?_⟩
  dsimp only [constant] at hconst
  push_cast at hconst hfrac hrest ⊢
  have hbetapos:0<beta*size:=mul_pos hb hsizepos
  nlinarith only [hconst,hfrac,hrest,hbetapos]

end Oberwolfach
