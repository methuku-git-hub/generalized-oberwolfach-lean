module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterEarly

@[expose] public section
/-! Choose the deep-cover load, edit and domain constants below arbitrary
previously fixed positive caps, with a finite dominating weight bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_uniform_parameter_choices
    (m:ℕ) (a c capLoad capEdit ε ρ₀ pmin C:ℝ)
    (ha:0<a) (hc:0<c) (hLoad:0<capLoad) (hEdit:0<capEdit)
    (hε:0<ε) (hρ:0<ρ₀) (hp:0<pmin) (hC:0<C):
    ∃aLoad b Kdom Bweight:ℝ,0<aLoad ∧ aLoad≤a ∧ aLoad≤capLoad ∧
      0<b ∧ b≤c ∧ b≤capEdit ∧ 0<Kdom ∧ 0<Bweight ∧
      2/ε≤Kdom ∧ 1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight :=by
  let aLoad:=min a capLoad/2
  let b:=min c capEdit/2
  let Kdom:=max (2/ε) (1+1/(ε/2)+1/((ε/2)*(ρ₀/8)))+1
  let Bweight:=max ((4*C/pmin^(3*m+1))*Kdom^m) 0+1
  have haLoad:0<aLoad:=by dsimp [aLoad]; positivity
  have hb:0<b:=by dsimp [b]; positivity
  have hKleft:2/ε≤Kdom:=by dsimp [Kdom]; linarith [le_max_left (2/ε) (1+1/(ε/2)+1/((ε/2)*(ρ₀/8)))]
  have hKright:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom:=by
    dsimp [Kdom]; linarith [le_max_right (2/ε) (1+1/(ε/2)+1/((ε/2)*(ρ₀/8)))]
  have hK:0<Kdom:=lt_of_lt_of_le (by positivity:0<2/ε) hKleft
  have hB:0<Bweight:=by dsimp [Bweight]; linarith [le_max_right ((4*C/pmin^(3*m+1))*Kdom^m) 0]
  have hBb:(4*C/pmin^(3*m+1))*Kdom^m≤Bweight:=by
    dsimp [Bweight]; linarith [le_max_left ((4*C/pmin^(3*m+1))*Kdom^m) 0]
  have hAa:aLoad≤a:=by
    dsimp [aLoad]
    have hh:=min_le_left a capLoad
    linarith
  have hAc:aLoad≤capLoad:=by
    dsimp [aLoad]
    have hh:=min_le_right a capLoad
    linarith
  have hbc:b≤c:=by
    dsimp [b]
    have hh:=min_le_left c capEdit
    linarith
  have hbcap:b≤capEdit:=by
    dsimp [b]
    have hh:=min_le_right c capEdit
    linarith
  exact ⟨aLoad,b,Kdom,Bweight,haLoad,hAa,hAc,hb,hbc,hbcap,hK,hB,hKleft,hKright,hBb⟩
end Oberwolfach
