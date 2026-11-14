module

public import Oberwolfach.RawReservedLabelPhysicalAdaptiveEvent
public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! For polynomially many physical-sample-dependent test sets, all
unassigned counts hold with arbitrarily high probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_reserved_label_physical_adaptive_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color I:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [Fintype I],
    Fintype.card U≤Fintype.card V→Fintype.card I≤4*(Fintype.card V)^2→
    ∀(π:Equiv.Perm V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (color:Color) (A:(Sym2 V→Fin 6×Bool)→I→Finset V)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let law:=rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    let μ:=FiniteLaw.pi law
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w color (A (fun e=>z.1 (Sum.inl e)) i)-
        (A (fun e=>z.1 (Sum.inl e)) i).card*s w color|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  let c:ℝ:=2/(4*(d:ℝ)+3)^2
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N₀,hN₀⟩:=eventually_stretchedExp_le_inv_pow 8 3 (c:=c) (p:=1/2) hc (by norm_num) 1
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro V _ _ hn U Γ Color I _ _ _ _ _ hU hI π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort color A F _ ν law μ f
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn0
  have hUR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU
  have hIR:(Fintype.card I:ℝ)≤4*(Fintype.card V:ℝ)^2:=by exact_mod_cast hI
  have ht:0<(Fintype.card V:ℝ)^(3/4:ℝ):=by positivity
  have hpow:((Fintype.card V:ℝ)^(3/4:ℝ))^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
    calc
      _ = (Fintype.card V:ℝ)^(3/2:ℝ):=by rw [←Real.rpow_natCast,←Real.rpow_mul hnR.le];norm_num
      _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ):=by rw [←Real.rpow_add hnR];norm_num
      _ = _:=by rw [Real.rpow_one]
  have harg:-2*((Fintype.card V:ℝ)^(3/4:ℝ))^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ))=
      -c*(Fintype.card V:ℝ)^(1/2:ℝ):=by
    rw [hpow]
    dsimp [c]
    field_simp
  have hcoeff:2*(Fintype.card U:ℝ)*(Fintype.card I:ℝ)≤8*(Fintype.card V:ℝ)^3:=by
    have hU0:(0:ℝ)≤Fintype.card U:=by positivity
    have hI0:(0:ℝ)≤Fintype.card I:=by positivity
    nlinarith [mul_nonneg (show (Fintype.card V:ℝ)-Fintype.card U≥0 by linarith)
      (show (Fintype.card I:ℝ)≥0 by positivity),
      mul_nonneg (show (Fintype.card V:ℝ)≥0 by positivity)
      (show 4*(Fintype.card V:ℝ)^2-Fintype.card I≥0 by linarith)]
  have hbound:=hN₀ (Fintype.card V) (by omega)
  have hthree:(Fintype.card V:ℝ)^(3:ℝ)=(Fintype.card V:ℝ)^3:=by
    simpa using (Real.rpow_natCast (Fintype.card V:ℝ) 3)
  rw [hthree] at hbound
  simp only [pow_one] at hbound
  have hsmall:1/(Fintype.card V:ℝ)≤δ:=by
    have hh:1/δ<(Fintype.card V:ℝ):=lt_of_lt_of_le hN₁ (by exact_mod_cast (show N₁≤Fintype.card V by omega))
    apply (div_le_iff₀ hnR).2
    have hh':1<δ*(Fintype.card V:ℝ):=by have hhh:=(div_lt_iff₀ hδ).1 hh;nlinarith
    linarith
  have hp:=raw_reserved_label_physical_adaptive_family_event π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hn0 hnoshort color A _ ht F ν
  rw [harg] at hp
  have hfail:2*(Fintype.card U:ℝ)*(Fintype.card I:ℝ)*Real.exp (-c*(Fintype.card V:ℝ)^(1/2:ℝ))≤δ:=
    (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le).trans (hbound.trans hsmall)
  exact (sub_le_sub_left hfail 1).trans hp
end Oberwolfach
