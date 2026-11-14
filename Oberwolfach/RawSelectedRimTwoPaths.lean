module

public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.MarkedPhysicalTwoPaths
public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The physical edges reserved for the approximate ordinary layer retain
the two-path estimate even after arbitrary conditional start retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_selected_rim_two_paths
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,(∑j,s w j)≤ intervalUncoveredProbability d (∑g,q w g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a))
    {t:ℝ} (ht:0≤t):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
      (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀x y,x≠y→
        ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*((3*d:ℕ):ℝ)+1)≤
        ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
          (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
          0<markedPhysicalRim P π (3*d)
          (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)):=by
  intro μ f
  let E:=fun σ:RawMarkedOutcome V U Γ Color=>∀x y,x≠y→
    ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false v y)).card:ℝ)
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (f z.1))=
      (FiniteLaw.pi (fun _:Sym2 V=>markedPhysicalLaw p k hp hk (by linarith))).probability
        (fun σ=>∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*((3*d:ℕ):ℝ)+1)≤
          ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d) σ false x v ∧
            0<markedPhysicalRim P π (3*d) σ false v y)).card:ℝ)):=by
    calc
      _ = μ.probability (fun ω=>E (f ω)):=finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).probability E:=by
        rw [←finiteLaw_map_probability,raw_expanded_marked_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum]
      _ = _ := by
        let Q:=fun σ:Sym2 V→Option (Bool×Bool)=>∀x y,x≠y→
          ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-t-2*(2*((3*d:ℕ):ℝ)+1)≤
            ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d) σ false x v ∧
              0<markedPhysicalRim P π (3*d) σ false v y)).card:ℝ)
        change (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).probability
          (fun σ=>Q (fun e=>σ (Sum.inl e))) =
          (FiniteLaw.pi (fun _:Sym2 V=>markedPhysicalLaw p k hp hk (by linarith))).probability Q
        simpa only [rawMarkedWheelLaw] using
          (finiteLaw_pi_injective_projection_event
            (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)
            Sum.inl Sum.inl_injective Q)
  have hh:=markedPhysicalRim_twoPaths_event P π (3*d) p k hp hk (by linarith) t ht
  change _≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (f z.1))
  rw [heq]
  exact hh
theorem raw_expanded_selected_rim_two_paths_high_probability
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,∀(V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    ∀(P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,(∑j,s w j)≤ intervalUncoveredProbability d (∑g,q w g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀a,Fintype (F a)] (ν:∀a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀x y,x≠y→
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(Fintype.card V:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)):=by
  obtain ⟨N₀,hN₀⟩:=eventually_stretchedExp_le_inv_pow 2 2 (c:=1) (p:=1/2) (by norm_num) (by norm_num) 1
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS F _ ν μ f
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn0
  have hpow:((Fintype.card V:ℝ)^(3/4:ℝ))^2=(Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ):=by
    calc
      _ = (Fintype.card V:ℝ)^(3/2:ℝ):=by rw [←Real.rpow_natCast,←Real.rpow_mul hnR.le];norm_num
      _ = (Fintype.card V:ℝ)^(1/2:ℝ)*(Fintype.card V:ℝ)^(1:ℝ):=by rw [←Real.rpow_add hnR];norm_num
      _ = _:=by rw [Real.rpow_one]
  have harg:-((Fintype.card V:ℝ)^(3/4:ℝ))^2/(Fintype.card V:ℝ)=-(Fintype.card V:ℝ)^(1/2:ℝ):=by
    rw [hpow]
    field_simp
  have hbound:=hN₀ (Fintype.card V) (by omega)
  have htwo:(Fintype.card V:ℝ)^(2:ℝ)=(Fintype.card V:ℝ)^2:=by
    simpa using (Real.rpow_natCast (Fintype.card V:ℝ) 2)
  rw [htwo] at hbound
  simp only [pow_one,one_mul] at hbound
  have hsmall:1/(Fintype.card V:ℝ)≤δ:=by
    have hh:1/δ<(Fintype.card V:ℝ):=lt_of_lt_of_le hN₁ (by exact_mod_cast (show N₁≤Fintype.card V by omega))
    apply (div_le_iff₀ hnR).2
    have hh':1<δ*(Fintype.card V:ℝ):=by have hhh:=(div_lt_iff₀ hδ).1 hh;nlinarith
    linarith
  have hpEvent:=raw_expanded_selected_rim_two_paths P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν (t:=(Fintype.card V:ℝ)^(3/4:ℝ)) (by positivity)
  rw [harg] at hpEvent
  have hfail:2*(Fintype.card V:ℝ)^2*Real.exp (-(Fintype.card V:ℝ)^(1/2:ℝ))≤δ:=by
    simpa only [neg_one_mul] using hbound.trans hsmall
  exact (sub_le_sub_left hfail 1).trans hpEvent
end Oberwolfach
