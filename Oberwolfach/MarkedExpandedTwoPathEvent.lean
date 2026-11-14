module

public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.MarkedExpandedClassLaw
public import Oberwolfach.ColourOrientationTwoPathEvent
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Directed two-path concentration in the union of the sampled physical
classes, lifted to the joint raw exposure and arbitrary conditional retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_marked_class_two_paths
    (G E:SimpleGraph V) (hEG:E≤G)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)]
    (ν:∀ a,FiniteLaw (F a)) {t:ℝ} (ht:0≤t):
    let ρ:=2*p+2*k+2*p₂+2*k₂+u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ x y,x≠y→
      |(eligibleTwoPathCount E (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((E.neighborFinset x∩E.neighborFinset y).card:ℝ)*(ρ/2)^2|<t) := by
  intro ρ μ f
  let P:=fun σ:(Sym2 V→Fin 2×Bool)=>∀ x y,x≠y→
      |(eligibleTwoPathCount E (sampledColourOrientation G σ 0) x y:ℝ)-
        ((E.neighborFinset x∩E.neighborFinset y).card:ℝ)*(ρ/2)^2|<t
  have h:=sampledColourOrientation_twoPaths_common_event G E hEG (markedClassProbability ρ)
    (markedClassProbability_nonneg ρ (by dsimp [ρ];linarith) hsum) (markedClassProbability_sum ρ) 0 ht
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>P (fun e=>markedExpandedClass (z.1 (Sum.inl e))))=
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection (markedClassProbability ρ)
      (markedClassProbability_nonneg ρ (by dsimp [ρ];linarith) hsum) (markedClassProbability_sum ρ))).probability P:=by
    calc
      _ = μ.probability (fun ω=>P (fun e=>markedExpandedClass (ω (Sum.inl e)))) :=
        finiteLaw_sigma_first_probability μ (fun ω=>ν (f ω)) _
      _ = (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
        (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
        (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).probability (fun σ=>P (fun e=>markedExpandedClass (σ e))) := by
          simpa only [μ,rawExpandedMarkedWheelLaw] using
            (finiteLaw_pi_injective_projection_event
              (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
              Sum.inl Sum.inl_injective (fun σ=>P (fun e=>markedExpandedClass (σ e))))
      _ = _ := by
        rw [← finiteLaw_map_probability,
          marked_expanded_class_product_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum]
  change 1-2*(Fintype.card V:ℝ)^2*Real.exp (-t^2/Fintype.card V)≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>P (fun e=>markedExpandedClass (z.1 (Sum.inl e))))
  rw [heq]
  simpa [P,markedClassProbability] using h
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_marked_class_two_paths_highProbability :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (G E:SimpleGraph V) (hEG:E≤G)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let ρ:=2*p+2*k+2*p₂+2*k₂+u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    (999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ x y,x≠y→
      |(eligibleTwoPathCount E (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((E.neighborFinset x∩E.neighborFinset y).card:ℝ)*(ρ/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)) := by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (2:ℝ) 2
    (c:=1) (p:=1/5) (by norm_num) (by norm_num) 1
  refine ⟨max N 1000,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G E hEG p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν
  have hn1000:1000≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hb:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  simp only [pow_one, one_mul, neg_one_mul] at hb
  have hh:=raw_expanded_marked_class_two_paths G E hEG p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
    (t:=(Fintype.card V:ℝ)^(3/5:ℝ)) (by positivity)
  have he: -((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card V:ℝ)=-(Fintype.card V:ℝ)^(1/5:ℝ):=by
    have he':=threeFifths_tail_exponent hnpos
    have hr: -2*((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card V:ℝ)=
      2*(-((Fintype.card V:ℝ)^(3/5:ℝ))^2/(Fintype.card V:ℝ)):=by ring
    rw [hr] at he'
    linarith only [he']
  rw [he] at hh
  have hsmall:(1:ℝ)/(Fintype.card V:ℝ)≤1/1000:=by
    apply (div_le_iff₀ hnpos).2
    have : (1000:ℝ)≤Fintype.card V:=by exact_mod_cast hn1000
    linarith
  have hnum:(999:ℝ)/1000≤1-2*(Fintype.card V:ℝ)^2*Real.exp (-(Fintype.card V:ℝ)^(1/5:ℝ)):=by
    convert sub_le_sub_left (hb.trans hsmall) 1 using 1 <;> norm_num
  exact hnum.trans hh
end Oberwolfach
