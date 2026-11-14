module

public import Oberwolfach.RawExpandedReservedMatchingHighProbability
public import Oberwolfach.MarkedInitialIndexCardLower
public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! The reservation event is an admissible Extra event for the actual marked
reference, with its existing physical law and uniform start retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_marked_reserved_matching_event
    (d:ℕ) (hd:2≤d) (ρ₀ sstar ζ:ℝ) (hρ₀:0<ρ₀) (hsstar:0<sstar) (hζ:0<ζ):
    ∃ α:ℝ,α=(5/32:ℝ)*sstar^2*(ρ₀/4) ∧ 0<α ∧ ∃ N:ℕ,∀ (V U:Type) [Fintype V] [LinearOrder V] [Nonempty V]
      [Fintype U] [DecidableEq U],N≤Fintype.card V→
    ∀ (D:ℕ) (αHost:ℝ) (hαHost:0<αHost)
      (hD:(1/2+αHost)*Fintype.card V≤(D:ℝ))
      (hρlo:ρ₀≤ initialIndexDensity U D)
      (π:Equiv.Perm V)
      (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (a j:Bool) (hsl:∀w,sstar≤s w j),
      let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-ζ≤(μ.sigma (mixedClassActualRetention true π d a)).probability
        (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):=by
  obtain ⟨α,hαeq,hα,N,hN⟩:=raw_expanded_reserved_matching_high_probability d hd (ρ₀/4) sstar ζ (by positivity) hsstar hζ
  refine ⟨α,hαeq,hα,max N 1,?_⟩
  intro V U _ _ _ _ _ hn D αHost hαHost hD hρlo π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort a j hsl μ
  have hnpos:0<Fintype.card V:=by have hh:=le_trans (le_max_right N 1) hn;omega
  have hcard:=marked_initial_index_card_lower (V:=V) (U:=U) D hnpos αHost ρ₀ hαHost hρ₀ hD hρlo
  let F:RawMarkedOutcome V U Bool Bool→Type:=fun σ=>
    StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
  letI:∀σ,Fintype (F σ):=fun _=>inferInstance
  let ν:∀σ,FiniteLaw (F σ):=fun σ=>
    startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
      (startRetentionMinimum_le _)
  have hh:=hN V U Bool Bool (le_trans (le_max_left _ _) hn) hcard π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν j hsl
  change 1-ζ≤(μ.sigma (fun σ=>ν (fun e=>rawExpandedMarkedCollapse e (σ e)))).probability
    (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)
  exact hh.1

theorem mixed_marked_reserved_matching_event_uniform_d
    (ρ₀ sstar:ℝ) (hρ₀:0<ρ₀) (hsstar:0<sstar):
    ∃ α:ℝ,0<α ∧ ∀ ζ:ℝ,0<ζ→∀ (d:ℕ) (hd:2≤d),∃ N:ℕ,∀ (V U:Type) [Fintype V] [LinearOrder V] [Nonempty V]
      [Fintype U] [DecidableEq U],N≤Fintype.card V→
    ∀ (D:ℕ) (αHost:ℝ) (hαHost:0<αHost)
      (hD:(1/2+αHost)*Fintype.card V≤(D:ℝ))
      (hρlo:ρ₀≤ initialIndexDensity U D)
      (π:Equiv.Perm V)
      (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (a j:Bool) (hsl:∀w,sstar≤s w j),
      let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-ζ≤(μ.sigma (mixedClassActualRetention true π d a)).probability
        (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) :=by
  refine ⟨(5/32:ℝ)*sstar^2*(ρ₀/4),by positivity,?_⟩
  intro ζ hζ d hd
  obtain ⟨α,hαeq,hα,N,hN⟩:=mixed_marked_reserved_matching_event d hd ρ₀ sstar ζ hρ₀ hsstar hζ
  subst α
  exact ⟨N,hN⟩

end Oberwolfach
