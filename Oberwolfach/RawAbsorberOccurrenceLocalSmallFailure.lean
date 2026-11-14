module

public import Oberwolfach.RawAbsorberColumnLocalSmallFailure
public import Oberwolfach.RawIntervalExtendedHubsUpperOn

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_absorber_occurrence_local_small_failure
    (d:ℕ) (hd:2≤d) (δ:ℝ) (hδ:0<δ) :
    ∃N:ℕ,1≤N ∧ ∀(V U Color:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype Color],
    ∀(I:Type) (T:Finset I) (A:I→Finset V) (J:I→Finset U),
    (∀i∈T,N≤(A i).card) → Set.InjOn (fun i=>(A i).card) T →
    (∀i∈T,0<(J i).card) → (∀i∈T,(J i).card≤(A i).card) →
    ∀(π:Equiv.Perm V) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℝ) (hm:0<m) (hqm:∀u g,q u g≤1/m),
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-δ≤μ.probability (fun σ=>∀i∈T,∀v∈A i,
      ((rawIntervalExtendedAnyHubSet π d σ v ∩ J i).card:ℝ) ≤
      4*((J i).card:ℝ)/m+4*((A i).card:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN,hgood⟩:=raw_interval_absorber_column_local_family_small_failure d hd δ hδ
  refine ⟨N,hN,?_⟩
  intro V U Color _ _ _ _ _ I T A J hmin hinj hJ hJA π q hq hQ s hs hS hnoshort m hm hqm μ
  have hh:=hgood V U Color I T A J hmin hinj hJ hJA π q hq hQ s hs hS hnoshort
  refine hh.trans ?_
  apply finiteLaw_probability_mono
  intro σ hσ i hi
  have hlabel:∀v∈A i,∀g,|rawIntervalAssignedLabelColumnCount π d σ v g (J i)-∑u∈J i,q u g|<((A i).card:ℝ)^(3/4:ℝ):=by
    intro v hv g
    exact (hσ i hi v hv g).1
  have hstart:∀v∈A i,∀g,|rawIntervalStartColumnCount π d σ ((π^d).symm v) g (J i)-∑u∈J i,q u g/(d:ℝ)|<((A i).card:ℝ)^(3/4:ℝ):=by
    intro v hv g
    exact (hσ i hi v hv g).2
  exact raw_interval_extended_any_hubs_upper_on π d (by omega) σ q (A i) (J i) m _ hm hq hqm hlabel hstart
end Oberwolfach
