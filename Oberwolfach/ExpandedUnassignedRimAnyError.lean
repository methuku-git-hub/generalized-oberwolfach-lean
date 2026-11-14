module

public import Oberwolfach.ExpandedUnassignedRimInvCard
public import Oberwolfach.ExpandedUnassignedRimHighProbability

@[expose] public section
/-! Inverse-order failure probability for the same fixed-domain event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_unassigned_rim_degree_highProbability_any (δ:ℝ) (hδ:0<δ) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],N≤Fintype.card V→
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
    ∀ (G:SimpleGraph V) (A:Finset V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ x,
      |(((G.neighborFinset x∩A).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-
        u*(G.neighborFinset x∩A).card|<(Fintype.card V:ℝ)^(3/4:ℝ)):=by
  obtain ⟨N,hN⟩:=raw_expanded_unassigned_rim_degree_highProbability_invCard
  obtain ⟨M,hM⟩:=exists_nat_gt (1/δ)
  refine ⟨max (max N M) 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ G A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F _ ν μ f
  have hnN:N≤Fintype.card V:=by omega
  have hnM:M≤Fintype.card V:=by omega
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hm:(1/δ)<(Fintype.card V:ℝ):=lt_of_lt_of_le hM (by exact_mod_cast hnM)
  have hinv:1/(Fintype.card V:ℝ)≤δ:=by
    apply (div_le_iff₀ hnpos).2
    have hh:(1:ℝ)<δ*Fintype.card V:=by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hm
    linarith
  have hh:=hN V hnN U Γ Color G A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  linarith
end Oberwolfach
