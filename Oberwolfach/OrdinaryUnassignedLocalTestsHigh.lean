module

public import Oberwolfach.OrdinaryUnassignedLocalTests
public import Oberwolfach.FiniteSigmaSameFirstEvent

@[expose] public section
/-! The fixed protected domains and their full-domain counterparts share
one unassigned-edge/pair event on any dependent expanded experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unassigned_local_tests_high
    (d:ℕ) (hd:2≤d) (ζ:ℝ) (hζ:0<ζ):
    ∃N:ℕ,1≤N ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→0<Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (J:Finset U)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma ν).probability (fun z=>OrdinaryUnassignedLocalTests P π d q s u A J z.1) :=by
  obtain ⟨NRim,hRim⟩:=raw_expanded_unassigned_rim_degree_highProbability_any (ζ/4) (by positivity)
  obtain ⟨NPair,hPair⟩:=raw_expanded_unassigned_fixed_domains_high_probability_any d hd (ζ/4) (by positivity)
  refine ⟨max 1 (max NRim NPair),by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU0 hU P π A J p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort R _ ν μ
  have hnpos:0<(Fintype.card V:ℝ):=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hpow:0<(Fintype.card V:ℝ)^(3/4:ℝ):=by positivity
  let J':Finset U:=if J.Nonempty then J else Finset.univ
  have hJ':J'.Nonempty:=by
    dsimp [J']
    split_ifs with hJ
    · exact hJ
    · exact Finset.card_pos.mp (by simpa using hU0)
  have hUuniv:(Finset.univ:Finset U).Nonempty:=Finset.card_pos.mp (by simpa using hU0)
  let νunit:=fun (_:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>FiniteLaw.uniform Unit
  let R1:=fun σ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>∀v,
    |(((P.neighborFinset v∩A).filter (fun x=>(σ (Sum.inl s(v,x))).1=4)).card:ℝ)-u*(P.neighborFinset v∩A).card|<(Fintype.card V:ℝ)^(3/4:ℝ)
  let R2:=fun σ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)=>∀v,
    |(((P.neighborFinset v).filter (fun x=>(σ (Sum.inl s(v,x))).1=4)).card:ℝ)-u*(P.neighborFinset v).card|<(Fintype.card V:ℝ)^(3/4:ℝ)
  let Pair:=fun (T:Finset V) (H:Finset U) (σ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e))=>
    (∀w,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w T-(T.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    (∀v,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v H-∑w∈H,(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))
  have hLift (E:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Prop)
      (h:1-ζ/4≤(μ.sigma νunit).probability (fun z=>E z.1)):
      1-ζ/4≤(μ.sigma ν).probability (fun z=>E z.1):=by
    rw [finiteLaw_sigma_same_first_event μ νunit ν E] at h
    exact h
  have hR1:1-ζ/4≤(μ.sigma ν).probability (fun z=>R1 z.1):=by
    apply hLift
    exact hRim V (by omega) U Γ Color P A p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
  have hR2:1-ζ/4≤(μ.sigma ν).probability (fun z=>R2 z.1):=by
    apply hLift
    have hh:=hRim V (by omega) U Γ Color P Finset.univ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
    simpa only [Finset.inter_univ] using hh
  have hP1:1-ζ/4≤(μ.sigma ν).probability (fun z=>Pair A J' z.1):=by
    apply hLift
    exact hPair V (by omega) U Γ Color hU π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit) A J' hJ'
  have hP2:1-ζ/4≤(μ.sigma ν).probability (fun z=>Pair Finset.univ Finset.univ z.1):=by
    apply hLift
    exact hPair V (by omega) U Γ Color hU π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit) Finset.univ Finset.univ hUuniv
  let E1:(Σσ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),R σ)→Prop:=fun z=>R1 z.1
  let E2:(Σσ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),R σ)→Prop:=fun z=>R2 z.1
  let E3:(Σσ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),R σ)→Prop:=fun z=>Pair A J' z.1
  let E4:(Σσ:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),R σ)→Prop:=fun z=>Pair Finset.univ Finset.univ z.1
  have h12:=finiteLaw_intersection_lower (μ.sigma ν) E1 E2 (ζ/4) (ζ/4) hR1 hR2
  have h12':1-(ζ/2)≤(μ.sigma ν).probability (fun z=>E1 z ∧ E2 z):=by linarith
  have h123:=finiteLaw_intersection_lower (μ.sigma ν) (fun z=>E1 z ∧ E2 z) E3 (ζ/2) (ζ/4) h12' hP1
  have h123':1-(3*ζ/4)≤(μ.sigma ν).probability (fun z=>(E1 z ∧ E2 z) ∧ E3 z):=by linarith
  have h1234:=finiteLaw_intersection_lower (μ.sigma ν) (fun z=>(E1 z ∧ E2 z) ∧ E3 z) E4 (3*ζ/4) (ζ/4) h123' hP2
  have hbudget:1-ζ≤(μ.sigma ν).probability (fun z=>((E1 z ∧ E2 z) ∧ E3 z) ∧ E4 z):=by linarith
  apply hbudget.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨⟨hr1,hr2⟩,hp1⟩,hp2⟩:=hz
  have hcol:∀v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-
      ∑w∈J,(1-(∑g,q w g)-(∑j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ):=by
    by_cases hJ:J.Nonempty
    · simpa only [J',if_pos hJ] using hp1.2
    · have he:J=∅:=Finset.not_nonempty_iff_eq_empty.mp hJ
      intro v
      simp only [he,rawIntervalUnassignedColumnCount,Finset.sum_empty,sub_self,abs_zero]
      exact hpow
  change OrdinaryUnassignedLocalTests P π d q s u A J z.1
  exact ⟨hr1,hr2,hp1.1,by simpa using hp2.1,hcol,by simpa using hp2.2⟩
end Oberwolfach
