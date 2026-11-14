module

public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! One expanded outcome simultaneously satisfies any fixed finite family
of raw approximate-layer events, with the original retention law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color J:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Fintype J] [LinearOrder V] [DecidableEq U] [DecidableEq J]

theorem expanded_approximate_fixed_common_events
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (T:Finset J) (E:J→RawMarkedOutcome V U Γ Color→Prop) (failure:J→ℝ):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let μraw:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)
    (∀i∈T,1-failure i≤μraw.probability (E i))→
    1-∑i∈T,failure i ≤ (μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>∀i∈T,E i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
  intro μ f μraw hgood
  let M:=μ.sigma (fun ω=>ν (f ω))
  have hbad:∀i∈T,M.probability (fun z=>¬E i (fun e=>rawExpandedApproximateCollapse e (z.1 e)))≤failure i:=by
    intro i hi
    have hprojection:=raw_expanded_approximate_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν (E i)
    have hcomp:=finiteLaw_probability_compl M (fun z=>E i (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
    have hh:=hgood i hi
    dsimp only [M,μ,f,μraw] at *
    linarith
  have h:=finiteLaw_common_event_lower M T (fun i z=>¬E i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) failure hbad
  simpa only [not_not] using h
/-- The fixed raw tests may be joined to any already constructed event of
 the expanded-and-retained experiment, without resampling either outcome. -/
theorem expanded_approximate_common_events_with_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (T:Finset J) (E:J→RawMarkedOutcome V U Γ Color→Prop) (failure:J→ℝ):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let μraw:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)
    (∀i∈T,1-failure i≤μraw.probability (E i))→
    ∀(Prior:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ε:ℝ),
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability Prior →
    1-ε-∑i∈T,failure i ≤ (μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>Prior z ∧ ∀i∈T,E i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
  intro μ f μraw hgood Prior ε hprior
  have hh:=expanded_approximate_fixed_common_events p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν T E failure hgood
  have hi:=finiteLaw_good_intersection (μ.sigma (fun ω=>ν (f ω))) Prior
    (fun z=>∀i∈T,E i (fun e=>rawExpandedApproximateCollapse e (z.1 e))) (∑i∈T,failure i) hh
  linarith
/-- Positive probability yields a positive-mass point of a finite law. -/
theorem finiteLaw_positive_event_witness {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (h:0<μ.probability E):
    ∃ω,0<μ.mass ω ∧ E ω:=by
  have hn:∀ω∈(Finset.univ:Finset Ω),0≤(if E ω then μ.mass ω else 0):=by
    intro ω _
    split_ifs <;> simp_all [μ.nonneg]
  have hp:0<∑ω:Ω,if E ω then μ.mass ω else 0:=by
    unfold FiniteLaw.probability at h
    convert h using 1
  obtain ⟨ω,_,hω⟩:=(Finset.sum_pos_iff_of_nonneg hn).mp hp
  by_cases he:E ω
  · exact ⟨ω,by simpa [he] using hω,he⟩
  · simp [he] at hω

/-- A single positive-mass expanded-and-retained outcome satisfies the prior
 event and all fixed raw approximate tests when their total failure is below one. -/
theorem expanded_approximate_common_events_witness
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (T:Finset J) (E:J→RawMarkedOutcome V U Γ Color→Prop) (failure:J→ℝ):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let μraw:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)
    (∀i∈T,1-failure i≤μraw.probability (E i))→
    ∀(Prior:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,F (f ω))→Prop) (ε:ℝ),
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability Prior → ε+∑i∈T,failure i<1 →
    ∃z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Prior z ∧
      ∀i∈T,E i (fun e=>rawExpandedApproximateCollapse e (z.1 e)) :=by
  intro μ f μraw hgood Prior ε hprior hbudget
  have h:=expanded_approximate_common_events_with_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν T E failure hgood Prior ε hprior
  have hpos:0<(μ.sigma (fun ω=>ν (f ω))).probability
      (fun z=>Prior z ∧ ∀i∈T,E i (fun e=>rawExpandedApproximateCollapse e (z.1 e))):=by linarith
  obtain ⟨z,hz,hz'⟩:=finiteLaw_positive_event_witness _ _ hpos
  exact ⟨z,hz,hz'.1,hz'.2⟩
end Oberwolfach
