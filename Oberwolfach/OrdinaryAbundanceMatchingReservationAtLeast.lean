module

public import Oberwolfach.OrdinaryAbundanceMatchingGeometryAtLeast
public import Oberwolfach.OrdinaryAbundanceReservedData
public import Oberwolfach.OrdinaryAbundanceCandidate

@[expose] public section
/-! Before the graph choose matching geometry and a positive reservation
scale; the original abundance then supplies an exact common reservation and
the candidate condition for every factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_abundance_matching_reservation_at_least
    (β θ:ℝ) (hβ:0<β) (hβ1:β≤1) (hθ:0<θ) (rstar m dMin:ℕ) (hr:3≤rstar):
    ∃d K rank:ℕ,dMin≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∃smin:ℝ,0<smin ∧ ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hfreq:∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤s ∧ s≤1/100 ∧ s≤1/(2*(K:ℝ)) ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=s*n) ∧
      (∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n):=by
  obtain ⟨d,K,rank,hdMin,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap⟩:=
    ordinary_abundance_matching_geometry_at_least β θ hβ hθ rstar m dMin
  let βres:=min β (1/(K:ℝ))
  have hK0:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hβres:0<βres:=lt_min hβ (by positivity)
  have hβresβ:βres≤β:=min_le_left _ _
  have hβres1:βres≤1:=hβresβ.trans hβ1
  have hβresK:βres≤1/(K:ℝ):=min_le_right _ _
  obtain ⟨N,hN⟩:=ordinary_reserved_data_from_abundance βres hβres hβres1 rstar hr K hrK
  refine ⟨d,K,rank,hdMin,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,βres/200,by positivity,max N 1,?_⟩
  intro n hn U _ F hF hfreq
  have hn0:0<n:=by omega
  have hfreq':∀u,βres*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ):=by
    intro u
    exact (mul_le_mul_of_nonneg_right hβresβ (Nat.cast_nonneg n)).trans (hfreq u)
  obtain ⟨i₀,s,C,hi,hlo,hhi,hsize,heq,hreserve⟩:=hN n (by omega) U F hF hfreq'
  have hs1:s≤1/100:=by nlinarith only [hhi,hβres1]
  have hsclass:s≤1/(2*(K:ℝ)):=by
    have hpos:0<1/(K:ℝ):=by positivity
    have he:1/(2*(K:ℝ))=(1/(K:ℝ))/2:=by ring
    rw [he]
    nlinarith only [hhi,hβresK,hpos]
  have hfreq'':∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=i₀.val+1)).card:ℝ):=by
    simpa only [hi] using hfreq
  have hcand:=ordinary_specified_abundance_is_candidate hn0 F K i₀ β hβK hfreq''
  exact ⟨i₀,s,C,hi,hlo,hs1,hsclass,hcand,hsize,heq,hreserve⟩
end Oberwolfach
