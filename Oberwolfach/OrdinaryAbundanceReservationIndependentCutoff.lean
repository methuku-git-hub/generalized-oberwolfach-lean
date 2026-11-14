module

public import Oberwolfach.OrdinaryAbundanceReservedData
public import Oberwolfach.OrdinaryAbundanceCandidate

@[expose] public section
/-! The original common abundant length supplies a positive reserved density
whose lower bound is independent of the later cutoff K. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_abundance_reservation_independent_cutoff
    (β:ℝ) (hβ:0<β) (hβ1:β≤1) (r K:ℕ) (hr:3≤r) (hrK:r≤K)
    (hβK:1/(2*(K:ℝ))≤β):
    ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hfreq:∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=r)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=r ∧ β/200≤s ∧ s≤1/100 ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=r) ∧
      (∀u,(r:ℝ)*(C u).card=s*n) ∧
      (∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n) :=by
  obtain ⟨N,hN⟩:=ordinary_reserved_data_from_abundance β hβ hβ1 r hr K hrK
  refine ⟨max N 1,?_⟩
  intro n hn U _ F hF hfreq
  have hn0:0<n:=by omega
  obtain ⟨i₀,s,C,hi,hlo,hhi,hsize,heq,hreserve⟩:=hN n (by omega) U F hF hfreq
  have hs:s≤1/100:=by nlinarith [hhi,hβ1]
  have hfreq':∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=i₀.val+1)).card:ℝ):=by
    simpa only [hi] using hfreq
  have hcand:=ordinary_specified_abundance_is_candidate hn0 F K i₀ β hβK hfreq'
  exact ⟨i₀,s,C,hi,hlo,hs,hcand,hsize,heq,hreserve⟩
end Oberwolfach
