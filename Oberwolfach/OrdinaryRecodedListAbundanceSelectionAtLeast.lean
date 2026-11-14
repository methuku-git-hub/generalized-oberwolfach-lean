module

public import Oberwolfach.OrdinaryRecodedListRateChoice
public import Oberwolfach.OrdinaryAbundanceMatchingReservationAtLeast

@[expose] public section
/-! Choose the list rates from the positive recoded density, then choose d
above their threshold, and only then choose the class cutoff and reservation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_recoded_list_abundance_selection_at_least
    (βfreq θ ρ₀ γ:ℝ) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hθ:0<θ) (hρ:0<ρ₀) (hγ:0<γ) (rstar m dNeed:ℕ) (hr:3≤rstar):
    ∃βList lam ζ:ℝ,0<βList ∧ βList≤1 ∧ 0<lam ∧ 0<ζ ∧
    ∃d K rank:ℕ,dNeed≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∃smin:ℝ,0<smin ∧ ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*(ρ₀*θ/4)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤(γ*(ρ₀*θ/4)^2)*n*(θ/2) ∧
      (lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n ∧
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hfreq:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤s ∧ s≤1/100 ∧ s≤1/(2*(K:ℝ)) ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=s*n) ∧
      (∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n):=by
  have hp:0<ρ₀*θ/4:=by positivity
  obtain ⟨βList,lam,ζ,hβ,hβle,hlam,hζ,dMin,hdMin,hlist⟩:=ordinary_recoded_list_rate_choice γ (ρ₀*θ/4) θ hγ hp hθ
  obtain ⟨d,K,rank,hdd,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,smin,hsmin,Nres,hres⟩:=
    ordinary_abundance_matching_reservation_at_least βfreq θ hβfreq hβ1 hθ rstar m (max dMin dNeed) hr
  obtain ⟨Nlist,hNlist⟩:=hlist d (le_trans (le_max_left dMin dNeed) hdd)
  refine ⟨βList,lam,ζ,hβ,hβle,hlam,hζ,d,K,rank,le_trans (le_max_right dMin dNeed) hdd,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,smin,hsmin,max Nlist Nres,?_⟩
  intro n hn
  obtain ⟨h1,h2,h3⟩:=hNlist n (by omega)
  exact ⟨h1,h2,h3,hres n (by omega)⟩
end Oberwolfach
