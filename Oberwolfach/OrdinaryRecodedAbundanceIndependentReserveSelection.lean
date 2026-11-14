module

public import Oberwolfach.OrdinaryRecodedListRateChoice
public import Oberwolfach.OrdinaryAbundanceMatchingGeometryAtLeast
public import Oberwolfach.OrdinaryAbundanceReservationIndependentCutoff

@[expose] public section
/-! Choose the recoded list rates and a positive reserve floor before any
requested spacing; the actual class frequency supplies the reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_recoded_abundance_independent_reserve_selection
    (βfreq θ ρ₀ γ:ℝ) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hθ:0<θ) (hρ:0<ρ₀) (hγ:0<γ) (rstar m:ℕ) (hr:3≤rstar):
    ∃βList lam ζ smin:ℝ,0<βList ∧ βList≤1 ∧ 0<lam ∧ 0<ζ ∧ 0<smin ∧ smin=βfreq/200 ∧
    ∀dNeed:ℕ,∃d K rank:ℕ,dNeed≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*(ρ₀*θ/4)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤(γ*(ρ₀*θ/4)^2)*n*(θ/2) ∧
      (lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n ∧
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hfreq:∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤s ∧ s≤1/100 ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=s*n) ∧
      (∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n) :=by
  have hp:0<ρ₀*θ/4:=by positivity
  obtain ⟨βList,lam,ζ,hβ,hβle,hlam,hζ,dMin,hdMin,hlist⟩:=ordinary_recoded_list_rate_choice γ (ρ₀*θ/4) θ hγ hp hθ
  refine ⟨βList,lam,ζ,βfreq/200,hβ,hβle,hlam,hζ,by positivity,rfl,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hdd,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap⟩:=
    ordinary_abundance_matching_geometry_at_least βfreq θ hβfreq hθ rstar m (max dMin dNeed)
  obtain ⟨Nlist,hNlist⟩:=hlist d (le_trans (le_max_left dMin dNeed) hdd)
  obtain ⟨Nres,hres⟩:=ordinary_abundance_reservation_independent_cutoff βfreq hβfreq hβ1 rstar K hr hrK hβK
  refine ⟨d,K,rank,le_trans (le_max_right dMin dNeed) hdd,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,max Nlist Nres,?_⟩
  intro n hn
  obtain ⟨h1,h2,h3⟩:=hNlist n (by omega)
  exact ⟨h1,h2,h3,hres n (by omega)⟩
end Oberwolfach
