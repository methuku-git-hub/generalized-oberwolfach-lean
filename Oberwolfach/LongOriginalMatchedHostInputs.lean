module

public import Oberwolfach.LongOriginalAllowedHostInputs
public import Oberwolfach.LongRegularHostNumericInputs
public import Oberwolfach.FirstVortexDensityIdentity

@[expose] public section
/-! The original long-factor and regular-host assumptions supply the exact
    density, degree, classifier and allowed-length inputs together. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_original_matched_host_inputs
    {n q D K:ℕ} (hn:0<n) (θ α₀ αRef ρstar ρ₀:ℝ)
    (hαRef:0<αRef) (hα:2*αRef≤α₀) (hdegree:(θ+α₀)*(n:ℝ)≤D)
    (hρstar:0<ρstar) (hρ₀:0<ρ₀) (hρcap:ρ₀≤ρstar)
    (hρlo:ρstar≤2*(q:ℝ)/(D:ℝ)) (hρhi:2*(q:ℝ)/(D:ℝ)≤1)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)
    (hlong:∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ)):
    ∃Allowed:Set ℕ,Allowed.Nonempty ∧ (∀s∈Allowed,3≤s) ∧ allowedThreshold Allowed≤θ ∧
      (allowedThreshold Allowed+2*αRef)*(n:ℝ)≤D ∧ (∀w,AllowedCycleLengths (F w) Allowed) ∧
      (∀w,factorPreparationClass (F w) K=none) ∧
      0<q ∧ 0<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧ (1/2+2*αRef)*n≤(D:ℝ) ∧
      ρ₀≤ initialIndexDensity (Fin q) D ∧ initialIndexDensity (Fin q) D≤1 ∧
      initialIndexDensity (Fin q) D*(D:ℝ)=2*Fintype.card (Fin q) ∧ Fintype.card (Fin q)≤n :=by
  obtain ⟨hq,hD,hclass,Allowed,hAllowed,hvalid,hallowed,hmargin,hFallowed⟩:=
    long_original_full_host_inputs hn θ α₀ (2*αRef) ρstar hα hdegree hρstar hρlo F hF hthreshold hlong
  have hρlo':ρ₀≤ initialIndexDensity (Fin q) D:=by
    apply hρcap.trans
    simpa only [initialIndexDensity,Fintype.card_fin] using hρlo
  have hρhi':initialIndexDensity (Fin q) D≤1:=by
    simpa only [initialIndexDensity,Fintype.card_fin] using hρhi
  obtain ⟨hD',hDlo,hDhi,hmarginHalf,hdeg,hdensity⟩:=
    long_regular_host_numeric_inputs n D hn (Fin q) Allowed hAllowed hvalid (2*αRef) (by positivity) P hreg hmargin
  have hcards:0<Fintype.card (Fin q) ∧ Fintype.card (Fin q)≤n:=
    (first_vortex_density_identity n D ρ₀ hD' hρ₀ hρlo' hρhi' hDhi).2.2
  exact ⟨Allowed,hAllowed,hvalid,hallowed,hmargin,hFallowed,hclass,hq,hD,hDlo,hDhi,hmarginHalf,hρlo',hρhi',hdensity,hcards.2⟩
end Oberwolfach
