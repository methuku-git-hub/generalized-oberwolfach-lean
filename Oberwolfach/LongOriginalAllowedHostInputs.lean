module

public import Oberwolfach.LongOriginalAbundanceClass
public import Oberwolfach.FactorCyclePartition
public import Oberwolfach.UniformGrid

@[expose] public section
/-! Convert the original factor threshold and positive density into the
    nonempty allowed set and host margin used by the long construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_original_positive_density_counts (D q:ℕ)
    (hρ:0<2*(q:ℝ)/(D:ℝ)):0<q ∧ 0<D :=by
  constructor
  · by_contra h
    have hq:q=0:=by omega
    simp [hq] at hρ
  · by_contra h
    have hD:D=0:=by omega
    simp [hD] at hρ

theorem long_original_allowed_host_inputs
    {n q D:ℕ} (hn:0<n) (hq:0<q) (θ α₀ αHost:ℝ)
    (hα:αHost≤α₀) (hdegree:(θ+α₀)*(n:ℝ)≤D)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ):
    ∃Allowed:Set ℕ,Allowed.Nonempty ∧ (∀s∈Allowed,3≤s) ∧
      allowedThreshold Allowed≤θ ∧ (allowedThreshold Allowed+αHost)*(n:ℝ)≤D ∧
      ∀w,AllowedCycleLengths (F w) Allowed :=by
  let Allowed:Set ℕ:={s | 3≤s ∧ cycleThreshold s≤θ}
  let w₀:Fin q:=⟨0,hq⟩
  let v₀:Fin n:=⟨0,hn⟩
  have hAllowed:Allowed.Nonempty:=by
    refine ⟨Fintype.card ((F w₀).connectedComponentMk v₀),?_⟩
    exact ⟨(component_regular_two_cycle_iso (F w₀) (hF w₀) ((F w₀).connectedComponentMk v₀)).1,hthreshold w₀ v₀⟩
  have hvalid:∀s∈Allowed,3≤s:=by intro s hs;exact hs.1
  have hallowed:allowedThreshold Allowed≤θ:=by
    unfold allowedThreshold
    apply csSup_le (hAllowed.image cycleThreshold)
    rintro x ⟨s,hs,rfl⟩
    exact hs.2
  have hmargin:(allowedThreshold Allowed+αHost)*(n:ℝ)≤D:=by
    have hn0:(0:ℝ)≤n:=by positivity
    exact (mul_le_mul_of_nonneg_right (add_le_add hallowed hα) hn0).trans hdegree
  refine ⟨Allowed,hAllowed,hvalid,hallowed,hmargin,?_⟩
  intro w v
  rw [reachable_order_eq_component_card (F w) ((F w).connectedComponentMk v) v rfl]
  exact ⟨(component_regular_two_cycle_iso (F w) (hF w) ((F w).connectedComponentMk v)).1,hthreshold w v⟩
theorem long_original_full_host_inputs
    {n q D K:ℕ} (hn:0<n) (θ α₀ αHost ρstar:ℝ)
    (hα:αHost≤α₀) (hdegree:(θ+α₀)*(n:ℝ)≤D)
    (hρstar:0<ρstar) (hρlo:ρstar≤2*(q:ℝ)/(D:ℝ))
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (hthreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)
    (hlong:∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ)):
    0<q ∧ 0<D ∧ (∀w,factorPreparationClass (F w) K=none) ∧
    ∃Allowed:Set ℕ,Allowed.Nonempty ∧ (∀s∈Allowed,3≤s) ∧
      allowedThreshold Allowed≤θ ∧ (allowedThreshold Allowed+αHost)*(n:ℝ)≤D ∧
      ∀w,AllowedCycleLengths (F w) Allowed :=by
  obtain ⟨hq,hD⟩:=long_original_positive_density_counts D q (hρstar.trans_le hρlo)
  exact ⟨hq,hD,long_original_abundance_gives_class_none hn F hlong,
    long_original_allowed_host_inputs hn hq θ α₀ αHost hα hdegree F hF hthreshold⟩
end Oberwolfach
