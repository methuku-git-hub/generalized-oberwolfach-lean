module

public import Oberwolfach.MarkedIterationRestrictedProfiles
public import Oberwolfach.MarkedLocalEstimateMonotonicity
public import Oberwolfach.MarkedIterationErrorScales

@[expose] public section

/-! The actual protected-star incidence allowance supplies the local
cover-down inputs with their fixed local order and fixed coefficient
function. The hub domain may include hubs outside the protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K W Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype W] [Fintype Z] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W]
    [DecidableEq U] [DecidableEq Z] [DecidableEq E] [DecidableEq K]

theorem marked_local_cover_input_margins
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H : Bool→V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (F : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Y : Finset U) (hX : ∀ v,π v∈X↔v∈X)
    (sigma eps C t β η : ℝ) (hσ : 0≤sigma) (heps : 0<eps) (hC : 0≤C)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈F)
    (hS : ∀ s∈S,H false s.1 s.2∨H true s.1 s.2) (hSF : ∀ s∈S,Sum.inr s∈F)
    (hStar : ∀ physical z,(((markedIncidentEdges tail head ktail khead π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π (H false) (H true) e∈F.filter (markedStarResource X Y))).card:ℝ)
        ≤sigma*Fintype.card V)
    (f : W↪oV) (g : Z↪U) (hf : ∀ x,f x∈X)
    (P : SimpleGraph V) (ρ : Equiv.Perm W) (d r : ℕ) (hn : 0<Fintype.card W)
    (hsize : eps*Fintype.card V/4≤(Fintype.card W:ℝ))
    (D τ aLo B : ℝ) (hDlo : (Fintype.card W:ℝ)/2≤D) (hDhi : D≤2*Fintype.card W)
    (p k s₀ pstar : ℝ) (hpstar : 0<pstar) (hp : pstar≤p) (hk : pstar≤k) (hs : pstar≤s₀)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀≤1) (hB : 0≤B)
    (q : Z→Γ→ℝ) (s : Z→Color→ℝ) (a : Γ) (c : Color)
    (weight : (Fin (r+4+1)→W)→ℝ)
    (hw : SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τ aLo B weight)
    (hCR : 2≤C) (hCC : 2*(r+5:ℝ)≤C) (hCP : (2*r+11:ℝ)≤C)
    (hCL : 15*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))≤C)
    (hbudget : 4*C*sigma/eps≤min (t/8) (min β (η/4)))
    (σ : RawMarkedOutcome V U Γ Color)
    (hrow : MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a c ((t/8)*Fintype.card W)
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)))
    (hconf : MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ (3*β) (3*β)
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)))
    (hload : MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight (η/4)
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u))) :
    let DR := physicalEdgeGraph (A.image (markedPhysicalEdge tail head ktail khead π))
    let DS := markedFiniteSpokeGraph S
    let σ' := rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let H' := fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ p k q s a c ((t/4)*Fintype.card W) σ' H' ∧
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ (2*β) (2*β) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D p k s₀ weight (η/2) σ' H' := by
  intro DR DS σ' H'
  have hnR : (0:ℝ)<Fintype.card W := by exact_mod_cast hn
  have hδ : 0≤sigma*Fintype.card V := mul_nonneg hσ (Nat.cast_nonneg _)
  have hNorm := marked_iteration_local_normalization C sigma eps (Fintype.card V) (Fintype.card W)
    (min (t/8) (min β (η/4))) hC hσ heps (Nat.cast_nonneg _) hnR hsize hbudget
  have hNormR := hNorm.trans (min_le_left _ _)
  have hNormC := hNorm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNormL := hNorm.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBound (c : ℝ) (hc : c≤C) : c*(sigma*Fintype.card V)/Fintype.card W≤C*(sigma*Fintype.card V)/Fintype.card W :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hδ) hnR.le
  have hRowBudget : (t/8)*Fintype.card W+2*1*(sigma*Fintype.card V)≤(t/4)*Fintype.card W := by
    have h := (div_le_iff₀ hnR).mp ((hBound 2 hCR).trans hNormR)
    nlinarith only [h]
  obtain ⟨hr,hc⟩ := marked_iteration_restricted_profiles tail head ktail khead π H A S F X Y hX
    (sigma*Fintype.card V) hδ hA hS hSF hStar f g hf P ρ d 1 r hn p k q s a c
    ((t/8)*Fintype.card W) (3*β) (3*β) σ hrow hconf
  have hl := marked_iteration_local_loads_from_resource_bounds tail head ktail khead π H A S F X Y hX
    (sigma*Fintype.card V) hδ hA hS hSF hStar f g hf P ρ d (r+4) (by omega) hn D τ aLo B
    hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB weight hw (η/4) σ hload
  refine ⟨?_,?_,?_⟩
  · intro Q R J hQ hR hJ hinj
    exact (hr Q R J hQ hR hJ hinj).trans_le (by simpa only [Nat.cast_one] using hRowBudget)
  · apply markedLocalConfigurations_mono r (P.comap f) ρ d Finset.univ _ _ (2*β) (2*β) _ _ _ _ hc
    · linarith only [(hBound (2*(r+5:ℝ)) hCC).trans hNormC]
    · linarith only [(hBound (2*r+11:ℝ) hCP).trans hNormC]
  · apply markedLocalSpokeLoads_mono (P.comap f) ρ d (r+4) D p k s₀ weight _ (η/2) _ _ _ hl
    have h := (hBound (15*(r+5:ℝ)^4*(2*B/pstar^(2*(r+4)+1))) hCL).trans hNormL
    push_cast
    rw [show (r:ℝ)+4+1=r+5 by ring]
    linarith only [h]

end Oberwolfach
