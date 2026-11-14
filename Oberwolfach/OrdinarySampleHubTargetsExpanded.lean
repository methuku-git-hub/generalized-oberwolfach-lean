module

public import Oberwolfach.OrdinaryInducedHubTargetsFromCleanup
public import Oberwolfach.OrdinaryTrianglePotentialCoefficientBounds

@[expose] public section
/-! Fixed inner triangle weights, a supplied earlier expanded event, a raw
prior and the reference cuts share one outcome. Every subsequent cleanup
profile on that outcome has the required hub-potential targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_sample_hub_targets_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (J:RawWheelOutcome V U Γ Color→Prop) (a b c:ℝ)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color) (δref href:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U) (hA:0<A.card)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (pmin pH D cLo cHi t Ledit ξ density tR tH βe βh:ℝ)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hR:pmin≤2*p) (hH:pmin≤pH) (hH1:pH≤1)
    (hcLo:0<cLo) (hcHi:0<cHi)
    (hDlo:(A.card:ℝ)/2≤D) (hDhi:D≤2*A.card) (ht:0<t)
    (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (hweight:∀ C,cLo/(A.card:ℝ)≤weight C ∧ weight C≤cHi/(A.card:ℝ)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let raw:=rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS;
    let μraw:=FiniteLaw.pi raw;
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (A:Set V):ℝ)*Fintype.card U *
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (A:Set V))*(2*3)*((3:ℝ)^2*Bpot))));
    t+(3:ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ→
    1-a≤(μ.sigma ρ).probability E→1-b≤μraw.probability J→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δref href z.1 z.2)→
    1-a-b-err-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      let σ:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      (E z.1 ∧ (J σ ∧ ∀ (Q : SimpleGraph V) (H : V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z (2*p) pH density tR tH Ledit βe βh s j σ→
        ∀ vHub : {vHub : U // vHub ∉ Z}, ∀ v∈ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A vHub),
          |ordinaryLocalPotential (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
            (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A vHub))
            (fun C=>2*weight C/(D*(2*p)^3*pH^2)) v-
            ordinaryLocalTarget (P.induce (A:Set V)) (F.induce (A:Set V)) weight D v|≤ξ)) ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δref href σ z.2):=by
  intro μ raw μraw Bpot err hmargin hE hJ hC
  have hpRpos:0<2*p:=hpmin.trans_le hR
  have hpR1:2*p≤1:=by linarith
  have hpHpos:0<pH:=hpmin.trans_le hH
  have hDpos:0<D:=by have hh:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA; linarith
  have hcard:Fintype.card (A:Set V)=A.card:=by simp
  have hnA:0<Fintype.card (A:Set V):=by omega
  have hBpot:0<Bpot:=by dsimp [Bpot];positivity
  have hφ:∀ C:OrdinaryCycle (P.induce (A:Set V)) 3,
      0≤2*weight C/(D*(2*p)^3*pH^2) ∧
      2*weight C/(D*(2*p)^3*pH^2)≤Bpot/(Fintype.card (A:Set V):ℝ)^(3-1):=by
    have hh:=ordinary_triangle_potential_coefficient_bounds (P.induce (A:Set V)) pmin (2*p) pH D cLo cHi
      hnA hpmin hpmin1 hR hpR1 hH hH1 hcLo hcHi.le (by simpa only [hcard] using hDlo)
      (by simpa only [hcard] using hDhi) weight (by simpa only [hcard] using hweight)
    simpa only [Bpot] using hh
  have hh:=ordinary_induced_edited_potential_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E J a b c P F π j δref href hn hU (A:Set V) 3 (by omega) (by convert hnA using 1 <;> simp only [Set.fintypeCard_eq_ncard])
    (fun C=>2*weight C/(D*(2*p)^3*pH^2)) Bpot hBpot (by intro C; convert hφ C using 1 <;> simp only [Set.fintypeCard_eq_ncard]) t Ledit Ledit ht hE hJ hC
  dsimp only [err] at *
  simp only [Set.fintypeCard_eq_ncard, Nat.cast_ofNat] at hh ⊢
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨hEz,hJz,hpot⟩,hcut⟩:=hz
  refine ⟨⟨hEz,hJz,?_⟩,hcut⟩
  intro Q H profile
  have htarget:=ordinary_induced_hub_targets_from_cleanup P Q F H A Z π d hd j hconf hnoshort weight D (2*p) pH
    hpRpos hpR1 hpHpos hDpos.ne' q hq hQ s hs hS _ Bpot t Ledit ξ density tR tH βe βh profile hpot
    (by convert hmargin using 1 <;> simp only [hcard])
  exact htarget
end Oberwolfach
