module

public import Oberwolfach.OrdinaryFullRawHubPriorProbability
public import Oberwolfach.OrdinaryReferenceAndInnerRimProbability
public import Oberwolfach.OrdinaryEndpointDegreeFromInnerDensity

@[expose] public section
/-! Full-host triangle, endpoint, deep-profile and both oriented rim and
    reference-cut events on the same original outcome and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_raw_parent_reference_rim_joint_probability
    (kmin d q₀ : ℕ) (hd : 2≤d)
    (α αinner pstar ω βP ηP L K ωinner t εinner : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hαinner : 0<αinner) (hαinner1 : αinner≤1/2)
    (hθ1 : max (1/2) (cycleThreshold 3)+α/2≤1)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω)
    (hβP : 0<βP) (hβmax : βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub : βP≤ω*pstar^9/4) (hηP : 0<ηP) (hL : 0≤L)
    (hK : 1≤K) (hωinner : 0<ωinner) (ht : 0<t) (hεinner : 0<εinner) :
    ∃ (δ h : ℝ) (k : ℕ) (βH c Bweight : ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 5≤k ∧ kmin≤k ∧ 0<βH ∧ 0<c ∧ 0<Bweight ∧
    ∀ ηH : ℝ, 0<ηH → ∃ εhost : ℝ, 0<εhost ∧ ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [LinearOrder V], N≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀v,(max (1/2) (cycleThreshold 3)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ triangleWeight : OrdinaryCycle P 3→ℝ,
      (∀C,c/(Fintype.card V:ℝ)≤triangleWeight C ∧ triangleWeight C≤Bweight/(Fintype.card V:ℝ)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then triangleWeight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color : Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
      (A : Finset V), N≤A.card → ∀ density : ℝ,
      cycleThreshold 3≤density → (1/2:ℝ)+αinner≤density →
      (∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∃ endpointWeight : V→Sym2 (V⊕U)→ℝ, EndpointPhysicalParentWeights P A Aᶜ endpointWeight ∧
    ∀ (F : SimpleGraph V) (π : Equiv.Perm V) (Z : Finset U),
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
      (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card → ωinner*A.card≤(Z.card:ℝ) →
      (∀v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ (pR pH D₀ : ℝ) (hpR0 : pstar≤pR) (hpR1 : pR≤1), pstar≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D₀ → (∀v,|(P.degree v:ℝ)-D₀|≤εhost*Fintype.card V) →
      pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q : U→Γ→ℝ) (hq : ∀u g,0≤q u g) (hQ : ∀u,∑g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀u j,0≤s u j)
      (hS : ∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j : Color), (∀u,s u j=pH) →
    let μ:=(FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpstar.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin));
    1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)-3/(A.card:ℝ)^q₀-
      1/(Fintype.card V:ℝ)^q₀-1/(A.card:ℝ)^q₀≤
      μ.probability (fun z=>OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Bweight pR pH t (εinner*A.card) (εinner*Z.card) z.1 ∧
        OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2 ∧
        OrdinaryInducedRimCutEvent A (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar) := by
  obtain ⟨δ,h,hδ,hδsmall,hh,href⟩:=ordinary_reference_and_inner_rim_high_probability (α/2) αinner pstar ω
    (by positivity) (by linarith) hαinner hαinner1 hpstar hpstar1 hω
  obtain ⟨k,βH,c,Bweight,hk,hkmin,hβH,hc,hB,hraw⟩:=ordinary_full_raw_hub_parent_prior_probability
    kmin d q₀ hd α pstar ω βP ηP L K ωinner t εinner hα hα1 hθ1 hpstar hpstar1 hω
    hβP hβmax hβhub hηP hL hK hωinner ht hεinner
  refine ⟨δ,h,k,βH,c,Bweight,hδ,hδsmall,hh,hk,hkmin,hβH,hc,hB,?_⟩
  intro ηH hηH
  obtain ⟨εhost,hεhost,Nraw,hraw⟩:=hraw ηH hηH
  obtain ⟨Nref,href⟩:=href L hL d q₀ hd
  refine ⟨εhost,hεhost,max Nraw Nref,?_⟩
  intro V _ _ hn P hP
  obtain ⟨triangleWeight,hweights,hedge,hraw⟩:=hraw V (le_trans (le_max_left _ _) hn) P hP
  refine ⟨triangleWeight,hweights,hedge,?_⟩
  intro U Γ Color _ _ _ _ A hA density hdensity hhalf hmin
  have hparent:=ordinary_endpoint_degree_from_inner_density P A density hdensity hmin
  obtain ⟨endpointWeight,hendpoint,hraw⟩:=hraw U Γ Color A (le_trans (le_max_left _ _) hA) hparent
  refine ⟨endpointWeight,hendpoint,?_⟩
  intro F π Z hUlo hUhi hV hU hZ hFdeg hF hπ pR pH D₀ hpR0 hpR1 hpH0 hpH1 hDlo hreg hbal
    q hq hQ s hs hS j hj μ
  have hP' : ∀v,(1/2+α/2)*Fintype.card V≤(P.degree v:ℝ) := by
    intro v
    have hcoef : (1/2:ℝ)+α/2≤max (1/2) (cycleThreshold 3)+α := by
      have hh := le_max_left (1/2:ℝ) (cycleThreshold 3)
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef (by positivity : (0:ℝ)≤Fintype.card V)).trans (hP v)
  have hraw' := hraw F π Z hUlo hUhi hV hU hZ hFdeg hF hπ pR pH D₀ hpR0 hpR1 hpH0 hpH1 hDlo hreg hbal q hq hQ s hs hS j hj
  have href' := href V U Γ Color (le_trans (le_max_right _ _) hn) hUlo hUhi P F A
    (le_trans (le_max_right _ _) hA) hP' hFdeg density hhalf (fun v _=>hmin v) π hπ pR pH
    (hpstar.le.trans hpR0) hpR1 hpR0 hpH0 q hq hQ s hs hS j hj
  let E : RawWheelOutcome V U Γ Color→Prop := OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
    α pstar βP ηP ηH βH c Bweight pR pH t (εinner*A.card) (εinner*Z.card)
  let C : RawWheelOutcome V U Γ Color×(Sym2 V→Bool)→Prop := fun z=>
    OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2 ∧
    OrdinaryInducedRimCutEvent A (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar
  have hE : 1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)-3/(A.card:ℝ)^q₀≤μ.probability (fun z=>E z.1) := by
    rw [finiteLaw_prod_first_probability]
    exact hraw'
  have hC : 1-1/(Fintype.card V:ℝ)^q₀-1/(A.card:ℝ)^q₀≤μ.probability C := by
    convert href' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hboth := (sub_le_sub_right hE (1/(Fintype.card V:ℝ)^q₀+1/(A.card:ℝ)^q₀)).trans
    (finiteLaw_good_intersection μ (fun z=>E z.1) C (1/(Fintype.card V:ℝ)^q₀+1/(A.card:ℝ)^q₀) (by linarith))
  convert hboth using 1 <;> ring
end Oberwolfach
