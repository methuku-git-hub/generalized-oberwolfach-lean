module

public import Oberwolfach.OrdinaryTriangleEventNamedAtLeast
public import Oberwolfach.OrdinaryRawHubPriorWithDeepProbability

@[expose] public section
/-! The full-host triangle event, fixed endpoint parent potentials, and
    deeper row and column profiles share the original raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 15000000
set_option synthInstance.maxSize 16384
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_full_raw_hub_parent_prior_probability
    (kmin d q₀ : ℕ) (hd : 2≤d)
    (α pstar ω βP ηP L K ωinner t εinner : ℝ)
    (hα : 0<α) (hα1 : α≤1)
    (hθ1 : max (1/2) (cycleThreshold 3)+α/2≤1)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω)
    (hβP : 0<βP) (hβmax : βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub : βP≤ω*pstar^9/4) (hηP : 0<ηP) (hL : 0≤L)
    (hK : 1≤K) (hωinner : 0<ωinner) (ht : 0<t) (hεinner : 0<εinner) :
    ∃ (k : ℕ) (βH c Bweight : ℝ), 5≤k ∧ kmin≤k ∧ 0<βH ∧ 0<c ∧ 0<Bweight ∧
    ∀ ηH : ℝ, 0<ηH → ∃ εhost : ℝ, 0<εhost ∧ ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [LinearOrder V], N≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀v,(max (1/2) (cycleThreshold 3)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ triangleWeight : OrdinaryCycle P 3→ℝ,
      (∀C,c/(Fintype.card V:ℝ)≤triangleWeight C ∧ triangleWeight C≤Bweight/(Fintype.card V:ℝ)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then triangleWeight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color : Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
      (A : Finset V), N≤A.card →
      (∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
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
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpstar.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
    1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)-3/(A.card:ℝ)^q₀≤
      μ.probability (OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Bweight pR pH t (εinner*A.card) (εinner*Z.card)) := by
  let θ : ℝ := max (1/2) (cycleThreshold 3)
  have hθ : cycleThreshold 3≤θ := le_max_right _ _
  obtain ⟨k,βH,c,Bweight,hk,hkmin,hβH,hc,hB,htri⟩:=ordinary_full_host_and_triangle_inputs_named_at_least
    kmin d hd θ α pstar ω βP ηP L hθ hα hα1 hθ1 hpstar hpstar1 hω hβP hβmax hβhub hηP hL
  refine ⟨k,βH,c,Bweight,hk,hkmin,hβH,hc,hB,?_⟩
  intro ηH hηH
  obtain ⟨εhost,hεhost,Ntri,htri⟩:=htri ηH hηH
  obtain ⟨Ndeep,hdeep⟩:=ordinary_raw_hub_prior_with_deep_probability K ωinner pstar t εinner
    hK hωinner hpstar ht hεinner d q₀ hd
  refine ⟨εhost,hεhost,max Ntri Ndeep,?_⟩
  intro V _ _ hn P hP
  obtain ⟨triangleWeight,hweights,hedge,htri⟩:=htri V (le_trans (le_max_left _ _) hn) P hP
  refine ⟨triangleWeight,?_,hedge,?_⟩
  · simpa only [show (3:ℕ)-2=1 by norm_num, pow_one] using hweights
  intro U Γ Color _ _ _ _ A hA hdeg
  obtain ⟨endpointWeight,hendpoint,hprior⟩:=hdeep V U Γ Color P A (le_trans (le_max_right _ _) hA) hdeg
  refine ⟨endpointWeight,hendpoint,?_⟩
  intro F π Z hUlo hUhi hV hU hZ hFdeg hF hπ pR pH D₀ hpR0 hpR1 hpH0 hpH1 hDlo hreg hbal
    q hq hQ s hs hS j hj μ
  have ht := htri U Γ Color hUlo hUhi F π hFdeg hF hπ pR pH D₀ hpR0 hpR1 hpH0 hpH1 hDlo hreg hbal q hq hQ s hs hS j hj
  have hb := hprior F π Z hV hU hZ hF hπ pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
    k triangleWeight α pstar βP ηP ηH βH c Bweight (1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2) ht
  exact hb
end Oberwolfach
