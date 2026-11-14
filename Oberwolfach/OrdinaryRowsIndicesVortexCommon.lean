module

public import Oberwolfach.OrdinaryRowsVortex
public import Oberwolfach.OrdinaryIndicesVortex
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! All ordinary row and separated hub tests on every fixed vortex level
hold simultaneously on the same ambient sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_rows_indices_vortex_common
    (h d:ℕ) (hd:2≤d) (εR εH K η χ:ℝ) (hεR:0<εR) (hεH:0<εH) (hK:1≤K)
    (hη:0<η) (hη1:η<1) (hχ:0<χ):
    ∃M₀:ℕ,1≤M₀ ∧ ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→permutationConflictGraph π (3*d)≤F→
    ∀(f:∀i,W i↪V) (g:∀i,Z i↪U) (ρ:∀i,Equiv.Perm (W i)),
      (∀i x,f i (ρ i x)=π (f i x))→
    ∀(A:∀i,Finset (W i)) (B:∀i,Finset (Z i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i≤L,M₀≤(B i).card)→
      (∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
      (∀i<L,((B (i+1)).card:ℝ)≤η*(B i).card)→
      (∀i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card)→
      (∀i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card)→
      (∀i≤L,(Fintype.card (W i):ℝ)≤K*(B i).card)→
    ∀(p:ℝ) (hp:0≤p) (hp1:p≤1)
      (q:U→Γ→ℝ) (hq:∀u a,0≤q u a) (hQ:∀u,∑a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑a,q u a)) (j:Color) (pH:ℝ) (hj:∀u,s u j=pH),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i≤L,
        RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p (fun z=>s (g i z)) j (εR*(A i).card)
          (ordinaryRawRestrictPair (f i) (g i) σ) ∧
        RawOrdinaryDomainIndices (F.comap (f i)) (ρ i) d h (B i) pH j (εH*(B i).card)
          (ordinaryRawRestrictPair (f i) (g i) σ)):=by
  obtain ⟨MR,hMR,hrow⟩:=ordinary_rows_vortex_event h d hd εR K η (χ/2) hεR hK hη hη1 (by positivity)
  obtain ⟨MH,hMH,hcol⟩:=ordinary_indices_vortex_event h d hd εH K η (χ/2) hεH hK hη hη1 (by positivity)
  refine ⟨max MR MH,by omega,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F π hnoshort hF f g ρ hcomm A B L hnA hnB hstepA hstepB hWA hZA hWB
    p hp hp1 q hq hQ s hs hS j pH hj
  let μ:FiniteLaw (RawWheelOutcome V U Γ Color):=
    FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)
  let Row:=fun σ:RawWheelOutcome V U Γ Color=>∀i≤L,
    RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p (fun z=>s (g i z)) j (εR*(A i).card)
      (ordinaryRawRestrictPair (f i) (g i) σ)
  let Col:=fun σ:RawWheelOutcome V U Γ Color=>∀i≤L,
    RawOrdinaryDomainIndices (F.comap (f i)) (ρ i) d h (B i) pH j (εH*(B i).card)
      (ordinaryRawRestrictPair (f i) (g i) σ)
  have hR:=hrow V U Γ Color W Z P π hnoshort f g ρ hcomm A L
    (by intro i hi;have hh:=hnA i hi;omega) hstepA hWA hZA p hp hp1 q hq hQ s hs hS j
  have hC:=hcol V U Γ Color W Z F π hnoshort hF f g ρ hcomm B L
    (by intro i hi;have hh:=hnB i hi;omega) hstepB hWB p hp hp1 q hq hQ s hs hS j pH hj
  have hi:=finiteLaw_intersection_lower μ Row Col (χ/2) (χ/2) hR hC
  have hm:μ.probability (fun σ=>Row σ∧Col σ)≤μ.probability (fun σ=>∀i≤L,
      RawOrdinaryRows (P.comap (f i)) (ρ i) d h (A i) p (fun z=>s (g i z)) j (εR*(A i).card)
        (ordinaryRawRestrictPair (f i) (g i) σ) ∧
      RawOrdinaryDomainIndices (F.comap (f i)) (ρ i) d h (B i) pH j (εH*(B i).card)
        (ordinaryRawRestrictPair (f i) (g i) σ)):=by
    apply finiteLaw_probability_mono
    intro σ hσ i hi'
    exact ⟨hσ.1 i hi',hσ.2 i hi'⟩
  linarith only [hi,hm]
end Oberwolfach
