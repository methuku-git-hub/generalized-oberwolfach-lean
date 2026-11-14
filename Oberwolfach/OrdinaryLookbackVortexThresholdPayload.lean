module

public import Oberwolfach.VortexLookbackPermutation

@[expose] public section
/-! Combine the actual two-step lookback vortex and its preserving
permutation with an arbitrary beta-dependent size payload. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryLookbackVortexAt (β ε ρ₀:ℝ) (d m₀:ℕ):Prop :=
  ∀(V U:Type) [Fintype V] [Fintype U] (P:SimpleGraph V) (D mv:ℕ),
    P.IsRegularOfDegree D→(Fintype.card V:ℝ)/2≤D→
    ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤mv→mv≤Fintype.card V→
  ∃Q:VortexLookback U P D β ε mv 2,∃π:Equiv.Perm V,
    (∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i) ∧
    (∀x l,0<l→l<2*d+1→(π^l) x≠x)

theorem ordinary_lookback_vortex_threshold_payload
    (d:ℕ) (ε ρ₀ βcap δInitial δDeep δedit:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCert mVortex:ℕ,mCert≤m₀ ∧ mVortex≤m₀ ∧ Payload β mCert Nmin ∧
        OrdinaryLookbackVortexAt β ε ρ₀ d mVortex :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mVortex,_,hvortex⟩:=vortex_lookback_with_permutation_exists hβ hε hε1 hρ₀ 2 (2*d+1) (by omega)
  refine ⟨max mCert mVortex,Nmin,mCert,mVortex,le_max_left _ _,le_max_right _ _,hcert,?_⟩
  intro V U _ _ P D mv hreg hhalf hρlo hρhi hm hmn
  exact hvortex V U P D mv hreg hhalf hρlo hρhi hm hmn
end Oberwolfach
