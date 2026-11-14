module

public import Oberwolfach.OrdinaryFixedVortexNonrootNumericAt
public import Oberwolfach.OrdinaryVortexBufferedDomains
public import Oberwolfach.OrdinaryNonrootNumericSmallerDeep

@[expose] public section
/-! Specialize the shared fixed-vortex numeric choices to the initial buffered domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_numeric_from_shared
    (ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex:ℝ)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex)
    (ε:ℝ) (hε:0<ε) (hεv:ε≤εvortex) (aLoad:ℝ) (ha:0<aLoad)
    (β:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (d n₀:ℕ):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (pH εR εH Ledit:ℝ),pmin≤pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→
      Ledit≤ζlimit*(markedVortexInnerVertices Q 0).card→
    OrdinaryNonrootNumericInputs
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q 0))
      (markedVortexInnerVertices Q 0) (ordinaryVortexBufferedVertices Q 0 2)
      (markedVortexInnerHubs Q 0) (ordinaryVortexBufferedHubs Q 0 2) n₀ d
      (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href :=by
  obtain ⟨v₀,hv₀,hnum⟩:=hnum ε hε hεv aLoad ha β hβ hβ1 d n₀
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  have hh:=hnum V U P D vsize hreg hn hD hρlo hρhi hv Q π hπ 0 Q.length_pos pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL
  have hs:=ordinary_vortex_buffered_nested Q 0 2 (by omega)
  have ht:=ordinary_nonroot_numeric_inputs_smaller_deep _ _ _ _ _ _ _ n₀ d (ρ₀/8) a ρ θ aLoad ζlimit ε δcut ζcut εcut pH εR εH Ledit href hs.1 hs.2.1 hh
  convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
