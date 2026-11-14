module

public import Oberwolfach.OrdinaryVortexFirstHubInnerRatio
public import Oberwolfach.OrdinaryFirstVortexReservoirSize
public import Oberwolfach.FirstVortexIndicesNonempty

@[expose] public section

/-! First-level vortex geometry supplies the size and positivity conditions
for the reservoir and both local concentration tests. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_local_event_geometry_eventually
    (ε εabs εv:ℝ) (hε:0<ε) (habs:ε≤εabs) (hv:ε≤εv) (Nlocal:ℕ):
    ∃N:ℕ,1≤N ∧ ∀{V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β ρ₀:ℝ) (Q:Vortex U P D β ε mv),
      P.IsRegularOfDegree D→0<Fintype.card V→0<D→(Fintype.card V:ℝ)/2≤D→0<mv→
      0<ρ₀→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      0≤β→β≤1/4→Fintype.card U≤Fintype.card V→N≤Fintype.card V→
      Nlocal≤(Q.extendedVertices 1).card ∧ 0<(Q.extendedIndices 1).card ∧
      (Q.extendedIndices 1).card≤(Q.extendedVertices 1).card ∧
      ((Q.extendedIndices 1).card:ℝ)≤(2/ε)*(Q.extendedVertices 1).card ∧
      ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V ∧
      ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V ∧
      ((Q.extendedVertices 1).card:ℝ)≤εv*Fintype.card V ∧
      ((Q.extendedIndices 1).card:ℝ)≤εv*Fintype.card V :=by
  obtain ⟨N,hN,hlarge⟩:=ordinary_vortex_inner_eventually_large ε hε Nlocal
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ P D mv β ρ₀ Q hreg hn hD hDlo hm hρ₀ hρlo hρhi hβ hβ1 hU hnN
  have hlarge':=hlarge P D mv β Q hm hnN
  have hnonempty:=Q.first_inner_indices_nonempty hreg hn hDlo hρ₀ hρlo hβ hβ1 hε hm
  have hsize:=Q.extended_index_size_upper hreg hn hD hε.le hρhi 1
  have hratio:=ordinary_vortex_first_hub_inner_ratio P D mv β ε Q hε hm hU (Q.extendedIndices 1)
  have hsmall:=ordinary_first_vortex_reservoir_size P D mv β ε Q hreg hn hD hε hm hρhi εabs εv habs hv
  have hcard:(Q.extendedIndices 1).card≤(Q.extendedVertices 1).card:=by omega
  exact ⟨hlarge',hnonempty.card_pos,hcard,hratio,hsmall.1,hsmall.2.1,hsmall.2.2.1,hsmall.2.2.2⟩
end Oberwolfach
