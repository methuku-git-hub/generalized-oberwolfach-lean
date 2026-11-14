module

public import Oberwolfach.FractionalSampleAveraging
public import Oberwolfach.OrdinaryCycleCountBounds
public import Oberwolfach.SubsetInclusion

@[expose] public section

/-! Uniform coefficient bounds from sampling a fixed number of vertices.
The cycle family consists of physical subgraphs; its support has exactly r
vertices, so the inclusion probability has exponent r. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_sample_support_probability {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω] {m r : ℕ}
    [Nonempty (FixedSubset V m)] (hm : m≤Fintype.card V)
    (μ : FiniteLaw Ω) (S : Ω → FixedSubset V m)
    (hlaw : μ.map S=FiniteLaw.uniform (FixedSubset V m))
    (J : Ω → SimpleGraph V) (hJ : ∀ ω,(J ω).support⊆(S ω).val)
    (good : Ω → Prop) (C : SimpleGraph V) (hC : IsEmbeddedCycle C r) :
    μ.probability (fun ω => good ω ∧ C≤J ω)≤((m:ℝ)/Fintype.card V)^r := by
  let T := C.support.toFinset
  have hT : T.card=r := hC.support_card
  calc
    _ ≤ μ.probability (fun ω => T⊆(S ω).val) := by
      apply finiteLaw_probability_mono
      intro ω hω x hx
      have hx' : x∈C.support := Set.mem_toFinset.mp hx
      exact hJ ω (SimpleGraph.support_mono hω.2 hx')
    _ = (FiniteLaw.uniform (FixedSubset V m)).probability (fun A => T⊆A.val) := by
      rw [← finiteLaw_map_probability μ S (fun A => T⊆A.val),hlaw]
    _ ≤ ((m:ℝ)/Fintype.card V)^T.card := fixedSubset_joint_inclusion_le hm T
    _ = _ := by rw [hT]

theorem fractional_cycle_sample_average_bounded {V Ω : Type*}
    [Fintype V] [DecidableEq V] [Fintype Ω] {m r : ℕ}
    [Nonempty (FixedSubset V m)] (hm : m≤Fintype.card V)
    (μ : FiniteLaw Ω) (S : Ω → FixedSubset V m)
    (hlaw : μ.map S=FiniteLaw.uniform (FixedSubset V m))
    (G : SimpleGraph V) (J : Ω → SimpleGraph V) (good : Ω → Prop)
    (hsub : ∀ ω,J ω≤G) (hJ : ∀ ω,(J ω).support⊆(S ω).val)
    (hf : ∀ ω,good ω → HasFractionalDecomposition (J ω) (fun C => IsEmbeddedCycle C r))
    (t : ℝ) (ht : 0<t) :
    ∃ a : SimpleGraph V → ℝ,
      (∀ C,0≤a C) ∧
      (∀ C,0<a C → C≤G ∧ IsEmbeddedCycle C r) ∧
      (∀ C,IsEmbeddedCycle C r → a C≤((m:ℝ)/Fintype.card V)^r/t) ∧
      (∀ u v,(∑ C,if C.Adj u v then a C else 0)=
        μ.probability (fun ω => good ω ∧ (J ω).Adj u v)/t) ∧
      (∀ u v,μ.probability (fun ω => (J ω).Adj u v)/t-
          (∑ C,if C.Adj u v then a C else 0)=
        μ.probability (fun ω => ¬good ω ∧ (J ω).Adj u v)/t) := by
  obtain ⟨a,ha,hs,hb,he,hloss⟩ := fractional_cycle_sample_average μ G J r good hsub hf t ht
  refine ⟨a,ha,hs,?_,he,hloss⟩
  intro C hC
  exact (hb C).trans (div_le_div_of_nonneg_right
    (cycle_sample_support_probability hm μ S hlaw J hJ good C hC) ht.le)

end Oberwolfach
