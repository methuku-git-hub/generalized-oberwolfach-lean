module

public import Oberwolfach.RootedSetRetention
public import Oberwolfach.ProductFailureBounds

@[expose] public section

/-! One physical-edge event for every prescribed pair and hub in a fixed
finite family; no independence between the different counts is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedInducedSurvivalSum_common_event {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]
    {I : J → Type*} [∀ j,Fintype (I j)] {k : ℕ} (P : SimpleGraph V)
    (S : ∀ j,I j → FixedSubset V k) (hinj : ∀ j,Function.Injective (S j))
    (x y : J → V) (hxy : ∀ j,x j≠y j) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ j i,x j∈(S j i).val ∧ y j∈(S j i).val)
    (μ : Sym2 V → FiniteLaw Bool) (p t : ℝ) (c : J → ℝ)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : ∀ j,c j*(Fintype.card V:ℝ)^(k-2)≤Fintype.card (I j)) :
    1-Fintype.card J*(2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ j,
        p^(k^2)*c j-t<rootedInducedSurvivalSum P (S j) s(x j,y j) σ) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) (Finset.univ : Finset J)
    (fun j σ=>rootedInducedSurvivalSum P (S j) s(x j,y j) σ≤p^(k^2)*c j-t)
    (fun _=>2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)))
    (by
      intro j _
      exact rootedInducedSurvivalSum_lower_tail P (S j) (hinj j)
        (x j) (y j) (hxy j) hk hn (hroot j) μ p (c j) t hp hp1 ht hprob (hmany j))
  simpa only [Finset.mem_univ,forall_const,not_le,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] using hh

end Oberwolfach
