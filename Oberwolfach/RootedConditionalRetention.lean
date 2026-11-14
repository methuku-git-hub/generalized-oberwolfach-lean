module

public import Oberwolfach.RootedSetRetentionCommon
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Configuration families may depend on the first exposure. The second
physical-edge law is unchanged, and one event controls all tests together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedInducedSurvivalSum_two_exposures
    {V J Ω : Type*} [Fintype V] [DecidableEq V] [Fintype J] [Fintype Ω]
    {I : Ω → J → Type*} [∀ ω j,Fintype (I ω j)] {k : ℕ} (P : SimpleGraph V)
    (S : ∀ ω j,I ω j → FixedSubset V k) (hinj : ∀ ω j,Function.Injective (S ω j))
    (x y : J → V) (hxy : ∀ j,x j≠y j) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ ω j i,x j∈(S ω j i).val ∧ y j∈(S ω j i).val)
    (ν : FiniteLaw Ω) (Good : Ω → Prop) (b : ℝ) (hgood : 1-b≤ν.probability Good)
    (μ : Sym2 V → FiniteLaw Bool) (p t : ℝ) (c : J → ℝ)
    (hp : 0≤p) (hp1 : p≤1) (ht : 0<t)
    (hprob : ∀ e∈P.edgeFinset,p≤(μ e).mass true)
    (hmany : ∀ ω,Good ω → ∀ j,c j*(Fintype.card V:ℝ)^(k-2)≤Fintype.card (I ω j)) :
    1-b-Fintype.card J*(2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V)))≤
      (ν.prod (FiniteLaw.pi μ)).probability (fun z=>Good z.1 ∧ ∀ j,
        p^(k^2)*c j-t<rootedInducedSurvivalSum P (S z.1 j) s(x j,y j) z.2) := by
  have hh := finiteLaw_product_good_lower ν (FiniteLaw.pi μ) Good
    (fun ω σ=>∀ j,p^(k^2)*c j-t<rootedInducedSurvivalSum P (S ω j) s(x j,y j) σ)
    b ((Fintype.card J:ℝ)*(2*Real.exp (-2*t^2/((k:ℝ)^2/Fintype.card V))))
    (by positivity) hgood
    (by
      intro ω hω
      exact rootedInducedSurvivalSum_common_event P (S ω) (hinj ω) x y hxy hk hn (hroot ω)
        μ p t c hp hp1 ht hprob (hmany ω hω))
  convert hh using 1 <;> congr!

end Oberwolfach
