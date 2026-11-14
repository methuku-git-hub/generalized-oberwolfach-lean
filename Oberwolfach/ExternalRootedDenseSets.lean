module

public import Oberwolfach.DenseRootedSetsWithin
public import Oberwolfach.EnlargedNeighbourDensity

@[expose] public section

/-! Many admissible bounded sets through roots which need not belong to
the sampled neighbourhood. All degree assumptions use the original roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem external_rooted_dense_sets (s : ℕ) (α β : ℝ) (hα : 0<α) (hα1 : α≤1) (hβ : 0<β) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → ∃ c : ℝ,0<c ∧
    ∀ L : ℝ,0≤L → ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (A Z : Finset V),Z.card=s → β*Fintype.card V≤(A.card:ℝ) →
    ∀ θ : ℝ,0≤θ → θ≤1 →
    (∀ v∈A∪Z,(θ+α/2)*(A.card:ℝ)≤((P.neighborFinset v∩A).card:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) → (∀ x∈Z,∀ y∈Z,¬F.Adj x y) →
    c*(Fintype.card V:ℝ)^k≤
      Fintype.card {S : FixedSubset V (s+k) // Z⊆S.val ∧ S.val⊆A∪Z ∧
        (∀ v∈S.val,(θ+α/4)*(s+k:ℝ)≤((P.neighborFinset v∩S.val).card:ℝ)) ∧
        (∀ x∈S.val,∀ y∈S.val,¬F.Adj x y)} := by
  obtain ⟨K,hK⟩ := dense_rooted_sets_within s (α/8) (by positivity)
  refine ⟨K,?_⟩
  intro k hk
  let c : ℝ := β^k/((2:ℝ)^(k+1)*k.factorial)
  refine ⟨c,by dsimp [c];positivity,?_⟩
  intro L hL
  obtain ⟨N₀,hN₀⟩ := hK k hk L hL
  obtain ⟨N₁,hN₁⟩ := eventually_constant_le_linear (N₀:ℝ) β hβ
  obtain ⟨N₂,hN₂⟩ := eventually_constant_le_linear (16*(s:ℝ)) (α*β) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ hn P F A Z hZ hA θ hθ hθ1 hP hF hind
  have hN : N₀≤(A∪Z).card := by
    have hh := hN₁ (Fintype.card V) (le_trans (le_max_left _ _) hn)
    have ha : (A.card:ℝ)≤(A∪Z).card := by exact_mod_cast Finset.card_le_card Finset.subset_union_left
    exact_mod_cast hh.trans (hA.trans ha)
  have hmargin : ((θ+α/4)+(α/4)/2)*(Z.card:ℝ)≤(α/4)*(A.card:ℝ)/2 := by
    have hh := hN₂ (Fintype.card V) (le_trans (le_max_right _ _) hn)
    have ha := mul_le_mul_of_nonneg_left hA hα.le
    have hcoeff : (θ+α/4)+(α/4)/2≤2 := by linarith only [hθ1,hα1]
    have hb := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α:=ℝ) s)
    rw [hZ]
    nlinarith only [hh,ha,hb]
  have hp := enlarged_neighbour_density P A Z (θ+α/4) (α/4)
    (by positivity) hmargin
    (by intro v hv;convert hP v hv using 1 <;> ring)
  have hh := hN₀ V P F (A∪Z) Z hN hZ Finset.subset_union_right (θ+α/4)
    (by intro v hv;convert hp v hv using 1 <;> ring) hF hind
  let Strong := {S : FixedSubset V (s+k) // Z⊆S.val ∧ S.val⊆A∪Z ∧
    (∀ v∈S.val,((θ+α/4)+(α/8)/2)*(s+k:ℝ)<((P.neighborFinset v∩S.val).card:ℝ)) ∧
    (∀ x∈S.val,∀ y∈S.val,¬F.Adj x y)}
  let Weak := {S : FixedSubset V (s+k) // Z⊆S.val ∧ S.val⊆A∪Z ∧
    (∀ v∈S.val,(θ+α/4)*(s+k:ℝ)≤((P.neighborFinset v∩S.val).card:ℝ)) ∧
    (∀ x∈S.val,∀ y∈S.val,¬F.Adj x y)}
  let f (S : Strong) : Weak := ⟨S.val,S.property.1,S.property.2.1,
    (by
      intro v hv
      have hd := S.property.2.2.1 v hv
      have hm : 0≤(α/16)*(s+k:ℝ) := by positivity
      nlinarith only [hd,hm]),S.property.2.2.2⟩
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    exact congrArg (fun a : Weak=>a.val) he
  have hc : (Fintype.card Strong:ℝ)≤Fintype.card Weak := by
    exact_mod_cast Fintype.card_le_of_injective f hinj
  have hsize : β*Fintype.card V≤((A∪Z).card:ℝ) := hA.trans (by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_left (s₁:=A) (s₂:=Z)))
  have hscale : c*(Fintype.card V:ℝ)^k≤((A∪Z).card:ℝ)^k/((2:ℝ)^(k+1)*k.factorial) := by
    dsimp [c]
    calc
      _ = (β*Fintype.card V)^k/((2:ℝ)^(k+1)*k.factorial) := by rw [mul_pow];ring
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hsize k) (by positivity)
  exact hscale.trans (hh.trans hc)

end Oberwolfach
