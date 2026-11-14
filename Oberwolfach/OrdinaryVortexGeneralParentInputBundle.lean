module

public import Oberwolfach.OrdinaryVortexGeneralParentInputsFromOriginal

@[expose] public section
/-! Name the full-parent deterministic inputs separately from the sampled
selector so that Lean can check the two applications in different modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ}

def OrdinaryVortexGeneralParentInputBundle
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (mWheel d L M:ℕ) (α ρ₀ εTri pR pH:ℝ):Prop:=by
  let W:=markedVortexVertexType Q
  let Z:=markedVortexHubType Q
  let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding
  let ρ:=markedVortexPermutation Q π hπ
  let F:=permutationConflictGraph π (3*d)
  let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
  exact (∀i ≤ L,M ≤ Fintype.card (W i)) ∧
    (∀i<L,(Fintype.card (W (i+1)):ℝ) ≤ ε*Fintype.card (W i)) ∧
    (∀i ≤ L,(ρ₀/16)*Fintype.card (W i) ≤ (Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i) ≤ Fintype.card (W i)) ∧
    (∀i ≤ L,∀v,(max (1/2) (cycleThreshold (mWheel+1))+α)*Fintype.card (W i) ≤ ((P.comap (f i)).degree v:ℝ)) ∧
    (∀i ≤ L,∀v,((F.comap (f i)).degree v:ℝ) ≤ 2*(3*d)) ∧
    (∀i ≤ L,permutationConflictGraph (ρ i) (3*d) ≤ F.comap (f i)) ∧
    (∀i ≤ L,∀x l,0<l → l<2*d+1 → ((ρ i)^l) x≠x) ∧
    (∀i ≤ L,(Fintype.card (W i):ℝ)/2 ≤ Dlevel i) ∧
    (∀i ≤ L,∀v,|((P.comap (f i)).degree v:ℝ)-Dlevel i| ≤ εTri*Fintype.card (W i)) ∧
    (∀i ≤ L,pR*Dlevel i=2*(Fintype.card (Z i):ℝ)*pH)

theorem ordinary_vortex_general_parent_input_bundle_from_original
    (mWheel:ℕ) (hm:2 ≤ mWheel) (P:SimpleGraph V) (D mv d:ℕ) (β ε α ρ₀ pstar εTri pR pH:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hα:0<α)
    (hdegree:(max (1/2) (cycleThreshold (mWheel+1))+2*α)*Fintype.card V ≤ D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (hβ:0 ≤ β) (hβα:β ≤ α/4) (hβ1:β ≤ 1/4) (hβε:β ≤ εTri)
    (hε:0<ε) (hε1:ε ≤ 1) (hερ:ε ≤ ρ₀/16) (hmv:0<mv)
    (hnoshort:∀x t,0<t → t<2*d+1 → (π^t) x≠x)
    (hpR:pstar ≤ pR) (hpR1:pR ≤ 1) (hpH:pstar ≤ pH) (hpH1:pH ≤ 1)
    (hpEq:pR=initialIndexDensity U D*pH) (L M:ℕ) (hL:L<Q.length) (hM:(M:ℝ) ≤ ε*mv/2):
    OrdinaryVortexGeneralParentInputBundle Q π hπ mWheel d L M α ρ₀ εTri pR pH :=by
  have h:=ordinary_vortex_general_parent_inputs_from_original mWheel hm P D mv d β ε α ρ₀ pstar εTri pR pH Q π hπ
    hreg hn hα hdegree hρ₀ hρlo hρhi hβ hβα hβ1 hβε hε hε1 hερ hmv hnoshort hpR hpR1 hpH hpH1 hpEq L M hL hM
  exact h.2
end Oberwolfach
