module

public import Oberwolfach.PartitionColourMatching
public import Oberwolfach.WeightedEdgePartition

@[expose] public section

/-! Complete random-edge-partition and colour-class-selection construction.
All simultaneous failure bounds are numerical hypotheses, not assumed
existence of a matching, colouring or favourable sampling outcome. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem weighted_matching_on_disjoint_parts
    (k : ℕ) (hk : 0<k) (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1/2)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D₀ : ℕ, ∀ D B : ℕ, D₀≤D → (B : ℝ)≤(D : ℝ)^(1-δ) →
      ∀ (V E I C A : Type) [Fintype V] [Fintype E] [Fintype I] [Fintype C] [Fintype A]
        [Nonempty C], ∀ (R : E → Finset V) (part : E → I),
      (∀ e,(R e).card=k) →
      (∀ e f,part e≠part f → Disjoint (R e) (R f)) →
    ∀ (w : A → E → ℝ) (b : A → ℝ) (W : I → A → ℝ)
    (d β : ℝ) (T : I → A → ℝ) (s₀ s₁ s₂ : ℝ)
    (hb : ∀ a,0<b a) (hw : ∀ a e,0≤w a e ∧ w a e≤b a)
    (hdegree : ∀ i v,((Finset.univ.filter (fun e=>part e=i ∧ v∈R e)).card : ℝ)≤d)
    (hcodeg : ∀ i v u,v≠u →
      ((Finset.univ.filter (fun e=>part e=i ∧ v∈R e ∧ u∈R e)).card : ℝ)≤β)
    (hβ : 0≤β) (hW : ∀ i a,(∑ e,if part e=i then w a e else 0)≤W i a)
    (hs₀ : 0≤s₀) (hs₁ : 0≤s₁) (hs₂ : 0≤s₂)
    (hsmall :
      (∑ _i : I,∑ _v : V,∑ _c : C,Real.exp (d/Fintype.card C*(Real.exp s₀-1)-s₀*((D : ℝ)+1)))+
      ((∑ _i : I,∑ _v : V,∑ _u : V,∑ _c : C,Real.exp (β/Fintype.card C*(Real.exp s₁-1)-s₁*((B : ℝ)+1)))+
      (∑ i : I,∑ a : A,∑ _c : C,Real.exp ((W i a/Fintype.card C*(Real.exp s₂-1)-s₂*T i a)/b a)))<1)
    (t : A → ℝ) (ht : ∀ a,0≤t a)
    (hselect : (∑ a,2*Real.exp (-2*(t a)^2/(∑ i,(T i a)^2)))<1),
    ∃ M : Finset E,
      (∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
      ∀ a,|(∑ e∈M,w a e)-(∑ e,w a e)/
        ((Fintype.card C : ℝ)*⌈(1+ε)*(D : ℝ)⌉₊)|<t a := by
  classical
  obtain ⟨N,hN⟩ := partition_colouring_weighted_matching k hk ε δ hε hε1 hδ hδ1
  refine ⟨N,?_⟩
  intro D B hD hB V E I C A _ _ _ _ _ _ R part hsize hparts w b W d β T
    s₀ s₁ s₂ hb hw hdegree hcodeg hβ hW hs₀ hs₁ hs₂ hsmall t ht hselect
  obtain ⟨split,hdeg,hcode,hweight⟩ := weighted_edge_partition_exists (C:=C)
    R part w b W d β D B T s₀ s₁ s₂ hb hw hdegree hcodeg hβ hW hs₀ hs₁ hs₂ hsmall
  exact hN D B hD hB V E I C A R part split hsize hparts hdeg hcode
    w (fun a i=>T i a) t (fun a e=>(hw a e).1) (fun a i c=>(hweight i a c).le) ht hselect

end Oberwolfach
