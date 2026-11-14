module

public import Oberwolfach.OrdinaryIsolatorConfigurations
public import Oberwolfach.RootedSetRetention

@[expose] public section

/-! Fixed potential isolator candidates at a hub. The two endpoint spokes
and the physical root edge are omitted from their survival requirements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]

abbrev OrdinaryIsolatorCandidate (P F : SimpleGraph V) (H : V → U → Prop)
    (k : ℕ) (θ α : ℝ) (x y : V) (u : U) :=
  {S : FixedSubset V k // (x∈S.val ∧ y∈S.val) ∧
    (∀ z∈S.val,z≠x → z≠y → H z u) ∧
    (∀ z∈S.val,∀ w∈S.val,¬F.Adj z w) ∧
    (∀ z∈S.val,(θ+α)*k≤((P.neighborFinset z∩S.val).card:ℝ))}

/-- On an outcome where the root edge and its endpoint spokes are present,
a surviving potential candidate is exactly an actual isolator configuration. -/
def ordinaryIsolatorCandidateEquiv [Fintype U]
    (P F : SimpleGraph V) (H : V → U → Prop) (k : ℕ) (θ α : ℝ) (x y : V) (u : U)
    (σ : Sym2 V → Bool) (hroot : (retainedGraph P σ).Adj x y) (hx : H x u) (hy : H y u) :
    {S : OrdinaryIsolatorCandidate P F H k θ α x y u //
      ∀ e∈rootOmittedInducedEdges P S.val.val s(x,y),σ e=true} ≃
    {C : OrdinaryIsolatorConfiguration P (retainedGraph P σ) F H k θ α x y // C.hub=u} where
  toFun S := ⟨{
    hub := u
    vertices := S.val.val
    endpoints := S.val.property.1
    rim_edges := by
      intro z t hzt
      obtain ⟨hp,hz,ht⟩ := (spanningRestriction_adj P S.val.val.val z t).mp hzt
      by_cases he : s(z,t)=s(x,y)
      · have hg : s(z,t)∈(retainedGraph P σ).edgeSet := by
          rw [he]
          exact hroot
        exact hg
      · exact ⟨hp,S.property _ ((mem_rootOmittedInducedEdges P S.val.val.val s(x,y) z t).mpr ⟨he,hp,hz,ht⟩)⟩
    spokes := by
      intro z hz
      by_cases hzx : z=x
      · simpa only [hzx] using hx
      by_cases hzy : z=y
      · simpa only [hzy] using hy
      exact S.val.property.2.1 z hz hzx hzy
    independent := S.val.property.2.2.1
    density := S.val.property.2.2.2 },rfl⟩
  invFun C := ⟨⟨C.val.vertices,C.val.endpoints,
    (by intro z hz _ _;rw [← C.property];exact C.val.spokes z hz),
    C.val.independent,C.val.density⟩,by
      intro e he
      induction e using Sym2.ind with
      | _ z t=>
        obtain ⟨hne,hp,hz,ht⟩ := (mem_rootOmittedInducedEdges P C.val.vertices.val s(x,y) z t).mp he
        exact (C.val.rim_edges ((spanningRestriction_adj P C.val.vertices.val z t).mpr ⟨hp,hz,ht⟩)).2⟩
  left_inv S := by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv C := by
    apply Subtype.ext
    apply OrdinaryIsolatorConfiguration.encoding_injective
    exact Prod.ext C.property.symm rfl

end Oberwolfach
