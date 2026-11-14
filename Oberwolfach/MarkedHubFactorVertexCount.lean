module

public import Oberwolfach.MarkedHubFactorRootBijection

@[expose] public section
/-! Each wheel has one marked root and m+1 disjoint rim vertices, giving
 the manuscript's hubwise vertex-count identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_vertex_count
    {V U E K:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V)
    (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (S Y:Finset V) (hcover:M.biUnion (hubMarkedCycleVertices u)=S)
    (hYS:Y⊆S) (hmarked:∀x,Hₖ x u↔x∈Y) (hsep:∀x,Hₖ x u→¬H₀ x u):
    S.card=(m+1)*Y.card := by
  obtain ⟨select,hselected,honto⟩:=marked_hub_factor_root_bijection tail head ktail khead m b π H₀ Hₖ u M hM S Y hcover hYS hmarked hsep
  have himg:Finset.univ.image select=M:=by
    ext C
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩;exact (hselected x).1
    · intro hC;exact honto C hC
  have hmcard:M.card=Y.card:=by
    rw [←himg,Finset.card_image_of_injective _ select.injective]
    simp
  have hcard:∀C:HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u,
      (hubMarkedCycleVertices u C).card=m+1:=by
    intro C
    rw [hubMarkedCycleVertices,Finset.card_image_of_injective _
      (permutationSeparated_injective π b C.val C.property.1.1)]
    simp
  have hpair:(↑M:Set (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u)).PairwiseDisjoint (hubMarkedCycleVertices u):=by
    intro C hC D hD hne
    exact hM C hC D hD hne
  calc
    S.card=(M.biUnion (hubMarkedCycleVertices u)).card:=by rw [hcover]
    _=∑C∈M,(hubMarkedCycleVertices u C).card:=Finset.card_biUnion hpair
    _=M.card*(m+1):=by simp [hcard]
    _=Y.card*(m+1):=by rw [hmcard]
    _=(m+1)*Y.card:=Nat.mul_comm _ _
end Oberwolfach
