module

public import Oberwolfach.MarkedPermutationEmbedding
public import Oberwolfach.HubCommonPathCycles
public import Oberwolfach.MarkedFactorPhysical

@[expose] public section

/-! Exact transport of hub cycles from an invariant inner row domain to
its ambient row type. All arc identifiers, spoke types and coefficients
remain unchanged. Vertices outside the image have no image spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U E K:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

def spokeRelationImage (f:W↪V) (H:W→U→Prop) (v:V) (u:U):Prop:=∃ x,f x=v∧H x u

theorem spokeRelationImage_at (f:W↪V) (H:W→U→Prop) (x:W) (u:U):
    spokeRelationImage f H (f x) u↔H x u:=by
  simp only [spokeRelationImage,f.injective.eq_iff,exists_eq_left]

def hubCycleEmbedding (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U):
    HubMarkedCycle tail head ktail khead m ρ b H₀ HK u↪
      HubMarkedCycle (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
        (spokeRelationImage f H₀) (spokeRelationImage f HK) u where
  toFun C:=⟨f∘C.val,(markedCycle_embedding_iff f ρ π h tail head ktail khead m b C.val).mpr C.property.1,
    ⟨_,rfl,C.property.2.1⟩,fun i=>⟨_,rfl,C.property.2.2 i⟩⟩
  inj' A B he:=by
    apply Subtype.ext
    funext i
    exact f.injective (congrArg (fun C=>C.val i) he)

theorem hubCycleEmbedding_surjective (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U):
    Function.Surjective (hubCycleEmbedding f ρ π h tail head ktail khead m b H₀ HK u):=by
  intro C
  have hz:∀ i:Fin (m+1),∃ x,f x=C.val i:=by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with hi|⟨j,hj⟩
    · subst i;obtain ⟨x,hx,_⟩:=C.property.2.1;exact ⟨x,hx⟩
    · rw [hj];obtain ⟨x,hx,_⟩:=C.property.2.2 j;exact ⟨x,hx⟩
  let z:=fun i=>Classical.choose (hz i)
  have he:f∘z=C.val:=by funext i;exact Classical.choose_spec (hz i)
  have hc:IsMarkedCycleTuple tail head ktail khead m ρ b z:=
    (markedCycle_embedding_iff f ρ π h tail head ktail khead m b z).mp (he.symm ▸ C.property.1)
  have hs:MarkedHubCompatible H₀ HK z u:=by
    constructor
    · apply (spokeRelationImage_at f HK (z 0) u).mp
      rw [show f (z 0)=C.val 0 from congrFun he 0]
      exact C.property.2.1
    · intro i
      apply (spokeRelationImage_at f H₀ (z i.succ) u).mp
      rw [show f (z i.succ)=C.val i.succ from congrFun he i.succ]
      exact C.property.2.2 i
  refine ⟨⟨z,hc,hs⟩,?_⟩
  exact Subtype.ext he

def hubCycleEmbeddingEquiv (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U):
    HubMarkedCycle tail head ktail khead m ρ b H₀ HK u≃
      HubMarkedCycle (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
        (spokeRelationImage f H₀) (spokeRelationImage f HK) u:=
  Equiv.ofBijective _ ⟨(hubCycleEmbedding f ρ π h tail head ktail khead m b H₀ HK u).injective,
    hubCycleEmbedding_surjective f ρ π h tail head ktail khead m b H₀ HK u⟩

theorem hubCycleEmbedding_vertices (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U)
    (C:HubMarkedCycle tail head ktail khead m ρ b H₀ HK u):
    hubMarkedCycleVertices u (hubCycleEmbeddingEquiv f ρ π h tail head ktail khead m b H₀ HK u C)=
      (hubMarkedCycleVertices u C).image f:=by
  change Finset.univ.image (f∘C.val)=(Finset.univ.image C.val).image f
  rw [Finset.image_image]

theorem hubCycleEmbedding_weighted_degree (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U)
    (wt:HubMarkedCycle tail head ktail khead m ρ b H₀ HK u→ℝ) (x:W):
    hypergraphWeightedDegree (hubMarkedCycleVertices u)
      (fun C=>wt ((hubCycleEmbeddingEquiv f ρ π h tail head ktail khead m b H₀ HK u).symm C)) (f x)=
      hypergraphWeightedDegree (hubMarkedCycleVertices u) wt x:=by
  unfold hypergraphWeightedDegree
  rw [←Equiv.sum_comp (hubCycleEmbeddingEquiv f ρ π h tail head ktail khead m b H₀ HK u)]
  apply Finset.sum_congr rfl
  intro C _
  simp only [Equiv.symm_apply_apply,hubCycleEmbedding_vertices,Finset.mem_image,f.injective.eq_iff,exists_eq_right]

end Oberwolfach
