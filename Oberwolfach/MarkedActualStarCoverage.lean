module

public import Oberwolfach.MarkedActualRowResources

@[expose] public section

/-! Covering the exhaustive actual endpoint lists and all incident hub
spokes covers the full physical star of a permutation-invariant row set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_actual_star_covered
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hinj₀:Function.Injective (fun e=>(tail e,head e)))
    (hinjₖ:Function.Injective (fun e=>(ktail e,khead e)))
    (n h:ℕ) (v:Fin n→V) (u:Fin h→U) (T:Finset V)
    (hTv:T⊆Finset.univ.image v) (hT:∀ x,π x∈T↔x∈T)
    (M:Finset (Finset V⊕(V×U)))
    (hhubs:∀ i x,H₀ x (u i)∨HK x (u i)→Sum.inr (x,u i)∈M)
    (hrows:∀ i,markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π)
      (markedNeighbourArcEmbedding tail head ktail khead hinj₀ hinjₖ (v i))
      (markedNeighbourArcEmbedding head tail khead ktail
        (swapped_endpoint_injective tail head hinj₀) (swapped_endpoint_injective ktail khead hinjₖ) (v i))
      (v i) ((Finset.univ.filter (H₀ (v i)))∪(Finset.univ.filter (HK (v i))))⊆M):
    (∀ a:E⊕K,markedStarResource T (Finset.univ.image u)
      (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M)∧
    (∀ x z,H₀ x z∨HK x z→markedStarResource T (Finset.univ.image u) (Sum.inr (x,z))→
      Sum.inr (x,z)∈M):=by
  have harcs (a:E⊕K) (i:Fin n) (ha:Sum.elim head khead a=v i∨Sum.elim tail ktail a=v i):
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M:=by
    apply hrows i
    apply (marked_actual_row_required_iff tail head ktail khead π H₀ HK hinj₀ hinjₖ (v i) _).mpr
    exact Or.inl ⟨a,ha,rfl⟩
  constructor
  · intro a ha
    rcases (marked_physical_rim_star_iff tail head ktail khead π T (Finset.univ.image u) hT a).mp ha with ha|ha
    · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv ha)
      exact harcs a i (Or.inr hi.symm)
    · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv ha)
      exact harcs a i (Or.inl hi.symm)
  · intro x z hz hs
    rcases hs with hx|hz'
    · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv hx)
      change v i=x at hi
      subst x
      apply hrows i
      apply (marked_actual_row_required_iff tail head ktail khead π H₀ HK hinj₀ hinjₖ (v i) _).mpr
      exact Or.inr ⟨z,hz,rfl⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hz'
      change u i=z at hi
      subst z
      exact hhubs i x hz

end Oberwolfach
