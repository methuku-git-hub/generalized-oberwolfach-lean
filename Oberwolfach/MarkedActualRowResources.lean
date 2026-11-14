module

public import Oberwolfach.MarkedHostNeighbourEmbeddings
public import Oberwolfach.MarkedRowRequiredResources
public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section

/-! Exhaustiveness of the actual incoming and outgoing endpoint lists,
including the relation between the auxiliary rows and the physical star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem swapped_endpoint_injective (f g:E→V)
    (h:Function.Injective (fun e=>(f e,g e))):Function.Injective (fun e=>(g e,f e)):=by
  intro e e' he;apply h
  exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

theorem marked_actual_row_required_iff
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hinj₀:Function.Injective (fun e=>(tail e,head e)))
    (hinjₖ:Function.Injective (fun e=>(ktail e,khead e))) (v:V) (r:Finset V⊕(V×U)):
    let ain:=markedNeighbourArcEmbedding tail head ktail khead hinj₀ hinjₖ v
    let xout:=markedNeighbourArcEmbedding head tail khead ktail
      (swapped_endpoint_injective tail head hinj₀) (swapped_endpoint_injective ktail khead hinjₖ) v
    r∈markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π)
      ain xout v ((Finset.univ.filter (H₀ v))∪(Finset.univ.filter (HK v))) ↔
      (∃ a:E⊕K,(Sum.elim head khead a=v∨Sum.elim tail ktail a=v)∧
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)=r)∨
      (∃ u:U,(H₀ v u∨HK v u)∧Sum.inr (v,u)=r):=by
  dsimp only
  simp only [markedRowRequiredResources,Finset.mem_union,Finset.mem_image,
    Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ((⟨a,ha⟩|⟨a,ha⟩)|⟨u,hu,hr⟩)
    · exact Or.inl ⟨_,Or.inl (markedNeighbourArcEmbedding_root _ _ _ _ _ _ _ a),ha⟩
    · exact Or.inl ⟨_,Or.inr (markedNeighbourArcEmbedding_root _ _ _ _ _ _ _ a),ha⟩
    · exact Or.inr ⟨u,hu,hr⟩
  · rintro (⟨a,ha,hr⟩|⟨u,hu,hr⟩)
    · rcases ha with ha|ha
      · obtain ⟨x,hx⟩:=markedNeighbourArcEmbedding_exhaustive tail head ktail khead hinj₀ hinjₖ v a ha
        exact Or.inl (Or.inl ⟨x,by rw [hx];exact hr⟩)
      · obtain ⟨x,hx⟩:=markedNeighbourArcEmbedding_exhaustive head tail khead ktail
          (swapped_endpoint_injective tail head hinj₀) (swapped_endpoint_injective ktail khead hinjₖ) v a ha
        exact Or.inl (Or.inr ⟨x,by rw [hx];exact hr⟩)
    · exact Or.inr ⟨u,hu,hr⟩

theorem marked_physical_rim_star_iff
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (T:Finset V) (W:Finset U) (hT:∀ v,π v∈T↔v∈T) (a:E⊕K):
    markedStarResource T W (Sum.inl (markedPhysicalEdge tail head ktail khead π a))↔
      Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T:=by
  cases a with
  | inl e=>simp [markedStarResource,markedPhysicalEdge]
  | inr e=>simp [markedStarResource,markedPhysicalEdge,hT]

end Oberwolfach
