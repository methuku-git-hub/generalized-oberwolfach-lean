module

public import Oberwolfach.MarkedExpansionHostMaps
public import Oberwolfach.MarkedPresentOccurrenceInjection

@[expose] public section

/-! Separation and occurrence injectivity of the realised expansion.
No separation between two old vertices is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

theorem marked_expansion_host_arcs_separated (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (Z:Finset V) (hfZ:∀ v,f v∈Z)
    (hsep:∀ i k,∀ z∈Z,¬PermutationClose π b ((C i).1.val k) z):
    let D:=indexedMarkedExpansion G (l+4) (by omega)
    ∀ a,¬PermutationClose π b (markedExpansionHostRows f C (D.src a)) (markedExpansionHostRows f C (D.dst a)):=by
  dsimp only
  rintro (a|⟨a|s,k⟩)
  · exact (hsep (.inl a) _ _ (hfZ (G.src a))) ∘ (permutationClose_symm π b _ _).mp
  · rw [indexedMarkedExpansion_src_private,indexedMarkedExpansion_dst_private_rim]
    split
    · exact hsep (.inl a) k _ (hfZ (G.dst a))
    · exact marked_cycle_adjacent_separated (by omega) (C (.inl a)).1 k
  · exact marked_cycle_adjacent_separated (by omega) (C (.inr s)).1 k

theorem marked_expansion_host_occurrences_injective (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (g:U₀→U)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hF:Function.Injective (markedExpansionHostRows f C))
    (hH:Function.Injective (markedExpansionHostHubs g C))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hC:∀ i,MarkedExpansionWheelConditions (f∘G.src) (f∘G.dst) (f∘G.row) (g∘G.hub) G.jr G.js i (C i)):
    let D:=indexedMarkedExpansion G (l+4) (by omega)
    let F:=markedExpansionHostRows f C
    let H:=markedExpansionHostHubs g C
    Function.Injective (fun a=>if D.jr a then ({F (D.src a),π (F (D.dst a))}:Finset V) else {F (D.src a),F (D.dst a)})∧
    Function.Injective (fun s=>(F (D.row s),H (D.hub s))):=by
  dsimp only
  constructor
  · apply marked_present_occurrences_physical_injective _ _ _ hp (marked_expansion_host_present G f g C hC).1
    exact mapped_pair_injective _ _ _ _ hF hF (indexedMarkedExpansion_rim_injective G (l+4) (by omega))
  · exact mapped_pair_injective _ _ _ _ hF hH (indexedMarkedExpansion_spoke_injective G (l+4) (by omega))

end Oberwolfach
