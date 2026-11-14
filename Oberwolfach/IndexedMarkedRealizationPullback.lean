module

public import Oberwolfach.IndexedMarkedRealizationResources
public import Oberwolfach.TypedOccurrenceEquivalence

@[expose] public section

/-! Actual host realisations under a bijection between two different
occurrence index types. All physical resources are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V U E K A S A' S':Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

def IndexedMarkedHostRealization.pullbackOccurrences {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (τ:A'≃A) (σ:S'≃S):
    IndexedMarkedHostRealization (G.pullbackOccurrences τ σ) tail head ktail khead H₀ HK π b where
  rows:=R.rows
  hubs:=R.hubs
  rimPresent:=fun a=>R.rimPresent (τ a)
  spokePresent:=fun s=>R.spokePresent (σ s)
  arcSeparated:=fun a=>R.arcSeparated (τ a)
  rimInjective:=R.rimInjective.comp τ.injective
  spokeInjective:=R.spokeInjective.comp σ.injective

theorem finite_image_precompose_equiv_between {X X' Y:Type} [Fintype X] [Fintype X'] [DecidableEq Y]
    (f:X→Y) (τ:X'≃X):Finset.univ.image (f∘τ)=Finset.univ.image f:=by
  classical
  rw [←Finset.image_image,Finset.image_univ_equiv]

theorem IndexedMarkedHostRealization.resources_pullbackOccurrences
    [Fintype A] [Fintype S] [Fintype A'] [Fintype S'] [DecidableEq U]
    {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (τ:A'≃A) (σ:S'≃S):(R.pullbackOccurrences τ σ).resources=R.resources:=by
  change (Finset.univ.image ((fun a=>Sum.inl (if G.jr a then ({R.rows (G.src a),π (R.rows (G.dst a))}:Finset V)
      else {R.rows (G.src a),R.rows (G.dst a)}))∘τ)∪
    Finset.univ.image ((fun s=>Sum.inr (R.rows (G.row s),R.hubs (G.hub s)))∘σ))=R.resources
  rw [finite_image_precompose_equiv_between,finite_image_precompose_equiv_between]
  rfl

end Oberwolfach
