module

public import Oberwolfach.IndexedMarkedRealizationMaps

@[expose] public section

/-! Reindexing occurrences and preserving the mapped graph preserve the
actual physical resource set exactly, including all marked twists. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V₁ U₁ V U E K A S:Type} [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

theorem finite_image_precompose_equiv {X Y:Type} [Fintype X] [DecidableEq Y]
    (f:X→Y) (τ:Equiv.Perm X):Finset.univ.image (f∘τ)=Finset.univ.image f:=by
  classical
  rw [←Finset.image_image,Finset.image_univ_equiv]

theorem IndexedMarkedHostRealization.resources_reindex {G:IndexedMarkedGraph V₀ U₀ A S}
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (τ:Equiv.Perm A) (σ:Equiv.Perm S):(R.reindex τ σ).resources=R.resources:=by
  change (Finset.univ.image ((fun a=>Sum.inl (if G.jr a then ({R.rows (G.src a),π (R.rows (G.dst a))}:Finset V)
      else {R.rows (G.src a),R.rows (G.dst a)}))∘τ)∪
    Finset.univ.image ((fun s=>Sum.inr (R.rows (G.row s),R.hubs (G.hub s)))∘σ))=R.resources
  rw [finite_image_precompose_equiv,finite_image_precompose_equiv]
  rfl

theorem IndexedMarkedHostRealization.resources_ofMapEq
    (G:IndexedMarkedGraph V₀ U₀ A S) {G':IndexedMarkedGraph V₁ U₁ A S}
    (R:IndexedMarkedHostRealization G' tail head ktail khead H₀ HK π b)
    (f:V₀→V) (g:U₀→U) (he:G.map f g=G'.map R.rows R.hubs):
    (IndexedMarkedHostRealization.ofMapEq G R f g he).resources=R.resources:=by
  exact congrArg (fun D:IndexedMarkedGraph V U A S=>markedRootGraphResources π D.src D.dst D.row D.jr D.hub) he

end Oberwolfach
