module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.MarkedResourceEmbeddingComposition
public import Oberwolfach.MarkedSampleArcEmbedding
public import Oberwolfach.MarkedResourceDecompositionEmbedding

@[expose] public section
/-! Concrete maps between every two levels of the fixed vortex. These are
chosen before sampling; raw states are restricted without resampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexNestedVertex (i j:ℕ) (hij:i≤j):
    markedVortexVertexType Q j ↪o markedVortexVertexType Q i where
  toFun x:=⟨x.val,Q.extendedVertices_subset hij x.property⟩
  inj':=by intro x y h;apply Subtype.ext;exact congrArg (fun z:markedVortexVertexType Q i=>z.val) h
  map_rel_iff':=by intro x y;rfl

def markedVortexNestedHub (i j:ℕ) (hij:i≤j):
    markedVortexHubType Q j ↪ markedVortexHubType Q i where
  toFun x:=⟨x.val,Q.extendedIndices_subset hij x.property⟩
  inj':=by intro x y h;apply Subtype.ext;exact congrArg (fun z:markedVortexHubType Q i=>z.val) h

theorem marked_vortex_nested_vertex_comp (i j k:ℕ) (hij:i≤j) (hjk:j≤k) (hik:i≤k)
    (x:markedVortexVertexType Q k):
    markedVortexNestedVertex Q i j hij (markedVortexNestedVertex Q j k hjk x)=
      markedVortexNestedVertex Q i k hik x:=by
  apply Subtype.ext
  rfl

theorem marked_vortex_nested_hub_comp (i j k:ℕ) (hij:i≤j) (hjk:j≤k) (hik:i≤k)
    (u:markedVortexHubType Q k):
    markedVortexNestedHub Q i j hij (markedVortexNestedHub Q j k hjk u)=
      markedVortexNestedHub Q i k hik u:=by
  apply Subtype.ext
  rfl

theorem marked_vortex_nested_next_images (i:ℕ):
    Finset.univ.image (markedVortexNestedVertex Q i (i+1) (by omega))=markedVortexInnerVertices Q i ∧
    Finset.univ.image (markedVortexNestedHub Q i (i+1) (by omega))=markedVortexInnerHubs Q i:=by
  constructor
  · ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and,markedVortexInnerVertices,Finset.mem_filter]
    constructor
    · rintro ⟨v,rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
  · ext x
    simp only [Finset.mem_image,Finset.mem_univ,true_and,markedVortexInnerHubs,Finset.mem_filter]
    constructor
    · rintro ⟨v,rfl⟩
      exact v.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩

theorem marked_vortex_nested_next_deeper (i:ℕ):
    (∀ x:markedVortexVertexType Q (i+1),
      markedVortexNestedVertex Q i (i+1) (by omega) x∈markedVortexDeeperVertices Q i ↔
        x∈markedVortexInnerVertices Q (i+1)) ∧
    (∀ u:markedVortexHubType Q (i+1),
      markedVortexNestedHub Q i (i+1) (by omega) u∈markedVortexDeeperHubs Q i ↔
        u∈markedVortexInnerHubs Q (i+1)):=by
  constructor
  · intro x
    simp only [markedVortexDeeperVertices,markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    change x.val∈Q.extendedVertices (i+2) ↔ x.val∈Q.extendedVertices (i+1+1)
    have he:i+2=i+1+1:=by omega
    rw [he]
  · intro x
    simp only [markedVortexDeeperHubs,markedVortexInnerHubs,Finset.mem_filter,Finset.mem_univ,true_and]
    change x.val∈Q.extendedIndices (i+2) ↔ x.val∈Q.extendedIndices (i+1+1)
    have he:i+2=i+1+1:=by omega
    rw [he]

theorem marked_vortex_nested_commutes (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i j:ℕ) (hij:i≤j) (x:markedVortexVertexType Q j):
    markedVortexNestedVertex Q i j hij (markedVortexPermutation Q π hπ j x)=
      markedVortexPermutation Q π hπ i (markedVortexNestedVertex Q i j hij x):=by
  apply Subtype.ext
  rfl

theorem marked_vortex_nested_graph (i j:ℕ) (hij:i≤j):
    G.comap (markedVortexVertexEmbedding Q j)=
      (G.comap (markedVortexVertexEmbedding Q i)).comap (markedVortexNestedVertex Q i j hij):=by
  ext x y
  rfl
/-- Restricting first to one fixed pair and then to a smaller pair is
restriction of the very same raw outcome to the composed embeddings. -/
theorem raw_marked_pair_restriction_composition
    {V₀ V₁ V₂ U₀ U₁ U₂ Γ' Color':Type}
    [Fintype V₀] [Fintype V₁] [Fintype V₂] [Fintype U₀] [Fintype U₁] [Fintype U₂]
    [Fintype Γ'] [Fintype Color'] [LinearOrder V₀] [LinearOrder V₁] [LinearOrder V₂]
    [DecidableEq U₀] [DecidableEq U₁] [DecidableEq U₂]
    (f:V₁→V₀) (g:U₁→U₀) (f':V₂→V₁) (g':U₂→U₁)
    (σ:RawMarkedOutcome V₀ U₀ Γ' Color'):
    rawMarkedRestrictPair f' g' (rawMarkedRestrictPair f g σ)=
      rawMarkedRestrictPair (f∘f') (g∘g') σ:=by
  funext e
  cases e with
  | inl e=>
    simp only [rawMarkedRestrictPair,rawMarkedRestrictVertices,rawMarkedRestrictHubs,
      rawMarkedVertexState,rawMarkedHubState,rawMarkedVertexCoordinate,rawMarkedHubCoordinate,
      ]
    rw [Sym2.map_map]
  | inr e=>
    rcases e with ⟨u,e⟩
    cases e with
    | inl e=>rfl
    | inr e=>cases e <;> rfl

/-- Consecutive vortex restrictions preserve the exact sampled outcome. -/
theorem marked_vortex_nested_raw_restriction (i j:ℕ) (hij:i≤j)
    (σ:RawMarkedOutcome V U Γ Color):
    rawMarkedRestrictPair (markedVortexNestedVertex Q i j hij) (markedVortexNestedHub Q i j hij)
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)=
    rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ:=by
  rw [raw_marked_pair_restriction_composition]
  have hf:(markedVortexVertexEmbedding Q i ∘ markedVortexNestedVertex Q i j hij)=
      (markedVortexVertexEmbedding Q j:markedVortexVertexType Q j→V):=by funext x;rfl
  have hg:(markedVortexHubEmbedding Q i ∘ markedVortexNestedHub Q i j hij)=
      (markedVortexHubEmbedding Q j:markedVortexHubType Q j→U):=by funext x;rfl
  rw [hf,hg]

/-- Physical spoke relations restrict to the same ordered pair of vertices. -/
theorem marked_vortex_nested_spokes (i j:ℕ) (hij:i≤j) (H:Bool→V→U→Prop):
    (fun b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>
      H b (markedVortexVertexEmbedding Q i (markedVortexNestedVertex Q i j hij v))
        (markedVortexHubEmbedding Q i (markedVortexNestedHub Q i j hij u)))=
    (fun b v u=>H b (markedVortexVertexEmbedding Q j v) (markedVortexHubEmbedding Q j u)):=rfl

/-- Both rim types agree when a fixed raw sample is viewed at a smaller level. -/
theorem marked_vortex_nested_rim_agreement (i j:ℕ) (hij:i≤j)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (e:(markedVortexVertexType Q j×markedVortexVertexType Q j)⊕
      (markedVortexVertexType Q j×markedVortexVertexType Q j)):
    rawMarkedPairRims (G.comap (markedVortexVertexEmbedding Q j)) (markedVortexPermutation Q π hπ j) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ) e ↔
    rawMarkedPairRims (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
      (Sum.map (Prod.map (markedVortexNestedVertex Q i j hij) (markedVortexNestedVertex Q i j hij))
        (Prod.map (markedVortexNestedVertex Q i j hij) (markedVortexNestedVertex Q i j hij)) e):=by
  have he:=rawMarkedRestrictPair_rims (markedVortexNestedVertex Q i j hij)
    (markedVortexNestedHub Q i j hij) (markedVortexPermutation Q π hπ i)
    (markedVortexPermutation Q π hπ j) (marked_vortex_nested_commutes Q π hπ i j hij)
    (G.comap (markedVortexVertexEmbedding Q i)) d
    (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) e
  rw [←marked_vortex_nested_graph Q i j hij,marked_vortex_nested_raw_restriction Q i j hij σ] at he
  exact he

/-- Both spoke types agree for the corresponding row and hub. -/
theorem marked_vortex_nested_spoke_agreement (i j:ℕ) (hij:i≤j)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (a:Γ) (c:Color) (b:Bool)
    (x:markedVortexVertexType Q j) (u:markedVortexHubType Q j):
    rawMarkedPairSpokes (markedVortexPermutation Q π hπ j) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ) a c b x u ↔
    rawMarkedPairSpokes (markedVortexPermutation Q π hπ i) d
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) a c b
      (markedVortexNestedVertex Q i j hij x) (markedVortexNestedHub Q i j hij u):=by
  have he:=rawMarkedRestrictPair_spokes (markedVortexNestedVertex Q i j hij)
    (markedVortexNestedHub Q i j hij) (markedVortexPermutation Q π hπ i)
    (markedVortexPermutation Q π hπ j) (marked_vortex_nested_commutes Q π hπ i j hij) d
    (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) a c b x u
  rw [marked_vortex_nested_raw_restriction Q i j hij σ] at he
  exact he

/-- The first-level embeddings of the reference chain are identities. -/
theorem marked_vortex_nested_self (i:ℕ):
    (∀ x:markedVortexVertexType Q i,markedVortexNestedVertex Q i i (le_refl i) x=x) ∧
    (∀ u:markedVortexHubType Q i,markedVortexNestedHub Q i i (le_refl i) u=u):=by
  constructor <;> intro x <;> apply Subtype.ext <;> rfl

/-- Both rim-edge sets and spoke pairs have the same physical image
whether transported through an intermediate level or in one step. -/
theorem marked_vortex_nested_resource_composition
    (i j k:ℕ) (hij:i≤j) (hjk:j≤k) (hik:i≤k)
    (z:Finset (markedVortexVertexType Q k)⊕
      (markedVortexVertexType Q k×markedVortexHubType Q k)):
    markedResourceEmbedding (markedVortexNestedVertex Q i j hij).toEmbedding (markedVortexNestedHub Q i j hij)
      (markedResourceEmbedding (markedVortexNestedVertex Q j k hjk).toEmbedding (markedVortexNestedHub Q j k hjk) z)=
    markedResourceEmbedding (markedVortexNestedVertex Q i k hik).toEmbedding (markedVortexNestedHub Q i k hik) z:=by
  rw [markedResourceEmbedding_comp_apply]
  have hf:(markedVortexNestedVertex Q j k hjk).toEmbedding.trans (markedVortexNestedVertex Q i j hij).toEmbedding=
      (markedVortexNestedVertex Q i k hik).toEmbedding:=by
    ext x <;> rfl
  have hg:(markedVortexNestedHub Q j k hjk).trans (markedVortexNestedHub Q i j hij)=
      markedVortexNestedHub Q i k hik:=by
    ext x <;> rfl
  rw [hf,hg]

/-- An actual sampled arc at a later level maps injectively to the same
directed, typed arc at the earlier level. -/
def markedVortexNestedSampleArcEmbedding (i j:ℕ) (hij:i≤j)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (a:Bool):
    MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q j)) (markedVortexPermutation Q π hπ j) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ (Sum.inl e)) a ↪
    MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) a where
  toFun e:=⟨(markedVortexNestedVertex Q i j hij e.val.1,markedVortexNestedVertex Q i j hij e.val.2),by
    cases a with
    | false=>
      exact (marked_vortex_nested_rim_agreement Q i j hij π hπ d σ (Sum.inl e.val)).mp e.property
    | true=>
      exact (marked_vortex_nested_rim_agreement Q i j hij π hπ d σ (Sum.inr e.val)).mp e.property⟩
  inj' a b he:=by
    apply Subtype.ext
    apply Prod.ext
    · exact (markedVortexNestedVertex Q i j hij).injective (congrArg (fun z=>z.val.1) he)
    · exact (markedVortexNestedVertex Q i j hij).injective (congrArg (fun z=>z.val.2) he)

theorem marked_vortex_nested_arc_endpoints (i j:ℕ) (hij:i≤j)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (a:Bool)
    (e:MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q j)) (markedVortexPermutation Q π hπ j) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ (Sum.inl e)) a):
    (markedVortexNestedSampleArcEmbedding Q i j hij π hπ d σ a e).val=
      (markedVortexNestedVertex Q i j hij e.val.1,markedVortexNestedVertex Q i j hij e.val.2):=rfl

/-- A wheel decomposition on a later vortex level lifts to the earlier
level, preserving its physical rim and spoke resources exactly. -/
theorem marked_vortex_nested_decomposition_lift (i j:ℕ) (hij:i≤j)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let Ei:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) false
    let Ki:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) true
    let Ej:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q j)) (markedVortexPermutation Q π hπ j) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ (Sum.inl e)) false
    let Kj:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q j)) (markedVortexPermutation Q π hπ j) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j) σ (Sum.inl e)) true
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val
    let Hj:=fun b (v:markedVortexVertexType Q j) (u:markedVortexHubType Q j)=>H b v.val u.val;
    ∀ R:Finset (Finset (markedVortexVertexType Q j)⊕(markedVortexVertexType Q j×markedVortexHubType Q j)),
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:Ej=>e.val.1) (fun e=>e.val.2) (fun e:Kj=>e.val.1) (fun e=>e.val.2)
        m (markedVortexPermutation Q π hπ j) (3*d) (Hj false) (Hj true)=>markedWheelPhysicalResources W) R→
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
        m (markedVortexPermutation Q π hπ i) (3*d) (Hi false) (Hi true)=>markedWheelPhysicalResources W)
      (R.image (markedResourceEmbedding (markedVortexNestedVertex Q i j hij).toEmbedding (markedVortexNestedHub Q i j hij))):=by
  intro Ei Ki Ej Kj Hi Hj R hR
  apply marked_resource_decomposition_embedding
    (markedVortexNestedVertex Q i j hij).toEmbedding (markedVortexNestedHub Q i j hij)
    (marked_vortex_nested_commutes Q π hπ i j hij)
    (markedVortexNestedSampleArcEmbedding Q i j hij π hπ d σ false)
    (markedVortexNestedSampleArcEmbedding Q i j hij π hπ d σ true)
    (by intro a;rfl) (by intro a;rfl) (by intro a;rfl) (by intro a;rfl)
    (by intro x u h;exact h) (by intro x u h;exact h) R hR

/-- An actual typed arc on a vortex level is the same directed arc in
the ambient sample. -/
def markedVortexAmbientSampleArcEmbedding (i:ℕ)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d:ℕ) (σ:RawMarkedOutcome V U Γ Color) (a:Bool):
    MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) a ↪
    MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) a where
  toFun e:=⟨(markedVortexVertexEmbedding Q i e.val.1,markedVortexVertexEmbedding Q i e.val.2),by
    cases a with
    | false=>
      exact (rawMarkedRestrictPair_rims (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
        π (markedVortexPermutation Q π hπ i) (marked_vortex_permutation_compatibility Q π hπ i).1
        G d σ (Sum.inl e.val)).mp e.property
    | true=>
      exact (rawMarkedRestrictPair_rims (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
        π (markedVortexPermutation Q π hπ i) (marked_vortex_permutation_compatibility Q π hπ i).1
        G d σ (Sum.inr e.val)).mp e.property⟩
  inj' a b he:=by
    apply Subtype.ext
    apply Prod.ext
    · exact (markedVortexVertexEmbedding Q i).injective (congrArg (fun z=>z.val.1) he)
    · exact (markedVortexVertexEmbedding Q i).injective (congrArg (fun z=>z.val.2) he)

/-- Lift a later-level wheel decomposition all the way to the original
host. The conclusion uses the exact physical image of its resources. -/
theorem marked_vortex_ambient_decomposition_lift (i:ℕ)
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let Ei:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) false
    let Ki:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
      (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) true
    let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val;
    ∀ R:Finset (Finset (markedVortexVertexType Q i)⊕(markedVortexVertexType Q i×markedVortexHubType Q i)),
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
        m (markedVortexPermutation Q π hπ i) (3*d) (Hi false) (Hi true)=>markedWheelPhysicalResources W) R→
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (R.image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i))):=by
  intro E K Ei Ki Hi R hR
  apply marked_resource_decomposition_embedding
    (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
    (marked_vortex_permutation_compatibility Q π hπ i).1
    (markedVortexAmbientSampleArcEmbedding Q i π hπ d σ false)
    (markedVortexAmbientSampleArcEmbedding Q i π hπ d σ true)
    (by intro a;rfl) (by intro a;rfl) (by intro a;rfl) (by intro a;rfl)
    (by intro x u h;exact h) (by intro x u h;exact h) R hR

/-- Lifting a physical resource through an intermediate vortex level and
then to the ambient host has the same result as lifting it directly. -/
theorem marked_vortex_ambient_resource_composition (i j:ℕ) (hij:i≤j)
    (z:Finset (markedVortexVertexType Q j)⊕
      (markedVortexVertexType Q j×markedVortexHubType Q j)):
    markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)
      (markedResourceEmbedding (markedVortexNestedVertex Q i j hij).toEmbedding (markedVortexNestedHub Q i j hij) z)=
    markedResourceEmbedding (markedVortexVertexEmbedding Q j).toEmbedding (markedVortexHubEmbedding Q j) z:=by
  rw [markedResourceEmbedding_comp_apply]
  have hf:(markedVortexNestedVertex Q i j hij).toEmbedding.trans (markedVortexVertexEmbedding Q i).toEmbedding=
      (markedVortexVertexEmbedding Q j).toEmbedding:=by ext x <;> rfl
  have hg:(markedVortexNestedHub Q i j hij).trans (markedVortexHubEmbedding Q i)=
      markedVortexHubEmbedding Q j:=by ext x <;> rfl
  rw [hf,hg]

/-- Decompositions on finitely many vortex levels combine in the original
host when their actual physical images are pairwise disjoint. -/
theorem marked_vortex_ambient_finite_decompositions
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (J:Finset ℕ)
    (R:∀ i,Finset (Finset (markedVortexVertexType Q i)⊕
      (markedVortexVertexType Q i×markedVortexHubType Q i))):
    let E:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true;
    (∀ i∈J,
      let Ei:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) false
      let Ki:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) true
      let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val;
      HasResourceDecomposition
        (fun W:MarkedWheel (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
          m (markedVortexPermutation Q π hπ i) (3*d) (Hi false) (Hi true)=>markedWheelPhysicalResources W) (R i))→
    (∀ i∈J,∀ j∈J,i≠j→Disjoint
      ((R i).image (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)))
      ((R j).image (markedResourceEmbedding (markedVortexVertexEmbedding Q j).toEmbedding (markedVortexHubEmbedding Q j))))→
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (J.biUnion (fun i=>(R i).image
        (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i)))):=by
  intro E K hR hdis
  apply resource_decomposition_biUnion _ _ J
  · intro i hi
    exact marked_vortex_ambient_decomposition_lift Q i π hπ d m σ H (R i) (hR i hi)
  · exact hdis

/-- Resource layers of a decreasing finite-set sequence are disjoint. -/
theorem decreasing_resource_layers_disjoint {X:Type} [DecidableEq X]
    (B R:ℕ→Finset X) (J:Finset ℕ)
    (hB:∀ i,B (i+1)⊆B i)
    (hR:∀ i∈J,R i⊆B i\B (i+1)):
    ∀ i∈J,∀ j∈J,i≠j→Disjoint (R i) (R j):=by
  have hanti:Antitone B:=antitone_nat_of_succ_le hB
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  by_cases hij:i<j
  · have hnext:=hanti (Nat.succ_le_of_lt hij)
    exact (Finset.mem_sdiff.mp (hR i hi hzi)).2 (hnext (Finset.mem_sdiff.mp (hR j hj hzj)).1)
  · have hji : j < i := by omega
    have hnext:=hanti (Nat.succ_le_of_lt hji)
    exact (Finset.mem_sdiff.mp (hR j hj hzj)).2 (hnext (Finset.mem_sdiff.mp (hR i hi hzi)).1)

/-- Exact finite conservation: each covered layer and the final remainder
partition the initial resource set. No infinite sequence hypothesis is needed. -/
theorem finite_resource_layers_partition {X:Type} [DecidableEq X]
    (B R:ℕ→Finset X) (n:ℕ)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hR:∀ i,i<n→R i=B i\B (i+1)):
    (Finset.range n).biUnion R ∪ B n=B 0:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    have hBn:B (n+1)⊆B n:=hB n (by omega)
    have hRn:R n=B n\B (n+1):=hR n (by omega)
    have hprev:(Finset.range n).biUnion R ∪ B n=B 0:=
      ih (fun i hi=>hB i (by omega)) (fun i hi=>hR i (by omega))
    rw [Finset.range_add_one,Finset.biUnion_insert,hRn]
    calc
      (B n\B (n+1) ∪ (Finset.range n).biUnion R) ∪ B (n+1)
          = (Finset.range n).biUnion R ∪ ((B n\B (n+1)) ∪ B (n+1)):=by ac_rfl
      _ = (Finset.range n).biUnion R ∪ B n:=by rw [Finset.sdiff_union_of_subset hBn]
      _ = B 0:=hprev

/-- Disjointness of the covered layers needs only the finite sequence of
monotonicity and layer-containment facts used by the iteration. -/
theorem finite_resource_layers_disjoint {X:Type} [DecidableEq X]
    (B R:ℕ→Finset X) (n:ℕ)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hR:∀ i,i<n→R i⊆B i\B (i+1)):
    ∀ i<n,∀ j<n,i≠j→Disjoint (R i) (R j):=by
  have hmono:∀ i j,i≤j→j≤n→B j⊆B i:=by
    intro i j hij
    induction hij with
    | refl=>intro _;exact Finset.Subset.rfl
    | @step j hij ih=>
      intro hj
      exact (hB j (by omega)).trans (ih (by omega))
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  by_cases hij:i<j
  · have hnext:=hmono (i+1) j (by omega) (by omega)
    exact (Finset.mem_sdiff.mp (hR i hi hzi)).2 (hnext (Finset.mem_sdiff.mp (hR j hj hzj)).1)
  · have hji : j < i := by omega
    have hnext:=hmono (j+1) i (by omega) (by omega)
    exact (Finset.mem_sdiff.mp (hR j hj hzj)).2 (hnext (Finset.mem_sdiff.mp (hR i hi hzi)).1)

/-- A finite prefix of successive deletions is decreasing. -/
theorem finite_resource_prefix_subset {X:Type} [DecidableEq X]
    (B:ℕ→Finset X) (n:ℕ) (hB:∀ i,i<n→B (i+1)⊆B i)
    (i j:ℕ) (hij:i≤j) (hjn:j≤n):B j⊆B i:=by
  induction hij with
  | refl=>exact Finset.Subset.rfl
  | @step j hij ih=>
    exact (hB j (by omega)).trans (ih (by omega))

/-- The final remainder is disjoint from all resources covered earlier. -/
theorem finite_resource_layers_terminal_disjoint {X:Type} [DecidableEq X]
    (B R:ℕ→Finset X) (n:ℕ)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hR:∀ i,i<n→R i⊆B i\B (i+1)):
    Disjoint ((Finset.range n).biUnion R) (B n):=by
  apply Finset.disjoint_left.mpr
  intro z hz hzn
  obtain ⟨i,hi,hzi⟩:=Finset.mem_biUnion.mp hz
  have hin:i<n:=Finset.mem_range.mp hi
  have hsub:=finite_resource_prefix_subset B n hB (i+1) n (by omega) (by omega)
  exact (Finset.mem_sdiff.mp (hR i hin hzi)).2 (hsub hzn)

/-- Exact layer decompositions and a terminal decomposition combine into
a decomposition of the initial resource set. -/
theorem finite_resource_layer_decompositions {X W:Type} [DecidableEq X] [DecidableEq W]
    (F:W→Finset X) (B R:ℕ→Finset X) (n:ℕ)
    (hB:∀ i,i<n→B (i+1)⊆B i)
    (hR:∀ i,i<n→R i=B i\B (i+1))
    (hdec:∀ i,i<n→HasResourceDecomposition F (R i))
    (hterm:HasResourceDecomposition F (B n)):
    HasResourceDecomposition F (B 0):=by
  have hsub:∀ i,i<n→R i⊆B i\B (i+1):=by intro i hi;rw [hR i hi]
  have hdis:=finite_resource_layers_disjoint B R n hB hsub
  have hlayers:HasResourceDecomposition F ((Finset.range n).biUnion R):=by
    apply resource_decomposition_biUnion F R (Finset.range n)
    · intro i hi;exact hdec i (Finset.mem_range.mp hi)
    · intro i hi j hj hne;exact hdis i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne
  have htermDis:=finite_resource_layers_terminal_disjoint B R n hB hsub
  have hfull:=resource_decomposition_union F ((Finset.range n).biUnion R) (B n) hlayers hterm htermDis
  rw [finite_resource_layers_partition B R n hB hR] at hfull
  exact hfull

/-- If the actual images of the level decompositions are exactly the
successive deletion layers, a terminal decomposition completes the original
host. The layer identities themselves are the remaining iteration input. -/
theorem marked_vortex_decompositions_from_exact_layers
    (π:Equiv.Perm V) (hπ:∀ k x,π x∈Q.extendedVertices k↔x∈Q.extendedVertices k)
    (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (n:ℕ)
    (R:∀ i,Finset (Finset (markedVortexVertexType Q i)⊕
      (markedVortexVertexType Q i×markedVortexHubType Q i)))
    (B:ℕ→Finset (Finset V⊕(V×U))):
    let E:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σ (Sum.inl e)) true
    let F:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W
    let S:=fun i=>(R i).image
      (markedResourceEmbedding (markedVortexVertexEmbedding Q i).toEmbedding (markedVortexHubEmbedding Q i));
    (∀ i,i<n→B (i+1)⊆B i)→
    (∀ i,i<n→S i=B i\B (i+1))→
    (∀ i,i<n→
      let Ei:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) false
      let Ki:=MarkedSampleArc (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) (3*d)
        (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ (Sum.inl e)) true
      let Hi:=fun b (v:markedVortexVertexType Q i) (u:markedVortexHubType Q i)=>H b v.val u.val;
      HasResourceDecomposition
        (fun W:MarkedWheel (fun e:Ei=>e.val.1) (fun e=>e.val.2) (fun e:Ki=>e.val.1) (fun e=>e.val.2)
          m (markedVortexPermutation Q π hπ i) (3*d) (Hi false) (Hi true)=>markedWheelPhysicalResources W) (R i))→
    HasResourceDecomposition F (B n)→HasResourceDecomposition F (B 0):=by
  intro E K F S hB hS hR hterm
  apply finite_resource_layer_decompositions F B S n hB hS ?_ hterm
  intro i hi
  exact marked_vortex_ambient_decomposition_lift Q i π hπ d m σ H (R i) (hR i hi)

end Oberwolfach
