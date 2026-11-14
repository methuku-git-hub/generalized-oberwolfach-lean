module

public import Oberwolfach.OrdinaryRootFirstPostCleanupCounts
public import Oberwolfach.OrdinaryRootCoverCleanupParentCounts
public import Oberwolfach.OrdinaryRootFirstPackingSubhost

@[expose] public section
/-! The approximate packing avoids the entire inner pair. Hence inner
    extension counts survive it without a fresh-sampling density loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_inner_extension_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t ν:ℝ)
    (Droot:OrdinaryRootCoverData Q F H X T Z W r η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell t ν Droot σ)
    (pR pH density tR tH L βe₀ βh₀ βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W r η ell t ν Droot σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W r η ell t ν Droot σ O;
    ∀u∈Z,∀a∈X,∀c∈X,βe*Fintype.card (V⊕U)-3*ν≤
      (((X.filter (fun v=>H₂ v u))∩Q₂.neighborFinset a∩Q₂.neighborFinset c).card:ℝ) :=by
  intro Q₂ H₂
  let K:=O.context
  let Q₀:=Q\K.cover.rim
  let H₀:=fun v u=>H v u∧¬K.cover.spokes v u
  let A:=Finset.univ\T;let B:=Finset.univ\W
  let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ
  let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ
  let Q₁:=Q₀\D;let H₁:=fun v u=>H₀ v u∧¬E v u
  let R:=wheelFamilyRim O.cleanup.wheels;let S:=wheelFamilySpokes O.cleanup.wheels
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have hinnerbot:spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)=⊥:=by
    apply le_antisymm
    · intro v w hvw
      obtain ⟨hpack,hv,hw⟩:=(spanningRestriction_adj _ _ _ _).mp hvw
      have hu:=hs.1 hpack
      rw [ordinary_unreserved_physical_graph] at hu
      exact hu.1.2 ((spanningRestriction_adj _ _ _ _).mpr ⟨hu.1.1,hv,hw⟩)
    · exact bot_le
  have hpackdegree:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph D E) (ordinaryInnerVertices X Z)).degree w:ℝ)≤0:=by
    intro w
    rw [hinnerbot]
    simp
  have hclean:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν:=by
    intro w
    have hh:((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤
        ((ordinaryPhysicalGraph R S).degree w:ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le (show spanningRestriction (ordinaryPhysicalGraph R S)
        (ordinaryInnerVertices X Z)≤ordinaryPhysicalGraph R S from by intro a b hab;exact ((spanningRestriction_adj _ _ _ _).mp hab).1)
    exact hh.trans (O.cleanup.degree w)
  have hp:=ordinary_root_cover_cleanup_parent_counts P Q Q₀ F H π d X T Z W r η ell K.cover
    pR pH density tR tH L βe₀ βh₀ βe βh s j raw profile le_rfl hmE hmH
  intro u hu a ha c hc
  have hpre:=hp.1 a c u
  have heq:(X.filter (fun v=>Q₀.Adj a v∧Q₀.Adj v c∧H₀ v u))=
      (X.filter (fun v=>H₀ v u))∩Q₀.neighborFinset a∩Q₀.neighborFinset c:=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    have hh:Q₀.Adj v c↔Q₀.Adj c v:=Q₀.adj_comm _ _
    tauto
  rw [heq] at hpre
  have hpack:=ordinary_inner_extensions_after_local_cover Q₀ D H₀ E X Z 0 hpackdegree u hu a c ha hc
  have hpost:(βe*Fintype.card (V⊕U):ℝ)≤
      (((X.filter (fun v=>H₁ v u))∩Q₁.neighborFinset a∩Q₁.neighborFinset c).card:ℝ):=by
    have hh:(((X.filter (fun v=>H₀ v u))∩Q₀.neighborFinset a∩Q₀.neighborFinset c).card:ℝ)-3*0≤
        (((X.filter (fun v=>H₁ v u))∩Q₁.neighborFinset a∩Q₁.neighborFinset c).card:ℝ):=by
      convert hpack using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    linarith only [hpre,hh]
  have hsurvive:=ordinary_inner_extensions_after_local_cover Q₁ R H₁ S X Z ν hclean u hu a c ha hc
  have hsurvive':(((X.filter (fun v=>H₁ v u))∩Q₁.neighborFinset a∩Q₁.neighborFinset c).card:ℝ)-3*ν≤
      (((X.filter (fun v=>H₂ v u))∩Q₂.neighborFinset a∩Q₂.neighborFinset c).card:ℝ):=by
    convert hsurvive using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  linarith only [hpost,hsurvive']
end Oberwolfach
