module

public import Oberwolfach.LongClassProtectedCorrectionUniformSpacing
public import Oberwolfach.LongFirstVortexProtectedUnionBudget
public import Oberwolfach.MarkedValidDeletionPhysicalDegree
public import Oberwolfach.MarkedResourceRimGraph
public import Oberwolfach.LongReservedRimContainedInClass
public import Oberwolfach.LongSelectedInnerClassPreservation
public import Oberwolfach.LongEarlyMatchingListsForDeletion
public import Oberwolfach.LongActualRawLawParameters

@[expose] public section

/-! Once the correction and absorber reserve are fixed, every regular class
with the prescribed edit and protection conditions admits the same-sample
balanced orientation and a matching-compatible deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance everyClassFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_valid_deletion_every_protected_class
    (α ρ₀ δ:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃c:ℝ,0<c ∧ ∀d B:ℕ,2≤d→∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀ {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (π:Equiv.Perm (Fin n)) (r K:ℕ) (θ ρ D:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (γLoss σLoss ξClass Δ alpha γ eps βList:ℝ),
    let V:=Fin n
    let ω:=z.1
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) z.2 false false
    let T:=Q.extendedVertices 1
    let W:=Q.extendedIndices 1
    let Z:=spanningRestriction (⊤:SimpleGraph V) T
    let p:=ρ*(1/100)/2
    let s:ℝ:=(1/100)/(((r+4):ℕ):ℝ)
    let k:=ρ*s/2
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let u:=2*(∑w,(1-1/100-s-a w-b w))/D
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del;
    0≤εQ→εQ≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32→
    ρ₀≤ρ→ρ≤1→0<D→0≤θ→θ≤1/100→3≤K→7≤r+4→
    (1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ→(∀u,factorPreparationClass (F u) K=none)→
    ρ*D=2*Fintype.card U→(Dnat:ℝ)=D→P.IsRegularOfDegree Dnat→
    (1/2+α)*(n:ℝ)≤D→0≤ξClass→
    ξClass≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4)→γLoss+ξClass+δ≤Δ→
    (∀j v,|((∑w,sampledColourOrientation P (fun e=>ω (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-2*(2*((3*d:ℕ):ℝ)+1)≤
      ((Finset.univ.filter (fun w=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x w ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false w y)).card:ℝ))→
    (∀Del:SimpleGraph V,(∀v,(Del.degree v:ℝ)≤Δ*n)→Matching Del)→
    ∀D₀:MarkedReferenceDeletion P π d raw,
      D₀.Valid H (r+4) T W (γLoss*n) (σLoss*n)→
    let σ':=rawMarkedDeleteRims raw (markedSampleArcSetGraph P π d raw D₀.arcs).edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀C:MarkedSupportedEdgeSet (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π U,
      C.edges.card≤B→Disjoint D₀.removed C.edges→
    let A:=markedResourceRimGraph C.edges;
    ∀S:SimpleGraph V,S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈T,∀y∈T,S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)→
      A≤S→
      (∀x∈T,∀y∈T,(longSelectedPhysicalGraph P π d ω).Adj x y→S.Adj x y) ∧
      ∃M:V→V→ℕ,∃Del:SimpleGraph V,
        (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
        (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
        (markedSampleArcSetGraph P π d raw D₀.arcs)≤Del ∧
        ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
        orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
        (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
        (∀x y,Del.Adj x y→¬(Z⊔A).Adj x y) ∧
        (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
        (∀Kbad:SimpleGraph V,Kbad≤S→∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
        (∀x y,M x y=1→P.Adj x y) ∧
        (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧ Matching Del := by
  obtain ⟨c,hc,hOrientation⟩:=long_class_protected_correction_uniform_spacing α ρ₀ δ hα hρ₀ hδ
  refine ⟨c,hc,?_⟩
  intro d B hd
  obtain ⟨N₁,hN₁,hOrientation⟩:=hOrientation d
  obtain ⟨N₂,hN₂,hUnion⟩:=long_first_vortex_protected_union_budget α ρ₀ B hα hρ₀
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro n hn U _ _ _ P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w z γLoss σLoss ξClass Δ alpha γ eps βList
  dsimp only
  intro hεQ hcap hρlo hρhi hD hθ hθhi hK hm hcut hclass hsize hDnat hreg hmin hξ hξhi hsum hcolour hpath hMatching D₀ hvalid C hcard hdis S hSP hSreg hEdit hInner hA
  let A:=markedResourceRimGraph C.edges
  have hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
    hθ hθhi hρ₀ hρlo hρhi hD hsize hcut hclass
  dsimp only at hLaw
  have hDegP:∀v,|(P.degree v:ℝ)-D|≤(0:ℝ)*n:=by intro v;rw [hreg v,hDnat];simp
  have hMinP:∀v,(1/2+α)*(n:ℝ)≤P.degree v:=by intro v;rw [hreg v,hDnat];exact hmin
  obtain ⟨hDelDeg,hInnerAvoid⟩:=marked_valid_deletion_physical_degree P π d (r+4)
    (fun e=>rawExpandedMarkedCollapse e (z.1 e)) _ (Q.extendedVertices 1) (Q.extendedIndices 1) (γLoss*n) (σLoss*n) D₀ hvalid
  have hC0:markedResourceRimGraph C.edges≤longPhysicalStateGraph P z.1 {0,1,2,3,4}:=by
    have hh:=long_reserved_sample_rim_contained_in_class P (longPhysicalStateGraph P z.1 {0,1,2,3,4})
      (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)) π d z.1
      (markedSampleArcSetGraph P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).edgeFinset C
    have hdec6:instDecidableEqFin 6=everyClassFin 6:=Subsingleton.elim _ _
    try rw [hdec6] at hh
    exact (hh (by intro x y h; rfl)).1
  have hAgree:∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))⊔A).Adj x y→
      (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y):=by
    intro x y hxy
    change (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)).Adj x y ∨ A.Adj x y at hxy
    rcases hxy with hz|ha
    · obtain ⟨_,hx,hy⟩:=(spanningRestriction_adj ⊤ (Q.extendedVertices 1) x y).mp hz
      exact hInner x hx y hy
    · exact iff_of_true (hA ha) (hC0 ha)
  have hAvoid:∀x y,(markedSampleArcSetGraph P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs).Adj x y→
      ¬((spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))⊔A).Adj x y:=by
    intro x y hD hxy
    change (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)).Adj x y ∨ A.Adj x y at hxy
    rcases hxy with hz|ha
    · obtain ⟨_,hx,hy⟩:=(spanningRestriction_adj ⊤ (Q.extendedVertices 1) x y).mp hz
      exact hInnerAvoid x hx y hy hD
    · exact markedReferenceDeletion_disjoint_resourceRimGraph P π d _ D₀ C.edges hdis x y hD ha
  have hUnionBound:=hUnion n (by omega) U P Dnat vsize β εQ Q hεQ hcap A
    (fun v=>(markedResourceRimGraph_degree_le C.edges v).trans hcard)
  have hgraphdec : (fun x y:Fin n=>SimpleGraph.Sup.adjDecidable (Fin n)
      (spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)) A x y) =
      (fun x y:Fin n=>Classical.propDecidable (((spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))⊔A).Adj x y)) := Subsingleton.elim _ _
  try rw [hgraphdec] at hUnionBound
  have hColourLe:=fun j v=>(hcolour j v).le
  have hOrientation':=hOrientation n (by omega) P S
    ((spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1))⊔A)
    (markedSampleArcSetGraph P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)) D₀.arcs) π (Fintype.card U) z.1
    ρ D ((1/100)/(((r+4):ℕ):ℝ)) 0 ξClass ((α*(ρ₀/200)^2/16)*n) γLoss
    (longAssignedApproxMarkedWeight F hF K (r+4) θ) (longAssignedApproxOrdinaryWeight F hF K (r+4) θ)
  have hdec:classUniformSpacingCorrectionFin n=everyClassFin n:=Subsingleton.elim _ _
  have hdec6:classUniformSpacingCorrectionSix=everyClassFin 6:=Subsingleton.elim _ _
  try rw [hdec] at hOrientation'
  try rw [hdec6] at hOrientation'
  obtain ⟨M,Del,hM,hBalance,hD,hEditDel,hOrientDel,hDeg,hProtect,hSelected,hEdges,hHost,hMixed⟩:=
    hOrientation' hρlo hρhi hD hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1
      (le_refl _) (by linarith) hξ hξhi (by positivity) (le_refl _) hSreg hsize rfl hSP hDegP hColourLe hEdit hAgree hUnionBound hDelDeg hAvoid hMinP hpath
  have hDeg':∀v,(Del.degree v:ℝ)≤Δ*n:=by
    intro v
    exact (hDeg v).trans (mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg n))
  have hhSel:=long_selected_inner_preserved_in_regular_class P S A π d (Q.extendedVertices 1) z.1
  have hdecSel:instDecidableEqFin 6=everyClassFin 6:=Subsingleton.elim _ _
  try rw [hdecSel] at hhSel
  have hSel:=hhSel hAgree
  refine ⟨hSel,M,Del,hM,hBalance,hD,hEditDel,hOrientDel,hDeg',hProtect,hSelected,?_,hHost,hMixed,hMatching Del hDeg'⟩
  intro Kbad hK x y hxy
  exact hEdges x y (hK hxy)
end Oberwolfach
