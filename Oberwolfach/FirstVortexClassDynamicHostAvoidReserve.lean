module

public import Oberwolfach.FirstVortexClassDynamicHostResidual
public import Oberwolfach.FirstVortexClassDynamicResidualContinuation
public import Oberwolfach.FirstVortexClassAssignmentChangeDeletion
public import Oberwolfach.LongDynamicGlobalExtraMono
public import Oberwolfach.LongReserveAvoidingExtendingLists

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classDynamicHostAvoidReserveFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_dynamic_host_avoiding_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass DelG:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (F:U→SimpleGraph (Fin n)) (H:Finset U) (A:Finset (Fin n))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δlocal ρ₀ θ ε lam α b βfinal δglobal:ℝ)
    (hρ₀:0<ρ₀) (hb:0≤b) (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hθδ:10*θ≤δglobal) (hεδ:ε≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hU:0<Fintype.card U) (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (Mhost:Fin n→Fin n→ℕ)
    (hFreeDir:∀x y,rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y→¬DelG.Adj x y→Mhost x y=1)
    (hKorient:∀Pack x y,(Kbad Pack).Adj x y→Mhost x y=1∨Mhost y x=1)
    (hKavoid:∀Pack x y,(Kbad Pack).Adj x y→¬(markedResourceRimGraph C).Adj x y)
    (βpre ρreserve:ℝ) (hρreserve:0≤ρreserve) (hC:(C.card:ℝ)≤ρreserve*n)
    (hmargin:βfinal+2*ρreserve≤βpre):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:=Function.Embedding.subtype (·∈T)
    let DelPlus:=DelG⊔markedResourceRimGraph C
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬DelG.Adj x y
    let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
      (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
    (∀w,IsExtendingList Dfree (Lists w) βpre)→
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceDynamicGlobalLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δlocal
      (fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M →
    LongSelectedClassDynamicSourceHostCompletion hU F P π d m ℓ raw t Jret σE H A Sclass Kbad Used DelPlus absorber δlocal (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y)
      (fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelPlus Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
        ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
          (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
      ρ₀ θ δglobal M :=by
  intro raw T e DelPlus Dfree Lists hext M hsource
  have hC':(C.card:ℝ)≤ρreserve*Fintype.card (Fin n):=by simpa only [Fintype.card_fin] using hC
  have hext':∀w,IsExtendingList (fun x y=>Dfree x y ∧ ¬(markedResourceRimGraph C).Adj x y) (Lists w) βfinal:=
    long_reserve_avoiding_extending_lists Dfree Lists C βpre βfinal ρreserve hβ.le hρreserve hC' hmargin hext
  have hextPlus:∀w,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y ∧ ¬DelPlus.Adj x y) (Lists w) βfinal:=by
    intro w
    simpa only [Dfree,DelPlus,SimpleGraph.sup_adj,not_or,and_assoc] using hext' w
  let ExtraOld:=fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
    ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n
  let ExtraNew:=fun occupied Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelPlus Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack ∧
    ∀w,((innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n
  have hsource':=long_dynamic_global_extra_mono hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δlocal ExtraOld ExtraNew ρ₀ θ δglobal (by
    intro occupied Pack h
    exact ⟨first_vortex_class_assignment_change_deletion P Sclass DelG DelPlus Used (Kbad Pack) A π d σE t Jret H α b ρ₀ θ ε lam occupied Pack h.1,h.2⟩) M hsource
  have hFreeHost:∀x y,rawSelectedPhysicalRelation P π d (fun e=>σE (Sum.inl e)) x y→¬DelPlus.Adj x y→
      Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y:=by
    intro x y hs hd
    have hnDel:¬DelG.Adj x y:=fun h=>hd (Or.inl h)
    exact ⟨hFreeDir x y hs hnDel,fun h=>hd (Or.inr h)⟩
  have hKbadHost:∀Pack x y,(Kbad Pack).Adj x y→
      (Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y) ∨
      (Mhost y x=1 ∧ ¬(markedResourceRimGraph C).Adj y x):=by
    intro Pack x y hk
    have ha:=hKavoid Pack x y hk
    rcases hKorient Pack x y hk with h|h
    · exact Or.inl ⟨h,ha⟩
    · exact Or.inr ⟨h,fun hr=>ha hr.symm⟩
  exact first_vortex_class_dynamic_host_residual_continuation P Sclass DelPlus π d m ℓ σE t Jret F H A Kbad Used absorber
    (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y)
    δlocal ρ₀ θ ε lam α b βfinal δglobal hρ₀ hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn hnβ hnδ hu hU hFreeHost hKbadHost hextPlus M hsource' 
end Oberwolfach
