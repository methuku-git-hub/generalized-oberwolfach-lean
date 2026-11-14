module

public import Oberwolfach.OrdinaryComplementProtectedLocalPhysicalEdit
public import Oberwolfach.OrdinaryProtectedComplementLocalConflict
public import Oberwolfach.OrdinaryProtectedCorrectionWithForbiddenEdit

@[expose] public section
/-! On any smaller protected pair, the actual edited-target complement has
only the conflict-graph edit relative to the original sampled rim and spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_protected_local_conflict_and_edit {n q:ℕ}
    (Target Sample Fbad Protect:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Href:Fin n→Fin q→Prop) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old E:Fin q→Finset (Sym2 (Fin n)))
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hAgreement:∀v∈Inner,∀w∈Inner,(Target.Adj v w↔Sample.Adj v w))
    (hProtect:Protect≤Sample\Fbad)
    (hInnerProtect:spanningRestriction (Sample\Fbad) Inner≤Protect)
    (hA:A⊆ordinaryHostResources (Sample\Fbad) Href)
    (hAvoidA:Disjoint A (ordinaryRootResources Inner Hubs))
    (hReserveProtect:ordinaryResourceRim (Sample\Fbad) A≤Protect)
    (hReserveTarget:ordinaryResourceRim (Sample\Fbad) A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪E u)
    (hcover:∀e∈(ordinaryProtectedRequired Target Sample (Sample\Fbad) Inner).edgeFinset,∃u,e∈E u)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v)
    (X:Finset (Fin n)) (Z:Finset (Fin q)) (hX:X⊆Inner) (hZ:Z⊆Hubs)
    (LF:ℝ) (hLF:0≤LF) (hF:∀v,(Fbad.degree v:ℝ)≤LF):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let G:=Q\ordinaryResourceRim Q A
    let Hs:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    A⊆ordinaryHostResources Q H ∧
    Disjoint (G.induce (X:Set (Fin n))) (Fbad.induce (X:Set (Fin n))) ∧
    ∀a:↥X⊕↥Z,((changed
      ((ordinaryPhysicalGraph (Sample.induce (X:Set (Fin n)))
        (fun (v:↥X) (u:↥Z)=>Href v.val u.val)).neighborFinset a)
      ((ordinaryPhysicalGraph (G.induce (X:Set (Fin n)))
        (fun (v:↥X) (u:↥Z)=>Hs v.val u.val)).neighborFinset a)).card:ℝ)≤LF :=by
  intro Q H G Hs
  obtain ⟨hA',hr,_hs⟩:=ordinary_complement_protected_pair_and_reservoir_of_sample_agreement
    Target Sample (Sample\Fbad) Protect Inner Hubs Href Fs C f Old E A sdiff_le hAgreement hProtect hInnerProtect hA
    hReserveProtect hReserveTarget hRim hpartition hcover hAvoid hSpokeCover
  have hconf:=ordinary_protected_complement_local_conflict_free Target Sample Fbad Fs C f A X Inner hX hr
  have hlocal:=ordinary_complement_protected_local_physical_edit Target Sample Fbad Protect Inner Hubs Href Fs C f Old E A
    hAgreement hProtect hInnerProtect hA hAvoidA hReserveProtect hReserveTarget hRim hpartition hcover hAvoid hSpokeCover
    X Z hX hZ LF hLF hF
  refine ⟨hA',?_,?_⟩
  · convert hconf using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a
    have hh:=hlocal.2 a
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
