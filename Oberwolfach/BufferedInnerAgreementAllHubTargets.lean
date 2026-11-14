module

public import Oberwolfach.BufferedComplementDecompositionBounds
public import Oberwolfach.InnerComplementAgreementAllHubTargets

@[expose] public section
/-! The glued completion, with reserved path endpoints accounted for, retains
exactly the protected ordinary spokes on the first inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem buffered_inner_completion_agreement_all_hub_targets
    (I:Finset V) (J:Finset U) (Index:U→Type) [∀u,Fintype (Index u)]
    (n:∀u,Index u→ℕ) (inner:∀u i,Fin (n u i+1)↪X)
    (old remaining:U→Finset X) (Y End Outer R Absorber L Anchor Endpoints:U→Finset V)
    (ψ:U→X→V) (Φ:∀u,{x // x∈remaining u}→V)
    (f:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}→V)
    (B:∀u,Finset {x // x∈remaining u}) (g:∀u,{x // x∈remaining u}→V)
    (hcover:∀u,old u∪remaining u=Finset.univ)
    (hremain:∀u,Disjoint (bufferedPathStrictInterior (n u) (inner u)) (remaining u))
    (hold:∀u x,x.val∈old u→f u x=ψ u x.val)
    (hnew:∀u (x:{x // x∈remaining u}) (hx:x.val∉bufferedPathStrictInterior (n u) (inner u)),f u ⟨x.val,hx⟩=Φ u x)
    (hstart:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (n u) (inner u)),f u ⟨inner u i 0,hx⟩∈Y u)
    (hend:∀u i (hx:inner u i (Fin.last (n u i))∉bufferedPathStrictInterior (n u) (inner u)),f u ⟨inner u i (Fin.last (n u i)),hx⟩∈End u)
    (hR:∀u,R u=Finset.univ\(outsideBufferedPathImage (n u) (inner u) (f u)∪End u))
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) ((old u\bufferedPathStrictInterior (n u) (inner u)).image (ψ u)))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hAbs:∀u,Disjoint (Absorber u) I)
    (hAnchor:∀u,Anchor u⊆(old u\bufferedPathStrictInterior (n u) (inner u)).image (ψ u))
    (hEndpoints:∀u∈J,Endpoints u=∅)
    (hB:∀u,(B u).image (g u)=Anchor u∪Endpoints u∪
      innerRequiredTargets Finset.univ I Outer Y Absorber (fun u=>(old u\bufferedPathStrictInterior (n u) (inner u)).image (ψ u)) u)
    (hag:∀u x,x∈B u→Φ u x=g u x)
    (hfree:∀u x,x∉B u→Φ u x∈L u)
    (hLI:∀u,Disjoint (L u) I):
    ∀u∈J,∀v∈I,(v∈R u\Y u↔v∈Outer u):=by
  let Outside:=fun u=>outsideBufferedPathImage (n u) (inner u) (f u)
  let Old:=fun u=>(old u\bufferedPathStrictInterior (n u) (inner u)).image (ψ u)
  let Prescribed:=fun u=>Anchor u∪Endpoints u
  have hbounds:=fun u=>buffered_complement_decomposition_bounds (n u) (inner u) (old u) (remaining u) (Y u) (End u)
    (ψ u) (Φ u) (f u) (hcover u) (hremain u) (hold u) (hnew u) (hstart u) (hend u)
  have hPO:∀u∈J,Disjoint (Prescribed u) (Outer u):=by
    intro u hu
    apply Finset.disjoint_left.mpr
    intro v hv ho
    rcases Finset.mem_union.mp hv with ha|he
    · exact (Finset.disjoint_left.mp (hOuterOld u)) ho (hAnchor u ha)
    · rw [hEndpoints u hu] at he
      simpa using he
  exact inner_complement_completion_agreement_all_hub_targets I J (fun u=>{x // x∈remaining u}) Y Old End Outer Outside R Absorber L Prescribed B Φ g
    hR (fun u=>(hbounds u).1) (fun u=>(hbounds u).2.1) (fun u=>(hbounds u).2.2)
    hOuterY hOuterOld hOuterEnd hAbs hB hag hfree hLI hPO
end Oberwolfach
