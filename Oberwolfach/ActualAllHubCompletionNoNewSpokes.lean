module

public import Oberwolfach.BufferedCompletionNoNewSpokes
public import Oberwolfach.ActualRetainedCompletionInnerAgreement

@[expose] public section
/-! The same completed maps introduce no new ordinary spokes on the first
vortex when missing retained targets are covered at every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_all_hub_completion_no_new_spokes
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d c:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (F:U→SimpleGraph V) (K L:U→Type) [∀u,DecidableEq (K u)] [∀u,DecidableEq (L u)]
    (data:∀u,ActualResidualData (K:=K u) (J:=L u) (F u))
    (inner:∀u,retainedMarkedIndex π d σ false t Jret u→Fin (c*d+1)↪V)
    (ψ:U→V→V) (I:Finset V) (absorber:U→Finset V)
    (Anchor Endpoints:U→Finset V)
    (BB:∀u,Finset {x // x∈(data u).remaining}) (g Φ:∀u,{x // x∈(data u).remaining}→V)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}↪V)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (hDR:∀u,Disjoint (bufferedPathStrictInterior (fun _=>c*d) (inner u)) (data u).remaining)
    (hC:∀u (x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}),x.val∈(data u).oldDomain→fC u x=ψ u x.val)
    (hR:∀u (x:{x // x∈(data u).remaining}) (hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨x.val,hx⟩=Φ u x)
    (hStart:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩=i.val)
    (hEnd:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩=(π^d) i.val)
    (hAbs:∀u,Disjoint (absorber u) I)
    (hBB:∀u,(BB u).image (g u)=Anchor u∪Endpoints u∪
      innerRequiredTargets Finset.univ I (fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u))
        (retainedFinalMarkedAt π d σ t Jret) absorber (fun u=>((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u)) u)
    (hag:∀u x,x∈BB u→Φ u x=g u x):
    ∀u v,v∈I→
      let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val
      let End:=Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val)
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪End);
      v∈R\Y → retainedRawMarkedSpokes π d σ false t Jret false false false v u :=by
  let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val
  let End:=fun u=>Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val)
  let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u)
  let Old:=fun u=>((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u)
  let R:=fun u=>Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪End u)
  have hY:∀u,Y u=retainedFinalMarkedAt π d σ t Jret u:=by
    intro u;ext v
    simpa only [Y,retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using
      retained_marked_root_membership π d hd σ false t Jret u v
  have hstarts:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩∈Y u:=by
    intro u i hx
    rw [hStart u i hx]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,by simp⟩⟩
  have hends:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩∈End u:=by
    intro u i hx
    rw [hEnd u i hx]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hBB':∀u,(BB u).image (g u)=Anchor u∪Endpoints u∪innerRequiredTargets Finset.univ I Outer Y absorber Old u:=by
    intro u
    simpa only [Y,Outer,Old,hY] using hBB u
  have hh:=buffered_completion_no_new_spokes I Finset.univ (fun u=>retainedMarkedIndex π d σ false t Jret u)
    (fun _ _=>c*d) inner (fun u=>(data u).oldDomain) (fun u=>(data u).remaining) Y End Outer R absorber Anchor Endpoints
    ψ Φ (fun u=>fC u) BB g (fun u=>(data u).old_domain_union_remaining (hCycle u)) hDR hC hR hstarts hends
    (fun _=>rfl) (by intro u _;exact hAbs u) hBB' hag
  intro u v hv Y' End' R' hr
  simpa only [R',End',Y',R,Y,Outer,Finset.mem_filter,Finset.mem_univ,true_and] using hh u (Finset.mem_univ _) v hv hr
end Oberwolfach
