module

public import Oberwolfach.BufferedComplementDecompositionBounds
public import Oberwolfach.ActualRetainedCompletionInnerAgreementAllHubTargets
public import Oberwolfach.LongRetainedProtectedInnerTargets

@[expose] public section
/-! A raw reserved spoke remains a residual spoke unless the same completion
uses it as a new image vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_retained_completion_protects_raw_spokes
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d c:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (F:U→SimpleGraph V) (K L:U→Type) [∀u,DecidableEq (K u)] [∀u,DecidableEq (L u)]
    (data:∀u,ActualResidualData (K:=K u) (J:=L u) (F u))
    (inner:∀u,retainedMarkedIndex π d σ false t Jret u→Fin (c*d+1)↪V)
    (ψ:U→V→V) (Φ:∀u,{x // x∈(data u).remaining}→V)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}↪V)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (hDR:∀u,Disjoint (bufferedPathStrictInterior (fun _=>c*d) (inner u)) (data u).remaining)
    (hC:∀u (x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}),x.val∈(data u).oldDomain→fC u x=ψ u x.val)
    (hR:∀u (x:{x // x∈(data u).remaining}) (hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨x.val,hx⟩=Φ u x)
    (hStart:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩=i.val)
    (hEnd:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩=(π^d) i.val)
    (hOld:∀u,Disjoint (((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u))
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u))):
    ∀u v,v∈rawReservedSpokeList π d σ u→v∉Finset.univ.image (Φ u)→
      let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val
      let End:=Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val)
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪End);
      v∈R\Y :=by
  intro u v hv hnot Y End R
  let Outer:=Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u)
  have hvO:v∈Outer:=(long_retained_protected_inner_targets π d σ t Jret Finset.univ Finset.univ
    (fun _=>∅) (fun _=>∅) (fun _=>∅)).1 u hv
  have hstarts:∀i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩∈Y:=by
    intro i hx
    rw [hStart u i hx]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,by simp⟩⟩
  have hends:∀i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩∈End:=by
    intro i hx
    rw [hEnd u i hx]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hb:=buffered_complement_decomposition_bounds (fun _=>c*d) (inner u) (data u).oldDomain (data u).remaining Y End
    (ψ u) (Φ u) (fC u) ((data u).old_domain_union_remaining (hCycle u)) (hDR u) (hC u) (hR u) hstarts hends
  have hY: v∉Y:=fun hy=>Finset.disjoint_left.mp (retained_ordinary_avoids_interval_roots π d σ t Jret u).1 hvO hy
  have hEnd: v∉End:=fun he=>Finset.disjoint_left.mp (retained_ordinary_avoids_interval_roots π d σ t Jret u).2 hvO he
  have hOutside:v∉outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u):=by
    intro hx
    rcases Finset.mem_union.mp (hb.1 hx) with ho|hn
    · exact Finset.disjoint_left.mp (hOld u) ho hvO
    · exact hnot hn
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hu=>by
    rcases Finset.mem_union.mp hu with hx|hx
    · exact hOutside hx
    · exact hEnd hx⟩,hY⟩
end Oberwolfach
