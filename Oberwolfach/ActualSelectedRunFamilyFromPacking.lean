module

public import Oberwolfach.ActualSelectedRunFromPacking
public import Oberwolfach.ActualSelectedRunMarkerLabels

@[expose] public section
/-! Realise all actual selected runs simultaneously inside the same marked
wheel packing; their target supports are pairwise disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_selected_run_family_from_packed_wheels
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (hb:1≤b) (hπ:∀x,π x≠x) (H₀ Hₖ:V→U→Prop) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hub:U)
    (hW:∀z,(W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val))
    (hpair:∀z z',z≠z'→Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z')))
    (Ord:Finset V) (hOrd:∀z (a:Fin (m+1)),a.val≠0→(W z).1.val a∈Ord)
    (hOrdAvoid:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:L,G.Adj (ktail e) (π (khead e)))
    (R:V→V→Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:L,R (ktail e) (π (khead e))):
    ∃q:∀r:SelectedRunIndex data.s₂ data.d data.T,
      (SimpleGraph.completeGraph V).Walk ((π^r.2.val.1) (root r.1.val)) ((π^(r.2.val.2+1)) (root r.1.val)),
      (∀r,(q r).IsPath ∧ (q r).length=data.c*(r.2.val.2+1-r.2.val.1) ∧
        (∀x,x∈(q r).support ↔ x=(π^(r.2.val.2+1)) (root r.1.val) ∨
          ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃i:Fin (m+1),(W z).1.val i=x) ∧
        (∀j,j≤r.2.val.2+1-r.2.val.1→(q r).getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1.val)) ∧
        (∀e:Sym2 V,e∈(q r).edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧
          e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1) ∧
        (∀k,k<(q r).length→R ((q r).getVert k) ((q r).getVert (k+1)))) ∧
      (∀r s,r≠s→Disjoint (q r).support.toFinset (q s).support.toFinset):=by
  classical
  let endIndex (r:SelectedRunIndex data.s₂ data.d data.T):Fin (data.d+1):=
    ⟨r.2.val.2+1,by have hh:=(actual_selected_run_bounds data r).2;omega⟩
  let endpoint (r:SelectedRunIndex data.s₂ data.d data.T):V:=(π^r.2.val.2.succ) (root r.1.val)
  have hEndOrd:∀r,endpoint r∉Ord:=by
    intro r
    have hm:endpoint r∈permutationWindow π 0 data.d (root r.1.val):=by
      rw [permutationWindow_mem_iff]
      simp only [zero_add,pow_zero,Equiv.refl_apply]
      exact ⟨⟨(endIndex r).val,by have hh:=(endIndex r).isLt;omega⟩,rfl⟩
    exact Finset.disjoint_left.mp (hOrdAvoid r.1.val) hm
  have hEndNe:∀r s,r≠s→endpoint r≠endpoint s:=by
    intro r s hrs
    apply actual_distinct_run_markers_have_distinct_labels data π root hinj hdis r s hrs (endIndex r) (endIndex s)
    · constructor
      · have hh:=(actual_selected_run_bounds data r).1;dsimp [endIndex];omega
      · simp [endIndex]
    · constructor
      · have hh:=(actual_selected_run_bounds data s).1;dsimp [endIndex];omega
      · simp [endIndex]
  have hEndRoot:∀r (z:actualSelectedSegmentIndex data),r≠z.1→endpoint r≠(W z).1.val 0:=by
    intro r z hrz
    rw [(hW z).2]
    apply actual_distinct_run_markers_have_distinct_labels data π root hinj hdis r z.1 hrz (endIndex r) z.2.val
    · constructor
      · have hh:=(actual_selected_run_bounds data r).1;dsimp [endIndex];omega
      · simp [endIndex]
    · exact ⟨z.2.property.1,le_trans z.2.property.2 (Nat.le_succ _)⟩
  have hEndRim:∀r (z:actualSelectedSegmentIndex data),r≠z.1→∀a:Fin (m+1),endpoint r≠(W z).1.val a:=by
    intro r z hrz a he
    by_cases ha:a.val=0
    · have ha':a=0:=Fin.ext (by simpa using ha)
      subst a
      exact hEndRoot r z hrz he
    · apply hEndOrd r
      rw [he]
      exact hOrd z a ha
  have hex:∀r:SelectedRunIndex data.s₂ data.d data.T,
      ∃q:(SimpleGraph.completeGraph V).Walk ((π^r.2.val.1) (root r.1.val)) ((π^(r.2.val.2+1)) (root r.1.val)),
      q.IsPath ∧ q.length=data.c*(r.2.val.2+1-r.2.val.1) ∧
      (∀x,x∈q.support ↔ x=endpoint r ∨ ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃i:Fin (m+1),(W z).1.val i=x) ∧
      (∀j,j≤r.2.val.2+1-r.2.val.1→q.getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1.val)) ∧
      (∀e:Sym2 V,e∈q.edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧ e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1) ∧
      (∀k,k<q.length→R (q.getVert k) (q.getVert (k+1))):=by
    intro r
    exact actual_selected_run_from_packed_wheels data G tail head ktail khead m b hc π hb hπ H₀ Hₖ root hinj W hub hW hpair Ord hOrd r (hEndOrd r) hE hK R hER hKR
  choose q hq using hex
  refine ⟨q,?_,?_⟩
  · intro r
    exact hq r
  · intro r s hrs
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases ((hq r).2.2.1 x).mp (List.mem_toFinset.mp hx) with hr|⟨z,hzr,a,ha⟩
    · rcases ((hq s).2.2.1 x).mp (List.mem_toFinset.mp hy) with hs|⟨z,hzs,a,ha⟩
      · exact hEndNe r s hrs (hr.symm.trans hs)
      · exact hEndRim r z (fun hh=>hrs (hh.trans hzs)) a (hr.symm.trans ha.symm)
    · rcases ((hq s).2.2.1 x).mp (List.mem_toFinset.mp hy) with hs|⟨z',hzs,a',ha'⟩
      · exact hEndRim s z (fun hh=>hrs (hzr.symm.trans hh.symm)) a (hs.symm.trans ha.symm)
      · have hzz:z≠z':=by
          intro he
          apply hrs
          exact hzr.symm.trans (congrArg Sigma.fst he |>.trans hzs)
        have hh:=(hW z).1.trans (hW z').1.symm
        exact disjoint_marked_wheels_distinct_spoke_labels (W z) (W z') (hpair z z' hzz) hh a a' (ha.trans ha'.symm)
end Oberwolfach
