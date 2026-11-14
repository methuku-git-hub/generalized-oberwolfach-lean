module

public import Oberwolfach.ActualSelectedRunFamilyFromPacking

@[expose] public section
/-! Every nonordinary label on a selected packed-wheel run is one of its
parent interval markers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem packed_run_nonordinary_label_is_marker
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop) (root:K→V)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hW:∀z,(W z).1.val 0=(π^z.2.val.val) (root z.1.1.val))
    (Ord:Finset V) (hOrd:∀z (i:Fin (m+1)),i.val≠0→(W z).1.val i∈Ord)
    (r:SelectedRunIndex data.s₂ data.d data.T)
    (q:(SimpleGraph.completeGraph V).Walk ((π^r.2.val.1) (root r.1.val)) ((π^(r.2.val.2+1)) (root r.1.val)))
    (hq:∀x,x∈q.support→x=(π^(r.2.val.2+1)) (root r.1.val) ∨
      ∃z:actualSelectedSegmentIndex data,z.1=r ∧ ∃i:Fin (m+1),(W z).1.val i=x)
    (x:V) (hx:x∈q.support) (hn:x∉Ord):
    ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val):=by
  rcases hq x hx with he|⟨z,hz,i,hi⟩
  · let j:Fin (data.d+1):=⟨r.2.val.2+1,by have hh:=(actual_selected_run_bounds data r).2;omega⟩
    exact ⟨j,by have hh:=(actual_selected_run_bounds data r).1;dsimp [j];omega,le_rfl,he⟩
  · by_cases hzero:i.val=0
    · have hi0:i=0:=Fin.ext (by simpa using hzero)
      subst i
      let j:Fin (data.d+1):=z.2.val
      have hlo:r.2.val.1≤j.val:=by rw [←hz];exact z.2.property.1
      have hhi:j.val≤r.2.val.2+1:=by rw [←hz];have hh:=z.2.property.2;omega
      have he:x=(π^j.val) (root r.1.val):=by
        have hpar:z.1.1.val=r.1.val:=congrArg (fun a:SelectedRunIndex data.s₂ data.d data.T=>a.1.val) hz
        exact hi.symm.trans ((hW z).trans (congrArg (fun k=> (π^j.val) (root k)) hpar))
      exact ⟨j,hlo,hhi,he⟩
    · exact False.elim (hn (hi ▸ hOrd z i hzero))
end Oberwolfach
