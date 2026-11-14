module

public import Oberwolfach.InnerRequiredRawStateCover
public import Oberwolfach.PermutationWindows

@[expose] public section
/-! Every approximate interval label is occupied once the buffered marker
images have been identified, including labels next to missing spokes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem raw_approximate_markers_imply_occupied
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool) (occupied:U→Finset V)
    (hmarkers:∀w a,rawIntervalColouredStart π d (fun e=>σ (w,e)) a true→
      ∀j:Fin (d+1),(π^j.val) a∈occupied w):
    ∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w:=by
  intro w x hx
  have hcov:rawIntervalCovered π d (fun e=>σ (w,e)) x true:=
    (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) x true).mp hx
  obtain ⟨a,ha,hwin⟩:=hcov
  obtain ⟨j,hj⟩:=(permutationWindow_mem_iff π 0 (d-1) a x).mp hwin
  have hjlt:j.val<d+1:=by have hj':=j.isLt;omega
  have hocc:=hmarkers w a ha ⟨j.val,hjlt⟩
  have heq:(π^j.val) a=x:=by simpa using hj
  simpa only [heq] using hocc
end Oberwolfach
