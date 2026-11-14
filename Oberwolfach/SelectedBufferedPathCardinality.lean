module

public import Oberwolfach.SelectedBufferedPathRestriction
public import Oberwolfach.UniformBufferedStrictCardinality

@[expose] public section
/-! The paper's deleted final-path interiors count only the selected intervals. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_uniform_buffered_strict_interior_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (S:Finset I) (L:ℕ) (ext:∀i:I,Fin (L+5)↪V) (inner:∀i:I,Fin (L+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (bufferedPathStrictInterior (bufferedSelectedLengths S (fun _=>L))
      (bufferedSelectedPaths S (fun _=>L) inner)).card=S.card*(L-1) := by
  classical
  have hdis':∀i j:{i // i∈S},i≠j→
      Disjoint (Finset.univ.image (ext i.val)) (Finset.univ.image (ext j.val)):=by
    intro i j hij
    apply hdis i.val j.val
    intro h
    exact hij (Subtype.ext h)
  have hh:=uniform_buffered_strict_interior_card L (fun i:{i // i∈S}=>ext i.val)
    (fun i:{i // i∈S}=>inner i.val) (fun i=>hinner i.val) hdis'
  change (bufferedPathStrictInterior (fun _ : {i // i∈S}=>L) (fun i=>inner i.val)).card=S.card*(L-1)
  simpa using hh
end Oberwolfach
