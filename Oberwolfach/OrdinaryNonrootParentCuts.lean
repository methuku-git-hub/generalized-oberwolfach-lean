module

public import Oberwolfach.BipartiteLargeCutEmbedding
public import Oberwolfach.SparseCorrectionMatrices

@[expose] public section
/-! Uniform parent cut bounds pass deterministically to the nonroot domains.
No independent sample is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_parent_cuts
    (A:V→V→ℕ) (H:V→U→Prop) (T:Finset V) (W:Finset U)
    (κ δ δfree h:ℝ) (hκ:0<κ) (hh:0≤h)
    (hV:0<Fintype.card ↥(Finset.univ\T)) (hU:0<Fintype.card ↥(Finset.univ\W))
    (hVsize:κ*Fintype.card V≤(Fintype.card ↥(Finset.univ\T):ℝ))
    (hUsize:κ*Fintype.card U≤(Fintype.card ↥(Finset.univ\W):ℝ))
    (hcutoff:1-2*δ≤κ*(1-2*δfree))
    (hA:BipartiteLargeCut A δ h) (hH:BipartiteLargeCut (relationMultiplicity H) δ h):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    BipartiteLargeCut (fun (v w:Vfree)=>A v.val w.val) δfree h ∧
    BipartiteLargeCut (relationMultiplicity (fun (v:Vfree) (u:Ufree)=>H v.val u.val)) δfree h:=by
  intro Vfree Ufree
  let f:Vfree↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let g:Ufree↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have ha:=bipartiteLargeCut_embedding f f A hV hV κ δ δfree h hκ hh hVsize hVsize hcutoff hA
  have hb:=bipartiteLargeCut_embedding f g (relationMultiplicity H) hV hU κ δ δfree h hκ hh hVsize hUsize hcutoff hH
  exact ⟨ha,hb⟩
end Oberwolfach
