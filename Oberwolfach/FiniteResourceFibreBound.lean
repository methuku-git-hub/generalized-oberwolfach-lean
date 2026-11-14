module

public import Oberwolfach.LongRawIncidenceFamily

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_resource_fibre_card_le
    {U R:Type} [Fintype U] [DecidableEq U] [DecidableEq R]
    (S:Finset R) (B:Finset {r // r∈S}) (H:Finset U) (f:U→R) (hf:Function.Injective f):
    (H.filter (fun w=>∃z∈B,z.1=f w)).card≤B.card:=by
  let A:=H.filter (fun w=>∃z∈B,z.1=f w)
  let Φ:A→B:=fun w=>⟨Classical.choose (Finset.mem_filter.mp w.2).2,
    (Classical.choose_spec (Finset.mem_filter.mp w.2).2).1⟩
  have hΦ:Function.Injective Φ:=by
    intro w w' h
    apply Subtype.ext
    apply hf
    have hval:=congrArg (fun z:B=>z.1.1) h
    have ha: (Φ w).1.1=f w.1:=(Classical.choose_spec (Finset.mem_filter.mp w.2).2).2
    have hb: (Φ w').1.1=f w'.1:=(Classical.choose_spec (Finset.mem_filter.mp w'.2).2).2
    exact ha.symm.trans (hval.trans hb)
  exact Finset.card_le_card_of_injective hΦ
end Oberwolfach
