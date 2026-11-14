module

public import Oberwolfach.TransformerEndpointAssignments

@[expose] public section

/-! The shifted assignment of fresh rim-edge hubs has no repeated root
spoke, even when the root map is noninjective on vertices. Only the fact
that adjacent roots have distinct images is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

 theorem shifted_hub_root_injective (G:SimpleGraph V) (h:G.edgeFinset↪U)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (φ:V→V)
    (hφ:∀ v w,G.Adj v w→φ v≠φ w):
    Function.Injective (fun d:(Σ v,G.neighborSet v)=>
      (φ d.1,h ⟨s(d.1,(σ d.1 d.2).val),SimpleGraph.mem_edgeFinset.mpr (σ d.1 d.2).property⟩)):=by
  rintro ⟨v,w⟩ ⟨v',w'⟩ he
  have hv:φ v=φ v':=(Prod.mk.inj he).1
  have hed:=h.injective (Prod.mk.inj he).2
  have hed':s(v,(σ v w).val)=s(v',(σ v' w').val):=congrArg Subtype.val hed
  rcases Sym2.eq_iff.mp hed' with ⟨hvv,hww⟩|⟨hvw,hwh⟩
  · subst v'
    have hw:w=w':=(σ v).injective (Subtype.ext hww)
    subst w';rfl
  · have hadj:G.Adj v v':=by
      have ha:(σ v w).val∈G.neighborSet v:=(σ v w).property
      change G.Adj v (σ v w).val at ha
      simpa only [hwh] using ha
    exact (hφ v v' hadj hv).elim

 theorem shifted_hub_avoids_own_path (G:SimpleGraph V) (h:G.edgeFinset↪U)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w):
    ∀ (v:V) (w:G.neighborSet v),
      h ⟨s(v,(σ v w).val),SimpleGraph.mem_edgeFinset.mpr (σ v w).property⟩≠
        h ⟨s(v,w.val),SimpleGraph.mem_edgeFinset.mpr w.property⟩:=by
  intro v w he
  have hh:=congrArg Subtype.val (h.injective he)
  exact hσ v w (Subtype.ext (sym2_fixed_endpoint_injective v hh))

end Oberwolfach
