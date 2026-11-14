module

public import Oberwolfach.TransformerActualData
public import Oberwolfach.TransformerUnusedEndpointSpokes

@[expose] public section

/-! A triangular rim path consists of one vertex p_e. Two incidences
share that vertex precisely when they are the two ends of e. The shifted
hub distinguishes those incidences: simplicity and the absence of fixed
points rule out a second edge with the same two ends. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

theorem triangle_root_shared_endpoint_injective (G:SimpleGraph V) (φ:V→V)
    (p:G.edgeFinset↪V) (hφ:∀ v w,G.Adj v w→φ v≠φ w):
    Function.Injective (fun d:Σ v,G.neighborSet v=>(φ d.1,p (rimIncidenceEquiv G d).1)):=by
  have he (d:Σ v,G.neighborSet v):(rimIncidenceEquiv G d).1=
      ⟨s(d.1,d.2.val),SimpleGraph.mem_edgeFinset.mpr d.2.property⟩:=
    Subtype.ext (rimIncidenceEquiv_edge G d)
  simpa only [he,Equiv.refl_apply] using
    shifted_hub_root_injective G p (fun _=>Equiv.refl _) φ hφ

theorem triangle_edge_shifted_edge_injective (G:SimpleGraph V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w):
    Function.Injective (fun d:Σ v,G.neighborSet v=>
      ((rimIncidenceEquiv G d).1,(shiftedIncidenceEquiv G σ d).1)):=by
  rintro ⟨v,w⟩ ⟨v',w'⟩ he
  have h1:=congrArg Subtype.val (Prod.mk.inj he).1
  have h2:=congrArg Subtype.val (Prod.mk.inj he).2
  rw [rimIncidenceEquiv_edge,rimIncidenceEquiv_edge] at h1
  rw [shiftedIncidenceEquiv_edge,shiftedIncidenceEquiv_edge] at h2
  change s(v,w.val)=s(v',w'.val) at h1
  change s(v,(σ v w).val)=s(v',(σ v' w').val) at h2
  rcases Sym2.eq_iff.mp h1 with ⟨hvv,hww⟩|⟨hvw,hwh⟩
  · subst v'
    have hw:w=w':=Subtype.ext hww
    subst w';rfl
  · rcases Sym2.eq_iff.mp h2 with ⟨hvv,_⟩|⟨_,hsv⟩
    · exact (w.property.ne (hvv.trans hwh.symm)).elim
    · have hfixed:σ v w=w:=Subtype.ext (hsv.trans hwh.symm)
      exact (hσ v w hfixed).elim

theorem triangle_shared_endpoint_hub_injective (G:SimpleGraph V)
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w)
    (p:G.edgeFinset↪V) (h:G.edgeFinset↪U):
    Function.Injective (fun d:Σ v,G.neighborSet v=>
      (p (rimIncidenceEquiv G d).1,transformerAssignedHub G σ h d)):=by
  intro d e he
  apply triangle_edge_shifted_edge_injective G σ hσ
  exact Prod.ext (p.injective (Prod.mk.inj he).1) (h.injective (Prod.mk.inj he).2)

end Oberwolfach
