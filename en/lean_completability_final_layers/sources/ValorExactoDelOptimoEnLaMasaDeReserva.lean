import ElValorInteriorDominaAlLlenoCercaDelBorde
namespace ArticuloA.Historias
open Perfil Real Set
open scoped NNReal
noncomputable section

theorem valor_del_optimo_en_su_masa {P p} {x b κ M L : ℝ} (xp : 0<x)
    (e : EulerFisica P p x.toNNReal b) (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) :
    sSup (valoresCartesianosEnMasa (1-x))=P.s := by
  have mass : P.rho=1-x:=by simpa [Real.coe_toNNReal _ xp.le] using e.masa
  obtain ⟨qi,ui⟩:=entropias_del_optimo_integrables e sp kp lp
  have top : IsGreatest (valoresMedidosEnMasa (1-x)) P.s:=by
    refine ⟨⟨P,mass,qi,ui,rfl⟩,?_⟩
    rintro _ ⟨Q,hq,qj,uj,rfl⟩
    have support:=soporte_del_perfil_positivo e sp kp lp (Real.toNNReal_pos.mpr xp) Q qj uj
    rw [mass,hq,sub_self,neg_zero,zero_mul] at support
    linarith only [support]
  rw [conjuntos_de_valores_en_cada_masa,top.csSup_eq]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.valor_del_optimo_en_su_masa
