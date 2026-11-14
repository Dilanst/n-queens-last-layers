import MargenesFisicosParaReservarLasOblicuas
import ReservaAdmisibleConEntropiaYAbsorbedores
import ValorExactoDelOptimoEnLaMasaDeReserva
import EntropiaFisicaDelOptimoEnLaMallaDeReserva
namespace ArticuloA.Historias
open Perfil Repair Limites Filter Set Real
open scoped NNReal BigOperators Topology
noncomputable section
open Classical

/-- The reserve matrix is here the normalized sample of the same optimum that dominates the full value. -/
theorem existe_reserva_del_optimo_fisico :
    ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (κ A C : ℝ),0<κ ∧ 0<A ∧ 0≤C ∧
    ∀ᶠ n : ℕ in atTop,
      let x:=fraccionReserva n
      let q:=n-huecosReserva n
      let w:=cargaCelda n q (p x)
      let τ:=(n:ℝ)^(-exponenteReserva)
      sSup valoresCartesianosDeAbsorcion≤(P x).s ∧ sSup (valoresCartesianosEnMasa (1-x))=(P x).s ∧
      (q:ℝ)*log n+n*(P x).s-C≤entropiaDiscretaDeReserva w ∧ (∑ e : Cell n,w e)=(q:ℝ) ∧
      ∃ u : LineaReservable n→Bool,
        let X:=∑ e : Cell n,pesoRetenido w u e
        let v:=fun e=>((q:ℝ)/X)*pesoRetenido w u e
        0<X ∧ (∑ e : Cell n,v e)=(q:ℝ) ∧ (∀ e,0≤v e ∧ v e≤2*(A/n)) ∧
        (∀ i,masaBajo v (enLaFibra i)≤1-κ*x/4) ∧
        (q:ℝ)*log n+n*(P x).s-C-constanteB1 κ*τ*n*log (1/x)≤entropiaDiscretaDeReserva v ∧
        ∀ z : Cell n,τ^4*(q:ℝ)/8≤masaBajo v (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z) := by
  obtain ⟨P,p,b,κ,M,L,kp,k1,mm,lp,_,eq,sp,lower⟩:=existe_perfil_para_la_cota_inferior
  let A:=M^4/κ^4
  have mp : 0<M:=zero_lt_one.trans_le mm
  have ap : 0<A:=div_pos (pow_pos mp _) (pow_pos kp _)
  have βp : 0<1/(2*M^4):=by positivity
  let C:=costoDeCuadraturaBL1 κ M L
  have cp : 0≤C:=by dsimp [C,costoDeCuadraturaBL1]; positivity
  refine ⟨P,p,κ,A,C,kp,ap,cp,?_⟩
  filter_upwards [entropia_de_la_muestra_del_optimo κ M L kp k1 mm lp,margenes_fisicos_de_la_reserva κ M L kp k1 mm lp,
    B1_con_entropia_y_marcas_para_la_misma_reserva A κ κ ap kp kp k1,
    cortes_de_la_reserva,fraccion_de_reserva_tiende_a_cero.eventually_lt_const βp,
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    eventually_ge_atTop 8] with n entropy margins reserve cut tiny small big
  intro x q w τ
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have xp : 0<x:=div_pos (by exact_mod_cast (show 0<huecosReserva n from cut.1)) np
  have xx : x∈Icc 0 (1/2:ℝ):=⟨xp.le,small.le⟩
  have x1 : x≤1:=by linarith only [xx.2]
  have xx1 : x^2≤x:=by nlinarith only [mul_nonneg xp.le (sub_nonneg.mpr x1)]
  have low:=lower x xp small.le (xx1.trans tiny.le)
  have physical : x.toNNReal=fraccionHuecos n (huecosReserva n) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ xp.le]
    simp [fraccionHuecos,x,fraccionReserva]
  have e:=eq x xx
  have optimum:=valor_del_optimo_en_su_masa xp e (sp x xx) kp lp
  rw [physical] at e
  have reg:=sp x xx
  obtain ⟨rc,ob⟩:=margins e reg
  have nq:q≤n:=Nat.sub_le _ _
  have ⟨mass,pos⟩:=masa_y_signo_de_la_densidad_fisica (q:=q) (by omega : 0<n) reg kp
  have cap (v : Cell n) : w v≤A/n :=
    (le_div_iff₀ np).mpr (by simpa [w,A,mul_comm] using arista_difusa (by omega : 0<n) nq reg kp v)
  have half : (n:ℝ)/2≤(q:ℝ) := by
    have h':(huecosReserva n:ℝ)≤(1/2:ℝ)*n:=(div_le_iff₀ np).mp small.le
    dsimp [q]; rw [Nat.cast_sub cut.2.1]; linarith only [h']
  have four : (4:ℝ)≤q := by
    have bn : (8:ℝ)≤n:=by exact_mod_cast big
    linarith only [half,bn]
  have raw := entropy e reg
  change (q:ℝ)*log n+n*(P x).s-C≤entropiaDiscretaDeReserva w at raw
  obtain ⟨u,xpos,vm,vc,vf,ve,mk⟩:=reserve w q pos cap mass four (by exact_mod_cast nq) half rc ob
  exact ⟨low,optimum,raw,mass,u,xpos,vm,vc,vf,(sub_le_sub_right raw _).trans ve,mk⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existe_reserva_del_optimo_fisico
