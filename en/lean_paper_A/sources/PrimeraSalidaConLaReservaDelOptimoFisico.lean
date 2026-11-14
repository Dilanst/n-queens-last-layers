import ProbabilidadDeUnaSalidaFisicaEnLaReserva
import EscalaDelErrorFisicoEnLaReserva
import ConcentracionEnLaMismaReservaDelOptimo
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter Perfil
open scoped Topology

theorem error_fisico_tiende_a_cero {κ ν : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    Tendsto (errorFisicoReserva κ ν) atTop (𝓝 0) := by
  have limit:=(error_fisico_incluso_en_dos_fracciones kp vn).mul (fraccion_de_reserva_tiende_a_cero.pow 2)
  simp only [zero_mul] at limit
  apply limit.congr'
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1] with n cut hn
  have xp : 0<fraccionReserva n:=div_pos (by exact_mod_cast cut.1) (by exact_mod_cast (show 0<n by omega))
  exact div_mul_cancel₀ _ (pow_ne_zero 2 xp.ne')

def cotaFisicaDeLaReserva {n} (v : Cell n→ℝ≥0) (q : ℕ) (E : ℝ) : Prop :=
  (avg masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fallaElSeguimiento v q E))).val≤
    (Fintype.card (IndiceDeSeguimiento n Unit):ℝ)*(q+1)*(2*exp (-(log (n:ℝ))^2))

theorem reserva_del_optimo_con_seguimiento_del_tablero :
    ∃ (κ A C : ℝ),0<κ ∧ 0<A ∧ 0≤C ∧ ∀ᶠ n : ℕ in atTop,
    let q:=n-huecosReserva n
    let x:=fraccionReserva n
    let τ:=(n:ℝ)^(-exponenteReserva)
    let η:=κ*x/4
    ∃ (u : LineaReservable n→Bool) (v : Cell n→ℝ≥0),
      (∑ e,(v e:ℝ))=q ∧ (∀ e,(v e:ℝ)≤2*(A/n)) ∧ (∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) ∧
      (∀ e,v e≠0→¬oblicuaMarcada u etiquetaD 2 (llaveDeLinea 2 e) ∧ ¬oblicuaMarcada u etiquetaA 3 (llaveDeLinea 3 e)) ∧
      (∀ z,τ^4*(q:ℝ)/8≤masaBajo (fun e=>(v e:ℝ)) (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z)) ∧
      (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-C-constanteB1 κ*τ*n*log (1/x)≤
        entropiaDiscretaDeReserva (fun e=>(v e:ℝ)) ∧
      colaParaTodasLasMarcas v q η (2*(A/n)) ∧ cotaFisicaDeLaReserva v q (errorFisicoReserva κ (max 1 (2*A)) n) := by
  obtain ⟨κ,A,C,kp,ap,cp,source⟩:=existe_reserva_fisica_con_cola_simultanea
  let ν:=max 1 (2*A)
  have v1 : 1≤ν:=le_max_left _ _
  have vn : 0≤ν:=by linarith only [v1]
  have tiny:=(error_fisico_tiende_a_cero kp vn).eventually_lt_const (by norm_num : (0:ℝ)<1/10)
  have logs:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ)
  refine ⟨κ,A,C,kp,ap,cp,?_⟩
  filter_upwards [source,parametros_del_seguimiento_en_la_reserva kp,tiny,logs] with n src pars tol a1
  intro q x τ η
  obtain ⟨u,v,mass,cap,slack,avoids,marks,ent,tail⟩:=src
  obtain ⟨np,qp,hp,h4,sm,_,scale⟩:=pars
  refine ⟨u,v,mass,cap,slack,avoids,marks,ent,tail,?_⟩
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have cap' e : (v e:ℝ)≤ν/n:=by
    apply (cap e).trans
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_right _ _) nr.le
  exact probabilidad_de_primera_salida np qp (Nat.sub_le _ _) v mass (fun (_ : Unit) _=>(1:ℝ)) ()
    (fun _=>rfl) (fun _ _=>zero_le_one) (fun _ _=>le_rfl) hp h4 v1 a1 scale cap' slack sm tol.le
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reserva_del_optimo_con_seguimiento_del_tablero
