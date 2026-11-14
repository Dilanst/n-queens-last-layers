import IdentidadDeEntropiaParaElPesoCanonicoDiscreto
import RestoEntropicoFisicoParaHuecosVariables
import CotaInferiorDelLogaritmoDelNormalizador
import CotaYExtremosDesdeLaMedida
namespace ArticuloA.Historias
open Perfil Real Filter
open scoped NNReal BigOperators Topology
noncomputable section

def costoDeCuadraturaBL1 (κ M L : ℝ) :=
  2*(4*M^3*L)/κ^4 + 6*(L/κ) + 16*(4*(4*M^3*L)/κ^4)

theorem entropia_de_la_muestra_del_optimo (κ M L : ℝ) (kp : 0<κ) (k1 : κ≤1)
    (mm : 1≤M) (lp : 0≤L) :
    ∀ᶠ n : ℕ in atTop, ∀ {P p b}, EulerFisica P p (fraccionHuecos n (huecosReserva n)) b →
    ControlEspacial p κ M L →
    let q:=n-huecosReserva n
    (q:ℝ)*log n+(n:ℝ)*P.s-costoDeCuadraturaBL1 κ M L≤entropiaDiscretaDeReserva (cargaCelda n q p) := by
  filter_upwards [correccion_entropica_de_las_lineas_fisicas κ M L kp k1 mm lp,
    cortes_de_la_reserva,eventually_ge_atTop 1,
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const zero_lt_one] with n corr cut hn small
  intro P p b e sp q
  let h:=huecosReserva n
  let x:=fraccionHuecos n h
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have xp : 0<(x:ℝ):=by
    dsimp [x,fraccionHuecos]; push_cast; exact div_pos (by exact_mod_cast (show 0<h from cut.1)) np
  have xn : 0<x:=by exact_mod_cast xp
  have qn : q≤n:=Nat.sub_le _ _
  have hr : (h:ℝ)<n:=by simpa using (div_lt_iff₀ np).mp small
  have hlt : h<n:=by exact_mod_cast hr
  have qp : 0<q:=Nat.sub_pos_of_lt hlt
  have mass : (n:ℝ)*P.rho=(q:ℝ) := by
    rw [e.masa]; simp only [fraccionHuecos,NNReal.coe_div,NNReal.coe_natCast]
    dsimp [q]; rw [Nat.cast_sub cut.2.1]
    field_simp
  have imass : integralTablero (pesoContinuo p)=((q:ℝ)/n)/b := by
    rw [integral_masa_cuadrada e]
    rw [←mass]; field_simp
  have logN:=normalizador_logaritmico_desde_abajo hn qp qn kp (zero_le_one.trans mm) lp e.coef xp sp imass
  obtain ⟨de,ae⟩:=vacancia_en_los_extremos e sp lp
  have Q:=error_del_producto_de_pesos n hn p x xn κ L kp lp sp.R sp.C sp.D sp.A de ae
  have logs := (abs_le.mp Q).1
  have rest:=corr e sp
  have identity:=identidad_de_entropia_para_la_muestra (h:=h) hn qp x rfl xp kp sp
  dsimp only at identity rest
  simp_rw [virtual_de_la_malla] at identity rest
  have es : escalaLog x=x := by simp [escalaLog,xn.ne']
  have continuum:=entropia_fisica e sp kp lp
  change P.s=P.rho*(-log (b/(escalaLog x:ℝ)^2)-3)-entropiaDeFactores p (escalaLog x) at continuum
  rw [es] at continuum
  have whole : (n:ℝ)*P.s=(q:ℝ)*(-log (b/(x:ℝ)^2)-3)-(n:ℝ)*entropiaDeFactores p x := by
    rw [continuum,mul_sub,←mul_assoc,mass]
  rw [whole]
  change _≤entropiaDiscretaDeReserva (cargaCelda n q p)
  rw [identity]
  unfold costoDeCuadraturaBL1
  change -(6*(L/κ))≤ (n:ℝ)*entropiaDeFactores p x -
    (∑ i,∑ j : Indice n,log (factores (pesosMalla n x p) i j)) at logs
  dsimp only [x,h,q] at *
  linarith only [logs,logN,rest]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_la_muestra_del_optimo
