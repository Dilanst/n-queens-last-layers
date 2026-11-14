import AplicacionDeLaCotaEntropicaALaReservaOptima
import ArticuloADesdeLaEntropiaDelCaminoFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Filter Perfil
open scoped Topology

def perdidaDeLaPrueba (κ ν C : ℝ) (n : ℕ) : ℝ :=
  C+|constanteB1 κ| * (n:ℝ)^(-exponenteReserva)*n*log n+
    (2+log n+(n:ℝ)*gastoPorEleccion κ ν n)

theorem la_perdida_final_es_sublineal {κ ν C : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    Tendsto (fun n : ℕ=>perdidaDeLaPrueba κ ν C n/(n:ℝ)) atTop (𝓝 0) := by
  have ap : 0<exponenteReserva:=by norm_num [exponenteReserva]
  have a : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^exponenteReserva) atTop (𝓝 0):=
    (isLittleO_log_rpow_atTop ap).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have l : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)) atTop (𝓝 0):=by
    simpa using ((isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have h:=(((tendsto_const_div_atTop_nhds_zero_nat (C+2)).add (a.const_mul |constanteB1 κ|)).add l).add
    (costo_medio_de_la_reserva_tiende_a_cero kp vn)
  simp only [mul_zero,zero_add,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n top
  have np : 0<(n:ℝ):=by exact_mod_cast top
  dsimp only [perdidaDeLaPrueba]
  rw [Real.rpow_neg np.le]
  field_simp [np.ne',(Real.rpow_pos_of_pos np exponenteReserva).ne']; ring

theorem conclusion_del_articulo_A_para_los_tableros_fisicos : ConclusionDelArticuloA := by
  classical
  obtain ⟨κ,A,C,hκ,hA,_,witness⟩:=existe_reserva_con_fallo_cuadratico_y_entropia_de_entrada
  let ν:=max 1 (2*A)
  have v1 : 1≤ν:=le_max_left _ _
  have vn : 0≤ν:=by linarith only [v1]
  let d (n : ℕ):=Real.toNNReal (100*fraccionReserva n)
  let r:=perdidaDeLaPrueba κ ν C
  let good (n : ℕ) (y : (LineaReservable n→Bool)×(Cell n→ℝ≥0)) : Prop :=
    let q:=n-huecosReserva n
    falloDelParcialReservado y.2 q (huecosReserva n) (oblicuaMarcada y.1 etiquetaD 2) (oblicuaMarcada y.1 etiquetaA 3) (d n)≤25/(n:ℝ)^2 ∧
      (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-r n≤entropiaDeEstados (rutas (pasoDeG y.2 q) 0 q (some []))-log q.factorial
  have many : ∀ᶠ n : ℕ in atTop,∃ y,good n y:=by
    filter_upwards [witness,entropia_fisica_de_cualquier_peso_en_la_reserva hκ v1,cortes_de_la_reserva,eventually_ge_atTop 1] with n w phys cut one
    obtain ⟨u,v,mass,cap,slack,_,ent,_,fail⟩:=w
    refine ⟨(u,v),fail,?_⟩
    let q:=n-huecosReserva n
    let x:=fraccionReserva n
    let τ:=(n:ℝ)^(-exponenteReserva)
    have nr : 0<(n:ℝ):=by exact_mod_cast one
    have cap' e : (v e:ℝ)≤ν/n:=by
      apply (cap e).trans
      rw [←mul_div_assoc]
      exact div_le_div_of_nonneg_right (le_max_right _ _) nr.le
    have a:=phys v mass cap' slack
    have xp : 0<x:=div_pos (by exact_mod_cast cut.1) nr
    have inv : 1/x≤n:=by
      apply (div_le_iff₀ xp).mpr
      have mh : (1:ℝ)≤huecosReserva n:=by exact_mod_cast cut.1
      convert mh using 1
      dsimp [x,fraccionReserva]; field_simp
    have x1 : x≤1:=(div_le_one nr).mpr (by exact_mod_cast cut.2.1)
    have lx : 0≤log (1/x):=Real.log_nonneg ((one_le_div xp).mpr x1)
    have tn : 0≤τ:=Real.rpow_nonneg nr.le _
    have lc : constanteB1 κ*τ*n*log (1/x)≤|constanteB1 κ| * τ*n*log n:=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) tn) nr.le)
        (Real.log_le_log (one_div_pos.mpr xp) inv) lx (by positivity)
    change (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-(C+|constanteB1 κ| * τ*n*log n+(2+log n+n*gastoPorEleccion κ ν n))≤_
    change (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-C-constanteB1 κ*τ*n*log (1/x)≤entropiaDiscretaDeReserva _ at ent
    linarith only [ent,lc,a]
  let y n:=Classical.epsilon (good n)
  apply articulo_A_desde_la_entropia_del_camino_fisico (fun n=>(y n).2) (fun n=>oblicuaMarcada (y n).1 etiquetaD 2)
    (fun n=>oblicuaMarcada (y n).1 etiquetaA 3) d r (la_perdida_final_es_sublineal hκ vn)
  filter_upwards [many] with n existsY
  exact Classical.epsilon_spec existsY

end
end ArticuloA.Historias
#check ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos
#print axioms ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos
