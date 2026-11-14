import ToleranciasDeCrucesEnLaReservaFisica
import FluctuacionesFisicasDeTableroMarcasYLineas
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter
open scoped Topology

theorem los_huecos_superan_al_logaritmo :
    ∀ᶠ n : ℕ in atTop,log (n:ℝ)≤(huecosReserva n:ℝ) := by
  let a:=1-4*exponenteReserva
  have ap : 0<a:=by norm_num [a,exponenteReserva]
  have limit : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^a) atTop (𝓝 0):=
    (isLittleO_log_rpow_atTop ap).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have big : Tendsto (fun n : ℕ=>(n:ℝ)^a) atTop atTop:=(tendsto_rpow_atTop ap).comp tendsto_natCast_atTop_atTop
  filter_upwards [limit.eventually_lt_const (by norm_num : (0:ℝ)<1/16000),
    big.eventually_ge_atTop 16000,eventually_ge_atTop 1] with n lo hi hn
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have small:=(div_lt_iff₀ (Real.rpow_pos_of_pos np a)).mp lo
  have floor:=Nat.lt_floor_add_one ((1/8000:ℝ)*(n:ℝ)^a)
  change _≤(⌊(1/8000:ℝ)*(n:ℝ)^a⌋₊:ℝ)
  linarith only [small,hi,floor]

theorem fallo_del_seguimiento_a_escala_inversa :
    ∀ᶠ n : ℕ in atTop,
    let m:=huecosReserva n
    let q:=n-m
    let d:=Real.toNNReal (100*fraccionReserva n)
    (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)*(q+1)*(2*exp (-(log (n:ℝ))^2))+
        (n:ℝ)^2*exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6)≤25/(n:ℝ)^2 := by
  have large:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (6:ℝ)
  filter_upwards [cortes_de_la_reserva,large,los_huecos_superan_al_logaritmo,eventually_ge_atTop 1,
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with n cut lg hlog hn small
  intro m q d
  change 6≤log (n:ℝ) at lg
  have one : (1:ℝ)≤n:=by exact_mod_cast hn
  have np : 0<(n:ℝ):=by linarith
  have x : 0≤fraccionReserva n:=by unfold fraccionReserva; positivity
  have eq : fraccionReserva n*n=(m:ℝ):=by dsimp [fraccionReserva,m]; field_simp
  have qeq : (q:ℝ)=(n:ℝ)-(m:ℝ):=Nat.cast_sub cut.2.1
  have half : (n:ℝ)/2≤q:=by have h:=mul_le_mul_of_nonneg_right small.le np.le; linarith only [eq,h,qeq]
  have qb : (q:ℝ)≤n:=by exact_mod_cast Nat.sub_le n m
  have l0 : 0≤log n:=by linarith only [lg]
  have invexp (b : ℕ) : exp (-(b:ℝ)*log (n:ℝ))=1/(n:ℝ)^b:=by
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log np,one_div]
  have e1 : exp (-(log (n:ℝ))^2)≤1/(n:ℝ)^6:=by
    calc _ ≤ exp (-6*log (n:ℝ)):=Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg l0 (sub_nonneg.mpr lg)])
         _ = _:=by simpa using invexp 6
  have de : (d:ℝ)=100*fraccionReserva n:=Real.coe_toNNReal _ (by positivity)
  have e2 : exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6)≤1/(n:ℝ)^4:=by
    calc _ ≤ exp (-4*log (n:ℝ)):=by
           apply Real.exp_le_exp.mpr
           push_cast; rw [de]
           have a:=mul_le_mul_of_nonneg_left half x
           change log (n:ℝ)≤(m:ℝ) at hlog
           nlinarith only [a,eq,hlog,l0]
         _ = _:=by simpa using invexp 4
  have card : (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)≤6*(n:ℝ)^2:=by
    simp [IndiceDeSeguimiento,Cell,Fintype.card_option,Fintype.card_sum,Fintype.card_prod]
    nlinarith only [one,sq_nonneg ((n:ℝ)-1)]
  have count : (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)*(q+1)≤12*(n:ℝ)^3:=by
    have hh:=mul_le_mul card (by linarith only [qb,one] : (q:ℝ)+1≤2*n) (by positivity) (by positivity)
    nlinarith only [hh]
  have first:=mul_le_mul count (mul_le_mul_of_nonneg_left e1 (by norm_num : (0:ℝ)≤2)) (by positivity) (by positivity)
  have second:=mul_le_mul_of_nonneg_left e2 (sq_nonneg (n:ℝ))
  apply (add_le_add first second).trans
  have geom : 12*(n:ℝ)^3*(2*(1/(n:ℝ)^6))+(n:ℝ)^2*(1/(n:ℝ)^4)=
      (24/(n:ℝ)+1)/(n:ℝ)^2:=by field_simp; ring
  rw [geom]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n:ℝ))
  have h : 24/(n:ℝ)≤24:=(div_le_iff₀ np).mpr (by linarith only [one])
  linarith only [h]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.fallo_del_seguimiento_a_escala_inversa
