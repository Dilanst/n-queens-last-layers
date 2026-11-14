import ConteoDeLosParcialesQueSalenDeLaReservaFisica
import ArticuloADesdeLaEntropiaDeLosParcialesReservados
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Filter Perfil
open scoped Topology

/-- The same choice of reserve is used in the path entropy and in the failure control. -/
theorem articulo_A_desde_la_entropia_del_camino_fisico (v : (n : ℕ)→Cell n→ℝ≥0)
    (D A : ℕ→ℤ→Prop) (d : ℕ→ℝ≥0) (r : ℕ→ℝ)
    (loss : Tendsto (fun n : ℕ=>r n/(n:ℝ)) atTop (𝓝 0))
    (hyp : ∀ᶠ n : ℕ in atTop,
      let h:=huecosReserva n
      let q:=n-h
      falloDelParcialReservado (v n) q h (D n) (A n) (d n)≤25/(n:ℝ)^2 ∧
      (q:ℝ)*log n+(n:ℝ)*sSup valoresCartesianosDeAbsorcion-r n≤
        entropiaDeEstados (rutas (pasoDeG (v n) q) 0 q (some []))-log q.factorial) :
    ConclusionDelArticuloA := by
  classical
  let f (n : ℕ) (s : Finset (Cell n)):=elegirCasillas s (board n)
  let O (n : ℕ):=(parcialesDeReserva (n:=n) (huecosReserva n) (D n) (A n)).image (f n)
  let R (n : ℕ):=r n+(huecosReserva n:ℝ)*log n+51*log n
  have ll : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)) atTop (𝓝 0):=by
    simpa using ((isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have norm : Tendsto (fun n : ℕ=>R n/(n:ℝ)) atTop (𝓝 0):=by
    have combined:=((loss.add (perdida_de_marcas_en_la_escala_de_G.div_const 4)).add (ll.const_mul 51))
    simp only [zero_div,add_zero,mul_zero] at combined
    apply combined.congr'
    filter_upwards with n
    dsimp [R]
    ring
  apply articulo_desde_las_salidas_de_G (C:=1/8000) (d:=4*exponenteReserva) (by norm_num [exponenteReserva])
    huecosReserva O R (Eventually.of_forall (fun _=>Nat.floor_le (by positivity))) norm
  filter_upwards [hyp,cortes_de_la_reserva,eventually_ge_atTop 6] with n hs cut n6
  let h:=huecosReserva n
  let q:=n-h
  let S:=parcialesDeReserva (n:=n) h (D n) (A n)
  let bad:=falloDelParcialReservado (v n) q h (D n) (A n) (d n)
  have nh : h≤n:=cut.2.1
  have nb : (6:ℝ)≤n:=by exact_mod_cast n6
  have np : 0<(n:ℝ):=by linarith
  obtain ⟨bb,hh⟩:=hs
  change bad≤25/(n:ℝ)^2 at bb
  have small : bad<1:=bb.trans_lt ((div_lt_one (sq_pos_of_pos np)).mpr (by nlinarith))
  have size : q+h=n:=Nat.sub_add_cancel nh
  have raw:=conteo_fisico_de_parciales_desde_las_elecciones (by omega : 0<n) (v n) (D n) (A n) (d n) size small
  obtain ⟨nonempty,ct⟩:=raw
  have fi : Function.Injective (f n):=fun s t eq=>by simpa only [f,soporte_elegido] using congrArg soporteFisico eq
  have card : (O n).card=S.card:=Finset.card_image_of_injective S fi
  have logn : 0≤log (n:ℝ):=Real.log_nonneg (by linarith)
  have log2 : log (2:ℝ)≤log n:=Real.log_le_log (by norm_num) (by linarith)
  have qle : (q:ℝ)≤n:=by exact_mod_cast Nat.sub_le n h
  have b1 : bad*(n:ℝ)≤25:=by
    have bn:= (le_div_iff₀ (sq_pos_of_pos np)).mp bb
    have bnon : 0≤bad:=NNReal.coe_nonneg _
    have nsmall : (n:ℝ)≤(n:ℝ)^2:=by nlinarith
    exact (mul_le_mul_of_nonneg_left nsmall bnon).trans bn
  have bq:= (mul_le_mul_of_nonneg_left qle (show 0≤bad from NNReal.coe_nonneg _)).trans b1
  have penalty : bad*(2*(q:ℝ)*log n)≤50*log n:=by
    calc _ = (2*(bad*(q:ℝ)))*log n:=by ring
         _ ≤ _:=mul_le_mul_of_nonneg_right (by linarith only [bq]) logn
  refine ⟨nonempty.image (f n),?_,D n,A n,?_⟩
  · rw [card]
    change entropiaDeEstados _-log q.factorial-log 2-bad*(2*(q:ℝ)*log n)≤log (S.card:ℝ) at ct
    change (q:ℝ)*log n+_ -r n≤entropiaDeEstados _-log q.factorial at hh
    have qr : (q:ℝ)=n-(h:ℝ):=Nat.cast_sub nh
    rw [qr,sub_mul] at hh
    dsimp only [R,h] at *
    linarith only [ct,hh,penalty,log2]
  · intro p hp
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp hp
    exact (pertenencia_al_conteo_de_reserva _ _ _ _).mp hs
end
end ArticuloA.Historias

#print axioms ArticuloA.Historias.articulo_A_desde_la_entropia_del_camino_fisico
