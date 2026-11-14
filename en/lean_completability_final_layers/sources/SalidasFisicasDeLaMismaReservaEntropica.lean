import PrimeraSalidaConLaReservaDelOptimoFisico
import ProbabilidadDeUnParcialConCandidatasEnCadaCruz
import ToleranciasDeCrucesEnLaReservaFisica
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter Perfil
open scoped Topology

theorem reserva_del_optimo_con_probabilidad_de_parciales_legales :
    ∃ (κ A C : ℝ),0<κ ∧ 0<A ∧ 0≤C ∧ ∀ᶠ n : ℕ in atTop,
    let m:=huecosReserva n
    let q:=n-m
    let x:=fraccionReserva n
    let τ:=(n:ℝ)^(-exponenteReserva)
    let η:=κ*x/4
    let d:=Real.toNNReal (100*x)
    ∃ (u : LineaReservable n→Bool) (v : Cell n→ℝ≥0),
      let D:=oblicuaMarcada u etiquetaD 2
      let F:=oblicuaMarcada u etiquetaA 3
      (∑ e,(v e:ℝ))=q ∧ (∀ e,(v e:ℝ)≤2*(A/n)) ∧ (∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) ∧
      (∀ e,v e≠0→¬D (llaveDeLinea 2 e) ∧ ¬F (llaveDeLinea 3 e)) ∧
      (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-C-constanteB1 κ*τ*n*log (1/x)≤
        entropiaDiscretaDeReserva (fun e=>(v e:ℝ)) ∧
      colaParaTodasLasMarcas v q η (2*(A/n)) ∧
      falloDelParcialReservado v q m D F d≤
        (Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ)*(q+1)*(2*exp (-(log (n:ℝ))^2))+
        (n:ℝ)^2*exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6) := by
  obtain ⟨κ,A,C,kp,ap,cp,source⟩:=existe_reserva_fisica_con_cola_simultanea
  let ν:=max 1 (2*A)
  have v1 : 1≤ν:=le_max_left _ _
  have vn : 0≤ν:=by linarith only [v1]
  have tiny:=(error_fisico_tiende_a_cero kp vn).eventually_lt_const (by norm_num : (0:ℝ)<1/80)
  have logs:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ)
  refine ⟨κ,A,C,kp,ap,cp,?_⟩
  filter_upwards [source,parametros_del_seguimiento_en_la_reserva kp,tiny,logs,umbrales_de_las_cruces kp vn,
    cortes_de_la_reserva] with n src pars tol a1 sizes cuts
  intro m q x τ η d
  obtain ⟨u,v,mass,cap,slack,avoids,marks,ent,tail⟩:=src
  obtain ⟨np,qp,hp,h4,sm,_,scale⟩:=pars
  obtain ⟨_,dm,d1,dsize,mt⟩:=sizes
  refine ⟨u,v,mass,cap,slack,avoids,ent,tail,?_⟩
  let D:=oblicuaMarcada u etiquetaD 2
  let F:=oblicuaMarcada u etiquetaA 3
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have cap' e : (v e:ℝ)≤ν/n:=by
    apply (cap e).trans
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_right _ _) nr.le
  have marks' z : (d:ℝ)*q≤∑ e,(v e:ℝ)*(mark masas (marcasDeG D F z) e).val:=by
    rw [←masa_B1_como_marca]
    apply le_trans _ (marks z)
    have h:=mul_le_mul_of_nonneg_right dm (Nat.cast_nonneg (α:=ℝ) q)
    change (d:ℝ)*q≤τ^4/8*q at h
    linarith only [h]
  have b:=cola_fisica_de_B2 np qp (Nat.sub_le _ _) v mass (marcasDeG D F) d marks'
    hp h4 v1 a1 scale cap' slack sm tol.le mt
  exact fallo_total_del_parcial v D F d (log n) (Nat.sub_add_cancel cuts.2.1) avoids d1 dsize b
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reserva_del_optimo_con_probabilidad_de_parciales_legales
