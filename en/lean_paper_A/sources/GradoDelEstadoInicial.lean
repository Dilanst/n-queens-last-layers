import SumasYMargenesDelBalance
import MasasDelTablero
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular RealFinita Limites
noncomputable section

def vInicial {n} (p : FactoresContinuos) (e : Cell n) : ℝ≥0 :=
  p.fila (medio n e.1.val)*p.columna (medio n e.2.val)*p.diagonal (medio n e.1.val-medio n e.2.val)*
    p.anti (medio n e.1.val+medio n e.2.val)

theorem peso_para_el_nucleo {n} (p : FactoresContinuos) (e : Cell n) :
    (vInicial p e:ℝ)=pesoFisico n p e := rfl

private theorem suma_de_masas {α : Type} [DecidableEq α] (l : List α) (nd : l.Nodup) (v : α→ℝ≥0) :
    (masas.sum l v:ℝ)=∑ x∈l.toFinset,(v x:ℝ) := by
  rw [←suma_lista_sin_repetidos l nd]
  induction l with
  | nil => rfl
  | cons e l ih =>
    change (v e:ℝ)+(masas.sum l v:ℝ)=(v e:ℝ)+sumReal.over l _
    exact congrArg ((v e:ℝ)+·) (ih (List.nodup_cons.mp nd).2)

theorem grado_inicial_del_proceso {n h : ℕ} (p : FactoresContinuos) (i : Fin 4) (j : Indice n) :
    (auxDegree masas (initial n h) (vInicial p) (i,j.val)).val=gradoInicial n p i j := by
  unfold auxDegree boardSum gradoInicial
  apply Eq.trans (suma_de_masas _ (board_unique n) (fun e =>
    if hitsVertex (lines e) (i,j.val) && otherLive (initial n h) i (lines e) then vInicial p e else 0))
  have all : (board n).toFinset=Finset.univ := by ext e; simp [board_complete]
  rw [all]; apply Finset.sum_congr rfl; intro e _
  have active : otherLive (initial n h) i (lines e)=true := by simp [otherLive,initial,List.all_eq_true]
  rw [active]; simp only [Bool.and_true,hitsVertex,beq_iff_eq]
  split_ifs <;> rfl
def masaActiva {n : ℕ} (p : FactoresContinuos) (X : State n) :=
  ∑ e : Cell n,if E2.available X (lines e) then pesoFisico n p e else 0
def virtualActiva {n : ℕ} (h : ℕ) (p : FactoresContinuos) (X : State n) (i : Fin 4) :=
  ∑ j : Indice n,if X.active i j.val then holguraInicial n h p i j else 0
def virtualInicial {n : ℕ} (h : ℕ) (p : FactoresContinuos) (i : Fin 4) :=
  ∑ j : Indice n,holguraInicial n h p i j

theorem margen_antes_de_la_salida {n h : ℕ} {p κ M L ζ z ε C} (hn : 0<n) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (zp : 0<ζ) (corte : ζ≤z) (eW : ε≤κ^4*ζ^4/2) (eU : ε≤ζ/4)
    (C0 : 0≤C) (grande : 4*C+2≤(n:ℝ)) (X : State n)
    (bal : ∀ i (j : Indice n),(n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤C)
    (regularW : |masaActiva p X/n-Wfisico n p*z^4/n|≤ε*n)
    (regularU : ∀ i,|virtualActiva h p X i-virtualInicial (n:=n) h p i*z|≤ε*n) :
    κ^4*ζ^4/2*(n:ℝ)^2≤masaActiva p X ∧ ∀ i,ζ/4*(n:ℝ)≤virtualActiva h p X i := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have low:=masa_inferior (n:=n) sp kp.le
  have wp : 0<Wfisico n p := (mul_pos (pow_pos kp 4) (pow_pos np 2)).trans_le low
  have z4 : ζ^4≤z^4 := pow_le_pow_left₀ zp.le corte 4
  have w4 := mul_le_mul low z4 (pow_nonneg zp.le _) wp.le
  have wm := (abs_le.mp regularW).1
  have loss := mul_le_mul_of_nonneg_right eW np.le
  constructor
  · have left : Wfisico n p*z^4-(ε*n)*n≤masaActiva p X := by
      have bound : Wfisico n p*z^4/n-ε*n≤masaActiva p X/n := by linarith
      have raw:=(le_div_iff₀ np).mp bound
      rw [sub_mul,div_mul_cancel₀ _ np.ne'] at raw
      exact raw
    have pLoss:=mul_le_mul_of_nonneg_right loss np.le
    nlinarith only [left,w4,pLoss]
  · intro i
    have u:=suma_de_holguras hn i C0 wp.ne' (bal i)
    have norm : ((2*n-1:ℕ):ℝ)=2*(n:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1≤2*n)]; norm_num
    rw [norm] at u
    have lim : (↑(n-h):ℝ)≤n := by exact_mod_cast Nat.sub_le n h
    have init : (n:ℝ)/2≤virtualInicial (n:=n) h p i := by
      unfold virtualInicial; linarith only [(abs_le.mp u).1,grande,lim]
    have compare := mul_le_mul init corte zp.le (by linarith only [np,init])
    have err:=mul_le_mul_of_nonneg_right eU np.le
    linarith only [(abs_le.mp (regularU i)).1,compare,err]
def escalaReal (n h : ℕ) : ℝ := if h=0 then 1 else (fraccionHuecos n h:ℝ)^2

theorem pesos_reales_para_el_estado {n h : ℕ} (p : FactoresContinuos) (e : Cell n) :
    wCelda (coloresDelPerfil n h p) e=escalaReal n h*pesoFisico n p e := by
  by_cases hz : h=0
  · subst h
    have eq : wCelda (coloresLlenos n (pesosMalla n 1 p)) e=wCelda (sameColors (pesosMalla n 1 p)) e := by
      unfold wCelda pesoDe; rw [Fin.prod_univ_four,Fin.prod_univ_four]; rfl
    simp [coloresDelPerfil,eq,muestra_real,escalaReal,pesoFisico]
  · simpa only [coloresDelPerfil,escalaReal,if_neg hz,pesoFisico] using muestra_real (fraccionHuecos n h) p e

theorem masas_del_nucleo_en_un_estado {n h : ℕ} (p : FactoresContinuos) (X : State n) :
    (ProfileKernel.total masas (realChoices masas X (coloresDelPerfil n h p))).val =
        escalaReal n h*masaActiva p X ∧
    (ProfileKernel.total masas (virtualChoices masas X (coloresDelPerfil n h p).virtual)).val =
        ∏ i : Fin 4,virtualActiva h p X i := by
  constructor
  · change (ProfileKernel.total masas (onList (board n) _ _ Choice.real)).val=_
    rw [Cart.total_list]; unfold masaActiva
    rw [Finset.mul_sum]
    apply Eq.trans (suma_de_masas _ (board_unique n) (fun e =>
      if E2.available X (lines e) then weights masas (coloresDelPerfil n h p).real (lines e) else 0))
    have all : (board n).toFinset=Finset.univ := by ext e; simp [board_complete]
    rw [all]; apply Finset.sum_congr rfl; intro e _
    by_cases ok : E2.available X (lines e)=true
    · rw [if_pos ok,if_pos ok]
      exact (cuatro_pesos _ (tuplaReal e)).trans (pesos_reales_para_el_estado p e)
    · simp [ok]
  · rw [Cart.normalizer]
    have eq (i : Fin 4) : (Cart.part masas X (coloresDelPerfil n h p).virtual i).val=virtualActiva h p X i := by
      unfold Cart.part
      rw [←List.map_coe_finRange,Cart.sum_map]
      apply Eq.trans (suma_de_masas _ (List.nodup_finRange _) (fun j : Indice n =>
        if X.active i j.val then (coloresDelPerfil n h p).virtual i j.val else 0))
      simp only [List.toFinset_finRange]
      apply Finset.sum_congr rfl; intro j _
      cases bit : X.active i j.val <;> simp [bit,holguraInicial,factores]
    rw [Fin.prod_univ_four,←eq 0,←eq 1,←eq 2,←eq 3]
    change (_*_)*(_*_) = ((_*_)*_)*_
    ring

theorem ambos_normalizadores_positivos {n h : ℕ} (hn : 0<n) (p : FactoresContinuos) (X : State n)
    (w : 0<masaActiva p X) (u : ∀ i,0<virtualActiva h p X i) :
    0<(ProfileKernel.total masas (realChoices masas X (coloresDelPerfil n h p))).val ∧
    0<(ProfileKernel.total masas (virtualChoices masas X (coloresDelPerfil n h p).virtual)).val := by
  obtain ⟨wr,wv⟩:=masas_del_nucleo_en_un_estado (h:=h) p X
  rw [wr,wv]
  have ep : 0<escalaReal n h := by
    unfold escalaReal; split_ifs with hz
    · exact zero_lt_one
    · have pos : 0<fraccionHuecos n h := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hn)
      exact pow_pos (by exact_mod_cast pos) 2
  exact ⟨mul_pos ep w,Finset.prod_pos (fun i _ => u i)⟩
theorem eleccion_sin_fallo_por_masa_nula {n h : ℕ} (hn : 0<n) (p : FactoresContinuos) (X : State n)
    (w : 0<masaActiva p X) (u : ∀ i,0<virtualActiva h p X i) (real : Bool) :
    let v:=if real then realChoices masas X (coloresDelPerfil n h p)
      else virtualChoices masas X (coloresDelPerfil n h p).virtual
    ProfileKernel.choose masas v Choice.fail (·⁻¹)=v.map (fun i => (((ProfileKernel.total masas v)⁻¹)*i.1,i.2)) := by
  obtain ⟨r,v⟩:=ambos_normalizadores_positivos (h:=h) hn p X w u
  have vn : ProfileKernel.total masas (virtualChoices masas X (coloresDelPerfil n h p).virtual)≠masas.zero := by
    intro zero; rw [zero] at v; exact (lt_irrefl (0:ℝ)) v
  have rn : ProfileKernel.total masas (realChoices masas X (coloresDelPerfil n h p))≠masas.zero := by
    intro zero; rw [zero] at r; exact (lt_irrefl (0:ℝ)) r
  cases real <;> simp [ProfileKernel.choose,rn,vn] <;> intros <;> rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.grado_inicial_del_proceso
#print axioms ArticuloA.Historias.margen_antes_de_la_salida
#print axioms ArticuloA.Historias.ambos_normalizadores_positivos
#print axioms ArticuloA.Historias.eleccion_sin_fallo_por_masa_nula
