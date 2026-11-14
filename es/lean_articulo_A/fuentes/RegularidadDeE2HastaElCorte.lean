import ProbabilidadDeLaSalidaFisica
import ConstantesDeLaColaRegular
import ProyeccionAlProcesoOriginal
import BalanceFisicoCompleto
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def salidaOriginal {n} (p : FactoresContinuos) (h T : ℕ) (um : ℝ≥0) (l : List (State n)) : Prop :=
  ∃ t≤T,let X:=estadoEn (initial n h) l t
    X.failed=true ∨ um≤errorDelEstado p h X (fraccionAntes n t)

theorem regularidad_hasta_el_corte (κ m ζ C ε : ℝ≥0)
    (kp : 0<κ) (m1 : 1≤m) (zp : 0<ζ) (ep : 0<ε) (admite : ε≤piso κ ζ) :
    ∃ c : ℝ,0<c ∧ ∃ n₀ : ℕ,∀ n≥n₀,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
      ControlEspacial p κ m L → BalanceMalla n h p C →
      ∀ T≤2*n-1,ζ≤fraccionAntes n T →
      (avg masas (rutas (kernel masas (coloresDelPerfil n h p) (·⁻¹)) 0 T (initial n h))
        (mark masas (salidaOriginal p h T (ε*n)))).val ≤ Real.exp (-(c*n)) := by
  classical
  let K:=coefSeguimiento m κ ζ C
  have bp : 0<limiteSalto (m^4) m := by unfold limiteSalto; have z:=(m^4).property; linarith [m.property]
  obtain ⟨θ,α,c,N,θp,ap,cp,small,param⟩:=eleccion_del_umbral K (limiteSalto (m^4) m) ε K.property bp
    (show 0<(ε:ℝ) from ep)
  have floorPos:=piso_positivo kp zp
  obtain ⟨N₂,grow⟩:=exists_nat_gt ((2*C/piso κ ζ:ℝ≥0):ℝ)
  refine ⟨c,cp,max 2 (max N N₂),?_⟩
  intro n hn h hh p L sp bal T tN floor
  let um:=ε*n
  let w:=coloresDelPerfil n h p
  let halt:ℕ→State n→Bool:=fun _ _ => false
  let R:=rutas (pasoParado w halt) 0 T (0,initial n h)
  have n2 : 2≤n := by omega
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
  have hu : um/n≤piso κ ζ := by dsimp [um]; rw [mul_div_cancel_right₀ _ np.ne']; exact admite
  have nn : 2*C/piso κ ζ≤(n:ℝ≥0) := NNReal.coe_le_coe.mp (grow.le.trans (by exact_mod_cast (by omega : N₂≤n)))
  have ho : 2*C/n≤piso κ ζ := (div_le_iff₀ np).mpr (by simpa only [mul_comm] using (div_le_iff₀ floorPos).mp nn)
  have par:=param n (by omega) T (by omega)
  have margin : (α*n+1)*Real.exp (T*((K:ℝ)/n))<(um:ℝ) := by simpa only [um,NNReal.coe_mul,NNReal.coe_natCast] using par.1
  have tail:=probabilidad_de_salida_desde_el_tablero n2 hh sp kp m1 zp bal hu ho halt (fun _ _ _ => rfl)
    T tN floor θ (α*n) θp.le small (by positivity) margin
  let raw:=fun l : List (ℕ×State n) => salidaOriginal p h T um (l.map Prod.snd)
  have sub:=misma_masa_en_el_soporte R raw (cruzaElUmbral p h T um) (by
    intro i mem nz yes
    by_contra no
    have before (t : ℕ) (tT : t≤T) : errorDelEstado p h (estadoEn (0,initial n h) i.2 t).2 (fraccionAntes n t)<um := by
      apply lt_of_not_ge; intro hit; exact no ⟨t,tT,hit⟩
    obtain ⟨t,tT,ev⟩:=yes
    have path:=hasta_el_primer_cruce n2 hh sp kp m1 zp bal hu ho halt (fun _ _ _ => rfl) T floor i mem nz t tT
      (fun j jt => before j (jt.le.trans tT))
    have state:=estado_al_olvidar_el_reloj 0 (initial n h) i.2 t
    dsimp only at ev
    rw [←state] at ev
    rcases ev with fail | hit
    · exact Bool.noConfusion ((path.2 t le_rfl).2.1.symm.trans fail)
    · exact (not_le.mpr (before t tT)) hit)
  have proj:=ley_al_olvidar_el_reloj (kernel masas w (·⁻¹)) 0 T (initial n h) (mark masas (salidaOriginal p h T um))
  rw [←proj]
  exact (NNReal.coe_le_coe.mpr sub).trans (tail.trans par.2)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.regularidad_hasta_el_corte
