import BorradosYNacimientosSumados
import ErroresFisicosDeLosPatronesDirectos
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

def errorDelAtomo {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (e : Cell n) : ℝ≥0 :=
  ⟨|(realAtom masas X w (·⁻¹) e).val-(A.birth e/(n:ℝ≥0)^2).val|,abs_nonneg _⟩

theorem error_del_nacimiento_activo {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (nn : 0<n)
    (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (e : Cell n) (live : E2.available X (lines e)=true) :
    (n:ℝ≥0)^3*errorDelAtomo A e≤constanteUna A.l A.M C*(E+1) := by
  have active : activeLine X (0,lines e 0) := ⟨on_board e 0,List.all_eq_true.mp live 0 (by simp [List.finRange,List.mem_ofFn])⟩
  have est:=(A.estimates (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _)) _ active e).2.2.2
  rw [ns_real] at est
  have within' : within masas ((n:ℝ≥0)^2*realAtom masas X w (·⁻¹) e) (A.birth e) A.budget := by
    simpa only [pow_two] using est
  have delta := (presupuesto_absoluto _ _ _).mp within'
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast] at delta
  have np : 0<(n:ℝ) := by exact_mod_cast nn
  have bound : A.budget≤A.combined := by
    change A.budget≤(A.budget+A.vBudget)+A.time⁻¹*A.bal
    exact (le_add_of_nonneg_right (zero_le _)).trans (le_add_of_nonneg_right (zero_le _))
  have cap:=(mul_le_mul_left' bound (n:ℝ≥0)).trans (presupuesto_escalado A E C he ho hb)
  apply le_trans _ cap
  change (↑((n:ℝ≥0)^3*errorDelAtomo A e):ℝ)≤(↑((n:ℝ≥0)*A.budget):ℝ)
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast]
  let a:ℝ:=(realAtom masas X w (·⁻¹) e).val
  let b:ℝ:=(A.birth e).val
  change (n:ℝ)^3*|a-((A.birth e/(n:ℝ≥0)^2):ℝ≥0).val|≤_
  have val : ((A.birth e/(n:ℝ≥0)^2):ℝ≥0).val=b/(n:ℝ)^2 := by
    change (↑(A.birth e/(n:ℝ≥0)^2):ℝ)=(↑(A.birth e):ℝ)/(n:ℝ)^2
    push_cast; rfl
  rw [val]
  calc _ = (n:ℝ)*|(n:ℝ)^2*a-b| := by
            rw [show (n:ℝ)^2*a-b=n^2*(a-b/n^2) by field_simp; ring,abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left delta np.le

theorem errores_de_ambos_nacimientos_en_el_soporte {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (nn : 0<n) (leg : Legal X.physical) (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (primera v j₂ j₃ : Bool) :
    let a:=if primera then false else v
    let b:=if primera then v else false
    pesoDeUnaFuente n v*masas.sum (soporteDeParejas X a b j₂ j₃)
      (fun u => errorDelAtomo A (if primera then u.1 else u.2)) ≤constanteUna A.l A.M C*(E+1) := by
  intro a b
  apply suma_de_error_de_nacimiento nn X leg primera v j₂ j₃
  intro u hu
  have ok:=((miembros_del_soporte X u.1 u.2 a b j₂ j₃).mp hu).2
  apply error_del_nacimiento_activo A nn E C he ho hb
  cases primera
  · exact ok.2.1
  · exact ok.1

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.errores_de_ambos_nacimientos_en_el_soporte
