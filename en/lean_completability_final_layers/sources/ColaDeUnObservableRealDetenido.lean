import MediaDeUnaSumaDeMarcas
import ColaFisicaConDerivaFirmada
import PasosPositivosDeUnaHistoria
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto

theorem cola_del_observable_real {X : Type} (S : ℕ→X→Atoms ℝ≥0 X) (Φ : X→ℝ)
    (U J : ℝ≥0) (norm : ∀ t x,total masas (S t x)=1)
    (jump : ∀ t x,∀ i∈S t x,|Φ i.2-Φ x|≤(J:ℝ))
    (drift : ∀ t x,|media (S t x) (fun y => Φ y-Φ x)|≤(U:ℝ))
    (T : ℕ) (x : X) (θ a : ℝ) (tp : 0≤θ) (small : θ*(2*(J:ℝ))≤1) :
    (avg masas (rutas S 0 T x) (mark masas (fun l =>
      a+T*(U:ℝ)≤|Φ (l.foldl (fun _ y => y) x)-Φ x|))).val ≤
      2*Real.exp ((T:ℝ)*(θ*(2*(J:ℝ)))^2-θ*a) := by
  let F:=fun y => (Φ y).toNNReal
  let G:=fun y => (-Φ y).toNNReal
  have split (y) : (F y:ℝ)-(G y:ℝ)=Φ y := by
    change max (Φ y) 0-max (-Φ y) 0=Φ y
    rcases le_total 0 (Φ y) with hy|hy
    · rw [max_eq_left hy,max_eq_right (neg_nonpos.mpr hy),sub_zero]
    · rw [max_eq_right hy,max_eq_left (neg_nonneg.mpr hy)]; ring
  have mu (t y) : media (S t y) Φ=(avg masas (S t y) F:ℝ≥0).val-(avg masas (S t y) G:ℝ≥0).val := by
    simpa only [split] using media_sub (S t y) F G
  have increment (t y) : media (S t y) (fun z => Φ z-Φ y)=media (S t y) Φ-Φ y := by
    simpa only [one_mul,sub_eq_add_neg] using media_con_constante (S t y) (norm t y) Φ (-Φ y) 1
  have budget (t y) : within masas (avg masas (S t y) F+G y) (avg masas (S t y) G+F y) U := by
    apply (presupuesto_absoluto _ _ _).mpr
    rw [NNReal.coe_add,NNReal.coe_add]
    have eq:=drift t y
    rw [increment,mu,←split y] at eq
    rw [show ∀ a b c d : ℝ,a+b-(c+d)=a-c-(d-b) by intros; ring]
    exact eq
  have paths (l : List X) (t : ℕ) (y : X) : pasosConDeriva S F G U t y l := by
    induction l generalizing t y with
    | nil => trivial
    | cons z zs ih => exact ⟨budget t y,ih (t+1) z⟩
  have cent (t y) (i) (hi : i∈S t y) :
      within masas (F i.2+avg masas (S t y) G) (G i.2+avg masas (S t y) F) (2*J) := by
    apply (presupuesto_absoluto _ _ _).mpr
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
    have av:=promedio_de_un_resto (S t y) (norm t y) (fun z => Φ z-Φ y) J (jump t y)
    have cb:=abs_sub (Φ i.2-Φ y) (media (S t y) (fun z => Φ z-Φ y))
    have bound:=cb.trans (add_le_add (jump t y i hi) av)
    rw [increment,mu,←split i.2] at bound
    rw [←two_mul] at bound
    have rearr (a b c d u k : ℝ) (h : |a-c-u-(d-b-u)|≤k) : |a+b-(c+d)|≤k := by
      rw [show a+b-(c+d)=a-c-u-(d-b-u) by ring]; exact h
    exact rearr _ _ _ _ (Φ y) _ bound
  have estimate:=cola_del_valor_en_buenas_historias S F G U (2*J) (fun _ => True) norm (by simp)
    (fun t y _ i hi => cent t y i hi) 0 T x trivial θ a tp (by simpa using small)
  apply le_trans _ estimate
  apply NNReal.coe_le_coe.mpr
  apply misma_masa_en_el_soporte
  intro i mem nz large
  exact ⟨(pasos_con_peso mem nz).1,paths i.2 0 x,by simpa only [split] using large⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_del_observable_real
