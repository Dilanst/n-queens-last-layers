import DescomposicionEnLaHistoriaDetenida
open scoped NNReal
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
variable {X : Type}

theorem pasos_con_peso {S : ℕ→X→Atoms ℝ≥0 X} {t T : ℕ} {x : X} {i : ℝ≥0×List X}
    (mem : i∈rutas S t T x) (nz : i.1≠0) :
    i.2.length=T ∧ ∀ j<T,∃ a∈S (t+j) (estadoEn x i.2 j),a.1≠0 ∧ a.2=estadoEn x i.2 (j+1) := by
  induction T generalizing t x i with
  | zero =>
    obtain rfl:=List.mem_singleton.mp mem
    exact ⟨rfl,by intro j hj; omega⟩
  | succ T ih =>
    obtain ⟨a,ha,tail⟩:=List.mem_flatMap.mp mem
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp tail
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hb
    change a.1*i.1≠0 at nz
    have az: a.1≠0 := left_ne_zero_of_mul nz
    have iz: i.1≠0 := right_ne_zero_of_mul nz
    obtain ⟨len,steps⟩:=ih hi iz
    change (a.2::i.2).length=_ ∧ _
    refine ⟨by simp [len],?_⟩
    intro j hj
    cases j with
    | zero => exact ⟨a,ha,az,rfl⟩
    | succ j =>
      obtain ⟨v,hv,vp,eq⟩:=steps j (by omega)
      refine ⟨v,?_,vp,eq⟩
      simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_comm 1 j] using hv

theorem misma_masa_en_el_soporte (row : Atoms ℝ≥0 X) (bad good : X→Prop)
    (imp : ∀ i∈row,i.1≠0 → bad i.2 → good i.2) :
    avg masas row (mark masas bad)≤avg masas row (mark masas good) := by
  classical
  induction row with
  | nil => rfl
  | cons a l ih =>
    change a.1*mark masas bad a.2+_≤a.1*mark masas good a.2+_
    apply add_le_add _ (ih (fun i hi => imp i (by simp [hi])))
    by_cases az : a.1=0
    · simp [az]
    by_cases h : bad a.2
    · simp only [mark,if_pos h,if_pos (imp a (by simp) az h),le_refl]
    · simp only [mark,if_neg h]; change a.1*0≤_; rw [mul_zero]; exact zero_le _
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.pasos_con_peso
#print axioms ArticuloA.RealFinita.misma_masa_en_el_soporte
