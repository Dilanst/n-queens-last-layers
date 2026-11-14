import TelescopiaDeLasCapas
namespace ArticuloA.Capas
open ArticuloA Repair

theorem posiciones_restantes {n} (p : Placement n) (ok : Legal p) :
    available p ≤ (n-pieces p)^2 := by
  classical
  let test : Placement n → Bool := fun u => decide (Legal u)
  let cs := destinations p test
  have num : available p = cs.length := by
    simpa [available,cs,test] using (destinationLength p test).symm
  obtain ⟨rs,_,lenR,memR⟩ := freeIndices _ (distinctRows ok)
  obtain ⟨cl,_,lenC,memC⟩ := freeIndices _ (distinctColumns ok)
  have sub (z : Cell n) (hz : z ∈ cs) : z ∈ pairs rs cl := by
    obtain ⟨u,_,yes,perm⟩ := insertionWitness p test z hz
    have hu : Legal u := by simpa [test] using yes
    have hr := (List.nodup_cons.mp ((perm.map Prod.fst).nodup (distinctRows hu))).1
    have hc := (List.nodup_cons.mp ((perm.map Prod.snd).nodup (distinctColumns hu))).1
    apply List.mem_flatMap.mpr
    exact ⟨z.1,(memR _).mpr hr,List.mem_map.mpr ⟨z.2,(memC _).mpr hc,rfl⟩⟩
  have nd := List.Pairwise.sublist (destinationSublist p test) (board_unique n)
  rw [num]; simpa only [pairs_length,lenR,lenC,List.length_map,queenLength,Nat.pow_two] using
    subset_length cs (pairs rs cl) nd sub

theorem una_retirada (n h : Nat) (pos : 0 < h) (inside : h ≤ n) :
    (n-h+1)*count n (n-(h-1)) ≤ h^2*count n (n-h) := by
  classical
  rw [←interpretation n h pos inside,Nat.mul_comm (h^2),count,←sum_times]
  apply sum_mono; intro p
  by_cases yes : Legal p ∧ pieces p = n-h
  · have ge := posiciones_restantes p yes.1
    have hh : n-pieces p=h := by omega
    rw [hh] at ge; exact Nat.mul_le_mul_left _ ge
  · simp [layer,yes]

/-- Integer form of the removal lemma with the factorial cleared. -/
theorem retirar (n h : Nat) (inside : h ≤ n) :
    falling n h * count n n ≤ (fac h)^2 * count n (n-h) := by
  induction h with
  | zero => simp [falling,fac,prodTo]
  | succ j ih =>
    have a := ih (by omega)
    have b := una_retirada n (j+1) (by omega) inside
    change _ ≤ _ at b
    simp only [Nat.add_sub_cancel] at b
    have prod := Nat.mul_le_mul_left (n-(j+1)+1) a
    have prog := Nat.mul_le_mul_left ((fac j)^2) b
    change (falling n j*(n-(j+1)+1))*count n n ≤ (fac j*(j+1))^2*count n (n-(j+1))
    calc _ = (n-(j+1)+1)*(falling n j*count n n) := by ac_rfl
         _ ≤ _ := prod
         _ = (fac j)^2*((n-(j+1)+1)*count n (n-j)) := by ac_rfl
         _ ≤ _ := prog
         _ = _ := by simp only [Nat.pow_two]; ac_rfl

end ArticuloA.Capas
#print axioms ArticuloA.Capas.posiciones_restantes
#print axioms ArticuloA.Capas.retirar
