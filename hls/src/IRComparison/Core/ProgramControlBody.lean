import IRComparison.Core.ProgramControlIR
import IRComparison.Core.BodyBackends

namespace IRComparison.ProgramControlIR

theorem body_run_reaches (i x y : Int) (n : Nat) (c : ControlIR.Config) :
    ControlIR.Reaches i x y c (ControlIR.run i x y n c) := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih => exact .next (ih _)

theorem body_from_finishes (input : Input) (code : List ControlIR.Instr) (meaning : Step State)
    (h : ∀ i x y s, ∃ n, ControlIR.run i x y n (.running code s []) = .stopped (meaning i x y s)) :
    BodyCorrect input code meaning := by
  intro f s rest
  obtain ⟨n,hn⟩ := h f.index f.left f.right s
  apply Reaches.next
  apply lift_body
  have reaches := body_run_reaches f.index f.left f.right n (.running code s [])
  rw [hn] at reaches
  exact reaches

theorem optimizedBody_finishes (code : List ControlIR.Instr) (meaning : Step State)
    (body : ∀ i x y s, ∃ n, ControlIR.run i x y n (.running code s []) = .stopped (meaning i x y s))
    (i d : Int) (n : Nat) (l r : Int) (input : Input) (s : State) :
    ∃ fuel, run input fuel (.running (optimizedLoopCode i d n l r code) s initial) =
      .stopped (BodyBackends.runSource meaning i d n l r input s) := by
  have hb := body_from_finishes input code meaning body
  have finish {c : Config} {result : Option State} (f : Frame)
      (h : Reaches input c (resume result [] f)) : ∃ fuel, run input fuel c = .stopped result := by
    apply Reaches.finite
    apply h.trans
    cases result <;> simp [resume]
    · exact .refl _
    · exact .next (.refl _)
  simp only [BodyBackends.runSource,NativeLoop.run_readBody]
  by_cases overlap : r = l+d
  · subst r
    rw [readLoop_overlap]
    cases n with
    | zero => exact ⟨1,by simp [optimizedLoopCode,bufferedCode,run,step,sourceLoop]⟩
    | succ n =>
      cases hr : input (i+l) with
      | none =>
        refine ⟨3,?_⟩
        simp [optimizedLoopCode,bufferedCode,run,step,hr,sourceLoop]
      | some x =>
        obtain ⟨f,hf⟩ := bufferedRepeat_generic input code meaning hb d l (n+1) ⟨i,x,0⟩ s []
        have hh : Reaches input (.running (optimizedLoopCode i d (n+1) l (l+d) code) s initial)
            (resume (sourceLoop (fun j => input (j+l)) meaning d (n+1) i s) [] f) := by
          apply Reaches.next
          apply Reaches.next
          simpa [optimizedLoopCode,bufferedCode,step,hr,Imperative.bufferedLoop_correct (fun j => input (j+l)) meaning d (n+1) i ⟨s,x⟩ hr] using hf
        exact finish f hh
  · obtain ⟨f,hf⟩ := readRepeat_generic input code meaning hb d l r n ⟨i,0,0⟩ s []
    apply finish f
    apply Reaches.next
    simpa [optimizedLoopCode,overlap,loopCode,step] using hf

end IRComparison.ProgramControlIR
