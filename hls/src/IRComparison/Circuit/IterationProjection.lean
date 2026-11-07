import IRComparison.Circuit.MemoryProjection
import IRComparison.Circuit.CompactProducerSound
import IRComparison.Circuit.CompactReceiverSound

namespace IRComparison.Circuit

def trimTriple (limit : Nat) (p : State × List Int × List Int) := (trimState limit p.1,p.2)

theorem iterationLoop_trim (load : WindowLoader) (body : WindowBody)
    (compatible : ∀ j s q vs, (body j s q vs).map (trimResult limit) = body j (trimState limit s) q vs)
    (n k : Nat) (values : List Int) (s : State) (qi qo : List Int) :
    (iterationLoop load body n k values s qi qo).map (trimTriple limit) =
      iterationLoop load body n k values (trimState limit s) qi qo := by
  induction n generalizing k values s qi qo with
  | zero => rfl
  | succ n ih =>
    rw [iterationLoop,iterationLoop,← compatible]
    cases body k s qo values with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simp only [Option.map_some,bind,Option.bind,trimResult]
      cases n with
      | zero => rfl
      | succ m =>
        cases load (k+1) values qi with
        | none => rfl
        | some pair => obtain ⟨next,rest⟩ := pair; exact ih (k+1) next t rest out

theorem iterationEval_trim (load : WindowLoader) (body : WindowBody)
    (compatible : ∀ j s q vs, (body j s q vs).map (trimResult limit) = body j (trimState limit s) q vs)
    (n : Nat) (s : State) (qi qo : List Int) :
    (iterationEval load body n s qi qo).map (trimTriple limit) =
      iterationEval load body n (trimState limit s) qi qo := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [iterationEval]
    cases load 0 [] qi with
    | none => rfl
    | some pair => obtain ⟨next,rest⟩ := pair; exact iterationLoop_trim load body compatible (n+1) 0 next s rest qo

theorem producer_trim (code : HybridSymbolicProducerLoop.Code)
    (safe : ∀ a ∈ allCommandArrays code.body, a < limit) :
    (code.eval input x y s).map (trimResult limit) = code.eval input x y (trimState limit s) := by
  have h := iterationEval_trim
    (frozenLoader input code.start code.stride (code.initial.map fromMemoryLoad) (code.refill.map fromMemoryLoad))
    (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs)
    (fun _ _ _ _ => command_trim code.body safe) code.count s [] []
  rw [producer_eval_iteration,producer_eval_iteration] at h
  have projected := congrArg (Option.map (fun result : State × List Int × List Int => (result.1,result.2.2))) h
  simpa [Option.map_map,Function.comp_def,trimTriple,trimResult] using projected

theorem duplex_full_trim (code : HybridCompactDuplex.Code)
    (safe : ∀ a ∈ allCommandArrays code.body, a < limit) :
    (HybridCompactDuplexControl.evalFull code x y s qi).map (trimTriple limit) =
      HybridCompactDuplexControl.evalFull code x y (trimState limit s) qi := by
  have h := iterationEval_trim (fifoLoader code.start code.stride code.initial code.refill)
    (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs)
    (fun _ _ _ _ => command_trim code.body safe) code.count s qi []
  simpa only [duplex_eval_iteration] using h

theorem duplex_trim (code : HybridCompactDuplex.Code)
    (safe : ∀ a ∈ allCommandArrays code.body, a < limit) :
    (code.eval x y s qi).map (trimResult limit) = code.eval x y (trimState limit s) qi := by
  have h := duplex_full_trim (x:=x) (y:=y) (s:=s) (qi:=qi) code safe
  have projected := congrArg (Option.map (fun result : State × List Int × List Int => (result.1,result.2.2))) h
  rw [← HybridCompactDuplexControl.evalFull_correct,← HybridCompactDuplexControl.evalFull_correct]
  simpa [Option.map_map,Function.comp_def,trimTriple,trimResult] using projected

theorem receiver_trim (code : HybridCompactFIFO.Code)
    (safe : ∀ a ∈ allCommandArrays code.body.target, a < limit) :
    (code.eval x y s qi).map (trimResult limit) = code.eval x y (trimState limit s) qi := by
  have h := duplex_full_trim (x:=x) (y:=y) (s:=s) (qi:=qi) (receiverDuplex code) safe
  rw [receiver_eval_duplex,receiver_eval_duplex] at h
  have projected := congrArg (Option.map (fun result : State × List Int × List Int => (result.1,result.2.1))) h
  simpa [Option.map_map,Function.comp_def,trimTriple,trimResult] using projected

theorem trim_erase : trimState limit (StreamConsumer.erase a s) = StreamConsumer.erase a (trimState limit s) := by
  unfold trimState StreamConsumer.erase
  congr 1
  funext k
  by_cases hk : k = a <;> simp [hk]

theorem tail_trim (code : HybridCompactChainControl.Code)
    (safe : ∀ a ∈ tailArrays code, a < limit) :
    (code.eval x y s qi).map (trimState limit) = code.eval x y (trimState limit s) qi := by
  induction code generalizing s qi with
  | finish receiver =>
    have h := receiver_trim (x:=x) (y:=y) (s:=s) (qi:=qi) receiver safe
    have projected := congrArg (Option.map Prod.fst) h
    simpa [HybridCompactChainControl.Code.eval,Option.map_map,Function.comp_def,trimResult] using projected
  | stage a sender rest ih =>
    have senderSafe : ∀ n ∈ allCommandArrays sender.body, n < limit := fun n hn => safe n (by simp [tailArrays,hn])
    have restSafe : ∀ n ∈ tailArrays rest, n < limit := fun n hn => safe n (by simp [tailArrays,hn])
    simp only [HybridCompactChainControl.Code.eval,← trim_erase,← duplex_trim sender senderSafe]
    cases sender.eval x y (StreamConsumer.erase a s) qi with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simpa only [Option.map_some,bind,Option.bind,trimResult,← trim_erase] using ih (s:=StreamConsumer.erase a t) restSafe

end IRComparison.Circuit
