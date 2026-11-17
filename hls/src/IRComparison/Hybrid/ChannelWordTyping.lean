import IRComparison.Hybrid.WordTyping
import IRComparison.Hybrid.ChannelCommandBridge

namespace IRComparison.HybridIR

/-- Word data and integer administrative bindings for named communication.
This is a proof judgment on the existing target, not an additional IR. -/
inductive WordChannel : WordBindings → ChannelCmd → Prop where
  | skip : WordChannel locals .skip
  | assign : WordRead locals (fun _ => False) e → WordChannel locals (.assign r e)
  | send : WordRead locals (fun _ => False) e → WordChannel locals (.send q e)
  | store : WordRead locals (fun _ => False) e → WordChannel locals (.store a j e)
  | hold : WordRead locals (fun _ => False) e → WordChannel locals (.hold b e)
  | receive : WordChannel locals (.receive q b)
  | letBuffer : WordChannel (pushWord True locals) c → WordChannel locals (.letBuffer b c)
  | letWord : WordRead locals (fun _ => False) e → WordChannel (pushWord True locals) c →
      WordChannel locals (.letValue e c)
  | letInteger : WordChannel (pushWord False locals) c → WordChannel locals (.letValue e c)
  | seq : WordChannel locals a → WordChannel locals b → WordChannel locals (.seq a b)
  | branch : WordChannel locals a → WordChannel locals b → WordChannel locals (.branch e a b)
  | repeat : WordChannel locals c → WordChannel locals (.repeat n c)
  | forWord : WordRead locals (fun _ => False) e → WordChannel (pushWord True locals) c →
      WordChannel locals (.forRange e c)
  | forInteger : WordChannel (pushWord False locals) c → WordChannel locals (.forRange e c)

def prependWords (count : Nat) (locals : WordBindings) : WordBindings :=
  fun n => if n < count then True else locals (n-count)

theorem prependWords_zero : prependWords 0 locals = locals := by funext n; simp [prependWords]

theorem prependWords_succ : prependWords (n+1) locals = pushWord True (prependWords n locals) := by
  funext k
  cases k <;> simp [prependWords,pushWord,Nat.succ_lt_succ_iff]

theorem WordChannel.capture (slots : List Nat)
    (typed : WordChannel (prependWords slots.length locals) c) :
    WordChannel locals (ChannelBuffers.capture slots c) := by
  induction slots generalizing c with
  | nil => simpa only [prependWords_zero] using typed
  | cons a slots ih =>
    apply ih
    apply WordChannel.letBuffer
    simpa only [List.length_cons,prependWords_succ] using typed

end IRComparison.HybridIR

namespace IRComparison.ChannelScope
open HybridIR

/-- Retain source bindings, leave inserted index/counter bindings untyped as
data, and give the missing-local sentinel its zero-range word type. -/
def wordBindings (width padding : Nat) (locals : WordBindings) : WordBindings :=
  fun n => if n < width then locals n else width+padding ≤ n

theorem wordBindings_push :
    wordBindings (width+1) padding (pushWord kind locals) =
      pushWord kind (wordBindings width padding locals) := by
  funext n
  cases n with
  | zero => simp [wordBindings,pushWord]
  | succ n => simp [wordBindings,pushWord,Nat.succ_lt_succ_iff,Nat.add_right_comm]

theorem value_word (typed : WordValue locals temps e) :
    WordValue (wordBindings width padding locals) temps (value width padding e) := by
  induction typed with
  | lit n lo hi => exact .lit n lo hi
  | left => exact .left
  | right => exact .right
  | «local» n h =>
    apply WordValue.local
    by_cases hn : n < width <;> simp [wordBindings,hn,h,show ¬ width+padding < width from by omega]
  | temp n h => exact .temp n h
  | wrap v => exact .wrap _
  | div _ _ a b => exact .div a b

theorem read_word (typed : WordRead locals temps e) :
    WordRead (wordBindings width padding locals) temps (read width padding e) := by
  induction typed with
  | pure h => exact .pure (value_word h)
  | register r => exact .register r
  | memory a j => exact .memory a _
  | bind _ _ a b => exact .bind a b
  | branch _ _ a b => exact .branch a b

end IRComparison.ChannelScope

namespace IRComparison.ChannelCommandBridge
open HybridIR

theorem command_word (typed : WordCommand locals c) :
    WordChannel (ChannelScope.wordBindings width padding locals) (command output width padding c) := by
  induction typed generalizing width with
  | skip => exact .skip
  | assign h => exact .assign (ChannelScope.read_word h)
  | send h => exact .send (ChannelScope.read_word h)
  | store h => exact .store (ChannelScope.read_word h)
  | letValue h _ ih =>
    exact .letWord (ChannelScope.read_word h)
      (by simpa only [ChannelScope.wordBindings_push] using ih (width:=width+1))
  | seq _ _ a b => exact .seq a b
  | branch _ _ a b => exact .branch a b
  | «repeat» _ ih => exact .repeat ih
  | forWord h _ ih =>
    exact .forWord (ChannelScope.read_word h)
      (by simpa only [ChannelScope.wordBindings_push] using ih (width:=width+1))
  | forInteger _ ih =>
    exact .forInteger
      (by simpa only [ChannelScope.wordBindings_push] using ih (width:=width+1))

end IRComparison.ChannelCommandBridge
