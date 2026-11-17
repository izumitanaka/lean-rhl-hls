import IRComparison.Frontend.WordOrdinarySourceInterpretation
import IRComparison.Frontend.WordOrdinarySourceFlow
import IRComparison.Examples.RetainedArgumentExamples
import IRComparison.Examples.FrontendSourceMatching

/-! Checks of the new independent source judgment against ordinary Lean
elaboration, with the general generation theorem applied to the resulting
original-source conditions. Examples supplement, rather than replace, the
mutual induction over all source constructors. -/
namespace IRComparison.OrdinarySourceExamples
open Lean FrontendSourceMatching WordFrontend WordFrontend.OrdinarySource WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference
set_option maxHeartbeats 2400000

def updateSignature : Signature := ⟨[.scalar .word,.state],.body⟩

def helperBody (binder : Name) (flag : Bool) : Lean.Expr :=
  StateLet.source binder
    (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7])
    (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 1,.bvar 2])) flag

/-- The source child is written once, with its original State and value
binders. No retained command, CastTyping or transformed-body family occurs. -/
theorem helperSource (Γ : Context) (binder : Name) (flag : Bool) :
    Body #[] (.value .state::.value (.scalar .word)::Γ) .body (helperBody binder flag) := by
  apply Body.letState .body
    (.set (.variable rfl) 0 .elaborated (.literal .word 7))
  exact .returns .some (.set (.variable rfl) 1 .elaborated (.variable rfl))

/-- The updated State is the only State used by the continuation; the saved
scalar remains a normal value reference. -/
theorem helperFlow (Γ : Context) (effects : EffectScope) (binder : Name) (flag : Bool) :
    Body.Flow #[] (helperSource Γ binder flag) (parameterEffects 2 effects) [0] := by
  have flow := Body.Flow.letState (ds := #[]) (effects := parameterEffects 2 effects) .body
    (StateValue.set (Γ := .value .state::.value (.scalar .word)::Γ) (.variable (index := 0) rfl) 0 .elaborated (.literal .word 7))
    (Body.returns .some (StateValue.set (.variable (index := 0) rfl) 1 .elaborated (.variable (index := 2) rfl)))
    binder flag (Body.Flow.returns .some (StateValue.set (.variable (index := 0) rfl) 1 .elaborated (.variable (index := 2) rfl)))
    (by intro i member; simpa [stateVariables,freeVariables,app,NatNotation.native,AnnotatedLiteral.native,
      WordBinder.Annotation.native] using member)
  exact flow

def helper (valueName memoryName binder : Name) (valueInfo memoryInfo : BinderInfo) (flag : Bool) : Lean.Expr :=
  .lam valueName word (.lam memoryName state (helperBody binder flag) memoryInfo) valueInfo

theorem helperFunction (Γ : Context) (valueName memoryName binder : Name)
    (valueInfo memoryInfo : BinderInfo) (flag : Bool) :
    OrdinarySource.Function #[] Γ (helper valueName memoryName binder valueInfo memoryInfo flag) updateSignature := by
  apply OrdinarySource.Function.lambda (.scalar .word) [.state] .body
    (.next (.last (by intros; simp [helperBody,StateLet.source])))
  exact helperSource Γ binder flag

theorem helperFunctionFlow (Γ : Context) (effects : EffectScope) (valueName memoryName binder : Name)
    (valueInfo memoryInfo : BinderInfo) (flag : Bool) :
    Function.Flow #[] (helperFunction Γ valueName memoryName binder valueInfo memoryInfo flag) effects [] := by
  exact .lambda (.scalar .word) [.state] .body
    (.next (.last (by intros; simp [helperBody,StateLet.source])))
    (helperSource Γ binder flag) (helperFlow Γ effects binder flag)

def callBody : Lean.Expr :=
  Lean.mkApp2 (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 0]) (.bvar 1)

theorem callSource : Body #[] [.function updateSignature,.value .state] .body callBody := by
  apply Body.call (head := .scalar .word) (tail := [.state])
    (first := app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 0]) (rest := [.bvar 1]) (.variable (index := 0) rfl)
  exact .cons (.scalar (.register (.variable rfl) 0 .elaborated)) (.cons (.state (.variable rfl)) .nil)

theorem callFlow : Body.Flow #[] callSource [some [],none] [1,1] := by
  exact Body.Flow.call (effects := [some [],none])
    (OrdinarySource.Function.variable (Γ := [.function updateSignature,.value .state]) (index := 0) rfl)
    (.cons (.scalar (.register (.variable (index := 1) rfl) 0 .elaborated))
      (.cons (.state (.variable (index := 1) rfl)) .nil))
    (.variable (Γ := [.function updateSignature,.value .state])
      (effects := [some [],none]) (requires := []) rfl rfl)

/-- All parameter annotations, including mixed Word/BV32 prefixes, use the
same original helper-body derivation and the general retagging theorem. -/
example (binder : Name) (flag : Bool) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) :
    ∃ core, Represents (helperBody binder flag) core ∧ ∀ n,
      CastTyping env 0 (Arithmetic.SourceCasts env)
        ((([Parameter.scalar .bitvec,.state].take n ++ [Parameter.scalar .word,.state].drop n).map Parameter.core).reverse)
        core (optionType stateType) := by
  simpa only [Context.core,List.map_nil,List.append_nil] using
    (helperSource [] binder flag).typingPrefixes
      (declared := [.scalar .word,.state]) (actual := [.scalar .bitvec,.state])
      (.cons (.scalar .word .bitvec) (.cons .state .nil)) library closed

run_cmd do
  let env ← getEnv
  let some input := NativeEnvironment.input env ``RetainedArgumentExamples.updateArgument
    | throwError "ordinary source: missing native input"
  let .letE name ty value next flag := input.header.body | throwError "ordinary source: expected function let"
  let .lam valueName _ (.lam memoryName _ (.letE binder _ _ _ bodyFlag) memoryInfo) valueInfo := value
    | throwError "ordinary source: expected original helper binders"
  let .forallE typeName _ (.forallE typeMemory _ _ typeMemoryInfo) typeInfo := ty
    | throwError "ordinary source: expected original helper type"
  let expectedType : Lean.Expr := .forallE typeName word (.forallE typeMemory state (.app (.const ``Option [.zero]) state) typeMemoryInfo) typeInfo
  let expected : Lean.Expr := .letE name expectedType (helper valueName memoryName binder valueInfo memoryInfo bodyFlag) callBody flag
  let some same := sameClosedHeader expected input.header.body
    | throwError "ordinary source: original source shape differs"
  have original : Body #[] [.value .state] .body expected :=
    .letFunction (.arrow (.scalar .word) (.arrow .state (.result .body) typeMemory typeMemoryInfo) typeName typeInfo)
      (helperFunction [.value .state] valueName memoryName binder valueInfo memoryInfo bodyFlag) callSource name flag
  have current : original.Current := by
    refine ⟨[0,0],?_,?_⟩
    · exact Body.Flow.letFunction
        (.arrow (.scalar .word) (.arrow .state (.result .body) typeMemory typeMemoryInfo) typeName typeInfo)
        (helperFunction [.value .state] valueName memoryName binder valueInfo memoryInfo bodyFlag)
        callSource name flag
        (helperFunctionFlow [.value .state] [none] valueName memoryName binder valueInfo memoryInfo bodyFlag)
        callFlow
    · intro i member; simpa using member
  have source : Body #[] [.value .state] .body input.header.body := same.down.symm ▸ original
  let _ := source.typing StandardLibrary.library StandardLibrary.closed
  let _ := source.wellScoped
  have actualCurrent : source.Current := current.cast same.down.symm
  have view : Nonempty (NatNotation.View (NatNotation.elaborated.native 0)) := ⟨⟨0,.elaborated,rfl⟩⟩
  have staticExpected : LexicalScalarSyntax.StaticRegisters expected := by
    simp [expected,helper,helperBody,callBody,StateLet.source,Return.Form.source,Return.Form.nativeHeader,word,Arithmetic.nativeWidth,NatNotation.native,
      app,AnnotatedLiteral.native,WordBinder.Annotation.native,LexicalScalarSyntax.StaticRegisters,state]
    exact view
  have static : LexicalScalarSyntax.StaticRegisters input.header.body := same.down.symm ▸ staticExpected
  let _ := OrdinarySource.generates input source actualCurrent static (by decide) [] (by decide) 0 .rolled
  logInfo "ordinary source: updateArgument → original syntax/static conditions → compileRetained → Entry → RTL generation theorem"


/-- State let followed by an annotated monadic array read: actual do syntax,
not a manually supplied internal Syntax or a successful parser premise. -/
def readAfterUpdate (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let s := s.set 0 7
  let v : BitVec 32 ← (s.arrays 0)[0]?
  pure (s.set 1 v)

private def readDeclarations : FixedMemory.Declarations := #[(0,4)]

private def readOriginal (sn vn : Name) (flag : Bool) (info : BinderInfo) : Lean.Expr :=
  StateLet.source sn
    (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7])
    (readBind .body .bitvec
      (FixedReadSourceCompleteness.naturalSource .bitvec (.bvar 0)
        (NatNotation.elaborated.native 0) (NatNotation.elaborated.native 0))
      (.lam vn WordBinder.Annotation.bitvec.native
        (Return.Form.pure.source (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 1,.bvar 0])) info)) flag

private theorem readOriginalSource (sn vn : Name) (flag : Bool) (info : BinderInfo) :
    Body readDeclarations [.value .state] .body (readOriginal sn vn flag info) := by
  apply Body.letState .body (.set (.variable rfl) 0 .elaborated (.literal .word 7))
  apply Body.bindRead .body .bitvec (.natural .bitvec (.variable rfl) 0 0 .elaborated .elaborated (by decide))
  exact .returns .pure (.set (.variable rfl) 1 .elaborated (.variable rfl))

private theorem readOriginalCurrent (sn vn : Name) (flag : Bool) (info : BinderInfo) :
    (readOriginalSource sn vn flag info).Current := by
  let value := StateValue.set (Γ := [.value .state]) (.variable (index := 0) rfl)
    0 .elaborated (.literal .word 7)
  let read := Read.natural (ds := readDeclarations) (Γ := [.value .state,.value .state])
    .bitvec (.variable (index := 0) rfl) 0 0 .elaborated .elaborated (by decide)
  let next := Body.returns (ds := readDeclarations) .pure
    (StateValue.set (Γ := [.value (.scalar .bitvec),.value .state,.value .state])
      (.variable (index := 1) rfl) 1 .elaborated (.variable (index := 0) rfl))
  have nextFlow := Body.Flow.bindRead (effects := bindEffects [none]) .body .bitvec read next vn info
    (Body.Flow.returns .pure (StateValue.set (Γ := [.value (.scalar .bitvec),.value .state,.value .state])
      (.variable (index := 1) rfl) 1 .elaborated (.variable (index := 0) rfl)))
  have latest : currentOnly 0 (stateVariables [.value .state,.value .state]
      (FixedReadSourceCompleteness.naturalSource .bitvec (.bvar 0)
        (NatNotation.elaborated.native 0) (NatNotation.elaborated.native 0)) ++
      outsideValue (stateVariables [.value (.scalar .bitvec),.value .state,.value .state]
        (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 1,.bvar 0]))) := by
    simp [currentOnly,stateVariables,freeVariables,outsideValue,
      FixedReadSourceCompleteness.naturalSource,Read.bitsSource,Read.nativeBitsHeader,
      Read.nativeArray,Read.nativeValidity,app,NatNotation.native,word,WordBinder.Annotation.native,Arithmetic.nativeWidth]
  have flow := Body.Flow.letState (effects := [none]) .body value
    (Body.bindRead .body .bitvec read next vn info) sn flag nextFlow latest
  refine ⟨_,flow,?_⟩
  simp [currentOnly,stateVariables,freeVariables,app,NatNotation.native,
    AnnotatedLiteral.native,WordBinder.Annotation.native,word,Arithmetic.nativeWidth]

run_cmd do
  let env ← getEnv
  let some input := NativeEnvironment.input env ``readAfterUpdate
    | throwError "ordinary source: read input preparation"
  let .letE sn _ _ (.app _ (.lam vn _ _ info)) flag := input.header.body
    | throwError "ordinary source: read do binders"
  let some same := sameClosedHeader (readOriginal sn vn flag info) input.header.body
    | throwError "ordinary source: read original shape"
  have source : Body readDeclarations [.value .state] .body input.header.body :=
    same.down.symm ▸ readOriginalSource sn vn flag info
  have current : source.Current := (readOriginalCurrent sn vn flag info).cast same.down.symm
  have staticOriginal : LexicalScalarSyntax.StaticRegisters (readOriginal sn vn flag info) := by
    simp [readOriginal,StateLet.source,readBind,FixedReadSourceCompleteness.naturalSource,
      Read.bitsSource,Read.nativeBitsHeader,Read.nativeArray,Read.nativeValidity,Result.native,Return.nativePureInstance,Return.Form.source,Return.Form.nativeHeader,
      bindHead,app,AnnotatedLiteral.native,WordBinder.Annotation.native,word,state,
      Arithmetic.nativeWidth,NatNotation.native,LexicalScalarSyntax.StaticRegisters]
  have static : LexicalScalarSyntax.StaticRegisters input.header.body := same.down.symm ▸ staticOriginal
  let _ := OrdinarySource.generates input source current static (by decide) [0] (by decide) 0 .rolled
  logInfo "ordinary source: State let + BitVec do read → compileRetained → Entry → RTL generation theorem"

end IRComparison.OrdinarySourceExamples
