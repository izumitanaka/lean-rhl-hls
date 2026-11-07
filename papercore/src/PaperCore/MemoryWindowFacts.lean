import PaperCore.MemoryWindowPlan
import PaperCore.MemoryBufferSimulation

namespace PaperCore.MemoryWindowPlan
open AccessAnalysis OrientedWindow SourcePass MemoryWindowSchedule
variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def Candidate.ordinary (p : Candidate classify source) : Var → Prop := fun x => x ∈ p.variables
def Candidate.layout (p : Candidate classify source) : Layout := ⟨p.input,p.first,p.scale,p.reverse,p.buffers⟩
def Candidate.base (p : Candidate classify source) (k : Int) : Int := p.scale*k+p.first

theorem Candidate.initial_length (p : Candidate classify source) : p.initialBuffers.length = p.overlap := by
  simp [Candidate.initialBuffers,WindowNames.names]
theorem Candidate.refill_length (p : Candidate classify source) : p.refill.length = p.reload := by
  simp [Candidate.refill,WindowNames.refillNames]
theorem Candidate.distinct (p : Candidate classify source) : p.buffers.Nodup := WindowNames.all_distinct

theorem Candidate.buffers_fresh (p : Candidate classify source) : ∀ b ∈ p.buffers, ¬p.ordinary b :=
  WindowNames.all_fresh

theorem Candidate.cursor_fresh (p : Candidate classify source) : ¬p.ordinary p.cursor := BufferNames.fresh
theorem Candidate.increment_fresh (p : Candidate classify source) : ¬p.ordinary p.increment := BufferNames.fresh

theorem Candidate.cursor_not_buffer (p : Candidate classify source) : p.cursor ∉ p.buffers := by
  intro member
  change p.cursor ∈ WindowNames.names p.variables p.overlap ++ WindowNames.refillNames p.variables p.overlap p.reload at member
  rw [← WindowNames.split_names] at member
  obtain ⟨i,hi,same⟩ := List.mem_map.mp member
  have eq := BufferNames.injective same
  have lt := List.mem_range.mp hi
  change i = p.overlap+p.reload at eq
  omega

theorem Candidate.increment_not_buffer (p : Candidate classify source) : p.increment ∉ p.buffers := by
  intro member
  change p.increment ∈ WindowNames.names p.variables p.overlap ++ WindowNames.refillNames p.variables p.overlap p.reload at member
  rw [← WindowNames.split_names] at member
  obtain ⟨i,hi,same⟩ := List.mem_map.mp member
  have eq := BufferNames.injective same
  have lt := List.mem_range.mp hi
  change i = p.overlap+p.reload+1 at eq
  omega

theorem Candidate.cursor_ne_increment (p : Candidate classify source) : p.cursor ≠ p.increment := by
  intro same
  have eq := BufferNames.injective same
  change p.overlap+p.reload = p.overlap+p.reload+1 at eq
  omega

theorem Candidate.typed (p : Candidate classify source) : BufferView.Typed p.ordinary p.body :=
  BufferNames.source_typed p.body p.bodyVars

theorem Candidate.next_base (p : Candidate classify source) (k : Int) :
    p.base (k+p.counterDelta) = p.base k+(p.reload:Int)*direction p.reverse := by
  simp only [Candidate.base,Int.mul_add,p.movement]
  omega

theorem Candidate.counter_after (p : Candidate classify source)
    (env : p.substitution.after.Matches regs k) : regs.lookup p.counter = some (k+p.counterDelta-p.step) := by
  simpa [Affine.eval,Int.add_sub_assoc] using env p.counter _ p.counterKnown

def Candidate.readPrefix (p : Candidate classify source) : List (Source Op) :=
  address p.add p.mul p.counter p.cursor p.increment p.scale
      (p.first+(p.overlap:Int)*direction p.reverse) (direction p.reverse) ++
  loads p.add p.input p.cursor p.increment p.refill

theorem Candidate.readPrefix_flat (p : Candidate classify source) : ∀ c ∈ p.readPrefix, Flat c := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact address_flat c h
  · exact loads_flat c h

/-- Prepare a full window, preserving all original variables and memory. -/
theorem Candidate.readPrefix_exists (p : Candidate classify source) (ops : ArithmeticSound classify meaning)
    (value : initial.regs.lookup p.counter = some k)
    (held : Held (direction p.reverse) initial.memory initial.regs p.input (p.base k) p.initialBuffers)
    (coverage : MemoryCoverage.Covers initial.memory p.input
      (p.base k+(p.overlap:Int)*direction p.reverse) (direction p.reverse) p.reload) :
    ∃ final, Runs meaning p.readPrefix initial final ∧ Agrees p.ordinary initial final ∧
      Held (direction p.reverse) final.memory final.regs p.input (p.base k) p.buffers := by
  have counterCursor : p.counter ≠ p.cursor := fun same => p.cursor_fresh (same ▸ p.counterMember)
  obtain ⟨middle,addressRun,cv,iv,mem⟩ := address_exists (ops _ _ p.addClass) (ops _ _ p.mulClass)
    value counterCursor p.cursor_ne_increment
    (scale := p.scale) (offset := p.first+(p.overlap:Int)*direction p.reverse) (stride := direction p.reverse)
  have heldMiddle : Held (direction p.reverse) middle.memory middle.regs p.input (p.base k) p.initialBuffers := by
    rw [mem]
    apply held.congr_regs
    intro b hb
    have full := List.mem_append_left p.refill hb
    exact (address_frame addressRun
      (fun same => p.cursor_not_buffer (same ▸ full))
      (fun same => p.increment_not_buffer (same ▸ full))).1
  have cv' : middle.regs.lookup p.cursor = some (p.base k+(p.initialBuffers.length:Int)*direction p.reverse) := by
    simpa [Candidate.base,p.initial_length,Int.add_assoc] using cv
  have coverage' : MemoryCoverage.Covers middle.memory p.input
      (p.base k+(p.initialBuffers.length:Int)*direction p.reverse) (direction p.reverse) p.refill.length := by
    simpa [mem,p.initial_length,p.refill_length] using coverage
  obtain ⟨final,loadRun,fullHeld⟩ := refill_exists p.initialBuffers p.refill (ops _ _ p.addClass) cv' iv
    p.cursor_ne_increment p.cursor_not_buffer p.increment_not_buffer p.distinct heldMiddle coverage'
  have finalMemory := (loads_memory loadRun).trans mem
  refine ⟨final,addressRun.append loadRun,⟨?_,finalMemory.symm⟩,?_⟩
  · intro x hx
    rw [loads_frame loadRun
      (fun member => p.buffers_fresh x (List.mem_append_right _ member) hx)
      (fun same => p.cursor_fresh (same ▸ hx))]
    exact ((address_frame addressRun
      (fun same => p.cursor_fresh (same ▸ hx))
      (fun same => p.increment_fresh (same ▸ hx))).1).symm
  · simpa only [loads_memory loadRun] using fullHeld

#print axioms Candidate.readPrefix_exists
end PaperCore.MemoryWindowPlan
