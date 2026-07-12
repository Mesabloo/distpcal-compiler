module

/-- A spinner is a set of frames together with an update interval. -/
@[unbox]
public structure SpinnerData : Type where
  /-- The frames of the spinner (which ideally are all of the same size). -/
  frames : Array String
  /-- The update interval, in milliseconds. -/
  interval : UInt32

  /-- All frames must take the same amount of space, so the prompt doesn't shift mid-animation. -/
  all_frames_same_length : ∀ f₁ ∈ frames, ∀ f₂ ∈ frames, f₁.length = f₂.length := by decide
