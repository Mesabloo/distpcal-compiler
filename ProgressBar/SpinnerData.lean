/-- A spinner is a set of frames together with an update interval. -/
@[unbox]
structure SpinnerData : Type where
  /-- The frames of the spinner (which ideally are all of the same size). -/
  frames : Array String
  /-- The update interval, in milliseconds. -/
  interval : UInt32

  /--
    All frames take the same amount of space.
    This is a requirement because we don't want the prompt to move in the middle of
    some animation.
  -/
  all_frames_same_length : ∀ f₁ ∈ frames, ∀ f₂ ∈ frames, f₁.length = f₂.length := by decide
