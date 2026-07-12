module

public import ProgressBar.SpinnerData
public import Std.Sync.Channel


/-- What must be done when stopping the spinner? -/
public inductive CancelAction : Type
  /-- Replace the spinner animation with the symbol `sym`, optionally changing the message to
  `msg`. -/
  | persist (sym : String) (msg : Option String)
  /-- Completely erase the spinner. -/
  | erase
  /-- Print the given `msg` in place of the spinner. -/
  | replace (msg : String)

/-- Messages sent to the spinner's background task over its channel: `setTitle` replaces the
title shown next to the animation, or `log` prints a line above the animation without stopping
it (unlike `Spinner.cancel`'s `.persist`, which stops the spinner for good). -/
private inductive Spinner.Msg : Type
  | setTitle (title : String)
  | log (line : String)

public structure Spinner : Type where
  private mk ::
  /-- A way to transmit new messages to be shown next to the spinner. -/
  private chan : Std.CloseableChannel Spinner.Msg
  /-- The inner task in charge of updating the spinner. -/
  private task : Task (Except IO.Error Unit)
  /-- On which stream to output the spinner? (usually `stdout` or `stderr`) -/
  private stream : IO.FS.Stream
  /-- The task to be performed when cancelling the spinner. -/
  private cancelAction : IO.Ref CancelAction

public def Spinner.newInner (spinner : SpinnerData) (message : Option String) (stream : Option IO.FS.Stream) : IO Spinner := do
  let stream ← match stream with | some s => pure s | none => IO.getStdout
  let chan : Std.CloseableChannel Spinner.Msg ← BaseIO.toIO Std.CloseableChannel.new
  let cancelAction : IO.Ref CancelAction ← IO.mkRef .erase

  let msg ← IO.mkRef (message.getD "")
  let currentFrame ← IO.mkRef ""
  let rcvTask ← IO.asTask do
    for m in chan.sync do
      match m with
      | .setTitle title =>
        msg.set title
        -- Erase the whole line, since the new title may be a different length.
        stream.write s!"\x1b[2K\r{← currentFrame.get} {title}".toUTF8
        stream.flush
      | .log line =>
        -- Erase the animation line, print `line` as its own persisted line, then immediately
        -- redraw the current frame/title beneath it, so there's no gap before the next tick.
        stream.write s!"\x1b[2K\r{line}\n{← currentFrame.get} {← msg.get}".toUTF8
        stream.flush

  let task ← IO.asTask do
    let mut cont := true
    while cont do
      for frame in spinner.frames do
        currentFrame.set frame
        stream.write s!"\r{frame} {← msg.get}".toUTF8
        stream.flush

        if ← IO.checkCanceled then
          cont := false
          IO.cancel rcvTask
          match ← IO.wait rcvTask with
          | .ok _ => break
          | .error e => throw e

        IO.sleep spinner.interval

    match ← cancelAction.get with
    | .erase => stream.write "\x1b[2K\r".toUTF8
    | .replace msg => stream.write s!"\x1b[2K\r{msg}\n".toUTF8
    | .persist sym none => stream.write s!"\x1b[2K\r{sym} {← msg.get}\n".toUTF8
    | .persist sym (some msg) => stream.write s!"\x1b[2K\r{sym} {msg}\n".toUTF8
    stream.flush

  return {
    chan
    task
    stream
    cancelAction
  }

/-- Change the title of the spinner. -/
public protected def Spinner.setTitle (spinner : Spinner) (title : String) : IO Unit := BaseIO.toIO do
  let _ ← spinner.chan.send (.setTitle title)

/-- Print `line` as its own persisted line above the spinner, without stopping it (unlike
`Spinner.cancel .persist`, which ends the spinner for good). -/
public protected def Spinner.log (spinner : Spinner) (line : String) : IO Unit := BaseIO.toIO do
  let _ ← spinner.chan.send (.log line)

/-- Stops the spinner, erasing the spinner and its message. -/
public protected def Spinner.cancel (spinner : Spinner) (act : CancelAction := .erase) : IO Unit := do
  spinner.cancelAction.set act
  spinner.chan.close
  IO.cancel spinner.task

  match ← IO.wait spinner.task with
  | .ok _ => return
  | .error e => throw e

/-- Check if a call to `Spinner.cancel` has already been done or not. -/
public protected def Spinner.isCancelled (spinner : Spinner) : IO Bool := IO.hasFinished spinner.task

/-- Create a new spinner on `stdout` that will execute `endAction` when cancelled. -/
public protected abbrev Spinner.new (spinner : SpinnerData) (message : Option String) : IO Spinner :=
  Spinner.newInner spinner message none

/-- Create a new spinner on the provided `stream` that will execute `endAction` when cancelled. -/
public protected abbrev Spinner.newOnStream (spinner : SpinnerData) (message : Option String) (stream : IO.FS.Stream) : IO Spinner :=
  Spinner.newInner spinner message (some stream)
