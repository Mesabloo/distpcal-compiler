package comm

import (
	"testing"
	"time"
)

// goChan is a Sender/Receiver backed by a Go channel: the medium used when both
// endpoints live in one compiled process.
//
// It exists here to pin the interfaces' contract with something executable —
// particularly what Recv reports once the medium is gone — rather than to be
// the shipped implementation. Cross-process media are a separate question.
type goChan[T any] chan T

func (c goChan[T]) Send(value T) { c <- value }

func (c goChan[T]) Recv() (T, bool) {
	v, ok := <-c
	return v, ok
}

// Compile-time evidence that a Go channel satisfies both endpoints.
var (
	_ Sender[int]   = goChan[int](nil)
	_ Receiver[int] = goChan[int](nil)
)

func TestSendThenReceive(t *testing.T) {
	c := make(goChan[int], 1)

	c.Send(42)
	got, ok := c.Recv()
	if !ok {
		t.Fatalf("Recv reported the medium gone on a live channel")
	}
	if got != 42 {
		t.Errorf("Recv = %d, want 42", got)
	}
}

// TestRecvReportsVanishedMedium pins the part of the contract a receive loop
// depends on: once the medium is gone, Recv must report it rather than block,
// and must keep reporting it.
func TestRecvReportsVanishedMedium(t *testing.T) {
	c := make(goChan[int], 1)
	c.Send(7)
	close(c)

	// Values buffered before the close are still delivered.
	if got, ok := c.Recv(); !ok || got != 7 {
		t.Errorf("Recv = (%d, %v), want (7, true): buffered values are lost on close", got, ok)
	}

	for range 3 {
		if got, ok := c.Recv(); ok || got != 0 {
			t.Fatalf("Recv = (%d, %v) after close, want (0, false)", got, ok)
		}
	}
}

// TestRecvBlocksUntilSent is the other half: with the medium alive but empty,
// Recv waits rather than reporting it gone.
func TestRecvBlocksUntilSent(t *testing.T) {
	c := make(goChan[int])

	received := make(chan int, 1)
	go func() {
		v, ok := c.Recv()
		if !ok {
			t.Errorf("Recv reported the medium gone while it was alive")
		}
		received <- v
	}()

	select {
	case <-received:
		t.Fatalf("Recv returned before anything was sent")
	case <-time.After(50 * time.Millisecond):
	}

	c.Send(3)

	select {
	case got := <-received:
		if got != 3 {
			t.Errorf("Recv = %d, want 3", got)
		}
	case <-time.After(time.Second):
		t.Errorf("Recv did not return after a value was sent")
	}
}
