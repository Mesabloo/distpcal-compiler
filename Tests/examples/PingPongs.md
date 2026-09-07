# Running PingPongs

`PingPongs.tla` is one `Ping` process and a set of `Pong` processes that bounce
`"Ping"` / `"Pong"` messages off each other. `Ping` receives on a shared mailbox
`ping` and replies on a per-`Pong` mailbox `pong[from]`; each `Pong` sends to
`ping` and receives on its own `pong[self]`.

The compiler emits the process bodies and the shape of the network they run
over. It does not emit a `main`, a transport, or a deployment: turning the
output into running processes is integration work, sketched below.

## Compile to Go

```bash
fugue compile -t go -X go-pkg:pingpong -o pingpong/pingpong.go Tests/examples/PingPongs.tla
```

`-X go-pkg:pingpong` puts the output in an importable package rather than
`package main`, so a hand-written `main` can call into it.

## What the output gives you

```go
type Net_Network struct {
	Ping comm.Sender[struct{ From comm.Address; Mes tlaplus.Str }]
	Pong map[comm.Address]comm.Sender[tlaplus.Str]
}

func Proc_Ping(net Net_Network,
	mailbox comm.Receiver[struct{ From comm.Address; Mes tlaplus.Str }],
	self comm.Address) chan struct{}

func Proc_Pong(net Net_Network,
	mailbox comm.Receiver[tlaplus.Str],
	self comm.Address) chan struct{}
```

`Net_Network` mirrors the channels in the spec: `Ping` is the endpoint the
`ping` mailbox is reached through, `Pong` maps a `Pong`'s address to the
endpoint its `pong[self]` mailbox is reached through. Each `Proc_*` takes the
receiving end of its own mailbox and its own identity, spawns the process's
goroutines, and returns a channel that fires once the process finishes (never,
for Ping-Pong).

A process only needs the parts of `Net_Network` its body actually uses:

| process | needs | leaves nil |
|---|---|---|
| `Ping` | `Pong[a]` for every `Pong` address `a` (it replies to whoever wrote to it) | `Ping` |
| `Pong` | `Ping` | `Pong` |

## A ready-made transport

`runtime/comm` ships only the `Sender` / `Receiver` / `Address` interfaces.
`runtime/comm/tcp` is one concrete implementation over TCP with a name server:

- `tcp.Name` — an `Address` that is just a logical name (`"Ping"`, `"Pong1"`).
- `tcp.Listen[T](bind)` — opens a mailbox, returns a `Receiver[T]` and the
  address it bound to.
- `tcp.Dial[T](addr)` — a `Sender[T]` that connects on first use and reconnects.
- `tcp.ServeNameServer(bind)` — runs the registry.
- `tcp.Register(ns, name, addr)` / `tcp.Lookup(ns, name)` — publish and resolve a
  name; `Lookup` blocks until the name is registered, so processes may start in
  any order.

## Wiring a process

`Ping`, resolving every `Pong` name given on its command line:

```go
self := tcp.Name("Ping")
mailbox, addr, _ := tcp.Listen[pingMsg]("127.0.0.1:0")
tcp.Register(nameserver, string(self), addr)

pong := map[comm.Address]comm.Sender[tlaplus.Str]{}
for _, name := range pongNames {
	peer, _ := tcp.Lookup(nameserver, name)
	pong[tcp.Name(name)] = tcp.Dial[tlaplus.Str](peer)
}
<-pingpong.Proc_Ping(pingpong.Net_Network{Pong: pong}, mailbox, self)
```

`Pong`, resolving only `"Ping"`:

```go
self := tcp.Name(os.Args[2])
mailbox, addr, _ := tcp.Listen[tlaplus.Str]("127.0.0.1:0")
tcp.Register(nameserver, string(self), addr)

peer, _ := tcp.Lookup(nameserver, "Ping")
net := pingpong.Net_Network{Ping: tcp.Dial[pingMsg](peer)}
<-pingpong.Proc_Pong(net, mailbox, self)
```

where `pingMsg = struct{ From comm.Address; Mes tlaplus.Str }`, matching the
generated code field for field (Go structs are structurally typed, so a local
alias is enough).

## Running

Start the name server, then the processes in any order:

```bash
nameserver 127.0.0.1:9000
ping       127.0.0.1:9000 Pong1 Pong2
pong       127.0.0.1:9000 Pong1
pong       127.0.0.1:9000 Pong2
```

`PingPongs.tla` has no `print`, so a run is silent unless the integrator adds
observation — for example by wrapping each `Sender` / `Receiver` in a decorator
that logs before delegating.
