package tcp

import (
	"net"
	"net/rpc"
	"sync"
)

// rpcName is the service name the name server registers under and clients call
// into. It is an implementation detail shared between ServeNameServer and the
// Register / Lookup helpers.
const rpcName = "NameServer"

// Registration is the argument of a NameServer.Register call: the logical name
// a process answers to and the "host:port" its Listen endpoint bound to.
//
// It is exported because net/rpc requires a call's argument type to be.
type Registration struct {
	Name string
	Addr string
}

// nameServer is the in-memory registry: a name-to-address map plus a condition
// variable so that a Lookup for a name nobody has registered yet parks instead
// of failing.
//
// Parking rather than failing is what lets the processes of one system start in
// any order — a process that looks up a peer before that peer has registered
// simply waits for it.
type nameServer struct {
	mu      sync.Mutex
	arrived *sync.Cond
	entries map[string]string
}

// Register records that name is reachable at the given address, replacing any
// previous entry, and wakes every parked Lookup so it can re-check.
func (ns *nameServer) Register(args Registration, _ *struct{}) error {
	ns.mu.Lock()
	defer ns.mu.Unlock()
	ns.entries[args.Name] = args.Addr
	ns.arrived.Broadcast()
	return nil
}

// Lookup returns the address registered under name, blocking until some process
// registers it.
func (ns *nameServer) Lookup(name string, addr *string) error {
	ns.mu.Lock()
	defer ns.mu.Unlock()
	for {
		if a, ok := ns.entries[name]; ok {
			*addr = a
			return nil
		}
		ns.arrived.Wait()
	}
}

// ServeNameServer runs a name server on bind ("host:port") and does not return
// until its listener fails.
//
// One name server process must be running and reachable before the processes
// that use it start, since they register and resolve names through it.
func ServeNameServer(bind string) error {
	ln, err := net.Listen("tcp", bind)
	if err != nil {
		return err
	}
	return serveNameServerOn(ln)
}

// serveNameServerOn is ServeNameServer once the listener exists, split out so a
// test can serve on a listener it bound to an arbitrary free port.
func serveNameServerOn(ln net.Listener) error {
	defer ln.Close()

	ns := &nameServer{entries: map[string]string{}}
	ns.arrived = sync.NewCond(&ns.mu)

	srv := rpc.NewServer()
	if err := srv.RegisterName(rpcName, ns); err != nil {
		return err
	}

	srv.Accept(ln)
	return nil
}

// Register tells the name server at nsAddr that name is reachable at addr. It
// opens a fresh connection for the one call.
func Register(nsAddr, name, addr string) error {
	client, err := rpc.Dial("tcp", nsAddr)
	if err != nil {
		return err
	}
	defer client.Close()
	return client.Call(rpcName+".Register", Registration{Name: name, Addr: addr}, &struct{}{})
}

// Lookup asks the name server at nsAddr for the address registered under name.
// The call does not return until that name has been registered, so a caller may
// resolve a peer that has not started yet.
func Lookup(nsAddr, name string) (string, error) {
	client, err := rpc.Dial("tcp", nsAddr)
	if err != nil {
		return "", err
	}
	defer client.Close()
	var addr string
	if err := client.Call(rpcName+".Lookup", name, &addr); err != nil {
		return "", err
	}
	return addr, nil
}
