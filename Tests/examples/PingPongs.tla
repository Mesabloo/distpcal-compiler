---- MODULE PingPongs ----
CONSTANTS
    (* @type: Address; *)
    Ping,
    (* @type: Set(Address); *)
         Pongs

(*--algorithm PingPong {
    fifos (* @type: Channel({from: Address, mes: Str}); *) ping, 
          (* @type: Address -> Channel(Str); *) pong[Pongs];

    (* @mailbox: ping; *) 
    process (Ping = Ping) 
      variable 
        (* @type: {from: Address, mes: Str}; *) 
        tmp1 = [ from |-> self, mes |-> ""];
    {
    rcvPi: receive(ping, tmp1);
           await tmp1.mes = "Ping";
           goto sndPo;
    sndPo: send(pong[tmp1.from], "Pong");
           goto rcvPi;
    }

    (* @mailbox: pong[self]; *) 
    process (Pong \in Pongs) 
      variable
        (* @type: Str; *) 
        tmp2 = "";
    {
    sndPi: send(ping, [from |-> self, mes |-> "Ping"]);
           goto rcvPo;
    rcvPo: receive(pong[self], tmp2);
           await tmp2 = "Pong";
           goto sndPi;
    }   
}*)
====