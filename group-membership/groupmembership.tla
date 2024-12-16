-------------------------- MODULE groupmembership --------------------------

(***************************************************************************)
(* Model of group membership management in Delta Chat.                     *)
(***************************************************************************)

EXTENDS Naturals,
        Sequences

CONSTANT \* Symmetry set of devices such as `{d1, d2, d3}'.
         Devices,
         Creator, \* Device that created the chat.
         MaxQueue \* Bound on the queue size to keep the model bounded.

VARIABLES \* Map from device to the set of devices it thinks are members of the group .
          Members,
          \* FIFO queues of messages sent between devices.
          Queues

vars == <<Members, Queues>>

-----------------------------------------------------------------

AllDevices ==
  Devices \union {Creator}

(*
 * The set of all possible messages.
 *
 * Messages do not have explicit `From:` field
 * because messages for each sender are placed into its own queue.
 *)
Messages ==
  [members: SUBSET AllDevices \* New member list.
   ] (* TODO add timestamps *)

(* Bounded sequence type. *)
SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

(* Pairs of devices excluding pairs of devices with self. *)
DevicePairs == { <<x, y>> \in AllDevices \X AllDevices : x # y }

TypeOK ==
  /\ Members \in [AllDevices -> SUBSET AllDevices]
  /\ Queues \in [DevicePairs -> Seq(Messages)]

Init ==
  /\ Members = [d \in AllDevices |-> IF d = Creator THEN {d} ELSE {}] \* Only chat creator is a member of the chat.
  /\ Queues = [pair \in DevicePairs |-> <<>>] \* All queues are empty.

----------------------------------------------------------------------------

(* Device `d` sends chat message. *)
SendsChatMessage(d) ==
  /\ d \in Members[d]
  /\ UNCHANGED Members
  /\ LET
       NewMessage == [members |-> Members[d]]
     IN
       Queues' = [<<s, r>> \in DevicePairs |-> IF s = d /\ r \in Members[d]
                                               THEN Append(Queues[s, r], NewMessage)
                                               ELSE Queues[s, r]]

AddsMember(d) ==
  /\ d \in Members[d]
  /\ \E m \in AllDevices :
     /\ m \notin Members[d]
     /\ Members' = [Members EXCEPT ![d] = Members[d] \union {m}]
     /\ LET
          MemberAddedMessage == [members |-> Members[d] \union {m}]
        IN
          Queues' = [<<s, r>> \in DevicePairs |->
                     IF s = d /\ (r \in Members[d] \/ r = m)
                     THEN Append(Queues[s, r], MemberAddedMessage)
                     ELSE Queues[s, r]]

RemovesMember(d) ==
  /\ d \in Members[d]
  /\ \E m \in Members[d] : \* It is possible that m = d, then d leaves the group.
     /\ Members' = [Members EXCEPT ![d] = Members[d] \ {m}]
     /\ LET
          MemberRemovedMessage == [members |-> Members[d] \ {m}]
        IN
          Queues' = [<<s, r>> \in DevicePairs |->
                     IF s = d /\ (r \in Members[d]) \* Removed member gets the message as well.
                     THEN Append(Queues[s, r], MemberRemovedMessage)
                     ELSE Queues[s, r]]

(* Message reception logic, the main part of the protocol. *)
ReceivesMessage(r) ==
  \E s \in AllDevices \ {r} :
  /\ Queues[s, r] /= <<>>
  /\ Queues' = [Queues EXCEPT ![<<s, r>>] = Tail(Queues[s, r])]
  /\ LET ReceivedMessage == Head(Queues[s, r])
     IN Members' = [x \in AllDevices |-> IF x = r
                                         THEN ReceivedMessage.members
                                         ELSE Members[x]]

Actions(d) ==
  \/ SendsChatMessage(d)
  \/ AddsMember(d)
  \/ RemovesMember(d)
  \/ ReceivesMessage(d)

Next ==
  \/ \E d \in AllDevices : Actions(d)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* If both devices think they are in the chat,
 * they must have the same memberlist.
 *
 * We want to have this property eventually
 * if devices stop adding and removing members,
 * but it does not hold at all times.
 *)
GroupConsistency ==
  \A d1, d2 \in AllDevices :
  \/ d1 \notin Members[d1]
  \/ d2 \notin Members[d2]
  \/ Members[d1] = Members[d2]

(*
 * All devices which think they are members of the chat
 * keep chatting.
 *)
MembersKeepChatting ==
  \A d \in AllDevices :
  d \in Members[d] => <>(\E r \in (AllDevices \ {d}) : Len(Queues[d, r]) > 0)

(* Message queues have no membership changing messages. *)
NoMembershipChanges ==
  \A d \in AllDevices :
  ~AddsMember(d) /\ ~RemovesMember(d)

(* Eventually membership changes are never queued. *)
EventuallyNoMembershipChanges ==
  <>[][NoMembershipChanges]_vars

(*
 * If chat members keep chatting and eventually stop adding or removing members,
 * then eventually group is always conistent.
 *)
EventualConsistencyProperty ==
  (WF_Queues(Next) /\ MembersKeepChatting /\ EventuallyNoMembershipChanges) => <>[]GroupConsistency


=============================================================================
