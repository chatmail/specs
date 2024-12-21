-------------------------- MODULE groupmembership --------------------------

(***************************************************************************)
(* Model of group membership management in Delta Chat.                     *)
(***************************************************************************)

EXTENDS Naturals,
        Sequences,
        TLC

CONSTANT Devices, \* Set of devices such as `{d1, d2, d3}'.
         Creator, \* Device that created the chat.
         MaxQueue,\* Bound on the queue size to keep the model bounded.
         MaxClock

Clock == 0 .. MaxClock

VARIABLES \* Map from device to the set of devices it thinks are members of the group .
          members,
          \* FIFO queues of messages sent between devices.
          queues,
          \* Global clock.
          clock

vars == <<members, queues, clock>>

-----------------------------------------------------------------

(*********)
(* Types *)
(*********)

AllDevices ==
  Devices \union {Creator}

(* Pairs of devices excluding pairs of devices with self. *)
DevicePairs == { <<x, y>> \in AllDevices \X AllDevices : x # y }

(* Member list is a function from a subset of devices
   to pairs of clock and a flag.
   If the flag is TRUE, the member is part of the group.
   If the flag is FALSE, it is a tombstone. *)
MemberList == UNION { [D -> [timestamp: Clock, flag: BOOLEAN]] : D \in SUBSET AllDevices }

TypeOK ==
  /\ members \in [AllDevices -> MemberList]
  /\ queues \in [DevicePairs -> Seq(MemberList)]
  /\ clock \in Clock

Init ==
  \* Only chat creator is a member of the chat.
  /\ members = [d \in AllDevices |->
                IF d = Creator THEN d :> [timestamp |-> 0, flag |-> TRUE] ELSE <<>>]
  /\ queues = [pair \in DevicePairs |-> <<>>] \* All queues are empty.
  /\ clock = 0

-----------------------------------------------------------------

(* Extracts members who are not tombstones from the member list. *)
MemberSet(l) ==
   {x \in DOMAIN l : l[x].flag }

(* True if device d thinks m is a chat member. *)
IsMember(d, m) ==
  /\ m \in DOMAIN members[d]
  /\ members[d][m].flag

EnabledDevices ==
  {d \in AllDevices : IsMember(d, d)}

----------------------------------------------------------------------------

SendMessage(sender, recipients) ==
  queues' = [<<s, r>> \in DevicePairs |->
             IF s = sender /\ r \in MemberSet(recipients)
             THEN Append(queues[s, r], members'[s])
             ELSE queues[s, r]]

(* Device `d' sends a chat message. *)
SendsChatMessage(d) ==
  /\ IsMember(d, d)
  /\ UNCHANGED <<members, clock>>
  /\ LET msg == members'[d]
     IN SendMessage(d, members[d])

(* Device `d' adds a member to the chat. *)
AddsMember(d) ==
  /\ IsMember(d, d)
  /\ \E m \in AllDevices :
     /\ ~IsMember(d, m)
     /\ clock' = clock + 1
     /\ members' = [members EXCEPT ![d] = (m :> [timestamp |-> clock', flag |-> TRUE]) @@ members[d]]
     (* Send "Member added" message to all chat members, including the new one. *)
     /\ LET msg == members'[d]
        IN SendMessage(d, members'[d])

RemovesMember(d) ==
  /\ IsMember(d, d)
  /\ \E m \in AllDevices :
     /\ IsMember(d, m) \* It is possible that m = d, then d leaves the group.
     /\ clock' = clock + 1
     /\ members' = [members EXCEPT ![d] = (m :> [timestamp |-> clock', flag |-> FALSE]) @@ members[d]]
     /\ LET msg == members'[d]
        IN SendMessage(d, members[d])

(* Message reception logic, the main part of the protocol. *)
ReceivesMessage(s, r) ==
  /\ queues[s, r] /= <<>>
  /\ queues' = [queues EXCEPT ![s, r] = Tail(@)]
  /\ UNCHANGED clock
  /\ LET msg == Head(queues[s, r])
     IN /\ members' = [members EXCEPT ![r] =
                       [x \in (DOMAIN @ \cup DOMAIN msg) |->
                        IF x \notin DOMAIN @
                        THEN msg[x]
                        ELSE IF x \in DOMAIN msg /\ msg[x].timestamp > @[x].timestamp
                        THEN msg[x]
                        ELSE @[x]]]

Actions(d) ==
  \/ SendsChatMessage(d)
  \/ AddsMember(d)
  \/ RemovesMember(d)
  \/ \E s \in AllDevices \ {d} : ReceivesMessage(s, d)

Next ==
  \/ \E d \in AllDevices : Actions(d)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------

(* If both devices think they are in the chat,
   they must have the same memberlist
   or disjoint memberlist.

   We want to have this property eventually
   if devices stop adding and removing members,
   but it does not hold at all times. *)
GroupConsistency ==
  \A d1, d2 \in EnabledDevices :
  \/ members[d1] = members[d2] \* Also checks that clocks are the same.
  \/ (MemberSet(members[d1]) \intersect MemberSet(members[d2])) = {}

(* If both devices think they are in the chat,
   they must have the same memberlist.

   This property does not allow the chat
   to split into "islands" of users
   who don't know about each other. *)
StrongGroupConsistency ==
  \A d1, d2 \in EnabledDevices :
  \/ members[d1] = members[d2]

(* If some device `d1' thinks it is not in the chat,
   then any other device `d2` which thinks it is in the chat
   must think that `d1' not in the chat. *)
NoStaleMembers ==
  \A d1, d2 \in AllDevices :
  (~IsMember(d1, d1) /\ IsMember(d2, d2) => ~IsMember(d2, d1))

----------------------------------------------------------------------------

(* All devices which can chat keep chatting. *)
MembersKeepChatting ==
  \A d \in AllDevices :
  WF_vars(SendsChatMessage(d))

DevicesKeepReceiving ==
  \A <<s, r>> \in DevicePairs :
  /\ WF_vars(ReceivesMessage(s, r))

(* Devices do not add or remove members. *)
NoMembershipChanges ==
  \A d \in AllDevices :
  ~AddsMember(d) /\ ~RemovesMember(d)

(* Eventually membership changes are never queued. *)
EventuallyNoMembershipChanges ==
  <>[][NoMembershipChanges]_vars

----------------------------------------------------------------------------

(* If chat members keep chatting and eventually stop adding or removing members,
   then eventually group is always conistent. *)
EventualConsistencyProperty ==
  (/\ WF_vars(Next)
   /\ MembersKeepChatting
   /\ DevicesKeepReceiving
   /\ EventuallyNoMembershipChanges)
   => <>[]GroupConsistency

(* This property does not hold because of the possibility to partition the group. *)
StrongEventualConsistencyProperty ==
  (/\ WF_vars(Next)
   /\ MembersKeepChatting
   /\ DevicesKeepReceiving
   /\ EventuallyNoMembershipChanges)
   => <>[]StrongGroupConsistency

(* This property does not hold. *)
NoStaleMembersProperty ==
  (/\ WF_vars(Next)
   /\ MembersKeepChatting
   /\ DevicesKeepReceiving
   /\ EventuallyNoMembershipChanges)
   => <>[]NoStaleMembers

----------------------------------------------------------------------------

StateConstraint == \A <<x, y>> \in DevicePairs : Len(queues[x, y]) <= MaxQueue

ClockConstraint == clock < MaxClock

=============================================================================
