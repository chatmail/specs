-------------------------- MODULE groupmembership --------------------------

(***************************************************************************)
(* Model of group membership management in Delta Chat.                     *)
(***************************************************************************)

EXTENDS Naturals,
        Sequences

CONSTANT Devices, \* Set of devices such as `{d1, d2, d3}'.
         Creator, \* Device that created the chat.
         MaxQueue,\* Bound on the queue size to keep the model bounded.
         MaxClock

Clock == 0 .. MaxClock

VARIABLES \* Map from device to the set of devices it thinks are members of the group .
          Members,
          \* FIFO queues of messages sent between devices.
          Queues,
          \* clock[d] is the clock of device `d`.
          clock

vars == <<Members, Queues, clock>>

-----------------------------------------------------------------

AllDevices ==
  Devices \union {Creator}

(*************)
(* Messages. *)
(*************)

(* Each message has the clock and the "To" field.
   "To" field contains the member list at the time of sending,
   so for the "Member removed" it does not include the removed member. *)
MemberAddedMessage(t, m, c) == [type |-> "add", to |-> t, member |-> m, clock |-> c]
MemberRemovedMessage(t, m, c) == [type |-> "remove", to |-> t, member |-> m, clock |-> c]
ChatMessage(t, c) == [type |-> "chat", to |-> t, clock |-> c]

(* The set of all possible messages.

   Messages do not have explicit `From:` field
   because messages for each sender are placed into its own queue. *)
Messages ==
  {MemberAddedMessage(t, m, c) :
   <<t, m, c>> \in (SUBSET AllDevices) \X AllDevices \X Clock} \union
  {MemberRemovedMessage(t, m, c) :
   <<t, m, c>> \in (SUBSET AllDevices) \X AllDevices \X Clock} \union
  {ChatMessage(t, c) : <<t, c>> \in (SUBSET AllDevices) \X Clock}

(* Pairs of devices excluding pairs of devices with self. *)
DevicePairs == { <<x, y>> \in AllDevices \X AllDevices : x # y }

TypeOK ==
  /\ Members \in [AllDevices -> SUBSET AllDevices]
  /\ Queues \in [DevicePairs -> Seq(Messages)]
  /\ clock \in [AllDevices -> Clock]

Init ==
  \* Only chat creator is a member of the chat.
  /\ Members = [d \in AllDevices |-> IF d = Creator THEN {d} ELSE {}]
  /\ Queues = [pair \in DevicePairs |-> <<>>] \* All queues are empty.
  /\ clock = [d \in AllDevices |-> 0]

----------------------------------------------------------------------------

SendMessage(sender, recipients, msg) ==
  Queues' = [<<s, r>> \in DevicePairs |->
             IF s = sender /\ r \in recipients
             THEN Append(Queues[s, r], msg)
             ELSE Queues[s, r]]

(* Device `d' sends a chat message. *)
SendsChatMessage(d) ==
  /\ d \in Members[d]
  /\ UNCHANGED <<Members, clock>>
  /\ LET
       msg == ChatMessage(Members[d], clock[d])
     IN
       SendMessage(d, Members[d], msg)

(* Device `d' adds a member to the chat. *)
AddsMember(d) ==
  /\ d \in Members[d]
  /\ \E m \in AllDevices :
     /\ m \notin Members[d]
     /\ Members' = [Members EXCEPT ![d] = Members[d] \union {m}]
     /\ clock' = [clock EXCEPT ![d] = @ + 1]
     (* Send "Member added" message to all chat members, including the new one. *)
     /\ LET
          to == Members'[d]
          msg == MemberAddedMessage(to, m, clock'[d])
        IN
          SendMessage(d, Members'[d], msg)

RemovesMember(d) ==
  /\ d \in Members[d]
  /\ \E m \in Members[d] : \* It is possible that m = d, then d leaves the group.
     /\ Members' = [Members EXCEPT ![d] = Members[d] \ {m}]
     /\ clock' = [clock EXCEPT ![d] = @ + 1]
     /\ LET
          to == Members'[d] (* Removed member is not included in the To field
                               but will receive the message. *)
          msg == MemberRemovedMessage(to, m, clock'[d])
        IN
          SendMessage(d, Members[d], msg)

----------------------------------------------------------------------------

(* Message reception logic, the main part of the protocol. *)

ReceiveMemberAdded(s, r) ==
  /\ Queues[s, r] /= <<>>
  /\ Queues' = [Queues EXCEPT ![s, r] = Tail(@)]
  /\ LET msg == Head(Queues[s, r])
     IN /\ msg.type = "add"
        /\ \/ msg.clock > clock[r] /\ Members' = [Members EXCEPT ![r] = msg.to]
                                   /\ clock' = [clock EXCEPT ![r] = msg.clock]
           \/ msg.clock = clock[r] /\ Members' = [Members EXCEPT ![r] = @ \union {msg.member}]
                                   /\ clock' = [clock EXCEPT ![r] =
                                                IF UNCHANGED Members
                                                THEN @
                                                ELSE @ + 1]
           \/ msg.clock < clock[r] /\ Members' = [Members EXCEPT ![r] = @ \union {msg.member}]
                                   /\ UNCHANGED clock

ReceiveMemberRemoved(s, r) ==
  /\ Queues[s, r] /= <<>>
  /\ Queues' = [Queues EXCEPT ![s, r] = Tail(@)]
  /\ LET msg == Head(Queues[s, r])
     IN /\ msg.type = "remove"
        /\ \/ msg.clock > clock[r] /\ Members' = [Members EXCEPT ![r] = msg.to]
                                   /\ clock' = [clock EXCEPT ![r] = msg.clock]
           \/ msg.clock = clock[r] /\ Members' = [Members EXCEPT ![r] = @ \ {msg.member}]
                                   /\ clock' = [clock EXCEPT ![r] =
                                                IF UNCHANGED Members
                                                THEN @
                                                ELSE @ + 1]
           \/ msg.clock < clock[r] /\ Members' = [Members EXCEPT ![r] = @ \ {msg.member}]
                                   /\ UNCHANGED clock

ReceiveChatMessage(s, r) ==
  /\ Queues[s, r] /= <<>>
  /\ Queues' = [Queues EXCEPT ![<<s, r>>] = Tail(@)]
  /\ LET msg == Head(Queues[s, r])
     IN /\ msg.type = "chat"
        (* Handle implicit member additions and removals. *)
        /\ \/ msg.clock > clock[r] /\ Members' = [Members EXCEPT ![r] = msg.to]
                                   /\ clock' = [clock EXCEPT ![r] = msg.clock]
              (* Tiebreaker to achieve eventual consistency.
                 Preferring additions over removal by
                 using union instead of intersection. *)
           \/ msg.clock = clock[r] /\ Members' = [Members EXCEPT ![r] = @ \union msg.to]
                                   /\ clock' = [clock EXCEPT ![r] =
                                                IF UNCHANGED Members
                                                THEN @
                                                ELSE @ + 1]
           \/ msg.clock < clock[r] /\ UNCHANGED <<Members, clock>>

ReceivesMessage(s, r) ==
  \/ ReceiveMemberAdded(s, r)
  \/ ReceiveMemberRemoved(s, r)
  \/ ReceiveChatMessage(s, r)

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
   they must have the same memberlist.

   We want to have this property eventually
   if devices stop adding and removing members,
   but it does not hold at all times. *)
GroupConsistency ==
  \A d1, d2 \in AllDevices :
  \/ d1 \notin Members[d1]
  \/ d2 \notin Members[d2]
  \/ Members[d1] = Members[d2]

(* If some device `d1' thinks it is not in the chat,
   then any other device `d2` which thinks it is in the chat
   must think that `d1' not in the chat. *)
NoStaleMembers ==
  \A d1, d2 \in AllDevices :
  (d1 \notin Members[d1] /\ d2 \in Members[d2]) => (d1 \notin Members[d2])

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

(* If chat members keep chatting and eventually stop adding or removing members,
   then eventually group is always conistent. *)
EventualConsistencyProperty ==
  (/\ WF_vars(Next)
   /\ MembersKeepChatting
   /\ DevicesKeepReceiving
   /\ EventuallyNoMembershipChanges)
   => <>[](GroupConsistency /\ NoStaleMembers)


=============================================================================
